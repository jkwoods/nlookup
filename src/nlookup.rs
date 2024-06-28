use crate::utils::*;
use ark_crypto_primitives::sponge::poseidon::{
    constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, CryptographicSponge};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    convert::ToConstraintFieldGadget,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};
use ark_std::test_rng;

pub struct NLookupWires<F: PrimeField> {
    q: Vec<(FpVar<F>, Vec<Boolean<F>>)>, // (field elt, bits)
    v: Vec<FpVar<F>>,
    next_running_q: Vec<FpVar<F>>,
    next_running_v: FpVar<F>,
}
// we assume for now user is not interested in prev_running_q/v

// TODO
pub struct Table<'a, F: PrimeField> {
    t: &'a Vec<F>,
    public: bool, // T pub or priv?
    projs: Option<Vec<(usize, usize)>>,
}

impl<'a, F: PrimeField> Table<'a, F> {
    pub fn new(t: &'a Vec<F>, public: bool) -> Self {
        Table {
            t,
            public,
            projs: None,
        }
    }

    pub fn new_proj(t: &'a Vec<F>, public: bool, projs: Vec<(usize, usize)>) -> Self {
        Table {
            t,
            public,
            projs: Some(projs),
        }
    }
}

pub struct NLookup<F: PrimeField> {
    ell: usize, // for "big" table
    m: usize,
    pcs: PoseidonConfig<F>,
    table: Vec<F>,
    padding_lookup: (usize, F),
}

// sumcheck for one round; q,v,eq table will change per round
impl<F: PrimeField> NLookup<F> {
    pub fn new<'a>(
        tables: &mut Vec<Table<'a, F>>,
        num_lookups: usize,
        padding_lookup: Option<(usize, F)>,
    ) -> Self {
        assert!(num_lookups > 0);
        assert!(tables.len() > 0);

        tables.sort_by(|a, b| {
            a.t.len()
                .next_power_of_two()
                .cmp(&b.t.len().next_power_of_two())
        });

        let mut table = Vec::<F>::new();
        let cur_size = 0;
        for t in tables {
            // todo proj

            let mut sub_table = t.t.clone();
            sub_table.extend(vec![
                F::zero();
                sub_table.len().next_power_of_two() - sub_table.len()
            ]);

            table.extend(sub_table);

            // cur_size += sub_table.len(); // TODO
        }

        let ell = logmn(table.len());

        let pcs: PoseidonConfig<F> =
            construct_poseidon_parameters_internal(2, 8, 56, 4, 5).unwrap(); //correct?

        let padding = if padding_lookup.is_some() {
            padding_lookup.unwrap()
        } else {
            (0, table[0])
        };

        NLookup {
            ell,
            m: num_lookups,
            pcs,
            table,
            padding_lookup: padding,
        }
    }

    pub fn first_running_claim(&self) -> (Vec<F>, F) {
        let mut running_q = Vec::<F>::new();
        for i in 0..self.ell {
            running_q.push(F::zero());
        }

        let running_v = self.table[0];
        (running_q, running_v)
    }

    // qs, vs taken in just as witnesses, fpvar wires returned
    pub fn nlookup_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        lookups: &Vec<(usize, F)>,
        running_q: Vec<F>,
        running_v: F,
    ) -> Result<NLookupWires<F>, SynthesisError> {
        assert_eq!(self.ell, running_q.len());
        assert!(lookups.len() > 0);
        assert!(lookups.len() <= self.m);

        let mut q = Vec::<(FpVar<F>, Vec<Boolean<F>>)>::new();
        let mut v = Vec::<FpVar<F>>::new();
        for (qi, vi) in lookups.clone().into_iter() {
            let qi_var = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(qi as u64)))?;
            let (qi_bits, _) = qi_var.to_bits_le_with_top_bits_zero(self.ell)?;
            q.push((qi_var, qi_bits));

            v.push(FpVar::<F>::new_witness(cs.clone(), || Ok(vi))?);
        }

        while q.len() < self.m {
            let qi_var =
                FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(self.padding_lookup.0 as u64)))?;
            let (qi_bits, _) = qi_var.to_bits_le_with_top_bits_zero(self.ell)?;
            q.push((qi_var, qi_bits));

            v.push(FpVar::<F>::new_witness(cs.clone(), || {
                Ok(self.padding_lookup.1)
            })?);
        }

        println!(
            "q {:#?}, v {:#?}",
            q.clone()
                .into_iter()
                .map(|(val, b)| val.value().unwrap())
                .collect::<Vec<F>>(),
            v.clone()
                .into_iter()
                .map(|val| val.value().unwrap())
                .collect::<Vec<F>>()
        );

        let mut running_q_vars = Vec::<FpVar<F>>::new();
        for rqi in 0..running_q.len() {
            running_q_vars.push(FpVar::<F>::new_witness(cs.clone(), || Ok(running_q[rqi]))?);
        }
        let running_v_var = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(running_v)))?;

        // q processing (combine)
        // TODO
        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), &self.pcs);

        // sponge aborbs qs, vs, running q, running v, and possibly doc commit
        // TODO
        let mut query = Vec::<FpVar<F>>::new();

        query.extend(running_q_vars.clone());
        query.extend(v.clone());
        query.extend(vec![running_v_var.clone()]);
        sponge.absorb(&query)?;

        // sponge squeezed to produce rs
        let hash = sponge.squeeze_field_elements(1)?;
        let rho = &hash[0];

        // LHS of nl equation (vs and ros)
        // running q,v are the "constant" (not hooked to a rho)
        let mut horners_vals = vec![running_v_var.clone()];
        horners_vals.extend(v.clone());
        let init_claim = horners(&horners_vals, &rho);

        // clean this up :(
        let mut temp_q: Vec<usize> = lookups.into_iter().map(|(x, v)| *x).collect();
        while temp_q.len() < self.m {
            temp_q.push(self.padding_lookup.0);
        }
        let temp_eq = Self::gen_eq_table(
            rho.value().unwrap(),
            &temp_q,
            &running_q.into_iter().rev().collect(),
        );
        let (next_running_q, last_claim) =
            self.sum_check(cs.clone(), init_claim, sponge, temp_eq)?;

        // last_claim & eq circuit
        // TODO CLONE REV CLEAN UP
        let mut eq_evals =
            vec![self.bit_eq(&running_q_vars.into_iter().rev().collect(), &next_running_q)?]; //??

        for i in 0..self.m {
            let mut qi_vec = Vec::<FpVar<F>>::new();
            for qij in q[i].1.iter() {
                let qij_vec = qij.to_constraint_field()?;
                assert_eq!(qij_vec.len(), 1);
                qi_vec.push(qij_vec[0].clone());
            }

            eq_evals.push(self.bit_eq(&qi_vec, &next_running_q)?);
        }
        let eq_eval = horners(&eq_evals, &rho);

        let next_running_v = FpVar::<F>::new_witness(cs.clone(), || {
            Ok(self.mle_eval(
                next_running_q
                    .clone()
                    .into_iter()
                    .map(|x| x.value().unwrap())
                    .collect(),
            ))
        })?;

        // last_claim = eq_eval * next_running_claim
        last_claim.enforce_equal(&(eq_eval * &next_running_v));

        Ok(NLookupWires {
            q,
            v,
            next_running_q,
            next_running_v,
        })
    }

    fn sum_check(
        &mut self,
        cs: ConstraintSystemRef<F>,
        init_claim: FpVar<F>,
        mut sponge: PoseidonSpongeVar<F>,
        mut temp_eq: Vec<F>,
    ) -> Result<(Vec<FpVar<F>>, FpVar<F>), SynthesisError> {
        let mut temp_table = self.table.clone(); // todo

        // current claim in each round
        let mut claim = init_claim.clone();

        let mut rands = Vec::<FpVar<F>>::new();
        for j in 0..self.ell {
            let (con, x, xsq) = self.prover_msg(j, &temp_table, &temp_eq);

            let g_j_const = FpVar::<F>::new_witness(cs.clone(), || Ok(con))?;
            let g_j_x = FpVar::<F>::new_witness(cs.clone(), || Ok(x))?;
            let g_j_xsq = FpVar::<F>::new_witness(cs.clone(), || Ok(xsq))?;

            // sanity
            assert_eq!(
                claim.value().unwrap(),
                (&g_j_const + &g_j_const + &g_j_x + &g_j_xsq)
                    .value()
                    .unwrap()
            );

            claim.enforce_equal(&(&g_j_const + &g_j_const + &g_j_x + &g_j_xsq))?;

            sponge.absorb(&vec![&g_j_const, &g_j_x, &g_j_xsq])?;
            let hash = sponge.squeeze_field_elements(1)?;
            let r_j = &hash[0];

            claim = ((g_j_xsq * r_j) + g_j_x) * r_j + g_j_const;

            self.update_tables(r_j.value()?, j, &mut temp_table, &mut temp_eq);
            rands.push(r_j.clone());
        }

        // last claim
        Ok((rands, claim))
    }

    fn bit_eq(
        &mut self,
        qi: &Vec<FpVar<F>>,
        r: &Vec<FpVar<F>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut eq = Vec::<FpVar<F>>::new();
        for j in (0..self.ell).rev() {
            let next = (&qi[j] * &r[self.ell - j - 1])
                + ((FpVar::one() - &qi[j]) * (FpVar::one() - &r[self.ell - j - 1]));
            eq.push(next);
        }

        let mut ret = eq[0].clone();
        for i in 1..eq.len() {
            ret *= &eq[i];
        }

        Ok(ret)
    }

    // starts with evals on hypercube
    fn prover_msg(&self, i: usize, temp_table: &Vec<F>, temp_eq: &Vec<F>) -> (F, F, F) {
        let base: usize = 2;
        let pow: usize = base.pow((self.ell - i - 1) as u32);

        assert_eq!(temp_table.len(), base.pow(self.ell as u32));
        assert_eq!(temp_eq.len(), base.pow(self.ell as u32));

        let mut xsq = F::zero();
        let mut x = F::zero();
        let mut con = F::zero();

        for b in 0..pow {
            let ti_0 = temp_table[b];
            let ti_1 = temp_table[b + pow];
            let ei_0 = temp_eq[b];
            let ei_1 = temp_eq[b + pow];

            let t_slope = ti_1 - ti_0;
            let e_slope = ei_1 - ei_0;

            xsq += t_slope * e_slope;
            x += e_slope * ti_0;
            x += t_slope * ei_0;
            con += ti_0 * ei_0;
        }

        (con, x, xsq)
    }

    fn update_tables(&mut self, r_i: F, i: usize, temp_table: &mut Vec<F>, temp_eq: &mut Vec<F>) {
        let base: usize = 2;
        let pow: usize = base.pow((self.ell - i - 1) as u32);

        for b in 0..pow {
            temp_table[b] = temp_table[b] * (F::one() - r_i) + temp_table[b + pow] * r_i;
            temp_eq[b] = temp_eq[b] * (F::one() - r_i) + temp_eq[b + pow] * r_i;
        }
    }

    fn mle_eval(&self, x: Vec<F>) -> F {
        assert_eq!(x.len(), self.ell);

        let chis = Self::evals(x);
        assert_eq!(chis.len(), self.table.len());

        (0..chis.len())
            .into_iter()
            .map(|i| chis[i] * self.table[i])
            .reduce(|x, y| x + y)
            .unwrap()
    }

    fn evals(x: Vec<F>) -> Vec<F> {
        let ell = x.len();
        let mut evals: Vec<F> = vec![F::zero(); (2_usize).pow(ell as u32)];
        let mut size = 1;
        evals[0] = F::one();

        for r in x.iter().rev() {
            let (evals_left, evals_right) = evals.split_at_mut(size);
            let (evals_right, _) = evals_right.split_at_mut(size);

            evals_left
                .iter_mut()
                .zip(evals_right.iter_mut())
                .for_each(|(x, y)| {
                    *y = *x * r;
                    *x -= &*y;
                });

            size *= 2;
        }
        evals
    }

    fn gen_eq_table(rho: F, qs: &Vec<usize>, last_q: &Vec<F>) -> Vec<F> {
        let base: usize = 2;
        let ell: usize = last_q.len();
        let t_len = base.pow(ell as u32);

        let mut rhos = Vec::<F>::new();
        rhos.push(rho);
        if qs.len() > 1 {
            for i in 0..(qs.len() - 1) {
                rhos.push(rhos[i] * rho);
            }
        }
        rhos.push(F::one());

        let mut eq_t = vec![F::zero(); t_len];

        for i in 0..qs.len() {
            eq_t[qs[i]] += rhos[i];
        }

        for i in 0..eq_t.len() {
            let mut term = rhos[qs.len()].clone();

            for j in (0..ell).rev() {
                let xi = (i >> j) & 1;
                term *= F::from(xi as u64) * last_q[j]
                    + (F::one() - F::from(xi as u64)) * (F::one() - last_q[j]);
            }
            eq_t[i] += term;
        }

        eq_t
    }
}

// todo add conditional_enforce

mod tests {

    use crate::nlookup::*;
    use ark_ff::{Field, PrimeField};
    use ark_pallas::Fr as F;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

    fn run_nlookup(batch_size: usize, qv: Vec<(usize, usize)>, table_pre: Vec<usize>) {
        let rounds = ((qv.len() as f32) / (batch_size as f32)).ceil() as usize;
        println!("ROUNDS {:#?}", rounds);

        let lookups: Vec<(usize, F)> = qv
            .into_iter()
            .map(|(q, v)| (q, F::from(v as u64)))
            .collect();
        let table: Vec<F> = table_pre.into_iter().map(|x| F::from(x as u64)).collect();

        let mut nl = NLookup::new(&mut vec![Table::new(&table, true)], batch_size, None);
        let (mut running_q, mut running_v) = nl.first_running_claim();

        for i in 0..rounds {
            let cs = ConstraintSystem::<F>::new_ref();
            cs.set_optimization_goal(OptimizationGoal::Constraints);

            let lu_end = if (i + 1) * batch_size < lookups.len() {
                (i + 1) * batch_size
            } else {
                lookups.len()
            };

            println!("lookups {:#?}", lookups[(i * batch_size)..lu_end].to_vec());

            let res = nl.nlookup_circuit(
                cs.clone(),
                &lookups[(i * batch_size)..lu_end].to_vec(),
                running_q,
                running_v,
            );
            assert!(res.is_ok());

            let nl_wires = res.unwrap();
            running_q = nl_wires
                .next_running_q
                .into_iter()
                .map(|x| x.value().unwrap())
                .collect();
            running_v = nl_wires.next_running_v.value().unwrap();

            cs.finalize();
            assert!(cs.is_satisfied().unwrap(), "Failed at iter {}", i);
        }
    }

    #[test]
    fn nl_basic() {
        let table = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let lookups = vec![(2, 5), (1, 3), (7, 19)];

        run_nlookup(3, lookups, table);
    }

    #[test]
    fn nl_many_lookups() {
        let table = vec![2, 3, 5, 7, 9, 13, 17, 19];

        let lookups = vec![
            (2, 5),
            (1, 3),
            (7, 19),
            (2, 5),
            (3, 7),
            (4, 9),
            (0, 2),
            (1, 3),
        ];

        run_nlookup(8, lookups.clone(), table.clone());
        run_nlookup(4, lookups.clone(), table.clone());
        run_nlookup(2, lookups.clone(), table.clone());
        run_nlookup(1, lookups.clone(), table.clone());
    }

    #[test]
    #[should_panic]
    fn nl_bad_lookup() {
        let table = vec![2, 3, 5, 7, 9, 13, 17, 19];

        let lookups = vec![(2, 5), (1, 13), (7, 19)];
        run_nlookup(3, lookups, table);
    }

    #[test]
    fn nl_padding() {
        let table = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let lookups = vec![(2, 5), (1, 3), (7, 19)];

        run_nlookup(4, lookups, table.clone());

        let big_lookups = vec![(2, 5), (1, 3), (7, 19), (2, 5), (3, 7), (1, 3)];

        run_nlookup(5, big_lookups, table);
    }

    #[test]
    fn mle_basic() {
        let mut evals = vec![F::from(2), F::from(6), F::from(5), F::from(14)];

        let table = evals.clone();
        let mut nl = NLookup::new(&mut vec![Table::new(&table, true)], 3, None);

        let qs = vec![2, 1, 1];
        let last_q = vec![F::from(5), F::from(4)];

        let rho = F::from(3);

        let running_v = nl.mle_eval(last_q.clone());

        let mut term = running_v;
        for i in 0..qs.len() {
            let mut rho_pow = rho;
            for p in 0..i {
                rho_pow *= rho;
            }
            term += evals[qs[i]].clone() * rho_pow;
        }

        let mut eq_a = NLookup::gen_eq_table(rho, &qs, &last_q.clone().into_iter().rev().collect());

        // claim check
        let mut claim: F = evals
            .iter()
            .zip(eq_a.iter())
            .map(|(ti, eqi)| ti * eqi)
            .sum();

        assert_eq!(term, claim);
        println!("claim {:#?}", claim.clone());

        let mut sc_rs = vec![];
        for i in 0..nl.ell {
            let (con, x, xsq) = nl.prover_msg(i, &mut evals, &mut eq_a);
            println!("prov msg {:#?} {:#?} {:#?}", con, x, xsq);

            let r_i = if i == 0 { F::from(3) } else { F::from(2) };

            let g0_g1 = F::from(2) * &con + &x + &xsq;
            assert_eq!(claim, g0_g1,);

            claim = xsq * &r_i * &r_i + x * &r_i + con;
            nl.update_tables(r_i, i, &mut evals, &mut eq_a);
            sc_rs.push(r_i);
        }

        //sc_rs = sc_rs.into_iter().rev().collect();
        // next
        let next_running_v = nl.mle_eval(sc_rs.clone());
        println!("nrv {:#?}", next_running_v.clone());

        // sanity check
        // eq_term = rhos * eq(qi, sc_rs_i)
        let mut eq_term = F::from(0);
        println!("loop");
        for i in 0..qs.len() {
            let mut eq = F::from(1);
            for j in (0..nl.ell).rev() {
                let qij = F::from(((qs[i] >> j) & 1) as u64);
                println!(
                    "qij {:#?} -> {:#?}, scrs ij {:#?}",
                    qs[i],
                    ((qs[i] >> j) & 1),
                    sc_rs[j].clone()
                );
                eq *= qij * &sc_rs[nl.ell - j - 1]
                    + (F::from(1) - qij) * (F::from(1) - &sc_rs[nl.ell - j - 1]);
            }

            let mut rho_pow = rho;
            for p in 0..i {
                rho_pow *= rho;
            }

            println!("i {:#?}: RP {:#?}, EQ {:#?}", i, rho_pow, eq);
            eq_term += rho_pow * eq;
        }
        // last q
        sc_rs = sc_rs.into_iter().rev().collect();
        let mut eq = F::from(1);
        for j in (0..nl.ell).rev() {
            let qij = last_q[j];
            eq *= qij * &sc_rs[nl.ell - j - 1]
                + (F::from(1) - qij) * (F::from(1) - &sc_rs[nl.ell - j - 1]);
        }
        println!("last q eq term {:#?}", eq.clone());
        eq_term += eq;
        println!("eq term {:#?}", eq_term.clone());

        // (last) claim == eq_term * next_running_v
        assert_eq!(claim, eq_term * next_running_v);
    }
}
