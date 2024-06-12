use crate::utils::*;
use ark_crypto_primitives::sponge::poseidon::{
    constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, CryptographicSponge};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
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

/*
#[derive(Clone, Debug)]
pub struct NLookupTable<F: PrimeField> {
    t: Vec<F>,

}*/

#[derive(Clone, Debug)]
pub struct NLookup<F: PrimeField> {
    ell: usize,
    pcs: PoseidonConfig<F>,
    table_t: Vec<F>,
    table_pub: bool, // T pub or priv?
    table_eq: Vec<F>,
}

// sumcheck for one round; q,v,eq table will change per round
impl<F: PrimeField> NLookup<F> {
    pub fn new(table_t: Vec<F>, table_pub: bool) -> Self {
        let ell = logmn(table_t.len());

        let pcs: PoseidonConfig<F> =
            construct_poseidon_parameters_internal(2, 8, 56, 4, 5).unwrap(); //correct?

        NLookup {
            ell,
            pcs,
            table_t,
            table_pub,
            table_eq: Vec::<F>::new(),
        }
    }

    pub fn first_running_claim(&self) -> (Vec<F>, F) {
        let mut running_q = Vec::<F>::new();
        for i in 0..self.ell {
            running_q.push(F::zero());
        }

        let running_v = self.table_t[0];
        (running_q, running_v)
    }

    // qs, vs taken in just as witnesses, fpvar wires returned
    fn nlookup_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        q: Vec<usize>,
        v: Vec<F>,
        running_q: Vec<F>,
        running_v: F,
    ) -> Result<NLookupWires<F>, SynthesisError> {
        assert_eq!(q.len(), v.len());
        assert_eq!(self.ell, running_q.len());
        let num_lookups = v.len();

        let mut q_vars = Vec::<(FpVar<F>, Vec<Boolean<F>>)>::new();
        for qi in 0..q.len() {
            let qi_var = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(q[qi] as u64)))?;
            let (qi_bits, _) = to_bits_le_with_top_bits_zero(&qi_var, self.ell)?;
            q_vars.push((qi_var, qi_bits));
        }

        let mut v_vars = Vec::<FpVar<F>>::new();
        for vi in 0..v.len() {
            v_vars.push(FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(v[vi])))?);
        }

        // q processing (combine)
        // TODO
        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), &self.pcs);

        // sponge aborbs qs, vs, running q, running v, and possibly doc commit
        // TODO
        let query = Vec::<FpVar<F>>::new();
        sponge.absorb(&query)?;

        // sponge squeezed to produce rs
        let hash = sponge.squeeze_field_elements(1)?;
        let rho = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(2 as u64)))?; //&hash[0];

        let mut rs = Vec::<FpVar<F>>::new();
        rs.push(rho.clone());
        for i in 0..num_lookups {
            rs.push(&rs[i] * &rho);
        }

        let temp_eq = Self::gen_eq_table(
            &rs.into_iter().map(|x| x.value().unwrap()).collect(),
            &q,
            &running_q.into_iter().rev().collect(),
        );

        // LHS of nl equation (vs and ros)
        let init_claim = horners(&v_vars, &rho);

        let last_claim = self.sum_check_circuit(cs.clone(), init_claim, sponge, temp_eq);

        // last_claim & eq circuit -> TODO possibly make this horners too and remove rs fpvar calc

        let next_running_q = vec![];
        let next_running_v = FpVar::<F>::new_witness(cs.clone(), || Ok(F::zero()))?;

        Ok(NLookupWires {
            q: q_vars,
            v: v_vars,
            next_running_q,
            next_running_v,
        })
    }

    fn sum_check_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        init_claim: FpVar<F>,
        mut sponge: PoseidonSpongeVar<F>,
        mut temp_eq: Vec<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut temp_table = self.table_t.clone(); // todo

        // current claim in each round
        let mut claim = init_claim.clone();

        for j in 0..self.ell {
            let (con, x, xsq) = self.prover_msg(j, &temp_table, &temp_eq);
            println!(
                "prover msg {:#?}, {:#?}, {:#?}",
                con.clone(),
                x.clone(),
                xsq.clone()
            );

            let g_j_const = FpVar::<F>::new_witness(cs.clone(), || Ok(con))?;
            let g_j_x = FpVar::<F>::new_witness(cs.clone(), || Ok(x))?;
            let g_j_xsq = FpVar::<F>::new_witness(cs.clone(), || Ok(xsq))?;

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
        }

        // last claim
        Ok(claim)
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

    fn gen_eq_table(rs: &Vec<F>, qs: &Vec<usize>, last_q: &Vec<F>) -> Vec<F> {
        let base: usize = 2;
        let ell: usize = last_q.len();

        let t_len = base.pow(ell as u32);
        assert_eq!(rs.len(), qs.len() + 1);

        let mut eq_t = vec![F::zero(); t_len];

        for i in 0..qs.len() {
            eq_t[qs[i]] += rs[i];
        }

        for i in 0..eq_t.len() {
            let mut term = rs[qs.len()].clone();

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
    use ark_pallas::Fr as F;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

    fn run_nlookup(batch_size: usize, q: Vec<usize>, v_pre: Vec<usize>, table_pre: Vec<usize>) {
        let v: Vec<F> = v_pre.into_iter().map(|x| F::from(x as u64)).collect();
        let table: Vec<F> = table_pre.into_iter().map(|x| F::from(x as u64)).collect();

        assert_eq!(q.len(), v.len());

        let mut nl = NLookup::new(table, true);
        let rounds = ((q.len() as f32) / (batch_size as f32)).ceil() as usize;
        let (mut running_q, mut running_v) = nl.first_running_claim();

        for i in 0..rounds {
            let cs = ConstraintSystem::<F>::new_ref();
            cs.set_optimization_goal(OptimizationGoal::Constraints);
            let res = nl.nlookup_circuit(
                cs.clone(),
                q[(i * batch_size)..(i + 1 * batch_size)].to_vec(),
                v[(i * batch_size)..(i + 1 * batch_size)].to_vec(),
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
        let table = vec![3, 5, 7, 9];

        let q = vec![0, 1, 2];
        let v = vec![3, 5, 7];

        run_nlookup(3, q, v, table);
    }

    #[test]
    fn mle_linear_basic() {
        let mut evals = vec![
            F::from(2),
            F::from(3),
            F::from(5),
            F::from(7),
            F::from(9),
            F::from(13),
            F::from(17),
            F::from(19),
        ];

        let table = evals.clone();

        let mut nl = NLookup::new(table.clone(), true);

        let qs = vec![2, 1, 7];

        let last_q = vec![F::from(0), F::from(0), F::from(0)];
        //vec![F::from(2), F::from(3), F::from(5)],

        let claims = vec![F::from(3), F::from(9), F::from(27), F::from(81)];

        let mut term = F::from(0);
        for i in 0..qs.len() {
            term += evals[qs[i]].clone() * &claims[i];
        }

        let mut eq_a =
            NLookup::gen_eq_table(&claims, &qs, &last_q.clone().into_iter().rev().collect());

        println!("EQ TABLE {:#?} END", eq_a);

        // claim check
        let running_v = table[0];
        //let (_, running_v) = F::from();
        //    prover_mle_partial_eval(&evals, &last_q, &(0..evals.len()).collect(), true, None);
        term += running_v * &claims[3];

        let mut claim: F = evals
            .iter()
            .zip(eq_a.iter())
            .map(|(ti, eqi)| ti * eqi)
            .sum();

        assert_eq!(term, claim);

        let mut sc_rs = vec![];
        for i in 0..3 {
            let (con, x, xsq) = nl.prover_msg(i, &evals, &eq_a);
            println!(
                "prover msg {:#?}, {:#?}, {:#?}",
                con.clone(),
                x.clone(),
                xsq.clone()
            );

            let r_i = F::from(5); // todo

            let g0_g1 = &con + &con + &x + &xsq;
            println!(
                "i {:#?}, claim {:#?}, g0 g1 {:#?}",
                i,
                claim.clone(),
                g0_g1.clone()
            );
            assert_eq!(claim, g0_g1);

            claim = xsq * r_i * r_i + x * r_i + con;

            sc_rs.push(r_i);

            nl.update_tables(r_i, i, &mut evals, &mut eq_a);
        }
        /*
                    // next
                    let (_, next_running_v) =
                        prover_mle_partial_eval(&table, &sc_rs, &(0..table.len()).collect(), true, None);

                    // sanity check
                    let (_, eq_term) = prover_mle_partial_eval(&claims, &sc_rs, &qs, false, Some(&last_q));
                    assert_eq!(
                        claim, // last claim
                        (eq_term * next_running_v.clone())
                    );
        */
    }
}
