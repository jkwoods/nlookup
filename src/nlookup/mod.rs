use crate::{bellpepper::*, nlookup::table::*, utils::*};
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
use itertools::Itertools;
use std::collections::HashMap;
use std::ops::Range;

use nova_snark::provider::hyrax_pc::HyraxPC;

pub mod table;

#[derive(Clone, Debug)]
pub struct NLookupWires<A: PrimeField> {
    pub q: Vec<(FpVar<A>, Vec<Boolean<A>>)>, // (field elt, bits)
    pub v: Vec<FpVar<A>>,
    pub prev_running_q: Vec<FpVar<A>>,
    pub prev_running_v: FpVar<A>,
    pub next_running_q: Vec<FpVar<A>>,
    pub next_running_v: FpVar<A>,
}

#[derive(Debug)]
pub struct NLookup<'a, A: PrimeField> {
    ell: usize, // for "big" table
    m: usize,
    pcs: PoseidonConfig<A>,
    table: Vec<A>,
    small_table_refs: Vec<&'a Table<A>>,
    priv_cmts: Vec<A>,
    tag_to_loc: HashMap<usize, Vec<(Range<usize>, isize)>>,
    padding_lookup: (usize, A),
    ordering_info: Vec<(usize, (usize, usize))>, // (table tag, proj)
}

// initialize nlookup table, allowed to call circuit for multiple rounds
// takes Tables with unique tags, the number of lookups per round
// optionally, you can specify what "lookup" is used to pad non-full batches
impl<'a, A: PrimeField> NLookup<'a, A> {
    pub fn new(
        tables: Vec<&'a Table<A>>,
        num_lookups: usize,
        padding_lookup: Option<(usize, A)>,
    ) -> Self {
        assert!(num_lookups > 0);
        assert!(tables.len() > 0);

        let tags: Vec<usize> = tables.iter().map(|t| t.tag).collect();
        let unique_tags: Vec<usize> = tags.into_iter().unique().collect();
        assert_eq!(unique_tags.len(), tables.len(), "Duplicate tags on tables");

        // accumulate subtables
        let mut sub_tables = Vec::<(Vec<A>, usize, (usize, usize))>::new();
        let mut priv_cmts = Vec::<A>::new();

        for t in &tables {
            match t.priv_cmt {
                Some(cmt) => priv_cmts.push(cmt.clone()),
                None => (),
            }

            match &t.proj {
                Some(projs) => {
                    for p in projs {
                        let sub_table = t.t[p.0..p.1].to_vec();
                        assert_eq!(sub_table.len().next_power_of_two(), sub_table.len());
                        sub_tables.push((sub_table, t.tag, *p));
                    }
                }
                None => {
                    let mut sub_table = t.t.clone();
                    assert_eq!(sub_table.len().next_power_of_two(), sub_table.len());
                    let full_range = (0, sub_table.len());
                    sub_tables.push((sub_table, t.tag, full_range));
                }
            }
        }

        sub_tables.sort_by(|a, b| {
            a.0.len()
                .next_power_of_two()
                .cmp(&b.0.len().next_power_of_two())
        });
        sub_tables = sub_tables
            .into_iter()
            .rev()
            .collect::<Vec<(Vec<A>, usize, (usize, usize))>>();

        let mut remaining_table_size = 0;
        let mut ordering_info = Vec::new();
        for (st, tag, proj) in &sub_tables {
            remaining_table_size += st.len();
            ordering_info.push((*tag, *proj));
        }
        remaining_table_size = remaining_table_size.next_power_of_two();

        let mut table = Vec::<A>::new();
        let mut tag_to_loc = HashMap::<usize, Vec<(Range<usize>, isize)>>::new();
        // TODO: make sure projections and hybrid make sense?

        for (st, tag, proj) in sub_tables {
            println!("table len {:#?}, proj 0 {:#?}", table.len(), proj.0);
            let offset = (table.len() as isize) - (proj.0 as isize);
            let range = proj.0..proj.1;
            match tag_to_loc.remove(&tag) {
                Some(mut offset_vec) => {
                    offset_vec.push((range, offset));
                    tag_to_loc.insert(tag, offset_vec);
                }
                None => {
                    tag_to_loc.insert(tag, vec![(range, offset)]); // offset = table placement offset - proj.0
                }
            }
            remaining_table_size -= st.len();
            table.extend(st);
        }

        table.extend(vec![A::zero(); remaining_table_size]);

        let ell = logmn(table.len());

        let pcs: PoseidonConfig<A> =
            construct_poseidon_parameters_internal(4, 8, 56, 4, 5).unwrap(); //correct?

        let padding = if padding_lookup.is_some() {
            let pd = padding_lookup.unwrap();
            assert_eq!(table[pd.0], pd.1, "specified padding not in table");
            pd
        } else {
            (0, table[0])
        };

        println!(
            "OFFSETS {:#?}, TABLE {:#?}",
            tag_to_loc.clone(),
            table.clone()
        );

        NLookup {
            ell,
            m: num_lookups,
            pcs,
            table,
            small_table_refs: tables,
            priv_cmts,
            tag_to_loc,
            padding_lookup: padding,
            ordering_info,
        }
    }

    pub fn first_running_claim(&self) -> (Vec<A>, A) {
        let mut running_q = Vec::<A>::new();
        for i in 0..self.ell {
            running_q.push(A::zero());
        }

        let running_v = self.table[0];
        (running_q, running_v)
    }

    // circuit for a round of lookups
    // qs, vs taken in just as witnesses, fpvar wires returned
    pub fn nlookup_circuit_F(
        &mut self,
        cs: ConstraintSystemRef<A>,
        lookups: &Vec<(usize, A, usize)>, // (q, v, table tag), qs should correspond to original
        // table
        running_q: Vec<A>,
        running_v: A,
    ) -> Result<NLookupWires<A>, SynthesisError> {
        let mut new_lookups = Vec::<(usize, FpVar<A>, usize)>::new();
        for (qi, vi, tagi) in lookups.clone().into_iter() {
            new_lookups.push((qi, FpVar::<A>::new_witness(cs.clone(), || Ok(vi))?, tagi));
        }

        self.nlookup_circuit(cs, &new_lookups, running_q, running_v)
    }

    pub fn nlookup_circuit(
        &mut self,
        cs: ConstraintSystemRef<A>,
        lookups: &Vec<(usize, FpVar<A>, usize)>, // (q, v, table tag), qs should correspond to original
        // table
        running_q: Vec<A>,
        running_v: A,
    ) -> Result<NLookupWires<A>, SynthesisError> {
        assert_eq!(self.ell, running_q.len());
        assert!(lookups.len() > 0);
        assert!(lookups.len() <= self.m);

        let mut q = Vec::<(FpVar<A>, Vec<Boolean<A>>)>::new();
        let mut q_usize = Vec::<usize>::new();
        let mut v = Vec::<FpVar<A>>::new();
        let mut all_q_bits = Vec::<Boolean<A>>::new();
        for (qi, vi, tagi) in lookups.clone().into_iter() {
            let mut offset = 0 as isize;
            let mut in_range = false;
            for (range, o) in &self.tag_to_loc[&tagi] {
                if range.contains(&qi) {
                    offset = *o;
                    in_range = true;
                }
            }
            assert!(in_range, "q not in range of table projections");

            let actual_idx = qi as isize + offset;
            assert!(actual_idx >= 0);
            q_usize.push(actual_idx as usize);
            // sanity
            assert_eq!(self.table[actual_idx as usize], vi.value()?);

            let qi_var = FpVar::<A>::new_witness(cs.clone(), || Ok(A::from(actual_idx as u64)))?; // change
                                                                                                  // later?
            let (qi_bits, _) = qi_var.to_bits_le_with_top_bits_zero(self.ell)?;
            all_q_bits.extend(qi_bits.clone());
            q.push((qi_var, qi_bits));

            v.push(vi);
            //    FpVar::<A>::new_witness(cs.clone(), || Ok(vi))?);
        }

        while q.len() < self.m {
            q_usize.push(self.padding_lookup.0);
            let qi_var =
                FpVar::<A>::new_witness(cs.clone(), || Ok(A::from(self.padding_lookup.0 as u64)))?;
            let (qi_bits, _) = qi_var.to_bits_le_with_top_bits_zero(self.ell)?;
            all_q_bits.extend(qi_bits.clone());
            q.push((qi_var, qi_bits));

            v.push(FpVar::<A>::new_witness(cs.clone(), || {
                Ok(self.padding_lookup.1)
            })?);
        }

        println!(
            "q {:#?}, v {:#?}",
            q.clone()
                .into_iter()
                .map(|(val, b)| val.value().unwrap())
                .collect::<Vec<A>>(),
            v.clone()
                .into_iter()
                .map(|val| val.value().unwrap())
                .collect::<Vec<A>>()
        );

        let mut running_q_vars = Vec::<FpVar<A>>::new();
        for rqi in 0..running_q.len() {
            running_q_vars.push(FpVar::<A>::new_witness(cs.clone(), || Ok(running_q[rqi]))?);
        }
        let running_v_var = FpVar::<A>::new_witness(cs.clone(), || Ok(A::from(running_v)))?;

        // q processing (combine)
        let mut combined_qs = Vec::new();
        while !all_q_bits.is_empty() {
            let mut bits = Vec::new();
            let mut i = 0;
            while let Some(bit) = all_q_bits.pop() {
                if i < (A::MODULUS_BIT_SIZE as usize - 1) {
                    bits.push(bit);
                    i += 1;
                } else {
                    break;
                };
            }
            combined_qs.push(Boolean::le_bits_to_fp(&bits)?);
        }

        let mut sponge = PoseidonSpongeVar::<A>::new(cs.clone(), &self.pcs);

        // sponge aborbs qs, vs, running q, running v, and possibly doc commit
        let mut query = Vec::<FpVar<A>>::new();
        for cmt in &self.priv_cmts {
            query.push(FpVar::<A>::new_witness(cs.clone(), || {
                Ok(A::from(cmt.clone()))
            })?);
        }
        query.extend(combined_qs);
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

        let temp_eq = Self::gen_eq_table(
            rho.value().unwrap(),
            &q_usize,
            &running_q.into_iter().rev().collect(),
        );
        let (next_running_q, last_claim) =
            self.sum_check(cs.clone(), init_claim, sponge, temp_eq)?;

        // last_claim & eq circuit
        // TODO CLONE REV CLEAN UP
        let mut eq_evals = vec![self.bit_eq(
            &running_q_vars.clone().into_iter().rev().collect(),
            &next_running_q,
        )?]; //??

        for i in 0..self.m {
            let mut qi_vec = Vec::<FpVar<A>>::new();
            for qij in q[i].1.iter() {
                let qij_vec = qij.to_constraint_field()?;
                assert_eq!(qij_vec.len(), 1);
                qi_vec.push(qij_vec[0].clone());
            }

            eq_evals.push(self.bit_eq(&qi_vec, &next_running_q)?);
        }
        let eq_eval = horners(&eq_evals, &rho);

        let next_running_v = FpVar::<A>::new_witness(cs.clone(), || {
            Ok(self.mle_eval(&next_running_q.iter().map(|x| x.value().unwrap()).collect()))
        })?;

        // last_claim = eq_eval * next_running_claim
        last_claim.enforce_equal(&(eq_eval * &next_running_v))?;

        // inputize
        let mut in_running_q: Vec<FpVar<A>> = Vec::new();
        let mut out_next_running_q: Vec<FpVar<A>> = Vec::new();
        for i in 0..running_q_vars.len() {
            let (iq, oq) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(running_q_vars[i].value()?),
                || Ok(next_running_q[i].value()?),
            )
            .unwrap();
            iq.enforce_equal(&running_q_vars[i])?;
            oq.enforce_equal(&next_running_q[i])?;
        }
        let (in_running_v, out_next_running_v) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_v_var.value()?),
            || Ok(next_running_v.value()?),
        )
        .unwrap();
        in_running_v.enforce_equal(&running_v_var)?;
        out_next_running_v.enforce_equal(&next_running_v)?;

        Ok(NLookupWires {
            q,
            v,
            prev_running_q: running_q_vars,
            prev_running_v: running_v_var,
            next_running_q,
            next_running_v,
        })
    }

    fn sum_check(
        &mut self,
        cs: ConstraintSystemRef<A>,
        init_claim: FpVar<A>,
        mut sponge: PoseidonSpongeVar<A>,
        mut temp_eq: Vec<A>,
    ) -> Result<(Vec<FpVar<A>>, FpVar<A>), SynthesisError> {
        let mut temp_table = self.table.clone(); // todo

        // current claim in each round
        let mut claim = init_claim.clone();

        let mut rands = Vec::<FpVar<A>>::new();
        for j in 0..self.ell {
            let (con, x, xsq) = self.prover_msg(j, &temp_table, &temp_eq);

            let g_j_const = FpVar::<A>::new_witness(cs.clone(), || Ok(con))?;
            let g_j_x = FpVar::<A>::new_witness(cs.clone(), || Ok(x))?;
            let g_j_xsq = FpVar::<A>::new_witness(cs.clone(), || Ok(xsq))?;

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
        qi: &Vec<FpVar<A>>,
        r: &Vec<FpVar<A>>,
    ) -> Result<FpVar<A>, SynthesisError> {
        let mut eq = Vec::<FpVar<A>>::new();
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
    fn prover_msg(&self, i: usize, temp_table: &Vec<A>, temp_eq: &Vec<A>) -> (A, A, A) {
        let base: usize = 2;
        let pow: usize = base.pow((self.ell - i - 1) as u32);

        assert_eq!(temp_table.len(), base.pow(self.ell as u32));
        assert_eq!(temp_eq.len(), base.pow(self.ell as u32));

        let mut xsq = A::zero();
        let mut x = A::zero();
        let mut con = A::zero();

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

    fn update_tables(&mut self, r_i: A, i: usize, temp_table: &mut Vec<A>, temp_eq: &mut Vec<A>) {
        let base: usize = 2;
        let pow: usize = base.pow((self.ell - i - 1) as u32);

        for b in 0..pow {
            temp_table[b] = temp_table[b] * (A::one() - r_i) + temp_table[b + pow] * r_i;
            temp_eq[b] = temp_eq[b] * (A::one() - r_i) + temp_eq[b + pow] * r_i;
        }
    }

    fn mle_eval(&self, x: &Vec<A>) -> A {
        assert_eq!(x.len(), self.ell);

        mle_eval(&self.table, x)
    }

    fn gen_eq_table(rho: A, qs: &Vec<usize>, last_q: &Vec<A>) -> Vec<A> {
        let base: usize = 2;
        let ell: usize = last_q.len();
        let t_len = base.pow(ell as u32);

        let mut rhos = Vec::<A>::new();
        rhos.push(rho);
        if qs.len() > 1 {
            for i in 0..(qs.len() - 1) {
                rhos.push(rhos[i] * rho);
            }
        }
        rhos.push(A::one());

        let mut eq_t = vec![A::zero(); t_len];

        for i in 0..qs.len() {
            eq_t[qs[i]] += rhos[i];
        }

        for i in 0..eq_t.len() {
            let mut term = rhos[qs.len()].clone();

            for j in (0..ell).rev() {
                let xi = (i >> j) & 1;
                term *= A::from(xi as u64) * last_q[j]
                    + (A::one() - A::from(xi as u64)) * (A::one() - last_q[j]);
            }
            eq_t[i] += term;
        }

        eq_t
    }

    pub fn verify_running_claim(
        &self,
        verifier_gens: &HyraxPC<E1>,
        q: &Vec<N1>,
        proofs: &mut HashMap<usize, NLProofInfo>,
    ) {
        let ark_q: Vec<A> = q.iter().map(|x| nova_to_ark_field::<N1, A>(x)).collect();

        // TODO - eq proof
        Table::calc_running_claim(
            &self.ordering_info,
            self.small_table_refs.clone(),
            ark_q,
            false,
            Some(verifier_gens),
            proofs,
        );
    }

    pub fn prove_running_claim(
        &self,
        prover_gens: &HyraxPC<E1>,
        q: &Vec<N1>,
    ) -> (Option<A>, HashMap<usize, NLProofInfo>) {
        let ark_q: Vec<A> = q.iter().map(|x| nova_to_ark_field::<N1, A>(x)).collect();

        let mut proofs = HashMap::new();
        let ark_v = Table::calc_running_claim(
            &self.ordering_info,
            self.small_table_refs.clone(),
            ark_q,
            true,
            Some(prover_gens),
            &mut proofs,
        );
        match ark_v {
            VComp::ArkScalar(a) => (Some(a), proofs),
            _ => (None, proofs),
        }
    }
}

// todo add conditional_enforce

mod tests {

    use crate::bellpepper::*;
    use crate::nlookup::*;
    use ark_ff::{Field, PrimeField};
    use ark_pallas::Fr as A;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};
    use nova_snark::provider::hyrax_pc::HyraxPC;
    use nova_snark::traits::Engine;

    fn run_nlookup(
        batch_size: usize,
        qv: Vec<(usize, usize, usize)>,
        tables: Vec<&Table<A>>,
        gens: &HyraxPC<E1>,
    ) {
        let rounds = ((qv.len() as f32) / (batch_size as f32)).ceil() as usize;
        println!("ROUNDS {:#?}", rounds);

        let lookups: Vec<(usize, A, usize)> = qv
            .into_iter()
            .map(|(q, v, t)| (q, A::from(v as u64), t))
            .collect();

        let mut nl = NLookup::new(tables.clone(), batch_size, None);
        let (mut running_q, mut running_v) = nl.first_running_claim();

        for i in 0..rounds {
            let cs = ConstraintSystem::<A>::new_ref();
            cs.set_optimization_goal(OptimizationGoal::Constraints);

            let lu_end = if (i + 1) * batch_size < lookups.len() {
                (i + 1) * batch_size
            } else {
                lookups.len()
            };

            println!("lookups {:#?}", lookups[(i * batch_size)..lu_end].to_vec());

            let res = nl.nlookup_circuit_F(
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

        // obv double conversion is bad - just for testing
        let nova_q = running_q.iter().map(|x| ark_to_nova_field(x)).collect();
        let (v_calc, mut proofs) = nl.prove_running_claim(&gens, &nova_q);
        if v_calc.is_some() {
            assert_eq!(v_calc.unwrap(), running_v);
        }
        nl.verify_running_claim(&gens, &nova_q, &mut proofs);
    }

    #[test]
    fn nl_basic() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let table = Table::new(t, false, 0, None);

        let lookups = vec![(2, 5, 0), (1, 3, 0), (7, 19, 0)];

        let gens = HyraxPC::setup(b"test", logmn(8));
        run_nlookup(3, lookups, vec![&table], &gens);
    }

    #[test]
    fn nl_many_lookups() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let table = Table::new(t, false, 0, None);

        let lookups = vec![
            (2, 5, 0),
            (1, 3, 0),
            (7, 19, 0),
            (2, 5, 0),
            (3, 7, 0),
            (4, 9, 0),
            (0, 2, 0),
            (1, 3, 0),
        ];

        let gens = HyraxPC::setup(b"test", logmn(8));
        run_nlookup(8, lookups.clone(), vec![&table], &gens);
        run_nlookup(4, lookups.clone(), vec![&table], &gens);
        run_nlookup(2, lookups.clone(), vec![&table], &gens);
        run_nlookup(1, lookups.clone(), vec![&table], &gens);
    }

    #[test]
    #[should_panic]
    fn nl_bad_lookup() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let table = Table::new(t, false, 0, None);

        let lookups = vec![(2, 5, 0), (1, 13, 0), (7, 19, 0)];
        let gens = HyraxPC::setup(b"test", logmn(8));
        run_nlookup(3, lookups, vec![&table], &gens);
    }

    #[test]
    fn nl_padding() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let table = Table::new(t, false, 0, None);

        let lookups = vec![(2, 5, 0), (1, 3, 0), (7, 19, 0)];

        let gens = HyraxPC::setup(b"test", logmn(8));
        run_nlookup(4, lookups, vec![&table], &gens);

        let big_lookups = vec![
            (2, 5, 0),
            (1, 3, 0),
            (7, 19, 0),
            (2, 5, 0),
            (3, 7, 0),
            (1, 3, 0),
        ];

        run_nlookup(5, big_lookups, vec![&table], &gens);
    }

    #[test]
    fn nl_hybrid_BAD() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let pub_table = Table::new(t, false, 0, None);

        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let gens = HyraxPC::setup(b"test", logmn(8));
        let priv_table = Table::new(t, true, 1, Some(&gens));

        // let lookups = vec![(2, 5, 0), (1, 3, 0), (0, 23, 1), (4, 41, 1)];
        let lookups = vec![(2, 5, 0), (0, 23, 1), (4, 41, 1)];

        run_nlookup(2, lookups, vec![&pub_table, &priv_table], &gens);
    }

    #[test]
    fn nl_hybrid_size() {
        let t_pre = vec![2, 3, 5];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let pub_table = Table::new(t, false, 19, None);

        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let gens = HyraxPC::setup(b"test", logmn(8));
        let priv_table = Table::new(t, true, 1, Some(&gens));

        let lookups = vec![(2, 5, 19), (1, 3, 19), (0, 2, 19), (0, 23, 1), (4, 41, 1)];

        run_nlookup(2, lookups, vec![&pub_table, &priv_table], &gens);
    }

    #[test]
    #[should_panic]
    fn nl_hybrid_dup_tags() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let pub_table = Table::new(t, false, 4, None);

        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let gens = HyraxPC::setup(b"test", logmn(8));
        let priv_table = Table::new(t, true, 4, Some(&gens));

        let lookups = vec![(2, 5, 0), (1, 3, 0), (0, 23, 1), (4, 41, 1)];

        run_nlookup(2, lookups, vec![&pub_table, &priv_table], &gens);
    }

    #[test]
    #[should_panic]
    fn nl_hybrid_bad_tags() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let pub_table = Table::new(t, false, 0, None);

        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();
        let gens = HyraxPC::setup(b"test", logmn(8));
        let priv_table = Table::new(t, true, 1, Some(&gens));

        let lookups = vec![(2, 5, 0), (1, 3, 1), (0, 23, 1), (4, 41, 1)];

        run_nlookup(2, lookups, vec![&pub_table, &priv_table], &gens);
    }

    #[test]
    fn nl_proj_calc() {
        let tests = vec![
            (8, vec![(0, 4)], Some(vec![(0, 4)])),
            (8, vec![(0, 8)], None),
            (8, vec![(0, 7)], None),
            (8, vec![(1, 3)], Some(vec![(0, 4)])),
            (8, vec![(1, 4), (4, 7)], None),
            (8, vec![(0, 2), (2, 4)], Some(vec![(0, 4)])),
            (8, vec![(0, 2), (0, 4)], Some(vec![(0, 4)])),
            (8, vec![(0, 4), (2, 4)], Some(vec![(0, 4)])),
            (8, vec![(0, 2), (4, 6)], Some(vec![(0, 2), (4, 6)])),
            (8, vec![(4, 6), (0, 2)], Some(vec![(0, 2), (4, 6)])),
            (6, vec![(0, 4)], Some(vec![(0, 4)])),
            (6, vec![(0, 7)], None),
        ];

        for (len, ranges, expected) in tests {
            let t = vec![A::from(3); len];
            let table = Table::new_proj(t, false, ranges, 0, None);

            match expected {
                Some(proj) => assert_eq!(table.proj.unwrap(), proj),
                None => assert!(table.proj.is_none()),
            }
        }
    }

    #[test]
    fn nl_proj() {
        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();

        let tests = vec![
            (vec![(0, 8)], vec![(2, 31, 1), (0, 23, 1), (4, 41, 1)]),
            (vec![(0, 4)], vec![(2, 31, 1), (0, 23, 1), (1, 29, 1)]),
            (vec![(4, 8)], vec![(4, 41, 1), (7, 53, 1), (6, 47, 1)]),
            (
                vec![(0, 2), (4, 6)],
                vec![(4, 41, 1), (0, 23, 1), (5, 43, 1)],
            ),
            (
                vec![(0, 2), (2, 4)],
                vec![(0, 23, 1), (3, 37, 1), (1, 29, 1)],
            ),
        ];

        let gens = HyraxPC::setup(b"test", logmn(t.len()));
        for (ranges, lookups) in tests {
            let table = Table::new_proj(t.clone(), false, ranges, 1, None);

            run_nlookup(2, lookups, vec![&table], &gens);
        }
    }

    #[test]
    #[should_panic]
    fn nl_proj_bad() {
        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();

        let ranges = vec![(1, 4), (6, 8)];
        let table = Table::new_proj(t, false, ranges, 1, None);

        let lookups = vec![(1, 23, 1), (5, 43, 1)];

        let gens = HyraxPC::setup(b"test", logmn(8));
        run_nlookup(2, lookups, vec![&table], &gens);
    }

    #[test]
    fn nl_hybrid_and_proj() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let pub_t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();

        let t_pre = vec![23, 29, 31, 37, 41, 43, 47, 53];
        let priv_t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();

        let tests = vec![
            (
                vec![(0, 8)],
                vec![(0, 8)],
                vec![(2, 5, 0), (0, 23, 1), (4, 41, 1)],
            ),
            (
                vec![(0, 4)],
                vec![(0, 2), (6, 8)],
                vec![(3, 7, 0), (0, 23, 1), (6, 47, 1)],
            ),
            (
                vec![(4, 8)],
                vec![(2, 3), (7, 8)],
                vec![(4, 9, 0), (7, 19, 0), (2, 31, 1), (7, 53, 1)],
            ),
            (
                vec![(0, 8)],
                vec![(0, 2), (4, 6)],
                vec![(4, 41, 1), (0, 23, 1), (5, 13, 0)],
            ),
            (
                vec![(0, 2), (2, 4)],
                vec![(1, 7)],
                vec![(0, 2, 0), (3, 7, 0), (5, 43, 1)],
            ),
        ];

        let gens = HyraxPC::setup(b"test", logmn(priv_t.len()));
        for (pub_ranges, priv_ranges, lookups) in tests {
            let pub_table = Table::new_proj(pub_t.clone(), false, pub_ranges, 0, None);
            let priv_table = Table::new_proj(priv_t.clone(), true, priv_ranges, 1, Some(&gens));

            run_nlookup(2, lookups, vec![&pub_table, &priv_table], &gens);
        }
    }

    #[test]
    fn mle_basic() {
        let mut evals = vec![A::from(2), A::from(6), A::from(5), A::from(14)];

        let table = evals.clone();
        let t = Table::new(table, false, 0, None);
        let mut nl = NLookup::new(vec![&t], 3, None);

        let qs = vec![2, 1, 1];
        let last_q = vec![A::from(5), A::from(4)];

        let rho = A::from(3);

        let running_v = nl.mle_eval(&last_q);

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
        let mut claim: A = evals
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

            let r_i = if i == 0 { A::from(3) } else { A::from(2) };

            let g0_g1 = A::from(2) * &con + &x + &xsq;
            assert_eq!(claim, g0_g1,);

            claim = xsq * &r_i * &r_i + x * &r_i + con;
            nl.update_tables(r_i, i, &mut evals, &mut eq_a);
            sc_rs.push(r_i);
        }

        //sc_rs = sc_rs.into_iter().rev().collect();
        // next
        let next_running_v = nl.mle_eval(&sc_rs);
        println!("nrv {:#?}", next_running_v.clone());

        // sanity check
        // eq_term = rhos * eq(qi, sc_rs_i)
        let mut eq_term = A::from(0);
        println!("loop");
        for i in 0..qs.len() {
            let mut eq = A::from(1);
            for j in (0..nl.ell).rev() {
                let qij = A::from(((qs[i] >> j) & 1) as u64);
                println!(
                    "qij {:#?} -> {:#?}, scrs ij {:#?}",
                    qs[i],
                    ((qs[i] >> j) & 1),
                    sc_rs[j].clone()
                );
                eq *= qij * &sc_rs[nl.ell - j - 1]
                    + (A::from(1) - qij) * (A::from(1) - &sc_rs[nl.ell - j - 1]);
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
        let mut eq = A::from(1);
        for j in (0..nl.ell).rev() {
            let qij = last_q[j];
            eq *= qij * &sc_rs[nl.ell - j - 1]
                + (A::from(1) - qij) * (A::from(1) - &sc_rs[nl.ell - j - 1]);
        }
        println!("last q eq term {:#?}", eq.clone());
        eq_term += eq;
        println!("eq term {:#?}", eq_term.clone());

        // (last) claim == eq_term * next_running_v
        assert_eq!(claim, eq_term * next_running_v);
    }
}
