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
// we assume for now user is not interested in prev_running_q/v

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
        query.extend(v_vars.clone());
        query.extend(vec![running_v_var.clone()]);
        sponge.absorb(&query)?;

        // sponge squeezed to produce rs
        let hash = sponge.squeeze_field_elements(1)?;
        let rho = &hash[0];

        // LHS of nl equation (vs and ros)
        // running q,v are the "constant" (not hooked to a rho)
        let mut horners_vals = vec![running_v_var.clone()];
        horners_vals.extend(v_vars.clone());
        let init_claim = horners(&horners_vals, &rho);

        let temp_eq = Self::gen_eq_table(
            rho.value().unwrap(),
            &q,
            &running_q.into_iter().rev().collect(),
        );
        let (next_running_q, last_claim) =
            self.sum_check_circuit(cs.clone(), init_claim, sponge, temp_eq)?;

        // last_claim & eq circuit
        let mut eq_evals = vec![FpVar::zero()]; // dummy for horners
        for i in 0..num_lookups + 1 {
            eq_evals.push(self.bit_eq_circuit(i));
        }
        let eq_eval = horners(&eq_evals, &rho);

        let next_running_v = FpVar::<F>::new_witness(cs.clone(), || {
            Ok(mle_eval(
                next_running_q
                    .into_iter()
                    .map(|x| x.value().unwrap())
                    .collect(),
            ))
        })?;

        // last_claim = eq_eval * next_running_claim
        last_claim.enforce_equal(&(eq_eval * next_running_v));

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
    ) -> Result<(Vec<FpVar<F>>, FpVar<F>), SynthesisError> {
        let mut temp_table = self.table_t.clone(); // todo

        // current claim in each round
        let mut claim = init_claim.clone();

        let mut rands = Vec::<FpVar<F>>::new();
        for j in 0..self.ell {
            let (con, x, xsq) = self.prover_msg(j, &temp_table, &temp_eq);

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
            rands.push(hash[0]);
        }

        // last claim
        Ok((rands, claim))
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

    fn gen_eq_table(rho: F, qs: &Vec<usize>, last_q: &Vec<F>) -> Vec<F> {
        let base: usize = 2;
        let ell: usize = last_q.len();
        let t_len = base.pow(ell as u32);

        let mut rhos = Vec::<F>::new();
        rhos.push(rho);
        for i in 0..(qs.len() - 1) {
            rhos.push(rhos[i] * rho);
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
        let table = vec![2, 3, 5, 7, 9, 13, 17, 19];

        let q = vec![2, 1, 7];
        let v = vec![5, 3, 19];

        run_nlookup(3, q, v, table);
    }
}
