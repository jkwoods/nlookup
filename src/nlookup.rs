use crate::utils::*;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar, ToConstraintFieldGadget,
};
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};
use ark_std::test_rng;

pub struct NLookupWires<F: PrimeField> {
    qs: Vec<Vec<Boolean<F>>>,
    vs: Vec<FpVar<F>>,
    next_running_q: Vec<FpVar<F>>,
    next_running_v: FpVar<F>,
}

#[derive(Clone, Debug)]
pub struct NLookup<F: PrimeField> {
    ell: usize,
    table_t: Vec<F>,
    table_pub: bool, // T pub or priv?
    table_eq: Vec<F>,
}

// sumcheck for one round; q,v,eq table will change per round
impl<F: PrimeField> NLookup<F> {
    pub fn new(table_t: Vec<F>, table_pub: bool) -> Self {
        let ell = logmn(table_t.len());

        NLookup {
            ell,
            table_t,
            table_pub,
            table_eq: Vec::<F>::new(),
        }
    }

    // qs, vs taken in just as witnesses, fpvar wires returned
    fn nlookup_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        q: Vec<usize>,
        v: Vec<F>,
        running_q: Vec<FpVar<F>>,
        running_v: FpVar<F>,
    ) -> Result<NLookupWires<F>, SynthesisError> {
        assert_eq!(q.len(), v.len());
        assert_eq!(self.ell, running_q.len());

        // q processing (combine)
        // sponge aborbs qs, vs, running q, running v, and possibly doc commit
        // sponge squeezed to produce rs

        let rs = vec![];
        let last_q = vec![];
        self.table_eq = Self::gen_eq_table(&rs, &q, &running_q);

        // LHS of nl equation (vs and ros)
        let init_claim = FpVar::<F>::new_witness(cs.clone(), || Ok(F::zero()))?;

        let last_claim = self.sum_check_circuit(cs, init_claim, sponge);

        // last_claim & eq circuit

        let next_running_q = vec![];
        let next_running_v = FpVar::<F>::new_witness(cs.clone(), || Ok(F::zero()))?;
        (next_running_q, next_running_v)
    }

    fn sum_check_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        init_claim: FpVar<F>,
        sponge: PoseidonSponge,
    ) -> Result<FpVar<F>, SynthesisError> {
        // current claim in each round
        let mut claim = init_claim.clone();

        for j in 0..self.ell {
            let (con, x, xsq) = self.prover_msg(j + 1);

            let g_j_const = FpVar::<F>::new_witness(cs.clone(), || Ok(con))?;
            let g_j_x = FpVar::<F>::new_witness(cs.clone(), || Ok(x))?;
            let g_j_xsq = FpVar::<F>::new_witness(cs.clone(), || Ok(xsq))?;

            claim.enforce_equal(&(&g_j_const + &g_j_const + &g_j_x + &g_j_xsq))?;

            let r_j = FpVar::<F>::new_witness(cs.clone(), || Ok(F::one()))?;

            self.update_tables(r_j.value()?, j + 1);

            claim = ((&g_j_xsq * &r_j) + &g_j_x) * &r_j + &g_j_const;
        }

        // last claim
        Ok(claim)
    }

    // starts with evals on hypercube
    fn prover_msg(
        &self,
        //    table_t: &mut Vec<Integer>,
        //    table_eq: &mut Vec<Integer>,
        //    ell: usize,
        i: usize,
        //    sponge: &mut Sponge<F, typenum::U4>,
    ) -> (F, F, F) {
        let base: usize = 2;
        let pow: usize = base.pow((self.ell - i) as u32);
        assert_eq!(self.table_t.len(), base.pow(self.ell as u32));
        assert_eq!(self.table_eq.len(), base.pow(self.ell as u32));

        let mut xsq = F::zero();
        let mut x = F::zero();
        let mut con = F::zero();

        for b in 0..pow {
            let ti_0 = self.table_t[b];
            let ti_1 = self.table_t[b + pow];
            let ei_0 = self.table_eq[b];
            let ei_1 = self.table_eq[b + pow];

            let t_slope = ti_1 - ti_0;
            let e_slope = ei_1 - ei_0;

            xsq += t_slope * e_slope;
            x += e_slope * ti_0;
            x += t_slope * ei_0;
            con += ti_0 * ei_0;
        }

        (con, x, xsq)
    }

    fn update_tables(&mut self, r_i: F, i: usize) {
        let base: usize = 2;
        let pow: usize = base.pow((self.ell - i) as u32);

        for b in 0..pow {
            self.table_t[b] = self.table_t[b] * (F::one() - r_i) + self.table_t[b + pow] * r_i;
            self.table_eq[b] = self.table_eq[b] * (F::one() - r_i) + self.table_eq[b + pow] * r_i;
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

mod tests {}
