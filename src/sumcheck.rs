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

#[derive(Clone, Debug)]
pub struct SumCheck<F: PrimeField> {
    ell: usize,
    poly: Vec<(F, F, F)>, // const, x, x^2
    table_t: Vec<F>,
    table_eq: Vec<F>,
}

impl<F: PrimeField> SumCheck<F> {
    pub fn new(table_t: Vec<F>, q: Vec<usize>, v: Vec<F>) -> Self {
        let ell = logmn(table_t.len());
        assert_eq!(q.len(), v.len());

        let poly = vec![]; // TODO
        let rs = vec![];

        let table_eq = gen_eq_table(rs, qs, last_q);

        SumCheck {
            ell,
            poly,
            table_t,
            table_eq,
        }
    }

    pub fn make_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        init_claim: FpVar<F>,
        num_rounds: usize,
        id: &str,
    ) -> Result<FpVar<F>, SynthesisError> {
        // current claim in each round
        let mut claim = init_claim.clone();

        for j in 0..num_rounds {
            // For each round j, we allocate a new variable g_j representing the claim of the current round
            // We use AllocatedNum::alloc to allocate the variable and provide a closure that returns the value of the current claim

            // A, B, C -> these should get their actual values from prover computations
            // First, we need to get the allocated numbers corresponding to the variables
            let g_j_const = FpVar::<F>::new_witness(cs.clone(), || Ok(self.poly[j].0))?;
            let g_j_x = FpVar::<F>::new_witness(cs.clone(), || Ok(self.poly[j].1))?;
            let g_j_xsq = FpVar::<F>::new_witness(cs.clone(), || Ok(self.poly[j].2))?;

            // We enforce a constraint that checks the consistency of the claim between round
            // claim (either is init_claim or was set last loop to be g_j-1(r_j-1)) == g(0) + g(1) ==
            // xsq_coeff + x_coeff + const + const

            claim.enforce_equal(&(&g_j_const + &g_j_const + &g_j_x + &g_j_xsq))?;

            let r_j = FpVar::<F>::new_witness(cs.clone(), || Ok(F::one()))?;

            // Then, we construct the polynomial using the allocated numbers
            // horner's g_j(r_j) -> (((xsq * r) + x)*r + const)
            claim = ((&g_j_xsq * &r_j) + &g_j_x) * &r_j + &g_j_const;

            // If it's the last round, we allocate a variable for the final claim and push it to the out vector
        }

        Ok(claim)
    }

    // starts with evals on hypercube
    fn prover_msg<F: PrimeField>(
        &self,
        //    table_t: &mut Vec<Integer>,
        //    table_eq: &mut Vec<Integer>,
        //    ell: usize,
        i: usize,
        //    sponge: &mut Sponge<F, typenum::U4>,
    ) -> (F, F, F, F) {
        let base: usize = 2;
        let pow: usize = base.pow((ell - i) as u32);
        //assert_eq!(table_t.len(), base.pow(ell as u32));
        //assert_eq!(table_eq.len(), base.pow(ell as u32));

        let mut xsq = F::zero();
        let mut x = F::zero();
        let mut con = F::zero();

        for b in 0..pow {
            let ti_0 = &self.table_t[b];
            let ti_1 = &self.table_t[b + pow];
            let ei_0 = &self.table_eq[b];
            let ei_1 = &self.table_eq[b + pow];

            let t_slope = ti_1 - ti_0;
            let e_slope = ei_1 - ei_0;

            xsq += t_slope * &e_slope;
            x += e_slope * ti_0;
            x += t_slope * ei_0;
            con += ti_0 * ei_0;
        }
        // todo V
        let query = vec![
            int_to_ff(con.clone()),
            int_to_ff(x.clone()),
            int_to_ff(xsq.clone()),
        ];

        let acc = &mut ();
        SpongeAPI::absorb(sponge, 3, &query, acc);
        let rand = SpongeAPI::squeeze(sponge, 1, acc);
        let r_i = Integer::from_digits(rand[0].to_repr().as_ref(), Order::Lsf);

        for b in 0..pow {
            table_t[b] = &table_t[b] * (F::one() - &r_i) + &table_t[b + pow] * &r_i;
            table_eq[b] = &table_eq[b] * (F::one() - &r_i) + &table_eq[b + pow] * &r_i;
        }

        (r_i, xsq, x, con)
    }
}

// helper functions
fn gen_eq_table(rs: &Vec<F>, qs: &Vec<usize>, last_q: &Vec<F>) -> Vec<F> {
    let base: usize = 2;
    let ell: usize = last_q.len();

    let t_len = base.pow(ell as u32);
    assert_eq!(rs.len(), qs.len() + 1);

    let mut eq_t = vec![F::zero(); t_len];

    for i in 0..qs.len() {
        eq_t[qs[i]] += &rs[i];
    }

    for i in 0..eq_t.len() {
        let mut term = rs[qs.len()].clone();

        for j in (0..ell).rev() {
            let xi = (i >> j) & 1;

            term *= F::from(xi) * &last_q[j] + F::from(1 - xi) * (F::one() - &last_q[j]);
        }
        eq_t[i] += term;
    }

    eq_t
}

mod tests {}
