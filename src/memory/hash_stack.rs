use crate::utils::construct_poseidon_parameters_internal;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};

#[derive(Clone, Debug)]
pub struct HashStack<F: PrimeField> {
    pcs: PoseidonConfig<F>,
    preimages: Vec<(F, F)>, // (stack, elem)
}

// you can make this only once - can be used across different arkworks ConstraintSystemRefs
// (different IVC rounds)
// stack designed to be completely internal
impl<F: PrimeField> HashStack<F> {
    pub fn new() -> Self {
        // initalize sponge constants
        let pcs: PoseidonConfig<F> =
            construct_poseidon_parameters_internal(2, 8, 56, 4, 5).unwrap(); //correct?

        Self {
            pcs,
            preimages: Vec::new(),
        }
    }

    pub fn pop(
        &mut self,
        cs: ConstraintSystemRef<F>,
        running_stack: &mut FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        self.conditional_pop(cs, &Boolean::TRUE, running_stack)
    }

    pub fn conditional_pop(
        &mut self,
        cs: ConstraintSystemRef<F>,
        cond: &Boolean<F>,
        running_stack: &mut FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let (preimage_F, elem_F) = if cond.value()? {
            let top = self.preimages.pop();
            assert!(top.is_some(), "Trying to pop empty stack");
            top.unwrap()
        } else {
            (F::from(0), F::from(0))
        };

        let (preimage, elem) = (
            FpVar::new_witness(cs.clone(), || Ok(preimage_F))?,
            FpVar::new_witness(cs.clone(), || Ok(elem_F))?,
        );

        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), &self.pcs);
        sponge.absorb(&vec![&preimage, &elem])?;
        let hash = sponge.squeeze_field_elements(1)?;
        let out = &hash[0];

        out.conditional_enforce_equal(running_stack, cond)?;

        if cond.value()? {
            *running_stack = preimage;
        }

        Ok(elem)
    }

    pub fn push(
        &mut self,
        cs: ConstraintSystemRef<F>,
        elem: &FpVar<F>,
        running_stack: &mut FpVar<F>,
    ) -> Result<(), SynthesisError> {
        self.conditional_push(cs, &Boolean::TRUE, elem, running_stack)
    }

    pub fn conditional_push(
        &mut self,
        cs: ConstraintSystemRef<F>,
        cond: &Boolean<F>,
        elem: &FpVar<F>,
        running_stack: &mut FpVar<F>,
    ) -> Result<(), SynthesisError> {
        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), &self.pcs);
        sponge.absorb(&vec![running_stack, elem])?;
        let hash = sponge.squeeze_field_elements(1)?;
        let out = &hash[0];

        if cond.value()? {
            self.preimages.push((running_stack.value()?, elem.value()?));

            *running_stack = out.clone();
        }

        Ok(())
    }
}

mod tests {
    use crate::bellpepper::AllocIoVar;
    use crate::memory::hash_stack::HashStack;
    use ark_ff::PrimeField;
    use ark_pallas::Fr as F;
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, SynthesisError};
    use ark_std::test_rng;

    // pattern: true == push, false == pop
    fn run_stack<F: PrimeField>(
        pattern: Vec<bool>,
        vals: Vec<Vec<F>>,
        should_clear_stack: bool,
    ) -> Result<(), SynthesisError> {
        let mut num_cs = 0;

        let mut hs: HashStack<F> = HashStack::new();
        let mut running_stack_F = F::zero();

        let rounds = vals.len();

        // test w and w/out conditional push/pop
        for conditional_test in vec![true, false] {
            for i in 0..rounds {
                // ivc rounds

                assert_eq!(vals[i].len(), pattern.len());

                let cs = ConstraintSystem::<F>::new_ref();
                cs.set_optimization_goal(OptimizationGoal::Constraints);

                // set up cond that won't be optimized away
                let cond_a = FpVar::new_witness(cs.clone(), || Ok(F::rand(&mut test_rng())))?;
                let cond_b = FpVar::new_witness(cs.clone(), || Ok(F::rand(&mut test_rng())))?;
                let cond = cond_a.is_eq(&cond_b)?;

                // this is a changeable ptr
                let mut running_stack = FpVar::new_witness(cs.clone(), || Ok(running_stack_F))?;
                let running_stack_in = running_stack.clone();

                for p in 0..pattern.len() {
                    if pattern[p] {
                        // push
                        println!("push {:#?}", vals[i][p]);

                        let elem = FpVar::new_witness(cs.clone(), || Ok(vals[i][p]))?;
                        if conditional_test {
                            hs.conditional_push(cs.clone(), &cond, &elem, &mut running_stack)?;
                        } else {
                            hs.push(cs.clone(), &elem, &mut running_stack)?;
                        }
                    } else {
                        //pop
                        println!("pop {:#?}", vals[i][p]);

                        let popped = if conditional_test {
                            hs.conditional_pop(cs.clone(), &cond, &mut running_stack)?
                        } else {
                            hs.pop(cs.clone(), &mut running_stack)?
                        };
                        assert_eq!(popped.value()?, vals[i][p]);
                    }
                }

                let (rs_in, rs_out) = FpVar::new_input_output_pair(
                    cs.clone(),
                    || Ok(running_stack_F),
                    || Ok(running_stack.value()?),
                )?;
                rs_in.enforce_equal(&running_stack_in)?;
                rs_out.enforce_equal(&running_stack)?;

                // bc we don't pass cs between rounds!
                running_stack_F = running_stack.value()?;

                cs.finalize();
                assert!(cs.is_satisfied().unwrap(), "Failed at iter {}", i);

                if should_clear_stack {
                    assert_eq!(running_stack_F, F::zero());
                } else {
                    assert!(running_stack_F != F::zero());
                }

                if i == 0 {
                    num_cs = cs.num_constraints();
                    println!("num cs {:#?}", num_cs);
                } else {
                    assert_eq!(num_cs, cs.num_constraints());
                }
            }
        }
        Ok(())
    }

    #[test]
    fn hash_stack_ex() {
        // push, pop
        run_stack(vec![true, false], vec![vec![F::from(1), F::from(1)]], true).unwrap();

        // push, push, pop, pop
        run_stack(
            vec![true, true, false, false],
            vec![
                vec![F::from(1), F::from(2), F::from(2), F::from(1)],
                vec![F::from(10), F::from(4), F::from(4), F::from(10)],
                vec![F::from(3), F::from(0), F::from(0), F::from(3)],
            ],
            true,
        )
        .unwrap();

        // push, pop, push, pop
        run_stack(
            vec![true, false, true, false],
            vec![
                vec![F::from(1), F::from(1), F::from(2), F::from(2)],
                vec![F::from(4), F::from(4), F::from(10), F::from(10)],
                vec![F::from(3), F::from(3), F::from(0), F::from(0)],
            ],
            true,
        )
        .unwrap();

        // push, pop, push, push, pop
        run_stack(
            vec![true, false, true, true, false],
            vec![
                vec![F::from(1), F::from(1), F::from(2), F::from(3), F::from(3)],
                vec![F::from(10), F::from(10), F::from(4), F::from(5), F::from(5)],
                vec![F::from(0), F::from(0), F::from(3), F::from(2), F::from(2)],
            ],
            false,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn hash_stack_wrong_pop() {
        run_stack(vec![true, false], vec![vec![F::from(5), F::from(0)]], true).unwrap();
    }

    #[test]
    #[should_panic]
    fn hash_stack_no_finish() {
        run_stack(vec![true], vec![vec![F::from(5)]], true).unwrap();
    }
}
