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
    preimages: Vec<(F, Option<F>)>, // (stack, elem)
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
            preimages: vec![(F::from(0), None)],
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
            let (p, e) = self.preimages.pop().unwrap();
            assert!(e.is_some(), "Trying to pop empty stack");

            (p, e.unwrap())
        } else {
            (F::from(0), F::from(0))
        };

        let (preimage, elem) = (
            FpVar::new_witness(cs.clone(), || Ok(preimage_F))?,
            FpVar::new_witness(cs.clone(), || Ok(elem_F))?,
        );

        let mut sponge = PoseidonSpongeVar::<F>::new(cs.clone(), &self.pcs);
        sponge.absorb(&vec![&preimage, &elem]);
        let hash = sponge.squeeze_field_elements(1)?;
        let out = &hash[0];

        out.conditional_enforce_equal(running_stack, cond);

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
        sponge.absorb(&vec![running_stack, elem]);
        let hash = sponge.squeeze_field_elements(1)?;
        let out = &hash[0];

        if cond.value()? {
            self.preimages.push((out.value()?, Some(elem.value()?)));

            *running_stack = out.clone();
        }

        Ok(())
    }
}
