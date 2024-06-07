use ark_ff::{fields::PrimeField, Zero};
use ark_pallas::Fr as ScalarField;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NlookupCircuit<F: PrimeField> {
    placeholder: F,
    batch_size: usize,
    _engine: PhantomData<F>,
}

impl<F: PrimeField> NlookupCircuit<F> {
    pub fn new(batch_size: usize) -> Self {
        return NlookupCircuit {
            placeholder: F::zero(),
            batch_size: batch_size,
            _engine: PhantomData,
        };
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for NlookupCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // Here you can add your constraints to the ConstraintSystem `cs`
        // For example:
        // let var = cs.new_witness_variable(|| Ok(self.placeholder))?;
        // cs.enforce_constraint(lc!() + var, lc!() + CS::one(), lc!() + var)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::PairingEngine;
    use ark_ff::Field;
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
    use ark_std::rand::Rng;
    use ark_std::test_rng;

    #[test]
    fn test_1() {
        let rng = &mut test_rng();
        let circuit = NlookupCircuit::new(0);
        test_circuit::<_, _, ark_ec::bls12::Bls12_381>(circuit, rng);
    }

    fn test_circuit<E: PairingEngine, C: ConstraintSynthesizer<E::Fr>, R: Rng>(
        circuit: C,
        rng: &mut R,
    ) {
        // Create an instance of our circuit (with the witness)
        let cs = ConstraintSystem::<E::Fr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();

        // Check that the circuit is satisfied
        assert!(cs.is_satisfied().unwrap());

        // Check that the number of constraints is correct
        assert_eq!(cs.num_constraints(), 0);
    }
}
