use ark_ff::{fields::PrimeField, Zero};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError};
use ark_std::marker::PhantomData;

type G1 = ark_ec::ProjectiveCurve;
type G2 = ark_ec::ProjectiveCurve;
type C1 = NlookupCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

use nova_ark::traits::{
    circuit::{StepCircuit, TrivialTestCircuit},
    Group,
};
use nova_ark::CompressedSNARK;
use nova_ark::PublicParams;
use nova_ark::RecursiveSNARK;
use nova_ark::StepCounterType;
use nova_ark::FINAL_EXTERNAL_COUNTER;

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

    use crate::circuit::*;

    #[test]
    fn test_1() {
        let circuit_primary: NlookupCircuit<<G1 as Group>::Scalar> = NlookupCircuit::new(0);

        // trivial circuit
        let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

        // produce public parameters
        let pp = PublicParams::<
            G1,
            G2,
            NlookupCircuit<<G1 as Group>::Scalar>,
            TrivialTestCircuit<<G2 as Group>::Scalar>,
        >::setup(circuit_primary.clone(), circuit_secondary.clone())
        .unwrap();

        println!(
            "Number of constraints (primary circuit): {}",
            pp.num_constraints().0
        );
        println!(
            "Number of constraints (secondary circuit): {}",
            pp.num_constraints().1
        );

        println!(
            "Number of variables (primary circuit): {}",
            pp.num_variables().0
        );
        println!(
            "Number of variables (secondary circuit): {}",
            pp.num_variables().1
        );

        let z0_primary = vec![
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::from(4),
        ];
        let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

        let mut recursive_snark = None;

        // prover folds
        for i in 0..3 {
            println!("Proving step {}", i);

            let result = RecursiveSNARK::prove_step(
                &pp,
                recursive_snark,
                circuit_primary.clone(),
                circuit_secondary.clone(),
                z0_primary.clone(),
                z0_secondary.clone(),
            );

            recursive_snark = Some(result.unwrap());
        }

        assert!(recursive_snark.is_some());
        let recursive_snark = recursive_snark.unwrap();

        // prover compresses final SNARK
        let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);

        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify
        let res = compressed_snark.verify(&pp, FINAL_EXTERNAL_COUNTER, z0_primary, z0_secondary);

        assert!(res.is_ok());
    }
}
