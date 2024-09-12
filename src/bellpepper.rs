use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
//use ff::Field;
use nova_snark::{
    provider::{PallasEngine, VestaEngine},
    traits::{circuit::StepCircuit, Engine, Group},
};

type E1 = PallasEngine;
type E2 = VestaEngine;
type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

#[derive(Clone, Debug)]
struct FCircuit<G: Group> {
    temp: G::Scalar,
}

impl<G: Group> StepCircuit<G::Scalar> for FCircuit<G> {
    fn arity(&self) -> usize {
        2
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<G::Scalar>],
    ) -> Result<Vec<AllocatedNum<G::Scalar>>, SynthesisError> {
        Ok(z.to_vec())
    }
}

#[cfg(test)]
mod tests {

    fn generate_arkworks_example() {}

    fn run_nova() {
        let circuit_primary = TrivialCircuit::default();
        let circuit_secondary = CubicCircuit::default();

        // produce public parameters
        let pp = PublicParams::<
            E1,
            E2,
            TrivialCircuit<<E1 as Engine>::Scalar>,
            CubicCircuit<<E2 as Engine>::Scalar>,
        >::setup(
            &circuit_primary,
            &circuit_secondary,
            &*default_ck_hint(),
            &*default_ck_hint(),
        )
        .unwrap();

        let num_steps = 3;

        // produce a recursive SNARK
        let mut recursive_snark = RecursiveSNARK::<
            E1,
            E2,
            TrivialCircuit<<E1 as Engine>::Scalar>,
            CubicCircuit<<E2 as Engine>::Scalar>,
        >::new(
            &pp,
            &circuit_primary,
            &circuit_secondary,
            &[<E1 as Engine>::Scalar::ONE],
            &[<E2 as Engine>::Scalar::ZERO],
        )
        .unwrap();

        for _i in 0..num_steps {
            let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
            assert!(res.is_ok());
        }

        // verify the recursive SNARK
        let res = recursive_snark.verify(
            &pp,
            num_steps,
            &[<E1 as Engine>::Scalar::ONE],
            &[<E2 as Engine>::Scalar::ZERO],
        );
        assert!(res.is_ok());

        let (zn_primary, zn_secondary) = res.unwrap();

        // sanity: check the claimed output with a direct computation of the same
        assert_eq!(zn_primary, vec![<E1 as Engine>::Scalar::ONE]);
        let mut zn_secondary_direct = vec![<E2 as Engine>::Scalar::ZERO];
        for _i in 0..num_steps {
            zn_secondary_direct = circuit_secondary.clone().output(&zn_secondary_direct);
        }
        assert_eq!(zn_secondary, zn_secondary_direct);
        assert_eq!(zn_secondary, vec![<E2 as Engine>::Scalar::from(2460515u64)]);

        // produce the prover and verifier keys for compressed snark
        let (pk, vk) = CompressedSNARK::<_, _, _, _, S<E1, EE1>, S<E2, EE2>>::setup(&pp).unwrap();

        // produce a compressed SNARK
        let res = CompressedSNARK::<_, _, _, _, S<E1, EE1>, S<E2, EE2>>::prove(
            &pp,
            &pk,
            &recursive_snark,
        );
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify the compressed SNARK
        let res = compressed_snark.verify(
            &vk,
            num_steps,
            &[<E1 as Engine>::Scalar::ONE],
            &[<E2 as Engine>::Scalar::ZERO],
        );
        assert!(res.is_ok());
    }
}
