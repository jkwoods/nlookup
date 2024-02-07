type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = NlookupCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, Namespace, SynthesisError,
    Variable,
};
use ff::{Field, PrimeField};
use neptune::{
    circuit2::Elt,
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{Mode, SpongeTrait},
};

use nova_snark::{
    traits::{
        circuit::{StepCircuit, TrivialTestCircuit},
        Group,
    },
    CompressedSNARK, PublicParams, RecursiveSNARK, StepCounterType, FINAL_EXTERNAL_COUNTER,
};

#[derive(Clone, Debug)]
pub struct NlookupCircuit<F: PrimeField> {
    placeholder: F,
    batch_size: usize,
}

impl<F: PrimeField> NlookupCircuit<F> {
    pub fn new(batch_size: usize) -> Self {
        return NlookupCircuit {
            placeholder: F::zero(),
            batch_size: batch_size,
        };
    }

    fn internal_gadget_example<CS>(&self, cs: &mut CS) -> Result<AllocatedNum<F>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let allocated_witness =
            AllocatedNum::alloc(cs.namespace(|| "unique_name"), || Ok(self.placeholder))?;

        return Ok(allocated_witness);
    }
}

impl<F: PrimeField> StepCircuit<F> for NlookupCircuit<F> {
    // nova wants this to return the "output" of each step
    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
    {
        // inputs
        let alloc_z0 = z[0].clone();
        let alloc_z1 = z[1].clone();

        let alloc_placeholder = self.internal_gadget_example(cs)?;

        cs.enforce(
            || format!("z0 * (z1 + 1) == placeholder"),
            |lc| lc + alloc_z0.get_variable(),
            |lc| lc + alloc_z1.get_variable() + CS::one(),
            |lc| lc + alloc_placeholder.get_variable(),
        );

        // outputs
        let out = vec![alloc_z0, alloc_z1];
        return Ok(out);
    }

    // arity = len of i/o vector z
    fn arity(&self) -> usize {
        return 2;
    }

    // this function does not make constraints, but you have to have it (stupid)
    // it's usually used as a sanity check that your synthesize() is outputing what you expect
    fn output(&self, z: &[F]) -> Vec<F> {
        assert!(z.len() == 2);
        return z.to_vec(); // right now the input == output, this should change eventually
    }

    // can leave this as is
    fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::External
    }
}

// external helper functions/gadgets

// ret = if condition, a, else b
// condition must be asserted to be 0 or 1 somewhere else
fn select<F, CS>(
    cs: &mut CS,
    cond: AllocatedNum<F>,
    a: AllocatedNum<F>,
    b: AllocatedNum<F>,
    tag: &String,
) -> Result<AllocatedNum<F>, SynthesisError>
where
    F: PrimeField,
    CS: ConstraintSystem<F>,
{
    let ret = AllocatedNum::alloc(cs.namespace(|| format!("ret {}", tag)), || {
        Ok(b.get_value().unwrap()
            + cond.get_value().unwrap() * (a.get_value().unwrap() - b.get_value().unwrap()))
    })?;

    // RET = B + COND * (A - B) <- ite
    cs.enforce(
        || format!("ite {}", tag),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + cond.get_variable(),
        |lc| lc + ret.get_variable() - b.get_variable(),
    );

    return Ok(ret);
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
