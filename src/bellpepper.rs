use ark_ff::{BigInteger, Field as arkField, PrimeField as arkPrimeField};
use ark_relations::r1cs::{ConstraintMatrices, ConstraintSystemRef};
use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::{Field as novaField, PrimeField as novaPrimeField};
use nova_snark::{
    provider::{PallasEngine, VestaEngine},
    traits::{circuit::StepCircuit, Engine, Group as novaGroup},
};

fn ark_to_nova_field<A: arkPrimeField, N: novaPrimeField<Repr = [u8; 32]>>(ark_ff: &A) -> N {
    // ark F -> ark BigInt
    let b = ark_ff.into_bigint();

    // BigInt -> bytes
    let bytes = b.to_bytes_le();

    // bytes -> nova F
    N::from_repr(TryInto::<[u8; 32]>::try_into(bytes).unwrap()).unwrap()
}

fn bellpepper_lc<N: novaPrimeField, CS: ConstraintSystem<N>>(
    alloc_inputs: &[AllocatedNum<N>],
    alloc_wits: &Vec<AllocatedNum<N>>,
    lc: &Vec<(N, usize)>,
    i: usize,
) -> LinearCombination<N> {
    let mut lc_bellpepper = LinearCombination::zero();

    let num_inputs = alloc_inputs.len();

    for (val, idx) in lc {
        if *idx == 0 {
            // constant
            lc_bellpepper = lc_bellpepper + (*val, CS::one());
        } else if *idx <= num_inputs {
            // input
            lc_bellpepper = lc_bellpepper + (*val, alloc_inputs[*idx - 1].get_variable());
        } else {
            // witness
            lc_bellpepper =
                lc_bellpepper + (*val, alloc_wits[*idx - 1 - num_inputs].get_variable());
        }
    }

    lc_bellpepper
}

#[derive(Clone, Debug)]
struct FCircuit<N: novaPrimeField<Repr = [u8; 32]>> {
    //ark_matrices: Vec<ConstraintMatrices<F>>,
    lcs: Vec<(Vec<(N, usize)>, Vec<(N, usize)>, Vec<(N, usize)>)>,
    wit_assignments: Vec<N>,
    output_assignments: Vec<N>, // TODO split this for recursive!
    z_len: usize,
}

impl<N: novaPrimeField<Repr = [u8; 32]>> FCircuit<N> {
    // make circuits and witnesses for round i
    pub fn new<A: arkPrimeField>(ark_cs_ref: ConstraintSystemRef<A>) -> (Self, Vec<N>) {
        ark_cs_ref.finalize();
        let ark_cs = ark_cs_ref.borrow().unwrap();

        assert_eq!(ark_cs.instance_assignment[0], A::one());

        let io_assignments: Vec<N> = ark_cs
            .instance_assignment
            .iter()
            .skip(1) // this is always a constant one
            .map(|f| ark_to_nova_field(f))
            .collect(); // this is ouput and used as zi
        let wit_assignments = ark_cs
            .witness_assignment
            .iter()
            .map(|f| ark_to_nova_field(f))
            .collect();

        let ark_matrices = ark_cs.to_matrices().unwrap();
        let mut lcs = Vec::new();
        for i in 0..ark_matrices.a.len() {
            lcs.push((
                ark_matrices.a[i]
                    .iter()
                    .map(|(val, index)| (ark_to_nova_field(val), *index))
                    .collect(),
                ark_matrices.b[i]
                    .iter()
                    .map(|(val, index)| (ark_to_nova_field(val), *index))
                    .collect(),
                ark_matrices.c[i]
                    .iter()
                    .map(|(val, index)| (ark_to_nova_field(val), *index))
                    .collect(),
            ));
        }

        (
            FCircuit {
                lcs,
                wit_assignments,
                output_assignments: Vec::new(), // TODO!
                z_len: io_assignments.len(),
            },
            io_assignments,
        )
    }
}

impl<N: novaPrimeField<Repr = [u8; 32]>> StepCircuit<N> for FCircuit<N> {
    fn arity(&self) -> usize {
        self.z_len
    }

    fn synthesize<CS: ConstraintSystem<N>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<N>],
    ) -> Result<Vec<AllocatedNum<N>>, SynthesisError> {
        // io already allocated in z
        assert_eq!(z.len(), self.z_len);

        // allocate all wits
        let mut alloc_wits = Vec::new();
        for (i, w) in self.wit_assignments.iter().enumerate() {
            alloc_wits.push(AllocatedNum::alloc(
                cs.namespace(|| format!("wit {}", i)),
                || Ok(*w),
            )?)
        }

        // add constraints
        for (i, (a, b, c)) in self.lcs.iter().enumerate() {
            let a_lc = bellpepper_lc::<N, CS>(z, &alloc_wits, a, i);
            let b_lc = bellpepper_lc::<N, CS>(z, &alloc_wits, b, i);
            let c_lc = bellpepper_lc::<N, CS>(z, &alloc_wits, c, i);
            cs.enforce(|| format!("con{}", i), |_| a_lc, |_| b_lc, |_| c_lc);
        }

        Ok(z.to_vec())
    }
}

#[cfg(test)]
mod tests {

    use crate::bellpepper::*;
    use ark_ff::{BigInt, One};
    use ark_relations::{
        lc,
        r1cs::{ConstraintSystem, Variable},
    };
    use ff::PrimeField as novaPrimeField;
    use nova_snark::{
        traits::{
            circuit::TrivialCircuit, evaluation::EvaluationEngineTrait, snark::default_ck_hint,
            Group,
        },
        CompressedSNARK, PublicParams, RecursiveSNARK,
    };

    type NG = pasta_curves::pallas::Point;
    type AF = ark_pallas::Fr;

    type E1 = PallasEngine;
    type E2 = VestaEngine;
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

    #[test]
    fn ff_convert() {
        for v in vec![0, 1, 13, std::u64::MAX] {
            let ark_val = AF::from(v);
            let nova_val: <NG as Group>::Scalar = ark_to_nova_field(&ark_val);
            assert_eq!(nova_val, <NG as Group>::Scalar::from(v));
        }

        // modulus
        let mut biggest = AF::MODULUS;
        biggest.sub_with_borrow(&BigInt::from(1u64));
        let ark_biggest: AF = biggest.into();
        let nova_val: <NG as Group>::Scalar = ark_to_nova_field(&ark_biggest);
        assert_eq!(
            nova_val,
            <NG as Group>::Scalar::ZERO - <NG as Group>::Scalar::ONE
        );
    }

    #[test]
    fn arkworks_example() {
        let cs = ConstraintSystem::<AF>::new_ref();
        let two = AF::one() + AF::one();
        let a = cs.new_input_variable(|| Ok(AF::one())).unwrap();
        let b = cs.new_witness_variable(|| Ok(AF::one())).unwrap();
        let c = cs.new_witness_variable(|| Ok(two)).unwrap();
        cs.enforce_constraint(lc!() + a, lc!() + (two, b), lc!() + c)
            .unwrap();
        let d = cs.new_lc(lc!() + a + b).unwrap();
        cs.enforce_constraint(lc!() + a, lc!() + d, lc!() + d)
            .unwrap();
        let e = cs.new_lc(lc!() + d + d).unwrap();
        cs.enforce_constraint(lc!() + Variable::One, lc!() + e, lc!() + e)
            .unwrap();
        // TODO bug??
        //cs.inline_all_lcs();
        //cs.finalize();
        //assert!(cs.is_satisfied().unwrap());
        //println!("SAT");

        let (bp_circuit, z0) = FCircuit::new(cs);

        run_nova(bp_circuit, z0);
    }

    fn run_nova(
        circuit_primary: FCircuit<<NG as Group>::Scalar>,
        z0_primary: Vec<<NG as Group>::Scalar>,
    ) {
        let circuit_secondary = TrivialCircuit::default();

        // produce public parameters
        let pp = PublicParams::<
            E1,
            E2,
            FCircuit<<E1 as Engine>::Scalar>,
            TrivialCircuit<<E2 as Engine>::Scalar>,
        >::setup(
            &circuit_primary,
            &circuit_secondary,
            &*default_ck_hint(),
            &*default_ck_hint(),
        )
        .unwrap();

        let num_steps = 1;

        // produce a recursive SNARK
        let mut recursive_snark = RecursiveSNARK::<
            E1,
            E2,
            FCircuit<<E1 as Engine>::Scalar>,
            TrivialCircuit<<E2 as Engine>::Scalar>,
        >::new(
            &pp,
            &circuit_primary,
            &circuit_secondary,
            &z0_primary,
            &[<E2 as Engine>::Scalar::ZERO],
        )
        .unwrap();

        for _i in 0..num_steps {
            let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
            assert!(res.is_ok());
        }

        // verify the recursive SNARK
        let res =
            recursive_snark.verify(&pp, num_steps, &z0_primary, &[<E2 as Engine>::Scalar::ZERO]);
        assert!(res.is_ok());

        let (zn_primary, zn_secondary) = res.unwrap();

        // produce the prover and verifier keys for compressed snark
        let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

        // produce a compressed SNARK
        let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify the compressed SNARK
        let res =
            compressed_snark.verify(&vk, num_steps, &z0_primary, &[<E2 as Engine>::Scalar::ZERO]);
        assert!(res.is_ok());
    }
}
