use ark_ff::{BigInteger, Field as arkField, PrimeField as arkPrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSystemRef, Namespace, SynthesisError as arkSynthesisError,
};
use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError as bpSynthesisError,
};
use core::borrow::Borrow;
use ff::{Field as novaField, PrimeField as novaPrimeField};
use nova_snark::{
    provider::{PallasEngine, VestaEngine},
    traits::{circuit::StepCircuit, Engine, Group as novaGroup},
};

pub trait AllocIoVar<V: ?Sized, A: arkField>: Sized + AllocVar<V, A> {
    /// Allocates a new input/output pair of type `Self` in the `ConstraintSystem`
    /// `cs`.
    fn new_input_output_pair<T: Borrow<V>>(
        cs: impl Into<Namespace<A>> + Clone,
        f_in: impl FnOnce() -> Result<T, arkSynthesisError>,
        f_out: impl FnOnce() -> Result<T, arkSynthesisError>,
    ) -> Result<(Self, Self), arkSynthesisError> {
        let alloc_in = Self::new_variable(cs.clone(), f_in, AllocationMode::Input)?;
        let alloc_out = Self::new_variable(cs, f_out, AllocationMode::Input)?;

        Ok((alloc_in, alloc_out))
    }
}

impl<A: arkField> AllocIoVar<bool, A> for Boolean<A> {}
impl<A: arkPrimeField> AllocIoVar<A, A> for FpVar<A> {}

fn ark_to_nova_field<A: arkPrimeField, N: novaPrimeField<Repr = [u8; 32]>>(ark_ff: &A) -> N {
    // ark F -> ark BigInt
    let b = ark_ff.into_bigint();

    // BigInt -> bytes
    let bytes = b.to_bytes_le();

    // bytes -> nova F
    N::from_repr(TryInto::<[u8; 32]>::try_into(bytes).unwrap()).unwrap()
}

fn bellpepper_lc<N: novaPrimeField, CS: ConstraintSystem<N>>(
    alloc_io: &Vec<AllocatedNum<N>>,
    alloc_wits: &Vec<AllocatedNum<N>>,
    lc: &Vec<(N, usize)>,
    i: usize,
) -> LinearCombination<N> {
    let mut lc_bellpepper = LinearCombination::zero();

    let num_io = alloc_io.len();

    for (val, idx) in lc {
        if *idx == 0 {
            // constant
            lc_bellpepper = lc_bellpepper + (*val, CS::one());
        } else if *idx <= num_io {
            // input
            lc_bellpepper = lc_bellpepper + (*val, alloc_io[*idx - 1].get_variable());
        } else {
            // witness
            lc_bellpepper = lc_bellpepper + (*val, alloc_wits[*idx - 1 - num_io].get_variable());
        }
    }

    lc_bellpepper
}

#[derive(Clone, Debug)]
struct FCircuit<N: novaPrimeField<Repr = [u8; 32]>> {
    //ark_matrices: Vec<ConstraintMatrices<F>>,
    lcs: Vec<(Vec<(N, usize)>, Vec<(N, usize)>, Vec<(N, usize)>)>,
    wit_assignments: Vec<N>,
    input_assignments: Vec<N>,
    output_assignments: Vec<N>,
}

impl<N: novaPrimeField<Repr = [u8; 32]>> FCircuit<N> {
    // make circuits and witnesses for round i
    // the ark_cs should only have witness and input/output PAIRs
    // (i.e. a user should have never called new_input())
    pub fn new<A: arkPrimeField>(ark_cs_ref: ConstraintSystemRef<A>) -> Self {
        ark_cs_ref.finalize();
        let ark_cs = ark_cs_ref.borrow().unwrap();

        // io pairs + constant
        assert_eq!(ark_cs.instance_assignment[0], A::one());
        assert_eq!(ark_cs.instance_assignment.len() % 2, 1);

        let mut input_assignments = Vec::new();
        let mut output_assignments = Vec::new();
        for (i, io) in ark_cs.instance_assignment.iter().skip(1).enumerate() {
            if i % 2 == 0 {
                // input
                input_assignments.push(ark_to_nova_field(io));
            } else {
                // output
                output_assignments.push(ark_to_nova_field(io));
            }
        }

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

        FCircuit {
            lcs,
            input_assignments,
            output_assignments,
            wit_assignments,
        }
    }

    // call this to get your first inputs to IVC
    pub fn get_zi(&self) -> &Vec<N> {
        return &self.input_assignments;
    }

    pub fn get_z_i_plus_1(&self) -> &Vec<N> {
        return &self.output_assignments;
    }
}

impl<N: novaPrimeField<Repr = [u8; 32]>> StepCircuit<N> for FCircuit<N> {
    fn arity(&self) -> usize {
        self.output_assignments.len()
    }

    fn synthesize<CS: ConstraintSystem<N>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<N>],
    ) -> Result<Vec<AllocatedNum<N>>, bpSynthesisError> {
        // input already allocated in z
        assert_eq!(z.len(), self.input_assignments.len());

        // alloc outputs
        let mut alloc_out = Vec::new();
        for (i, v) in self.output_assignments.iter().enumerate() {
            alloc_out.push(AllocatedNum::alloc(
                cs.namespace(|| format!("out {}", i)),
                || Ok(*v),
            )?)
        }

        // combine io
        let mut alloc_io = Vec::new();
        for i in 0..(self.input_assignments.len() + self.output_assignments.len()) {
            if i % 2 == 0 {
                // input
                alloc_io.push(z[i / 2].clone());
            } else {
                // output
                alloc_io.push(alloc_out[(i - 1) / 2].clone()); // TODO?
            }
        }

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
            let a_lc = bellpepper_lc::<N, CS>(&alloc_io, &alloc_wits, a, i);
            let b_lc = bellpepper_lc::<N, CS>(&alloc_io, &alloc_wits, b, i);
            let c_lc = bellpepper_lc::<N, CS>(&alloc_io, &alloc_wits, c, i);
            cs.enforce(|| format!("con{}", i), |_| a_lc, |_| b_lc, |_| c_lc);
        }

        Ok(alloc_out)
    }
}

#[cfg(test)]
mod tests {

    use crate::bellpepper::*;
    use ark_ff::{BigInt, One};
    use ark_r1cs_std::eq::EqGadget;
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
    fn circuit_convert() {
        let zi_list = vec![
            vec![AF::one(), AF::one()],
            vec![AF::from(2), AF::from(4)],
            vec![AF::from(4), AF::from(12)],
            vec![AF::from(8), AF::from(32)],
        ];
        run_nova(make_circuit_1, zi_list, 3);
    }

    fn make_circuit_1(z_in: &Vec<AF>) -> FCircuit<<NG as Group>::Scalar> {
        let cs = ConstraintSystem::<AF>::new_ref();

        let two = AF::one() + AF::one();
        let a_val = z_in[0].clone();
        let b_val = z_in[1].clone();

        let (a_in, a_out) =
            FpVar::new_input_output_pair(cs.clone(), || Ok(a_val), || Ok(a_val * two)).unwrap();
        let (b_in, b_out) =
            FpVar::new_input_output_pair(cs.clone(), || Ok(b_val), || Ok((b_val + a_val) * two))
                .unwrap();

        // witness always 2 in this example, but that could vary
        let w = FpVar::new_witness(cs.clone(), || Ok(two)).unwrap();

        // a_in * 2 = a_out
        a_out.enforce_equal(&(a_in.clone() * two));

        // (b_in + a_in) * w = b_out
        b_out.enforce_equal(&((b_in + a_in) * w));

        FCircuit::new(cs)
    }

    fn run_nova(
        make_ark_circuit: fn(&Vec<AF>) -> FCircuit<<NG as Group>::Scalar>,
        zi_list: Vec<Vec<AF>>,
        num_steps: usize,
    ) -> Vec<<NG as Group>::Scalar> {
        let circuit_secondary = TrivialCircuit::default();
        let mut circuit_primary = make_ark_circuit(&zi_list[0]);
        let z0_primary = circuit_primary.get_zi().clone();
        assert_eq!(
            z0_primary,
            zi_list[0]
                .iter()
                .map(|f| ark_to_nova_field::<AF, <NG as Group>::Scalar>(f))
                .collect::<Vec<<NG as Group>::Scalar>>()
        );

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

        for i in 0..num_steps {
            let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
            assert!(res.is_ok());
            res.unwrap();
            circuit_primary = make_ark_circuit(&zi_list[i + 1]);
        }

        // verify the recursive SNARK
        let res =
            recursive_snark.verify(&pp, num_steps, &z0_primary, &[<E2 as Engine>::Scalar::ZERO]);
        assert!(res.is_ok());

        let (zn_primary, zn_secondary) = res.unwrap();
        assert_eq!(
            zn_primary,
            zi_list[num_steps]
                .iter()
                .map(|f| ark_to_nova_field::<AF, <NG as Group>::Scalar>(f))
                .collect::<Vec<<NG as Group>::Scalar>>()
        );

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

        return zn_primary;
    }
}
