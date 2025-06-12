use ark_ff::{BigInteger, BigInteger256, Field as arkField, PrimeField as arkPrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
};
use ark_relations::gr1cs::{
    ConstraintSystemRef, Namespace, SynthesisError as arkSynthesisError, R1CS_PREDICATE_LABEL,
};
use core::borrow::Borrow;
use ff::{Field as novaField, PrimeField as novaPrimeField};
use halo2curves::serde::Repr;
use itertools::Either;
use nova_snark::frontend::{
    num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError as bpSynthesisError,
};
use nova_snark::traits::circuit::StepCircuit;
use rayon::prelude::*;
use std::sync::Arc;

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

#[inline]
pub fn ark_to_nova_field<
    A: arkPrimeField<BigInt = BigInteger256>,
    N: novaPrimeField<Repr = Repr<32>>,
>(
    ark_ff: &A,
) -> N {
    // ark F -> ark BigInt
    let b = ark_ff.into_bigint();

    // BigInt -> bytes
    let bytes = u64x4_to_u8x32(&b.0);

    // bytes -> nova F
    N::from_repr_vartime(Repr::from(bytes)).unwrap()
}

#[inline]
fn u64x4_to_u8x32(input: &[u64; 4]) -> [u8; 32] {
    let mut output = [0u8; 32];
    for (chunk, &val) in output.chunks_exact_mut(8).zip(input) {
        chunk.copy_from_slice(&val.to_le_bytes());
    }
    output
}

pub fn nova_to_ark_field<N: novaPrimeField<Repr = Repr<32>>, A: arkPrimeField>(nova_ff: &N) -> A {
    // nova F -> bytes
    let b = nova_ff.to_repr();

    // bytes -> ark F
    A::from_le_bytes_mod_order(b.inner())
}

#[inline]
pub fn ark_to_u64<A: arkPrimeField<BigInt = BigInteger256>>(ark_ff: &A) -> u64 {
    // ark F -> ark BigInt
    let b = ark_ff.into_bigint();

    let limbs: [u64; 4] = b.0;

    assert_eq!(limbs[1], 0);
    assert_eq!(limbs[2], 0);
    assert_eq!(limbs[3], 0);

    limbs[0]
}

#[inline]
fn bellpepper_lc<N: novaPrimeField, CS: ConstraintSystem<N>>(
    alloc_io: &[AllocatedNum<N>],
    alloc_wits: &[AllocatedNum<N>],
    lc: &Vec<(N, usize)>,
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

type Constraint<N> = (
    LinearCombination<N>,
    LinearCombination<N>,
    LinearCombination<N>,
);

type LcUsize<N> = Vec<(N, usize)>;

#[derive(Clone, Debug)]
pub struct FCircuit<N: novaPrimeField<Repr = Repr<32>>> {
    pub lcs: Either<Vec<(LcUsize<N>, LcUsize<N>, LcUsize<N>)>, Arc<Vec<Constraint<N>>>>,
    wit_assignments: Vec<N>,
    input_assignments: Vec<N>,
    output_assignments: Vec<N>,
}

impl<N: novaPrimeField<Repr = Repr<32>>> FCircuit<N> {
    // make circuits and witnesses for round i
    // the ark_cs should only have witness and input/output PAIRs
    // (i.e. a user should have never called new_input())
    pub fn new<A: arkPrimeField<BigInt = BigInteger256>>(
        ark_cs_ref: ConstraintSystemRef<A>,
        nova_matrices: Option<Arc<Vec<Constraint<N>>>>,
    ) -> Self {
        ark_cs_ref.finalize();
        /*        if nova_matrices.is_none() {
            assert!(ark_cs_ref.is_satisfied().unwrap());
        }*/

        let ark_cs = ark_cs_ref.borrow().unwrap();

        // io pairs + constant
        let instance_assignment = ark_cs.instance_assignment().unwrap();
        assert_eq!(instance_assignment[0], A::one());
        assert_eq!(instance_assignment.len() % 2, 1);

        let input_assignments = instance_assignment[1..]
            .par_iter()
            .step_by(2)
            .map(ark_to_nova_field)
            .collect();

        let output_assignments = instance_assignment[2..]
            .par_iter()
            .step_by(2)
            .map(ark_to_nova_field)
            .collect();

        let wit_assignments: Vec<N> = ark_cs
            .witness_assignment()
            .unwrap()
            .par_iter()
            .map(ark_to_nova_field)
            .collect();

        let lcs = if let Some(nova_matrices) = nova_matrices {
            Either::Right(nova_matrices)
        } else {
            let ark_matrices = &ark_cs.to_matrices().unwrap()[R1CS_PREDICATE_LABEL];
            let lcs = (0..ark_matrices[0].len())
                .into_par_iter()
                .map(|i| {
                    (
                        ark_matrices[0][i]
                            .iter()
                            .map(|(val, index)| (ark_to_nova_field(val), *index))
                            .collect(),
                        ark_matrices[1][i]
                            .iter()
                            .map(|(val, index)| (ark_to_nova_field(val), *index))
                            .collect(),
                        ark_matrices[2][i]
                            .iter()
                            .map(|(val, index)| (ark_to_nova_field(val), *index))
                            .collect(),
                    )
                })
                .collect();
            Either::Left(lcs)
        };

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

impl<N: novaPrimeField<Repr = Repr<32>>> StepCircuit<N> for FCircuit<N> {
    fn arity(&self) -> usize {
        self.output_assignments.len()
    }

    fn synthesize<CS: ConstraintSystem<N>>(
        &mut self,
        cs: &mut CS,
        z: &[AllocatedNum<N>],
    ) -> Result<Vec<AllocatedNum<N>>, bpSynthesisError> {
        // input already allocated in z
        assert_eq!(z.len(), self.input_assignments.len());

        // alloc outputs
        let alloc_out =
            AllocatedNum::alloc_batch(cs.namespace(|| "out"), || Ok(&self.output_assignments))?;

        // combine io
        let alloc_io = z
            .par_iter()
            .zip(&alloc_out)
            .flat_map(|(zi, oi)| [zi.clone(), oi.clone()])
            .collect::<Vec<_>>();

        // allocate all wits
        let alloc_wits =
            AllocatedNum::alloc_batch(&mut cs.namespace(|| "wit"), || Ok(&self.wit_assignments))?;

        // add constraints

        match &self.lcs {
            Either::Left(lcs) => {
                let saved_lcs = lcs
                    .iter()
                    .enumerate()
                    .map(|(i, (a, b, c))| {
                        let a_lc = bellpepper_lc::<N, CS>(&alloc_io, &alloc_wits, a);
                        let b_lc = bellpepper_lc::<N, CS>(&alloc_io, &alloc_wits, b);
                        let c_lc = bellpepper_lc::<N, CS>(&alloc_io, &alloc_wits, c);
                        if !cs.is_witness_generator() {
                            cs.enforce(
                                || format!("con{i}"),
                                |_| a_lc.clone(),
                                |_| b_lc.clone(),
                                |_| c_lc.clone(),
                            );
                        }
                        (a_lc, b_lc, c_lc)
                    })
                    .collect();
                self.lcs = Either::Right(Arc::new(saved_lcs))
            }
            Either::Right(saved_lcs) => {
                if !cs.is_witness_generator() {
                    saved_lcs
                        .iter()
                        .enumerate()
                        .for_each(|(i, (a_lc, b_lc, c_lc))| {
                            cs.enforce(
                                || format!("con{}", i),
                                |_| a_lc.clone(),
                                |_| b_lc.clone(),
                                |_| c_lc.clone(),
                            );
                        });
                }
            }
        }

        Ok(alloc_out)
    }
}

#[cfg(test)]
mod tests {

    use crate::{bellpepper::*, utils::*};
    use ark_ff::{BigInt, One, Zero};
    use ark_r1cs_std::eq::EqGadget;
    use ark_r1cs_std::GR1CSVar;
    use ark_relations::{
        gr1cs::{ConstraintSystem, OptimizationGoal, Variable},
        lc,
    };
    use ff::PrimeField as novaPrimeField;
    use nova_snark::{
        nova::{CompressedSNARK, PublicParams, RecursiveSNARK},
        traits::{
            circuit::TrivialCircuit, evaluation::EvaluationEngineTrait, snark::default_ck_hint,
            Engine, Group,
        },
    };
    use rand::{rngs::OsRng, RngCore};

    type NG = nova_snark::provider::bn256_grumpkin::bn256::Point;
    type NS = <NG as Group>::Scalar;
    type AF = ark_bn254::Fr;

    type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

    #[test]
    fn ff_convert() {
        for v in vec![0, 1, 13, std::u64::MAX] {
            let ark_val = AF::from(v);
            let nova_val: NS = ark_to_nova_field(&ark_val);
            assert_eq!(nova_val, NS::from(v));
        }

        // modulus
        let mut biggest = AF::MODULUS;
        biggest.sub_with_borrow(&BigInt::from(1u64));
        let ark_biggest: AF = biggest.into();
        let nova_val: NS = ark_to_nova_field(&ark_biggest);
        assert_eq!(nova_val, NS::ZERO - NS::ONE);
    }

    #[test]
    fn ff_reverse_convert() {
        for v in vec![0, 1, 13, std::u64::MAX] {
            let nova_val = NS::from(v);
            let ark_val: AF = nova_to_ark_field(&nova_val);
            assert_eq!(ark_val, AF::from(v));
        }

        // modulus
        let nova_biggest = NS::ZERO - NS::ONE;
        let ark_val: AF = nova_to_ark_field(&nova_biggest);
        assert_eq!(ark_val, AF::zero() - AF::one());
    }

    #[test]
    fn ff_metamorphic() {
        for _ in 0..10 {
            let mut bytes = [0, 32];
            OsRng.fill_bytes(&mut bytes);

            let ark_rand = AF::from_random_bytes(&bytes).unwrap();
            let n: NS = ark_to_nova_field(&ark_rand);
            let a: AF = nova_to_ark_field(&n);
            assert_eq!(ark_rand, a);

            let nova_rand = NS::random(&mut OsRng);
            let a: AF = nova_to_ark_field(&nova_rand);
            let n: NS = ark_to_nova_field(&a);
            assert_eq!(nova_rand, n);
        }
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

    fn make_circuit_1(
        z_in: &Vec<AF>,
        saved_nova_matrices: Option<
            Arc<
                Vec<(
                    LinearCombination<NS>,
                    LinearCombination<NS>,
                    LinearCombination<NS>,
                )>,
            >,
        >,
    ) -> FCircuit<NS> {
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
        a_out.enforce_equal(&(a_in.clone() * two)).unwrap();

        // (b_in + a_in) * w = b_out
        b_out.enforce_equal(&((b_in + a_in) * w)).unwrap();

        FCircuit::new(cs, saved_nova_matrices)
    }

    fn run_nova(
        make_ark_circuit: fn(
            &Vec<AF>,
            Option<
                Arc<
                    Vec<(
                        LinearCombination<NS>,
                        LinearCombination<NS>,
                        LinearCombination<NS>,
                    )>,
                >,
            >,
        ) -> FCircuit<NS>,
        zi_list: Vec<Vec<AF>>,
        num_steps: usize,
    ) -> Vec<NS> {
        let mut circuit_primary = make_ark_circuit(&zi_list[0], None);

        let z0_primary = circuit_primary.get_zi().clone();
        assert_eq!(
            z0_primary,
            zi_list[0]
                .iter()
                .map(|f| ark_to_nova_field::<AF, NS>(f))
                .collect::<Vec<NS>>()
        );

        // produce public parameters
        let pp = PublicParams::<E1, E2, FCircuit<<E1 as Engine>::Scalar>>::setup(
            &mut circuit_primary,
            &*default_ck_hint(),
            &*default_ck_hint(),
            vec![],
        )
        .unwrap();

        // produce a recursive SNARK
        let mut recursive_snark = RecursiveSNARK::<E1, E2, FCircuit<<E1 as Engine>::Scalar>>::new(
            &pp,
            &mut circuit_primary,
            &z0_primary,
            None,
            vec![],
            vec![],
        )
        .unwrap();

        let saved_nova_matrices = circuit_primary.lcs.as_ref().right().unwrap().clone();

        for i in 0..num_steps {
            let res = recursive_snark.prove_step(&pp, &mut circuit_primary, None, vec![], vec![]);
            assert!(res.is_ok());
            res.unwrap();

            circuit_primary = make_ark_circuit(&zi_list[i + 1], Some(saved_nova_matrices.clone()));
        }

        // verify the recursive SNARK
        let res = recursive_snark.verify(&pp, num_steps, &z0_primary);
        assert!(res.is_ok());

        let zn_primary = res.unwrap();
        assert_eq!(
            zn_primary,
            zi_list[num_steps]
                .iter()
                .map(|f| ark_to_nova_field::<AF, NS>(f))
                .collect::<Vec<NS>>()
        );

        // produce the prover and verifier keys for compressed snark
        let (pk, vk) = CompressedSNARK::<_, _, _, S1, S2>::setup(&pp).unwrap();

        // produce a compressed SNARK
        let random_layer = CompressedSNARK::<_, _, _, S1, S2>::sample_random_layer(&pp).unwrap();
        let res =
            CompressedSNARK::<_, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark, random_layer);
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify the compressed SNARK
        let res = compressed_snark.verify(&vk, num_steps, &z0_primary);
        assert!(res.is_ok());

        return zn_primary;
    }
}
