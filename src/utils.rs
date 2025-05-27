use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig};
use ark_ff::{BigInteger256, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar, boolean::Boolean, eq::EqGadget, fields::fp::FpVar, fields::FieldVar,
    prelude::AllocationMode, GR1CSVar,
};
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};
use nova_snark::traits::Engine;

pub trait arkPrimeField = PrimeField<BigInt = BigInteger256>;

// we have to hardcode these, unfortunately
pub(crate) type E1 = nova_snark::provider::Bn256EngineKZG;
pub(crate) type E2 = nova_snark::provider::GrumpkinEngine;
pub(crate) type N1 = <E1 as Engine>::Scalar;
pub(crate) type N2 = <E2 as Engine>::Scalar;

pub fn logmn(mn: usize) -> usize {
    match mn {
        1 => 1,
        _ => (mn as f32).log2().ceil() as usize,
    }
}

// from eli
pub fn chunk_cee<F: arkPrimeField>(
    cond: &Boolean<F>,
    l_vals: &Vec<FpVar<F>>,
    r_vals: &Vec<FpVar<F>>,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    assert_eq!(l_vals.len(), r_vals.len());

    let l_chunks = l_vals.chunks(7).map(|c| c.to_vec()).collect::<Vec<_>>();
    let r_chunks = r_vals.chunks(7).map(|c| c.to_vec()).collect::<Vec<_>>();

    let mut shift_const = F::from(1_u64 << 32);

    for (l_chunk, r_chunk) in l_chunks.iter().zip(r_chunks.iter()) {
        let mut l_pack = l_chunk[0].clone();
        let mut r_pack = r_chunk[0].clone();

        for i in 1..l_chunk.len() {
            let shift = FpVar::new_constant(cs.clone(), shift_const)?;
            l_pack = l_pack + (&l_chunk[i] * shift.clone());
            r_pack = r_pack + (&r_chunk[i] * shift.clone());
            shift_const = shift_const.square();
        }
        l_pack.conditional_enforce_equal(&r_pack, cond)?;
    }

    Ok(())
}

pub fn chunk_ee<F: arkPrimeField>(
    l_vals: &Vec<FpVar<F>>,
    r_vals: &Vec<FpVar<F>>,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    assert_eq!(l_vals.len(), r_vals.len());

    let l_chunks = l_vals.chunks(7).map(|c| c.to_vec()).collect::<Vec<_>>();
    let r_chunks = r_vals.chunks(7).map(|c| c.to_vec()).collect::<Vec<_>>();

    let mut shift_const = F::from(1_u64 << 32);

    for (l_chunk, r_chunk) in l_chunks.iter().zip(r_chunks.iter()) {
        let mut l_pack = l_chunk[0].clone();
        let mut r_pack = r_chunk[0].clone();

        for i in 1..l_chunk.len() {
            let shift = FpVar::new_constant(cs.clone(), shift_const)?;
            l_pack = l_pack + (&l_chunk[i] * shift.clone());
            r_pack = r_pack + (&r_chunk[i] * shift.clone());
            shift_const = shift_const.square();
        }
        l_pack.enforce_equal(&r_pack)?;
    }

    Ok(())
}

pub fn chunk_cee_zero<F: arkPrimeField>(
    cond: &Boolean<F>,
    l_vals: &Vec<FpVar<F>>,
    zero: &FpVar<F>,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    let l_chunks = l_vals.chunks(7).map(|c| c.to_vec()).collect::<Vec<_>>();

    for l_chunk in l_chunks.iter() {
        let mut l_pack = l_chunk[0].clone();

        let mut shift_const = F::from(1_u64 << 32);

        for i in 1..l_chunk.len() {
            let shift = FpVar::new_constant(cs.clone(), shift_const)?;
            l_pack = l_pack + (&l_chunk[i] * shift.clone());
            shift_const = shift_const.square();
        }
        l_pack.conditional_enforce_equal(&zero, cond)?;
    }
    Ok(())
}

pub fn chunk_ee_zero<F: arkPrimeField>(
    l_vals: &Vec<FpVar<F>>,
    zero: &FpVar<F>,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    let l_chunks = l_vals.chunks(7).map(|c| c.to_vec()).collect::<Vec<_>>();

    for l_chunk in l_chunks.iter() {
        let mut l_pack = l_chunk[0].clone();

        let mut shift_const = F::from(1_u64 << 32);

        for i in 1..l_chunk.len() {
            let shift = FpVar::new_constant(cs.clone(), shift_const)?;
            l_pack = l_pack + (&l_chunk[i] * shift.clone());
            shift_const = shift_const.square();
        }
        l_pack.enforce_equal(&zero)?;
    }
    Ok(())
}

pub fn mle_eval<F: PrimeField>(table: &[F], x: &[F]) -> F {
    let chis = evals(x);
    assert_eq!(chis.len(), table.len());

    (0..chis.len())
        .into_iter()
        .map(|i| chis[i] * table[i])
        .reduce(|x, y| x + y)
        .unwrap()
}

fn evals<F: PrimeField>(x: &[F]) -> Vec<F> {
    let ell = x.len();
    let mut evals: Vec<F> = vec![F::zero(); (2_usize).pow(ell as u32)];
    let mut size = 1;
    evals[0] = F::one();

    for r in x.iter().rev() {
        let (evals_left, evals_right) = evals.split_at_mut(size);
        let (evals_right, _) = evals_right.split_at_mut(size);

        evals_left
            .iter_mut()
            .zip(evals_right.iter_mut())
            .for_each(|(x, y)| {
                *y = *x * r;
                *x -= &*y;
            });

        size *= 2;
    }
    evals
}

pub fn horners<F: PrimeField>(coeffs: &Vec<FpVar<F>>, x: &FpVar<F>) -> FpVar<F> {
    let num_c = coeffs.len();

    let mut horners = x * &coeffs[num_c - 1];

    for i in (1..(num_c - 1)).rev() {
        horners = x * (&coeffs[i] + horners);
    }

    // constant
    horners = horners + &coeffs[0];

    horners
}

// from Eli
pub fn custom_ge<F: arkPrimeField>(
    l: &FpVar<F>,
    g: &FpVar<F>,
    max_val: usize,
    cs: ConstraintSystemRef<F>,
) -> Result<Boolean<F>, SynthesisError> {
    let max_val_fpv = FpVar::new_constant(cs.clone(), F::from((max_val + 1) as u64))?;
    let (bits, _) = (g - l + max_val_fpv).to_bits_le_with_top_bits_zero(logmn(max_val) + 1)?;
    Ok(bits.last().unwrap().clone())
}

// from Eli
// https://github.com/ecmargo/coral/blob/af1e35d53effe1060f1488675d55681314e24b1d/src/util.rs#L20
///Uses the `PoseidonDefaultConfig` to compute the Poseidon parameters.
pub fn construct_poseidon_parameters_internal<F: PrimeField>(
    rate: usize,
    full_rounds: u64,
    partial_rounds: u64,
    skip_matrices: u64,
    alpha: u64,
) -> Option<PoseidonConfig<F>> {
    let (ark, mds) =
        find_poseidon_ark_and_mds(255, rate, full_rounds, partial_rounds, skip_matrices as u64);
    Some(PoseidonConfig {
        full_rounds: full_rounds as usize,
        partial_rounds: partial_rounds as usize,
        alpha: alpha,
        ark,
        mds,
        rate: rate,
        capacity: 1,
    })
}
