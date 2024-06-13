use ark_crypto_primitives::sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar, boolean::Boolean, eq::EqGadget, fields::fp::FpVar, fields::FieldVar,
    prelude::AllocationMode, R1CSVar,
};
use ark_relations::r1cs::SynthesisError;

pub fn logmn(mn: usize) -> usize {
    match mn {
        1 => 1,
        _ => (mn as f32).log2().ceil() as usize,
    }
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
// https://github.com/ecmargo/coral/blob/af1e35d53effe1060f1488675d55681314e24b1d/src/util.rs#L20
///Uses the `PoseidonDefaultConfig` to compute the Poseidon parameters.
pub(crate) fn construct_poseidon_parameters_internal<F: PrimeField>(
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

// arkworks in devel
// https://github.com/arkworks-rs/r1cs-std/blob/4020fbc22625621baa8125ede87abaeac3c1ca26/src/fields/fp/mod.rs#L58
/// Decomposes fp into a vector of `bits` and a remainder `rest` such that
/// * `bits.len() == size`, and
/// * `rest == 0`.
pub fn to_bits_le_with_top_bits_zero<F: PrimeField>(
    fp: &FpVar<F>,
    size: usize,
) -> Result<(Vec<Boolean<F>>, FpVar<F>), SynthesisError> {
    assert!(size <= F::MODULUS_BIT_SIZE as usize - 1);
    let cs = fp.cs();
    let mode = if fp.is_constant() {
        AllocationMode::Constant
    } else {
        AllocationMode::Witness
    };

    let value = fp.value().map(|f| f.into_bigint());
    let lower_bits = (0..size)
        .map(|i| Boolean::new_variable(cs.clone(), || value.map(|v| v.get_bit(i as usize)), mode))
        .collect::<Result<Vec<_>, _>>()?;
    let lower_bits_fp = Boolean::le_bits_to_fp_var(&lower_bits)?;
    let rest = fp - &lower_bits_fp;
    rest.enforce_equal(&FpVar::<F>::zero())?;
    Ok((lower_bits, rest))
}
