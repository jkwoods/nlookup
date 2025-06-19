use std::{any::TypeId, ops::DerefMut};

use ark_ff::{BigInteger256, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar, boolean::Boolean, eq::EqGadget, fields::fp::FpVar, fields::FieldVar,
};
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};
use nova_snark::traits::Engine;
use rustc_hash::FxHashMap;

pub trait ArkPrimeField: PrimeField<BigInt = BigInteger256> {}
impl<P: PrimeField<BigInt = BigInteger256>> ArkPrimeField for P {}

// we have to hardcode these, unfortunately
pub(crate) type E1 = nova_snark::provider::Bn256EngineKZG;
pub(crate) type E2 = nova_snark::provider::GrumpkinEngine;
pub(crate) type N1 = <E1 as Engine>::Scalar;
pub(crate) type N2 = <E2 as Engine>::Scalar;

pub fn logmn(mn: usize) -> usize {
    match mn {
        1 | 0 => 1,
        _ => (mn as f32).log2().ceil() as usize,
    }
}

pub fn new_hash_map<K, V>() -> FxHashMap<K, V> {
    FxHashMap::with_hasher(Default::default())
}

type ShiftPowers<F> = Vec<FpVar<F>>;

fn get_shift_powers<F: PrimeField>(cs: &ConstraintSystemRef<F>, bits: usize) -> ShiftPowers<F> {
    let cs = cs.borrow().unwrap();
    let mut map = cs.cache_map.borrow_mut();
    let shift_powers = map
        .entry(TypeId::of::<ShiftPowers<F>>())
        .or_insert_with(|| {
            let mut shift_powers = vec![FpVar::one(); 254u32.div_ceil(bits as u32) as usize];
            let mut power = FpVar::constant(F::from(1u64 << bits));
            for p in &mut shift_powers[1..] {
                *p = power.clone();
                power.square_in_place().unwrap();
            }
            Box::new(shift_powers)
        });
    shift_powers
        .deref_mut()
        .downcast_mut::<ShiftPowers<F>>()
        .expect("Failed to downcast ShiftPowers")
        .clone()
}

// from eli
pub fn chunk_cee<F: ArkPrimeField>(
    cond: &Boolean<F>,
    l_vals: &[FpVar<F>],
    r_vals: &[FpVar<F>],
    bits: usize,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    let shift_powers = get_shift_powers::<F>(&cs, bits);
    assert_eq!(l_vals.len(), r_vals.len());
    for (l_chunk, r_chunk) in l_vals
        .chunks(254u32.div_ceil(bits as u32) as usize)
        .zip(r_vals.chunks(254u32.div_ceil(bits as u32) as usize))
    {
        let shift_powers = &shift_powers[..l_chunk.len()];
        let l_pack = FpVar::inner_product(l_chunk, shift_powers)?;
        let r_pack = FpVar::inner_product(r_chunk, shift_powers)?;
        l_pack.conditional_enforce_equal(&r_pack, cond)?;
    }

    Ok(())
}

pub fn chunk_ee<F: ArkPrimeField>(
    l_vals: &[FpVar<F>],
    r_vals: &[FpVar<F>],
    bits: usize,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    assert_eq!(l_vals.len(), r_vals.len());
    let shift_powers = get_shift_powers::<F>(&cs, bits);
    for (l_chunk, r_chunk) in l_vals
        .chunks(254u32.div_ceil(bits as u32) as usize)
        .zip(r_vals.chunks(254u32.div_ceil(bits as u32) as usize))
    {
        let shift_powers = &shift_powers[..l_chunk.len()];
        let l_pack = FpVar::inner_product(l_chunk, shift_powers)?;
        let r_pack = FpVar::inner_product(r_chunk, shift_powers)?;
        l_pack.enforce_equal(&r_pack)?;
    }
    Ok(())
}

pub fn chunk_cee_zero<F: ArkPrimeField>(
    cond: &Boolean<F>,
    l_vals: &[FpVar<F>],
    bits: usize,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    let shift_powers = get_shift_powers::<F>(&cs, bits);
    for l_chunk in l_vals.chunks(254u32.div_ceil(bits as u32) as usize) {
        let shift_powers = &shift_powers[..l_chunk.len()];
        let l_pack = FpVar::inner_product(l_chunk, shift_powers)?;
        l_pack.conditional_enforce_equal(&FpVar::zero(), cond)?;
    }
    Ok(())
}

pub fn chunk_ee_zero<F: ArkPrimeField>(
    l_vals: &[FpVar<F>],
    bits: usize,
    cs: ConstraintSystemRef<F>,
) -> Result<(), SynthesisError> {
    let shift_powers = get_shift_powers::<F>(&cs, bits);
    for l_chunk in l_vals.chunks(254u32.div_ceil(bits as u32) as usize) {
        let shift_powers = &shift_powers[..l_chunk.len()];
        let l_pack = FpVar::inner_product(l_chunk, shift_powers)?;
        l_pack.enforce_equal(&FpVar::zero())?;
    }
    Ok(())
}

pub fn mle_eval<F: PrimeField>(table: &[F], x: &[F]) -> F {
    let chis = evals(x);
    assert_eq!(chis.len(), table.len());

    (0..chis.len())
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

pub fn horners<F: PrimeField>(coeffs: &[FpVar<F>], x: &FpVar<F>) -> FpVar<F> {
    let num_c = coeffs.len();

    let mut horners = x * &coeffs[num_c - 1];

    for i in (1..(num_c - 1)).rev() {
        horners = x * (&coeffs[i] + horners);
    }

    // constant
    horners += &coeffs[0];

    horners
}

// from Eli
pub fn custom_ge<F: ArkPrimeField>(
    l: &FpVar<F>,
    g: &FpVar<F>,
    max_bits: usize,
    cs: ConstraintSystemRef<F>,
) -> Result<Boolean<F>, SynthesisError> {
    let max_val_fpv = FpVar::new_constant(cs.clone(), F::from((1u64 << max_bits) + 1))?;
    let (bits, _) = (g - l + max_val_fpv).to_bits_le_with_top_bits_zero(max_bits + 1)?;
    Ok(bits.last().unwrap().clone())
}
