pub mod hash_stack;
pub mod heckaton;

use crate::bellpepper::ark_to_nova_field;
use crate::memory::heckaton::RunningMem;
use crate::utils::*;
use ark_ff::PrimeField as arkPrimeField;
use nova_snark::provider::incremental::Incremental;

// helper function for incremental commitment to RAM
// batch_size == number of memory ops
pub fn incr_commit_to_ram<A: arkPrimeField>(
    ic_scheme: &Incremental<E1, E2>,
    ram: RunningMem<A>,
    batch_size: usize,
) -> (N2, Vec<N1>) {
    let (t, a) = ram.get_t_a();
    assert!(t.len() % batch_size == 0); // assumes exact padding
    assert!(batch_size > 0);
    assert!(t.len() > 0);

    let num_rounds = t.len() / batch_size;
    let mut ci: Option<N2> = None;
    let mut blinds = Vec::new();
    for i in 0..num_rounds {
        let mut wits: Vec<N1> = Vec::new();
        for (tm, am) in t[(i * batch_size)..(i * batch_size + batch_size)]
            .iter()
            .zip(a[(i * batch_size)..(i * batch_size + batch_size)].iter())
        {
            let nova_tm: Vec<N1> = tm
                .get_vec()
                .iter()
                .map(|a| ark_to_nova_field::<A, N1>(a))
                .collect();
            let nova_ta: Vec<N1> = am
                .get_vec()
                .iter()
                .map(|a| ark_to_nova_field::<A, N1>(a))
                .collect();

            wits.extend(nova_tm);
            wits.extend(nova_ta);
        }

        let (hash, blind) = ic_scheme.commit(ci, &wits);
        ci = Some(hash);

        blinds.push(blind);
    }

    (ci.unwrap(), blinds)
}
/*
mod tests {
    use crate::memory::*;
    use ark_pallas::Fr as A;

    fn make_full_mem_circ() -> FCircuit<N1> {
        let cs = ConstraintSystem::<A>::new_ref();
    }

    fn run_ram_and_nl_with_nova() {
        // commitments

        // nova
        let circuit_secondary = TrivialCircuit::default();
        let mut circuit_primary = make_full_mem_circ();

        let z0_primary = circuit_primary.get_zi().clone();

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
            TODO,
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

            // verify the recursive SNARK
            let res = recursive_snark.verify(
                &pp,
                num_steps,
                &z0_primary,
                &[<E2 as Engine>::Scalar::ZERO],
            );
            assert!(res.is_ok());

            circuit_primary = make_full_mem_circ();
        }

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

        // check final cmt outputs
    }
}*/
