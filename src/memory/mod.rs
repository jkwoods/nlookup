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
