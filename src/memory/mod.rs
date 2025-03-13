pub mod hash_stack;
pub mod heckaton;
pub mod nebula;

use crate::bellpepper::ark_to_nova_field;
use crate::memory::heckaton::RunningMem;
use crate::utils::*;
use ark_ff::PrimeField as arkPrimeField;
use nova_snark::provider::incremental::Incremental;

// helper function for incremental commitment to RAM
// batch_size == number of memory ops
pub fn incr_commit_to_ram<A: arkPrimeField>(
    ic_scheme: &Incremental<E1, E2>,
    ram: &RunningMem<A>,
    batch_size: usize,
) -> (N2, Vec<N1>, Vec<Vec<N1>>) {
    let (t, a) = ram.get_t_a();
    assert!(t.len() % batch_size == 0); // assumes exact padding
    assert!(batch_size > 0);
    assert!(t.len() > 0);

    let num_rounds = t.len() / batch_size;
    let mut ci: Option<N2> = None;
    let mut blinds = Vec::new();
    let mut ram_hints = Vec::new();
    for i in 0..num_rounds {
        let mut rm = Vec::new();
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

            rm.extend(nova_tm.clone());
            wits.extend(nova_tm);
            rm.extend(nova_ta.clone());
            wits.extend(nova_ta);
        }

        let (hash, blind) = ic_scheme.commit(ci, &wits);
        println!("IC_i {:#?}", hash.clone());
        ci = Some(hash);

        ram_hints.push(rm);
        blinds.push(blind);
    }

    (ci.unwrap(), blinds, ram_hints)
}

mod tests {
    use crate::bellpepper::*;
    use crate::memory::{heckaton::*, *};
    use crate::nlookup::{table::*, *};
    use crate::utils::*;
    use ark_ff::Zero;
    use ark_r1cs_std::{
        alloc::AllocVar, boolean::Boolean, eq::EqGadget, fields::fp::FpVar, R1CSVar,
    };
    use ark_relations::r1cs::{
        ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    };
    use ff::Field as novaField;
    use ff::PrimeField as novaPrimeField;
    use nova_snark::{
        provider::hyrax_pc::HyraxPC,
        traits::{circuit::TrivialCircuit, snark::default_ck_hint, Engine},
        CompressedSNARK, PublicParams, RecursiveSNARK,
    };

    type A = ark_pallas::Fr;

    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

    fn make_full_mem_circ(
        batch_size: usize,
        i: usize,
        rsm: &mut RunningMem<A>,
        prev_stack_ops: Option<Vec<MemElemWires<A>>>,
    ) -> (Option<Vec<MemElemWires<A>>>, FCircuit<N1>) {
        let cs = ConstraintSystem::<A>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        // ram
        let mut running_mem_wires = rsm.begin_new_circuit(cs.clone()).unwrap();
        let running_t_prev = running_mem_wires.running_t.clone();
        let running_a_prev = running_mem_wires.running_a.clone();

        let not_stack = Boolean::new_witness(cs.clone(), || Ok(false)).unwrap();

        let ram = Boolean::new_witness(cs.clone(), || Ok(true)).unwrap();

        let mut next_stack_ops = Vec::new();
        for b in 0..batch_size {
            let res = rsm.next_op(&not_stack, &ram, &mut running_mem_wires);
            assert!(res.is_ok());
            let (t, a) = res.unwrap();
            next_stack_ops.push(t);
            next_stack_ops.push(a);
        }

        if prev_stack_ops.is_some() {
            let new_stack_ops =
                ivcify_stack_op(&prev_stack_ops.unwrap(), &next_stack_ops, cs.clone()).unwrap();
        } else {
            ivcify_stack_op(&next_stack_ops, &next_stack_ops, cs.clone()).unwrap();
        }

        let (running_t_in, running_t_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_t_prev.value().unwrap()),
            || Ok(running_mem_wires.running_t.value().unwrap()),
        )
        .unwrap();
        running_t_in.enforce_equal(&running_t_prev).unwrap();
        running_t_out
            .enforce_equal(&running_mem_wires.running_t)
            .unwrap();

        let (running_a_in, running_a_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_a_prev.value().unwrap()),
            || Ok(running_mem_wires.running_a.value().unwrap()),
        )
        .unwrap();
        running_a_in.enforce_equal(&running_a_prev).unwrap();
        running_a_out
            .enforce_equal(&running_mem_wires.running_a)
            .unwrap();

        // running mem needs to be ivcified too, but that doesn't effect our final checks
        // so we omit for now

        (Some(next_stack_ops), FCircuit::new(cs))
    }

    pub fn ivcify_stack_op<F: arkPrimeField>(
        prev_ops: &Vec<MemElemWires<F>>,
        next_ops: &Vec<MemElemWires<F>>,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(prev_ops.len(), next_ops.len());
        //println!("ivc stack ops");
        for i in 0..prev_ops.len() {
            let (time_in, time_out) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].time.value()?),
                || Ok(next_ops[i].time.value()?),
            )?;
            //        prev_ops[i].time.enforce_equal(&time_in)?;
            next_ops[i].time.enforce_equal(&time_out)?;
            let (addr_in, addr_out) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].addr.value()?),
                || Ok(next_ops[i].addr.value()?),
            )?;
            //    prev_ops[i].addr.enforce_equal(&addr_in)?;
            next_ops[i].addr.enforce_equal(&addr_out)?;

            let (rw_in, rw_out) = Boolean::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].rw.value()?),
                || Ok(next_ops[i].rw.value()?),
            )?;
            //  prev_ops[i].rw.enforce_equal(&rw_in)?;
            next_ops[i].rw.enforce_equal(&rw_out)?;

            for j in 0..prev_ops[i].vals.len() {
                let (val_j_in, val_j_out) = FpVar::new_input_output_pair(
                    cs.clone(),
                    || Ok(prev_ops[i].vals[j].value()?),
                    || Ok(next_ops[i].vals[j].value()?),
                )?;
                //    prev_ops[i].vals[j].enforce_equal(&val_j_in)?;
                next_ops[i].vals[j].enforce_equal(&val_j_out)?;
            }
            let (sr_in, sr_out) = Boolean::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].sr.value()?),
                || Ok(next_ops[i].sr.value()?),
            )?;
            //prev_ops[i].sr.enforce_equal(&sr_in)?;
            next_ops[i].sr.enforce_equal(&sr_out)?;
        }
        Ok(())
    }

    fn run_ram_nl_nova(batch_size: usize, time_list: Vec<MemElem<A>>) {
        let num_steps = ((time_list.len() as f32) / (batch_size as f32)).ceil() as usize;

        // commitments
        let ic_gens = Incremental::<E1, E2>::setup(b"test2", batch_size * 2 * 5);

        let mem_pad = MemElem::<A>::new(0, 0, false, vec![0; time_list[0].vals.len()], false);
        let mut rsm = RunningMem::new(time_list, false, mem_pad.clone());

        let (C_final, blinds, ram_hints) = incr_commit_to_ram(&ic_gens, &rsm, batch_size);
        //println!("ram hints {:#?}", ram_hints.clone());

        // nova
        let circuit_secondary = TrivialCircuit::default();
        let mut circuit_primary;
        let mut running_stack_ops;
        (running_stack_ops, circuit_primary) = make_full_mem_circ(batch_size, 0, &mut rsm, None);

        let z0_primary_full = circuit_primary.get_zi();
        let z0_primary = z0_primary_full[(batch_size * 5 * 2)..].to_vec();
        //println!("Z0 {:#?}", z0_primary.clone());

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
            batch_size * 5 * 2,
            &[&ic_gens.ped_gen],
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
            Some(vec![blinds[0]]),
            ram_hints[0].clone(),
        )
        .unwrap();

        for i in 0..(num_steps) {
            println!("==============================================");
            let res = recursive_snark.prove_step(
                &pp,
                &circuit_primary,
                &circuit_secondary,
                Some(vec![blinds[i]]),
                ram_hints[i].clone(),
            );
            assert!(res.is_ok());
            res.unwrap();

            let zi_primary = circuit_primary.get_zi();
            // verify the recursive SNARK
            let res =
                recursive_snark.verify(&pp, i + 1, &z0_primary, &[<E2 as Engine>::Scalar::ZERO]);
            assert!(res.is_ok());

            if i < num_steps - 1 {
                (running_stack_ops, circuit_primary) =
                    make_full_mem_circ(batch_size, i + 1, &mut rsm, running_stack_ops);
            }
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
        let (zn, _) = res.unwrap();

        // running t == running a (verifier)
        assert_eq!(zn[0], zn[1]);

        // incr cmt = acc cmt (verifier)
        assert_eq!(C_final, compressed_snark.Ci[0]);
    }

    #[test]
    fn mem_basic() {
        let time_list = vec![
            MemElem::<A>::new_single(1, 1, true, 1, false),
            MemElem::<A>::new_single(2, 2, true, 2, false),
            MemElem::<A>::new_single(3, 3, true, 3, false),
            MemElem::<A>::new_single(4, 1, false, 1, false),
        ];

        run_ram_nl_nova(2, time_list);
    }
}
