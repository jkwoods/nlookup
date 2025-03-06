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
        lookups: &Vec<(usize, A, usize)>,
        nl: &mut NLookup<A>,
        running_q: Vec<A>,
        running_v: A,
        gens: &HyraxPC<E1>,
        rsm: &mut RunningMem<A>,
        prev_stack_ops: Option<Vec<MemElemWires<A>>>,
    ) -> (Vec<A>, A, Option<Vec<MemElemWires<A>>>, FCircuit<N1>) {
        let cs = ConstraintSystem::<A>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        // nl
        let lu_end = if (i + 1) * batch_size < lookups.len() {
            (i + 1) * batch_size
        } else {
            lookups.len()
        };

        println!("lookups {:#?}", lookups[(i * batch_size)..lu_end].to_vec());

        let res = nl.nlookup_circuit_F(
            cs.clone(),
            &lookups[(i * batch_size)..lu_end].to_vec(),
            running_q,
            running_v,
        );
        assert!(res.is_ok());

        let nl_wires = res.unwrap();
        let next_running_q = nl_wires
            .next_running_q
            .clone()
            .into_iter()
            .map(|x| x.value().unwrap())
            .collect();
        let next_running_v = nl_wires.next_running_v.value().unwrap();

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

        // ivc
        let (nl_running_v_in, nl_running_v_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(nl_wires.prev_running_v.value().unwrap()),
            || Ok(nl_wires.next_running_v.value().unwrap()),
        )
        .unwrap();
        nl_wires
            .next_running_v
            .enforce_equal(&nl_running_v_out)
            .unwrap();
        nl_wires
            .prev_running_v
            .enforce_equal(&nl_running_v_in)
            .unwrap();

        if prev_stack_ops.is_some() {
            let new_stack_ops =
                ivcify_stack_op(&prev_stack_ops.unwrap(), &next_stack_ops, cs.clone()).unwrap();
        } else {
            ivcify_stack_op(&next_stack_ops, &next_stack_ops, cs.clone()).unwrap();
        }

        for i in 0..nl_wires.prev_running_q.len() {
            let (nl_running_q_in, nl_running_q_out) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(nl_wires.prev_running_q[i].value().unwrap()),
                || Ok(nl_wires.next_running_q[i].value().unwrap()),
            )
            .unwrap();
            nl_wires.prev_running_q[i]
                .enforce_equal(&nl_running_q_in)
                .unwrap();
            nl_wires.next_running_q[i]
                .enforce_equal(&nl_running_q_out)
                .unwrap();
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

        (
            next_running_q,
            next_running_v,
            Some(next_stack_ops),
            FCircuit::new(cs),
        )
    }

    pub fn ivcify_stack_op<F: arkPrimeField>(
        prev_ops: &Vec<MemElemWires<F>>,
        next_ops: &Vec<MemElemWires<F>>,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(prev_ops.len(), next_ops.len());
        println!("ivc stack ops");
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

    fn run_ram_nl_nova(
        batch_size: usize,
        qv: Vec<(usize, usize, usize)>,
        tables: Vec<Table<A>>,
        hyrax_gens: HyraxPC<E1>,
        gen_size: usize,
        time_list: Vec<MemElem<A>>,
    ) {
        let num_steps = ((qv.len() as f32) / (batch_size as f32)).ceil() as usize;

        // commitments
        //let hyrax_gens = HyraxPC::setup(b"test", logmn(gen_size));
        let ic_gens = Incremental::setup(b"test2", &hyrax_gens.ck_s, logmn(batch_size * 2 * 5));

        let lookups: Vec<(usize, A, usize)> = qv
            .into_iter()
            .map(|(q, v, t)| (q, A::from(v as u64), t))
            .collect();

        let mut nl = NLookup::new(tables.clone(), batch_size, None);
        let (mut running_q, mut running_v) = nl.first_running_claim();

        let mem_pad = MemElem::<A>::new(0, 0, false, vec![0; time_list[0].vals.len()], false);
        let mut rsm = RunningMem::new(time_list, false, mem_pad.clone());

        let (C_final, blinds, ram_hints) = incr_commit_to_ram(&ic_gens, &rsm, batch_size);
        println!("ram hints {:#?}", ram_hints.clone());

        // nova
        let circuit_secondary = TrivialCircuit::default();
        let mut circuit_primary;
        let mut running_stack_ops;
        (running_q, running_v, running_stack_ops, circuit_primary) = make_full_mem_circ(
            batch_size,
            0,
            &lookups,
            &mut nl,
            running_q,
            running_v,
            &hyrax_gens,
            &mut rsm,
            None,
        );

        let z0_primary = circuit_primary.get_zi().clone();
        println!("Z0 {:#?}", z0_primary.clone());

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
            &[&hyrax_gens.ck_s, &ic_gens.ped_gen],
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
            Some(blinds[0]),
            ram_hints[0].clone(),
        )
        .unwrap();

        for i in 0..(num_steps) {
            println!("==============================================");
            let res = recursive_snark.prove_step(
                &pp,
                &circuit_primary,
                &circuit_secondary,
                Some(blinds[i]),
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
                (running_q, running_v, running_stack_ops, circuit_primary) = make_full_mem_circ(
                    batch_size,
                    i + 1,
                    &lookups,
                    &mut nl,
                    running_q,
                    running_v,
                    &hyrax_gens,
                    &mut rsm,
                    running_stack_ops,
                );
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
        assert_eq!(
            zn[batch_size * 2 * 5 + logmn(gen_size) + 1],
            zn[batch_size * 2 * 5 + logmn(gen_size) + 2]
        );

        // incr cmt = acc cmt (verifier)
        assert_eq!(C_final, compressed_snark.Ci);

        // nlookup prover
        let nova_q =
            zn[(1 + batch_size * 2 * 5)..(1 + batch_size * 2 * 5 + logmn(gen_size))].to_vec();
        let blind_v = recursive_snark.r_W_primary.r_W[0];
        let mut proofs = nl.prove_running_claim(&hyrax_gens, &nova_q, blind_v);

        // nlookup verifier
        let v_cmt = VComp::Cmt(compressed_snark.r_U_primary.comm_W[0]);
        nl.publicize();
        nl.verify_running_claim(&hyrax_gens, &nova_q, &mut proofs, &v_cmt);
    }

    #[test]
    fn mem_basic() {
        let t_pre = vec![2, 3, 5, 7, 9, 13, 17, 19];
        let t: Vec<A> = t_pre.into_iter().map(|x| A::from(x as u64)).collect();

        let gens = HyraxPC::setup(b"test", logmn(8));

        let table = Table::new(t, true, 0, Some(&gens));

        let lookups = vec![(2, 5, 0), (1, 3, 0), (7, 19, 0), (6, 17, 0)];

        let time_list = vec![
            MemElem::<A>::new_single(1, 1, true, 1, false),
            MemElem::<A>::new_single(2, 2, true, 2, false),
            MemElem::<A>::new_single(3, 3, true, 3, false),
            MemElem::<A>::new_single(4, 1, false, 1, false),
        ];

        run_ram_nl_nova(2, lookups, vec![table], gens, 8, time_list);
    }
}
