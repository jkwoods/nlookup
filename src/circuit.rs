pub struct NlookupCircuit<'a, F, A>
where
    F: PrimeField,
    A: Arity<F>,
{
    constants: &'a PoseidonConstants<F, A>,
    //_w: PhantomData<A>,
}

impl<'a, F, A> NlookupCircuit<'a, F, A>
where
    F: PrimeField,
    A: Arity<F>,
{
    

    fn fiatshamir<'b, CS, A>(
        &self,
        cs: &mut CS,
        tag: &str,
        num_rounds: usize,
        num_cqs: usize,
        alloc_qs: &Vec<Option<AllocatedNum<F>>>,
        alloc_vs: &Vec<Option<AllocatedNum<F>>>,
        alloc_prev_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_rc: &Vec<Option<AllocatedNum<F>>>,
        alloc_claim_r: &Option<AllocatedNum<F>>,
        alloc_gs: &Vec<Vec<Option<AllocatedNum<F>>>>,
        vesta_hash: F,
    ) -> Result<(), SynthesisError>
    where
        A: Arity<F>,
        CS: ConstraintSystem<F>,
    {
        let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);
        let mut sponge_ns = cs.namespace(|| format!("{} sponge", tag));

        let mut pattern = match tag {
            "nl" => {
                vec![
                    SpongeOp::Absorb((self.batch_size + sc_l + 1 + num_cqs) as u32), // vs,
                    // combined_q,
                    // running q,v
                    SpongeOp::Squeeze(1),
                ]
            }
            "nldoc" => {
                vec![
                    SpongeOp::Absorb((self.batch_size + sc_l + 2 + num_cqs) as u32), // vs,
                    SpongeOp::Squeeze(1),
                ]
            }
            "nlhybrid" => {
                vec![
                    SpongeOp::Absorb((self.batch_size * 2 + sc_l + 2 + num_cqs) as u32), // vs,
                    SpongeOp::Squeeze(1),
                ]
            }
            _ => panic!("weird tag"),
        };
        for _i in 0..sc_l {
            // sum check rounds
            pattern.append(&mut vec![SpongeOp::Absorb(3), SpongeOp::Squeeze(1)]);
        }

        sponge.start(IOPattern(pattern), None, &mut sponge_ns);

        // first round claim
        let mut claim = c_1.clone();

for j in 1..=num_rounds {
            // P makes a claim g_j(X_j) about a slice of its large multilinear polynomial
            // g_j is degree 2 in our case

            // V checks g_{j-1}(r_{j-1}) = g_j(0) + g_j(1)
            // Ax^2 + Bx + C -> A + B + C + C

            let g_j = sc_g_{}_xsq + sc_g_{}_x + (sc_g_{}_const * 2);

            let claim_check = term(Op::Eq, vec![claim.clone(), g_j]);

            // "V" chooses rand r_{j} (P chooses this with hash)
            //let r_j = new_var(format!("sc_r_{}", j));

            // update claim for the next round g_j(r_j)
            claim = (((sc_g_{}_xsq * sc_r_{}) + sc_g_{}_x ) * sc_r_{}) + sc_g_{}_const

            if j == num_rounds {
                // output last g_v(r_v) claim

                let last_claim = term(
                    Op::Eq,
                    vec![claim.clone(), new_var(format!("{}_sc_last_claim", id))],
                );
                self.assertions.push(last_claim);
                self.pub_inputs
                    .push(new_var(format!("{}_sc_last_claim", id)));
            }
}

        // (combined_q, vs, running_q, running_v)
        let mut elts = vec![];
        //println!("FIAT SHAMIR ELTS {}", tag);

        // if DOC
        if matches!(tag, "nldoc") || matches!(tag, "nlhybrid") {
            let e = AllocatedNum::alloc(sponge_ns.namespace(|| "doc commit hash start"), || {
                Ok(vesta_hash)
            })?;

            //println!("e: {:#?}", e.clone().get_value());
            elts.push(Elt::Allocated(e));
        }
        for e in alloc_qs {
            elts.push(Elt::Allocated(e.clone().unwrap()));
            //println!("e: {:#?}", e.clone().unwrap().get_value());
        }
        for e in alloc_vs {
            elts.push(Elt::Allocated(e.clone().unwrap()));
            //println!("e: {:#?}", e.clone().unwrap().get_value());
        }
        for e in alloc_prev_rc {
            elts.push(Elt::Allocated(e.clone().unwrap()));
            //println!("e: {:#?}", e.clone().unwrap().get_value());
        }


        for j in 0..sc_l {
            let mut elts = vec![];
            for coeffs in &alloc_gs[j] {
                for e in coeffs {
                    elts.push(Elt::Allocated(e.clone()));
                }
            }

            self.fiatshamir_circuit(
                &elts,
                &mut sponge,
                &mut sponge_ns,
                alloc_rc[j].clone().unwrap(),
                &format!("sc_r_{}", j),
            )?;
        }

        sponge.finish(&mut sponge_ns).unwrap();
        return Ok(());
    }

    fn fiatshamir_circuit<'b, CS>(
        &self,
        query: &[Elt<F>],
        sponge: &mut SpongeCircuit<'b, F, A, CS>,
        sponge_ns: &mut Namespace<'b, F, CS>,
        input_eq: AllocatedNum<F>,
        tag: &str,
    ) -> Result<AllocatedNum<F>, SynthesisError>
    where
        A: Arity<F>,
        CS: ConstraintSystem<F>,
    {
        let new_pos = {
            SpongeAPI::absorb(sponge, query.len() as u32, query, sponge_ns);

            let output = SpongeAPI::squeeze(sponge, 1, sponge_ns);

            Elt::ensure_allocated(
                &output[0],
                &mut sponge_ns.namespace(|| format!("ensure allocated {}", tag)), // name must be the same
                true,
            )?
        };

        Ok(new_pos)
    }
}
