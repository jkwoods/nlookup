use crate::{
    bellpepper::{ark_to_nova_field, nova_to_ark_field},
    utils::{logmn, mle_eval},
};
use ark_ff::PrimeField as arkPrimeField;
use ff::{Field as novaField, PrimeField as novaPrimeField, PrimeFieldBits};
use nova_snark::{
    provider::{
        hyrax_pc::{HyraxPC, PolyCommit, PolyCommitBlinds},
        pedersen::Commitment,
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
        zk_ipa_pc::{InnerProductArgument, InnerProductWitness},
    },
    spartan::polys::multilinear::MultilinearPolynomial,
    traits::{AbsorbInROTrait, Engine, ROTrait, TranscriptEngineTrait},
};
use rand::rngs::OsRng;
use std::collections::HashMap;
use std::ops::{Add, Mul};

// we have to hardcode these, unfortunately
pub(crate) type E1 = nova_snark::provider::PallasEngine;
pub(crate) type E2 = nova_snark::provider::VestaEngine;
pub(crate) type N1 = <E1 as Engine>::Scalar;
pub(crate) type N2 = <E2 as Engine>::Scalar;

#[derive(Clone, Debug)]
pub struct Table<A: arkPrimeField> {
    pub t: Vec<A>,
    nova_t: Option<MultilinearPolynomial<N1>>,
    nova_t_cmt: Option<PolyCommit<E1>>,
    nova_t_decmt: Option<PolyCommitBlinds<E1>>,
    pub priv_cmt: Option<A>, // T pub or priv?
    pub proj: Option<Vec<(usize, usize)>>,
    pub tag: usize,
}

#[derive(Clone, Debug)]
enum TableInfo<'a, A: arkPrimeField> {
    Public(&'a [A]),
    Private(&'a Table<A>, (usize, usize)),
    Filler(usize),
}

#[derive(Clone, Debug)]
pub struct NLProofInfo {
    ipa: InnerProductArgument<E1>,
    proj_q: Vec<N1>,
    v_commit: Commitment<E1>,
}

#[derive(Clone, Debug)]
pub(crate) enum VComp<A: arkPrimeField> {
    ArkScalar(A),
    NovaScalar(N1),
    Cmt(Commitment<E1>),
}

impl<A: arkPrimeField> Add for VComp<A> {
    type Output = VComp<A>;

    fn add(self, other: VComp<A>) -> VComp<A> {
        match (self, other) {
            (VComp::ArkScalar(a), VComp::ArkScalar(b)) => VComp::ArkScalar(a + b),
            (VComp::NovaScalar(a), VComp::NovaScalar(b)) => VComp::NovaScalar(a + b),
            (VComp::Cmt(a), VComp::Cmt(b)) => VComp::Cmt(a + b),
            _ => panic!("type mismatch"),
        }
    }
}

impl<A: arkPrimeField> Mul for VComp<A> {
    type Output = VComp<A>;

    fn mul(self, other: VComp<A>) -> VComp<A> {
        match (self, other) {
            (VComp::ArkScalar(a), VComp::ArkScalar(b)) => VComp::ArkScalar(a * b),
            (VComp::NovaScalar(a), VComp::NovaScalar(b)) => VComp::NovaScalar(a * b),
            (VComp::NovaScalar(a), VComp::Cmt(b)) => VComp::Cmt(b * a),
            (VComp::Cmt(a), VComp::NovaScalar(b)) => VComp::Cmt(a * b),
            _ => panic!("type mismatch"),
        }
    }
}

// A must be ark_pallas::Fr
impl<A: arkPrimeField> Table<A> {
    pub fn new(
        mut t: Vec<A>,
        private: bool,
        tag: usize,
        prover_gens: Option<&HyraxPC<E1>>,
    ) -> Self {
        t.extend(vec![A::zero(); t.len().next_power_of_two() - t.len()]);

        let (nova_t, nova_t_cmt, nova_t_decmt, priv_cmt) = if private {
            assert!(prover_gens.is_some());

            // convert to nova Fields
            let nova_table = t.iter().map(|a| ark_to_nova_field::<A, N1>(a)).collect();

            // commit using Hyrax
            let poly = MultilinearPolynomial::new(nova_table);

            //let num_vars = poly.get_num_vars();
            let gens = prover_gens.unwrap();

            let (doc_commit, doc_decommit) = gens.commit(&poly);

            // using the commitment in the hash in circuit
            let mut ro: PoseidonRO<N2, N1> = PoseidonRO::new(
                PoseidonConstantsCircuit::default(),
                doc_commit.comm.len() * 3,
            ); // TODO?
            for c in &doc_commit.comm {
                c.absorb_in_ro(&mut ro);
            }
            let doc_commit_for_hash: N1 = ro.squeeze(256);

            let ark_cmt: A = nova_to_ark_field(&doc_commit_for_hash);
            (
                Some(poly),
                Some(doc_commit),
                Some(doc_decommit),
                Some(ark_cmt),
            )
        } else {
            (None, None, None, None)
        };

        Table {
            t,
            nova_t,
            nova_t_cmt,
            nova_t_decmt,
            priv_cmt,
            proj: None,
            tag,
        }
    }

    // ranges are (inclusive, exclusive]. i.e. the first half of a table of len 8 is (0,4)
    // automatically will find smallest valid projection given each range
    // you can include as many distinct ranges as you want,
    // func will automatically combine when valid
    // please do not abuse (i.e. a million len 1 ranges), func does not account for human stupidity
    pub fn new_proj(
        t: Vec<A>,
        priv_cmt: bool,
        ranges: Vec<(usize, usize)>,
        tag: usize,
        prover_gens: Option<&HyraxPC<E1>>,
    ) -> Self {
        let mut proj = Vec::new();
        assert!(ranges.len() >= 1);

        for range in ranges {
            // adjust proj
            let real_start = range.0;
            let real_end = range.1;

            println!("real start {:#?}, real end {:#?}", real_start, real_end);

            assert!(real_end <= t.len().next_power_of_two());

            let mut end = t.len().next_power_of_two();
            let mut start = 0;
            let mut chunk_len = end;

            while chunk_len > 1 {
                let mut s = 0;
                while s + chunk_len <= real_start {
                    s += chunk_len;
                }

                let e = s + chunk_len;
                if e >= real_end {
                    start = s;
                    end = e;

                    // try to go smaller
                    if chunk_len > 1 {
                        chunk_len = chunk_len / 2;
                    }
                } else {
                    break;
                }
            }

            println!("found start {:#?}, found end {:#?}", start, end);
            println!("chunk len {:#?}", chunk_len);

            assert!(chunk_len.next_power_of_two() == chunk_len);
            assert!(start <= real_start);
            assert!(end >= real_end);
            assert!(start % chunk_len == 0);

            if chunk_len != t.len().next_power_of_two() {
                proj.push((start, end));
            }
        }

        // elim overlap
        proj.sort_by(|a, b| a.0.cmp(&b.0));

        let mut i = 0;
        while i < (proj.len() - 1) {
            let a = proj[i];
            let b = proj[i + 1];
            if a.0 == b.0 && a.1 <= b.1 {
                // first inside second
                proj.remove(i);
            } else if a.0 <= b.0 && a.1 >= b.1 {
                // second inside first
                proj.remove(i + 1);
            } else {
                i += 1;
            }
        }

        let mut i = 0;
        while i < (proj.len() - 1) {
            let a = proj[i];
            let b = proj[i + 1];
            if a.1 == b.0 && (a.1 - a.0 == b.1 - b.0) && (a.0 % (b.1 - a.0) == 0) {
                // check if can merge
                proj.remove(i + 1);
                proj.remove(i);
                proj.insert(i, (a.0, b.1));
            } else {
                i += 1;
            }
        }

        // confirm seperate
        for i in 0..(proj.len() - 1) {
            let a = proj[i];
            let b = proj[i + 1];
            assert!(a.1 <= b.0);
        }

        let projection = if proj.len() == 0 {
            panic!("Projection calcualtion bad");
        } else if proj.len() == 1 && proj[0].0 == 0 && proj[0].1 == t.len().next_power_of_two() {
            None
        } else {
            Some(proj)
        };

        let mut table = Table::new(t, priv_cmt, tag, prover_gens);
        table.proj = projection;
        table
    }

    // for now assume all tables public
    fn calc_sub_v(
        sub_tables: Vec<TableInfo<A>>,
        q: &[A],
        prover: bool,
        gens: Option<&HyraxPC<E1>>,
        proofs: &mut HashMap<usize, NLProofInfo>,
    ) -> VComp<A> {
        //        println!("sub_tables {:#?}, q {:#?}", sub_tables, q);
        assert!(sub_tables.len() >= 1);

        if sub_tables.len() == 1 {
            match sub_tables[0].clone() {
                TableInfo::Public(t) => {
                    if q.len() == 0 {
                        let ell = logmn(t.len());
                        let real_q = vec![A::zero(); ell];

                        let v = mle_eval(t, &real_q);
                        if prover {
                            VComp::ArkScalar(v)
                        } else {
                            VComp::NovaScalar(ark_to_nova_field::<A, N1>(&v))
                        }
                    } else if logmn(t.len()) == q.len() {
                        let v = mle_eval(t, q);
                        if prover {
                            VComp::ArkScalar(v)
                        } else {
                            VComp::NovaScalar(ark_to_nova_field::<A, N1>(&v))
                        }
                    } else {
                        panic!("table length and q length mismatch");
                    }
                }
                TableInfo::Private(t, (from, to)) => {
                    if q.len() == 0 || (logmn(to - from) == q.len()) {
                        if prover {
                            // prover
                            // proj chunk indx
                            assert_eq!(t.t.len(), t.t.len().next_power_of_two());
                            let chunk_size = to - from;
                            assert_eq!(chunk_size, chunk_size.next_power_of_two());
                            let num_chunks = t.t.len() / chunk_size;
                            let num_q_idxs = logmn(num_chunks);

                            let mut chunk_idx = from / chunk_size;
                            let mut proj_q: Vec<N1> = Vec::new();
                            for _i in 0..num_q_idxs {
                                proj_q.push(N1::from((chunk_idx % 2) as u64));
                                chunk_idx = chunk_idx >> 1;
                            }

                            for qi in q
                                .iter()
                                .rev()
                                .map(|x| ark_to_nova_field::<A, N1>(x))
                                .collect::<Vec<N1>>()
                            {
                                proj_q.push(qi);
                            }
                            assert_eq!(proj_q.len(), logmn(t.t.len()));

                            // let v = mle_eval(&t.t, proj_q);
                            // TODO - rm this sanity check later
                            //assert_eq!(t.nova_t.as_ref().unwrap().evaluate(&proj_q), v);
                            let v = t.nova_t.as_ref().unwrap().evaluate(&proj_q);

                            let proof_info = t.prove_dot_prod(gens.as_ref().unwrap(), proj_q, v);
                            proofs.insert(t.tag, proof_info);

                            VComp::ArkScalar(nova_to_ark_field(&v))
                        } else {
                            // verifier

                            let proof_info = proofs.get(&t.tag).unwrap();

                            t.verify_dot_prod(gens.as_ref().unwrap(), proof_info);

                            VComp::Cmt(proof_info.v_commit)
                        }
                    } else {
                        panic!("table length and q length mismatch");
                    }
                }

                TableInfo::Filler(u) => {
                    // end of table
                    if prover {
                        VComp::ArkScalar(A::zero())
                    } else {
                        VComp::NovaScalar(N1::zero())
                    }
                }
            }
        } else {
            let mut total_subtables_len: usize = 0;
            for e in &sub_tables {
                match e {
                    TableInfo::Public(t) => {
                        total_subtables_len += t.len();
                    }
                    TableInfo::Private(_, (from, to)) => {
                        total_subtables_len += to - from;
                    }
                    TableInfo::Filler(u) => {
                        total_subtables_len += u;
                    }
                }
            }

            let half_len = total_subtables_len / 2;

            let mut sub_vec_left = Vec::new();
            let mut sub_len = 0;
            let mut i = 0;
            let mut right_remaining = 0;
            while sub_len < half_len {
                match sub_tables[i] {
                    TableInfo::Public(t) => {
                        sub_vec_left.push(sub_tables[i].clone());
                        sub_len += t.len();
                    }
                    TableInfo::Private(_, (from, to)) => {
                        sub_vec_left.push(sub_tables[i].clone());
                        sub_len += to - from;
                    }
                    TableInfo::Filler(u) => {
                        let remaining = half_len - sub_len;
                        sub_vec_left.push(TableInfo::Filler(remaining));
                        sub_len = half_len;
                        right_remaining = u - remaining;
                    }
                }
                i += 1;
            }
            assert_eq!(sub_len, half_len);

            let mut sub_vec_right = Vec::new();
            sub_len = 0;

            if right_remaining != 0 {
                assert_eq!(sub_tables.len(), i);
                sub_vec_right.push(TableInfo::Filler(right_remaining));
            } else {
                for j in i..sub_tables.len() {
                    match sub_tables[j] {
                        TableInfo::Public(t) => {
                            sub_vec_right.push(sub_tables[j].clone());
                            sub_len += t.len();
                        }
                        TableInfo::Private(_, (from, to)) => {
                            sub_vec_right.push(sub_tables[j].clone());
                            sub_len += to - from;
                        }
                        TableInfo::Filler(u) => {
                            let remaining = half_len - sub_len;
                            sub_vec_right.push(TableInfo::Filler(remaining));
                            sub_len = half_len;
                        }
                    }
                }
                assert!(sub_len <= half_len);
            }

            match (
                Self::calc_sub_v(sub_vec_left, &q[1..], prover, gens, proofs),
                Self::calc_sub_v(sub_vec_right, &q[1..], prover, gens, proofs),
            ) {
                (VComp::ArkScalar(l), VComp::ArkScalar(r)) => {
                    VComp::ArkScalar((A::one() - q[0]) * l + q[0] * r)
                }
                (VComp::NovaScalar(l), VComp::NovaScalar(r)) => {
                    let q0 = ark_to_nova_field::<A, N1>(&q[0]);
                    VComp::NovaScalar((N1::one() - q0) * l + q0 * r)
                }
                (VComp::Cmt(l), VComp::Cmt(r)) => {
                    let q0 = ark_to_nova_field::<A, N1>(&q[0]);
                    VComp::Cmt(l * (N1::one() - q0) + r * q0)
                }
                _ => panic!("type mismatch during v calc"),
            }
        }
    }

    // ordering info: (table tag, proj)
    pub(crate) fn calc_running_claim(
        ordering_info: &Vec<(usize, (usize, usize))>,
        tables: Vec<&Table<A>>,
        running_q: Vec<A>,
        prover: bool,
        gens: Option<&HyraxPC<E1>>,
        proofs: &mut HashMap<usize, NLProofInfo>,
    ) -> VComp<A> {
        //        println!("ORDERING INFO {:#?}", ordering_info);

        let mut sliced_tables = Vec::new();
        let mut table_len = 0;
        for (tag, proj) in ordering_info {
            let table = tables.iter().find(|&t| t.tag == *tag).unwrap();

            if table.proj.is_some() {
                assert!(table.proj.as_ref().unwrap().contains(&proj));
            } else {
                assert_eq!(table.t.len(), proj.1 - proj.0);
            }

            if table.priv_cmt.is_some() {
                sliced_tables.push(TableInfo::Private(table, *proj));
            } else {
                sliced_tables.push(TableInfo::Public(&table.t[proj.0..proj.1]));
            }
            table_len += proj.1 - proj.0;
        }

        let full_table_len = table_len.next_power_of_two();
        if table_len < full_table_len {
            let filler = full_table_len - table_len;
            sliced_tables.push(TableInfo::Filler(filler));
        }

        Self::calc_sub_v(sliced_tables, &running_q, prover, gens, proofs)
    }

    pub fn verify_dot_prod(&self, verifier_gens: &HyraxPC<E1>, info: &NLProofInfo) {
        assert!(self.priv_cmt.is_some());
        assert!(self.nova_t_cmt.is_some());

        let mut verifier_transcript = <E1 as Engine>::TE::new(b"dot_prod");

        let res = verifier_gens.verify_eval(
            &info.proj_q,
            self.nova_t_cmt.as_ref().unwrap(),
            &info.v_commit,
            &info.ipa,
            &mut verifier_transcript,
        );
        assert!(res.is_ok());
    }

    pub fn prove_dot_prod(
        &self,
        prover_gens: &HyraxPC<E1>,
        proj_q: Vec<N1>,
        eval: N1,
    ) -> NLProofInfo {
        assert!(self.priv_cmt.is_some());
        assert!(self.nova_t.is_some());
        assert!(self.nova_t_cmt.is_some());
        assert!(self.nova_t_decmt.is_some());

        let mut prover_transcript = <E1 as Engine>::TE::new(b"dot_prod");

        let blind = N1::random(&mut OsRng);

        let (ipa_proof, _ipa_witness, v_commit): (
            InnerProductArgument<E1>,
            InnerProductWitness<E1>,
            _,
        ) = prover_gens
            .prove_eval(
                self.nova_t.as_ref().unwrap(),
                self.nova_t_cmt.as_ref().unwrap(),
                self.nova_t_decmt.as_ref().unwrap(),
                &proj_q,
                &eval,
                &blind,
                &mut prover_transcript,
            )
            .unwrap();

        NLProofInfo {
            ipa: ipa_proof,
            proj_q,
            v_commit,
        }
    }
}
