use crate::{
    bellpepper::{ark_to_nova_field, nova_to_ark_field},
    utils::{logmn, mle_eval},
};
use ark_ff::PrimeField as arkPrimeField;
use ff::{PrimeField as novaPrimeField, PrimeFieldBits};
use nova_snark::{
    provider::{
        hyrax_pc::HyraxPC,
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
        traits::DlogGroup,
    },
    spartan::polys::multilinear::MultilinearPolynomial,
    traits::{AbsorbInROTrait, Engine, ROTrait},
};
use std::collections::HashMap;

// we have to hardcode these, unfortunately
type E1 = nova_snark::provider::PallasEngine;
type E2 = nova_snark::provider::VestaEngine;
type N1 = <E1 as Engine>::Scalar;
type N2 = <E2 as Engine>::Scalar;

#[derive(Clone, Debug)]
pub struct Table<A: arkPrimeField> {
    pub t: Vec<A>,
    nova_t: Option<MultilinearPolynomial<N1>>,
    pub priv_cmt: Option<A>, // T pub or priv?
    pub proj: Option<Vec<(usize, usize)>>,
    pub tag: usize,
}

// A must be ark_pallas::Fr
impl<A: arkPrimeField> Table<A> {
    pub fn new(mut t: Vec<A>, private: bool, tag: usize) -> Self {
        t.extend(vec![A::zero(); t.len().next_power_of_two() - t.len()]);

        let (nova_t, priv_cmt) = if private {
            // convert to nova Fields
            let nova_table = t.iter().map(|a| ark_to_nova_field::<A, N1>(a)).collect();

            // commit using Hyrax
            let poly = MultilinearPolynomial::new(nova_table);

            let num_vars = poly.get_num_vars();
            let prover_gens: HyraxPC<E1> = HyraxPC::setup(b"poly_test", num_vars);

            let (doc_commit, doc_decommit) = prover_gens.commit(&poly);

            // using the commitment in the hash in circuit
            let mut ro: PoseidonRO<N2, N1> = PoseidonRO::new(
                PoseidonConstantsCircuit::default(),
                doc_commit.comm.len() * 3,
            ); // TODO?
            for c in doc_commit.comm {
                c.absorb_in_ro(&mut ro);
            }
            let doc_commit_for_hash: N1 = ro.squeeze(256);

            let ark_cmt: A = nova_to_ark_field(&doc_commit_for_hash);
            (Some(poly), Some(ark_cmt))
        } else {
            (None, None)
        };

        Table {
            t,
            nova_t,
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
    pub fn new_proj(t: Vec<A>, priv_cmt: bool, ranges: Vec<(usize, usize)>, tag: usize) -> Self {
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

                let mut e = s + chunk_len;
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

        let mut table = Table::new(t, priv_cmt, tag);
        table.proj = projection;
        table
    }

    // for now assume all tables public
    fn calc_sub_v(sub_tables: Vec<&[A]>, q: &[A]) -> A {
        //TODO

        if q.len() == 0 {
            // in this case, passed subtable should be the correct subset already
            assert_eq!(sub_tables.len(), 1);
            let ell = logmn(sub_tables[0].len());
            let real_q = vec![A::zero(); ell];
            mle_eval(sub_tables[0], &real_q)
        } else if sub_tables.len() == 1 && logmn(sub_tables[0].len()) == q.len() {
            mle_eval(sub_tables[0], q)
        } else if sub_tables.len() == 1 && logmn(sub_tables[0].len()) != q.len() {
            panic!("table length and q length mismatch");
        } else {
            let total_subtables_len: usize = sub_tables
                .iter()
                .map(|t| t.len())
                .sum::<usize>()
                .next_power_of_two();
            assert!(total_subtables_len % 2 == 0);
            let half_len = total_subtables_len / 2;

            let mut sub_vec_left = Vec::new();
            let mut sub_len = 0;
            let mut i = 0;
            while sub_len < half_len {
                sub_vec_left.push(sub_tables[i]);
                sub_len += sub_tables[i].len();
                i += 1;
            }
            assert_eq!(sub_len, half_len);
            let mut sub_vec_right = Vec::new();
            sub_len = 0;
            for j in i..sub_tables.len() {
                sub_vec_right.push(sub_tables[j]);
                sub_len += sub_tables[j].len();
            }
            //assert_eq!(sub_len, half_len);

            (A::one() - q[0]) * Self::calc_sub_v(sub_vec_left, &q[1..])
                + q[0] * Self::calc_sub_v(sub_vec_right, &q[1..])
        }
    }

    // ordering info: (table tag, proj)
    pub(crate) fn calc_running_claim(
        ordering_info: Vec<(usize, (usize, usize))>,
        tables: Vec<&Table<A>>,
        running_q: Vec<A>,
    ) -> A {
        println!("ORDERING INFO {:#?}", ordering_info);

        let mut hash_tag_table = HashMap::<usize, &Table<A>>::new();
        for t in tables {
            hash_tag_table.insert(t.tag, t);
        }

        let mut sliced_tables = Vec::new();
        for (tag, proj) in ordering_info {
            let table = hash_tag_table[&tag];

            if table.proj.is_some() {
                assert!(table.proj.as_ref().unwrap().contains(&proj));
            } else {
                assert_eq!(table.t.len(), proj.1 - proj.0);
            }

            sliced_tables.push(&table.t[proj.0..proj.1]);
        }

        Self::calc_sub_v(sliced_tables, &running_q)
    }

    pub fn verify_running_claim(
        ordering_info: Vec<(usize, (usize, usize))>,
        tables: Vec<&Table<A>>,
        q: &Vec<N1>,
        v: &N1,
    ) {
        //assert!(self.priv_cmt.is_none());
        //assert!(self.nova_t.is_none());

        let ark_q: Vec<A> = q.iter().map(|x| nova_to_ark_field::<N1, A>(x)).collect();
        let ark_v: A = nova_to_ark_field::<N1, A>(v);

        assert_eq!(
            ark_v,
            Self::calc_running_claim(ordering_info, tables, ark_q)
        );
    }

    pub fn prove_private_running_claim(&self) {}
}
