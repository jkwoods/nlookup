use crate::bellpepper::{ark_to_nova_field, nova_to_ark_field};
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

#[derive(Clone, Debug)]
pub struct Table<A: arkPrimeField> {
    pub t: Vec<A>,
    pub priv_cmt: Option<A>, // T pub or priv?
    pub proj: Option<Vec<(usize, usize)>>,
    pub tag: usize,
}

// A must be ark_pallas::Fr
impl<A: arkPrimeField> Table<A> {
    pub fn new(mut t: Vec<A>, private: bool, tag: usize) -> Self {
        // we have to hardcode these, unfortunately
        type E1 = nova_snark::provider::PallasEngine;
        type E2 = nova_snark::provider::VestaEngine;
        type N1 = <E1 as Engine>::Scalar;
        type N2 = <E2 as Engine>::Scalar;

        t.extend(vec![A::zero(); t.len().next_power_of_two() - t.len()]);

        let priv_cmt = if private {
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
            Some(ark_cmt)
        } else {
            None
        };

        Table {
            t,
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
}
