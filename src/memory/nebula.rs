// TODOs
// priv fs
// interface for final verifier checks
// get rid of padding in typical mem

use crate::bellpepper::{ark_to_nova_field, nova_to_ark_field, AllocIoVar};
use crate::utils::*;
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    GR1CSVar,
};
use ark_relations::gr1cs::{ConstraintSystemRef, SynthesisError};
use itertools::multiunzip;
use nova_snark::{
    gadgets::utils::scalar_as_base,
    provider::{hyperkzg::Commitment, incremental::Incremental},
    traits::{Engine, ROConstants, ROTrait},
};
use rayon::prelude::*;
use rustc_hash::FxHashMap as HashMap;
use std::{cmp::max, path::Path};

#[derive(Clone, Debug, PartialEq)]
struct StackElem<F: ArkPrimeField> {
    vals: Vec<F>,
}

impl<F: ArkPrimeField> StackElem<F> {
    fn new(v: Vec<F>) -> Self {
        StackElem { vals: v }
    }

    fn padding(elem_len: usize) -> Self {
        StackElem {
            vals: vec![F::zero(); elem_len],
        }
    }

    fn get_vec(&self) -> Vec<F> {
        self.vals.clone()
    }
}

#[derive(Clone, Debug)]
struct HeapElem<F: ArkPrimeField> {
    time: F,
    addr: F,
    vals: Vec<F>,
    sr: F,
}

impl<F: ArkPrimeField> HeapElem<F> {
    fn new_u(t: usize, a: usize, v: Vec<usize>, sr: usize) -> Self {
        HeapElem {
            time: F::from(t as u64),
            addr: F::from(a as u64),
            vals: v.into_iter().map(|x| F::from(x as u64)).collect(),
            sr: F::from(sr as u64),
        }
    }

    fn new_f(t: F, a: F, v: Vec<F>, sr: F) -> Self {
        HeapElem {
            time: t,
            addr: a,
            vals: v,
            sr,
        }
    }

    fn padding(elem_len: usize, addr: usize) -> Self {
        HeapElem {
            time: F::zero(),
            addr: F::from(addr as u64),
            vals: vec![F::zero(); elem_len],
            sr: F::zero(),
        }
    }

    fn get_vec(&self) -> Vec<F> {
        let mut v = vec![self.time, self.addr, self.sr];
        v.extend(self.vals.clone());

        v
    }
    fn hash(&self, perm_chal: &[F]) -> F {
        let mut hash = self.sr + F::from(1_u64 << 2) * self.time + F::from(1_u64 << 34) * self.addr;

        for i in 0..self.vals.len() {
            hash += perm_chal[i + 1] * self.vals[i];
        }

        perm_chal[0] - hash
    }
}

#[derive(Clone, Debug)]
pub struct StackElemWires<F: ArkPrimeField> {
    pub vals: Vec<FpVar<F>>,
}

impl<F: ArkPrimeField> StackElemWires<F> {
    pub fn print_vals(&self) {
        println!(
            "StackElem [[vals {:#?}]]",
            self.vals
                .iter()
                .map(|v| v.value().unwrap())
                .collect::<Vec<F>>()
        );
    }

    pub fn new(v: Vec<FpVar<F>>) -> Self {
        StackElemWires { vals: v }
    }

    fn hash(&self, perm_chal: &FpVar<F>, prev: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
        let mut hash = perm_chal - prev;

        for i in 0..self.vals.len() {
            hash *= perm_chal - &self.vals[i];
        }

        Ok(hash)
    }

    fn ivcify(&self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        for v in &self.vals {
            let (_, val_out) =
                FpVar::new_input_output_pair(cs.clone(), || Ok(F::ZERO), || v.value())?;
            v.enforce_equal(&val_out)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct HeapElemWires<F: ArkPrimeField> {
    pub time: FpVar<F>,
    pub addr: FpVar<F>,
    pub vals: Vec<FpVar<F>>,
    pub sr: FpVar<F>,
}

impl<F: ArkPrimeField> HeapElemWires<F> {
    pub fn print_vals(&self) {
        println!(
            "HeapElem [{:#?} [time {:#?}] [addr {:#?}] [vals {:#?}]]",
            self.sr.value().unwrap(), //self.mem_spaces[ark_to_u64(&self.sr.value().unwrap())]
            self.time.value().unwrap(),
            self.addr.value().unwrap(),
            self.vals
                .iter()
                .map(|v| v.value().unwrap())
                .collect::<Vec<F>>()
        );
    }

    pub fn new(t: FpVar<F>, a: FpVar<F>, v: Vec<FpVar<F>>, sr: FpVar<F>) -> Self {
        HeapElemWires {
            time: t,
            addr: a,
            vals: v,
            sr,
        }
    }

    fn hash(&self, perm_chal: &[FpVar<F>]) -> Result<FpVar<F>, SynthesisError> {
        let mut hash = &self.sr
            + FpVar::constant(F::from(1_u64 << 2)) * &self.time
            + FpVar::constant(F::from(1_u64 << 34)) * &self.addr;

        for i in 0..self.vals.len() {
            hash += &perm_chal[i + 1] * &self.vals[i];
        }

        Ok(&perm_chal[0] - hash)
    }

    fn ivcify(&self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let (_, time_out) =
            FpVar::new_input_output_pair(cs.clone(), || Ok(F::ZERO), || self.time.value())?;
        self.time.enforce_equal(&time_out)?;

        let (_, addr_out) =
            FpVar::new_input_output_pair(cs.clone(), || Ok(F::ZERO), || self.addr.value())?;
        self.addr.enforce_equal(&addr_out)?;

        let (_, sr_out) =
            FpVar::new_input_output_pair(cs.clone(), || Ok(F::ZERO), || self.sr.value())?;
        self.sr.enforce_equal(&sr_out)?;

        for v in &self.vals {
            let (_, val_out) =
                FpVar::new_input_output_pair(cs.clone(), || Ok(F::ZERO), || v.value())?;
            v.enforce_equal(&val_out)?;
        }
        Ok(())
    }
}

#[derive(Clone, Eq, Debug, PartialEq, PartialOrd, Ord)]
pub enum MemType {
    PrivROM(usize),
    PrivRAM(usize),
    PubROM(usize),
    PubRAM(usize), // TODO switch
}

// builds the witness for RunningMem
#[derive(Debug)]
pub struct MemBuilder<F: ArkPrimeField> {
    // bookeeping
    mem: HashMap<usize, HeapElem<F>>,
    stacks: Vec<Vec<StackElem<F>>>, // (preimage, elts)
    // nebula traces
    pub_is: Vec<HeapElem<F>>,
    priv_is: Vec<HeapElem<F>>,
    rs: Vec<HeapElem<F>>,
    ws: Vec<HeapElem<F>>,
    pub_fs: HashMap<usize, HeapElem<F>>,
    priv_fs: HashMap<usize, HeapElem<F>>,
    // stack trace
    ss: Vec<StackElem<F>>,
    // params
    mem_spaces: Vec<MemType>, // only mem here, stack is 0
    pub elem_len: usize,
    pub stack_elem_lens: Vec<usize>,
    ts: usize,
    max_addr: usize,
}

impl<F: ArkPrimeField> MemBuilder<F> {
    pub fn new(elem_len: usize, stack_elem_lens: Vec<usize>, mut mem_spaces: Vec<MemType>) -> Self {
        assert!(elem_len > 0);

        mem_spaces.sort();
        mem_spaces.dedup();

        Self {
            mem: new_hash_map(),
            stacks: vec![vec![]; stack_elem_lens.len()],
            pub_is: Vec::new(),
            priv_is: Vec::new(),
            rs: Vec::new(),
            ws: Vec::new(),
            pub_fs: new_hash_map(),
            priv_fs: new_hash_map(),
            ss: Vec::new(),
            mem_spaces,
            stack_elem_lens,
            elem_len,
            ts: 0,
            max_addr: 0,
        }
    }

    fn padding(&self, addr: usize) -> HeapElem<F> {
        HeapElem::padding(self.elem_len, addr)
    }

    pub fn push(&mut self, stack_tag: usize, vals: Vec<F>) {
        self.cond_push(true, stack_tag, vals)
    }

    pub fn cond_push(&mut self, cond: bool, stack_tag: usize, vals: Vec<F>) {
        assert!(stack_tag < self.stacks.len());
        assert_eq!(vals.len(), self.stack_elem_lens[stack_tag]);

        if cond {
            let se = StackElem::new(vals);
            self.stacks[stack_tag].push(se.clone());
            self.ss.push(se);
        } else {
            self.ss
                .push(StackElem::padding(self.stack_elem_lens[stack_tag]));
        }
    }

    pub fn pop(&mut self, stack_tag: usize) -> Vec<F> {
        self.cond_pop(true, stack_tag)
    }

    pub fn cond_pop(&mut self, cond: bool, stack_tag: usize) -> Vec<F> {
        assert!(stack_tag < self.stacks.len());

        if cond {
            let se = self.stacks[stack_tag].pop().unwrap();
            self.ss.push(se.clone());
            se.vals
        } else {
            self.ss
                .push(StackElem::padding(self.stack_elem_lens[stack_tag]));
            vec![F::ZERO; self.stack_elem_lens[stack_tag]]
        }
    }

    pub fn read(&mut self, addr: usize, ty: MemType) -> Vec<F> {
        self.cond_read(true, addr, ty)
    }

    pub fn cond_read(&mut self, cond: bool, addr: usize, ty: MemType) -> Vec<F> {
        let read_elem = if !cond {
            self.padding(addr)
        } else if self.mem.contains_key(&addr) {
            let re = self.mem.get(&addr).unwrap().clone();
            assert_eq!(re.addr, F::from(addr as u64));
            re
        } else {
            panic!("Uninitialized memory addr")
        };
        self.rs.push(read_elem.clone());

        if cond {
            self.ts += 1;
            //assert!((self.ts as u64) < (1_u64 << 32));
        }

        let write_elem = if !cond {
            self.padding(addr)
        } else {
            let mem_tag = self.mem_spaces.iter().position(|r| *r == ty).unwrap();

            let we = HeapElem::new_f(
                F::from(self.ts as u64),
                F::from(addr as u64),
                read_elem.vals.clone(),
                F::from(mem_tag as u64),
            );

            self.mem.insert(addr, we.clone());
            we
        };

        self.ws.push(write_elem.clone());

        if cond {
            match ty {
                MemType::PubROM(_) | MemType::PubRAM(_) => {
                    self.pub_fs.insert(addr, write_elem);
                }
                MemType::PrivROM(_) | MemType::PrivRAM(_) => {
                    self.priv_fs.insert(addr, write_elem);
                }
            }
        }

        read_elem.vals
    }

    // initialize memory
    // note: if you plan on writing to an addr, it must be initialized
    pub fn init(&mut self, addr: usize, vals: Vec<F>, mem_tag: MemType) {
        assert_ne!(addr, 0);

        self.max_addr = max(self.max_addr, addr);

        self.inner_init(addr, vals, mem_tag);
    }

    fn inner_init(&mut self, addr: usize, vals: Vec<F>, mem_tag: MemType) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert!(!self.mem.contains_key(&addr));
        //assert!((addr as u64) < (1_u64 << 32));

        let sr = self.mem_spaces.iter().position(|r| *r == mem_tag).unwrap();

        let elem = HeapElem::new_f(F::ZERO, F::from(addr as u64), vals, F::from(sr as u64));
        self.mem.insert(addr, elem.clone());

        match mem_tag {
            MemType::PrivRAM(_) | MemType::PrivROM(_) => {
                self.priv_is.push(elem.clone());
                self.priv_fs.insert(addr, elem.clone());
            }
            MemType::PubRAM(_) | MemType::PubROM(_) => {
                self.pub_is.push(elem.clone());
                self.pub_fs.insert(addr, elem.clone());
            }
        }
    }

    pub fn cond_write(&mut self, cond: bool, addr: usize, vals: Vec<F>, ty: MemType) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        let mem_tag = match ty {
            MemType::PrivROM(_) | MemType::PubROM(_) => panic!("cannot write to ROM"),
            ref m => self.mem_spaces.iter().position(|r| *r == *m).unwrap(),
        };

        let read_elem = if !cond {
            &self.padding(addr)
        } else if self.mem.contains_key(&addr) {
            let re = self.mem.get(&addr).unwrap();
            assert_eq!(re.addr, F::from(addr as u64));
            re
        } else {
            panic!("Uninitialized memory addr")
        };

        self.rs.push(read_elem.clone());
        if cond {
            self.ts += 1;
            //assert!((self.ts as u64) < (1_u64 << 32));
        }

        let write_elem = if !cond {
            self.padding(addr)
        } else {
            let we = HeapElem::new_f(
                F::from(self.ts as u64),
                read_elem.addr,
                vals,
                F::from(mem_tag as u64),
            );

            self.mem.insert(addr, we.clone());

            we
        };

        self.ws.push(write_elem.clone());

        if cond {
            match ty {
                MemType::PrivRAM(_) | MemType::PrivROM(_) => {
                    self.priv_fs.insert(addr, write_elem);
                }
                MemType::PubRAM(_) | MemType::PubROM(_) => {
                    self.pub_fs.insert(addr, write_elem);
                }
            }
        }
    }

    pub fn write(&mut self, addr: usize, vals: Vec<F>, ty: MemType) {
        self.cond_write(true, addr, vals, ty)
    }

    fn ic_to_ram(
        &self,
        ic_gen: &Incremental<E1, E2>,
        rw_batch_size: usize,
        scan_priv_batch_size: usize,
        scan_pub_batch_size: usize,
        stk_batch_size: usize,
        num_iters: usize,
        sep_final: bool, // true -> cmts/ivcify =  [is, rs, ws, stk], [fs]
        // false -> cmts/ivcify = [is, rs, ws, stk, fs]
        priv_fs: &[HeapElem<F>],
        pub_fs: &[HeapElem<F>],
        padding: &HeapElem<F>,
    ) -> (Vec<N2>, Vec<Vec<N1>>, Vec<Vec<N1>>) {
        let num_cmts = if sep_final { 3 } else { 1 };

        let mut ci: Vec<Option<N2>> = vec![None; num_cmts];
        // let mut inner_commits: Vec<Vec<Option<Commitment<E1>>>> =
        //    vec![vec![None; num_iters]; num_cmts];
        //let mut blinds: Vec<Vec<N1>> = vec![vec![N1::zero(); num_cmts]; num_iters];
        //let mut ram_hints = vec![Vec::new(); num_iters];

        let zipped: Vec<(Vec<Commitment<E1>>, Vec<N1>, Vec<N1>)> = (0..num_iters)
            .into_par_iter()
            .map(|i| {
                let mut is_hint = Vec::new();
                let mut rs_ws_hint = Vec::new();
                let mut ss_hint = Vec::new();
                let mut fs_hint = Vec::new();

                let is_slice = if (i * scan_priv_batch_size + scan_priv_batch_size)
                    <= self.priv_is.len()
                {
                    self.priv_is[(i * scan_priv_batch_size)
                        ..(i * scan_priv_batch_size + scan_priv_batch_size)]
                        .to_vec()
                } else if (i * scan_priv_batch_size) <= self.priv_is.len() {
                    let mut is_slice = self.priv_is[(i * scan_priv_batch_size)..].to_vec();
                    is_slice.extend(vec![padding.clone(); scan_priv_batch_size - is_slice.len()]);

                    is_slice
                } else {
                    vec![padding.clone(); scan_priv_batch_size]
                };
                for im in is_slice {
                    let nova_im: Vec<N1> = im
                        .get_vec()
                        .iter()
                        .map(|a| ark_to_nova_field::<F, N1>(a))
                        .collect();
                    is_hint.extend(nova_im);
                }

                for (scan_batch_size, fs_vec) in [
                    (scan_priv_batch_size, priv_fs),
                    (scan_pub_batch_size, pub_fs),
                ] {
                    let fs_slice = if (i * scan_batch_size + scan_batch_size) <= fs_vec.len() {
                        fs_vec[(i * scan_batch_size)..(i * scan_batch_size + scan_batch_size)]
                            .to_vec()
                    } else if (i * scan_batch_size) <= fs_vec.len() {
                        let mut fs_slice = fs_vec[(i * scan_batch_size)..].to_vec();
                        fs_slice.extend(vec![padding.clone(); scan_batch_size - fs_slice.len()]);

                        fs_slice
                    } else {
                        vec![padding.clone(); scan_batch_size]
                    };

                    for fm in fs_slice.iter() {
                        let nova_fm: Vec<N1> = fm
                            .get_vec()
                            .iter()
                            .map(|a| ark_to_nova_field::<F, N1>(a))
                            .collect();

                        fs_hint.extend(nova_fm);
                    }
                }

                for (rm, wm) in self.rs[(i * rw_batch_size)..(i * rw_batch_size + rw_batch_size)]
                    .iter()
                    .zip(self.ws[(i * rw_batch_size)..(i * rw_batch_size + rw_batch_size)].iter())
                {
                    let nova_rm: Vec<N1> = rm
                        .get_vec()
                        .iter()
                        .map(|a| ark_to_nova_field::<F, N1>(a))
                        .collect();
                    let nova_wm: Vec<N1> = wm
                        .get_vec()
                        .iter()
                        .map(|a| ark_to_nova_field::<F, N1>(a))
                        .collect();

                    rs_ws_hint.extend(nova_rm);
                    rs_ws_hint.extend(nova_wm);
                }

                for sm in
                    self.ss[(i * stk_batch_size)..(i * stk_batch_size + stk_batch_size)].iter()
                {
                    let nova_sm: Vec<N1> = sm
                        .get_vec()
                        .iter()
                        .map(|a| ark_to_nova_field::<F, N1>(a))
                        .collect();

                    ss_hint.extend(nova_sm);
                }
                let ssb = ss_hint.len();
                /* let isb = is_hint.len();
                                let rwb = rs_ws_hint.len();
                                let fsb = fs_hint.len();
                */

                let isb = scan_priv_batch_size * (3 + self.elem_len);
                let fsb = (scan_pub_batch_size + scan_priv_batch_size) * (3 + self.elem_len);
                let rwb = rw_batch_size * (3 + self.elem_len);

                let mut ordered_hints: Vec<_> = is_hint;
                ordered_hints.extend(rs_ws_hint);
                ordered_hints.extend(ss_hint);
                ordered_hints.extend(fs_hint);

                let hint_ranges = if sep_final {
                    vec![
                        0..(isb + rwb * 2),
                        (isb + rwb * 2)..(isb + fsb + rwb * 2 + ssb),
                    ]
                } else {
                    vec![0..(isb + fsb + rwb * 2 + ssb)]
                };
                //println!("HINT RANGES {:#?}", hint_ranges);

                let mut cmt_wits = vec![Vec::new(); num_cmts];

                for k in 0..num_cmts {
                    for (j, range) in hint_ranges.iter().enumerate() {
                        if j == k {
                            cmt_wits[k].extend(&ordered_hints[range.clone()]);
                        } else {
                            cmt_wits[k].extend(vec![N1::zero(); range.len()]);
                        }
                    }
                }

                let mut blinds_i = Vec::new();
                let mut inner_commits_i = Vec::new();
                for j in 0..num_cmts {
                    let (inner, blind) = ic_gen.inner_commit(&cmt_wits[j]);

                    //inner_commits[i][j] = Some(inner);
                    inner_commits_i.push(inner);
                    //blinds[i][j] = blind;
                    blinds_i.push(blind);
                }

                //ram_hints[i] = ordered_hints;
                (inner_commits_i, blinds_i, ordered_hints)
            })
            .collect();

        let (inner_commits, blinds, ram_hints): (
            Vec<Vec<Commitment<E1>>>,
            Vec<Vec<N1>>,
            Vec<Vec<N1>>,
        ) = multiunzip(zipped);

        // let mut inner_commits: Vec<Vec<Option<Commitment<E1>>>> =
        //    vec![vec![None; num_iters]; num_cmts];
        //let mut blinds: Vec<Vec<N1>> = vec![vec![N1::zero(); num_cmts]; num_iters];
        //let mut ram_hints = vec![Vec::new(); num_iters];

        for i in 0..num_iters {
            for j in 0..num_cmts {
                //println!("cmt wits {:#?}", cmt_wits[j]);
                let hash = ic_gen.hash(ci[j], &inner_commits[i][j]);
                ci[j] = Some(hash);
            }
        }

        let final_cmts = ci.iter().map(|c| c.unwrap()).collect();

        (final_cmts, blinds, ram_hints)
    }

    // consumes the mem builder object
    pub fn new_running_mem<P: AsRef<Path>>(
        mut self,
        rw_batch_size: usize,
        stk_batch_sizes: Vec<usize>,
        sep_final: bool, // true -> cmts/ivcify =  [is], [rs, ws], [fs]
        // false -> cmts/ivcify = [is, rs, ws, fs]
        path: P,
    ) -> (Vec<N2>, Vec<Vec<N1>>, Vec<Vec<N1>>, RunningMem<F>) {
        let total_stk_batch_sizes = stk_batch_sizes.iter().sum::<usize>();
        assert_eq!(self.rs.len(), self.ws.len());
        assert!(
            (!self.rs.is_empty() && !self.ws.is_empty() && rw_batch_size > 0)
                || (!self.ss.is_empty() && total_stk_batch_sizes > 0)
        );
        assert_eq!(
            (self.rs.len() + self.ss.len()) % (rw_batch_size + total_stk_batch_sizes),
            0
        ); // assumes exact padding
        let num_iters = (self.rs.len() + self.ss.len()) / (rw_batch_size + total_stk_batch_sizes);

        let padding = HeapElem::new_u(0, 0, vec![0; self.elem_len], 0);

        // by address
        let mut priv_fs: Vec<HeapElem<F>> = self.priv_fs.clone().into_values().collect();
        let mut pub_fs: Vec<HeapElem<F>> = self.pub_fs.clone().into_values().collect();
        self.priv_is
            .sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());
        //vec_fs.sort_by(|a, b| a.sr.partial_cmp(&b.sr).unwrap());

        priv_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());
        pub_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        let first_pub_addr = if !pub_fs.is_empty() {
            pub_fs[0].addr
        } else {
            F::ZERO
        };
        let first_priv_addr = if !priv_fs.is_empty() {
            priv_fs[0].addr
        } else {
            F::ZERO
        };

        println!("priv FS {:#?} pub FS {:#?}", priv_fs, pub_fs);

        assert_eq!(priv_fs.len(), self.priv_is.len());
        assert_eq!(pub_fs.len(), self.pub_is.len());

        let mut mem_wits = new_hash_map();
        for elem in &self.pub_is {
            mem_wits.insert(elem.addr, elem.clone());
        }
        for elem in &self.priv_is {
            mem_wits.insert(elem.addr, elem.clone());
        }

        let scan_priv_per_batch = if !self.priv_is.is_empty() && !priv_fs.is_empty() {
            ((self.priv_is.len() as f32) / (num_iters as f32)).ceil() as usize
        } else {
            0
        };

        let scan_pub_per_batch = if !self.pub_is.is_empty() && !pub_fs.is_empty() {
            ((self.pub_is.len() as f32) / (num_iters as f32)).ceil() as usize
        } else {
            0
        };

        let sr_bit_limit = logmn(self.mem_spaces.len());
        let time_bit_limit = logmn(self.ts);
        assert!(time_bit_limit <= 32);
        let addr_bit_limit = logmn(self.max_addr);
        assert!(addr_bit_limit <= 254 - 34);

        // cmt
        let mut key_len = (scan_priv_per_batch * 2 + scan_pub_per_batch) * (3 + self.elem_len)
            + rw_batch_size * 2 * (3 + self.elem_len);
        assert_eq!(stk_batch_sizes.len(), self.stack_elem_lens.len());
        for (b, l) in stk_batch_sizes.iter().zip(self.stack_elem_lens.iter()) {
            key_len += b * l;
        }

        let ic_gens = Incremental::<E1, E2>::setup(key_len, path);

        let (ic_cmt, blinds, ram_hints) = self.ic_to_ram(
            &ic_gens,
            rw_batch_size,
            scan_priv_per_batch,
            scan_pub_per_batch,
            total_stk_batch_sizes,
            num_iters,
            sep_final,
            &priv_fs,
            &pub_fs,
            &padding,
        );
        println!("RAM HINTS {:#?}", ram_hints);

        let nova_perm_chal = sample_challenges(&ic_cmt);
        let mut perm_chal = vec![
            nova_to_ark_field::<N1, F>(&nova_perm_chal[0]),
            nova_to_ark_field::<N1, F>(&nova_perm_chal[1]),
        ];

        let mut chal_pow = perm_chal[1];
        for _ in 1..self.elem_len {
            chal_pow *= perm_chal[1];
            perm_chal.push(chal_pow);
        }

        let mut rm = RunningMem {
            priv_is: self.priv_is,
            pub_is: self.pub_is,
            mem_wits,
            stack_wits: vec![vec![]; self.stacks.len()],
            priv_fs,
            pub_fs,
            pub_hash: F::one(),
            ts: F::zero(),
            perm_chal,
            elem_len: self.elem_len,
            stack_elem_lens: self.stack_elem_lens.clone(),
            scan_priv_per_batch,
            scan_pub_per_batch,
            first_priv_addr,
            first_pub_addr,
            priv_s: 0,
            pub_s: 0,
            mem_spaces: self.mem_spaces,
            padding,
            time_bit_limit,
            addr_bit_limit,
            sr_bit_limit,
            verifier_mode: false,
        };

        rm.pub_hash = rm.get_pub_is_hash();

        (ic_cmt, blinds, ram_hints, rm)
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: ArkPrimeField> {
    priv_is: Vec<HeapElem<F>>,
    pub_is: Vec<HeapElem<F>>,
    mem_wits: HashMap<F, HeapElem<F>>,
    stack_wits: Vec<Vec<(F, StackElem<F>)>>,
    priv_fs: Vec<HeapElem<F>>,
    pub_fs: Vec<HeapElem<F>>,
    pub_hash: F,
    ts: F,
    pub perm_chal: Vec<F>,
    pub elem_len: usize,
    pub stack_elem_lens: Vec<usize>,
    pub scan_priv_per_batch: usize,
    pub scan_pub_per_batch: usize,
    pub first_priv_addr: F,
    pub first_pub_addr: F,
    priv_s: usize, // iter through scan
    pub_s: usize,  // iter through scan
    mem_spaces: Vec<MemType>,
    padding: HeapElem<F>,
    time_bit_limit: usize,
    addr_bit_limit: usize,
    sr_bit_limit: usize,
    verifier_mode: bool,
}

#[derive(Clone, Debug)]
pub struct RunningMemWires<F: ArkPrimeField> {
    // for multiple calls in one CS
    pub cs: ConstraintSystemRef<F>,
    pub running_priv_i: FpVar<F>,
    pub running_pub_i: FpVar<F>,
    pub running_is: FpVar<F>,
    pub running_rs: FpVar<F>,
    pub running_ws: FpVar<F>,
    pub running_fs: FpVar<F>,
    pub ts_m1: FpVar<F>,
    pub perm_chal: Vec<FpVar<F>>,
    pub stack_states: Vec<FpVar<F>>,
    scan_called: bool,
    pub rw_ops: Vec<HeapElemWires<F>>,
    pub stk_ops: Vec<StackElemWires<F>>,
    pub is_ops: Vec<HeapElemWires<F>>,
    pub fs_ops: Vec<HeapElemWires<F>>,
}

impl<F: ArkPrimeField> RunningMem<F> {
    pub fn get_dummy(&self, ic_cmt: &Vec<N2>) -> Self {
        let mem_wits = new_hash_map();

        let nova_perm_chal = sample_challenges(ic_cmt);
        let mut perm_chal = vec![
            nova_to_ark_field::<N1, F>(&nova_perm_chal[0]),
            nova_to_ark_field::<N1, F>(&nova_perm_chal[1]),
        ];

        let mut chal_pow = perm_chal[1];
        for _ in 1..self.elem_len {
            chal_pow *= perm_chal[1];
            perm_chal.push(chal_pow);
        }

        Self {
            priv_is: vec![self.padding.clone(); self.priv_is.len()],
            pub_is: self.pub_is.clone(),
            mem_wits,
            stack_wits: vec![vec![]; self.stack_wits.len()],
            priv_fs: vec![self.padding.clone(); self.priv_fs.len()],
            pub_fs: vec![self.padding.clone(); self.pub_fs.len()],
            pub_hash: self.pub_hash,
            ts: F::zero(),
            perm_chal,
            elem_len: self.elem_len,
            stack_elem_lens: self.stack_elem_lens.clone(),
            scan_priv_per_batch: self.scan_priv_per_batch,
            scan_pub_per_batch: self.scan_pub_per_batch,
            first_priv_addr: self.first_priv_addr,
            first_pub_addr: self.first_pub_addr,
            priv_s: self.priv_s,
            pub_s: self.pub_s,
            mem_spaces: self.mem_spaces.clone(),
            padding: self.padding.clone(),
            time_bit_limit: self.time_bit_limit,
            addr_bit_limit: self.addr_bit_limit,
            sr_bit_limit: self.sr_bit_limit,
            verifier_mode: true,
        }
    }

    pub fn verifier_checks(&self) {
        // TODO

        assert!(self.verifier_mode);
    }

    pub fn get_starting_stack_states(&self) -> Vec<F> {
        vec![F::ZERO; self.stack_elem_lens.len()]
    }

    // can be called by prove on real RunningMem or by Verifier on dummy to produce same result
    pub fn get_pub_is_hash(&self) -> F {
        self.pub_is
            .par_iter()
            .map(|e| e.hash(&self.perm_chal))
            .product::<F>()
    }

    pub fn padding(&self, cs: ConstraintSystemRef<F>) -> Result<HeapElemWires<F>, SynthesisError> {
        Ok(HeapElemWires::new(
            FpVar::new_witness(cs.clone(), || Ok(self.padding.time))?,
            FpVar::new_witness(cs.clone(), || Ok(self.padding.addr))?,
            self.padding
                .vals
                .iter()
                .map(|v| FpVar::new_witness(cs.clone(), || Ok(v)))
                .collect::<Result<Vec<FpVar<F>>, _>>()?,
            FpVar::new_witness(cs.clone(), || Ok(self.padding.sr))?,
        ))
    }

    pub fn begin_new_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        running_priv_i: F,
        running_pub_i: F,
        running_is: F,
        running_rs: F,
        running_ws: F,
        running_fs: F,
        stack_states: &[F],
    ) -> Result<RunningMemWires<F>, SynthesisError> {
        let running_priv_i = FpVar::new_witness(cs.clone(), || Ok(running_priv_i))?;
        let running_pub_i = FpVar::new_witness(cs.clone(), || Ok(running_pub_i))?;
        let running_is = FpVar::new_witness(cs.clone(), || Ok(running_is))?;
        let running_rs = FpVar::new_witness(cs.clone(), || Ok(running_rs))?;
        let running_ws = FpVar::new_witness(cs.clone(), || Ok(running_ws))?;
        let running_fs = FpVar::new_witness(cs.clone(), || Ok(running_fs))?;
        let ts_m1 = FpVar::new_witness(cs.clone(), || Ok(self.ts))?;
        let mut perm_chal = vec![
            FpVar::new_witness(cs.clone(), || Ok(self.perm_chal[0]))?,
            FpVar::new_witness(cs.clone(), || Ok(self.perm_chal[1]))?,
        ];
        let mut chal_pow = perm_chal[1].clone();
        for _ in 1..self.elem_len {
            chal_pow = &chal_pow * &perm_chal[1];
            perm_chal.push(chal_pow.clone());
        }

        let stack_states = stack_states
            .iter()
            .map(|sp| FpVar::new_witness(cs.clone(), || Ok(sp)))
            .collect::<Result<Vec<FpVar<F>>, _>>()?;

        Ok(RunningMemWires {
            cs: cs.clone(),
            running_priv_i,
            running_pub_i,
            running_is,
            running_rs,
            running_ws,
            running_fs,
            ts_m1,
            perm_chal,
            stack_states,
            scan_called: false,
            rw_ops: vec![],
            stk_ops: vec![],
            is_ops: vec![],
            fs_ops: vec![],
        })
    }

    pub fn conditional_push(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(), SynthesisError> {
        assert!(stack_tag < self.stack_wits.len());

        let sw = StackElemWires::new(vals.clone());

        // save nondet wit for pop later
        if cond.value()? {
            self.stack_wits[stack_tag].push((
                w.stack_states[stack_tag].value()?,
                StackElem::new(
                    vals.iter()
                        .map(|w| w.value())
                        .collect::<Result<Vec<F>, SynthesisError>>()?,
                ),
            ));
        }

        w.stack_states[stack_tag] = cond.select(
            &sw.hash(&w.perm_chal[0], &w.stack_states[stack_tag])?,
            &w.stack_states[stack_tag],
        )?;

        w.stk_ops.push(sw);
        Ok(())
    }

    pub fn conditional_pop(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<StackElemWires<F>, SynthesisError> {
        assert!(stack_tag < self.stack_wits.len());

        // get wit
        let (preimage_wit, se) = if cond.value()? {
            self.stack_wits[stack_tag].pop().unwrap()
        } else {
            (
                F::ZERO,
                StackElem::new(vec![F::ZERO; self.stack_elem_lens[stack_tag]]),
            )
        };
        let preimage = FpVar::new_witness(w.cs.clone(), || Ok(preimage_wit))?;
        let sw = StackElemWires::new(
            se.vals
                .iter()
                .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                .collect::<Result<Vec<FpVar<F>>, _>>()?,
        );

        w.stack_states[stack_tag]
            .conditional_enforce_equal(&sw.hash(&w.perm_chal[0], &preimage)?, cond)?;
        w.stack_states[stack_tag] = cond.select(&preimage, &w.stack_states[stack_tag])?;

        w.stk_ops.push(sw.clone());
        Ok(sw)
    }

    pub fn pop(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<StackElemWires<F>, SynthesisError> {
        self.conditional_pop(&Boolean::TRUE, stack_tag, w)
    }

    pub fn push(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(), SynthesisError> {
        self.conditional_push(&Boolean::TRUE, stack_tag, vals, w)
    }

    pub fn conditional_write(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(), SynthesisError> {
        match ty {
            MemType::PrivROM(_) | MemType::PubROM(_) => panic!("cannot write to ROM"),
            _ => {}
        };

        let mut cee_pack_l = Vec::new();
        let mut cee_pack_r = Vec::new();

        let ops = self.conditional_op(
            cond,
            addr,
            Some(vals),
            ty,
            &mut cee_pack_l,
            &mut cee_pack_r,
            w,
        )?;

        chunk_cee(
            cond,
            &cee_pack_l,
            &cee_pack_r,
            max(self.time_bit_limit, self.sr_bit_limit),
            w.cs.clone(),
        )?;

        w.rw_ops.push(ops.0);
        w.rw_ops.push(ops.1);
        Ok(())
    }

    pub fn write(
        &mut self,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(), SynthesisError> {
        self.conditional_write(&Boolean::TRUE, addr, vals, ty, w)
    }

    pub fn conditional_read(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<HeapElemWires<F>, SynthesisError> {
        let mut cee_pack_l = Vec::new();
        let mut cee_pack_r = Vec::new();

        let ops = self.conditional_op(cond, addr, None, ty, &mut cee_pack_l, &mut cee_pack_r, w)?;

        chunk_cee(
            cond,
            &cee_pack_l,
            &cee_pack_r,
            max(self.time_bit_limit, self.sr_bit_limit),
            w.cs.clone(),
        )?;

        let res = ops.1.clone();
        w.rw_ops.push(ops.0);
        w.rw_ops.push(ops.1);

        Ok(res)
    }

    pub fn read(
        &mut self,
        addr: &FpVar<F>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<HeapElemWires<F>, SynthesisError> {
        self.conditional_read(&Boolean::TRUE, addr, ty, w)
    }

    fn conditional_op(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        write_vals: Option<Vec<FpVar<F>>>,
        ty: MemType,
        cee_pack_l: &mut Vec<FpVar<F>>,
        cee_pack_r: &mut Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(HeapElemWires<F>, HeapElemWires<F>), SynthesisError> {
        // ts = ts + 1
        let ts = FpVar::new_witness(w.cs.clone(), || {
            Ok(if cond.value()? {
                w.ts_m1.value()? + F::one()
            } else {
                F::zero() //w.ts_m1.value()?
            })
        })?;
        //ts.conditional_enforce_equal(&(&w.ts_m1 + &FpVar::one()), &cond)?;
        cee_pack_l.push(ts.clone());
        cee_pack_r.push(&w.ts_m1 + &FpVar::one());

        w.ts_m1 = cond.select(&ts, &w.ts_m1)?;
        if cond.value()? {
            self.ts = w.ts_m1.value()?;
        }

        let read_wit = if self.verifier_mode || !cond.value()? {
            &HeapElem {
                time: F::zero(),
                addr: addr.value()?,
                vals: vec![F::zero(); self.elem_len],
                sr: F::zero(),
            }
        } else {
            let rw = self.mem_wits.get(&addr.value()?).unwrap();
            assert_eq!(rw.addr, addr.value()?);
            rw
        };

        let read_mem_elem = HeapElemWires::new(
            FpVar::new_witness(w.cs.clone(), || Ok(read_wit.time))?,
            addr.clone(),
            read_wit
                .vals
                .iter()
                .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                .collect::<Result<Vec<FpVar<F>>, _>>()?,
            FpVar::new_witness(w.cs.clone(), || Ok(read_wit.sr))?,
        );

        // t < ts (not for ROM)
        match ty {
            MemType::PrivRAM(_) | MemType::PubRAM(_) => {
                let bit = custom_ge(&read_mem_elem.time, &ts, 32, w.cs.clone())?;
                cee_pack_l.push(bit.into());
                cee_pack_r.push(FpVar::one());
            }
            _ => {}
        };

        // RS = RS * tup
        let next_running_rs = &w.running_rs * read_mem_elem.hash(&w.perm_chal)?;
        w.running_rs = cond.select(&next_running_rs, &w.running_rs)?;

        // memory namespace
        /*read_mem_elem.sr.conditional_enforce_equal(
            &FpVar::<F>::new_constant(w.cs.clone(), F::from(mem_type as u64))?,
            cond,
        )?;*/
        let mem_type = self.mem_spaces.iter().position(|r| *r == ty).unwrap();
        cee_pack_l.push(read_mem_elem.sr.clone());
        cee_pack_r.push(FpVar::constant(F::from(mem_type as u64)));

        let v_prime = if let Some(vals) = write_vals {
            assert_eq!(vals.len(), self.elem_len);
            vals
        } else {
            read_mem_elem.vals.clone()
        };

        if cond.value()? {
            self.mem_wits.insert(
                addr.value()?,
                HeapElem::new_f(
                    ts.value()?,
                    addr.value()?,
                    v_prime
                        .iter()
                        .map(|v| v.value())
                        .collect::<Result<Vec<F>, _>>()?,
                    read_mem_elem.sr.value()?,
                ),
            );
        }

        // WS = WS * tup
        // write mem elem sr == read mem elem sr (important to perserve this wire)
        let write_mem_elem =
            HeapElemWires::new(ts, addr.clone(), v_prime, read_mem_elem.sr.clone());
        let next_running_ws = &w.running_ws * write_mem_elem.hash(&w.perm_chal)?;
        w.running_ws = cond.select(&next_running_ws, &w.running_ws)?;

        Ok((read_mem_elem, write_mem_elem))
    }

    // call once per step circuit
    pub fn scan(
        &mut self,
        w: &mut RunningMemWires<F>,
        last_round: bool, // is this the last folding?
    ) -> Result<Boolean<F>, SynthesisError> {
        w.scan_called = true;
        assert!(!self.priv_fs.is_empty() || !self.pub_fs.is_empty()); // otherwise, no need to scan

        let mut eez_pack = Vec::new();
        let mut ee_addr_pack_l = Vec::new();
        let mut ee_addr_pack_r = Vec::new();

        for (scan_per_batch, is_vec, fs_vec, mut s, priv_op) in [
            (
                self.scan_priv_per_batch,
                &self.priv_is,
                &self.priv_fs,
                self.priv_s,
                true,
            ),
            (
                self.scan_pub_per_batch,
                &self.pub_is,
                &self.pub_fs,
                self.pub_s,
                false,
            ),
        ] {
            for _ in 0..scan_per_batch {
                let (final_mem_elem, cond) = if s < fs_vec.len() {
                    let fs_wit = fs_vec[s].clone();
                    (
                        HeapElemWires::new(
                            FpVar::new_witness(w.cs.clone(), || Ok(fs_wit.time))?,
                            FpVar::new_witness(w.cs.clone(), || Ok(fs_wit.addr))?,
                            fs_wit
                                .vals
                                .iter()
                                .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                                .collect::<Result<Vec<FpVar<F>>, _>>()?,
                            FpVar::new_witness(w.cs.clone(), || Ok(fs_wit.sr))?,
                        ),
                        Boolean::new_witness(w.cs.clone(), || Ok(true))?,
                    )
                } else {
                    (
                        self.padding(w.cs.clone())?,
                        Boolean::new_witness(w.cs.clone(), || Ok(false))?,
                    )
                };

                // FS check
                let next_running_fs = &w.running_fs * final_mem_elem.hash(&w.perm_chal)?;
                w.running_fs = cond.select(&next_running_fs, &w.running_fs)?;

                if priv_op {
                    let (initial_mem_elem, cond) = if s < is_vec.len() {
                        let is_wit = is_vec[s].clone();
                        (
                            HeapElemWires::new(
                                FpVar::new_witness(w.cs.clone(), || Ok(is_wit.time))?,
                                FpVar::new_witness(w.cs.clone(), || Ok(is_wit.addr))?,
                                is_wit
                                    .vals
                                    .iter()
                                    .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                                    .collect::<Result<Vec<FpVar<F>>, _>>()?,
                                FpVar::new_witness(w.cs.clone(), || Ok(is_wit.sr))?,
                            ),
                            Boolean::new_witness(w.cs.clone(), || Ok(true))?,
                        )
                    } else {
                        (
                            self.padding(w.cs.clone())?,
                            Boolean::new_witness(w.cs.clone(), || Ok(false))?,
                        )
                    };

                    // initial_mem_elem.time.enforce_equal(&FpVar::zero())?;
                    eez_pack.push(initial_mem_elem.time.clone());

                    // IS check
                    let next_running_is = &w.running_is * initial_mem_elem.hash(&w.perm_chal)?;
                    w.running_is = cond.select(&next_running_is, &w.running_is)?;

                    // a = a' = i
                    // initial_mem_elem.addr.enforce_equal(&final_mem_elem.addr)?;
                    ee_addr_pack_l.push(initial_mem_elem.addr.clone());
                    ee_addr_pack_r.push(final_mem_elem.addr.clone());

                    let not_padding = final_mem_elem.addr.is_neq(&FpVar::zero())?;
                    final_mem_elem
                        .addr
                        .conditional_enforce_equal(&w.running_priv_i, &not_padding)?;

                    // i += 1
                    w.running_priv_i =
                        not_padding.select(&(&w.running_priv_i + F::one()), &w.running_priv_i)?;

                    self.priv_s += 1;
                    w.is_ops.push(initial_mem_elem);
                } else {
                    // a = a' = i
                    let not_padding = final_mem_elem.addr.is_neq(&FpVar::zero())?;
                    final_mem_elem
                        .addr
                        .conditional_enforce_equal(&w.running_pub_i, &not_padding)?;

                    // i += 1
                    w.running_pub_i =
                        not_padding.select(&(&w.running_pub_i + F::one()), &w.running_pub_i)?;

                    self.pub_s += 1;
                }

                // TODO enforce domain

                s += 1;
                w.fs_ops.push(final_mem_elem);
            }
        }

        // final check
        let last_check = Boolean::new_witness(w.cs.clone(), || Ok(last_round))?;
        let union = &(&w.running_is * &w.running_ws * &FpVar::constant(self.pub_hash))
            .is_eq(&(&w.running_fs * &w.running_rs))?;
        union.conditional_enforce_equal(&Boolean::TRUE, &last_check)?;

        w.running_is = last_check.select(&FpVar::constant(F::zero()), &w.running_is)?;
        w.running_rs = last_check.select(&FpVar::zero(), &w.running_rs)?;
        w.running_ws = last_check.select(&FpVar::zero(), &w.running_ws)?;
        w.running_fs = last_check.select(&FpVar::zero(), &w.running_fs)?;

        // packed
        chunk_ee_zero(&eez_pack, self.time_bit_limit, w.cs.clone())?;
        chunk_ee(
            &ee_addr_pack_l,
            &ee_addr_pack_r,
            self.addr_bit_limit,
            w.cs.clone(),
        )?;

        Ok(last_check)
    }

    pub fn ivcify(&self, w: &RunningMemWires<F>) -> Result<(), SynthesisError> {
        assert!(w.scan_called || (self.priv_fs.is_empty() && self.pub_fs.is_empty()));

        // [is, rs, ws, stk, fs]
        for o in &w.is_ops {
            o.ivcify(w.cs.clone())?;
        }
        for o in &w.rw_ops {
            o.ivcify(w.cs.clone())?;
        }
        for o in &w.stk_ops {
            o.ivcify(w.cs.clone())?;
        }
        for o in &w.fs_ops {
            o.ivcify(w.cs.clone())?;
        }

        println!("INIT");
        for mo in &w.is_ops {
            mo.print_vals();
        }
        println!("RW");
        for mo in &w.rw_ops {
            mo.print_vals();
        }
        println!("STK");
        for mo in &w.stk_ops {
            mo.print_vals();
        }
        println!("FINAL");
        for mo in &w.fs_ops {
            mo.print_vals();
        }

        Ok(())
    }
}

// deterministic
pub fn sample_challenges(ic_cmts: &Vec<N2>) -> [N1; 2] {
    let ro_consts = ROConstants::<E1>::default();
    let mut hasher = <E1 as Engine>::RO::new(ro_consts);
    for c in ic_cmts {
        hasher.absorb(*c);
    }

    [
        scalar_as_base::<E2>(hasher.squeeze(250)),
        scalar_as_base::<E2>(hasher.squeeze(250)),
    ] // num hash bits from nova
}

#[cfg(test)]
mod tests {
    use crate::bellpepper::*;
    use crate::memory::nebula::*;
    use ark_ff::One;
    use ark_relations::gr1cs::{ConstraintSystem, OptimizationGoal};
    use nova_snark::{
        nova::{CompressedSNARK, PublicParams, RandomLayer, RecursiveSNARK},
        traits::{snark::default_ck_hint, Engine},
    };

    type A = ark_bn254::Fr;

    fn make_full_mem_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        do_rw_ops: fn(usize, &mut RunningMem<A>, &mut RunningMemWires<A>),
        running_priv_i: &mut A,
        running_pub_i: &mut A,
        running_is: &mut A,
        running_rs: &mut A,
        running_ws: &mut A,
        running_fs: &mut A,
        stack_states: &mut Vec<A>,
        stk_only: bool,
        last_fold: bool,
    ) -> FCircuit<N1> {
        let cs = ConstraintSystem::<A>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        let mut running_mem_wires = rm
            .begin_new_circuit(
                cs.clone(),
                *running_priv_i,
                *running_pub_i,
                *running_is,
                *running_rs,
                *running_ws,
                *running_fs,
                stack_states,
            )
            .unwrap();

        let running_priv_i_prev = running_mem_wires.running_priv_i.clone();
        let running_pub_i_prev = running_mem_wires.running_pub_i.clone();
        let running_is_prev = running_mem_wires.running_is.clone();
        let running_rs_prev = running_mem_wires.running_rs.clone();
        let running_ws_prev = running_mem_wires.running_ws.clone();
        let running_fs_prev = running_mem_wires.running_fs.clone();

        do_rw_ops(i, rm, &mut running_mem_wires);

        let last_check = if !stk_only {
            let res = rm.scan(&mut running_mem_wires, last_fold);
            assert!(res.is_ok());
            res.unwrap()
        } else {
            Boolean::FALSE
        };
        let res = rm.ivcify(&running_mem_wires);
        assert!(res.is_ok());

        // TODO MOVE
        let (running_is_in, running_is_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_is_prev.value().unwrap()),
            || Ok(running_mem_wires.running_is.value().unwrap()),
        )
        .unwrap();
        running_is_in.enforce_equal(&running_is_prev).unwrap();
        running_is_out
            .enforce_equal(&running_mem_wires.running_is)
            .unwrap();

        let (running_rs_in, running_rs_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_rs_prev.value().unwrap()),
            || Ok(running_mem_wires.running_rs.value().unwrap()),
        )
        .unwrap();
        running_rs_in.enforce_equal(&running_rs_prev).unwrap();
        running_rs_out
            .enforce_equal(&running_mem_wires.running_rs)
            .unwrap();

        let (running_ws_in, running_ws_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_ws_prev.value().unwrap()),
            || Ok(running_mem_wires.running_ws.value().unwrap()),
        )
        .unwrap();
        running_ws_in.enforce_equal(&running_ws_prev).unwrap();
        running_ws_out
            .enforce_equal(&running_mem_wires.running_ws)
            .unwrap();

        let (running_fs_in, running_fs_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_fs_prev.value().unwrap()),
            || Ok(running_mem_wires.running_fs.value().unwrap()),
        )
        .unwrap();
        running_fs_in.enforce_equal(&running_fs_prev).unwrap();
        running_fs_out
            .enforce_equal(&running_mem_wires.running_fs)
            .unwrap();

        // i
        let (running_priv_i_in, running_priv_i_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_priv_i_prev.value().unwrap()),
            || Ok(running_mem_wires.running_priv_i.value().unwrap()),
        )
        .unwrap();
        running_priv_i_in
            .enforce_equal(&running_priv_i_prev)
            .unwrap();
        running_priv_i_out
            .enforce_equal(&running_mem_wires.running_priv_i)
            .unwrap();
        let (running_pub_i_in, running_pub_i_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_pub_i_prev.value().unwrap()),
            || Ok(running_mem_wires.running_pub_i.value().unwrap()),
        )
        .unwrap();
        running_pub_i_in.enforce_equal(&running_pub_i_prev).unwrap();
        running_pub_i_out
            .enforce_equal(&running_mem_wires.running_pub_i)
            .unwrap();
        if !stk_only {
            // last
            let (_, last_out) = Boolean::new_input_output_pair(
                cs.clone(),
                || Ok(last_check.value().unwrap()),
                || Ok(last_check.value().unwrap()),
            )
            .unwrap();
            // don't need in
            last_out.enforce_equal(&last_check).unwrap();
        }
        // running mem, stack ptrs, etc, needs to be ivcified too, but that doesn't effect our final checks
        // so we omit for now

        *running_priv_i = running_mem_wires.running_priv_i.value().unwrap(); //running_i_out.value().unwrap();
        *running_pub_i = running_mem_wires.running_pub_i.value().unwrap(); //running_i_out.value().unwrap();
        *running_is = running_is_out.value().unwrap();
        *running_rs = running_rs_out.value().unwrap();
        *running_ws = running_ws_out.value().unwrap();
        *running_fs = running_fs_out.value().unwrap();
        *stack_states = running_mem_wires
            .stack_states
            .iter()
            .map(|f| f.value().unwrap())
            .collect();

        FCircuit::new(cs, None)
    }

    fn run_ram_nova(
        num_iters: usize,
        heap_batch_size: usize,
        stk_batch_sizes: Vec<usize>,
        mem_builder: MemBuilder<A>,
        stk_only: bool,
        do_rw_ops: fn(usize, &mut RunningMem<A>, &mut RunningMemWires<A>),
    ) {
        type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
        type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
        type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
        type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

        let (c_final, blinds, ram_hints, mut rm) = mem_builder.new_running_mem(
            heap_batch_size,
            stk_batch_sizes.clone(),
            false,
            "./ppot_0080_20.ptau",
        );

        // nova
        let mut running_priv_i = rm.first_priv_addr;
        let mut running_pub_i = rm.first_pub_addr;
        let mut running_is = A::one();
        let mut running_rs = A::one();
        let mut running_ws = A::one();
        let mut running_fs = A::one();
        let mut stack_ptrs = rm.get_starting_stack_states();

        let mut circuit_primary = make_full_mem_circ(
            0,
            &mut rm,
            do_rw_ops,
            &mut running_priv_i,
            &mut running_pub_i,
            &mut running_is,
            &mut running_rs,
            &mut running_ws,
            &mut running_fs,
            &mut stack_ptrs,
            stk_only,
            false,
        );

        let z0_primary_full = circuit_primary.get_zi();
        let mut ram_hints_len = heap_batch_size * 2 * (3 + rm.elem_len)
            + (rm.scan_priv_per_batch * 2 + rm.scan_pub_per_batch) * (3 + rm.elem_len);
        assert_eq!(stk_batch_sizes.len(), rm.stack_elem_lens.len());
        for (b, l) in stk_batch_sizes.iter().zip(rm.stack_elem_lens.iter()) {
            ram_hints_len += b * l;
        }

        //println!("z0 full {:#?}", z0_primary_full);

        let z0_primary = z0_primary_full[ram_hints_len..].to_vec();

        // produce public parameters
        let ram_batch_sizes = vec![ram_hints_len];
        let pp = PublicParams::<E1, E2, FCircuit<<E1 as Engine>::Scalar>>::setup(
            &mut circuit_primary,
            &*default_ck_hint(),
            &*default_ck_hint(),
            ram_batch_sizes.clone(),
            Some("./ppot_0080_20.ptau"),
        )
        .unwrap();

        // produce a recursive SNARK
        let mut recursive_snark = RecursiveSNARK::<E1, E2, FCircuit<<E1 as Engine>::Scalar>>::new(
            &pp,
            &mut circuit_primary,
            &z0_primary,
            Some(blinds[0].clone()),
            ram_hints[0].clone(),
            ram_batch_sizes.clone(),
        )
        .unwrap();

        for i in 0..num_iters {
            println!("==============================================");
            let res = recursive_snark.prove_step(
                &pp,
                &mut circuit_primary,
                Some(blinds[i].clone()),
                ram_hints[i].clone(),
                ram_batch_sizes.clone(),
            );
            assert!(res.is_ok());
            res.unwrap();

            // verify the recursive SNARK
            let res = recursive_snark.verify(&pp, i + 1, &z0_primary);
            assert!(res.is_ok());

            if i < num_iters - 1 {
                circuit_primary = make_full_mem_circ(
                    i + 1,
                    &mut rm,
                    do_rw_ops,
                    &mut running_priv_i,
                    &mut running_pub_i,
                    &mut running_is,
                    &mut running_rs,
                    &mut running_ws,
                    &mut running_fs,
                    &mut stack_ptrs,
                    stk_only,
                    i == num_iters - 2,
                );
            }
        }

        // produce the prover and verifier keys for compressed snark
        let (pk, vk) = CompressedSNARK::<_, _, _, S1, S2>::setup(&pp).unwrap();

        // produce a compressed SNARK
        let random_layer: RandomLayer<E1, E2> =
            CompressedSNARK::<_, _, _, S1, S2>::sample_random_layer(&pp).unwrap();
        let res =
            CompressedSNARK::<_, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark, random_layer);
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify the compressed SNARK
        let res = compressed_snark.verify(&vk, num_iters, &z0_primary);
        assert!(res.is_ok());

        // check final cmt outputs
        let (zn, ci) = res.unwrap();

        let pub_is = rm.get_pub_is_hash();
        assert_eq!(pub_is, rm.pub_hash);

        println!("Z {:#?}", zn);
        // is * ws == rs * fs (verifier)
        if !stk_only {
            assert_eq!(zn[6], N1::from(1));
        }

        // incr cmt = acc cmt (verifier)
        for i in 0..c_final.len() {
            //    println!("{}", i);
            assert_eq!(c_final[i], ci[i]);
        }
    }

    #[test]
    fn two_stacks() {
        let mut mb = MemBuilder::new(2, vec![2, 2], vec![]);

        // push, pop from stack 1
        mb.push(1, vec![A::from(1), A::from(2)]);
        assert_eq!(mb.pop(1), vec![A::from(1), A::from(2)]);

        // push stack 0
        mb.push(0, vec![A::from(5), A::from(6)]);

        // push, pop stack 1
        mb.push(1, vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(1), vec![A::from(7), A::from(8)]);

        // push stack 0
        mb.push(0, vec![A::from(9), A::from(10)]);

        // 2 iters, [push pop push] each time // 2,3
        run_ram_nova(2, 0, vec![2, 1], mb, true, two_stacks_circ);
    }

    fn two_stacks_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (push_vals_1, push_vals_2) = if i == 0 {
            (vec![1, 2], vec![5, 6])
        } else if i == 1 {
            (vec![7, 8], vec![9, 10])
        } else {
            panic!()
        };

        let res = rm.push(
            1,
            push_vals_1
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.pop(1, rmw);
        assert!(res.is_ok());

        let res = rm.push(
            0,
            push_vals_2
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn stack_ends_empty() {
        let mut mb = MemBuilder::new(2, vec![2], vec![MemType::PrivRAM(0)]);
        // ram
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        mb.push(0, vec![A::from(1), A::from(2)]);
        mb.push(0, vec![A::from(3), A::from(4)]);
        assert_eq!(mb.pop(0), vec![A::from(3), A::from(4)]);
        assert_eq!(mb.pop(0), vec![A::from(1), A::from(2)]);

        mb.push(0, vec![A::from(5), A::from(6)]);
        mb.push(0, vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(0), vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(0), vec![A::from(5), A::from(6)]);

        run_ram_nova(2, 0, vec![4], mb, false, stack_ends_empty_circ);
    }

    fn stack_ends_empty_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (push_vals_1, push_vals_2) = if i == 0 {
            (vec![1, 2], vec![3, 4])
        } else if i == 1 {
            (vec![5, 6], vec![7, 8])
        } else {
            panic!()
        };

        let res = rm.push(
            0,
            push_vals_1
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.push(
            0,
            push_vals_2
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.pop(0, rmw);
        assert!(res.is_ok());

        let res = rm.pop(0, rmw);
        assert!(res.is_ok());
    }

    #[test]
    fn stack_basic() {
        let mut mb = MemBuilder::new(2, vec![2], vec![MemType::PrivRAM(0)]);
        // stack doesn't need to be init
        // ram
        mb.init(1, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        mb.push(0, vec![A::from(1), A::from(2)]);
        mb.push(0, vec![A::from(3), A::from(4)]);
        assert_eq!(mb.pop(0), vec![A::from(3), A::from(4)]);

        mb.push(0, vec![A::from(5), A::from(6)]);
        mb.push(0, vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(0), vec![A::from(7), A::from(8)]);

        run_ram_nova(2, 0, vec![3], mb, false, stack_basic_circ);
    }

    fn stack_basic_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (push_vals_1, push_vals_2) = if i == 0 {
            (vec![1, 2], vec![3, 4])
        } else if i == 1 {
            (vec![5, 6], vec![7, 8])
        } else {
            panic!()
        };

        let res = rm.push(
            0,
            push_vals_1
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.push(
            0,
            push_vals_2
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.pop(0, rmw);
        assert!(res.is_ok());
    }

    #[test]
    fn mem_cond_simple() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivRAM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivRAM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivRAM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PrivRAM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        assert_eq!(
            vec![A::from(10), A::from(11)],
            mb.cond_read(true, 1, MemType::PrivRAM(0))
        ); // vec![A::from(2), A::from(9)], MemType::PrivRAM(0));
        assert_eq!(
            vec![A::from(10), A::from(11)],
            mb.cond_read(true, 1, MemType::PrivRAM(0))
        ); //vec![A::from(2), A::from(9)], MemType::PrivRAM(0));

        run_ram_nova(2, 1, vec![], mb, false, mem_cond_simple_circ);
    }

    fn mem_cond_simple_circ(_i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (cond_value, read_addr) = (true, 1);

        let cond = Boolean::new_witness(rmw.cs.clone(), || Ok(cond_value)).unwrap();

        let res = rm.conditional_read(
            &cond,
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr as u64))).unwrap(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn mem_conditional() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivRAM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivRAM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivRAM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PrivRAM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        assert_eq!(
            mb.cond_read(true, 1, MemType::PrivRAM(0)),
            vec![A::from(10), A::from(11)]
        );
        mb.cond_write(true, 2, vec![A::from(18), A::from(19)], MemType::PrivRAM(0));

        // TODO
        mb.cond_read(false, 0, MemType::PrivRAM(0));
        mb.cond_write(
            false,
            0,
            vec![A::from(18), A::from(19)],
            MemType::PrivRAM(0),
        );

        assert_eq!(
            mb.cond_read(true, 3, MemType::PrivRAM(0)),
            vec![A::from(14), A::from(15)]
        );
        mb.cond_write(true, 4, vec![A::from(20), A::from(21)], MemType::PrivRAM(0));

        run_ram_nova(3, 2, vec![], mb, false, mem_conditional_circ);
    }

    fn mem_conditional_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (cond_value, read_addr, write_addr, write_vals) = if i == 0 {
            (true, 1, 2, vec![18, 19])
        } else if i == 1 {
            (false, 0, 0, vec![0, 0]) //(false, 1, 2, vec![18, 19])
        } else if i == 2 {
            (true, 3, 4, vec![20, 21])
        } else {
            panic!()
        };

        let cond = Boolean::new_witness(rmw.cs.clone(), || Ok(cond_value)).unwrap();

        let res = rm.conditional_read(
            &cond,
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr as u64))).unwrap(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.conditional_write(
            &cond,
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(write_addr))).unwrap(),
            write_vals
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn mem_extra_init() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivRAM(0), MemType::PubRAM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivRAM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivRAM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PrivRAM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));
        mb.init(500, vec![A::from(30), A::from(40)], MemType::PubRAM(0));

        assert_eq!(
            mb.read(1, MemType::PrivRAM(0)),
            vec![A::from(10), A::from(11)]
        );
        mb.write(2, vec![A::from(18), A::from(19)], MemType::PrivRAM(0));

        assert_eq!(
            mb.read(3, MemType::PrivRAM(0)),
            vec![A::from(14), A::from(15)]
        );
        mb.write(4, vec![A::from(20), A::from(21)], MemType::PrivRAM(0));

        run_ram_nova(2, 2, vec![], mb, false, mem_basic_circ);
    }

    #[test]
    fn mem_pub_rom() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivROM(0), MemType::PubROM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivROM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivROM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PubROM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PubROM(0));

        assert_eq!(
            mb.read(3, MemType::PubROM(0)),
            vec![A::from(14), A::from(15)]
        );
        assert_eq!(
            mb.read(1, MemType::PrivROM(0)),
            vec![A::from(10), A::from(11)]
        );

        assert_eq!(
            mb.read(4, MemType::PubROM(0)),
            vec![A::from(16), A::from(17)]
        );
        assert_eq!(
            mb.read(2, MemType::PrivROM(0)),
            vec![A::from(12), A::from(13)]
        );

        run_ram_nova(2, 2, vec![], mb, false, mem_pub_rom_circ);
    }

    fn mem_pub_rom_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (read_addr_1, read_addr_2) = if i == 0 {
            (3, 1)
        } else if i == 1 {
            (4, 2)
        } else {
            panic!()
        };

        let res = rm.read(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr_1 as u64))).unwrap(),
            MemType::PubROM(0),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.read(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr_2 as u64))).unwrap(),
            MemType::PrivROM(0),
            rmw,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn mem_basic() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivRAM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivRAM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivRAM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PrivRAM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        assert_eq!(
            mb.read(1, MemType::PrivRAM(0)),
            vec![A::from(10), A::from(11)]
        );
        mb.write(2, vec![A::from(18), A::from(19)], MemType::PrivRAM(0));

        assert_eq!(
            mb.read(3, MemType::PrivRAM(0)),
            vec![A::from(14), A::from(15)]
        );
        mb.write(4, vec![A::from(20), A::from(21)], MemType::PrivRAM(0));

        run_ram_nova(2, 2, vec![], mb, false, mem_basic_circ);
    }

    fn mem_basic_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (read_addr, write_addr, write_vals) = if i == 0 {
            (1, 2, vec![18, 19])
        } else if i == 1 {
            (3, 4, vec![20, 21])
        } else {
            panic!()
        };

        let res = rm.read(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr as u64))).unwrap(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());

        let res = rm.write(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(write_addr))).unwrap(),
            write_vals
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());
    }

    #[test]
    fn mem_bigger_init() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivRAM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivRAM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivRAM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PrivRAM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        mb.write(1, vec![A::from(18), A::from(19)], MemType::PrivRAM(0));
        mb.write(2, vec![A::from(20), A::from(21)], MemType::PrivRAM(0));

        run_ram_nova(2, 1, vec![], mb, false, mem_bigger_init_circ);
    }

    fn mem_bigger_init_circ(i: usize, rm: &mut RunningMem<A>, rmw: &mut RunningMemWires<A>) {
        let (write_addr, write_vals) = if i == 0 {
            (1, vec![18, 19])
        } else if i == 1 {
            (2, vec![20, 21])
        } else {
            panic!()
        };

        let res = rm.write(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(write_addr))).unwrap(),
            write_vals
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());
    }
}
