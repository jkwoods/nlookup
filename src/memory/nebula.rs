use crate::bellpepper::{ark_to_nova_field, ark_to_u64, nova_to_ark_field};
use crate::utils::*;
use ark_ff::{BigInteger256, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    GR1CSVar,
};
use ark_relations::{
    gr1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
    lc, ns,
};
use ark_std::test_rng;
use nova_snark::{
    gadgets::utils::scalar_as_base,
    provider::incremental::Incremental,
    traits::{
        commitment::{CommitmentEngineTrait, Len},
        Engine, ROConstants, ROTrait,
    },
};
use std::collections::HashMap;

type CommitmentKey<E> = <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey;

#[derive(Clone, Debug, PartialEq)]
pub struct MemElem<F: arkPrimeField> {
    pub time: F,
    pub addr: F,
    pub vals: Vec<F>,
    pub sr: F,
}

impl<F: arkPrimeField> MemElem<F> {
    pub fn new_u(t: usize, a: usize, v: Vec<usize>, sr: usize) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(a as u64),
            vals: v.into_iter().map(|x| F::from(x as u64)).collect(),
            sr: F::from(sr as u64),
        }
    }

    pub fn new_f(t: F, a: F, v: Vec<F>, sr: F) -> Self {
        MemElem {
            time: t,
            addr: a,
            vals: v,
            sr: sr,
        }
    }

    pub fn get_vec(&self) -> Vec<F> {
        let mut v = vec![self.time, self.addr, self.sr];
        v.extend(self.vals.clone());

        v
    }

    pub fn hash(&self, perm_chal: F) -> F {
        let mut hash = (perm_chal - self.time) * (perm_chal - self.addr) * (perm_chal - self.sr);

        for i in 0..self.vals.len() {
            hash = hash * (perm_chal - self.vals[i]);
        }

        hash
    }
}

#[derive(Clone, Debug)]
pub struct MemElemWires<F: arkPrimeField> {
    pub time: FpVar<F>,
    pub addr: FpVar<F>,
    pub vals: Vec<FpVar<F>>,
    pub sr: FpVar<F>,
}

impl<F: arkPrimeField> MemElemWires<F> {
    pub fn new(t: FpVar<F>, a: FpVar<F>, v: Vec<FpVar<F>>, sr: FpVar<F>) -> Self {
        MemElemWires {
            time: t,
            addr: a,
            vals: v,
            sr: sr,
        }
    }

    pub fn assert_eq(&self, m: &MemElem<F>) {
        assert_eq!(self.time.value().unwrap(), (*m).time);
        assert_eq!(self.addr.value().unwrap(), (*m).addr);
        for j in 0..self.vals.len() {
            assert_eq!(self.vals[j].value().unwrap(), (*m).vals[j]);
        }
        assert_eq!(self.sr.value().unwrap(), (*m).sr);
    }

    pub fn print_vals(&self) {
        let sr_val = self.sr.value().unwrap();
        println!(
            "MemElem [{:#?} [time {:#?}] [addr {:#?}] [vals {:#?}]]",
            self.sr.value().unwrap(), //self.mem_spaces[ark_to_u64(&self.sr.value().unwrap())]
            self.time.value().unwrap(),
            self.addr.value().unwrap(),
            self.vals
                .iter()
                .map(|v| v.value().unwrap())
                .collect::<Vec<F>>()
        );
    }

    pub fn hash(
        &self,
        cs: ConstraintSystemRef<F>,
        perm_chal: &FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut hash = (perm_chal - &self.time) * (perm_chal - &self.addr) * (perm_chal - &self.sr);

        for i in 0..self.vals.len() {
            hash = hash * (perm_chal - &self.vals[i]);
        }

        Ok(hash)
    }
}

#[derive(Clone, Eq, Debug, PartialEq, PartialOrd, Ord)]
pub enum MemType {
    PrivStack(usize), // 0
    PrivROM(usize),
    PrivRAM(usize),
    PubROM(usize),
    PubRAM(usize),
}

// builds the witness for RunningMem
#[derive(Debug)]
pub struct MemBuilder<F: arkPrimeField> {
    mem: HashMap<usize, MemElem<F>>,
    pub_is: Vec<MemElem<F>>,
    priv_is: Vec<MemElem<F>>,
    rs: Vec<MemElem<F>>,
    ws: Vec<MemElem<F>>,
    fs: HashMap<usize, MemElem<F>>,
    mem_spaces: Vec<MemType>, // only mem here, stack is 0
    stack_spaces: Vec<usize>,
    stack_ptrs: Vec<usize>,
    pub elem_len: usize,
    ts: usize,
}

impl<F: arkPrimeField> MemBuilder<F> {
    pub fn new(elem_len: usize, stack_sizes: Vec<usize>, mut mem_spaces: Vec<MemType>) -> Self {
        assert!(elem_len > 0);

        mem_spaces.sort();
        mem_spaces.dedup();
        for m in &mem_spaces {
            match m {
                MemType::PrivStack(_) => panic!("mem spaces is only for non stack mem"),
                _ => {}
            }
        }

        let mut stack_spaces = Vec::new();
        let mut stack_ptrs = Vec::new();

        if stack_sizes.len() > 0 {
            stack_spaces.push(1);
            let mut stack_limit = 1;

            for (i, s) in stack_sizes.iter().enumerate() {
                stack_ptrs.push(stack_limit);
                stack_limit += s;
                stack_spaces.push(stack_limit);
            }
        }

        Self {
            mem: HashMap::new(),
            pub_is: Vec::new(),
            priv_is: Vec::new(),
            rs: Vec::new(),
            ws: Vec::new(),
            fs: HashMap::new(),
            mem_spaces,
            stack_spaces,
            stack_ptrs,
            elem_len,
            ts: 0,
        }
    }

    pub fn push(&mut self, stack_tag: usize, vals: Vec<F>) {
        self.cond_push(true, stack_tag, vals)
    }

    pub fn cond_push(&mut self, cond: bool, stack_tag: usize, vals: Vec<F>) {
        self.inner_cond_write(cond, self.stack_ptrs[stack_tag], vals, 0);

        if cond {
            self.stack_ptrs[stack_tag] += 1;
        }
        assert!(self.stack_ptrs[stack_tag] <= self.stack_spaces[stack_tag + 1]);
    }

    pub fn pop(&mut self, stack_tag: usize) -> Vec<F> {
        self.cond_pop(true, stack_tag)
    }

    pub fn cond_pop(&mut self, cond: bool, stack_tag: usize) -> Vec<F> {
        if cond {
            self.stack_ptrs[stack_tag] -= 1;
        }

        assert!(self.stack_ptrs[stack_tag] >= self.stack_spaces[stack_tag]);

        self.inner_cond_read(cond, self.stack_ptrs[stack_tag], 0)
    }

    pub fn read(&mut self, addr: usize, ty: MemType) -> Vec<F> {
        self.cond_read(true, addr, ty)
    }

    pub fn cond_read(&mut self, cond: bool, addr: usize, ty: MemType) -> Vec<F> {
        let mem_tag = match ty {
            MemType::PrivStack(_) => panic!("cannot read from stack, only pop"),
            m => self.mem_spaces.iter().position(|r| *r == m).unwrap() + 1,
        };
        self.inner_cond_read(cond, addr, mem_tag)
    }

    fn inner_cond_read(&mut self, cond: bool, addr: usize, mem_tag: usize) -> Vec<F> {
        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(&addr).unwrap().clone()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, F::from(addr as u64));
        self.rs.push(read_elem.clone());

        if cond {
            self.ts += 1;
        }

        let write_elem = MemElem::new_f(
            F::from(self.ts as u64),
            F::from(addr as u64),
            read_elem.vals.clone(),
            F::from(mem_tag as u64),
        );
        if cond {
            self.mem.insert(addr, write_elem.clone());
        }
        self.ws.push(write_elem.clone());

        if cond {
            self.fs.insert(addr, write_elem);
        }

        read_elem.vals
    }

    // initialize memory
    // note: if you plan on writing to an addr, it must be initialized
    pub fn init(&mut self, addr: usize, vals: Vec<F>, mem_tag: MemType) {
        assert_ne!(addr, 0);

        self.inner_init(addr, vals, mem_tag);
    }

    fn inner_init(&mut self, addr: usize, vals: Vec<F>, mem_tag: MemType) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert!(!self.mem.contains_key(&addr));

        let sr = match mem_tag {
            MemType::PrivStack(stack_tag) => {
                assert!(vals.iter().all(|v| *v == F::ZERO));
                assert!(addr < self.stack_spaces[stack_tag + 1]);
                assert!(addr >= self.stack_spaces[stack_tag]);
                0
            }
            ref m => self.mem_spaces.iter().position(|r| *r == *m).unwrap() + 1,
        };

        let elem = MemElem::new_f(F::ZERO, F::from(addr as u64), vals, F::from(sr as u64));
        self.mem.insert(addr, elem.clone());

        match mem_tag {
            MemType::PrivRAM(_) | MemType::PrivROM(_) | MemType::PrivStack(_) => {
                self.priv_is.push(elem.clone())
            }
            MemType::PubRAM(_) | MemType::PubROM(_) => self.pub_is.push(elem.clone()),
        }
        self.fs.insert(addr, elem);
    }

    fn inner_cond_write(&mut self, cond: bool, addr: usize, vals: Vec<F>, mem_type: usize) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");

        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(&addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, F::from(addr as u64));

        self.rs.push(read_elem.clone());
        if cond {
            self.ts += 1;
        }

        let write_elem = MemElem::new_f(
            F::from(self.ts as u64),
            read_elem.addr,
            vals,
            F::from(mem_type as u64),
        );
        if cond {
            self.mem.insert(addr, write_elem.clone());
        }
        self.ws.push(write_elem.clone());

        if cond {
            self.fs.insert(addr, write_elem);
        }
    }

    pub fn write(&mut self, addr: usize, vals: Vec<F>, ty: MemType) {
        self.cond_write(true, addr, vals, ty)
    }

    pub fn cond_write(&mut self, cond: bool, addr: usize, vals: Vec<F>, ty: MemType) {
        let mem_tag = match ty {
            MemType::PrivStack(_) => panic!("cannot write to stack, only push"),
            MemType::PrivROM(_) | MemType::PubROM(_) => panic!("cannot write to ROM"),
            m => self.mem_spaces.iter().position(|r| *r == m).unwrap() + 1,
        };

        self.inner_cond_write(cond, addr, vals, mem_tag);
    }

    fn ic_to_ram(
        &self,
        ic_gen: &Incremental<E1, E2>,
        rw_batch_size: usize,
        scan_batch_size: usize, // priv is/fs size
        num_iters: usize,
        sep_final: bool, // true -> cmts/ivcify =  [is], [rs, ws], [fs]
        // false -> cmts/ivcify = [is], [rs, ws, fs]
        priv_fs: &[MemElem<F>],
        padding: &MemElem<F>,
    ) -> (Vec<N2>, Vec<Vec<N1>>, Vec<Vec<N1>>) {
        let num_cmts = if sep_final { 3 } else { 1 };

        let mut ci: Vec<Option<N2>> = vec![None; num_cmts];
        let mut blinds: Vec<Vec<N1>> = vec![Vec::new(); num_iters];
        let mut ram_hints = Vec::new();

        for i in 0..num_iters {
            let mut is_hint = Vec::new();
            let mut rs_ws_hint = Vec::new();
            let mut fs_hint = Vec::new();

            let is_slice = if (i * scan_batch_size + scan_batch_size) <= self.priv_is.len() {
                self.priv_is[(i * scan_batch_size)..(i * scan_batch_size + scan_batch_size)]
                    .to_vec()
            } else {
                if (i * scan_batch_size) <= self.priv_is.len() {
                    let mut is_slice = self.priv_is[(i * scan_batch_size)..].to_vec();
                    is_slice.extend(vec![padding.clone(); scan_batch_size - is_slice.len()]);

                    is_slice
                } else {
                    vec![padding.clone(); scan_batch_size]
                }
            };

            let fs_slice = if (i * scan_batch_size + scan_batch_size) <= priv_fs.len() {
                (priv_fs[(i * scan_batch_size)..(i * scan_batch_size + scan_batch_size)].to_vec())
            } else {
                if (i * scan_batch_size) <= priv_fs.len() {
                    let mut fs_slice = priv_fs[(i * scan_batch_size)..].to_vec();
                    fs_slice.extend(vec![padding.clone(); scan_batch_size - fs_slice.len()]);

                    fs_slice
                } else {
                    (vec![padding.clone(); scan_batch_size])
                }
            };

            for im in is_slice {
                let nova_im: Vec<N1> = im
                    .get_vec()
                    .iter()
                    .map(|a| ark_to_nova_field::<F, N1>(a))
                    .collect();
                is_hint.extend(nova_im);
            }

            for fm in fs_slice.iter() {
                let nova_fm: Vec<N1> = fm
                    .get_vec()
                    .iter()
                    .map(|a| ark_to_nova_field::<F, N1>(a))
                    .collect();

                fs_hint.extend(nova_fm);
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

            let mut ordered_hints: Vec<_> = is_hint;
            ordered_hints.extend(rs_ws_hint);
            ordered_hints.extend(fs_hint);

            let isb = scan_batch_size * (3 + self.elem_len);
            let fsb = scan_batch_size * (3 + self.elem_len);
            let rwb = rw_batch_size * (3 + self.elem_len);

            let hint_ranges = if sep_final {
                vec![
                    0..isb,
                    isb..(isb + rwb * 2),
                    (isb + rwb * 2)..(isb + fsb + rwb * 2),
                ]
            } else {
                vec![0..(isb + fsb + rwb * 2)]
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

            for j in 0..num_cmts {
                //println!("cmt wits {:#?}", cmt_wits[j]);
                let (hash, blind) = ic_gen.commit(ci[j], &cmt_wits[j]);
                ci[j] = Some(hash);

                blinds[i].push(blind);
            }
            ram_hints.push(ordered_hints);
        }

        let final_cmts = ci.iter().map(|c| c.unwrap()).collect();

        (final_cmts, blinds, ram_hints)
    }

    // consumes the mem builder object
    pub fn new_running_mem(
        mut self,
        rw_batch_size: usize,
        sep_final: bool, // true -> cmts/ivcify =  [is], [rs, ws], [fs]
                         // false -> cmts/ivcify = [is, rs, ws, fs]
    ) -> (Vec<N2>, Vec<Vec<N1>>, Vec<Vec<N1>>, RunningMem<F>) {
        assert_eq!(self.rs.len(), self.ws.len());
        assert!(self.rs.len() > 0);
        assert_eq!(self.rs.len() % rw_batch_size, 0); // assumes exact padding
        assert!(rw_batch_size > 0);
        let num_iters = self.rs.len() / rw_batch_size;

        let padding = MemElem::new_u(0, 0, vec![0; self.elem_len], 0);

        let mut priv_cut_off = self.mem_spaces.len() + 1;
        for (i, sp) in self.mem_spaces.iter().enumerate() {
            match sp {
                MemType::PubROM(_) | MemType::PubRAM(_) => {
                    priv_cut_off = i + 1;
                    break;
                }
                _ => {}
            }
        }

        // by address
        let mut vec_fs: Vec<MemElem<F>> = self.fs.clone().into_values().collect();
        self.priv_is
            .sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());
        vec_fs.sort_by(|a, b| a.sr.partial_cmp(&b.sr).unwrap());

        let split = vec_fs
            .iter()
            .position(|f| f.sr >= F::from(priv_cut_off as u64));
        let (priv_fs, pub_fs) = if split.is_some() {
            vec_fs.split_at_mut(split.unwrap())
        } else {
            (vec_fs.as_mut_slice(), &mut [] as &mut [MemElem<F>])
        };

        priv_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());
        //pub_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        assert_eq!(
            priv_fs.len() + pub_fs.len(),
            self.priv_is.len() + self.pub_is.len()
        );

        let mut mem_wits = HashMap::new();
        for elem in &self.pub_is {
            mem_wits.insert(elem.addr, elem.clone());
        }
        for elem in &self.priv_is {
            mem_wits.insert(elem.addr, elem.clone());
        }

        let is_priv_per_batch = ((self.priv_is.len() as f32) / (num_iters as f32)).ceil() as usize;
        let fs_priv_per_batch = ((priv_fs.len() as f32) / (num_iters as f32)).ceil() as usize;

        assert_eq!(is_priv_per_batch, fs_priv_per_batch);

        // cmt
        let key_len = (is_priv_per_batch + fs_priv_per_batch) * (3 + self.elem_len)
            + rw_batch_size * 2 * (3 + self.elem_len);

        let ic_gens = Incremental::<E1, E2>::setup(key_len);

        let (ic_cmt, blinds, ram_hints) = self.ic_to_ram(
            &ic_gens,
            rw_batch_size,
            is_priv_per_batch,
            num_iters,
            sep_final,
            priv_fs,
            &padding,
        );
        //println!("RAM HINTS {:#?}", ram_hints);

        let perm_chal = nova_to_ark_field::<N1, F>(&sample_challenge(&ic_cmt));

        let mut rm = RunningMem {
            priv_is: self.priv_is,
            pub_is: self.pub_is,
            mem_wits,
            priv_fs: priv_fs.to_vec(),
            pub_fs: pub_fs.to_vec(),
            pub_hashes: (F::one(), F::one()),
            ts: F::zero(),
            perm_chal,
            elem_len: self.elem_len,
            scan_per_batch: is_priv_per_batch,
            s: 0,
            stack_spaces: self.stack_spaces,
            mem_spaces: self.mem_spaces,
            priv_cut_off,
            padding,
            dummy_mode: false,
        };

        rm.pub_hashes = rm.get_pub_is_fs_hashes();

        (ic_cmt, blinds, ram_hints, rm)
    }

    // should only be used for testing
    pub(crate) fn get_mem_wits(&self) -> &HashMap<usize, MemElem<F>> {
        &self.mem
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: arkPrimeField> {
    priv_is: Vec<MemElem<F>>,
    pub_is: Vec<MemElem<F>>,
    mem_wits: HashMap<F, MemElem<F>>,
    priv_fs: Vec<MemElem<F>>,
    pub_fs: Vec<MemElem<F>>,
    pub_hashes: (F, F),
    ts: F,
    pub perm_chal: F,
    pub elem_len: usize,
    pub scan_per_batch: usize,
    s: usize, // iter through scan
    // if only ram, empty
    // stacks = [1, stack_1_limit, stack_2_limit, ....]
    stack_spaces: Vec<usize>,
    mem_spaces: Vec<MemType>,
    priv_cut_off: usize,
    padding: MemElem<F>,
    dummy_mode: bool,
}

#[derive(Clone, Debug)]
pub struct RunningMemWires<F: arkPrimeField> {
    // for multiple calls in one CS
    pub cs: ConstraintSystemRef<F>,
    pub running_i: FpVar<F>,
    pub running_is: FpVar<F>,
    pub running_rs: FpVar<F>,
    pub running_ws: FpVar<F>,
    pub running_fs: FpVar<F>,
    pub ts_m1: FpVar<F>,
    pub perm_chal: FpVar<F>,
    pub stack_ptrs: Vec<FpVar<F>>,
}

impl<F: arkPrimeField> RunningMem<F> {
    pub fn get_dummy(&self) -> Self {
        let mut mem_wits = HashMap::new();
        mem_wits.insert(self.padding.addr, self.padding.clone());
        /*self.mem_wits.clone();
        for (_, elem) in mem_wits.iter_mut() {
            *elem = self.padding.clone();
        }*/

        Self {
            priv_is: vec![self.padding.clone(); self.priv_is.len()],
            pub_is: self.pub_is.clone(),
            mem_wits,
            priv_fs: vec![self.padding.clone(); self.priv_fs.len()],
            pub_fs: self.pub_fs.clone(),
            pub_hashes: self.pub_hashes.clone(),
            ts: F::zero(),
            perm_chal: self.perm_chal,
            elem_len: self.elem_len,
            scan_per_batch: self.scan_per_batch,
            s: self.s,
            stack_spaces: self.stack_spaces.clone(),
            mem_spaces: self.mem_spaces.clone(),
            priv_cut_off: self.priv_cut_off,
            padding: self.padding.clone(),
            dummy_mode: true,
        }
    }

    // can be called by prove on real RunningMem or by Verifier on dummy to produce same result
    pub fn get_pub_is_fs_hashes(&self) -> (F, F) {
        let mut pub_is = F::one();
        for elem in &self.pub_is {
            pub_is *= elem.hash(self.perm_chal);
        }

        let mut pub_fs = F::one();
        for elem in &self.pub_fs {
            pub_fs *= elem.hash(self.perm_chal);
        }

        (pub_is, pub_fs)
    }

    pub fn get_starting_stack_ptrs(&self) -> Vec<F> {
        if self.stack_spaces.len() == 0 {
            vec![]
        } else {
            self.stack_spaces[..self.stack_spaces.len() - 1]
                .iter()
                .map(|s| F::from(*s as u64))
                .collect()
        }
    }

    pub fn padding(&self, cs: ConstraintSystemRef<F>) -> Result<MemElemWires<F>, SynthesisError> {
        Ok(MemElemWires::new(
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

    // should only be used for testing
    pub(crate) fn get_mem_wits(&self) -> &HashMap<F, MemElem<F>> {
        &self.mem_wits
    }

    pub fn begin_new_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        running_i: F,
        running_is: F,
        running_rs: F,
        running_ws: F,
        running_fs: F,
        stack_ptrs: &Vec<F>,
    ) -> Result<RunningMemWires<F>, SynthesisError> {
        let running_i = FpVar::new_witness(cs.clone(), || Ok(running_i))?;
        let running_is = FpVar::new_witness(cs.clone(), || Ok(running_is))?;
        let running_rs = FpVar::new_witness(cs.clone(), || Ok(running_rs))?;
        let running_ws = FpVar::new_witness(cs.clone(), || Ok(running_ws))?;
        let running_fs = FpVar::new_witness(cs.clone(), || Ok(running_fs))?;
        let ts_m1 = FpVar::new_witness(cs.clone(), || Ok(self.ts))?;
        let perm_chal = FpVar::new_witness(cs.clone(), || Ok(self.perm_chal))?;
        let stack_ptrs = stack_ptrs
            .iter()
            .map(|sp| FpVar::new_witness(cs.clone(), || Ok(sp)))
            .collect::<Result<Vec<FpVar<F>>, _>>()?;

        Ok(RunningMemWires {
            cs: cs.clone(),
            running_i,
            running_is,
            running_rs,
            running_ws,
            running_fs,
            ts_m1,
            perm_chal,
            stack_ptrs,
        })
    }

    fn inner_conditional_push(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        assert!(self.stack_spaces.len() > 0);
        assert_eq!(w.stack_ptrs.len(), self.stack_spaces.len() - 1);
        assert!(stack_tag < self.stack_spaces.len());

        let res = self.conditional_op(cond, &w.stack_ptrs[stack_tag].clone(), Some(vals), 0, w);

        // sp ++
        let sp = FpVar::new_witness(w.cs.clone(), || {
            Ok(w.stack_ptrs[stack_tag].value()? + F::ONE)
        })?;
        sp.conditional_enforce_equal(&(&w.stack_ptrs[stack_tag] + &FpVar::one()), &cond)?;
        w.stack_ptrs[stack_tag] = cond.select(&sp, &w.stack_ptrs[stack_tag])?;

        // boundry check
        w.stack_ptrs[stack_tag].conditional_enforce_not_equal(
            &FpVar::new_constant(
                w.cs.clone(),
                F::from((self.stack_spaces[stack_tag + 1] + 1) as u64),
            )?,
            cond,
        )?;

        res
    }

    pub fn conditional_push(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_push(cond, stack_tag, vals, w)
    }

    pub fn push(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_push(&Boolean::TRUE, stack_tag, vals, w)
    }

    fn inner_conditional_write(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        let mem_tag = match ty {
            MemType::PrivStack(_) => panic!("cannot write to stack, only push"),
            MemType::PrivROM(_) | MemType::PubROM(_) => panic!("cannot write to ROM"),
            m => self.mem_spaces.iter().position(|r| *r == m).unwrap() + 1,
        };

        self.conditional_op(cond, addr, Some(vals), mem_tag, w)
    }

    pub fn conditional_write(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_write(cond, addr, vals, ty, w)
    }

    pub fn write(
        &mut self,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_write(&Boolean::TRUE, addr, vals, ty, w)
    }

    pub fn conditional_pop(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_pop(cond, stack_tag, w)
    }

    fn inner_conditional_pop(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        assert!(self.stack_spaces.len() > 0);
        assert_eq!(w.stack_ptrs.len(), self.stack_spaces.len() - 1);
        assert!(stack_tag < self.stack_spaces.len());

        // sp --
        let sp = FpVar::new_witness(w.cs.clone(), || {
            Ok(w.stack_ptrs[stack_tag].value()? - F::ONE)
        })?;
        sp.conditional_enforce_equal(&(&w.stack_ptrs[stack_tag] - &FpVar::one()), &cond)?;
        w.stack_ptrs[stack_tag] = cond.select(&sp, &w.stack_ptrs[stack_tag])?;

        let res = self.conditional_op(cond, &w.stack_ptrs[stack_tag].clone(), None, 0, w);

        // boundry check
        w.stack_ptrs[stack_tag].conditional_enforce_not_equal(
            &FpVar::new_constant(
                w.cs.clone(),
                F::from((self.stack_spaces[stack_tag] - 1) as u64),
            )?,
            cond,
        )?;

        res
    }

    pub fn pop(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_pop(&Boolean::TRUE, stack_tag, w)
    }

    fn inner_conditional_read(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        let mem_tag = match ty {
            MemType::PrivStack(_) => panic!("cannot read from stack, only pop"),
            m => self.mem_spaces.iter().position(|r| *r == m).unwrap() + 1,
        };

        self.conditional_op(cond, addr, None, mem_tag, w)
    }

    pub fn conditional_read(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_read(cond, addr, ty, w)
    }

    pub fn read(
        &mut self,
        addr: &FpVar<F>,
        ty: MemType,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.inner_conditional_read(&Boolean::TRUE, addr, ty, w)
    }

    fn conditional_op(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        write_vals: Option<Vec<FpVar<F>>>,
        mem_type: usize,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        // ts = ts + 1
        let ts = FpVar::new_witness(w.cs.clone(), || {
            Ok(if cond.value()? {
                w.ts_m1.value()? + F::one()
            } else {
                w.ts_m1.value()?
            })
        })?;
        ts.conditional_enforce_equal(&(&w.ts_m1 + &FpVar::one()), &cond)?;
        w.ts_m1 = cond.select(&ts, &w.ts_m1)?;
        if cond.value()? {
            self.ts = w.ts_m1.value()?;
        }

        // t < ts hacked in other part of code

        // RS = RS * tup
        let read_wit = if self.dummy_mode {
            &self.padding
        } else {
            let rw = self.mem_wits.get(&addr.value()?).unwrap();
            assert_eq!(rw.addr, addr.value()?);
            rw
        };

        let read_mem_elem = MemElemWires::new(
            FpVar::new_witness(w.cs.clone(), || Ok(read_wit.time))?,
            addr.clone(),
            read_wit
                .vals
                .iter()
                .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                .collect::<Result<Vec<FpVar<F>>, _>>()?,
            FpVar::new_witness(w.cs.clone(), || Ok(read_wit.sr))?,
        );
        let next_running_rs = &w.running_rs * read_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
        w.running_rs = cond.select(&next_running_rs, &w.running_rs)?;

        // memory namespace
        read_mem_elem.sr.conditional_enforce_equal(
            &FpVar::<F>::new_constant(w.cs.clone(), F::from(mem_type as u64))?,
            cond,
        )?;

        let v_prime = if write_vals.is_some() {
            let vals = write_vals.unwrap();
            assert_eq!(vals.len(), self.elem_len);
            vals
        } else {
            read_mem_elem.vals.clone()
        };

        if cond.value()? {
            self.mem_wits.insert(
                addr.value()?,
                MemElem::new_f(
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
        let write_mem_elem = MemElemWires::new(ts, addr.clone(), v_prime, read_mem_elem.sr.clone());
        let next_running_ws = &w.running_ws * write_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
        w.running_ws = cond.select(&next_running_ws, &w.running_ws)?;

        Ok((read_mem_elem, write_mem_elem))
    }

    // call once per step circuit
    pub fn scan(
        &mut self,
        w: &mut RunningMemWires<F>,
        last_round: bool, // is this the last folding?
    ) -> Result<(Vec<MemElemWires<F>>, Vec<MemElemWires<F>>, Boolean<F>), SynthesisError> {
        let mut is_elems = Vec::new();
        let mut fs_elems = Vec::new();

        for _ in 0..self.scan_per_batch {
            let (initial_mem_elem, cond) = if self.s < self.priv_is.len() {
                let is_wit = self.priv_is[self.s].clone();
                (
                    MemElemWires::new(
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

            // t < ts hack
            initial_mem_elem.time.enforce_equal(&FpVar::zero())?;

            // IS check
            let next_running_is =
                &w.running_is * initial_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
            w.running_is = cond.select(&next_running_is, &w.running_is)?;

            let (final_mem_elem, cond) = if self.s < self.priv_fs.len() {
                let fs_wit = self.priv_fs[self.s].clone();
                (
                    MemElemWires::new(
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
            let next_running_fs =
                &w.running_fs * final_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
            w.running_fs = cond.select(&next_running_fs, &w.running_fs)?;

            // a = a' = i
            initial_mem_elem.addr.enforce_equal(&final_mem_elem.addr)?;

            let not_padding = initial_mem_elem.addr.is_neq(&FpVar::zero())?;
            initial_mem_elem
                .addr
                .conditional_enforce_equal(&w.running_i, &not_padding)?;

            // i += 1
            w.running_i = not_padding.select(&(&w.running_i + F::one()), &w.running_i)?;
            self.s += 1;

            fs_elems.push(final_mem_elem);
            is_elems.push(initial_mem_elem);
        }

        // final check
        let last_check = Boolean::new_witness(w.cs.clone(), || Ok(last_round))?;
        &(&w.running_is * &w.running_ws * &FpVar::constant(self.pub_hashes.0))
            .is_eq(&(&w.running_fs * &w.running_rs * &FpVar::constant(self.pub_hashes.1)))?
            .conditional_enforce_equal(&Boolean::TRUE, &last_check)?;

        w.running_is = last_check.select(&FpVar::constant(F::zero()), &w.running_is)?;
        w.running_rs = last_check.select(&FpVar::constant(F::zero()), &w.running_rs)?;
        w.running_ws = last_check.select(&FpVar::constant(F::zero()), &w.running_ws)?;
        w.running_fs = last_check.select(&FpVar::constant(F::zero()), &w.running_fs)?;

        Ok((is_elems, fs_elems, last_check))
    }
}

// deterministic
pub fn sample_challenge(ic_cmts: &Vec<N2>) -> N1 {
    let ro_consts = ROConstants::<E1>::default();
    let mut hasher = <E1 as Engine>::RO::new(ro_consts);
    for c in ic_cmts {
        hasher.absorb(*c);
    }

    scalar_as_base::<E2>(hasher.squeeze(250)) // num hash bits from nova
}

mod tests {
    use crate::bellpepper::*;
    use crate::memory::nebula::*;
    use crate::utils::*;
    use ark_ff::{One, Zero};
    use ark_r1cs_std::{
        alloc::AllocVar, boolean::Boolean, eq::EqGadget, fields::fp::FpVar, GR1CSVar,
    };
    use ark_relations::gr1cs::{
        ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    };
    use ff::Field as novaField;
    use ff::PrimeField as novaPrimeField;
    use nova_snark::{
        nova::{CompressedSNARK, PublicParams, RecursiveSNARK},
        traits::{circuit::TrivialCircuit, snark::default_ck_hint, Engine},
    };

    //bn256, grumpkin
    type A = ark_bn254::Fr;

    type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

    fn make_full_mem_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        do_rw_ops: fn(
            usize,
            &mut RunningMem<A>,
            &mut RunningMemWires<A>,
            &mut Vec<MemElemWires<A>>,
        ),
        running_i: &mut A,
        running_is: &mut A,
        running_rs: &mut A,
        running_ws: &mut A,
        running_fs: &mut A,
        stack_ptrs: &mut Vec<A>,
        last_fold: bool,
    ) -> FCircuit<N1> {
        let cs = ConstraintSystem::<A>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        let mut running_mem_wires = rm
            .begin_new_circuit(
                cs.clone(),
                *running_i,
                *running_is,
                *running_rs,
                *running_ws,
                *running_fs,
                stack_ptrs,
            )
            .unwrap();

        let running_i_prev = running_mem_wires.running_i.clone();
        let running_is_prev = running_mem_wires.running_is.clone();
        let running_rs_prev = running_mem_wires.running_rs.clone();
        let running_ws_prev = running_mem_wires.running_ws.clone();
        let running_fs_prev = running_mem_wires.running_fs.clone();

        let mut rw_mem_ops = Vec::new();

        do_rw_ops(i, rm, &mut running_mem_wires, &mut rw_mem_ops);

        let res = rm.scan(&mut running_mem_wires, last_fold);
        assert!(res.is_ok());
        let (mut next_mem_ops, f, last_check) = res.unwrap();

        /*println!("INIT");
        for mo in &next_mem_ops {
            mo.print_vals();
        }
        println!("RW");
        for mo in &rw_mem_ops {
            mo.print_vals();
        }
        println!("FINAL");
        for mo in &f {
            mo.print_vals();
        }*/

        next_mem_ops.extend(rw_mem_ops);
        next_mem_ops.extend(f);

        // doesn't matter what goes in anymore
        ivcify_stack_op(&next_mem_ops, &next_mem_ops, cs.clone()).unwrap();

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
        let (running_i_in, running_i_out) = FpVar::new_input_output_pair(
            cs.clone(),
            || Ok(running_i_prev.value().unwrap()),
            || Ok(running_mem_wires.running_i.value().unwrap()),
        )
        .unwrap();
        running_i_in.enforce_equal(&running_i_prev).unwrap();
        running_i_out
            .enforce_equal(&running_mem_wires.running_i)
            .unwrap();
        // last
        let (last_in, last_out) = Boolean::new_input_output_pair(
            cs.clone(),
            || Ok(last_check.value().unwrap()),
            || Ok(last_check.value().unwrap()),
        )
        .unwrap();
        // don't need in
        last_out.enforce_equal(&last_check).unwrap();

        // running mem, stack ptrs, etc, needs to be ivcified too, but that doesn't effect our final checks
        // so we omit for now

        *running_i = running_mem_wires.running_i.value().unwrap(); //running_i_out.value().unwrap();
        *running_is = running_is_out.value().unwrap();
        *running_rs = running_rs_out.value().unwrap();
        *running_ws = running_ws_out.value().unwrap();
        *running_fs = running_fs_out.value().unwrap();
        *stack_ptrs = running_mem_wires
            .stack_ptrs
            .iter()
            .map(|f| f.value().unwrap())
            .collect();

        FCircuit::new(cs, None)
    }
    pub fn ivcify_stack_op(
        prev_ops: &Vec<MemElemWires<A>>,
        next_ops: &Vec<MemElemWires<A>>,
        cs: ConstraintSystemRef<A>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(prev_ops.len(), next_ops.len());

        for i in 0..prev_ops.len() {
            //println!("IVC OP");
            //println!("{:#?}", next_ops[i].time.value()?);
            let (time_in, time_out) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].time.value()?),
                || Ok(next_ops[i].time.value()?),
            )?;
            next_ops[i].time.enforce_equal(&time_out)?;

            //println!("{:#?}", next_ops[i].addr.value()?);
            let (addr_in, addr_out) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].addr.value()?),
                || Ok(next_ops[i].addr.value()?),
            )?;
            next_ops[i].addr.enforce_equal(&addr_out)?;

            //println!("{:#?}", next_ops[i].sr.value()?);
            let (sr_in, sr_out) = FpVar::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].sr.value()?),
                || Ok(next_ops[i].sr.value()?),
            )?;
            next_ops[i].sr.enforce_equal(&sr_out)?;

            for j in 0..prev_ops[i].vals.len() {
                //println!("{:#?}", next_ops[i].vals[j].value()?);
                let (val_j_in, val_j_out) = FpVar::new_input_output_pair(
                    cs.clone(),
                    || Ok(prev_ops[i].vals[j].value()?),
                    || Ok(next_ops[i].vals[j].value()?),
                )?;
                next_ops[i].vals[j].enforce_equal(&val_j_out)?;
            }
        }
        Ok(())
    }

    fn run_ram_nova(
        num_iters: usize,
        batch_size: usize,
        mem_builder: MemBuilder<A>,
        do_rw_ops: fn(
            usize,
            &mut RunningMem<A>,
            &mut RunningMemWires<A>,
            &mut Vec<MemElemWires<A>>,
        ),
    ) {
        let (C_final, blinds, ram_hints, mut rm) = mem_builder.new_running_mem(batch_size, false);

        // nova
        let mut running_i = A::one();
        let mut running_is = A::one();
        let mut running_rs = A::one();
        let mut running_ws = A::one();
        let mut running_fs = A::one();
        let mut stack_ptrs = rm.get_starting_stack_ptrs();
        let mut circuit_primary = make_full_mem_circ(
            0,
            &mut rm,
            do_rw_ops,
            &mut running_i,
            &mut running_is,
            &mut running_rs,
            &mut running_ws,
            &mut running_fs,
            &mut stack_ptrs,
            false,
        );

        let z0_primary_full = circuit_primary.get_zi();
        let z0_primary = z0_primary_full
            [(batch_size * 2 * (3 + rm.elem_len) + (rm.scan_per_batch * 2) * (3 + rm.elem_len))..]
            .to_vec();

        // produce public parameters
        let ram_batch_sizes =
            vec![batch_size * 2 * (3 + rm.elem_len) + rm.scan_per_batch * 2 * (3 + rm.elem_len)];
        let pp = PublicParams::<E1, E2, FCircuit<<E1 as Engine>::Scalar>>::setup(
            &mut circuit_primary,
            &*default_ck_hint(),
            &*default_ck_hint(),
            ram_batch_sizes.clone(),
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

            let zi_primary = circuit_primary.get_zi();
            // verify the recursive SNARK
            let res = recursive_snark.verify(&pp, i + 1, &z0_primary);
            assert!(res.is_ok());

            if i < num_iters - 1 {
                circuit_primary = make_full_mem_circ(
                    i + 1,
                    &mut rm,
                    do_rw_ops,
                    &mut running_i,
                    &mut running_is,
                    &mut running_rs,
                    &mut running_ws,
                    &mut running_fs,
                    &mut stack_ptrs,
                    (i == num_iters - 2),
                );
            }
        }

        // produce the prover and verifier keys for compressed snark
        let (pk, vk) = CompressedSNARK::<_, _, _, S1, S2>::setup(&pp).unwrap();

        // produce a compressed SNARK
        let res = CompressedSNARK::<_, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
        assert!(res.is_ok());
        let compressed_snark = res.unwrap();

        // verify the compressed SNARK
        let res = compressed_snark.verify(&vk, num_iters, &z0_primary);
        assert!(res.is_ok());

        // check final cmt outputs
        let (zn, Ci) = res.unwrap();

        let (pub_is, pub_fs) = rm.get_pub_is_fs_hashes();
        assert_eq!(pub_is, rm.pub_hashes.0);
        assert_eq!(pub_fs, rm.pub_hashes.1);

        println!("Z {:#?}", zn);
        // is * ws == rs * fs (verifier)
        assert_eq!(zn[5], N1::from(1));

        // incr cmt = acc cmt (verifier)
        for i in 0..C_final.len() {
            //    println!("{}", i);
            assert_eq!(C_final[i], Ci[i]);
        }
    }

    #[test]
    fn two_stacks() {
        let mut mb = MemBuilder::new(2, vec![3, 2], vec![]);
        // stack 0
        mb.init(1, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        mb.init(2, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        mb.init(3, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        // stack 1
        mb.init(4, vec![A::from(0), A::from(0)], MemType::PrivStack(1));
        mb.init(5, vec![A::from(0), A::from(0)], MemType::PrivStack(1));
        // ram

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
        run_ram_nova(2, 3, mb, two_stacks_circ);
    }

    fn two_stacks_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
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

        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.pop(1, rmw);

        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.push(
            0,
            push_vals_2
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );

        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
    }

    #[test]
    fn stack_ends_empty() {
        let mut mb = MemBuilder::new(2, vec![3], vec![MemType::PrivRAM(0)]);
        // stack
        mb.init(1, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        mb.init(2, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        mb.init(3, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
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

        run_ram_nova(2, 4, mb, stack_ends_empty_circ);
    }

    fn stack_ends_empty_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.push(
            0,
            push_vals_2
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.pop(0, rmw);
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.pop(0, rmw);
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
    }

    #[test]
    fn stack_basic() {
        let mut mb = MemBuilder::new(2, vec![3], vec![MemType::PrivRAM(0)]);
        // stack
        mb.init(1, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        mb.init(2, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        mb.init(3, vec![A::from(0), A::from(0)], MemType::PrivStack(0));
        // ram
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PrivRAM(0));

        mb.push(0, vec![A::from(1), A::from(2)]);
        mb.push(0, vec![A::from(3), A::from(4)]);
        assert_eq!(mb.pop(0), vec![A::from(3), A::from(4)]);

        mb.push(0, vec![A::from(5), A::from(6)]);
        mb.push(0, vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(0), vec![A::from(7), A::from(8)]);

        run_ram_nova(2, 3, mb, stack_basic_circ);
    }

    fn stack_basic_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.push(
            0,
            push_vals_2
                .iter()
                .map(|v| FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(*v as u64))).unwrap())
                .collect(),
            rmw,
        );
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

        let res = rm.pop(0, rmw);
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
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

        run_ram_nova(2, 1, mb, mem_cond_simple_circ);
    }

    fn mem_cond_simple_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
        let (cond_value, read_addr) = (true, 1);

        let cond = Boolean::new_witness(rmw.cs.clone(), || Ok(cond_value)).unwrap();

        let res = rm.read(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr as u64))).unwrap(),
            MemType::PrivRAM(0),
            rmw,
        );
        assert!(res.is_ok());
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
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
        mb.cond_read(false, 1, MemType::PrivRAM(0));
        mb.cond_write(
            false,
            2,
            vec![A::from(18), A::from(19)],
            MemType::PrivRAM(0),
        );

        assert_eq!(
            mb.cond_read(true, 3, MemType::PrivRAM(0)),
            vec![A::from(14), A::from(15)]
        );
        mb.cond_write(true, 4, vec![A::from(20), A::from(21)], MemType::PrivRAM(0));

        run_ram_nova(3, 2, mb, mem_conditional_circ);
    }

    fn mem_conditional_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
        let (cond_value, read_addr, write_addr, write_vals) = if i == 0 {
            (true, 1, 2, vec![18, 19])
        } else if i == 1 {
            (false, 1, 2, vec![18, 19])
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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
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

        run_ram_nova(2, 2, mb, mem_basic_circ);
    }

    #[test]
    fn mem_pub_ROM() {
        let mut mb = MemBuilder::new(2, vec![], vec![MemType::PrivRAM(0), MemType::PubRAM(0)]);
        mb.init(1, vec![A::from(10), A::from(11)], MemType::PrivRAM(0));
        mb.init(2, vec![A::from(12), A::from(13)], MemType::PrivRAM(0));
        mb.init(3, vec![A::from(14), A::from(15)], MemType::PubRAM(0));
        mb.init(4, vec![A::from(16), A::from(17)], MemType::PubRAM(0));

        assert_eq!(
            mb.read(3, MemType::PubRAM(0)),
            vec![A::from(14), A::from(15)]
        );
        mb.write(1, vec![A::from(18), A::from(19)], MemType::PrivRAM(0));

        assert_eq!(
            mb.read(4, MemType::PubRAM(0)),
            vec![A::from(16), A::from(17)]
        );
        mb.write(2, vec![A::from(20), A::from(21)], MemType::PrivRAM(0));

        run_ram_nova(2, 2, mb, mem_pub_ROM_circ);
    }

    fn mem_pub_ROM_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
        let (read_addr, write_addr, write_vals) = if i == 0 {
            (3, 1, vec![18, 19])
        } else if i == 1 {
            (4, 2, vec![20, 21])
        } else {
            panic!()
        };

        let res = rm.read(
            &FpVar::new_witness(rmw.cs.clone(), || Ok(A::from(read_addr as u64))).unwrap(),
            MemType::PubRAM(0),
            rmw,
        );
        assert!(res.is_ok());
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
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

        run_ram_nova(2, 2, mb, mem_basic_circ);
    }

    fn mem_basic_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);

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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
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

        run_ram_nova(2, 1, mb, mem_bigger_init_circ);
    }

    fn mem_bigger_init_circ(
        i: usize,
        rm: &mut RunningMem<A>,
        rmw: &mut RunningMemWires<A>,
        rw_mem_ops: &mut Vec<MemElemWires<A>>,
    ) {
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
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
    }
}
