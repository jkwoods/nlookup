use crate::bellpepper::{ark_to_nova_field, nova_to_ark_field};
use crate::utils::*;
use ark_ff::PrimeField;
use ark_ff::PrimeField as arkPrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};
use ark_std::test_rng;
use nova_snark::{
    provider::incremental::Incremental,
    traits::{Engine, ROConstants, ROTrait},
};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub struct MemElem<F: PrimeField> {
    pub time: F,
    pub addr: F,
    pub vals: Vec<F>,
    pub sr: bool, //stack=1  or ram=0
}

impl<F: PrimeField> MemElem<F> {
    pub fn new_u(t: usize, a: usize, v: Vec<usize>, sr: bool) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(a as u64),
            vals: v.into_iter().map(|x| F::from(x as u64)).collect(),
            sr: sr,
        }
    }

    pub fn new_f(t: F, a: F, v: Vec<F>, sr: bool) -> Self {
        MemElem {
            time: t,
            addr: a,
            vals: v,
            sr: sr,
        }
    }

    pub fn new_single(t: usize, a: usize, v: usize, sr: bool) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(a as u64),
            vals: vec![F::from(v as u64)],
            sr,
        }
    }

    pub fn get_vec(&self) -> Vec<F> {
        let mut v = vec![
            self.time,
            self.addr,
            if self.sr { F::one() } else { F::zero() },
        ];
        v.extend(self.vals.clone());

        v
    }
}

#[derive(Clone, Debug)]
pub struct MemElemWires<F: PrimeField> {
    pub time: FpVar<F>,
    pub addr: FpVar<F>,
    pub vals: Vec<FpVar<F>>,
    pub sr: Boolean<F>,
}

impl<F: PrimeField> MemElemWires<F> {
    pub fn new(t: FpVar<F>, a: FpVar<F>, v: Vec<FpVar<F>>, sr: Boolean<F>) -> Self {
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
        println!(
            "MemElem [{:#?} [time {:#?}] [addr {:#?}] [vals {:#?}]]",
            if self.sr.value().unwrap() {
                "STACK"
            } else {
                "RAM"
            },
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
        let mut hash = (perm_chal - &self.time)
            * (perm_chal - &self.addr)
            * (perm_chal - FpVar::from(self.sr.clone()));

        for i in 0..self.vals.len() {
            hash = hash * (perm_chal - &self.vals[i]);
        }

        Ok(hash)
    }
}

// builds the witness for RunningMem
#[derive(Debug)]
pub struct MemBuilder<F: PrimeField> {
    mem: HashMap<usize, MemElem<F>>,
    is: Vec<MemElem<F>>,
    rs: Vec<MemElem<F>>,
    ws: Vec<MemElem<F>>,
    fs: HashMap<usize, MemElem<F>>,
    stack_spaces: Vec<usize>,
    stack_ptrs: Vec<usize>,
    elem_len: usize,
    ts: usize,
}

impl<F: PrimeField> MemBuilder<F> {
    pub fn new(elem_len: usize, stack_sizes: Vec<usize>) -> Self {
        assert!(elem_len > 0);

        let mut stack_spaces = Vec::new();
        let mut stack_ptrs = Vec::new();

        if stack_sizes.len() > 0 {
            stack_spaces.push(1);
            let mut stack_limit = 1;

            for s in stack_sizes {
                stack_ptrs.push(stack_limit);
                stack_limit += s;
                stack_spaces.push(stack_limit);
            }
        }

        Self {
            mem: HashMap::new(),
            is: Vec::new(),
            rs: Vec::new(),
            ws: Vec::new(),
            fs: HashMap::new(),
            stack_spaces,
            stack_ptrs,
            elem_len,
            ts: 0,
        }
    }

    pub fn pad(&mut self) {
        let padding = MemElem::new_u(0, 0, vec![0; self.elem_len], false);

        self.rs.push(padding.clone());
        self.ws.push(padding);
    }

    pub fn push(&mut self, stack_tag: usize, vals: Vec<F>) {
        self.write(self.stack_ptrs[stack_tag], vals, true);

        self.stack_ptrs[stack_tag] += 1;

        assert!(self.stack_ptrs[stack_tag] < self.stack_spaces[stack_tag + 1]);
    }

    pub fn pop(&mut self, stack_tag: usize) -> Vec<F> {
        self.stack_ptrs[stack_tag] -= 1;

        assert!(self.stack_ptrs[stack_tag] >= self.stack_spaces[stack_tag]);

        self.read(self.stack_ptrs[stack_tag], true)
    }

    pub fn read(&mut self, addr: usize, is_stack: bool) -> Vec<F> {
        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(&addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, F::from(addr as u64));
        self.rs.push(read_elem.clone());

        self.ts += 1;

        let write_elem = MemElem::new_f(
            F::from(self.ts as u64),
            F::from(addr as u64),
            read_elem.vals.clone(),
            is_stack,
        );
        self.ws.push(write_elem.clone());
        self.fs.insert(addr, write_elem);

        read_elem.vals.clone()
    }

    // initialize memory
    // note: if you plan on writing to an addr, it must be initialized
    pub fn init(&mut self, addr: usize, vals: Vec<F>, stack_tag: Option<usize>) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert_ne!(addr, 0);
        if stack_tag.is_some() {
            assert!(vals.iter().all(|v| *v == F::ZERO));
            assert!(addr < self.stack_spaces[stack_tag.unwrap() + 1]);
            assert!(addr >= self.stack_spaces[stack_tag.unwrap()]);
        }

        let elem = MemElem::new_f(F::ZERO, F::from(addr as u64), vals, stack_tag.is_some());
        self.mem.insert(addr, elem.clone());
        self.is.push(elem.clone());
        self.fs.insert(addr, elem);
    }

    pub fn write(&mut self, addr: usize, vals: Vec<F>, is_stack: bool) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert_ne!(addr, 0);

        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(&addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, F::from(addr as u64));
        self.rs.push(read_elem.clone());
        self.ts += 1;

        let write_elem = MemElem::new_f(F::from(self.ts as u64), read_elem.addr, vals, is_stack);
        self.mem.insert(addr, write_elem.clone());
        self.ws.push(write_elem.clone());
        self.fs.insert(addr, write_elem);
    }

    fn ic_to_ram(
        &self,
        ic_gen: &Vec<Incremental<E1, E2>>,
        rw_batch_size: usize,
        if_batch_size: usize,
        num_iters: usize,
        sep_final: bool, // true -> cmts/ivcify =  [is], [rs, ws], [fs]
        // false -> cmts/ivcify = [is], [rs, ws, fs]
        fs: &Vec<MemElem<F>>,
    ) -> (Vec<N2>, Vec<Vec<N1>>, Vec<Vec<N1>>) {
        println!("if batch size {}", if_batch_size);
        assert!((sep_final && ic_gen.len() == 3) || (!sep_final && ic_gen.len() == 2));

        let mut ci: Vec<Option<N2>> = vec![None; ic_gen.len()];
        let mut blinds: Vec<Vec<N1>> = vec![Vec::new(); num_iters];
        let mut ram_hints = Vec::new();

        println!(
            "ic to ram: IS {:#?} RS {:#?} WS {:#?} FS {:#?}",
            self.is, self.rs, self.ws, fs
        );

        for i in 0..num_iters {
            let mut is_hint = Vec::new();
            let mut rs_ws_hint = Vec::new();
            let mut fs_hint = Vec::new();
            //let mut wits: Vec<Vec<N1>> = vec![Vec::new(); ic_gen.len()];
            for (im, fm) in self.is[(i * if_batch_size)..(i * if_batch_size + if_batch_size)]
                .iter()
                .zip(fs[(i * if_batch_size)..(i * if_batch_size + if_batch_size)].iter())
            {
                let nova_im: Vec<N1> = im
                    .get_vec()
                    .iter()
                    .map(|a| ark_to_nova_field::<F, N1>(a))
                    .collect();
                let nova_fm: Vec<N1> = fm
                    .get_vec()
                    .iter()
                    .map(|a| ark_to_nova_field::<F, N1>(a))
                    .collect();

                is_hint.extend(nova_im);
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

            println!(
                "is len {}, rs ws len {}, fs len {}",
                is_hint.len(),
                rs_ws_hint.len(),
                fs_hint.len()
            );
            let mut ordered_hints = is_hint;
            ordered_hints.extend(rs_ws_hint);
            ordered_hints.extend(fs_hint);

            let ifb = if_batch_size * (3 + self.elem_len);
            let rwb = rw_batch_size * (3 + self.elem_len);
            println!("ifb {}, rwb {}", ifb, rwb);

            let hint_ranges = if sep_final {
                vec![
                    0..ifb,
                    ifb..(ifb + rwb * 2),
                    (ifb + rwb * 2)..(ifb * 2 + rwb * 2),
                ]
            } else {
                vec![0..ifb, ifb..(ifb * 2 + rwb * 2)]
            };
            print!(
                "ordered_hints len {}, ranges {:#?}",
                ordered_hints.len(),
                hint_ranges
            );

            for (j, range) in hint_ranges.into_iter().enumerate() {
                let (hash, blind) = ic_gen[j].commit(ci[j], &ordered_hints[range]);
                ci[j] = Some(hash);

                blinds[i].push(blind);
            }
            println!("ordered hints {} {:#?}", i, ordered_hints.clone());
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
                         // false -> cmts/ivcify = [is], [rs, ws, fs]
    ) -> (
        Vec<Incremental<E1, E2>>,
        Vec<N2>,
        Vec<Vec<N1>>,
        Vec<Vec<N1>>,
        RunningMem<F>,
    ) {
        assert_eq!(self.rs.len(), self.ws.len());
        assert!(self.rs.len() > 0);
        assert_eq!(self.rs.len() % rw_batch_size, 0); // assumes exact padding
        assert!(rw_batch_size > 0);
        let num_iters = self.rs.len() / rw_batch_size;
        println!("num iters {}", num_iters);

        // by address
        let mut vec_fs: Vec<MemElem<F>> = self.fs.clone().into_values().collect();
        vec_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        self.is.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        let mut mem_wits = HashMap::new();
        for elem in &self.is {
            mem_wits.insert(elem.addr, elem.clone());
        }
        assert_eq!(vec_fs.len(), self.is.len());

        let scan_per_batch = ((self.is.len() as f32) / (num_iters as f32)).ceil() as usize;
        println!("scan per batch {}", scan_per_batch);

        let padding = MemElem::new_u(0, 0, vec![0; self.elem_len], false);

        // cmt
        let mut big_gens = Incremental::<E1, E2>::setup(
            b"ramcmt",
            scan_per_batch * 2 * (3 + self.elem_len) + rw_batch_size * 2 * (3 + self.elem_len),
        );
        let (is_gens, big_gens) = big_gens.split_at(scan_per_batch * (3 + self.elem_len));

        let mut ic_gens = vec![is_gens];

        if sep_final {
            let (rw_gens, big_gens) = big_gens.split_at(rw_batch_size * 2 * (3 + self.elem_len));
            ic_gens.push(rw_gens);
            ic_gens.push(big_gens);
        } else {
            ic_gens.push(big_gens);
        }

        let (ic_cmt, blinds, ram_hints) = self.ic_to_ram(
            &ic_gens,
            rw_batch_size,
            scan_per_batch,
            num_iters,
            sep_final,
            &vec_fs,
        );

        println!("RAM HINTS {:#?}", ram_hints.clone());

        let perm_chal = nova_to_ark_field::<N1, F>(&sample_challenge(&ic_cmt));
        println!("scan per batch {}", scan_per_batch);

        (
            ic_gens,
            ic_cmt,
            blinds,
            ram_hints,
            RunningMem {
                is: self.is,
                mem_wits,
                fs: vec_fs,
                ts: F::zero(),
                i: 0,
                perm_chal,
                elem_len: self.elem_len,
                scan_per_batch,
                stack_spaces: self.stack_spaces,
                padding,
            },
        )
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: PrimeField> {
    is: Vec<MemElem<F>>,
    mem_wits: HashMap<F, MemElem<F>>,
    fs: Vec<MemElem<F>>,
    ts: F,
    i: usize, // for is/fs
    perm_chal: F,
    elem_len: usize,
    pub scan_per_batch: usize,
    // if only ram, empty
    // stacks = [1, stack_1_limit, stack_2_limit, ....]
    stack_spaces: Vec<usize>,
    padding: MemElem<F>,
}

#[derive(Clone, Debug)]
pub struct RunningMemWires<F: PrimeField> {
    // for multiple calls in one CS
    cs: ConstraintSystemRef<F>,
    pub running_is: FpVar<F>,
    pub running_rs: FpVar<F>,
    pub running_ws: FpVar<F>,
    pub running_fs: FpVar<F>,
    pub ts_m1: FpVar<F>,
    pub perm_chal: FpVar<F>,
    pub stack_ptrs: Vec<FpVar<F>>,
}

impl<F: PrimeField> RunningMem<F> {
    pub fn get_dummy(&self) -> Self {
        let mut mem_wits = self.mem_wits.clone();
        for (_, elem) in mem_wits.iter_mut() {
            *elem = self.padding.clone();
        }

        Self {
            is: vec![self.padding.clone(); self.is.len()],
            mem_wits,
            fs: vec![self.padding.clone(); self.fs.len()],
            ts: F::zero(),
            i: 0,
            perm_chal: self.perm_chal,
            elem_len: self.elem_len,
            scan_per_batch: self.scan_per_batch,
            stack_spaces: self.stack_spaces.clone(),
            padding: self.padding.clone(),
        }
    }

    pub fn begin_new_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        running_is: F,
        running_rs: F,
        running_ws: F,
        running_fs: F,
        stack_ptrs: Vec<F>,
    ) -> Result<RunningMemWires<F>, SynthesisError> {
        let running_is = FpVar::new_witness(cs.clone(), || Ok(running_is))?;
        let running_rs = FpVar::new_witness(cs.clone(), || Ok(running_rs))?;
        let running_ws = FpVar::new_witness(cs.clone(), || Ok(running_ws))?;
        let running_fs = FpVar::new_witness(cs.clone(), || Ok(running_fs))?;
        let ts_m1 = FpVar::new_witness(cs.clone(), || Ok(self.ts))?;
        let perm_chal = FpVar::new_constant(cs.clone(), self.perm_chal)?;
        let stack_ptrs = stack_ptrs
            .iter()
            .map(|sp| FpVar::new_witness(cs.clone(), || Ok(sp)))
            .collect::<Result<Vec<FpVar<F>>, _>>()?;

        Ok(RunningMemWires {
            cs: cs.clone(),
            running_is,
            running_rs,
            running_ws,
            running_fs,
            ts_m1,
            perm_chal,
            stack_ptrs,
        })
    }

    pub fn conditional_push(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        assert!(self.stack_spaces.len() > 0);
        assert_eq!(w.stack_ptrs.len(), self.stack_spaces.len() + 1);
        assert!(stack_tag < self.stack_spaces.len());

        let res = self.conditional_op(cond, &w.stack_ptrs[stack_tag].clone(), Some(vals), true, w);

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
                F::from((self.stack_spaces[stack_tag + 1]) as u64),
            )?,
            cond,
        )?;

        res
    }

    pub fn push(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_push(&Boolean::TRUE, stack_tag, vals, w)
    }

    pub fn conditional_write(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_op(cond, addr, Some(vals), false, w)
    }

    pub fn write(
        &mut self,
        addr: &FpVar<F>,
        vals: Vec<FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_write(&Boolean::TRUE, addr, vals, w)
    }

    pub fn conditional_pop(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        assert!(self.stack_spaces.len() > 0);
        assert_eq!(w.stack_ptrs.len(), self.stack_spaces.len() + 1);
        assert!(stack_tag < self.stack_spaces.len());

        // sp --
        let sp = FpVar::new_witness(w.cs.clone(), || {
            Ok(w.stack_ptrs[stack_tag].value()? - F::ONE)
        })?;
        sp.conditional_enforce_equal(&(&w.stack_ptrs[stack_tag] - &FpVar::one()), &cond)?;
        w.stack_ptrs[stack_tag] = cond.select(&sp, &w.stack_ptrs[stack_tag])?;

        let res = self.conditional_op(cond, &w.stack_ptrs[stack_tag].clone(), None, true, w);

        // boundry check
        w.stack_ptrs[stack_tag].conditional_enforce_not_equal(
            &FpVar::new_constant(w.cs.clone(), F::from(self.stack_spaces[stack_tag] as u64))?,
            cond,
        )?;

        res
    }

    pub fn pop(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_pop(&Boolean::TRUE, stack_tag, w)
    }

    pub fn conditional_read(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_op(cond, addr, None, false, w)
    }

    pub fn read(
        &mut self,
        addr: &FpVar<F>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_read(&Boolean::TRUE, addr, w)
    }

    fn conditional_op(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        write_vals: Option<Vec<FpVar<F>>>,
        is_stack: bool,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        // ts = ts + 1
        let ts = FpVar::new_witness(w.cs.clone(), || Ok((&w.ts_m1 + &FpVar::one()).value()?))?;
        ts.conditional_enforce_equal(&(&w.ts_m1 + &FpVar::one()), &cond)?;
        w.ts_m1 = cond.select(&ts, &w.ts_m1)?;
        self.ts = w.ts_m1.value()?;

        // t < ts hack

        // RS = RS * tup
        let read_wit = self.mem_wits.get(&addr.value()?).unwrap();
        assert_eq!(read_wit.addr, addr.value()?);
        //println!("READ WIT");

        let read_mem_elem = MemElemWires::new(
            FpVar::new_witness(w.cs.clone(), || Ok(read_wit.time))?,
            addr.clone(),
            read_wit
                .vals
                .iter()
                .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                .collect::<Result<Vec<FpVar<F>>, _>>()?,
            Boolean::new_witness(w.cs.clone(), || Ok(is_stack))?,
        );
        let next_running_rs = &w.running_rs * read_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
        w.running_rs = cond.select(&next_running_rs, &w.running_rs)?;

        //read_mem_elem.print_vals();

        // stack or ram
        read_mem_elem.sr.conditional_enforce_equal(
            &Boolean::<F>::new_constant(w.cs.clone(), is_stack)?,
            cond,
        )?;

        let v_prime = if write_vals.is_some() {
            let vals = write_vals.unwrap();
            assert_eq!(vals.len(), self.elem_len);
            vals
        } else {
            read_mem_elem.vals.clone()
        };

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

        // WS = WS * tup
        let write_mem_elem = MemElemWires::new(ts, addr.clone(), v_prime, read_mem_elem.sr.clone());
        let next_running_ws = &w.running_ws * write_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
        w.running_ws = cond.select(&next_running_ws, &w.running_ws)?;

        //println!("WRITE WIT");
        //write_mem_elem.print_vals();

        Ok((read_mem_elem, write_mem_elem))
    }

    // call once per step circuit
    pub fn scan(
        &mut self,
        w: &mut RunningMemWires<F>,
    ) -> Result<(Vec<MemElemWires<F>>, Vec<MemElemWires<F>>), SynthesisError> {
        let mut is_elems = Vec::new();
        let mut fs_elems = Vec::new();

        for _ in 0..self.scan_per_batch {
            let (initial_mem_elem, final_mem_elem, cond) = if self.i < self.is.len() {
                let is_wit = self.is[self.i].clone();
                let fs_wit = self.fs[self.i].clone();

                (
                    MemElemWires::new(
                        FpVar::new_witness(w.cs.clone(), || Ok(is_wit.time))?,
                        FpVar::new_witness(w.cs.clone(), || Ok(fs_wit.addr))?,
                        is_wit
                            .vals
                            .iter()
                            .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                            .collect::<Result<Vec<FpVar<F>>, _>>()?,
                        Boolean::new_witness(w.cs.clone(), || Ok(is_wit.sr))?,
                    ),
                    MemElemWires::new(
                        FpVar::new_witness(w.cs.clone(), || Ok(fs_wit.time))?,
                        FpVar::new_witness(w.cs.clone(), || Ok(fs_wit.addr))?,
                        fs_wit
                            .vals
                            .iter()
                            .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                            .collect::<Result<Vec<FpVar<F>>, _>>()?,
                        Boolean::new_witness(w.cs.clone(), || Ok(fs_wit.sr))?,
                    ),
                    Boolean::<F>::new_witness(w.cs.clone(), || Ok(true))?,
                )
            } else {
                let padding_wires = MemElemWires::new(
                    FpVar::new_witness(w.cs.clone(), || Ok(self.padding.time))?,
                    FpVar::new_witness(w.cs.clone(), || Ok(self.padding.addr))?,
                    self.padding
                        .vals
                        .iter()
                        .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                        .collect::<Result<Vec<FpVar<F>>, _>>()?,
                    Boolean::new_witness(w.cs.clone(), || Ok(self.padding.sr))?,
                );

                (
                    padding_wires.clone(),
                    padding_wires,
                    Boolean::<F>::new_witness(w.cs.clone(), || Ok(false))?,
                )
            };

            // t < ts hack
            initial_mem_elem.time.enforce_equal(&FpVar::zero())?;

            // IS check
            let next_running_is =
                &w.running_is * initial_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
            w.running_is = cond.select(&next_running_is, &w.running_is)?;

            // FS check
            let next_running_fs =
                &w.running_fs * final_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
            w.running_fs = cond.select(&next_running_fs, &w.running_fs)?;

            // is_a = fs_a = i ?

            self.i += 1;

            is_elems.push(initial_mem_elem);
            fs_elems.push(final_mem_elem);
        }

        Ok((is_elems, fs_elems))
    }
}

// deterministic
pub fn sample_challenge(ic_cmts: &Vec<N2>) -> N1 {
    let ro_consts = ROConstants::<E1>::default();
    let mut hasher = <E1 as Engine>::RO::new(ro_consts, ic_cmts.len());
    for c in ic_cmts {
        hasher.absorb(*c);
    }

    hasher.squeeze(250) // num hash bits from nova
}

mod tests {
    use crate::bellpepper::*;
    use crate::memory::nebula::*;
    use crate::utils::*;
    use ark_ff::{One, Zero};
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
        //        batch_size: usize, 2
        i: usize,
        rm: &mut RunningMem<A>,
        do_rw_ops: fn(
            usize,
            &mut RunningMem<A>,
            &mut RunningMemWires<A>,
            &mut Vec<MemElemWires<A>>,
        ),
        running_is: &mut A,
        running_rs: &mut A,
        running_ws: &mut A,
        running_fs: &mut A,
    ) -> FCircuit<N1> {
        let cs = ConstraintSystem::<A>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        // ram (we omit stack ptrs for this example)
        let mut running_mem_wires = rm
            .begin_new_circuit(
                cs.clone(),
                *running_is,
                *running_rs,
                *running_ws,
                *running_fs,
                vec![],
            )
            .unwrap();
        let running_is_prev = running_mem_wires.running_is.clone();
        let running_rs_prev = running_mem_wires.running_rs.clone();
        let running_ws_prev = running_mem_wires.running_ws.clone();
        let running_fs_prev = running_mem_wires.running_fs.clone();

        let mut rw_mem_ops = Vec::new();

        do_rw_ops(i, rm, &mut running_mem_wires, &mut rw_mem_ops);

        let res = rm.scan(&mut running_mem_wires);
        assert!(res.is_ok());
        let (mut next_mem_ops, f) = res.unwrap();

        for mo in &rw_mem_ops {
            mo.print_vals();
        }
        println!("INIT");
        for mo in &next_mem_ops {
            mo.print_vals();
        }
        println!("FINAL");
        for mo in &f {
            mo.print_vals();
        }

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

        // running mem needs to be ivcified too, but that doesn't effect our final checks
        // so we omit for now

        *running_is = running_is_out.value().unwrap();
        *running_rs = running_rs_out.value().unwrap();
        *running_ws = running_ws_out.value().unwrap();
        *running_fs = running_fs_out.value().unwrap();
        FCircuit::new(cs)
    }
    pub fn ivcify_stack_op(
        prev_ops: &Vec<MemElemWires<A>>,
        next_ops: &Vec<MemElemWires<A>>,
        cs: ConstraintSystemRef<A>,
    ) -> Result<(), SynthesisError> {
        assert_eq!(prev_ops.len(), next_ops.len());

        for i in 0..prev_ops.len() {
            println!(
                "next in ivc {:#?}, {:#?}",
                next_ops[i].time.value()?,
                next_ops[i].addr.value()?
            );

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

            println!("{:#?}", next_ops[i].sr.value()?);
            let (sr_in, sr_out) = Boolean::new_input_output_pair(
                cs.clone(),
                || Ok(prev_ops[i].sr.value()?),
                || Ok(next_ops[i].sr.value()?),
            )?;
            //prev_ops[i].sr.enforce_equal(&sr_in)?;
            next_ops[i].sr.enforce_equal(&sr_out)?;

            for j in 0..prev_ops[i].vals.len() {
                println!("{:#?}", next_ops[i].vals[j].value()?);
                let (val_j_in, val_j_out) = FpVar::new_input_output_pair(
                    cs.clone(),
                    || Ok(prev_ops[i].vals[j].value()?),
                    || Ok(next_ops[i].vals[j].value()?),
                )?;
                //    prev_ops[i].vals[j].enforce_equal(&val_j_in)?;
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
        let (ic_gens, C_final, blinds, ram_hints, mut rm) =
            mem_builder.new_running_mem(batch_size, false);

        // nova
        let circuit_secondary = TrivialCircuit::default();
        let mut running_is = A::one();
        let mut running_rs = A::one();
        let mut running_ws = A::one();
        let mut running_fs = A::one();
        let mut circuit_primary = make_full_mem_circ(
            0,
            &mut rm,
            do_rw_ops,
            &mut running_is,
            &mut running_rs,
            &mut running_ws,
            &mut running_fs,
        );

        let z0_primary_full = circuit_primary.get_zi();
        let z0_primary = z0_primary_full
            [(batch_size * 2 * (3 + rm.elem_len) + rm.scan_per_batch * 2 * (3 + rm.elem_len))..]
            .to_vec();

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
            //rm.scan_per_batch * (3 + rm.elem_len),
            vec![
                rm.scan_per_batch * (3 + rm.elem_len),
                batch_size * 2 * (3 + rm.elem_len) + rm.scan_per_batch * (3 + rm.elem_len),
            ],
            &[&ic_gens[0].ped_gen, &ic_gens[1].ped_gen],
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
            Some(blinds[0].clone()),
            ram_hints[0].clone(),
        )
        .unwrap();

        for i in 0..num_iters {
            println!("==============================================");
            let res = recursive_snark.prove_step(
                &pp,
                &circuit_primary,
                &circuit_secondary,
                Some(blinds[i].clone()),
                ram_hints[i].clone(),
            );
            assert!(res.is_ok());
            res.unwrap();

            let zi_primary = circuit_primary.get_zi();
            // verify the recursive SNARK
            let res =
                recursive_snark.verify(&pp, i + 1, &z0_primary, &[<E2 as Engine>::Scalar::ZERO]);
            assert!(res.is_ok());

            if i < num_iters - 1 {
                circuit_primary = make_full_mem_circ(
                    i + 1,
                    &mut rm,
                    do_rw_ops,
                    &mut running_is,
                    &mut running_rs,
                    &mut running_ws,
                    &mut running_fs,
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
            compressed_snark.verify(&vk, num_iters, &z0_primary, &[<E2 as Engine>::Scalar::ZERO]);
        assert!(res.is_ok());

        // check final cmt outputs
        let (zn, _) = res.unwrap();

        // is * ws == rs * fs (verifier)
        assert_eq!(zn[0] * zn[2], zn[1] * zn[3]);

        // incr cmt = acc cmt (verifier)
        for i in 0..C_final.len() {
            println!("{}", i);
            assert_eq!(C_final[i], compressed_snark.Ci[i]);
        }
    }

    #[test]
    fn stack_basic() {
        let mut mb = MemBuilder::new(2, vec![3]);
        // stack
        mb.init(1, vec![A::from(0), A::from(0)], Some(0));
        mb.init(2, vec![A::from(0), A::from(0)], Some(0));
        mb.init(3, vec![A::from(0), A::from(0)], Some(0));
        // ram
        mb.init(4, vec![A::from(16), A::from(17)], None);

        mb.push(0, vec![A::from(1), A::from(2)]);
        mb.push(0, vec![A::from(3), A::from(4)]);
        assert_eq!(mb.pop(0), vec![A::from(3), A::from(4)]);

        mb.push(0, vec![A::from(5), A::from(6)]);
        mb.push(0, vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(0), vec![A::from(7), A::from(8)]);
        assert_eq!(mb.pop(0), vec![A::from(5), A::from(6)]);
        assert_eq!(mb.pop(0), vec![A::from(1), A::from(2)]);

        run_ram_nova(2, 2, mb, stack_basic_circ);
    }

    fn stack_basic_circ(
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
            rmw,
        );
        assert!(res.is_ok());
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
    }

    #[test]
    fn mem_basic() {
        let mut mb = MemBuilder::new(2, vec![]);
        mb.init(1, vec![A::from(10), A::from(11)], None);
        mb.init(2, vec![A::from(12), A::from(13)], None);
        mb.init(3, vec![A::from(14), A::from(15)], None);
        mb.init(4, vec![A::from(16), A::from(17)], None);

        assert_eq!(mb.read(1, false), vec![A::from(10), A::from(11)]);
        mb.write(2, vec![A::from(18), A::from(19)], false);

        assert_eq!(mb.read(3, false), vec![A::from(14), A::from(15)]);
        mb.write(4, vec![A::from(20), A::from(21)], false);

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
            rmw,
        );
        assert!(res.is_ok());
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
    }

    #[test]
    fn mem_bigger_init() {
        let mut mb = MemBuilder::new(2, vec![]);
        mb.init(1, vec![A::from(10), A::from(11)], None);
        mb.init(2, vec![A::from(12), A::from(13)], None);
        mb.init(3, vec![A::from(14), A::from(15)], None);
        mb.init(4, vec![A::from(16), A::from(17)], None);

        mb.write(1, vec![A::from(18), A::from(19)], false);
        mb.write(2, vec![A::from(20), A::from(21)], false);

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
            rmw,
        );
        assert!(res.is_ok());
        let (r, w) = res.unwrap();
        rw_mem_ops.push(r);
        rw_mem_ops.push(w);
    }
}
