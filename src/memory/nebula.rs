use ark_ff::PrimeField;
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
use nova_snark::provider::incremental::Incremental;
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

    pub fn hash(
        &self,
        cs: ConstraintSystemRef<F>,
        perm_chal: &FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        todo!()
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
        let padding = MemElem::new_f(0, 0, vec![F::ZERO; self.elem_len], false);

        self.rs.push(padding.clone());
        self.ws.push(padding);
    }

    pub fn push(&mut self, stack_tag: usize, vals: Vec<F>) {
        self.write(self.stack_ptrs[stack_tag], vals, false);

        self.stack_ptrs[stack_tag] += 1;

        assert!(self.stack_ptrs[stack_tag] < self.stack_spaces[stack_tag + 1]);
    }

    pub fn pop(&mut self, stack_tag: usize) -> Vec<F> {
        self.stack_ptrs[stack_tag] -= 1;

        assert!(self.stack_ptrs[stack_tag] >= self.stack_spaces[stack_tag - 1]);

        self.read(self.stack_ptrs[stack_tag], false)
    }

    pub fn read(&mut self, addr: usize, is_ram: bool) -> Vec<F> {
        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(&addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, F::from(addr as u64));
        self.rs.push(read_elem.clone());

        self.ts += 1;

        let write_elem = MemElem::new_f(self.ts, addr, read_elem.vals.clone(), is_ram);
        self.ws.push(write_elem);

        read_elem.vals.clone()
    }

    // initialize memory
    // note: if you plan on writing to an addr, it must be initialized
    pub fn init(&mut self, addr: usize, vals: Vec<F>, stack_tag: Option<usize>) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert_ne!(addr, 0);
        if stack_tag.is_some() {
            assert!(vals.iter().all(|v| v == F::ZERO));
            assert!(addr < self.stack_spaces[stack_tag.unwrap() + 1]);
            assert!(addr >= self.stack_spaces[stack_tag.unwrap()]);
        }

        let elem = MemElem::new_f(F::ZERO, addr, vals, !stack_tag.is_some());
        self.mem.insert(addr, elem.clone());
        self.is.push(elem);
        self.fs.insert(addr, elem.clone());
    }

    pub fn write(&mut self, addr: usize, vals: Vec<F>, is_ram: bool) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert_ne!(addr, 0);

        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, addr);
        self.rs.push(read_elem);
        self.ts += 1;

        let write_elem = MemElem::new_f(self.time, read_elem.addr, vals, is_ram);
        self.mem.insert(addr, write_elem.clone());
        self.rs.push(write_elem.clone());
        self.fs.insert(addr, write_elem);
    }

    // TODO return cmt
    // num iters = number of foldings
    pub fn new_running_mem(&self, num_iters: usize) -> RunningMem<F> {
        // by address
        let vec_fs: Vec<MemElem<F>> = self.fs.into_values().collect();
        vec_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        self.is.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        let mem_wits = todo!(); // TODO

        assert_eq!(vec_fs.len(), self.is.len());
        assert_eq!(self.rs.len(), self.ws.len());

        let scan_per_batch = ((self.is.len() as f32) / (num_iters as f32)).ceil() as usize;

        let padding = MemElem::new_f(0, 0, vec![F::ZERO; self.elem_len], false);

        RunningMem {
            is: self.is,
            mem_wits,
            fs: vec_fs,
            ts: self.ts,
            i: 0,
            perm_chal: todo!(),
            elem_len: self.elem_len,
            scan_per_batch,
            stack_spaces: self.stack_spaces,
            padding,
        };
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: PrimeField> {
    is: Vec<MemElem<F>>,
    mem_wits: HashMap<F, MemElem<F>>,
    fs: Vec<MemElem<F>>,
    ts: usize,
    i: usize, // for is/fs
    perm_chal: F,
    elem_len: usize,
    scan_per_batch: usize,
    // if only ram, empty
    // stacks = [0, stack_1_limit, stack_2_limit, ....]
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
        let running_rs = FpVar::new_witness(cs.clone(), || Ok(running_fs))?;
        let ts_m1 = FpVar::new_witness(cs.clone(), || Ok(self.ts))?;
        let perm_chal = FpVar::new_constant(cs.clone(), || Ok(self.perm_chal))?;
        let stack_ptrs = stack_ptrs
            .iter()
            .map(|sp| FpVar::new_witness(cs.clone(), || Ok(sp)))
            .collect()?;

        Ok(RunningMemWires {
            cs: cs.clone(),
            running_is,
            running_rs,
            running_ws,
            running_rs,
            ts_m1,
            perm_chal,
            stack_ptrs,
        })
    }

    pub fn conditional_push(
        &mut self,
        cond: &Boolean<F>,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<&FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        assert!(self.stack_spaces.len() > 0);
        assert_eq!(w.stack_ptrs.len(), self.stack_spaces.len() + 1);
        assert!(stack_tag < self.stack_spaces.len());

        let res = self.conditional_op(cond, &w.stack_ptrs[stack_tag], Some(vals), false, w);

        // sp ++
        let sp = FpVar::new_witness(w.cs.clone(), || Ok(w.stack_ptrs[stack_tag].value()? + 1))?;
        sp.conditional_enforce_equal(&(&w.stack_ptrs[stack_tag] + &FpVar::one()), &cond)?;
        w.stack_ptrs[stack_tag] = cond.select(&sp, &w.stack_ptrs[stack_tag])?;

        // boundry check
        w.stack_ptrs[stack_tag].conditional_enforce_not_equal(
            &FpVar::new_constant(w.cs.clone(), || self.stack_spaces[stack_tag + 1]),
            cond,
        )?;

        res
    }

    pub fn push(
        &mut self,
        stack_tag: usize, // which stack (0, 1, 2, etc)
        vals: Vec<&FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_push(&Boolean::TRUE, stack_tag, vals, w)
    }

    pub fn conditional_write(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        vals: Vec<&FpVar<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_op(cond, addr, Some(vals), true, w)
    }

    pub fn write(
        &mut self,
        addr: &FpVar<F>,
        vals: Vec<&FpVar<F>>,
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
        let sp = FpVar::new_witness(w.cs.clone(), || Ok(w.stack_ptrs[stack_tag].value()? - 1))?;
        sp.conditional_enforce_equal(&(&w.stack_ptrs[stack_tag] - &FpVar::one()), &cond)?;
        w.stack_ptrs[stack_tag] = cond.select(&sp, &w.stack_ptrs[stack_tag])?;

        let res = self.conditional_op(cond, &w.stack_ptrs[stack_tag], None, false, w);

        // boundry check
        w.stack_ptrs[stack_tag].conditional_enforce_not_equal(
            &FpVar::new_constant(w.cs.clone(), || Ok(self.stack_spaces[stack_tag] - 1))?,
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
        self.conditional_op(cond, addr, None, true, w)
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
        write_vals: Option<Vec<&FpVar<F>>>,
        is_ram: bool,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        // ts = ts + 1
        let ts = FpVar::new_witness(w.cs.clone(), || Ok(w.ts_m1 + FpVar::one()))?;
        ts.conditional_enforce_equal(&(&w.ts_m1 + &FpVar::one()), &cond)?;
        w.ts_m1 = cond.select(&ts, &w.ts_m1)?;

        // t < ts hack

        // RS = RS * tup
        let read_wit = self.mem_wits.get(&addr.value()?).unwrap();
        assert_eq!(read_wit.addr, addr.value()?);

        let read_mem_elem = MemElemWires::new(
            FpVar::new_witness(w.cs.clone(), || Ok(read_wit.time))?,
            addr,
            read_wit
                .vals
                .iter()
                .map(|v| FpVar::new_witness(w.cs.clone(), || Ok(v)))
                .collect::<Result<Vec<FpVar<F>>, _>>()?,
            Boolean::new_witness(w.cs.clone(), || Ok(is_ram))?,
        );
        let next_running_rs = w.running_rs * read_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
        w.running_rs = cond.select(&next_running_rs, &w.running_rs)?;

        // stack or ram
        read_mem_elem
            .sr
            .conditional_enforce_equal(&Boolean::<F>::new_constant(w.cs.clone(), || is_ram)?, cond);

        let v_prime = if write_vals.is_some() {
            let vals = write_vals.unwrap();
            assert_eq!(vals.len(), self.elem_len);
            vals
        } else {
            read_mem_elem.vals
        };

        self.mem_wits.insert(
            addr.value()?,
            MemElem::new(
                ts.value()?,
                v_prime.iter().map(|v| v.value()).collect()?,
                read_mem_elem.sr.value()?,
            ),
        );

        // WS = WS * tup
        let write_mem_elem = MemElemWires::new(ts, addr, v_prime, read_mem_elem.sr);
        let next_running_ws = w.running_ws * write_mem_elem.hash(w.cs.clone(), &w.perm_chal)?;
        w.running_ws = cond.select(&next_running_ws, &w.running_ws)?;

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
            initial_mem_elem.time.enforce_equal(&FpVar::zero());

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
        }

        Ok((is_elems, fs_elems))
    }
}
