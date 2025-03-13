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

    pub fn new_f(t: usize, a: usize, v: Vec<F>, sr: bool) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(a as u64),
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
        perm_chal: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        todo!();
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
    elem_len: usize,
    ts: usize,
}

impl<F: PrimeField> MemBuilder<F> {
    pub fn new(elem_len: usize) -> Self {
        assert!(elem_len > 0);

        Self {
            mem: HashMap::new(),
            is: Vec::new(),
            rs: Vec::new(),
            ws: Vec::new(),
            fs: HashMap::new(),
            elem_len,
            time: 1,
        }
    }

    pub fn pad(&mut self) {
        let padding = MemElem::new_f(0, 0, false, vec![F::ZERO; self.elem_len], false);

        self.rs.push(padding);
        self.ws.push(padding);
    }

    pub fn read(&mut self, addr: usize, is_stack: bool) -> Vec<F> {
        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, addr);
        self.rs.push(elem);

        self.ts += 1;

        let write_elem = MemElem::new_f(self.ts, read_elem.addr, read_elem.vals, todo!());
        self.ws.push(elem);

        elem
    }

    // initialize memory
    // note: if you plan on writing to an addr, it must be initialized
    pub fn init(&mut self, addr: usize, vals: Vec<F>) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert_ne!(addr, 0);

        let elem = MemElem::new_f(self.time, addr, vals, todo!());
        self.mem.insert(addr, elem.clone());
        self.is.push(elem);
        self.fs.insert(addr, elem.clone());
    }

    pub fn write(&mut self, addr: usize, vals: Vec<F>) {
        assert_eq!(vals.len(), self.elem_len, "Element not correct length");
        assert_ne!(addr, 0);

        let read_elem = if self.mem.contains_key(&addr) {
            self.mem.get(addr).unwrap()
        } else {
            panic!("Uninitialized memory addr")
        };
        assert_eq!(read_elem.addr, addr);
        self.rs.push(elem);
        self.ts += 1;

        let write_elem = MemElem::new_f(self.time, read_elem.addr, vals, todo!());
        self.mem.insert(addr, elem.clone());
        self.rs.push(write_elem.clone());
        self.fs.insert(addr, elem);
    }

    pub fn new_running_mem(&self) -> RunningMem<F> {
        // by address
        let vec_fs = self.fs.into_values().collect();
        vec_fs.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        self.is.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        assert_eq!(vec_fs.len(), self.is.len());
        assert_eq!(self.rs.len(), self.ws.len());

        // we assume r/w >= i/f
        assert!(self.is.len() <= self.rs.len());
        let scan_per_rw_op = ((self.is.len() as f32) / (self.rs.len() as f32)).ceil() as usize;

        let padding = MemElem::new_f(0, 0, false, vec![F::ZERO; self.elem_len], false);

        RunningMem {
            is: self.is,
            rs: self.rs,
            ws: self.ws,
            fs: vec_fs,
            ts: self.ts,
            i: 0,
            perm_chal: todo!(),
            elem_len: self.elem_len,
            scan_per_rw_op,
            has_stack: todo!(),
            padding,
        };
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: PrimeField> {
    is: Vec<MemElem<F>>,
    rs: Vec<MemElem<F>>,
    ws: Vec<MemElem<F>>,
    fs: Vec<MemElem<F>>,
    ts: usize,
    i: usize, // for is/fs
    perm_chal: F,
    elem_len: usize,
    scan_per_rw_op: usize,
    has_stack: bool,
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
    /*pub ai_m1_addr: FpVar<F>,
    pub ai_m1_rw: Boolean<F>,
    pub ai_m1_vals: Vec<FpVar<F>>,
    pub ai_m1_sr: Boolean<F>,*/
}

impl<F: PrimeField> RunningMem<F> {
    pub fn begin_new_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
        running_is: F,
        running_rs: F,
        running_ws: F,
        running_fs: F,
    ) -> Result<RunningMemWires<F>, SynthesisError> {
        let running_is = FpVar::new_witness(cs.clone(), || Ok(running_is))?;
        let running_rs = FpVar::new_witness(cs.clone(), || Ok(running_rs))?;
        let running_ws = FpVar::new_witness(cs.clone(), || Ok(running_ws))?;
        let running_rs = FpVar::new_witness(cs.clone(), || Ok(running_fs))?;
        let ts_m1 = FpVar::new_witness(cs.clone(), || Ok(self.ts))?;

        RunningMemWires {
            cs: cs.clone(),
            running_is,
            running_rs,
            running_ws,
            running_rs,
            ts_m1,
        }
    }

    pub fn conditional_write(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        vals: Vec<&FpVars<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<
        (
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
        ),
        SynthesisError,
    > {
        self.conditional_op(cond, addr, Some(vals), w)
    }

    pub fn write(
        &mut self,
        addr: &FpVar<F>,
        vals: Vec<&FpVars<F>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<
        (
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
        ),
        SynthesisError,
    > {
        let cond = Boolean::<F>::new_constant(w.cs.clone(), || true)?;
        self.conditional_op(cond, addr, Some(vals), w)
    }

    pub fn conditional_read(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        w: &mut RunningMemWires<F>,
    ) -> Result<
        (
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
        ),
        SynthesisError,
    > {
        self.conditional_op(cond, addr, None, w)
    }

    pub fn read(
        &mut self,
        addr: &FpVar<F>,
        w: &mut RunningMemWires<F>,
    ) -> Result<
        (
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
        ),
        SynthesisError,
    > {
        let cond = Boolean::<F>::new_constant(w.cs.clone(), || true)?;
        self.conditional_op(cond, addr, None, w)
    }

    fn conditional_op(
        &mut self,
        cond: &Boolean<F>,
        addr: &FpVar<F>,
        write_vals: Option<Vec<&FpVar<F>>>,
        w: &mut RunningMemWires<F>,
    ) -> Result<
        (
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
            MemElemWires<F>,
        ),
        SynthesisError,
    > {
        // ts = ts + 1
        self.ts += 1;
        let ts = FpVar::new_witness(w.cs.clone(), || Ok(self.ts));
        ts.conditional_enforce_equal(&w.ts_m1 + &FpVar::one(), &cond)?;

        // t < ts hack TODO

        // RS = RS * tup
        let read_wit = self.mem_wits.get(addr.value()).unwrap();

        let read_mem_elem = MemElemWires::new(read_wit.time, read_wit.vals, todo!());
        let calc_running_rs = w.running_rs * read_mem_elem.hash(addr, self.perm_chal);
        let next_running_rs = cond.select(&calc_running_rs, &w.running_rs)?;

        // store in untrusted
        let v_prime = if write_vals.is_some() {
            let vals = write_vals.unwrap();
            assert_eq!(vals.len(), self.elem_len);
            vals
        } else {
            read_wit.vals
        };

        self.mem_wits.insert(
            addr.value(),
            MemElem::new(
                ts.value(),
                v_prime.iter().map(|v| v.value()).collect(),
                todo!(),
            ),
        );

        // WS = WS * tup
        let write_mem_elem = MemElemWires::new(ts, v_prime, todo!());
        let calc_running_ws = w.running_ws * write_mem_elem.hash(addr, self.perm_chal);
        let next_running_ws = cond.select(&calc_running_ws, &w.running_ws);

        for _ in 0..self.scan_per_rw_op {
            let (initial_mem_elem, final_mem_elem) = if self.i < self.is.len() {
                (
                    MemElemWires::new(self.is[i].time, self.is[i].vals, todo!()),
                    MemElemWires::new(self.is[i].time, self.is[i].vals, todo!()),
                )
            } else {
                todo!() //padding
            };

            // TODO cond
            // IS check
            let calc_running_is = w.running_is * initial_mem_elem.hash(addr, self.perm_chal);
            let next_running_is = cond.select(&calc_running_is, &w.running_is)?;

            // FS check
            let calc_running_fs = w.running_fs * final_mem_elem.hash(addr, self.perm_chal);
            let next_running_fs = cond.select(&calc_running_fs, &w.running_fs)?;

            // is_a = fs_a = i

            self.i += 1;
        }

        Ok(
            initial_mem_elem,
            read_mem_elem,
            write_mem_elem,
            final_mem_elem,
        )
    }
}
