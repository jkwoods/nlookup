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
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub struct MemElem<F: PrimeField> {
    pub time: F,
    pub addr: F,
    pub rw: bool, // push/write=1, pop/read=0
    pub vals: Vec<F>,
    pub sr: bool, //stack=1  or ram=0
}

impl<F: PrimeField> MemElem<F> {
    pub fn new(t: usize, sa: usize, rw: bool, v: Vec<usize>, sr: bool) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(sa as u64),
            rw,
            vals: v.into_iter().map(|x| F::from(x as u64)).collect(),
            sr: sr,
        }
    }

    pub fn new_f(t: usize, sa: usize, rw: bool, v: Vec<F>, sr: bool) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(sa as u64),
            rw,
            vals: v,
            sr: sr,
        }
    }

    pub fn new_single(t: usize, sa: usize, rw: bool, v: usize, sr: bool) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(sa as u64),
            rw,
            vals: vec![F::from(v as u64)],
            sr,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MemElemWires<F: PrimeField> {
    pub time: FpVar<F>,
    pub addr: FpVar<F>,
    pub rw: Boolean<F>, // push/write=1, pop/read=0
    pub vals: Vec<FpVar<F>>,
    pub sr: Boolean<F>,
}

impl<F: PrimeField> MemElemWires<F> {
    pub fn new(
        t: FpVar<F>,
        sa: FpVar<F>,
        rw: Boolean<F>,
        v: Vec<FpVar<F>>,
        sr: Boolean<F>,
    ) -> Self {
        MemElemWires {
            time: t,
            addr: sa,
            rw,
            vals: v,
            sr: sr,
        }
    }

    pub fn assert_eq(&self, m: &MemElem<F>) {
        assert_eq!(self.time.value().unwrap(), (*m).time);
        assert_eq!(self.addr.value().unwrap(), (*m).addr);
        assert_eq!(self.rw.value().unwrap(), (*m).rw);
        for j in 0..self.vals.len() {
            assert_eq!(self.vals[j].value().unwrap(), (*m).vals[j]);
        }
        assert_eq!(self.sr.value().unwrap(), (*m).sr);
    }
}

// builds the witness for RunningMem
#[derive(Debug)]
pub struct StackMemBuilder<F: PrimeField> {
    mem_builder: MemBuilder<F>,
    n_mems: usize,
    offsets: Vec<usize>,
    sps: Vec<usize>,
}

impl<F: PrimeField> StackMemBuilder<F> {
    pub fn new(elem_len: usize, offsets: Vec<usize>, n_mems: usize) -> Self {
        assert!(elem_len > 0);

        for i in 0..offsets.len() - 1 {
            assert!(offsets[i] < offsets[i + 1]);
        }

        Self {
            mem_builder: MemBuilder::new(elem_len),
            n_mems: n_mems,
            offsets: offsets.clone(),
            sps: offsets.clone(),
        }
    }

    pub fn pop(&mut self, tag: usize) -> Vec<F> {
        let cur_sp = self.sps[tag];
        assert!(cur_sp - 1 >= self.offsets[tag]);

        let popped = self.mem_builder.read(cur_sp, true);
        self.mem_builder.mem.remove(&cur_sp);

        self.sps[tag] = cur_sp - 1;

        popped
    }

    pub fn push(&mut self, elem: Vec<F>, tag: usize) {
        assert_eq!(
            elem.len(),
            self.mem_builder.elem_len,
            "Element not correct length"
        );

        let cur_sp = self.sps[tag];
        assert!(cur_sp + 1 < self.sps[tag + 1]);

        self.mem_builder.write(cur_sp + 1, elem.clone(), true);

        self.sps[tag] = cur_sp + 1;
    }

    pub fn get_time_list(&self) -> Vec<MemElem<F>> {
        assert_eq!(self.mem_builder.t.len(), self.mem_builder.time);
        self.mem_builder.t.clone()
    }
}

// builds the witness for RunningMem
#[derive(Debug)]
pub struct MemBuilder<F: PrimeField> {
    t: Vec<MemElem<F>>,
    stack: Vec<Vec<F>>,
    mem: HashMap<usize, Vec<F>>,
    elem_len: usize,
    time: usize,
}

impl<F: PrimeField> MemBuilder<F> {
    pub fn new(elem_len: usize) -> Self {
        assert!(elem_len > 0);

        Self {
            t: Vec::<MemElem<F>>::new(),
            stack: Vec::<Vec<F>>::new(),
            mem: HashMap::new(),
            elem_len,
            time: 0,
        }
    }

    pub fn read(&mut self, addr: usize, is_stack: bool) -> Vec<F> {
        let elem = if self.mem.contains_key(&addr) {
            self.mem[&addr].clone()
        } else {
            panic!("Uninitialized memory addr")
        };

        self.t.push(MemElem::new_f(
            self.time,
            addr,
            false,
            elem.clone(),
            is_stack,
        ));
        self.time += 1;

        elem
    }

    pub fn write(&mut self, addr: usize, elem: Vec<F>, is_stack: bool) {
        assert_eq!(elem.len(), self.elem_len, "Element not correct length");

        self.mem.insert(addr, elem.clone());

        self.t
            .push(MemElem::new_f(self.time, addr, true, elem, is_stack));
        self.time += 1;
    }

    pub fn get_time_list(&self) -> Vec<MemElem<F>> {
        assert_eq!(self.t.len(), self.time);
        self.t.clone()
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: PrimeField> {
    t: Vec<MemElem<F>>, // entries are (time step, mem addr, push/pop, val, tag)
    a: Vec<MemElem<F>>,
    i: usize,   // current round
    done: bool, // present to allow for "empty" circuits
    perm_chal: Vec<F>,
    // is_stack: bool,
    padding: MemElem<F>,
    // not for circuit use, not updated regularly, be careful
    running_t_F: F,
    running_a_F: F,
}

#[derive(Clone, Debug)]
pub struct RunningMemWires<F: PrimeField> {
    // for multiple calls in one CS
    cs: ConstraintSystemRef<F>,
    pub running_t: FpVar<F>,
    pub running_a: FpVar<F>,
    pub ti_m1_time: FpVar<F>,
    pub ai_m1_addr: FpVar<F>,
    pub ai_m1_rw: Boolean<F>,
    pub ai_m1_vals: Vec<FpVar<F>>,
    pub ai_m1_sr: Boolean<F>,
}

impl<F: PrimeField> RunningMem<F> {
    // all t elements should have the same size val vectors
    pub fn new(
        mut t: Vec<MemElem<F>>,
        padding: MemElem<F>, // what do you want to use for padding?
    ) -> Self {
        assert!(t.len() > 0);

        let vec_len = t[0].vals.len();
        assert!(vec_len > 0);
        assert_eq!(padding.vals.len(), vec_len);

        t.sort_by(|a, b| a.time.partial_cmp(&b.time).unwrap());

        let mut a = t.clone();
        a.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

        // println!("A list {:#?}", a.clone());

        let mut rng = test_rng();
        let mut perm_chal = Vec::<F>::new();
        for r in 0..(4 + vec_len) {
            perm_chal.push(F::rand(&mut rng));
        }

        Self {
            t,
            a,
            i: 0,
            done: false,
            perm_chal,
            padding,
            running_t_F: F::zero(),
            running_a_F: F::zero(),
        }
    }

    fn t(&self) -> &MemElem<F> {
        if self.i < self.t.len() {
            &self.t[self.i]
        } else {
            &self.t[0]
        }
    }

    fn a(&self) -> &MemElem<F> {
        if self.i < self.a.len() {
            &self.a[self.i]
        } else {
            &self.a[0]
        }
    }

    pub fn begin_new_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<RunningMemWires<F>, SynthesisError> {
        assert!(
            self.i < self.t.len() || self.done,
            "Already called funtion {} times",
            self.i
        );
        let vec_len = self.perm_chal.len() - 3;

        let running_t = FpVar::new_witness(cs.clone(), || Ok(self.running_t_F))?;
        let running_a = FpVar::new_witness(cs.clone(), || Ok(self.running_a_F))?;

        let ti_m1_time = FpVar::new_witness(cs.clone(), || {
            Ok(if self.i <= 0 || self.done {
                F::zero()
            } else {
                self.t[self.i - 1].time
            })
        })?;

        let (ai_m1_vals, ai_m1_rw, ai_m1_addr) = if self.i <= 0 || self.done {
            (
                vec![FpVar::new_witness(cs.clone(), || Ok(F::zero()))?; vec_len],
                Boolean::new_witness(cs.clone(), || Ok(false))?,
                FpVar::new_witness(cs.clone(), || Ok(F::zero()))?,
            )
        } else {
            let mut ai_m1_vals = Vec::<FpVar<F>>::new();
            for j in 0..vec_len {
                ai_m1_vals.push(FpVar::new_witness(cs.clone(), || {
                    Ok(self.a[self.i - 1].vals[j])
                })?);
            }
            (
                ai_m1_vals,
                Boolean::new_witness(cs.clone(), || Ok(self.a[self.i - 1].rw))?,
                FpVar::new_witness(cs.clone(), || Ok(self.a[self.i - 1].addr))?,
            )
        };

        let ai_m1_sr = Boolean::new_witness(cs.clone(), || Ok(true))?;

        Ok(RunningMemWires {
            cs: cs.clone(),
            running_t,
            running_a,
            ti_m1_time,
            ai_m1_addr,
            ai_m1_rw,
            ai_m1_vals,
            ai_m1_sr,
        })
    }

    // return lists of FpVars for time and addr lists
    // these should be hooked into your circuit in some way
    // likely the vars you want to use come from the time list
    // ex 1. for all stacks:
    // outer circuit maintains a stack pointer == t[i].addr + 1 if t[i].rw is push
    // ex 2. value constraints on t[i].vals
    pub fn next_op(
        &mut self,
        stack_check: &Boolean<F>,
        ram_after_stack: &Boolean<F>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        self.conditional_next_op(&Boolean::TRUE, stack_check, ram_after_stack, w)
    }

    pub fn conditional_next_op(
        &mut self,
        cond: &Boolean<F>,
        stack_check: &Boolean<F>,
        ram_after_stack: &Boolean<F>,
        w: &mut RunningMemWires<F>,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        if cond.value()? {
            assert!(
                self.i < self.t.len(),
                "Already called funtion {} times",
                self.i
            );
        }

        // i not 0
        let i = FpVar::new_witness(w.cs.clone(), || Ok(F::from(self.i as u64)))?;
        let i_not_0 = i.is_neq(&FpVar::new_constant(w.cs.clone(), F::zero())?)?;

        // running perm
        let mut perm_chal = Vec::<FpVar<F>>::new();
        for i in 0..self.perm_chal.len() {
            perm_chal.push(FpVar::new_witness(w.cs.clone(), || Ok(self.perm_chal[i]))?)
        }
        let vec_len = perm_chal.len() - 4;

        // by time
        let ti_time = cond.select(
            &FpVar::new_witness(w.cs.clone(), || Ok(self.t().time))?,
            &w.ti_m1_time,
        )?;
        let ti_addr = FpVar::new_witness(w.cs.clone(), || Ok(self.t().addr))?;
        let ti_rw = Boolean::new_witness(w.cs.clone(), || Ok(self.t().rw))?;
        let mut ti_vals = Vec::<FpVar<F>>::new();
        for j in 0..vec_len {
            ti_vals.push(FpVar::new_witness(w.cs.clone(), || Ok(self.t().vals[j]))?);
        }
        let ti_sr = Boolean::new_witness(w.cs.clone(), || Ok(self.t().sr))?;

        let mut actual_next_running_t = &w.running_t
            * (&perm_chal[0] - &ti_time)
            * (&perm_chal[1] - &ti_addr)
            * (&perm_chal[2] - &FpVar::from(ti_rw.clone()))
            * (&perm_chal[3] - &FpVar::from(ti_sr.clone()));
        for j in 0..vec_len {
            actual_next_running_t *= &perm_chal[4 + j] - &ti_vals[j];
        }

        let new_running_t = cond.select(&actual_next_running_t, &w.running_t)?;

        ti_time.conditional_enforce_equal(&(&w.ti_m1_time + &FpVar::one()), &(&i_not_0 & cond))?;

        // by addr
        let ai_time = FpVar::new_witness(w.cs.clone(), || Ok(self.a().time))?;
        let ai_addr = cond.select(
            &FpVar::new_witness(w.cs.clone(), || Ok(self.a().addr))?,
            &w.ai_m1_addr,
        )?;
        let ai_rw = cond.select(
            &Boolean::new_witness(w.cs.clone(), || Ok(self.a().rw))?,
            &w.ai_m1_rw,
        )?;
        let mut ai_vals = Vec::<FpVar<F>>::new();
        for j in 0..vec_len {
            ai_vals.push(cond.select(
                &FpVar::new_witness(w.cs.clone(), || Ok(self.a().vals[j]))?,
                &w.ai_m1_vals[j],
            )?);
        }
        let ai_sr = Boolean::new_witness(w.cs.clone(), || Ok(self.a().sr))?;

        let mut actual_next_running_a = &w.running_a
            * (&perm_chal[0] - &ai_time)
            * (&perm_chal[1] - &ai_addr)
            * (&perm_chal[2] - &FpVar::from(ai_rw.clone()))
            * (&perm_chal[3] - &FpVar::from(ai_sr.clone()));
        for j in 0..vec_len {
            actual_next_running_a *= &perm_chal[3 + j] - &ai_vals[j];
        }

        let new_running_a = cond.select(&actual_next_running_a, &w.running_a)?;

        // if a[i].rw == pop/read
        //      a[i-1].val == a[i].val
        let ai_is_read = ai_rw.is_eq(&Boolean::FALSE)?;
        for j in 0..vec_len {
            w.ai_m1_vals[j]
                .conditional_enforce_equal(&ai_vals[j], &(&i_not_0 & &ai_is_read & cond))?;
        }

        let ai_is_write = ai_rw.is_eq(&Boolean::TRUE)?;
        let ai_m1_is_read = w.ai_m1_rw.is_eq(&Boolean::FALSE)?;
        let ai_m1_is_write = w.ai_m1_rw.is_eq(&Boolean::TRUE)?;

        // only stack by addr
        // if a[i].rw == pop
        //      a[i-1].rw == push

        // println!("VALUE {:#?}", (&i_not_0 & &ai_is_read & cond).value()?);
        let push_pop_stack_check = &i_not_0 & &ai_is_read & cond & stack_check;
        w.ai_m1_rw
            .conditional_enforce_equal(&Boolean::TRUE, &push_pop_stack_check);

        // if a[i].rw == push
        //      if a[i-1].rw == push
        //          a[i-1].sp + 1 == a[i].sp
        let push_push_stack_check = &ai_is_write & &ai_m1_is_write & &i_not_0 & cond & stack_check;
        ai_addr
            .conditional_enforce_equal(&(&w.ai_m1_addr + &FpVar::one()), &push_push_stack_check)?;

        //check RAM after stack
        //either ai_m1_sr = 1 & ram_after_stack = false & ai_sr = 1
        //either ai_m1_sr = 1 & ram_after_stack = false & ai_sr = 0
        //either ai_m1_sr = 0 & ram_after_stack = true & ai_sr = 0
        let m1_sr_eq = w.ai_m1_sr.is_eq(&ai_sr)?;
        let still_in_stack = m1_sr_eq.clone() & &ai_sr & !ram_after_stack;
        let in_ram = m1_sr_eq.clone() & ram_after_stack & !&ai_sr;
        let stack_ram_trans = w.ai_m1_sr.clone() & !ram_after_stack & !&m1_sr_eq;
        let check_ram_after_stack = still_in_stack | &in_ram | &stack_ram_trans;

        check_ram_after_stack.conditional_enforce_equal(&Boolean::TRUE, cond)?;

        // update
        if cond.value()? {
            self.i += 1;
            if self.i == self.t.len() {
                self.done = true;
            }
            self.running_t_F = new_running_t.value()?;
            self.running_a_F = new_running_a.value()?;
        }
        w.running_t = new_running_t;
        w.ti_m1_time = ti_time.clone();
        let output_t = MemElemWires::new(ti_time, ti_addr, ti_rw, ti_vals, ti_sr);

        w.running_a = new_running_a;
        w.ai_m1_vals = ai_vals.clone();
        w.ai_m1_rw = ai_rw.clone();
        w.ai_m1_addr = ai_addr.clone();
        w.ai_m1_sr = ai_sr.clone();
        let output_a = MemElemWires::new(ai_time, ai_addr, ai_rw, ai_vals, ai_sr);

        Ok((output_t, output_a))
    }
}

#[derive(Clone, Debug)]
pub struct StackRunningMem<F: PrimeField> {
    pub running_mem: RunningMem<F>,
    pub additional_perm_chal: F,
    pub n_mems: F,
    pub n_mems_usize: usize,
    pub offsets: Vec<F>,
    pub post_stack: bool, //need ram marker --> once ai_m1 = S and ai=R turn on, while off must always be S while on must always be R
}

#[derive(Clone, Debug)]
pub struct StackRunningMemWires<F: PrimeField> {
    // for multiple calls in one CS
    cs: ConstraintSystemRef<F>,
    pub running_mem: RunningMemWires<F>,
    pub n_mems: FpVar<F>,
    pub n_mems_usize: usize,
    pub offsets: Vec<FpVar<F>>,
    pub post_stack: Boolean<F>,
}

impl<F: PrimeField> StackRunningMem<F> {
    // all t elements should have the same size val vectors
    pub fn new(
        mut t: Vec<MemElem<F>>,
        padding: MemElem<F>, // what do you want to use for padding?
        n_mems_usize: usize,
        offsets: Vec<F>,
    ) -> Self {
        let running_mem = RunningMem::new(t, padding);
        assert!(n_mems_usize > 0);
        assert_eq!(n_mems_usize, offsets.len());

        // println!("A list {:#?}", a.clone());

        let mut rng = test_rng();
        let perm_chal = F::rand(&mut rng);

        Self {
            running_mem: running_mem,
            additional_perm_chal: perm_chal,
            n_mems: F::from(n_mems_usize as u64),
            n_mems_usize: n_mems_usize,
            offsets: offsets.clone(),
            post_stack: false,
        }
    }

    fn t(&self) -> &MemElem<F> {
        self.running_mem.t()
    }

    fn a(&self) -> &MemElem<F> {
        self.running_mem.a()
    }

    pub fn begin_new_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<StackRunningMemWires<F>, SynthesisError> {
        let mem_wires = self.running_mem.begin_new_circuit(cs.clone())?;
        let n_mems = FpVar::new_witness(cs.clone(), || Ok(self.n_mems))?;

        let offsets = self
            .offsets
            .iter()
            .map(|f| FpVar::new_witness(cs.clone(), || Ok(f)).unwrap())
            .collect();

        let post_stack = Boolean::new_witness(cs.clone(), || Ok(false))?;

        Ok(StackRunningMemWires {
            cs: cs.clone(),
            running_mem: mem_wires,
            n_mems,
            n_mems_usize: self.n_mems_usize,
            offsets,
            post_stack,
        })
    }

    // return lists of FpVars for time and addr lists
    // these should be hooked into your circuit in some way
    // likely the vars you want to use come from the time list
    // ex 1. for all stacks:
    // outer circuit maintains a stack pointer == t[i].addr + 1 if t[i].rw is push
    // ex 2. value constraints on t[i].vals
    pub fn conditional_next_op(
        &mut self,
        cond: &Boolean<F>,
        w: &mut StackRunningMemWires<F>,
        tag: usize,
    ) -> Result<(MemElemWires<F>, MemElemWires<F>), SynthesisError> {
        let stack_bool = Boolean::new_witness(w.cs.clone(), || Ok(true))?;
        let ram_bool = Boolean::new_witness(w.cs.clone(), || Ok(false))?;
        let (out_t, out_a) = self.running_mem.conditional_next_op(
            cond,
            &stack_bool,
            &ram_bool,
            &mut w.running_mem,
        )?;

        let tag = FpVar::new_witness(w.cs.clone(), || Ok(F::from(tag as u64)))?;

        let perm_chal =
            FpVar::new_witness(w.cs.clone(), || Ok(F::from(self.additional_perm_chal)))?;

        let actual_next_running_t = w.running_mem.running_t.clone() * (&perm_chal - &tag);

        let new_running_t = cond.select(&actual_next_running_t, &w.running_mem.running_t)?;

        w.running_mem.running_t = new_running_t.clone();
        self.running_mem.running_t_F = new_running_t.value()?;

        let actual_next_running_a = w.running_mem.running_a.clone() * (&perm_chal - &tag);

        let new_running_a = cond.select(&actual_next_running_a, &w.running_mem.running_a)?;

        w.running_mem.running_a = new_running_a.clone();
        self.running_mem.running_a_F = new_running_a.value()?;

        w.post_stack = !&(out_a.sr);

        for i in 0..self.n_mems_usize {
            let i_fpvar = FpVar::new_witness(w.cs.clone(), || Ok(F::from(i as u64)))?;
            let is_not_tag = i_fpvar.is_neq(&tag)?;
            let offset = FpVar::new_witness(w.cs.clone(), || Ok(self.offsets[i]))?;

            out_t
                .addr
                .conditional_enforce_not_equal(&offset, &is_not_tag)?;
        }

        Ok((out_t, out_a))
    }
}

// mod tests {

//     use crate::memory::heckaton::*;
//     use ark_pallas::Fr as F;
//     use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};
//     use rand::Rng;

//     fn run_mem<F: PrimeField>(time_list: Vec<MemElem<F>>, is_stack: bool, batch_size: Vec<usize>) {
//         let mem_pad = MemElem::<F>::new(0, 0, false, vec![0; time_list[0].vals.len()]);
//         let mut num_cs = 0;

//         for b in batch_size {
//             println!("Batch size {}", b);
//             // regular
//             let mut rsm = RunningMem::new(
//                 time_list.clone(),
//                 is_stack,
//                 mem_pad.clone(),
//                 1,
//                 vec![F::ZERO],
//             );
//             let rounds = ((time_list.len() as f32) / (b as f32)).ceil() as usize;

//             let rand = rand::thread_rng().gen_range(0..(b + 1));
//             for i in 0..rounds {
//                 println!("round {}", i);

//                 let cs = ConstraintSystem::<F>::new_ref();
//                 cs.set_optimization_goal(OptimizationGoal::Constraints);

//                 let mut rw = rsm.begin_new_circuit(cs.clone()).unwrap();

//                 for bb in 0..b {
//                     if rand == bb {
//                         //let res = rsm.conditional_enforce(&Boolean::FALSE, &mut rw);
//                         //assert!(res.is_ok());
//                         //println!("BLANK");
//                     }

//                     println!("iter {}", bb);

//                     if (i * b + bb) < time_list.len() {
//                         let res = rsm.next_op(&mut rw);
//                         assert!(res.is_ok());
//                         let (output_t, output_a) = res.unwrap();
//                         output_t.assert_eq(&time_list[i * b + bb]);
//                     } else {
//                         let res = rsm.conditional_next_op(&Boolean::FALSE, &mut rw);
//                         assert!(res.is_ok());
//                     };
//                 }
//                 cs.finalize();
//                 assert!(cs.is_satisfied().unwrap(), "Failed at iter {}", i);

//                 if i == 0 {
//                     num_cs = cs.num_constraints();
//                     println!("num cs {:#?}", num_cs);
//                 } else {
//                     assert_eq!(num_cs, cs.num_constraints());
//                 }
//             }
//             // final checks
//             assert_eq!(rsm.running_t_F, rsm.running_a_F);
//         }
//     }

//     #[test]
//     fn stack_ex() {
//         let time_list = vec![
//             MemElem::<F>::new_single(0, 0, true, 1),
//             MemElem::<F>::new_single(1, 1, true, 2),
//             MemElem::<F>::new_single(2, 1, false, 2),
//             MemElem::<F>::new_single(3, 0, false, 1),
//             MemElem::<F>::new_single(4, 0, true, 3),
//         ];

//         run_mem(time_list.clone(), true, vec![1, 2, 5]);

//         let mut mb = MemBuilder::new(1, true);
//         mb.push(vec![F::from(1)]);
//         mb.push(vec![F::from(2)]);
//         assert_eq!(vec![F::from(2)], mb.pop());
//         assert_eq!(vec![F::from(1)], mb.pop());
//         mb.push(vec![F::from(3)]);

//         let t = mb.get_time_list();
//         assert_eq!(time_list, t);
//     }

//     #[test]
//     #[should_panic]
//     fn bad_pop() {
//         let time_list = vec![
//             MemElem::<F>::new_single(0, 0, true, 1),
//             MemElem::<F>::new_single(1, 1, true, 3),
//             MemElem::<F>::new_single(2, 1, false, 2),
//             MemElem::<F>::new_single(3, 0, false, 1),
//             MemElem::<F>::new_single(4, 0, true, 3),
//         ];

//         run_mem(time_list, true, vec![1, 2, 5]);
//     }

//     #[test]
//     fn mem_ex() {
//         let time_list = vec![
//             MemElem::<F>::new_single(0, 0, true, 0),
//             MemElem::<F>::new_single(1, 1, true, 1),
//             MemElem::<F>::new_single(2, 2, true, 2),
//             MemElem::<F>::new_single(3, 3, true, 3),
//             MemElem::<F>::new_single(4, 1, false, 1),
//             MemElem::<F>::new_single(5, 1, false, 1),
//             MemElem::<F>::new_single(6, 3, false, 3),
//             MemElem::<F>::new_single(7, 2, true, 4),
//             MemElem::<F>::new_single(8, 2, false, 4),
//         ];

//         run_mem(time_list.clone(), false, vec![1, 2, 4, 8, 9, 10]);

//         let mut mb = MemBuilder::new(1, false);
//         mb.write(0, vec![F::from(0)]);
//         mb.write(1, vec![F::from(1)]);
//         mb.write(2, vec![F::from(2)]);
//         mb.write(3, vec![F::from(3)]);
//         assert_eq!(vec![F::from(1)], mb.read(1));
//         assert_eq!(vec![F::from(1)], mb.read(1));
//         assert_eq!(vec![F::from(3)], mb.read(3));
//         mb.write(2, vec![F::from(4)]);
//         assert_eq!(vec![F::from(4)], mb.read(2));

//         let t = mb.get_time_list();
//         assert_eq!(time_list, t);
//     }

//     #[test]
//     fn mem_mult() {
//         let time_list = vec![
//             MemElem::<F>::new(0, 0, true, vec![0, 10]),
//             MemElem::<F>::new(1, 1, true, vec![1, 11]),
//             MemElem::<F>::new(2, 2, true, vec![2, 12]),
//             MemElem::<F>::new(3, 3, true, vec![3, 13]),
//             MemElem::<F>::new(4, 1, false, vec![1, 11]),
//             MemElem::<F>::new(5, 1, false, vec![1, 11]),
//             MemElem::<F>::new(6, 3, false, vec![3, 13]),
//             MemElem::<F>::new(7, 2, true, vec![4, 14]),
//             MemElem::<F>::new(8, 2, false, vec![4, 14]),
//         ];

//         run_mem(time_list.clone(), false, vec![1, 2, 4, 8, 9, 10]);

//         let mut mb = MemBuilder::new(2, false);
//         mb.write(0, vec![F::from(0), F::from(10)]);
//         mb.write(1, vec![F::from(1), F::from(11)]);
//         mb.write(2, vec![F::from(2), F::from(12)]);
//         mb.write(3, vec![F::from(3), F::from(13)]);
//         assert_eq!(vec![F::from(1), F::from(11)], mb.read(1));
//         assert_eq!(vec![F::from(1), F::from(11)], mb.read(1));
//         assert_eq!(vec![F::from(3), F::from(13)], mb.read(3));
//         mb.write(2, vec![F::from(4), F::from(14)]);
//         assert_eq!(vec![F::from(4), F::from(14)], mb.read(2));

//         let t = mb.get_time_list();
//         assert_eq!(time_list, t);
//     }

//     #[test]
//     #[should_panic]
//     fn mem_as_stack() {
//         let time_list = vec![
//             MemElem::<F>::new_single(0, 0, true, 0),
//             MemElem::<F>::new_single(1, 1, true, 1),
//             MemElem::<F>::new_single(2, 2, true, 2),
//             MemElem::<F>::new_single(3, 3, true, 3),
//             MemElem::<F>::new_single(4, 1, false, 1),
//             MemElem::<F>::new_single(5, 1, false, 1),
//             MemElem::<F>::new_single(6, 3, false, 3),
//             MemElem::<F>::new_single(7, 2, true, 4),
//             MemElem::<F>::new_single(8, 2, false, 4),
//         ];

//         run_mem(time_list, true, vec![1, 2, 4, 8, 10]);
//     }

//     #[test]
//     #[should_panic]
//     fn mem_bad_read() {
//         let time_list = vec![
//             MemElem::<F>::new_single(0, 0, true, 0),
//             MemElem::<F>::new_single(1, 1, true, 1),
//             MemElem::<F>::new_single(2, 2, true, 2),
//             MemElem::<F>::new_single(3, 3, true, 3),
//             MemElem::<F>::new_single(4, 1, false, 1),
//             MemElem::<F>::new_single(5, 1, false, 1),
//             MemElem::<F>::new_single(6, 1, false, 3),
//             MemElem::<F>::new_single(7, 2, true, 4),
//             MemElem::<F>::new_single(8, 2, false, 4),
//         ];

//         run_mem(time_list, false, vec![1, 2, 4, 8, 10]);
//     }

//     #[test]
//     fn eli_bug() {
//         let mut mb = MemBuilder::new(2, true);
//         mb.push(vec![F::from(0), F::from(0)]);
//         mb.push(vec![F::from(1), F::from(1)]);
//         mb.push(vec![F::from(2), F::from(1)]);
//         mb.pop();
//         mb.pop();
//         mb.pop();
//         mb.push(vec![F::from(0), F::from(1)]);

//         let time_list = mb.get_time_list();
//         println!("time list {:#?}", time_list.clone());
//         run_mem(time_list, true, vec![1]);
//     }
// }
