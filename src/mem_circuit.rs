use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
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
use std::ops::Not;

#[derive(Clone, Debug)]
pub struct MemElem<F: PrimeField> {
    time: F,
    addr: F,
    rw: bool, // push/write=1, pop/read=0
    vals: Vec<F>,
}

impl<F: PrimeField> MemElem<F> {
    pub fn new(t: usize, sa: usize, rw: bool, v: Vec<usize>) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(sa as u64),
            rw,
            vals: v.into_iter().map(|x| F::from(x as u64)).collect(),
        }
    }

    pub fn new_f(t: usize, sa: usize, rw: bool, v: Vec<F>) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(sa as u64),
            rw,
            vals: v,
        }
    }

    pub fn new_single(t: usize, sa: usize, rw: bool, v: usize) -> Self {
        MemElem {
            time: F::from(t as u64),
            addr: F::from(sa as u64),
            rw,
            vals: vec![F::from(v as u64)],
        }
    }
}

#[derive(Clone, Debug)]
pub struct MemElemWires<F: PrimeField> {
    time: FpVar<F>,
    addr: FpVar<F>,
    rw: Boolean<F>, // push/write=1, pop/read=0
    vals: Vec<FpVar<F>>,
}

impl<F: PrimeField> MemElemWires<F> {
    pub fn new(t: FpVar<F>, sa: FpVar<F>, rw: Boolean<F>, v: Vec<FpVar<F>>) -> Self {
        MemElemWires {
            time: t,
            addr: sa,
            rw,
            vals: v,
        }
    }

    pub fn assert_eq(&self, m: &MemElem<F>) {
        assert_eq!(self.time.value().unwrap(), (*m).time);
        assert_eq!(self.addr.value().unwrap(), (*m).addr);
        assert_eq!(self.rw.value().unwrap(), (*m).rw);
        for j in 0..self.vals.len() {
            assert_eq!(self.vals[j].value().unwrap(), (*m).vals[j]);
        }
    }
}

#[derive(Clone, Debug)]
pub struct RunningMem<F: PrimeField> {
    t: Vec<MemElem<F>>, // entries are (time step, mem addr, push/pop, val)
    running_t: F,       // running_t at round i
    a: Vec<MemElem<F>>,
    running_a: F, // running_a at round i
    ti: usize,    // current round
    ai: usize,
    perm_chal: Vec<F>,
    is_stack: bool, // ram=0, stack=1
    time_only: bool,
    ri_per_circ: usize,
    ai_per_circ: usize,
    padding: MemElem<F>,
}

// when a different proof "read in" your mem (performed only writes)
#[derive(Clone, Debug)]
pub struct PrevMem<F: PrimeField> {
    perm_chal: Vec<F>,
    witness_t: Vec<MemElem<F>>,
}

impl<F: PrimeField> RunningMem<F> {
    // all t elements should have the same size val vectors
    pub fn new(
        mut t: Vec<MemElem<F>>,
        is_stack: bool,
        time_only: bool,
        batch_size: usize,
        padding: MemElem<F>, // what do you want to use for padding?
        prev_mem: Option<PrevMem<F>>,
    ) -> Self {
        assert!(t.len() > 0);
        if time_only {
            assert!(prev_mem.is_none());
        }
        let vec_len = t[0].vals.len();
        assert!(vec_len > 0);
        assert_eq!(padding.vals.len(), vec_len);

        t.sort_by(|a, b| a.time.partial_cmp(&b.time).unwrap());

        if prev_mem.is_some() {
            let mut prev_m = prev_mem.unwrap();
            assert!(prev_m.witness_t.len() > 0);
            prev_m
                .witness_t
                .sort_by(|a, b| a.time.partial_cmp(&b.time).unwrap());

            assert_eq!(prev_m.witness_t.last().unwrap().time + F::one(), t[0].time);
            let mut new_t = Vec::<MemElem<F>>::new();
            new_t.extend(prev_m.witness_t.clone());
            new_t.extend(t.clone());

            let mut a = new_t.clone();
            a.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

            let mut running_t = F::one();
            for i in 0..prev_m.witness_t.len() {
                running_t = running_t
                    * (prev_m.perm_chal[0] - prev_m.witness_t[i].time)
                    * (prev_m.perm_chal[1] - prev_m.witness_t[i].addr)
                    * (prev_m.perm_chal[2] - F::from(prev_m.witness_t[i].rw));
                for j in 0..vec_len {
                    running_t = running_t * (prev_m.perm_chal[3 + j] - prev_m.witness_t[i].vals[j]);
                }
            }

            let ai_per_circ = if time_only {
                0
            } else {
                (((a.len() as f32) / (t.len() as f32)).ceil() as usize) * batch_size
            };

            Self {
                t: new_t,
                running_t,
                a,
                running_a: F::one(),
                ti: prev_m.witness_t.len(),
                ai: 0,
                perm_chal: prev_m.perm_chal,
                is_stack,
                time_only,
                ri_per_circ: batch_size,
                ai_per_circ,
                padding,
            }
        } else {
            let mut a = t.clone();
            a.sort_by(|a, b| a.addr.partial_cmp(&b.addr).unwrap());

            let mut rng = test_rng();
            let mut perm_chal = Vec::<F>::new();
            for r in 0..(3 + vec_len) {
                perm_chal.push(F::rand(&mut rng));
            }

            let ai_per_circ = if time_only {
                0
            } else {
                (((a.len() as f32) / (t.len() as f32)).ceil() as usize) * batch_size
            };

            Self {
                t,
                running_t: F::one(),
                a,
                running_a: F::one(),
                ti: 0,
                ai: 0,
                perm_chal,
                is_stack,
                time_only,
                ri_per_circ: batch_size,
                ai_per_circ,
                padding,
            }
        }
    }

    pub fn final_checks(&self) {
        assert_eq!(self.running_t, self.running_a);
    }

    // return lists of FpVars for time and addr lists
    // these should be hooked into your circuit in some way
    // likely the vars you want to use come from the time list
    // ex 1. for all stacks:
    // outer circuit maintains a stack pointer == t[i].addr + 1 if t[i].rw is push
    // ex 2. value constraints on t[i].vals
    pub fn make_circuit(
        &mut self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<MemElemWires<F>>, Vec<MemElemWires<F>>), SynthesisError> {
        let mut output_t = Vec::<MemElemWires<F>>::new();
        let mut output_a = Vec::<MemElemWires<F>>::new();

        // running perm
        let mut perm_chal = Vec::<FpVar<F>>::new();
        for i in 0..self.perm_chal.len() {
            perm_chal.push(FpVar::<F>::new_input(cs.clone(), || Ok(self.perm_chal[i]))?)
        }
        let vec_len = perm_chal.len() - 3;

        // by time
        let mut ti_m1_time = FpVar::<F>::new_input(cs.clone(), || {
            Ok(if self.ti <= 0 {
                F::zero()
            } else {
                self.t[self.ti - 1].time
            })
        })?;

        let mut ti_time = FpVar::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].time))?;
        let mut ti_addr = FpVar::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].addr))?;
        let mut ti_rw = Boolean::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].rw))?;
        let mut ti_vals = Vec::<FpVar<F>>::new();
        for j in 0..vec_len {
            ti_vals.push(FpVar::<F>::new_input(cs.clone(), || {
                Ok(self.t[self.ti].vals[j])
            })?);
        }

        let mut running_t = FpVar::new_witness(cs.clone(), || Ok(self.running_t))?;

        // i not 0
        let mut alloc_t_i = FpVar::<F>::new_input(cs.clone(), || Ok(F::from(self.ti as u64)))?;

        for t_rep in 0..self.ri_per_circ {
            let ti_not_0 = if t_rep == 0 {
                alloc_t_i.is_neq(&FpVar::<F>::new_constant(cs.clone(), F::zero())?)?
            } else {
                Boolean::TRUE
            };
            let ti_not_max = alloc_t_i.is_neq(&FpVar::<F>::new_constant(
                cs.clone(),
                F::from(self.t.len() as u64),
            )?)?;

            let new_running_t = if self.ti < self.t.len() {
                let mut intm = FpVar::<F>::new_input(cs.clone(), || {
                    Ok(self.running_t
                        * (self.perm_chal[0] - self.t[self.ti].time)
                        * (self.perm_chal[1] - self.t[self.ti].addr)
                        * (self.perm_chal[2] - F::from(self.t[self.ti].rw)))
                })?;
                for j in 0..vec_len {
                    intm *= self.perm_chal[3 + j] - self.t[self.ti].vals[j];
                }
                intm
            } else {
                FpVar::<F>::new_input(cs.clone(), || Ok(self.running_t))?
            };

            let mut nrt = running_t.clone()
                * (&perm_chal[0] - &ti_time)
                * (&perm_chal[1] - &ti_addr)
                * (&perm_chal[2] - &FpVar::from(ti_rw.clone()));
            for j in 0..vec_len {
                nrt *= &perm_chal[3 + j] - &ti_vals[j];
            }
            new_running_t.conditional_enforce_equal(&nrt, &ti_not_max);

            // TODO: fix clonse??
            new_running_t.conditional_enforce_equal(&running_t, &ti_not_max.clone().not());

            let new_t_i = FpVar::<F>::new_input(cs.clone(), || {
                Ok(F::from(
                    (if self.ti < self.t.len() {
                        self.ti + 1
                    } else {
                        self.ti
                    }) as u64,
                ))
            })?;
            new_t_i.conditional_enforce_equal(&(&alloc_t_i + &FpVar::one()), &ti_not_max);

            ti_time.conditional_enforce_equal(
                &(&ti_m1_time + &FpVar::one()),
                &(&ti_not_0 & &ti_not_max),
            );

            // update
            alloc_t_i = new_t_i;
            ti_m1_time = ti_time.clone();
            output_t.push(MemElemWires::new(
                ti_time.clone(),
                ti_addr.clone(),
                ti_rw.clone(),
                ti_vals.clone(),
            ));

            if self.ti < self.t.len() {
                self.ti += 1;
                if self.ti < self.t.len() {
                    ti_time = FpVar::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].time))?;
                    ti_addr = FpVar::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].addr))?;
                    ti_rw = Boolean::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].rw))?;
                    for j in 0..vec_len {
                        ti_vals[j] =
                            FpVar::<F>::new_input(cs.clone(), || Ok(self.t[self.ti].vals[j]))?;
                    }
                } else {
                    // padding
                    ti_time = FpVar::<F>::new_input(cs.clone(), || Ok(self.padding.time))?;
                    ti_addr = FpVar::<F>::new_input(cs.clone(), || Ok(self.padding.addr))?;
                    ti_rw = Boolean::<F>::new_input(cs.clone(), || Ok(self.padding.rw))?;
                    for j in 0..vec_len {
                        ti_vals[j] =
                            FpVar::<F>::new_input(cs.clone(), || Ok(self.padding.vals[j]))?;
                    }
                }
            }
            self.running_t = new_running_t.value()?;
            running_t = new_running_t;
        }

        if !self.time_only {
            // by addr
            let (mut ai_m1_vals, mut ai_m1_rw, mut ai_m1_addr) = if self.ai <= 0 {
                (
                    vec![FpVar::<F>::new_input(cs.clone(), || Ok(F::zero()))?; vec_len],
                    Boolean::<F>::new_input(cs.clone(), || Ok(false))?,
                    FpVar::<F>::new_input(cs.clone(), || Ok(F::zero()))?,
                )
            } else {
                let mut ai_m1_vals = Vec::<FpVar<F>>::new();
                for j in 0..vec_len {
                    ai_m1_vals.push(FpVar::<F>::new_input(cs.clone(), || {
                        Ok(self.a[self.ai - 1].vals[j])
                    })?);
                }
                (
                    ai_m1_vals,
                    Boolean::<F>::new_input(cs.clone(), || Ok(self.a[self.ai - 1].rw))?,
                    FpVar::<F>::new_input(cs.clone(), || Ok(self.a[self.ai - 1].addr))?,
                )
            };

            let mut ai_time = FpVar::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].time))?;
            let mut ai_addr = FpVar::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].addr))?;
            let mut ai_rw = Boolean::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].rw))?;
            let mut ai_vals = Vec::<FpVar<F>>::new();
            for j in 0..vec_len {
                ai_vals.push(FpVar::<F>::new_input(cs.clone(), || {
                    Ok(self.a[self.ai].vals[j])
                })?);
            }

            let mut running_a = FpVar::<F>::new_input(cs.clone(), || Ok(self.running_a))?;

            // i not 0
            let mut alloc_a_i = FpVar::<F>::new_input(cs.clone(), || Ok(F::from(self.ai as u64)))?;

            for a_rep in 0..self.ai_per_circ {
                let ai_not_0 = if a_rep == 0 {
                    alloc_a_i.is_neq(&FpVar::<F>::new_constant(cs.clone(), F::zero())?)?
                } else {
                    Boolean::TRUE
                };
                let ai_not_max = alloc_a_i.is_neq(&FpVar::<F>::new_constant(
                    cs.clone(),
                    F::from(self.a.len() as u64),
                )?)?;
                let ai_okay = &(&ai_not_0 & &ai_not_max);

                let new_running_a = if self.ai < self.a.len() {
                    let mut intm = FpVar::<F>::new_input(cs.clone(), || {
                        Ok(self.running_a
                            * (self.perm_chal[0] - self.a[self.ai].time)
                            * (self.perm_chal[1] - self.a[self.ai].addr)
                            * (self.perm_chal[2] - F::from(self.a[self.ai].rw)))
                    })?;
                    for j in 0..vec_len {
                        intm *= self.perm_chal[3 + j] - self.a[self.ai].vals[j];
                    }
                    intm
                } else {
                    FpVar::<F>::new_input(cs.clone(), || Ok(self.running_a))?
                };

                let mut nra = running_a.clone()
                    * (&perm_chal[0] - &ai_time)
                    * (&perm_chal[1] - &ai_addr)
                    * (&perm_chal[2] - &FpVar::from(ai_rw.clone()));
                for j in 0..vec_len {
                    nra *= &perm_chal[3 + j] - &ai_vals[j];
                }
                new_running_a.conditional_enforce_equal(&nra, &ai_not_max);
                new_running_a.conditional_enforce_equal(&running_a, &ai_not_max.clone().not());

                let new_a_i = FpVar::<F>::new_input(cs.clone(), || {
                    Ok(F::from(
                        (if self.ai < self.a.len() {
                            self.ai + 1
                        } else {
                            self.ai
                        }) as u64,
                    ))
                })?;
                new_a_i.conditional_enforce_equal(&(&alloc_a_i + &FpVar::one()), &ai_not_max);

                // if a[i].rw == pop/read
                //      a[i-1].val == a[i].val
                let ai_is_read = ai_rw.is_eq(&Boolean::FALSE)?;
                for j in 0..vec_len {
                    ai_m1_vals[j].conditional_enforce_equal(&ai_vals[j], &(ai_okay & &ai_is_read));
                }

                if self.is_stack {
                    let ai_is_write = ai_rw.is_eq(&Boolean::TRUE)?;
                    let ai_m1_is_read = ai_m1_rw.is_eq(&Boolean::FALSE)?;
                    let ai_m1_is_write = ai_m1_rw.is_eq(&Boolean::TRUE)?;

                    // only stack by addr
                    // if a[i].rw == pop
                    //      a[i-1].rw == push
                    ai_m1_rw.conditional_enforce_equal(&Boolean::TRUE, &(ai_okay & &ai_is_read));

                    // if a[i].rw == push
                    //      if a[i-1].rw == push
                    //          a[i-1].sp + 1 == a[i].sp
                    ai_addr.conditional_enforce_equal(
                        &(&ai_m1_addr + &FpVar::one()),
                        &(&ai_is_write & &ai_m1_is_write & ai_okay),
                    );

                    //      else if a[i-1].rw == pop
                    //          a[i-1].sp == a[i].sp
                    ai_addr.conditional_enforce_equal(
                        &(ai_m1_addr),
                        &(&ai_is_write & &ai_m1_is_read & ai_okay), // seperate rust var
                    );
                }

                // update
                alloc_a_i = new_a_i.clone();
                ai_m1_vals = ai_vals.clone();
                ai_m1_rw = ai_rw.clone();
                ai_m1_addr = ai_addr.clone();
                output_a.push(MemElemWires::new(
                    ai_time.clone(),
                    ai_addr.clone(),
                    ai_rw.clone(),
                    ai_vals.clone(),
                ));
                if self.ai < self.a.len() {
                    self.ai += 1;
                    if self.ai < self.a.len() {
                        ai_time = FpVar::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].time))?;
                        ai_addr = FpVar::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].addr))?;
                        ai_rw = Boolean::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].rw))?;
                        for j in 0..vec_len {
                            ai_vals[j] =
                                FpVar::<F>::new_input(cs.clone(), || Ok(self.a[self.ai].vals[j]))?;
                        }
                    } else {
                        // padding
                        ai_time = FpVar::<F>::new_input(cs.clone(), || Ok(self.padding.time))?;
                        ai_addr = FpVar::<F>::new_input(cs.clone(), || Ok(self.padding.addr))?;
                        ai_rw = Boolean::<F>::new_input(cs.clone(), || Ok(self.padding.rw))?;
                        for j in 0..vec_len {
                            ai_vals[j] =
                                FpVar::<F>::new_input(cs.clone(), || Ok(self.padding.vals[j]))?;
                        }
                    }
                }
                self.running_a = new_running_a.value()?;
                running_a = new_running_a;
            }
        }

        Ok((output_t, output_a))
    }
}

mod tests {

    use crate::mem_circuit::*;
    use ark_pallas::Fr as F;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

    fn run_mem<F: PrimeField>(
        time_list: Vec<MemElem<F>>,
        is_stack: bool,
        batch_size: Vec<usize>,
        prev_writes: Option<Vec<MemElem<F>>>,
    ) {
        let mem_pad = MemElem::<F>::new(0, 0, false, vec![0; time_list[0].vals.len()]);

        for b in batch_size {
            // need to do write only?
            let pm = if prev_writes.is_some() {
                let write_list = prev_writes.clone().unwrap();
                let mut rsm =
                    RunningMem::new(write_list.clone(), is_stack, true, b, mem_pad.clone(), None);
                let rounds = ((write_list.len() as f32) / (b as f32)).ceil() as usize;

                let mut padded_write_list = write_list.clone();
                padded_write_list.extend(vec![mem_pad.clone(); (rounds * b) - write_list.len()]);

                for i in 0..rounds {
                    let cs = ConstraintSystem::<F>::new_ref();
                    cs.set_optimization_goal(OptimizationGoal::Constraints);
                    let res = rsm.make_circuit(cs.clone());
                    assert!(res.is_ok());
                    cs.finalize();
                    assert!(
                        cs.is_satisfied().unwrap(),
                        "Failed at batch {}, iter {}",
                        b,
                        i
                    );

                    let (output_t, output_a) = res.unwrap();
                    assert_eq!(output_a.len(), 0);

                    println!("round {:#?} b {:#?}", i, b);
                    let t_chunk = &padded_write_list[(i * b)..((i + 1) * b)];
                    assert_eq!(output_t.len(), t_chunk.len());
                    assert_eq!(output_t.len(), rsm.ri_per_circ);
                    assert_eq!(output_a.len(), rsm.ai_per_circ);

                    for o in 0..output_t.len() {
                        output_t[o].assert_eq(&t_chunk[o]);
                    }
                }
                Some(PrevMem {
                    perm_chal: rsm.perm_chal,
                    witness_t: write_list,
                })
            } else {
                None
            };

            // regular
            let mut rsm =
                RunningMem::new(time_list.clone(), is_stack, false, b, mem_pad.clone(), pm);
            let rounds = ((time_list.len() as f32) / (b as f32)).ceil() as usize;

            let mut padded_time_list = time_list.clone();
            padded_time_list.extend(vec![mem_pad.clone(); (rounds * b) - time_list.len()]);

            for i in 0..rounds {
                let cs = ConstraintSystem::<F>::new_ref();
                cs.set_optimization_goal(OptimizationGoal::Constraints);
                let res = rsm.make_circuit(cs.clone());
                assert!(res.is_ok());
                cs.finalize();
                assert!(
                    cs.is_satisfied().unwrap(),
                    "Failed at batch {}, iter {}",
                    b,
                    i
                );
                println!("Batch {}, iter {}, good", b, i);

                let (output_t, output_a) = res.unwrap();
                let t_chunk = &padded_time_list[(i * b)..((i + 1) * b)];
                assert_eq!(output_t.len(), t_chunk.len());
                assert_eq!(output_t.len(), rsm.ri_per_circ);
                assert_eq!(output_a.len(), rsm.ai_per_circ);

                for o in 0..output_t.len() {
                    output_t[o].assert_eq(&t_chunk[o]);
                }
            }
            rsm.final_checks();
            println!("Batch {} good", b);
        }
    }

    #[test]
    fn write_ahead_of_time() {
        let write_list = vec![
            MemElem::<F>::new_single(0, 0, true, 0),
            MemElem::<F>::new_single(1, 1, true, 1),
            MemElem::<F>::new_single(2, 2, true, 2),
            MemElem::<F>::new_single(3, 3, true, 3),
        ];

        let time_list = vec![
            MemElem::<F>::new_single(4, 1, false, 1),
            MemElem::<F>::new_single(5, 1, false, 1),
            MemElem::<F>::new_single(6, 3, false, 3),
            MemElem::<F>::new_single(7, 2, true, 4),
            MemElem::<F>::new_single(8, 2, false, 4),
        ];

        run_mem(time_list, false, vec![1, 2, 4, 8, 9, 10], Some(write_list));
    }

    #[test]
    #[should_panic]
    fn write_ahead_of_time_bad() {
        let write_list = vec![
            MemElem::<F>::new_single(0, 0, true, 0),
            MemElem::<F>::new_single(1, 1, true, 1),
            MemElem::<F>::new_single(2, 2, true, 2),
            MemElem::<F>::new_single(3, 3, true, 3),
        ];

        let time_list = vec![
            MemElem::<F>::new_single(4, 1, false, 1),
            MemElem::<F>::new_single(5, 1, false, 1),
            MemElem::<F>::new_single(6, 3, false, 2),
            MemElem::<F>::new_single(7, 2, true, 4),
            MemElem::<F>::new_single(8, 2, false, 4),
        ];

        run_mem(time_list, false, vec![1, 2, 4, 8, 9, 10], Some(write_list));
    }

    #[test]
    fn stack_ex() {
        let time_list = vec![
            MemElem::<F>::new_single(0, 0, true, 1),
            MemElem::<F>::new_single(1, 1, true, 2),
            MemElem::<F>::new_single(2, 1, false, 2),
            MemElem::<F>::new_single(3, 0, false, 1),
            MemElem::<F>::new_single(4, 0, true, 3),
        ];

        run_mem(time_list, true, vec![1, 2, 5], None);
    }

    #[test]
    #[should_panic]
    fn bad_pop() {
        let time_list = vec![
            MemElem::<F>::new_single(0, 0, true, 1),
            MemElem::<F>::new_single(1, 1, true, 3),
            MemElem::<F>::new_single(2, 1, false, 2),
            MemElem::<F>::new_single(3, 0, false, 1),
            MemElem::<F>::new_single(4, 0, true, 3),
        ];

        run_mem(time_list, true, vec![1, 2, 5], None);
    }

    #[test]
    fn mem_ex() {
        let time_list = vec![
            MemElem::<F>::new_single(0, 0, true, 0),
            MemElem::<F>::new_single(1, 1, true, 1),
            MemElem::<F>::new_single(2, 2, true, 2),
            MemElem::<F>::new_single(3, 3, true, 3),
            MemElem::<F>::new_single(4, 1, false, 1),
            MemElem::<F>::new_single(5, 1, false, 1),
            MemElem::<F>::new_single(6, 3, false, 3),
            MemElem::<F>::new_single(7, 2, true, 4),
            MemElem::<F>::new_single(8, 2, false, 4),
        ];

        run_mem(time_list, false, vec![1, 2, 4, 8, 9, 10], None);
    }

    #[test]
    #[should_panic]
    fn mem_as_stack() {
        let time_list = vec![
            MemElem::<F>::new_single(0, 0, true, 0),
            MemElem::<F>::new_single(1, 1, true, 1),
            MemElem::<F>::new_single(2, 2, true, 2),
            MemElem::<F>::new_single(3, 3, true, 3),
            MemElem::<F>::new_single(4, 1, false, 1),
            MemElem::<F>::new_single(5, 1, false, 1),
            MemElem::<F>::new_single(6, 3, false, 3),
            MemElem::<F>::new_single(7, 2, true, 4),
            MemElem::<F>::new_single(8, 2, false, 4),
        ];

        run_mem(time_list, true, vec![1, 2, 4, 8, 10], None);
    }

    #[test]
    #[should_panic]
    fn mem_bad_read() {
        let time_list = vec![
            MemElem::<F>::new_single(0, 0, true, 0),
            MemElem::<F>::new_single(1, 1, true, 1),
            MemElem::<F>::new_single(2, 2, true, 2),
            MemElem::<F>::new_single(3, 3, true, 3),
            MemElem::<F>::new_single(4, 1, false, 1),
            MemElem::<F>::new_single(5, 1, false, 1),
            MemElem::<F>::new_single(6, 1, false, 3),
            MemElem::<F>::new_single(7, 2, true, 4),
            MemElem::<F>::new_single(8, 2, false, 4),
        ];

        run_mem(time_list, false, vec![1, 2, 4, 8, 10], None);
    }
}
