use crate::backend::nova::int_to_ff;
use ::bellperson::{
    gadgets::num::AllocatedNum, ConstraintSystem, LinearCombination, Namespace, SynthesisError,
    Variable,
};
use ff::PrimeField;

pub fn sum_check_circuit<F: PrimeField, CS>(
    cs: &mut CS,
    init_claim: AllocatedNum<F>,
    num_rounds: usize,
    id: &str,
) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
where
    CS: ConstraintSystem<F>,
{
    // current claim in each round
    let mut claim = init_claim.clone();

    // vector that will store the output values of the sum check circuit
    let mut output = vec![];

    for j in 1..=num_rounds {
        // For each round j, we allocate a new variable g_j representing the claim of the current round
        // We use AllocatedNum::alloc to allocate the variable and provide a closure that returns the value of the current claim

        // A, B, C -> these should get their actual values from prover computations
// First, we need to get the allocated numbers corresponding to the variables
        let g_j_const = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}_const", id, j)), || Ok(g_j.get_value().unwrap()))?;
        let g_j_x = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}_x", id, j)), || Ok(g_j.get_value().unwrap()))?;
        let g_j_xsq = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}_xsq", id, j)), || Ok(g_j.get_value().unwrap()))?;

        // We enforce a constraint that checks the consistency of the claim between round
        // claim (either is init_claim or was set last loop to be g_j-1(r_j-1)) == g(0) + g(1) ==
        // xsq_coeff + x_coeff + const + const
        let claim_check = cs.enforce(
            || format!("{}_claim_check_{}", id, j),
            |lc| lc + claim.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + g_j.get_variable(), // make this a different variable that desribes
                                          // constraints A + B + C + C
        );

        let r_j = AllocatedNum::alloc(
            cs.namespace(|| format!("{}_sc_r_{}", id, j)),
            || Ok(Fr::random(&mut thread_rng())),
        )?;

        
        // Then, we construct the polynomial using the allocated numbers
        // horner's g_j(r_j) -> (((xsq * r) + x)*r + const)
        let claim = g_j_const
            .add(cs.namespace(|| format!("{}_claim_add", id, j)), &r_j.mul(cs.namespace(|| format!("{}_claim_mul", id, j)), &(g_j_x.add(cs.namespace(|| format!("{}_claim_add", id, j)), &r_j.mul(cs.namespace(|| format!("{}_claim_mul", id, j)), &g_j_xsq))))?;

        // If it's the last round, we allocate a variable for the final claim and push it to the out vector
        if j == num_rounds {
            // output last g_v(r_v) claim
            let last_claim = claim.clone();
            
            // Add last_claim to the list of public inputs
            cs.set_input(|| format!("{}_sc_last_claim", id), || Ok(last_claim.get_value().unwrap()));
        }
    }

    Ok(output)
}

fn synthesize<E: Engine, CS: ConstraintSystem<E>>(
    cs: &mut CS,
    z: &[AllocatedNum<E>],
) -> Result<Vec<AllocatedNum<E>>, SynthesisError> {
    // inputs
    let state_0 = z[0].clone();

    // your logic here

    Ok(vec![state_0])
}
