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

        let r_j = AllocatedNum::alloc(
            cs.namespace(|| format!("{}_sc_r_{}", id, j)),
            || Ok(Fr::random(&mut thread_rng())),
        )?;

        let g_j = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}", id, j)), || {
            Ok(claim.get_value().unwrap())
        })?;

        // We enforce a constraint that checks the consistency of the claim between round
        let claim_check = cs.enforce(
            || format!("{}_claim_check_{}", id, j),
            |lc| lc + claim.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + g_j.get_variable(),
        );

        // We allocate variables for the coefficients of the polynomial g_j (xsq, x, const) and the random challenge r_j
        // These allocated variables are pushed to the out vector
        output.push(AllocatedNum::alloc(
            cs.namespace(|| format!("{}_sc_g_{}_xsq", id, j)),
            || Ok(g_j.get_value().unwrap()),
        )?);
        output.push(AllocatedNum::alloc(
            cs.namespace(|| format!("{}_sc_g_{}_x", id, j)),
            || Ok(g_j.get_value().unwrap()),
        )?);
        output.push(AllocatedNum::alloc(
            cs.namespace(|| format!("{}_sc_g_{}_const", id, j)),
            || Ok(g_j.get_value().unwrap()),
        )?);
        output.push(AllocatedNum::alloc(
            cs.namespace(|| format!("{}_sc_r_{}", id, j)),
            || Ok(g_j.get_value().unwrap()),
        )?);

        // Add in synthesize here?
        let state_0 = g_j.clone();
        let z = &output;
        synthesize(cs, z)?;

        // First, we need to get the allocated numbers corresponding to the variables
        let g_j_const = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}_const", id, j)), || Ok(g_j.get_value().unwrap()))?;
        let g_j_x = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}_x", id, j)), || Ok(g_j.get_value().unwrap()))?;
        let g_j_xsq = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_g_{}_xsq", id, j)), || Ok(g_j.get_value().unwrap()))?;
        let r_j = AllocatedNum::alloc(cs.namespace(|| format!("{}_sc_r_{}", id, j)), || Ok(g_j.get_value().unwrap()))?;

        
        // Then, we construct the polynomial using the allocated numbers
        let claim = g_j_const
            .add(cs.namespace(|| format!("{}_claim_add", id, j)), &r_j.mul(cs.namespace(|| format!("{}_claim_mul", id, j)), &(g_j_x.add(cs.namespace(|| format!("{}_claim_add", id, j)), &r_j.mul(cs.namespace(|| format!("{}_claim_mul", id, j)), &g_j_xsq))))?;

        // If it's the last round, we allocate a variable for the final claim and push it to the out vector
        if j == num_rounds {
            // output last g_v(r_v) claim
            let last_claim = AllocatedNum::alloc(
                cs.namespace(|| format!("{}_sc_last_claim", id)),
                || Ok(claim.get_value().unwrap()),
            )?;
        
            // Enforce that last_claim is equal to claim - do we do this here?
            cs.enforce(
                || format!("{}_last_claim_enforce", id),
                |lc| lc + claim.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + last_claim.get_variable(),
            );
        
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