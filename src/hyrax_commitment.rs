use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use generic_array::typenum;
use merlin::Transcript;
use neptune::{
    circuit2::Elt,
    poseidon::PoseidonConstants,
    sponge::api::{IOPattern, SpongeAPI, SpongeOp},
    sponge::circuit::SpongeCircuit,
    sponge::vanilla::{Mode, Sponge, SpongeTrait},
    Strength,
};
use nova_snark::{
    errors::NovaError,
    provider::{
        hyrax_pc::{HyraxPC, PolyCommit, PolyCommitBlinds},
        ipa_pc::InnerProductArgument,
        pedersen::{CommitmentGens, CompressedCommitment},
        poseidon::{PoseidonConstantsCircuit, PoseidonRO},
    },
    spartan::{
        direct::{SpartanProverKey, SpartanSNARK, SpartanVerifierKey},
        nizk::EqualityProof,
        polynomial::{EqPolynomial, MultilinearPolynomial},
    },
    traits::{
        circuit::StepCircuit, commitment::*, evaluation::GetGeneratorsTrait, AbsorbInROTrait,
        AppendToTranscriptTrait, ChallengeTrait, Group, ROConstantsTrait, ROTrait,
    },
    StepCounterType,
};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;

// hyrax commitment to an MLE
#[derive(Deserialize, Serialize)]
pub struct NLCommitment {
    // commitment
    pub single_gens: CommitmentGens<G1>,
    hyrax_gen: HyraxPC<G1>,
    doc_poly: MultilinearPolynomial<<G1 as Group>::Scalar>,
    pub doc_commit: PolyCommit<G1>,
    doc_decommit: PolyCommitBlinds<G1>,
    pub doc_commit_hash: <G1 as Group>::Scalar,
    pub hash_salt: <G1 as Group>::Scalar,
    // consistency verification
    cap_pk: SpartanProverKey<G1, EE1>,
    cap_vk: SpartanVerifierKey<G1, EE1>,
    q_len: usize,
    // prover only info
}

impl NLCommitment {
    pub fn new(table: Vec<<G1 as Group>::Scalar>) -> Self
    where
        G1: Group<Base = <G2 as Group>::Scalar>,
        G2: Group<Base = <G1 as Group>::Scalar>,
    {
        let cap_circuit: ConsistencyCircuit<<G1 as Group>::Scalar> = ConsistencyCircuit::new(
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::zero(),
            <G1 as Group>::Scalar::zero(),
        );

        // produce CAP keys
        let (cap_pk, cap_vk) =
            SpartanSNARK::<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>::setup(
                cap_circuit.clone(),
            )
            .unwrap();

        // salf for H(s||v) proof
        let salt = <G1 as Group>::Scalar::random(&mut OsRng);

        // commitment to document
        let doc_ext_len = doc.len().next_power_of_two();
        let q_len = logmn(doc_ext_len);

        let mut doc_ext: Vec<<G1 as Group>::Scalar> = doc
            .into_iter()
            .map(|x| <G1 as Group>::Scalar::from(x as u64))
            .collect();

        if doc_ext_len > doc_ext.len() {
            doc_ext.append(&mut vec![
                <G1 as Group>::Scalar::zero();
                doc_ext_len - doc_ext.len()
            ]);
        }
        let poly = MultilinearPolynomial::new(doc_ext);

        let single_gen = cap_pk.pk.gens.get_scalar_gen();

        let (_left, right) =
            EqPolynomial::<<G1 as Group>::Scalar>::compute_factored_lens(poly.get_num_vars());

        let vector_gen = CommitmentGens::<G1>::new_with_blinding_gen(
            b"vector_gen_doc",
            (2usize).pow(right as u32),
            &single_gen.get_blinding_gen(),
        );

        let hyrax_gen = HyraxPC {
            gens_v: vector_gen.clone(),
            gens_s: single_gen.clone(),
        };

        let (doc_commit, doc_decommit) = hyrax_gen.commit(&poly);

        // for in-circuit fiat shamir
        let mut ro: PoseidonRO<<G2 as Group>::Scalar, <G1 as Group>::Scalar> =
            PoseidonRO::new(PoseidonConstantsCircuit::new(), doc_commit.comm.len() * 3);
        for c in 0..doc_commit.comm.len() {
            let cc: CompressedCommitment<<G1 as Group>::CompressedGroupElement> =
                doc_commit.comm[c];
            let dc = cc.decompress().unwrap();
            dc.absorb_in_ro(&mut ro);
        }
        let commit_doc_hash = ro.squeeze(256);

        return Self {
            single_gens: single_gen.clone(),
            hyrax_gen,
            doc_poly: poly,
            doc_commit,
            doc_decommit,
            doc_commit_hash: commit_doc_hash,
            hash_salt: salt,
            cap_pk,
            cap_vk,
            q_len,
        };
    }
}

/*
#[derive(Deserialize, Serialize)]
pub struct ConsistencyProof<G1, EE1> {
    // consistency verification
    pub hash_d: <G1 as Group>::Scalar,
    circuit: ConsistencyCircuit<<G1 as Group>::Scalar>,
    pub snark: SpartanSNARK<G1, EE1, ConsistencyCircuit<<G1 as Group>::Scalar>>,
    pub v_commit: CompressedCommitment<<G1 as Group>::CompressedGroupElement>,
    // dot prod verification
    pub v_prime_commit: Option<CompressedCommitment<<G1 as Group>::CompressedGroupElement>>,
    pub ipa: InnerProductArgument<G1>,
    pub running_q: Vec<<G1 as Group>::Scalar>,
    // eq proof
    pub eq_proof: Option<EqualityProof<G1>>,
    l_commit: Option<CompressedCommitment<<G1 as Group>::CompressedGroupElement>>,
}

#[derive(Clone, Deserialize, Serialize)]
pub struct ConsistencyCircuit<F: BellPrimeField> {
    d: F,
    v: F,
    s: F,
}

impl<F: BellPrimeField> ConsistencyCircuit<F> {
    pub fn new(d: F, v: F, s: F) -> Self {
        ConsistencyCircuit { d, v, s }
    }
}

impl<F> StepCircuit<F> for ConsistencyCircuit<F>
where
    F: BellPrimeField,
{
    fn arity(&self) -> usize {
        1
    }

    fn output(&self, z: &[F]) -> Vec<F> {
        assert_eq!(z[0], self.d);
        z.to_vec()
    }

    #[allow(clippy::let_and_return)]
    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        // can't store this, bc can't be serialized
        let pc = Sponge::<F, typenum::U4>::api_constants(Strength::Standard);
        let d_in = z[0].clone();

        //v at index 0 (but technically 1 since io is allocated first)
        let alloc_v = AllocatedNum::alloc(cs.namespace(|| "v"), || Ok(self.v))?;
        let alloc_s = AllocatedNum::alloc(cs.namespace(|| "s"), || Ok(self.s))?;

        //poseidon(v,s) == d
        let d_calc = {
            let acc = &mut cs.namespace(|| "d hash circuit");
            let mut sponge = SpongeCircuit::new_with_constants(&pc, Mode::Simplex);

            sponge.start(
                IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
                None,
                acc,
            );
            SpongeAPI::absorb(
                &mut sponge,
                2,
                &[Elt::Allocated(alloc_v.clone()), Elt::Allocated(alloc_s)],
                acc,
            );

            let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
            sponge.finish(acc).unwrap();
            let out =
                Elt::ensure_allocated(&output[0], &mut acc.namespace(|| "ensure allocated"), true)?;
            out
        };

        // sanity
        if d_calc.get_value().is_some() {
            assert_eq!(d_in.get_value().unwrap(), d_calc.get_value().unwrap());
        }

        cs.enforce(
            || "d == d",
            |z| z + d_in.get_variable(),
            |z| z + CS::one(),
            |z| z + d_calc.get_variable(),
        );

        Ok(vec![d_calc]) // doesn't hugely matter
    }

    fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::Incremental
    }
}
*/
