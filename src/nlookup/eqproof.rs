use ff::Field;
use nova_snark::{
    errors::NovaError,
    pedersen::{Commitment, CommitmentKey},
    traits::{Engine, TranscriptEngineTrait},
};
use serde::{Deserialize, Serialize};

/// EqualityProof
#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct EqualityProof<E: Engine> {
    /// alpha
    pub alpha: Commitment<E>,
    /// z
    pub z: E::Scalar,
}

/// EqualityProof
impl<E: Engine> EqualityProof<E> {
    /// protocol name
    pub fn protocol_name() -> &'static [u8] {
        b"equality proof"
    }

    /// prove
    pub fn prove(
        gens_n: &CommitmentKey<E>,
        transcript: &mut E::TE,
        v1: &E::Scalar,
        s1: &E::Scalar,
        v2: &E::Scalar,
        s2: &E::Scalar,
    ) -> Result<(EqualityProof<E>, Commitment<E>, Commitment<E>), NovaError> {
        transcript.dom_sep(Self::protocol_name());

        // produce a random scalar
        let r = E::Scalar::random(&mut OsRng);

        let C1 = CE::<E>::commit(gens_n, &[*v1], s1);
        transcript.absorb(b"C1", C1);

        let C2 = CE::<E>::commit(gens_n, &[*v2], s2);
        transcript.absorb(b"C2", C2);

        let alpha = CE::<E>::commit(gens_n, &[G::Scalar::zero()], &r); // h^r
        transcript.absorb(b"alpha", alpha);

        let c = transcript.squeeze(b"c")?;

        let z = c * (*s1 - *s2) + r;

        Ok((Self { alpha, z }, C1, C2))
    }

    /// verify
    pub fn verify(
        &self,
        gens_n: &CommitmentKey<E>,
        transcript: &mut E::TE,
        C1: &Commitment<E>,
        C2: &Commitment<E>,
    ) -> Result<(), NovaError> {
        transcript.dom_sep(Self::protocol_name());
        transcript.absorb(b"C1", C1);
        transcript.absorb(b"C2", C2);
        transcript.absorb(b"alpha", self.alpha);

        let c = transcript.squeeze(b"c")?;

        let rhs = {
            let C = C1 - C2;
            C * c + self.alpha
        };

        let lhs = CE::<E>::commit(gens_n, &[E::Scalar::zero()], &self.z); // h^z

        if lhs == rhs {
            Ok(())
        } else {
            Err(NovaError::InvalidEqualityProof)
        }
    }
}
