//! Exact Pool V1 consumed-nullifier marker image.
//!
//! A marker is written only after a separately authenticated proof/transition
//! succeeds.  This pure module freezes the occupied account bytes and PDA seed
//! inputs; it does not create accounts, check Solana ownership, or authorize a
//! state transition.

use aspis_core::field::P;

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{
    HistoricalAnchorEnvelopeV1, PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION,
    POOL_V1_LEAF_CAPACITY,
};

pub const POOL_V1_NULLIFIER_MARKER_MAGIC: [u8; 4] = *b"ASNM";
pub const POOL_V1_NULLIFIER_MARKER_VERSION: u8 = 1;
pub const POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES: usize = 208;
pub const POOL_V1_NULLIFIER_MARKER_SEED: &[u8] = b"aspis-pool-nullifier-v1";

const MARKER_POOL_OFFSET: usize = 8;
const MARKER_DEPLOYMENT_DOMAIN_OFFSET: usize = 40;
const MARKER_NULLIFIER_OFFSET: usize = 72;
const MARKER_ANCHOR_SEQUENCE_OFFSET: usize = 104;
const MARKER_ANCHOR_ROOT_OFFSET: usize = 112;
const MARKER_PROFILE_OFFSET: usize = 144;
const MARKER_RELEASE_OFFSET: usize = 176;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1NullifierMarkerFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongDigestEncoding,
    NonZeroReserved,
    InvalidTransitionKind,
    ZeroRequiredBinding,
    InvalidAnchorSequence,
    NonCanonicalDigest,
}

/// Immutable evidence that one exact Pool V1 authorization context consumed
/// its public nullifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1NullifierMarkerV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub nullifier: Digest,
    pub retained_anchor_sequence: u64,
    pub retained_anchor_root: Digest,
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
}

impl PoolV1NullifierMarkerV1 {
    /// Exact marker payload derived from the already-versioned common spend
    /// envelope.  No field is reinterpreted or omitted.
    pub fn from_historical_anchor(envelope: &HistoricalAnchorEnvelopeV1) -> Self {
        Self {
            transition_kind: envelope.transition_kind,
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            nullifier: envelope.nullifier,
            retained_anchor_sequence: envelope.anchor_sequence,
            retained_anchor_root: envelope.anchor_root,
            verifier_profile: envelope.verifier_profile,
            verifier_release: envelope.verifier_release,
        }
    }

    /// The third PDA seed is exactly this canonical 32-byte encoding.
    pub fn canonical_nullifier_encoding(self) -> [u8; 32] {
        encode_digest_canonical(&self.nullifier)
    }
}

fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

pub fn validate_pool_v1_nullifier_marker(
    marker: &PoolV1NullifierMarkerV1,
) -> Result<(), PoolV1NullifierMarkerFormatError> {
    if marker.pool == [0u8; 32]
        || marker.deployment_domain == [0u8; 32]
        || marker.verifier_profile == [0u8; 32]
        || marker.verifier_release == [0u8; 32]
    {
        return Err(PoolV1NullifierMarkerFormatError::ZeroRequiredBinding);
    }
    if marker.retained_anchor_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1NullifierMarkerFormatError::InvalidAnchorSequence);
    }
    if !digest_is_canonical(&marker.nullifier) || !digest_is_canonical(&marker.retained_anchor_root)
    {
        return Err(PoolV1NullifierMarkerFormatError::NonCanonicalDigest);
    }
    Ok(())
}

pub fn encode_pool_v1_nullifier_marker(
    marker: &PoolV1NullifierMarkerV1,
) -> Result<[u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES], PoolV1NullifierMarkerFormatError> {
    validate_pool_v1_nullifier_marker(marker)?;
    let mut output = [0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_NULLIFIER_MARKER_MAGIC);
    output[4] = POOL_V1_NULLIFIER_MARKER_VERSION;
    output[5] = marker.transition_kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[MARKER_POOL_OFFSET..MARKER_DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&marker.pool);
    output[MARKER_DEPLOYMENT_DOMAIN_OFFSET..MARKER_NULLIFIER_OFFSET]
        .copy_from_slice(&marker.deployment_domain);
    output[MARKER_NULLIFIER_OFFSET..MARKER_ANCHOR_SEQUENCE_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&marker.nullifier));
    output[MARKER_ANCHOR_SEQUENCE_OFFSET..MARKER_ANCHOR_ROOT_OFFSET]
        .copy_from_slice(&marker.retained_anchor_sequence.to_le_bytes());
    output[MARKER_ANCHOR_ROOT_OFFSET..MARKER_PROFILE_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&marker.retained_anchor_root));
    output[MARKER_PROFILE_OFFSET..MARKER_RELEASE_OFFSET].copy_from_slice(&marker.verifier_profile);
    output[MARKER_RELEASE_OFFSET..].copy_from_slice(&marker.verifier_release);
    Ok(output)
}

pub fn decode_pool_v1_nullifier_marker(
    bytes: &[u8],
) -> Result<PoolV1NullifierMarkerV1, PoolV1NullifierMarkerFormatError> {
    if bytes.len() != POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES {
        return Err(PoolV1NullifierMarkerFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_NULLIFIER_MARKER_MAGIC {
        return Err(PoolV1NullifierMarkerFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_NULLIFIER_MARKER_VERSION {
        return Err(PoolV1NullifierMarkerFormatError::WrongVersion);
    }
    let transition_kind = match bytes[5] {
        1 => PoolV1TransitionKind::PrivateTransfer,
        2 => PoolV1TransitionKind::Withdrawal,
        _ => return Err(PoolV1NullifierMarkerFormatError::InvalidTransitionKind),
    };
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1NullifierMarkerFormatError::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolV1NullifierMarkerFormatError::NonZeroReserved);
    }
    let nullifier = decode_digest_canonical(
        bytes[MARKER_NULLIFIER_OFFSET..MARKER_ANCHOR_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1NullifierMarkerFormatError::NonCanonicalDigest)?;
    let retained_anchor_root = decode_digest_canonical(
        bytes[MARKER_ANCHOR_ROOT_OFFSET..MARKER_PROFILE_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1NullifierMarkerFormatError::NonCanonicalDigest)?;
    let marker = PoolV1NullifierMarkerV1 {
        transition_kind,
        pool: bytes[MARKER_POOL_OFFSET..MARKER_DEPLOYMENT_DOMAIN_OFFSET]
            .try_into()
            .unwrap(),
        deployment_domain: bytes[MARKER_DEPLOYMENT_DOMAIN_OFFSET..MARKER_NULLIFIER_OFFSET]
            .try_into()
            .unwrap(),
        nullifier,
        retained_anchor_sequence: u64::from_le_bytes(
            bytes[MARKER_ANCHOR_SEQUENCE_OFFSET..MARKER_ANCHOR_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        retained_anchor_root,
        verifier_profile: bytes[MARKER_PROFILE_OFFSET..MARKER_RELEASE_OFFSET]
            .try_into()
            .unwrap(),
        verifier_release: bytes[MARKER_RELEASE_OFFSET..].try_into().unwrap(),
    };
    validate_pool_v1_nullifier_marker(&marker)?;
    Ok(marker)
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;

    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 23 * index as u32))
    }

    fn marker() -> PoolV1NullifierMarkerV1 {
        PoolV1NullifierMarkerV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            nullifier: digest(10),
            retained_anchor_sequence: 257,
            retained_anchor_root: digest(100),
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        }
    }

    #[test]
    fn exact_208_byte_consumed_marker_roundtrips() {
        let marker = marker();
        let encoded = encode_pool_v1_nullifier_marker(&marker).unwrap();
        assert_eq!(encoded.len(), 208);
        assert_eq!(&encoded[..8], &[b'A', b'S', b'N', b'M', 1, 1, 1, 0]);
        assert_eq!(
            &encoded[MARKER_NULLIFIER_OFFSET..MARKER_ANCHOR_SEQUENCE_OFFSET],
            &marker.canonical_nullifier_encoding()
        );
        assert_eq!(decode_pool_v1_nullifier_marker(&encoded), Ok(marker));
    }

    #[test]
    fn marker_is_exact_field_copy_of_historical_anchor_envelope() {
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 99,
            anchor_root: digest(100),
            nullifier: digest(10),
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        };
        let marker = PoolV1NullifierMarkerV1::from_historical_anchor(&envelope);
        assert_eq!(marker.transition_kind, envelope.transition_kind);
        assert_eq!(marker.pool, envelope.pool);
        assert_eq!(marker.deployment_domain, envelope.deployment_domain);
        assert_eq!(marker.nullifier, envelope.nullifier);
        assert_eq!(marker.retained_anchor_sequence, envelope.anchor_sequence);
        assert_eq!(marker.retained_anchor_root, envelope.anchor_root);
        assert_eq!(marker.verifier_profile, envelope.verifier_profile);
        assert_eq!(marker.verifier_release, envelope.verifier_release);
    }

    #[test]
    fn decoder_rejects_type_version_reserved_sequence_and_noncanonical_digest() {
        let encoded = encode_pool_v1_nullifier_marker(&marker()).unwrap();
        let cases = [
            (4, 2, PoolV1NullifierMarkerFormatError::WrongVersion),
            (
                5,
                0,
                PoolV1NullifierMarkerFormatError::InvalidTransitionKind,
            ),
            (6, 2, PoolV1NullifierMarkerFormatError::WrongDigestEncoding),
            (7, 1, PoolV1NullifierMarkerFormatError::NonZeroReserved),
        ];
        for (offset, value, expected) in cases {
            let mut changed = encoded;
            changed[offset] = value;
            assert_eq!(decode_pool_v1_nullifier_marker(&changed), Err(expected));
        }

        let mut changed = encoded;
        changed[MARKER_ANCHOR_SEQUENCE_OFFSET..MARKER_ANCHOR_ROOT_OFFSET]
            .copy_from_slice(&(POOL_V1_LEAF_CAPACITY + 1).to_le_bytes());
        assert_eq!(
            decode_pool_v1_nullifier_marker(&changed),
            Err(PoolV1NullifierMarkerFormatError::InvalidAnchorSequence)
        );

        let mut changed = encoded;
        changed[MARKER_NULLIFIER_OFFSET..MARKER_NULLIFIER_OFFSET + 4]
            .copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_pool_v1_nullifier_marker(&changed),
            Err(PoolV1NullifierMarkerFormatError::NonCanonicalDigest)
        );
    }
}
