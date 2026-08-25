//! Exact Pool V1 historical-anchor envelope.
//!
//! This is a statement-side binding only.  It does not prove membership,
//! authenticate a retained-root account, check nullifier freshness, invoke a
//! verifier, or mutate Pool state.  The Pool program performs those actions
//! in separate, ordered layers.

use aspis_core::field::P;

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_LEAF_CAPACITY};

pub const POOL_V1_HISTORICAL_ANCHOR_MAGIC: [u8; 4] = *b"ASPA";
pub const POOL_V1_HISTORICAL_ANCHOR_VERSION: u8 = 1;
pub const POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES: usize = 208;

const ENVELOPE_POOL_OFFSET: usize = 8;
const ENVELOPE_DEPLOYMENT_DOMAIN_OFFSET: usize = 40;
const ENVELOPE_SEQUENCE_OFFSET: usize = 72;
const ENVELOPE_ROOT_OFFSET: usize = 80;
const ENVELOPE_NULLIFIER_OFFSET: usize = 112;
const ENVELOPE_PROFILE_OFFSET: usize = 144;
const ENVELOPE_RELEASE_OFFSET: usize = 176;

/// Spend shapes that consume an authenticated historical anchor.
///
/// Zero is deliberately invalid.  Deposit is absent because it consumes no
/// private input and therefore must never authorize through this envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PoolV1TransitionKind {
    PrivateTransfer = 1,
    Withdrawal = 2,
}

impl PoolV1TransitionKind {
    fn decode(value: u8) -> Result<Self, PoolV1HistoricalAnchorFormatError> {
        match value {
            1 => Ok(Self::PrivateTransfer),
            2 => Ok(Self::Withdrawal),
            _ => Err(PoolV1HistoricalAnchorFormatError::InvalidTransitionKind),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1HistoricalAnchorFormatError {
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

/// Fixed statement envelope shared by future Pool V1 spend proof profiles.
///
/// Output commitments, fees and withdrawal fields live in the transition's
/// separately versioned statement body.  These 208 bytes pin the common
/// authorization context that the Pool must compare with retained history and
/// the exact active verifier-registry selection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoricalAnchorEnvelopeV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub verifier_profile: [u8; 32],
    pub verifier_release: [u8; 32],
}

fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

pub fn validate_historical_anchor_envelope_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
) -> Result<(), PoolV1HistoricalAnchorFormatError> {
    if envelope.pool == [0u8; 32]
        || envelope.deployment_domain == [0u8; 32]
        || envelope.verifier_profile == [0u8; 32]
        || envelope.verifier_release == [0u8; 32]
    {
        return Err(PoolV1HistoricalAnchorFormatError::ZeroRequiredBinding);
    }
    if envelope.anchor_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1HistoricalAnchorFormatError::InvalidAnchorSequence);
    }
    if !digest_is_canonical(&envelope.anchor_root) || !digest_is_canonical(&envelope.nullifier) {
        return Err(PoolV1HistoricalAnchorFormatError::NonCanonicalDigest);
    }
    Ok(())
}

pub fn encode_historical_anchor_envelope_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
) -> Result<[u8; POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES], PoolV1HistoricalAnchorFormatError> {
    validate_historical_anchor_envelope_v1(envelope)?;
    let mut output = [0u8; POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES];
    output[..4].copy_from_slice(&POOL_V1_HISTORICAL_ANCHOR_MAGIC);
    output[4] = POOL_V1_HISTORICAL_ANCHOR_VERSION;
    output[5] = envelope.transition_kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[ENVELOPE_POOL_OFFSET..ENVELOPE_DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&envelope.pool);
    output[ENVELOPE_DEPLOYMENT_DOMAIN_OFFSET..ENVELOPE_SEQUENCE_OFFSET]
        .copy_from_slice(&envelope.deployment_domain);
    output[ENVELOPE_SEQUENCE_OFFSET..ENVELOPE_ROOT_OFFSET]
        .copy_from_slice(&envelope.anchor_sequence.to_le_bytes());
    output[ENVELOPE_ROOT_OFFSET..ENVELOPE_NULLIFIER_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&envelope.anchor_root));
    output[ENVELOPE_NULLIFIER_OFFSET..ENVELOPE_PROFILE_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&envelope.nullifier));
    output[ENVELOPE_PROFILE_OFFSET..ENVELOPE_RELEASE_OFFSET]
        .copy_from_slice(&envelope.verifier_profile);
    output[ENVELOPE_RELEASE_OFFSET..].copy_from_slice(&envelope.verifier_release);
    Ok(output)
}

pub fn decode_historical_anchor_envelope_v1(
    bytes: &[u8],
) -> Result<HistoricalAnchorEnvelopeV1, PoolV1HistoricalAnchorFormatError> {
    if bytes.len() != POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES {
        return Err(PoolV1HistoricalAnchorFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_HISTORICAL_ANCHOR_MAGIC {
        return Err(PoolV1HistoricalAnchorFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_HISTORICAL_ANCHOR_VERSION {
        return Err(PoolV1HistoricalAnchorFormatError::WrongVersion);
    }
    let transition_kind = PoolV1TransitionKind::decode(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1HistoricalAnchorFormatError::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolV1HistoricalAnchorFormatError::NonZeroReserved);
    }
    let anchor_root = decode_digest_canonical(
        bytes[ENVELOPE_ROOT_OFFSET..ENVELOPE_NULLIFIER_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1HistoricalAnchorFormatError::NonCanonicalDigest)?;
    let nullifier = decode_digest_canonical(
        bytes[ENVELOPE_NULLIFIER_OFFSET..ENVELOPE_PROFILE_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1HistoricalAnchorFormatError::NonCanonicalDigest)?;
    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind,
        pool: bytes[ENVELOPE_POOL_OFFSET..ENVELOPE_DEPLOYMENT_DOMAIN_OFFSET]
            .try_into()
            .unwrap(),
        deployment_domain: bytes[ENVELOPE_DEPLOYMENT_DOMAIN_OFFSET..ENVELOPE_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
        anchor_sequence: u64::from_le_bytes(
            bytes[ENVELOPE_SEQUENCE_OFFSET..ENVELOPE_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        anchor_root,
        nullifier,
        verifier_profile: bytes[ENVELOPE_PROFILE_OFFSET..ENVELOPE_RELEASE_OFFSET]
            .try_into()
            .unwrap(),
        verifier_release: bytes[ENVELOPE_RELEASE_OFFSET..].try_into().unwrap(),
    };
    validate_historical_anchor_envelope_v1(&envelope)?;
    Ok(envelope)
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;

    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn envelope() -> HistoricalAnchorEnvelopeV1 {
        HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 257,
            anchor_root: digest(10),
            nullifier: digest(100),
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        }
    }

    #[test]
    fn exact_208_byte_envelope_roundtrips() {
        let envelope = envelope();
        let encoded = encode_historical_anchor_envelope_v1(&envelope).unwrap();
        assert_eq!(encoded.len(), 208);
        assert_eq!(&encoded[..8], &[b'A', b'S', b'P', b'A', 1, 1, 1, 0]);
        assert_eq!(decode_historical_anchor_envelope_v1(&encoded), Ok(envelope));
    }

    #[test]
    fn decoder_fails_closed_on_header_reserved_binding_sequence_and_digest_changes() {
        let encoded = encode_historical_anchor_envelope_v1(&envelope()).unwrap();
        let cases = [
            (4, 2, PoolV1HistoricalAnchorFormatError::WrongVersion),
            (
                5,
                0,
                PoolV1HistoricalAnchorFormatError::InvalidTransitionKind,
            ),
            (6, 2, PoolV1HistoricalAnchorFormatError::WrongDigestEncoding),
            (7, 1, PoolV1HistoricalAnchorFormatError::NonZeroReserved),
        ];
        for (offset, value, expected) in cases {
            let mut changed = encoded;
            changed[offset] = value;
            assert_eq!(
                decode_historical_anchor_envelope_v1(&changed),
                Err(expected)
            );
        }

        let mut changed = encoded;
        changed[ENVELOPE_POOL_OFFSET..ENVELOPE_DEPLOYMENT_DOMAIN_OFFSET].fill(0);
        assert_eq!(
            decode_historical_anchor_envelope_v1(&changed),
            Err(PoolV1HistoricalAnchorFormatError::ZeroRequiredBinding)
        );

        let mut changed = encoded;
        changed[ENVELOPE_SEQUENCE_OFFSET..ENVELOPE_ROOT_OFFSET]
            .copy_from_slice(&(POOL_V1_LEAF_CAPACITY + 1).to_le_bytes());
        assert_eq!(
            decode_historical_anchor_envelope_v1(&changed),
            Err(PoolV1HistoricalAnchorFormatError::InvalidAnchorSequence)
        );

        let mut changed = encoded;
        changed[ENVELOPE_ROOT_OFFSET..ENVELOPE_ROOT_OFFSET + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_historical_anchor_envelope_v1(&changed),
            Err(PoolV1HistoricalAnchorFormatError::NonCanonicalDigest)
        );
    }

    #[test]
    fn withdrawal_kind_and_terminal_sequence_are_explicitly_supported() {
        let changed = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            anchor_sequence: POOL_V1_LEAF_CAPACITY,
            ..envelope()
        };
        let encoded = encode_historical_anchor_envelope_v1(&changed).unwrap();
        assert_eq!(encoded[5], 2);
        assert_eq!(decode_historical_anchor_envelope_v1(&encoded), Ok(changed));
    }
}
