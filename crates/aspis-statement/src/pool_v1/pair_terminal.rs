//! Pair-Pool selected-verifier transport experiments.
//!
//! The Pool binds a finalized verifier-owned proof account by identity and
//! exact body length, not by re-hashing the 30,504-byte body. The selected
//! verifier receives that same read-only account and returns a fixed binding
//! receipt.  The stable-proof experiment returns a pair digest for an
//! execution-time append.  The conservative production candidate instead
//! returns the proof-carried root/frontier afterstate and requires no Pool-side
//! Poseidon call.

use alloc::{vec, vec::Vec};
use aspis_core::{
    field::{M31, P},
    transcript::HashFn,
};

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{
    PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_HISTORICAL_ANCHOR_VERSION,
    POOL_V1_PAIR_TREE_FORMAT_BINDING,
};

pub const POOL_V1_PAIR_VERIFIER_REQUEST_MAGIC: [u8; 4] = *b"ASJQ";
/// Conservative one-terminal request.  Unlike `ASJQ`, this request carries
/// the exact live snapshot constructed from the locked Pool account by the
/// outer Pool instruction.
pub const POOL_V1_PAIR_AFTERSTATE_VERIFIER_REQUEST_MAGIC: [u8; 4] = *b"ASJ2";
pub const POOL_V1_PAIR_VERIFIER_RESULT_MAGIC: [u8; 4] = *b"ASJR";
pub const POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION: u8 = 1;
pub const POOL_V1_PAIR_VERIFIER_SUCCESS_CODE: u32 = 0x4153_4a01;
pub const POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES: usize = 240;
pub const POOL_V1_PAIR_VERIFIER_RESULT_BYTES: usize = 40;
/// Exact payload proved from the live pair-tree snapshot.  The Pool derives
/// history routing and output note indices from `next_pair_index`, so those
/// values are intentionally not duplicated here.
pub const POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES: usize = 680;
/// Eight-byte typed envelope plus the exact 680-byte afterstate payload.
pub const POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES: usize =
    8 + POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES;
pub const POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC: [u8; 4] = *b"ASJA";
pub const POOL_V1_PAIR_STATEMENT_BINDING_DOMAIN: &[u8] =
    b"aspis/pool-v1/stable-pair-statement-binding/v1";

const PROOF_LENGTH_OFFSET: usize = 8;
const STATEMENT_LENGTH_OFFSET: usize = 12;
const VERIFIER_OFFSET: usize = 16;
const PROFILE_OFFSET: usize = 48;
const RELEASE_OFFSET: usize = 80;
const POOL_OFFSET: usize = 112;
const PROOF_OFFSET: usize = 144;
const STATEMENT_DIGEST_OFFSET: usize = 176;
const FORMAT_BINDING_OFFSET: usize = 208;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairVerifierTransportErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongStatementVersion,
    WrongDigestEncoding,
    InvalidTransitionKind,
    WrongSuccessCode,
    WrongPairFormat,
    ZeroRequiredBinding,
    InvalidProofBodyLength,
    InvalidStatementPayloadLength,
    InvalidLiveSnapshotPayloadLength,
    NonCanonicalOutputPair,
    InvalidAfterstateIndex,
    NonCanonicalAfterstate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairVerifierBindingV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub pool: [u8; 32],
    pub proof_account: [u8; 32],
    pub proof_body_length: u32,
    pub statement_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairVerifierRequestV1<'a> {
    pub binding: PoolV1PairVerifierBindingV1,
    pub statement_payload: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairAfterstateVerifierRequestV1<'a> {
    pub binding: PoolV1PairVerifierBindingV1,
    pub statement_payload: &'a [u8],
    /// Exact canonical `ASPLIVE1` bytes derived from the account locked by
    /// the same outer terminal transaction.
    pub live_snapshot_payload: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairVerifierResultV1 {
    /// The pair compression already checked inside the stable 34-block proof.
    /// The Pool consumes it directly and computes only the 20 live parents.
    pub output_pair: Digest,
}

/// Minimal proof-carried append result for the one-terminal transaction.
///
/// This is not the execution-time append experiment above.  The selected
/// verifier has checked the twenty late Poseidon parents against the exact
/// live snapshot and returns the resulting state.  The Pool performs only
/// canonical byte validation, checks `next_pair_index = current + 1`, and
/// persists these bytes atomically with history and the nullifier marker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairVerifiedAfterstateV1 {
    pub next_pair_index: u64,
    pub next_root: Digest,
    pub next_frontier: [Digest; super::POOL_V1_PAIR_TREE_DEPTH],
}

fn validate_verified_afterstate(
    afterstate: &PoolV1PairVerifiedAfterstateV1,
) -> Result<(), PoolV1PairVerifierTransportErrorV1> {
    if afterstate.next_pair_index == 0 || afterstate.next_pair_index > super::POOL_V1_PAIR_CAPACITY
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex);
    }
    if afterstate.next_root.iter().any(|limb| limb.0 >= P)
        || afterstate
            .next_frontier
            .iter()
            .flatten()
            .any(|limb| limb.0 >= P)
    {
        return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);
    }
    Ok(())
}

pub fn encode_pool_v1_pair_verified_afterstate_v1(
    afterstate: &PoolV1PairVerifiedAfterstateV1,
) -> Result<[u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES], PoolV1PairVerifierTransportErrorV1> {
    validate_verified_afterstate(afterstate)?;
    let mut output = [0u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);
    output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
    output[5] = super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = 1;
    output[8..16].copy_from_slice(&afterstate.next_pair_index.to_le_bytes());
    output[16..48].copy_from_slice(&encode_digest_canonical(&afterstate.next_root));
    for (level, node) in afterstate.next_frontier.iter().enumerate() {
        let start = 48 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }
    Ok(output)
}

pub fn decode_pool_v1_pair_verified_afterstate_v1(
    bytes: &[u8],
) -> Result<PoolV1PairVerifiedAfterstateV1, PoolV1PairVerifierTransportErrorV1> {
    if bytes.len() != POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongVersion);
    }
    if bytes[5] != super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongPairFormat);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 1 {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongSuccessCode);
    }
    let next_root = decode_digest_canonical(&exact(&bytes[16..48])?)
        .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?;
    let mut next_frontier = [[M31::ZERO; 8]; super::POOL_V1_PAIR_TREE_DEPTH];
    for (level, node) in next_frontier.iter_mut().enumerate() {
        let start = 48 + 32 * level;
        *node = decode_digest_canonical(&exact(&bytes[start..start + 32])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?;
    }
    let afterstate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: u64::from_le_bytes(exact(&bytes[8..16])?),
        next_root,
        next_frontier,
    };
    validate_verified_afterstate(&afterstate)?;
    Ok(afterstate)
}

fn exact<const N: usize>(bytes: &[u8]) -> Result<[u8; N], PoolV1PairVerifierTransportErrorV1> {
    bytes
        .try_into()
        .map_err(|_| PoolV1PairVerifierTransportErrorV1::WrongLength)
}

fn transition_kind(byte: u8) -> Result<PoolV1TransitionKind, PoolV1PairVerifierTransportErrorV1> {
    match byte {
        value if value == PoolV1TransitionKind::PrivateTransfer as u8 => {
            Ok(PoolV1TransitionKind::PrivateTransfer)
        }
        value if value == PoolV1TransitionKind::Withdrawal as u8 => {
            Ok(PoolV1TransitionKind::Withdrawal)
        }
        _ => Err(PoolV1PairVerifierTransportErrorV1::InvalidTransitionKind),
    }
}

pub fn pool_v1_pair_statement_digest_v1(payload: &[u8], hash: HashFn) -> [u8; 32] {
    hash(&[POOL_V1_PAIR_STATEMENT_BINDING_DOMAIN, payload])
}

pub fn validate_pool_v1_pair_verifier_binding_v1(
    binding: &PoolV1PairVerifierBindingV1,
) -> Result<(), PoolV1PairVerifierTransportErrorV1> {
    if binding.verifier_program == [0u8; 32]
        || binding.profile_binding == [0u8; 32]
        || binding.release_binding == [0u8; 32]
        || binding.pool == [0u8; 32]
        || binding.proof_account == [0u8; 32]
        || binding.statement_digest == [0u8; 32]
    {
        return Err(PoolV1PairVerifierTransportErrorV1::ZeroRequiredBinding);
    }
    if binding.proof_body_length == 0 {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidProofBodyLength);
    }
    Ok(())
}

fn encode_binding_header(
    magic: [u8; 4],
    binding: &PoolV1PairVerifierBindingV1,
    statement_length_or_success: u32,
) -> Result<[u8; POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES], PoolV1PairVerifierTransportErrorV1> {
    validate_pool_v1_pair_verifier_binding_v1(binding)?;
    let mut output = [0u8; POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES];
    output[..4].copy_from_slice(&magic);
    output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
    output[5] = binding.transition_kind as u8;
    output[6] = POOL_V1_HISTORICAL_ANCHOR_VERSION;
    output[7] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[PROOF_LENGTH_OFFSET..STATEMENT_LENGTH_OFFSET]
        .copy_from_slice(&binding.proof_body_length.to_le_bytes());
    output[STATEMENT_LENGTH_OFFSET..VERIFIER_OFFSET]
        .copy_from_slice(&statement_length_or_success.to_le_bytes());
    output[VERIFIER_OFFSET..PROFILE_OFFSET].copy_from_slice(&binding.verifier_program);
    output[PROFILE_OFFSET..RELEASE_OFFSET].copy_from_slice(&binding.profile_binding);
    output[RELEASE_OFFSET..POOL_OFFSET].copy_from_slice(&binding.release_binding);
    output[POOL_OFFSET..PROOF_OFFSET].copy_from_slice(&binding.pool);
    output[PROOF_OFFSET..STATEMENT_DIGEST_OFFSET].copy_from_slice(&binding.proof_account);
    output[STATEMENT_DIGEST_OFFSET..FORMAT_BINDING_OFFSET]
        .copy_from_slice(&binding.statement_digest);
    output[FORMAT_BINDING_OFFSET..].copy_from_slice(&POOL_V1_PAIR_TREE_FORMAT_BINDING);
    Ok(output)
}

fn decode_binding_header(
    bytes: &[u8],
    expected_magic: [u8; 4],
) -> Result<(PoolV1PairVerifierBindingV1, u32), PoolV1PairVerifierTransportErrorV1> {
    if bytes.len() != POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongLength);
    }
    if bytes[..4] != expected_magic {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongVersion);
    }
    if bytes[6] != POOL_V1_HISTORICAL_ANCHOR_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongStatementVersion);
    }
    if bytes[7] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding);
    }
    if bytes[FORMAT_BINDING_OFFSET..] != POOL_V1_PAIR_TREE_FORMAT_BINDING {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongPairFormat);
    }
    let binding = PoolV1PairVerifierBindingV1 {
        transition_kind: transition_kind(bytes[5])?,
        proof_body_length: u32::from_le_bytes(exact(
            &bytes[PROOF_LENGTH_OFFSET..STATEMENT_LENGTH_OFFSET],
        )?),
        verifier_program: exact(&bytes[VERIFIER_OFFSET..PROFILE_OFFSET])?,
        profile_binding: exact(&bytes[PROFILE_OFFSET..RELEASE_OFFSET])?,
        release_binding: exact(&bytes[RELEASE_OFFSET..POOL_OFFSET])?,
        pool: exact(&bytes[POOL_OFFSET..PROOF_OFFSET])?,
        proof_account: exact(&bytes[PROOF_OFFSET..STATEMENT_DIGEST_OFFSET])?,
        statement_digest: exact(&bytes[STATEMENT_DIGEST_OFFSET..FORMAT_BINDING_OFFSET])?,
    };
    validate_pool_v1_pair_verifier_binding_v1(&binding)?;
    Ok((
        binding,
        u32::from_le_bytes(exact(&bytes[STATEMENT_LENGTH_OFFSET..VERIFIER_OFFSET])?),
    ))
}

pub fn encode_pool_v1_pair_verifier_request_v1(
    request: &PoolV1PairVerifierRequestV1<'_>,
) -> Result<Vec<u8>, PoolV1PairVerifierTransportErrorV1> {
    if request.statement_payload.is_empty() || request.statement_payload.len() > u32::MAX as usize {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidStatementPayloadLength);
    }
    let header = encode_binding_header(
        POOL_V1_PAIR_VERIFIER_REQUEST_MAGIC,
        &request.binding,
        request.statement_payload.len() as u32,
    )?;
    let mut output = vec![0u8; header.len() + request.statement_payload.len()];
    output[..header.len()].copy_from_slice(&header);
    output[header.len()..].copy_from_slice(request.statement_payload);
    Ok(output)
}

pub fn decode_pool_v1_pair_verifier_request_v1(
    bytes: &[u8],
) -> Result<PoolV1PairVerifierRequestV1<'_>, PoolV1PairVerifierTransportErrorV1> {
    if bytes.len() <= POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongLength);
    }
    let (binding, statement_length) = decode_binding_header(
        &bytes[..POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES],
        POOL_V1_PAIR_VERIFIER_REQUEST_MAGIC,
    )?;
    if statement_length == 0
        || POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES.checked_add(statement_length as usize)
            != Some(bytes.len())
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidStatementPayloadLength);
    }
    Ok(PoolV1PairVerifierRequestV1 {
        binding,
        statement_payload: &bytes[POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES..],
    })
}

pub fn encode_pool_v1_pair_afterstate_verifier_request_v1(
    request: &PoolV1PairAfterstateVerifierRequestV1<'_>,
) -> Result<Vec<u8>, PoolV1PairVerifierTransportErrorV1> {
    if request.statement_payload.is_empty() || request.statement_payload.len() > u32::MAX as usize {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidStatementPayloadLength);
    }
    if request.live_snapshot_payload.len()
        != super::pair_tree_profile::POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidLiveSnapshotPayloadLength);
    }
    // Decode here so malformed account-derived bytes cannot cross the CPI
    // boundary under the typed request magic.
    super::pair_tree_profile::decode_pool_v1_pair_live_snapshot_v1(request.live_snapshot_payload)
        .map_err(|_| PoolV1PairVerifierTransportErrorV1::InvalidLiveSnapshotPayloadLength)?;
    let header = encode_binding_header(
        POOL_V1_PAIR_AFTERSTATE_VERIFIER_REQUEST_MAGIC,
        &request.binding,
        request.statement_payload.len() as u32,
    )?;
    let total = header
        .len()
        .checked_add(request.statement_payload.len())
        .and_then(|length| length.checked_add(request.live_snapshot_payload.len()))
        .ok_or(PoolV1PairVerifierTransportErrorV1::WrongLength)?;
    let mut output = vec![0u8; total];
    let statement_end = header.len() + request.statement_payload.len();
    output[..header.len()].copy_from_slice(&header);
    output[header.len()..statement_end].copy_from_slice(request.statement_payload);
    output[statement_end..].copy_from_slice(request.live_snapshot_payload);
    Ok(output)
}

pub fn decode_pool_v1_pair_afterstate_verifier_request_v1(
    bytes: &[u8],
) -> Result<PoolV1PairAfterstateVerifierRequestV1<'_>, PoolV1PairVerifierTransportErrorV1> {
    let minimum = POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES
        + 1
        + super::pair_tree_profile::POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES;
    if bytes.len() < minimum {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongLength);
    }
    let (binding, statement_length) = decode_binding_header(
        &bytes[..POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES],
        POOL_V1_PAIR_AFTERSTATE_VERIFIER_REQUEST_MAGIC,
    )?;
    let statement_length = statement_length as usize;
    let statement_end = POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES
        .checked_add(statement_length)
        .ok_or(PoolV1PairVerifierTransportErrorV1::WrongLength)?;
    if statement_length == 0
        || statement_end.checked_add(super::pair_tree_profile::POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)
            != Some(bytes.len())
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidStatementPayloadLength);
    }
    let live_snapshot_payload = &bytes[statement_end..];
    super::pair_tree_profile::decode_pool_v1_pair_live_snapshot_v1(live_snapshot_payload)
        .map_err(|_| PoolV1PairVerifierTransportErrorV1::InvalidLiveSnapshotPayloadLength)?;
    Ok(PoolV1PairAfterstateVerifierRequestV1 {
        binding,
        statement_payload: &bytes[POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES..statement_end],
        live_snapshot_payload,
    })
}

pub fn encode_pool_v1_pair_verifier_result_v1(
    result: &PoolV1PairVerifierResultV1,
) -> Result<[u8; POOL_V1_PAIR_VERIFIER_RESULT_BYTES], PoolV1PairVerifierTransportErrorV1> {
    if result.output_pair.iter().any(|limb| limb.0 >= P) {
        return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalOutputPair);
    }
    let mut output = [0u8; POOL_V1_PAIR_VERIFIER_RESULT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIER_RESULT_MAGIC);
    output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
    output[5] = POOL_V1_HISTORICAL_ANCHOR_VERSION;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = 1; // successful, proof-verified pair result
    output[8..].copy_from_slice(&encode_digest_canonical(&result.output_pair));
    Ok(output)
}

pub fn decode_pool_v1_pair_verifier_result_v1(
    bytes: &[u8],
) -> Result<PoolV1PairVerifierResultV1, PoolV1PairVerifierTransportErrorV1> {
    if bytes.len() != POOL_V1_PAIR_VERIFIER_RESULT_BYTES {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_VERIFIER_RESULT_MAGIC {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_HISTORICAL_ANCHOR_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongStatementVersion);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 1 {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongSuccessCode);
    }
    Ok(PoolV1PairVerifierResultV1 {
        output_pair: decode_digest_canonical(bytes[8..].try_into().unwrap())
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalOutputPair)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest as _, Sha256};

    fn sha256(parts: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for part in parts {
            hash.update(part);
        }
        hash.finalize().into()
    }

    fn binding() -> PoolV1PairVerifierBindingV1 {
        PoolV1PairVerifierBindingV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            verifier_program: [1u8; 32],
            profile_binding: [2u8; 32],
            release_binding: [3u8; 32],
            pool: [4u8; 32],
            proof_account: [5u8; 32],
            proof_body_length: 30_504,
            statement_digest: pool_v1_pair_statement_digest_v1(&[6u8; 216], sha256),
        }
    }

    #[test]
    fn stable_request_and_result_roundtrip_without_live_state_or_proof_digest() {
        let statement = [6u8; 216];
        let request = PoolV1PairVerifierRequestV1 {
            binding: binding(),
            statement_payload: &statement,
        };
        let encoded = encode_pool_v1_pair_verifier_request_v1(&request).unwrap();
        assert_eq!(encoded.len(), 456);
        assert_eq!(
            decode_pool_v1_pair_verifier_request_v1(&encoded),
            Ok(request)
        );
        let expected = PoolV1PairVerifierResultV1 {
            output_pair: core::array::from_fn(|lane| aspis_core::field::M31(100 + lane as u32)),
        };
        let result = encode_pool_v1_pair_verifier_result_v1(&expected).unwrap();
        assert_eq!(result.len(), 40);
        assert_eq!(
            decode_pool_v1_pair_verifier_result_v1(&result),
            Ok(expected)
        );
    }

    #[test]
    fn afterstate_request_carries_exact_account_derived_live_snapshot() {
        let statement = [6u8; 216];
        let snapshot = super::super::pair_tree_profile::PoolV1PairLiveSnapshotV1 {
            pool: [4u8; 32],
            deployment_domain: [7u8; 32],
            sequence: 19,
            next_pair_index: 19,
            current_root: core::array::from_fn(|lane| M31(100 + lane as u32)),
            frontier: core::array::from_fn(|level| {
                core::array::from_fn(|lane| M31(1_000 + 8 * level as u32 + lane as u32))
            }),
        };
        let mut live = [0u8; super::super::pair_tree_profile::POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
        super::super::pair_tree_profile::encode_pool_v1_pair_live_snapshot_v1(&snapshot, &mut live)
            .unwrap();
        let request = PoolV1PairAfterstateVerifierRequestV1 {
            binding: binding(),
            statement_payload: &statement,
            live_snapshot_payload: &live,
        };
        let encoded = encode_pool_v1_pair_afterstate_verifier_request_v1(&request).unwrap();
        assert_eq!(encoded.len(), 1_256);
        assert_eq!(
            decode_pool_v1_pair_afterstate_verifier_request_v1(&encoded),
            Ok(request)
        );

        let mut mutated = encoded;
        let live_start = POOL_V1_PAIR_VERIFIER_REQUEST_HEADER_BYTES + statement.len();
        mutated[live_start + 128] ^= 1;
        let decoded = decode_pool_v1_pair_afterstate_verifier_request_v1(&mutated).unwrap();
        assert_ne!(decoded.live_snapshot_payload, request.live_snapshot_payload);

        let trailing = [request.live_snapshot_payload, &[0u8][..]].concat();
        assert_eq!(
            encode_pool_v1_pair_afterstate_verifier_request_v1(
                &PoolV1PairAfterstateVerifierRequestV1 {
                    live_snapshot_payload: &trailing,
                    ..request
                }
            ),
            Err(PoolV1PairVerifierTransportErrorV1::InvalidLiveSnapshotPayloadLength)
        );
    }

    #[test]
    fn transport_rejects_trailing_and_mutated_pair_format() {
        let statement = [6u8; 216];
        let request = PoolV1PairVerifierRequestV1 {
            binding: binding(),
            statement_payload: &statement,
        };
        let mut encoded = encode_pool_v1_pair_verifier_request_v1(&request).unwrap();
        encoded.push(0);
        assert_eq!(
            decode_pool_v1_pair_verifier_request_v1(&encoded),
            Err(PoolV1PairVerifierTransportErrorV1::InvalidStatementPayloadLength)
        );
        let expected = PoolV1PairVerifierResultV1 {
            output_pair: core::array::from_fn(|lane| aspis_core::field::M31(100 + lane as u32)),
        };
        let mut result = encode_pool_v1_pair_verifier_result_v1(&expected).unwrap();
        result[4] ^= 1;
        assert_eq!(
            decode_pool_v1_pair_verifier_result_v1(&result),
            Err(PoolV1PairVerifierTransportErrorV1::WrongVersion)
        );
    }

    #[test]
    fn proof_carried_afterstate_is_exactly_688_bytes_and_canonical() {
        let expected = PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 123,
            next_root: core::array::from_fn(|lane| M31(100 + lane as u32)),
            next_frontier: core::array::from_fn(|level| {
                core::array::from_fn(|lane| M31(1_000 + 8 * level as u32 + lane as u32))
            }),
        };
        let encoded = encode_pool_v1_pair_verified_afterstate_v1(&expected).unwrap();
        assert_eq!(POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES, 680);
        assert_eq!(encoded.len(), 688);
        assert_eq!(
            decode_pool_v1_pair_verified_afterstate_v1(&encoded),
            Ok(expected)
        );

        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_pool_v1_pair_verified_afterstate_v1(&trailing),
            Err(PoolV1PairVerifierTransportErrorV1::WrongLength)
        );

        let mut zero_index = encoded;
        zero_index[8..16].fill(0);
        assert_eq!(
            decode_pool_v1_pair_verified_afterstate_v1(&zero_index),
            Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex)
        );
    }
}
