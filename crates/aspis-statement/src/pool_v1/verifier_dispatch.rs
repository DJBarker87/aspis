//! Exact Pool V1 authenticated-verifier dispatch contract.
//!
//! The request is intended as future CPI instruction data and the result as
//! exact Solana return data.  This module only freezes and parses bytes.  It
//! does not invoke a program, read or write return data, inspect accounts, or
//! accept a proof.

use alloc::vec::Vec;
use aspis_core::{field::P, transcript::HashFn};

use crate::{decode_digest_canonical, encode_digest_canonical, poseidon2::Digest};

use super::{
    encode_historical_anchor_envelope_v1, HistoricalAnchorEnvelopeV1, PoolV1TransitionKind,
    POOL_V1_HISTORICAL_ANCHOR_VERSION, POOL_V1_LEAF_CAPACITY,
};

pub const POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC: [u8; 4] = *b"ASVQ";
pub const POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC: [u8; 4] = *b"ASVS";
pub const POOL_V1_VERIFIER_DISPATCH_VERSION: u8 = 1;
pub const POOL_V1_VERIFIER_DISPATCH_HASH_SHA256: u8 = 1;
pub const POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION: u8 = 1;
pub const POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE: u32 = 1;
pub const POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE: u32 = 0x4153_0001;
pub const POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES: usize = 384;
pub const POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES: usize = 640;
pub const POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES: usize =
    POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES;
pub const POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES: usize = 384;
pub const POOL_V1_VERIFIER_RETURN_DATA_MAX_BYTES: usize = 1_024;
pub const POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC: [u8; 4] = *b"ASPU";
pub const POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES: usize = 40;
pub const POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/historical-anchor-envelope-digest/v1";
pub const POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/profile-statement-payload-digest/v1";

const VERIFIER_PROGRAM_OFFSET: usize = 16;
const PROFILE_OFFSET: usize = 48;
const RELEASE_OFFSET: usize = 80;
const POOL_OFFSET: usize = 112;
const DEPLOYMENT_DOMAIN_OFFSET: usize = 144;
const ANCHOR_SEQUENCE_OFFSET: usize = 176;
const ANCHOR_ROOT_OFFSET: usize = 184;
const NULLIFIER_OFFSET: usize = 216;
const STATEMENT_DIGEST_OFFSET: usize = 248;
const ENVELOPE_DIGEST_OFFSET: usize = 280;
const PROOF_ACCOUNT_OFFSET: usize = 312;
const PROOF_BODY_DIGEST_OFFSET: usize = 344;
const PROOF_BODY_LENGTH_OFFSET: usize = 376;
const STATEMENT_PAYLOAD_LENGTH_OFFSET: usize = 380;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1VerifierDispatchFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongStatementVersion,
    WrongHashAlgorithm,
    WrongStatementDigestVersion,
    WrongVerifyCode,
    WrongSuccessCode,
    NonZeroReserved,
    InvalidTransitionKind,
    ZeroRequiredBinding,
    InvalidAnchorSequence,
    InvalidProofBodyLength,
    InvalidStatementPayloadLength,
    StatementPayloadDigestMismatch,
    NonCanonicalDigest,
}

/// Fields copied exactly between one verifier request and its success result.
///
/// `statement_digest` is the profile-specific digest checked by the proof
/// verifier. `envelope_digest` is SHA-256 over the domain-separated canonical
/// 208-byte `ASPA` envelope. `proof_body_digest` is raw SHA-256 of only the
/// declared proof body, excluding the frozen 40-byte `ASPU` account header.
/// `statement_payload_length` is echoed by `ASVS`; only `ASVQ` appends the
/// actual profile-specific payload after this fixed 384-byte binding prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierDispatchBindingV1 {
    pub statement_version: u8,
    pub transition_kind: PoolV1TransitionKind,
    pub verifier_program: [u8; 32],
    pub profile_binding: [u8; 32],
    pub release_binding: [u8; 32],
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub statement_digest: [u8; 32],
    pub envelope_digest: [u8; 32],
    pub proof_account: [u8; 32],
    pub proof_body_digest: [u8; 32],
    pub proof_body_length: u32,
    pub statement_payload_length: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierDispatchRequestV1<'a> {
    pub binding: VerifierDispatchBindingV1,
    pub statement_payload: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifierDispatchResultV1 {
    pub success_code: u32,
    pub binding: VerifierDispatchBindingV1,
}

fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

pub fn validate_verifier_dispatch_binding_v1(
    binding: &VerifierDispatchBindingV1,
) -> Result<(), PoolV1VerifierDispatchFormatError> {
    if binding.statement_version != POOL_V1_HISTORICAL_ANCHOR_VERSION {
        return Err(PoolV1VerifierDispatchFormatError::WrongStatementVersion);
    }
    if binding.verifier_program == [0u8; 32]
        || binding.profile_binding == [0u8; 32]
        || binding.release_binding == [0u8; 32]
        || binding.pool == [0u8; 32]
        || binding.deployment_domain == [0u8; 32]
        || binding.proof_account == [0u8; 32]
    {
        return Err(PoolV1VerifierDispatchFormatError::ZeroRequiredBinding);
    }
    if binding.anchor_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1VerifierDispatchFormatError::InvalidAnchorSequence);
    }
    if binding.proof_body_length == 0 {
        return Err(PoolV1VerifierDispatchFormatError::InvalidProofBodyLength);
    }
    if binding.statement_payload_length == 0
        || binding.statement_payload_length as usize > POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES
    {
        return Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength);
    }
    if !digest_is_canonical(&binding.anchor_root) || !digest_is_canonical(&binding.nullifier) {
        return Err(PoolV1VerifierDispatchFormatError::NonCanonicalDigest);
    }
    Ok(())
}

/// SHA-256 of the exact canonical `ASPA` v1 envelope under an explicit domain.
pub fn historical_anchor_envelope_digest_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    hash: HashFn,
) -> Result<[u8; 32], PoolV1VerifierDispatchFormatError> {
    let encoded = encode_historical_anchor_envelope_v1(envelope)
        .map_err(|_| PoolV1VerifierDispatchFormatError::NonCanonicalDigest)?;
    Ok(hash(&[
        POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_DIGEST_DOMAIN,
        &encoded,
    ]))
}

/// Raw SHA-256 convention already used by frozen proof-body artifacts.
pub fn verifier_proof_body_digest_v1(proof_body: &[u8], hash: HashFn) -> [u8; 32] {
    hash(&[proof_body])
}

/// Frozen profile-selected statement digest. Payload semantics remain owned
/// by the selected profile/release, while this generic wrapper binds the exact
/// bytes, their length and the registry-selected profile identity.
pub fn verifier_statement_payload_digest_v1(
    statement_version: u8,
    profile_binding: &[u8; 32],
    release_binding: &[u8; 32],
    statement_payload: &[u8],
    hash: HashFn,
) -> Result<[u8; 32], PoolV1VerifierDispatchFormatError> {
    if statement_version != POOL_V1_HISTORICAL_ANCHOR_VERSION {
        return Err(PoolV1VerifierDispatchFormatError::WrongStatementVersion);
    }
    if statement_payload.is_empty()
        || statement_payload.len() > POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES
        || profile_binding == &[0u8; 32]
        || release_binding == &[0u8; 32]
    {
        return Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength);
    }
    let digest_version = [POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION];
    let statement_version = [statement_version];
    let payload_length = (statement_payload.len() as u32).to_le_bytes();
    Ok(hash(&[
        POOL_V1_VERIFIER_STATEMENT_PAYLOAD_DIGEST_DOMAIN,
        &digest_version,
        &statement_version,
        profile_binding,
        release_binding,
        &payload_length,
        statement_payload,
    ]))
}

pub fn verifier_dispatch_binding_from_envelope_v1(
    verifier_program: [u8; 32],
    envelope: &HistoricalAnchorEnvelopeV1,
    statement_payload: &[u8],
    proof_account: [u8; 32],
    proof_body_digest: [u8; 32],
    proof_body_length: u32,
    hash: HashFn,
) -> Result<VerifierDispatchBindingV1, PoolV1VerifierDispatchFormatError> {
    let statement_digest = verifier_statement_payload_digest_v1(
        POOL_V1_HISTORICAL_ANCHOR_VERSION,
        &envelope.verifier_profile,
        &envelope.verifier_release,
        statement_payload,
        hash,
    )?;
    let envelope_digest = historical_anchor_envelope_digest_v1(envelope, hash)?;
    let binding = VerifierDispatchBindingV1 {
        statement_version: POOL_V1_HISTORICAL_ANCHOR_VERSION,
        transition_kind: envelope.transition_kind,
        verifier_program,
        profile_binding: envelope.verifier_profile,
        release_binding: envelope.verifier_release,
        pool: envelope.pool,
        deployment_domain: envelope.deployment_domain,
        anchor_sequence: envelope.anchor_sequence,
        anchor_root: envelope.anchor_root,
        nullifier: envelope.nullifier,
        statement_digest,
        envelope_digest,
        proof_account,
        proof_body_digest,
        proof_body_length,
        statement_payload_length: statement_payload.len() as u32,
    };
    validate_verifier_dispatch_binding_v1(&binding)?;
    Ok(binding)
}

fn encode_binding_fields(
    output: &mut [u8; POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES],
    binding: &VerifierDispatchBindingV1,
) {
    output[4] = POOL_V1_VERIFIER_DISPATCH_VERSION;
    output[5] = binding.statement_version;
    output[6] = binding.transition_kind as u8;
    output[7] = POOL_V1_VERIFIER_DISPATCH_HASH_SHA256;
    output[12] = POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION;
    output[VERIFIER_PROGRAM_OFFSET..PROFILE_OFFSET].copy_from_slice(&binding.verifier_program);
    output[PROFILE_OFFSET..RELEASE_OFFSET].copy_from_slice(&binding.profile_binding);
    output[RELEASE_OFFSET..POOL_OFFSET].copy_from_slice(&binding.release_binding);
    output[POOL_OFFSET..DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&binding.pool);
    output[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET]
        .copy_from_slice(&binding.deployment_domain);
    output[ANCHOR_SEQUENCE_OFFSET..ANCHOR_ROOT_OFFSET]
        .copy_from_slice(&binding.anchor_sequence.to_le_bytes());
    output[ANCHOR_ROOT_OFFSET..NULLIFIER_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&binding.anchor_root));
    output[NULLIFIER_OFFSET..STATEMENT_DIGEST_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&binding.nullifier));
    output[STATEMENT_DIGEST_OFFSET..ENVELOPE_DIGEST_OFFSET]
        .copy_from_slice(&binding.statement_digest);
    output[ENVELOPE_DIGEST_OFFSET..PROOF_ACCOUNT_OFFSET].copy_from_slice(&binding.envelope_digest);
    output[PROOF_ACCOUNT_OFFSET..PROOF_BODY_DIGEST_OFFSET].copy_from_slice(&binding.proof_account);
    output[PROOF_BODY_DIGEST_OFFSET..PROOF_BODY_LENGTH_OFFSET]
        .copy_from_slice(&binding.proof_body_digest);
    output[PROOF_BODY_LENGTH_OFFSET..STATEMENT_PAYLOAD_LENGTH_OFFSET]
        .copy_from_slice(&binding.proof_body_length.to_le_bytes());
    output[STATEMENT_PAYLOAD_LENGTH_OFFSET..]
        .copy_from_slice(&binding.statement_payload_length.to_le_bytes());
}

fn decode_transition_kind(
    value: u8,
) -> Result<PoolV1TransitionKind, PoolV1VerifierDispatchFormatError> {
    match value {
        1 => Ok(PoolV1TransitionKind::PrivateTransfer),
        2 => Ok(PoolV1TransitionKind::Withdrawal),
        _ => Err(PoolV1VerifierDispatchFormatError::InvalidTransitionKind),
    }
}

fn decode_binding_fields(
    bytes: &[u8; POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES],
) -> Result<VerifierDispatchBindingV1, PoolV1VerifierDispatchFormatError> {
    if bytes[4] != POOL_V1_VERIFIER_DISPATCH_VERSION {
        return Err(PoolV1VerifierDispatchFormatError::WrongVersion);
    }
    if bytes[5] != POOL_V1_HISTORICAL_ANCHOR_VERSION {
        return Err(PoolV1VerifierDispatchFormatError::WrongStatementVersion);
    }
    let transition_kind = decode_transition_kind(bytes[6])?;
    if bytes[7] != POOL_V1_VERIFIER_DISPATCH_HASH_SHA256 {
        return Err(PoolV1VerifierDispatchFormatError::WrongHashAlgorithm);
    }
    if bytes[12] != POOL_V1_VERIFIER_STATEMENT_DIGEST_VERSION {
        return Err(PoolV1VerifierDispatchFormatError::WrongStatementDigestVersion);
    }
    if bytes[13..16] != [0u8; 3] {
        return Err(PoolV1VerifierDispatchFormatError::NonZeroReserved);
    }
    let anchor_root = decode_digest_canonical(
        bytes[ANCHOR_ROOT_OFFSET..NULLIFIER_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1VerifierDispatchFormatError::NonCanonicalDigest)?;
    let nullifier = decode_digest_canonical(
        bytes[NULLIFIER_OFFSET..STATEMENT_DIGEST_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1VerifierDispatchFormatError::NonCanonicalDigest)?;
    let binding = VerifierDispatchBindingV1 {
        statement_version: bytes[5],
        transition_kind,
        verifier_program: bytes[VERIFIER_PROGRAM_OFFSET..PROFILE_OFFSET]
            .try_into()
            .unwrap(),
        profile_binding: bytes[PROFILE_OFFSET..RELEASE_OFFSET].try_into().unwrap(),
        release_binding: bytes[RELEASE_OFFSET..POOL_OFFSET].try_into().unwrap(),
        pool: bytes[POOL_OFFSET..DEPLOYMENT_DOMAIN_OFFSET]
            .try_into()
            .unwrap(),
        deployment_domain: bytes[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET]
            .try_into()
            .unwrap(),
        anchor_sequence: u64::from_le_bytes(
            bytes[ANCHOR_SEQUENCE_OFFSET..ANCHOR_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        anchor_root,
        nullifier,
        statement_digest: bytes[STATEMENT_DIGEST_OFFSET..ENVELOPE_DIGEST_OFFSET]
            .try_into()
            .unwrap(),
        envelope_digest: bytes[ENVELOPE_DIGEST_OFFSET..PROOF_ACCOUNT_OFFSET]
            .try_into()
            .unwrap(),
        proof_account: bytes[PROOF_ACCOUNT_OFFSET..PROOF_BODY_DIGEST_OFFSET]
            .try_into()
            .unwrap(),
        proof_body_digest: bytes[PROOF_BODY_DIGEST_OFFSET..PROOF_BODY_LENGTH_OFFSET]
            .try_into()
            .unwrap(),
        proof_body_length: u32::from_le_bytes(
            bytes[PROOF_BODY_LENGTH_OFFSET..STATEMENT_PAYLOAD_LENGTH_OFFSET]
                .try_into()
                .unwrap(),
        ),
        statement_payload_length: u32::from_le_bytes(
            bytes[STATEMENT_PAYLOAD_LENGTH_OFFSET..].try_into().unwrap(),
        ),
    };
    validate_verifier_dispatch_binding_v1(&binding)?;
    Ok(binding)
}

pub fn encode_verifier_dispatch_request_v1(
    request: &VerifierDispatchRequestV1<'_>,
    hash: HashFn,
) -> Result<Vec<u8>, PoolV1VerifierDispatchFormatError> {
    validate_verifier_dispatch_binding_v1(&request.binding)?;
    if request.statement_payload.len() != request.binding.statement_payload_length as usize {
        return Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength);
    }
    let expected_digest = verifier_statement_payload_digest_v1(
        request.binding.statement_version,
        &request.binding.profile_binding,
        &request.binding.release_binding,
        request.statement_payload,
        hash,
    )?;
    if expected_digest != request.binding.statement_digest {
        return Err(PoolV1VerifierDispatchFormatError::StatementPayloadDigestMismatch);
    }
    let total_length = POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES
        .checked_add(request.statement_payload.len())
        .ok_or(PoolV1VerifierDispatchFormatError::WrongLength)?;
    if total_length > POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES {
        return Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength);
    }
    let mut prefix = [0u8; POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES];
    prefix[..4].copy_from_slice(&POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC);
    prefix[8..12].copy_from_slice(&POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE.to_le_bytes());
    encode_binding_fields(&mut prefix, &request.binding);
    let mut output = Vec::with_capacity(total_length);
    output.extend_from_slice(&prefix);
    output.extend_from_slice(request.statement_payload);
    Ok(output)
}

pub fn decode_verifier_dispatch_request_v1(
    bytes: &[u8],
    hash: HashFn,
) -> Result<VerifierDispatchRequestV1<'_>, PoolV1VerifierDispatchFormatError> {
    if bytes.len() < POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES
        || bytes.len() > POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES
    {
        return Err(PoolV1VerifierDispatchFormatError::WrongLength);
    }
    let prefix: &[u8; POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES] = bytes
        [..POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES]
        .try_into()
        .map_err(|_| PoolV1VerifierDispatchFormatError::WrongLength)?;
    if prefix[..4] != POOL_V1_VERIFIER_DISPATCH_REQUEST_MAGIC {
        return Err(PoolV1VerifierDispatchFormatError::WrongMagic);
    }
    if u32::from_le_bytes(prefix[8..12].try_into().unwrap())
        != POOL_V1_VERIFIER_DISPATCH_VERIFY_CODE
    {
        return Err(PoolV1VerifierDispatchFormatError::WrongVerifyCode);
    }
    let binding = decode_binding_fields(prefix)?;
    let payload = &bytes[POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES..];
    if payload.len() != binding.statement_payload_length as usize {
        return Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength);
    }
    if verifier_statement_payload_digest_v1(
        binding.statement_version,
        &binding.profile_binding,
        &binding.release_binding,
        payload,
        hash,
    )? != binding.statement_digest
    {
        return Err(PoolV1VerifierDispatchFormatError::StatementPayloadDigestMismatch);
    }
    Ok(VerifierDispatchRequestV1 {
        binding,
        statement_payload: payload,
    })
}

pub fn encode_verifier_dispatch_result_v1(
    result: &VerifierDispatchResultV1,
) -> Result<[u8; POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES], PoolV1VerifierDispatchFormatError> {
    if result.success_code != POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE {
        return Err(PoolV1VerifierDispatchFormatError::WrongSuccessCode);
    }
    validate_verifier_dispatch_binding_v1(&result.binding)?;
    let mut output = [0u8; POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC);
    output[8..12].copy_from_slice(&result.success_code.to_le_bytes());
    encode_binding_fields(&mut output, &result.binding);
    Ok(output)
}

pub fn decode_verifier_dispatch_result_v1(
    bytes: &[u8],
) -> Result<VerifierDispatchResultV1, PoolV1VerifierDispatchFormatError> {
    let bytes: &[u8; POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES] = bytes
        .try_into()
        .map_err(|_| PoolV1VerifierDispatchFormatError::WrongLength)?;
    if bytes[..4] != POOL_V1_VERIFIER_DISPATCH_RESULT_MAGIC {
        return Err(PoolV1VerifierDispatchFormatError::WrongMagic);
    }
    let success_code = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    if success_code != POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE {
        return Err(PoolV1VerifierDispatchFormatError::WrongSuccessCode);
    }
    Ok(VerifierDispatchResultV1 {
        success_code,
        binding: decode_binding_fields(bytes)?,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use sha2::{Digest as _, Sha256};

    use super::*;

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        let mut hash = Sha256::new();
        for input in inputs {
            hash.update(input);
        }
        hash.finalize().into()
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 13 * index as u32))
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

    const PAYLOAD: &[u8] = b"profile-specific-statement-v1";

    fn binding(payload: &[u8]) -> VerifierDispatchBindingV1 {
        let envelope = envelope();
        verifier_dispatch_binding_from_envelope_v1(
            [5u8; 32],
            &envelope,
            payload,
            [7u8; 32],
            verifier_proof_body_digest_v1(b"proof", sha256),
            5,
            sha256,
        )
        .unwrap()
    }

    #[test]
    fn request_is_384_byte_prefix_plus_payload_and_result_echoes_binding_only() {
        let binding = binding(PAYLOAD);
        let request = VerifierDispatchRequestV1 {
            binding,
            statement_payload: PAYLOAD,
        };
        let result = VerifierDispatchResultV1 {
            success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
            binding,
        };
        let request_bytes = encode_verifier_dispatch_request_v1(&request, sha256).unwrap();
        let result_bytes = encode_verifier_dispatch_result_v1(&result).unwrap();
        assert_eq!(
            request_bytes.len(),
            POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + PAYLOAD.len()
        );
        assert_eq!(result_bytes.len(), 384);
        assert_eq!(&request_bytes[..4], b"ASVQ");
        assert_eq!(&result_bytes[..4], b"ASVS");
        let decoded_request = decode_verifier_dispatch_request_v1(&request_bytes, sha256).unwrap();
        assert_eq!(decoded_request, request);
        assert_eq!(
            decode_verifier_dispatch_result_v1(&result_bytes),
            Ok(result)
        );
        assert_eq!(
            decode_verifier_dispatch_result_v1(&result_bytes)
                .unwrap()
                .binding,
            decoded_request.binding
        );
        assert_eq!(decoded_request.statement_payload, PAYLOAD);
        assert_eq!(binding.statement_payload_length, PAYLOAD.len() as u32);
        assert!(POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES <= POOL_V1_VERIFIER_RETURN_DATA_MAX_BYTES);
        assert!(request_bytes.len() <= POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES);
    }

    #[test]
    fn header_code_hash_reserved_and_canonical_fields_fail_closed() {
        let encoded = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
            success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
            binding: binding(PAYLOAD),
        })
        .unwrap();
        let cases = [
            (4, 2, PoolV1VerifierDispatchFormatError::WrongVersion),
            (
                5,
                2,
                PoolV1VerifierDispatchFormatError::WrongStatementVersion,
            ),
            (
                6,
                0,
                PoolV1VerifierDispatchFormatError::InvalidTransitionKind,
            ),
            (7, 2, PoolV1VerifierDispatchFormatError::WrongHashAlgorithm),
            (
                12,
                2,
                PoolV1VerifierDispatchFormatError::WrongStatementDigestVersion,
            ),
            (13, 1, PoolV1VerifierDispatchFormatError::NonZeroReserved),
        ];
        for (offset, value, expected) in cases {
            let mut changed = encoded;
            changed[offset] = value;
            assert_eq!(decode_verifier_dispatch_result_v1(&changed), Err(expected));
        }

        let mut wrong_code = encoded;
        wrong_code[8..12].copy_from_slice(&0u32.to_le_bytes());
        assert_eq!(
            decode_verifier_dispatch_result_v1(&wrong_code),
            Err(PoolV1VerifierDispatchFormatError::WrongSuccessCode)
        );
        let mut noncanonical = encoded;
        noncanonical[ANCHOR_ROOT_OFFSET..ANCHOR_ROOT_OFFSET + 4].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_verifier_dispatch_result_v1(&noncanonical),
            Err(PoolV1VerifierDispatchFormatError::NonCanonicalDigest)
        );

        let mut zero_payload = encoded;
        zero_payload[STATEMENT_PAYLOAD_LENGTH_OFFSET..].fill(0);
        assert_eq!(
            decode_verifier_dispatch_result_v1(&zero_payload),
            Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength)
        );
    }

    #[test]
    fn envelope_proof_and_statement_digests_change_on_changed_bytes() {
        let original = envelope();
        let original_digest = historical_anchor_envelope_digest_v1(&original, sha256).unwrap();
        let changed = HistoricalAnchorEnvelopeV1 {
            anchor_sequence: original.anchor_sequence + 1,
            ..original
        };
        assert_ne!(
            historical_anchor_envelope_digest_v1(&changed, sha256).unwrap(),
            original_digest
        );
        assert_ne!(
            verifier_proof_body_digest_v1(b"proof", sha256),
            verifier_proof_body_digest_v1(b"proof!", sha256)
        );
        assert_ne!(
            verifier_statement_payload_digest_v1(1, &[3u8; 32], &[4u8; 32], PAYLOAD, sha256)
                .unwrap(),
            verifier_statement_payload_digest_v1(
                1,
                &[3u8; 32],
                &[4u8; 32],
                b"profile-specific-statement-v2",
                sha256,
            )
            .unwrap()
        );
    }

    #[test]
    fn request_rejects_zero_oversize_length_mismatch_and_payload_substitution() {
        let payload_binding = binding(PAYLOAD);
        assert_eq!(
            encode_verifier_dispatch_request_v1(
                &VerifierDispatchRequestV1 {
                    binding: payload_binding,
                    statement_payload: b"",
                },
                sha256,
            ),
            Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength)
        );

        let oversized = [0x55u8; POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES + 1];
        assert_eq!(
            verifier_statement_payload_digest_v1(1, &[3u8; 32], &[4u8; 32], &oversized, sha256,),
            Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength)
        );

        let max_payload = [0x44u8; POOL_V1_VERIFIER_STATEMENT_PAYLOAD_MAX_BYTES];
        let max_binding = binding(&max_payload);
        let max_encoded = encode_verifier_dispatch_request_v1(
            &VerifierDispatchRequestV1 {
                binding: max_binding,
                statement_payload: &max_payload,
            },
            sha256,
        )
        .unwrap();
        assert_eq!(
            max_encoded.len(),
            POOL_V1_VERIFIER_DISPATCH_REQUEST_MAX_BYTES
        );

        let request = VerifierDispatchRequestV1 {
            binding: payload_binding,
            statement_payload: PAYLOAD,
        };
        let encoded = encode_verifier_dispatch_request_v1(&request, sha256).unwrap();
        let mut changed_payload = encoded.clone();
        *changed_payload.last_mut().unwrap() ^= 1;
        assert_eq!(
            decode_verifier_dispatch_request_v1(&changed_payload, sha256),
            Err(PoolV1VerifierDispatchFormatError::StatementPayloadDigestMismatch)
        );

        let mut changed_length = encoded;
        changed_length
            [STATEMENT_PAYLOAD_LENGTH_OFFSET..POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES]
            .copy_from_slice(&((PAYLOAD.len() as u32) + 1).to_le_bytes());
        assert_eq!(
            decode_verifier_dispatch_request_v1(&changed_length, sha256),
            Err(PoolV1VerifierDispatchFormatError::InvalidStatementPayloadLength)
        );
    }
}
