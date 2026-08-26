//! Pool-selected ASVQ handler for the frozen Tag-73 read-only payment profile.
//!
//! This profile verifies exactly the existing same-private-path
//! `AtomicPaymentStatementV4` relation. It does not claim the Pool historical-
//! anchor, append-only output, withdrawal, or future 1-to-2 P3/P4 relations.
//! No Pool account is accepted or written.

use aspis_core::{
    v7_onefold::{
        V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_DIGEST_BYTES,
        V7_COMPACT_FRONTIER_CAP_PER_TREE, V7_COMPACT_MAX_BODY_BYTES,
    },
    HashFn,
};
use aspis_statement::{
    atomic_payment_statement_digest_v4, decode_asset_id_canonical, decode_digest_canonical,
    encode_atomic_payment_statement_v4,
    pool_v1::{
        decode_verifier_dispatch_request_v1, encode_verifier_dispatch_result_v1,
        historical_anchor_envelope_digest_v1, verifier_proof_body_digest_v1,
        HistoricalAnchorEnvelopeV1, PoolV1TransitionKind, VerifierDispatchBindingV1,
        VerifierDispatchResultV1, POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES,
        POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
    },
    AtomicPaymentStatementV4, AtomicStatementError, SpendPublic,
    ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES, ATOMIC_PAYMENT_STATEMENT_VERSION,
    ATOMIC_PAYMENT_TREE_DEPTH,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program, program_error::ProgramError,
    pubkey::Pubkey,
};

use crate::{
    lifecycle::{proof_account_finalized, uploaded_proof_bounds},
    v7_transaction::V7_RELEASE_BINDING,
};

pub const V7_POOL_TAG73_PROFILE_PAYLOAD_MAGIC: [u8; 4] = *b"A7P1";
pub const V7_POOL_TAG73_PROFILE_PAYLOAD_VERSION: u8 = 1;
pub const V7_POOL_TAG73_PROOF_SOURCE_SEALED_ASPU: u8 = 1;
pub const V7_POOL_TAG73_CHECK_ALL_WORK: u8 = 1;
/// Smallest binary authentication frontier for 16 distinct leaves in a
/// depth-18 tree (the 16 leaves form one complete depth-four subtree).
pub const V7_POOL_TAG73_MIN_FRONTIER_NODES: u16 = 14;
/// Frozen cap, retained under the original public name for source consumers.
pub const V7_POOL_TAG73_FRONTIER_NODES: u16 = V7_COMPACT_FRONTIER_CAP_PER_TREE as u16;
/// Frozen maximum body size, retained under the original public name.
pub const V7_POOL_TAG73_PROOF_BODY_BYTES: u32 = V7_COMPACT_MAX_BODY_BYTES as u32;
pub const V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES: usize = 392;
pub const V7_POOL_TAG73_PROFILE_BINDING_PREIMAGE: &[u8] =
    b"aspis:pool-v1:verifier-profile:tag73-read-only-atomic-payment-v4:asvq-v1";

/// SHA-256 of `V7_POOL_TAG73_PROFILE_BINDING_PREIMAGE`.
pub const V7_POOL_TAG73_PROFILE_BINDING: [u8; 32] = [
    0x34, 0x99, 0x2c, 0x19, 0x2a, 0xec, 0xf5, 0x26, 0x2a, 0xd2, 0xa7, 0x8f, 0x5c, 0x7e, 0x07, 0x5c,
    0x81, 0x67, 0x3f, 0x5c, 0xa3, 0x8e, 0xec, 0x22, 0x78, 0x41, 0xf7, 0x27, 0x8a, 0x2b, 0xc1, 0xc1,
];

const FRONTIER_OFFSET: usize = 8;
const PROOF_LENGTH_OFFSET: usize = 12;
const PROOF_DIGEST_OFFSET: usize = 16;
const PROGRAM_OFFSET: usize = 48;
const RELEASE_OFFSET: usize = 80;
const ATTEMPT_OFFSET: usize = 112;
const STATEMENT_DIGEST_OFFSET: usize = 144;
const STATEMENT_OFFSET: usize = 176;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V7PoolTag73ProfileFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongProofSource,
    WorkChecksRequired,
    WrongStatementVersion,
    NonZeroReserved,
    WrongFrontierCount,
    WrongProofLength,
    ZeroRequiredBinding,
    WrongRelease,
    NonCanonicalStatement,
    StatementDigestMismatch,
}

/// Canonical compact proof length for a transcript-derived frontier count.
/// Both C1 and C2 use the same frontier count and 208-bit digest width.
pub const fn v7_pool_tag73_proof_body_bytes(frontier_nodes: u16) -> Option<u32> {
    if frontier_nodes < V7_POOL_TAG73_MIN_FRONTIER_NODES
        || frontier_nodes > V7_POOL_TAG73_FRONTIER_NODES
    {
        return None;
    }
    Some(
        V7_COMPACT_BODY_WITHOUT_FRONTIERS as u32
            + 2 * frontier_nodes as u32 * V7_COMPACT_DIGEST_BYTES as u32,
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V7PoolTag73ProfilePayloadV1 {
    pub frontier_nodes: u16,
    pub proof_body_length: u32,
    pub proof_body_digest: [u8; 32],
    pub verifier_program: [u8; 32],
    pub release_binding: [u8; 32],
    pub attempt_id: [u8; 32],
    pub statement_digest: [u8; 32],
    pub statement: AtomicPaymentStatementV4,
    pub check_pow: bool,
}

fn required_binding_is_zero(binding: &[u8; 32]) -> bool {
    binding.iter().all(|byte| *byte == 0)
}

fn map_statement_error(_: AtomicStatementError) -> V7PoolTag73ProfileFormatError {
    V7PoolTag73ProfileFormatError::NonCanonicalStatement
}

fn decode_atomic_payment_statement_v4(
    bytes: &[u8; ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES],
) -> Result<AtomicPaymentStatementV4, V7PoolTag73ProfileFormatError> {
    if bytes[0] != ATOMIC_PAYMENT_STATEMENT_VERSION
        || bytes[1] != ATOMIC_PAYMENT_TREE_DEPTH as u8
        || bytes[2..8] != [0u8; 6]
    {
        return Err(V7PoolTag73ProfileFormatError::NonCanonicalStatement);
    }
    let statement = AtomicPaymentStatementV4 {
        pool: bytes[8..40].try_into().unwrap(),
        sequence: u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
        spend: SpendPublic {
            anchor: decode_digest_canonical(bytes[48..80].try_into().unwrap())
                .map_err(map_statement_error)?,
            nullifier: decode_digest_canonical(bytes[80..112].try_into().unwrap())
                .map_err(map_statement_error)?,
            output_commitment: decode_digest_canonical(bytes[112..144].try_into().unwrap())
                .map_err(map_statement_error)?,
            asset_id: decode_asset_id_canonical(u32::from_le_bytes(
                bytes[176..180].try_into().unwrap(),
            ))
            .map_err(map_statement_error)?,
            fee: u32::from_le_bytes(bytes[180..184].try_into().unwrap()),
        },
        output_anchor: decode_digest_canonical(bytes[144..176].try_into().unwrap())
            .map_err(map_statement_error)?,
        deployment_domain: bytes[184..216].try_into().unwrap(),
    };
    let canonical = encode_atomic_payment_statement_v4(&statement).map_err(map_statement_error)?;
    if canonical != *bytes {
        return Err(V7PoolTag73ProfileFormatError::NonCanonicalStatement);
    }
    Ok(statement)
}

fn validate_profile_payload_v1(
    payload: &V7PoolTag73ProfilePayloadV1,
    hash: HashFn,
) -> Result<[u8; ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES], V7PoolTag73ProfileFormatError> {
    let expected_length = v7_pool_tag73_proof_body_bytes(payload.frontier_nodes)
        .ok_or(V7PoolTag73ProfileFormatError::WrongFrontierCount)?;
    if payload.proof_body_length != expected_length {
        return Err(V7PoolTag73ProfileFormatError::WrongProofLength);
    }
    if required_binding_is_zero(&payload.verifier_program)
        || required_binding_is_zero(&payload.attempt_id)
        || required_binding_is_zero(&payload.proof_body_digest)
        || required_binding_is_zero(&payload.statement_digest)
    {
        return Err(V7PoolTag73ProfileFormatError::ZeroRequiredBinding);
    }
    if payload.release_binding != V7_RELEASE_BINDING {
        return Err(V7PoolTag73ProfileFormatError::WrongRelease);
    }
    if !payload.check_pow {
        return Err(V7PoolTag73ProfileFormatError::WorkChecksRequired);
    }
    let statement =
        encode_atomic_payment_statement_v4(&payload.statement).map_err(map_statement_error)?;
    let expected = atomic_payment_statement_digest_v4(&payload.statement, hash)
        .map_err(map_statement_error)?;
    if expected != payload.statement_digest {
        return Err(V7PoolTag73ProfileFormatError::StatementDigestMismatch);
    }
    Ok(statement)
}

pub fn encode_v7_pool_tag73_profile_payload_v1(
    payload: &V7PoolTag73ProfilePayloadV1,
    hash: HashFn,
) -> Result<[u8; V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES], V7PoolTag73ProfileFormatError> {
    let statement = validate_profile_payload_v1(payload, hash)?;
    let mut output = [0u8; V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES];
    output[..4].copy_from_slice(&V7_POOL_TAG73_PROFILE_PAYLOAD_MAGIC);
    output[4] = V7_POOL_TAG73_PROFILE_PAYLOAD_VERSION;
    output[5] = V7_POOL_TAG73_PROOF_SOURCE_SEALED_ASPU;
    output[6] = V7_POOL_TAG73_CHECK_ALL_WORK;
    output[7] = ATOMIC_PAYMENT_STATEMENT_VERSION;
    output[FRONTIER_OFFSET..FRONTIER_OFFSET + 2]
        .copy_from_slice(&payload.frontier_nodes.to_le_bytes());
    output[PROOF_LENGTH_OFFSET..PROOF_DIGEST_OFFSET]
        .copy_from_slice(&payload.proof_body_length.to_le_bytes());
    output[PROOF_DIGEST_OFFSET..PROGRAM_OFFSET].copy_from_slice(&payload.proof_body_digest);
    output[PROGRAM_OFFSET..RELEASE_OFFSET].copy_from_slice(&payload.verifier_program);
    output[RELEASE_OFFSET..ATTEMPT_OFFSET].copy_from_slice(&payload.release_binding);
    output[ATTEMPT_OFFSET..STATEMENT_DIGEST_OFFSET].copy_from_slice(&payload.attempt_id);
    output[STATEMENT_DIGEST_OFFSET..STATEMENT_OFFSET].copy_from_slice(&payload.statement_digest);
    output[STATEMENT_OFFSET..].copy_from_slice(&statement);
    Ok(output)
}

pub fn decode_v7_pool_tag73_profile_payload_v1(
    bytes: &[u8],
    hash: HashFn,
) -> Result<V7PoolTag73ProfilePayloadV1, V7PoolTag73ProfileFormatError> {
    let bytes: &[u8; V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES] = bytes
        .try_into()
        .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?;
    if bytes[..4] != V7_POOL_TAG73_PROFILE_PAYLOAD_MAGIC {
        return Err(V7PoolTag73ProfileFormatError::WrongMagic);
    }
    if bytes[4] != V7_POOL_TAG73_PROFILE_PAYLOAD_VERSION {
        return Err(V7PoolTag73ProfileFormatError::WrongVersion);
    }
    if bytes[5] != V7_POOL_TAG73_PROOF_SOURCE_SEALED_ASPU {
        return Err(V7PoolTag73ProfileFormatError::WrongProofSource);
    }
    if bytes[6] != V7_POOL_TAG73_CHECK_ALL_WORK {
        return Err(V7PoolTag73ProfileFormatError::WorkChecksRequired);
    }
    if bytes[7] != ATOMIC_PAYMENT_STATEMENT_VERSION {
        return Err(V7PoolTag73ProfileFormatError::WrongStatementVersion);
    }
    if bytes[10..12] != [0u8; 2] {
        return Err(V7PoolTag73ProfileFormatError::NonZeroReserved);
    }
    let statement_bytes: &[u8; ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES] = bytes[STATEMENT_OFFSET..]
        .try_into()
        .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?;
    let statement = decode_atomic_payment_statement_v4(statement_bytes)?;
    let payload = V7PoolTag73ProfilePayloadV1 {
        frontier_nodes: u16::from_le_bytes(
            bytes[FRONTIER_OFFSET..FRONTIER_OFFSET + 2]
                .try_into()
                .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        ),
        proof_body_length: u32::from_le_bytes(
            bytes[PROOF_LENGTH_OFFSET..PROOF_DIGEST_OFFSET]
                .try_into()
                .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        ),
        proof_body_digest: bytes[PROOF_DIGEST_OFFSET..PROGRAM_OFFSET]
            .try_into()
            .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        verifier_program: bytes[PROGRAM_OFFSET..RELEASE_OFFSET]
            .try_into()
            .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        release_binding: bytes[RELEASE_OFFSET..ATTEMPT_OFFSET]
            .try_into()
            .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        attempt_id: bytes[ATTEMPT_OFFSET..STATEMENT_DIGEST_OFFSET]
            .try_into()
            .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        statement_digest: bytes[STATEMENT_DIGEST_OFFSET..STATEMENT_OFFSET]
            .try_into()
            .map_err(|_| V7PoolTag73ProfileFormatError::WrongLength)?,
        statement,
        check_pow: true,
    };
    validate_profile_payload_v1(&payload, hash)?;
    Ok(payload)
}

fn statement_matches_dispatch_binding(
    statement: &AtomicPaymentStatementV4,
    binding: &VerifierDispatchBindingV1,
) -> bool {
    binding.transition_kind == PoolV1TransitionKind::PrivateTransfer
        && statement.pool == binding.pool
        && statement.sequence == binding.anchor_sequence
        && statement.spend.anchor == binding.anchor_root
        && statement.spend.nullifier == binding.nullifier
        && statement.deployment_domain == binding.deployment_domain
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_v7_pool_tag73_asvq_with_runtime<F>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    hash: HashFn,
    verify: F,
) -> Result<VerifierDispatchBindingV1, ProgramError>
where
    F: FnOnce(
        &[u8],
        usize,
        &Pubkey,
        [u8; 32],
        &Pubkey,
        &AtomicPaymentStatementV4,
        [u8; 32],
        bool,
    ) -> ProgramResult,
{
    let [proof_account] = accounts else {
        return Err(if accounts.is_empty() {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    if proof_account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if proof_account.is_signer || proof_account.is_writable || proof_account.executable {
        return Err(ProgramError::InvalidAccountData);
    }

    let request = decode_verifier_dispatch_request_v1(instruction_data, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if request.binding.verifier_program != program_id.to_bytes() {
        return Err(ProgramError::IncorrectProgramId);
    }
    if request.binding.profile_binding != V7_POOL_TAG73_PROFILE_BINDING
        || request.binding.release_binding != V7_RELEASE_BINDING
        || request.binding.transition_kind != PoolV1TransitionKind::PrivateTransfer
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    if request.binding.proof_account != proof_account.key.to_bytes() {
        return Err(ProgramError::InvalidArgument);
    }

    let payload = decode_v7_pool_tag73_profile_payload_v1(request.statement_payload, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if payload.verifier_program != request.binding.verifier_program
        || payload.release_binding != request.binding.release_binding
        || payload.attempt_id != request.binding.proof_account
        || payload.proof_body_length != request.binding.proof_body_length
        || payload.proof_body_digest != request.binding.proof_body_digest
        || !statement_matches_dispatch_binding(&payload.statement, &request.binding)
    {
        return Err(ProgramError::InvalidInstructionData);
    }

    let envelope = HistoricalAnchorEnvelopeV1 {
        transition_kind: request.binding.transition_kind,
        pool: request.binding.pool,
        deployment_domain: request.binding.deployment_domain,
        anchor_sequence: request.binding.anchor_sequence,
        anchor_root: request.binding.anchor_root,
        nullifier: request.binding.nullifier,
        verifier_profile: request.binding.profile_binding,
        verifier_release: request.binding.release_binding,
    };
    let envelope_digest = historical_anchor_envelope_digest_v1(&envelope, hash)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if envelope_digest != request.binding.envelope_digest {
        return Err(ProgramError::InvalidInstructionData);
    }

    let data = proof_account.try_borrow_data()?;
    if !proof_account_finalized(&data) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (proof_start, proof_end) = uploaded_proof_bounds(&data)?;
    if proof_end != data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let proof = &data[proof_start..proof_end];
    if proof.len() != payload.proof_body_length as usize
        || verifier_proof_body_digest_v1(proof, hash) != request.binding.proof_body_digest
    {
        return Err(ProgramError::InvalidAccountData);
    }

    let attempt_id = *proof_account.key;
    verify(
        proof,
        usize::from(payload.frontier_nodes),
        program_id,
        payload.release_binding,
        &attempt_id,
        &payload.statement,
        payload.statement_digest,
        payload.check_pow,
    )?;

    Ok(request.binding)
}

fn process_v7_pool_tag73_asvq_instruction_with_runtime<F, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
    hash: HashFn,
    verify: F,
    set_return_data: S,
) -> ProgramResult
where
    F: FnOnce(
        &[u8],
        usize,
        &Pubkey,
        [u8; 32],
        &Pubkey,
        &AtomicPaymentStatementV4,
        [u8; 32],
        bool,
    ) -> ProgramResult,
    S: FnOnce(&[u8]),
{
    let binding = verify_v7_pool_tag73_asvq_with_runtime(
        program_id,
        accounts,
        instruction_data,
        hash,
        verify,
    )?;

    let result = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
        success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        binding,
    })
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    let _: &[u8; POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES] = &result;
    set_return_data(&result);
    Ok(())
}

/// Verify the exact frozen Tag-73 read-only payment profile and set ASVS only
/// after full acceptance. This handler has no Pool/state account and performs
/// no account write.
pub fn process_v7_pool_tag73_asvq_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    process_v7_pool_tag73_asvq_instruction_with_runtime(
        program_id,
        accounts,
        instruction_data,
        crate::verify::sbf_hashv,
        |proof,
         frontier_nodes,
         program_id,
         release_binding,
         attempt_id,
         statement,
         statement_digest,
         check_pow| {
            crate::v7_verifier::verify_v7_read_only_with_statement_digest(
                crate::verify::sbf_hashv,
                proof,
                frontier_nodes,
                program_id,
                release_binding,
                attempt_id,
                statement,
                statement_digest,
                check_pow,
            )
            .map_err(|_| ProgramError::InvalidAccountData)?;
            Ok(())
        },
        program::set_return_data,
    )
}

#[cfg(test)]
mod tests {
    use core::{cell::Cell, str::FromStr};
    use std::{cell::RefCell, vec, vec::Vec};

    use aspis_core::field::{M31, P};
    use aspis_statement::{
        encode_digest_canonical,
        pool_v1::{
            decode_verifier_dispatch_request_v1, decode_verifier_dispatch_result_v1,
            encode_verifier_dispatch_request_v1, verifier_dispatch_binding_from_envelope_v1,
            POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES,
            POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
        },
    };
    use solana_program::clock::Epoch;

    use super::*;

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        solana_program::hash::hashv(inputs).to_bytes()
    }

    fn digest(seed: u32) -> aspis_statement::Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn synthetic_statement(pool: Pubkey) -> AtomicPaymentStatementV4 {
        AtomicPaymentStatementV4 {
            pool: pool.to_bytes(),
            sequence: 7,
            spend: SpendPublic {
                anchor: digest(10),
                nullifier: digest(100),
                output_commitment: digest(200),
                asset_id: M31(17),
                fee: 1,
            },
            output_anchor: digest(300),
            deployment_domain: [0x44u8; 32],
        }
    }

    #[derive(Clone)]
    struct Fixture {
        program_id: Pubkey,
        proof_key: Pubkey,
        statement: AtomicPaymentStatementV4,
        envelope: HistoricalAnchorEnvelopeV1,
        profile: V7PoolTag73ProfilePayloadV1,
        payload: [u8; V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES],
        request: Vec<u8>,
        proof_body: Vec<u8>,
        proof_data: Vec<u8>,
    }

    fn request_for(
        fixture: &Fixture,
        envelope: &HistoricalAnchorEnvelopeV1,
        payload: &[u8],
        proof_body_digest: [u8; 32],
        proof_body_length: u32,
    ) -> Vec<u8> {
        let binding = verifier_dispatch_binding_from_envelope_v1(
            fixture.program_id.to_bytes(),
            envelope,
            payload,
            fixture.proof_key.to_bytes(),
            proof_body_digest,
            proof_body_length,
            sha256,
        )
        .unwrap();
        encode_verifier_dispatch_request_v1(
            &aspis_statement::pool_v1::VerifierDispatchRequestV1 {
                binding,
                statement_payload: payload,
            },
            sha256,
        )
        .unwrap()
    }

    fn fixture_from(
        program_id: Pubkey,
        proof_key: Pubkey,
        statement: AtomicPaymentStatementV4,
        frontier_nodes: u16,
        proof_body: Vec<u8>,
    ) -> Fixture {
        let proof_body_length = v7_pool_tag73_proof_body_bytes(frontier_nodes).unwrap();
        assert_eq!(proof_body.len(), proof_body_length as usize);
        let proof_body_digest = verifier_proof_body_digest_v1(&proof_body, sha256);
        let statement_digest = atomic_payment_statement_digest_v4(&statement, sha256).unwrap();
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: statement.pool,
            deployment_domain: statement.deployment_domain,
            anchor_sequence: statement.sequence,
            anchor_root: statement.spend.anchor,
            nullifier: statement.spend.nullifier,
            verifier_profile: V7_POOL_TAG73_PROFILE_BINDING,
            verifier_release: V7_RELEASE_BINDING,
        };
        let profile = V7PoolTag73ProfilePayloadV1 {
            frontier_nodes,
            proof_body_length,
            proof_body_digest,
            verifier_program: program_id.to_bytes(),
            release_binding: V7_RELEASE_BINDING,
            attempt_id: proof_key.to_bytes(),
            statement_digest,
            statement: statement.clone(),
            check_pow: true,
        };
        let payload = encode_v7_pool_tag73_profile_payload_v1(&profile, sha256).unwrap();
        let mut fixture = Fixture {
            program_id,
            proof_key,
            statement,
            envelope,
            profile,
            payload,
            request: Vec::new(),
            proof_body,
            proof_data: Vec::new(),
        };
        fixture.request = request_for(
            &fixture,
            &fixture.envelope,
            &fixture.payload,
            proof_body_digest,
            proof_body_length,
        );
        fixture.proof_data =
            vec![0u8; POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES + proof_body_length as usize];
        fixture.proof_data[..4].copy_from_slice(&POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC);
        fixture.proof_data[4..8].copy_from_slice(&proof_body_length.to_le_bytes());
        fixture.proof_data[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES..]
            .copy_from_slice(&fixture.proof_body);
        fixture
    }

    fn synthetic_fixture() -> Fixture {
        let program_id = crate::id();
        let proof_key = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let proof_body = (0..V7_POOL_TAG73_PROOF_BODY_BYTES as usize)
            .map(|index| (index as u8).wrapping_mul(29).wrapping_add(7))
            .collect();
        fixture_from(
            program_id,
            proof_key,
            synthetic_statement(pool),
            V7_POOL_TAG73_FRONTIER_NODES,
            proof_body,
        )
    }

    #[derive(Clone, Copy, Default)]
    struct AccountConfusion {
        wrong_key: bool,
        wrong_owner: bool,
        signer: bool,
        writable: bool,
        executable: bool,
        extra: bool,
    }

    struct HarnessResult {
        result: ProgramResult,
        verify_calls: usize,
        returned: Vec<u8>,
    }

    fn run_injected(
        fixture: &Fixture,
        request: &[u8],
        proof_data: &mut [u8],
        confusion: AccountConfusion,
        verifier_error: Option<ProgramError>,
    ) -> HarnessResult {
        let proof_key = if confusion.wrong_key {
            Pubkey::new_unique()
        } else {
            fixture.proof_key
        };
        let owner = if confusion.wrong_owner {
            Pubkey::new_unique()
        } else {
            fixture.program_id
        };
        let mut proof_lamports = 1;
        let proof_account = AccountInfo::new(
            &proof_key,
            confusion.signer,
            confusion.writable,
            &mut proof_lamports,
            proof_data,
            &owner,
            confusion.executable,
            Epoch::default(),
        );
        let extra_key = Pubkey::new_unique();
        let extra_owner = Pubkey::new_unique();
        let mut extra_lamports = 1;
        let mut extra_data = [];
        let extra_account = AccountInfo::new(
            &extra_key,
            false,
            false,
            &mut extra_lamports,
            &mut extra_data,
            &extra_owner,
            false,
            Epoch::default(),
        );
        let accounts = if confusion.extra {
            vec![proof_account, extra_account]
        } else {
            vec![proof_account]
        };
        let calls = Cell::new(0usize);
        let returned = RefCell::new(Vec::new());
        let result = process_v7_pool_tag73_asvq_instruction_with_runtime(
            &fixture.program_id,
            &accounts,
            request,
            sha256,
            |proof,
             frontier_nodes,
             program_id,
             release_binding,
             attempt_id,
             statement,
             statement_digest,
             check_pow| {
                calls.set(calls.get() + 1);
                assert_eq!(proof, fixture.proof_body);
                assert_eq!(frontier_nodes, usize::from(fixture.profile.frontier_nodes));
                assert_eq!(program_id, &fixture.program_id);
                assert_eq!(release_binding, V7_RELEASE_BINDING);
                assert_eq!(attempt_id, &fixture.proof_key);
                assert_eq!(statement, &fixture.statement);
                assert_eq!(statement_digest, fixture.profile.statement_digest);
                assert!(check_pow);
                match verifier_error {
                    Some(error) => Err(error),
                    None => Ok(()),
                }
            },
            |bytes| returned.borrow_mut().extend_from_slice(bytes),
        );
        HarnessResult {
            result,
            verify_calls: calls.get(),
            returned: returned.into_inner(),
        }
    }

    fn assert_rejected_before_verify(fixture: &Fixture, request: &[u8]) {
        let mut proof_data = fixture.proof_data.clone();
        let result = run_injected(
            fixture,
            request,
            &mut proof_data,
            AccountConfusion::default(),
            None,
        );
        assert!(result.result.is_err());
        assert_eq!(result.verify_calls, 0);
        assert!(result.returned.is_empty());
    }

    #[test]
    fn p3f_profile_binding_payload_and_success_result_are_exact() {
        assert_eq!(
            solana_program::hash::hash(V7_POOL_TAG73_PROFILE_BINDING_PREIMAGE).to_bytes(),
            V7_POOL_TAG73_PROFILE_BINDING
        );
        let fixture = synthetic_fixture();
        assert_eq!(fixture.payload.len(), V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES);
        assert_eq!(
            fixture.request.len(),
            POOL_V1_VERIFIER_DISPATCH_BINDING_PREFIX_BYTES + V7_POOL_TAG73_PROFILE_PAYLOAD_BYTES
        );
        let decoded = decode_v7_pool_tag73_profile_payload_v1(&fixture.payload, sha256).unwrap();
        assert_eq!(decoded, fixture.profile);

        let mut proof_data = fixture.proof_data.clone();
        let result = run_injected(
            &fixture,
            &fixture.request,
            &mut proof_data,
            AccountConfusion::default(),
            None,
        );
        assert_eq!(result.result, Ok(()));
        assert_eq!(result.verify_calls, 1);
        assert_eq!(
            result.returned.len(),
            POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES
        );
        let request = decode_verifier_dispatch_request_v1(&fixture.request, sha256).unwrap();
        let returned = decode_verifier_dispatch_result_v1(&result.returned).unwrap();
        assert_eq!(returned.binding, request.binding);
        assert_eq!(
            returned.success_code,
            POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE
        );
        assert_eq!(proof_data, fixture.proof_data);
    }

    #[test]
    fn p3f_canonical_variable_frontier_length_reaches_verifier() {
        assert_eq!(
            v7_pool_tag73_proof_body_bytes(V7_POOL_TAG73_MIN_FRONTIER_NODES),
            Some(20_676)
        );
        assert_eq!(
            v7_pool_tag73_proof_body_bytes(V7_POOL_TAG73_FRONTIER_NODES),
            Some(V7_POOL_TAG73_PROOF_BODY_BYTES)
        );
        assert_eq!(
            v7_pool_tag73_proof_body_bytes(V7_POOL_TAG73_MIN_FRONTIER_NODES - 1),
            None
        );
        assert_eq!(
            v7_pool_tag73_proof_body_bytes(V7_POOL_TAG73_FRONTIER_NODES + 1),
            None
        );

        // The current strengthened deterministic Tag-73 fixture derives a
        // 201-node first-cap schedule and therefore a 30,400-byte body.
        let frontier_nodes = 201;
        let proof_body_length = v7_pool_tag73_proof_body_bytes(frontier_nodes).unwrap();
        assert_eq!(proof_body_length, 30_400);
        let program_id = crate::id();
        let proof_key = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let proof_body = (0..proof_body_length as usize)
            .map(|index| (index as u8).wrapping_mul(31).wrapping_add(11))
            .collect();
        let fixture = fixture_from(
            program_id,
            proof_key,
            synthetic_statement(pool),
            frontier_nodes,
            proof_body,
        );
        let mut proof_data = fixture.proof_data.clone();
        let result = run_injected(
            &fixture,
            &fixture.request,
            &mut proof_data,
            AccountConfusion::default(),
            None,
        );
        assert_eq!(result.result, Ok(()));
        assert_eq!(result.verify_calls, 1);
        assert_eq!(proof_data, fixture.proof_data);
    }

    #[test]
    fn p3f_profile_release_attempt_statement_and_digest_substitutions_fail_closed() {
        let fixture = synthetic_fixture();

        let mut envelope = fixture.envelope.clone();
        envelope.verifier_profile = [0x51u8; 32];
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &envelope,
                &fixture.payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut payload = fixture.payload;
        let wrong_release = [0x52u8; 32];
        payload[RELEASE_OFFSET..ATTEMPT_OFFSET].copy_from_slice(&wrong_release);
        let mut envelope = fixture.envelope.clone();
        envelope.verifier_release = wrong_release;
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut payload = fixture.payload;
        payload[ATTEMPT_OFFSET..STATEMENT_DIGEST_OFFSET].copy_from_slice(&[0x53u8; 32]);
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut payload = fixture.payload;
        payload[PROGRAM_OFFSET..RELEASE_OFFSET].copy_from_slice(&[0x54u8; 32]);
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let decoded_request =
            decode_verifier_dispatch_request_v1(&fixture.request, sha256).unwrap();
        let mut foreign_program_binding = decoded_request.binding;
        foreign_program_binding.verifier_program = Pubkey::new_unique().to_bytes();
        let foreign_program_request = encode_verifier_dispatch_request_v1(
            &aspis_statement::pool_v1::VerifierDispatchRequestV1 {
                binding: foreign_program_binding,
                statement_payload: &fixture.payload,
            },
            sha256,
        )
        .unwrap();
        assert_rejected_before_verify(&fixture, &foreign_program_request);

        let mut payload = fixture.payload;
        payload[PROOF_DIGEST_OFFSET] ^= 1;
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut payload = fixture.payload;
        payload[PROOF_DIGEST_OFFSET..PROGRAM_OFFSET].fill(0);
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                [0u8; 32],
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut changed_profile = fixture.profile.clone();
        changed_profile.statement.pool = Pubkey::new_unique().to_bytes();
        changed_profile.statement_digest =
            atomic_payment_statement_digest_v4(&changed_profile.statement, sha256).unwrap();
        let payload = encode_v7_pool_tag73_profile_payload_v1(&changed_profile, sha256).unwrap();
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut payload = fixture.payload;
        payload[STATEMENT_DIGEST_OFFSET] ^= 1;
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );
    }

    #[test]
    fn p3f_proof_frontier_work_trailing_zero_and_noncanonical_substitutions_fail_closed() {
        let fixture = synthetic_fixture();

        let mut changed_proof = fixture.proof_data.clone();
        changed_proof[POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES] ^= 1;
        let result = run_injected(
            &fixture,
            &fixture.request,
            &mut changed_proof,
            AccountConfusion::default(),
            None,
        );
        assert_eq!(result.result, Err(ProgramError::InvalidAccountData));
        assert_eq!(result.verify_calls, 0);
        assert!(result.returned.is_empty());

        for (offset, value) in [
            (FRONTIER_OFFSET, 202u16.to_le_bytes()),
            (FRONTIER_OFFSET, 204u16.to_le_bytes()),
        ] {
            let mut payload = fixture.payload;
            payload[offset..offset + 2].copy_from_slice(&value);
            assert_rejected_before_verify(
                &fixture,
                &request_for(
                    &fixture,
                    &fixture.envelope,
                    &payload,
                    fixture.profile.proof_body_digest,
                    V7_POOL_TAG73_PROOF_BODY_BYTES,
                ),
            );
        }

        let mut payload = fixture.payload;
        payload[6] = 0;
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut trailing = fixture.request.clone();
        trailing.push(0);
        assert_rejected_before_verify(&fixture, &trailing);

        let mut payload = fixture.payload;
        payload[ATTEMPT_OFFSET..STATEMENT_DIGEST_OFFSET].fill(0);
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );

        let mut payload = fixture.payload;
        payload[STATEMENT_OFFSET + 48..STATEMENT_OFFSET + 52].copy_from_slice(&P.to_le_bytes());
        assert_rejected_before_verify(
            &fixture,
            &request_for(
                &fixture,
                &fixture.envelope,
                &payload,
                fixture.profile.proof_body_digest,
                V7_POOL_TAG73_PROOF_BODY_BYTES,
            ),
        );
    }

    #[test]
    fn p3f_proof_framing_account_confusion_and_verifier_failure_set_no_result() {
        let fixture = synthetic_fixture();
        let cases = [
            AccountConfusion {
                wrong_key: true,
                ..AccountConfusion::default()
            },
            AccountConfusion {
                wrong_owner: true,
                ..AccountConfusion::default()
            },
            AccountConfusion {
                signer: true,
                ..AccountConfusion::default()
            },
            AccountConfusion {
                writable: true,
                ..AccountConfusion::default()
            },
            AccountConfusion {
                executable: true,
                ..AccountConfusion::default()
            },
            AccountConfusion {
                extra: true,
                ..AccountConfusion::default()
            },
        ];
        for confusion in cases {
            let mut proof_data = fixture.proof_data.clone();
            let result = run_injected(&fixture, &fixture.request, &mut proof_data, confusion, None);
            assert!(result.result.is_err());
            assert_eq!(result.verify_calls, 0);
            assert!(result.returned.is_empty());
        }

        for mutation in 0..3 {
            let mut proof_data = fixture.proof_data.clone();
            match mutation {
                0 => proof_data[0] ^= 1,
                1 => proof_data[8] = 1,
                _ => proof_data[4..8]
                    .copy_from_slice(&(V7_POOL_TAG73_PROOF_BODY_BYTES - 1).to_le_bytes()),
            }
            let result = run_injected(
                &fixture,
                &fixture.request,
                &mut proof_data,
                AccountConfusion::default(),
                None,
            );
            assert!(result.result.is_err());
            assert_eq!(result.verify_calls, 0);
            assert!(result.returned.is_empty());
        }

        let mut trailing_proof_data = fixture.proof_data.clone();
        trailing_proof_data.push(0);
        let result = run_injected(
            &fixture,
            &fixture.request,
            &mut trailing_proof_data,
            AccountConfusion::default(),
            None,
        );
        assert_eq!(result.result, Err(ProgramError::InvalidAccountData));
        assert_eq!(result.verify_calls, 0);
        assert!(result.returned.is_empty());

        let mut proof_data = fixture.proof_data.clone();
        let result = run_injected(
            &fixture,
            &fixture.request,
            &mut proof_data,
            AccountConfusion::default(),
            Some(ProgramError::InvalidAccountData),
        );
        assert_eq!(result.result, Err(ProgramError::InvalidAccountData));
        assert_eq!(result.verify_calls, 1);
        assert!(result.returned.is_empty());
    }

    fn hex32(value: &str) -> [u8; 32] {
        assert_eq!(value.len(), 64);
        let mut output = [0u8; 32];
        for (index, byte) in output.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
        }
        output
    }

    fn digest_from_hex(value: &str) -> aspis_statement::Digest {
        decode_digest_canonical(&hex32(value)).unwrap()
    }

    #[test]
    fn p3f_frozen_full_c2_proof_accepts_through_actual_tag73_verifier_once() {
        let program_id = crate::id();
        let proof_key = Pubkey::from_str("97dyPnMkxRwsS2X8rBdosa7q35fXmMAyCMffhCuvao31").unwrap();
        let pool = Pubkey::from_str("5xoNdKpsAf19Bdgg1RtDeuV1X9vNHoU4GQSviEY46vqH").unwrap();
        let statement = AtomicPaymentStatementV4 {
            pool: pool.to_bytes(),
            sequence: 0,
            spend: SpendPublic {
                anchor: digest_from_hex(
                    "c804c93a175fc43e4b80e157a0e8301c9c9d831acdd79311e1310c5be6640361",
                ),
                nullifier: digest_from_hex(
                    "f801ce369536cf1fa9a789505cb9146b26556f78ffd9aa486c6f025002c6bc19",
                ),
                output_commitment: digest_from_hex(
                    "9704310b89b5737d8be98f36e4cf330668b85e58af4e1f07425b9e7b30ab6c2a",
                ),
                asset_id: M31(17),
                fee: 1,
            },
            output_anchor: digest_from_hex(
                "6d3255363dfd2e0d41e58d46c82679529b31cd2a3e35dc1599aada5fd2f5f25f",
            ),
            deployment_domain: hex32(
                "0f8a800b72fcf5a061f8ef9420815a4af69e097a80bb2148a26c59873a73f241",
            ),
        };
        let proof_body =
            include_bytes!("../../../results/spend/v7-devnet-20260825-fullc2/v7-proof.bin")
                .to_vec();
        assert_eq!(
            verifier_proof_body_digest_v1(&proof_body, sha256),
            hex32("e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb")
        );
        let fixture = fixture_from(
            program_id,
            proof_key,
            statement,
            V7_POOL_TAG73_FRONTIER_NODES,
            proof_body,
        );
        let mut proof_data = fixture.proof_data.clone();
        let mut lamports = 1;
        let proof_account = AccountInfo::new(
            &proof_key,
            false,
            false,
            &mut lamports,
            &mut proof_data,
            &program_id,
            false,
            Epoch::default(),
        );
        let returned = RefCell::new(Vec::new());
        let result = process_v7_pool_tag73_asvq_instruction_with_runtime(
            &program_id,
            &[proof_account],
            &fixture.request,
            sha256,
            |proof,
             frontier_nodes,
             program_id,
             release_binding,
             attempt_id,
             statement,
             statement_digest,
             check_pow| {
                crate::v7_verifier::verify_v7_read_only_with_statement_digest(
                    sha256,
                    proof,
                    frontier_nodes,
                    program_id,
                    release_binding,
                    attempt_id,
                    statement,
                    statement_digest,
                    check_pow,
                )
                .map_err(|_| ProgramError::InvalidAccountData)?;
                Ok(())
            },
            |bytes| returned.borrow_mut().extend_from_slice(bytes),
        );
        assert_eq!(result, Ok(()));
        assert_eq!(
            returned.into_inner().len(),
            POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES
        );
    }

    #[test]
    fn p3f_asvq_magic_routes_before_legacy_numeric_tag65() {
        let fixture = synthetic_fixture();
        let mut proof_data = fixture.proof_data.clone();
        let mut lamports = 1;
        let proof_account = AccountInfo::new(
            &fixture.proof_key,
            false,
            false,
            &mut lamports,
            &mut proof_data,
            &fixture.program_id,
            false,
            Epoch::default(),
        );
        assert_eq!(
            crate::dispatch::process_spend_production_instruction(
                &fixture.program_id,
                &[proof_account],
                &fixture.request,
            ),
            Err(ProgramError::InvalidAccountData)
        );
    }

    #[test]
    fn p3f_canonical_digest_encoding_matches_statement_bytes() {
        let fixture = synthetic_fixture();
        let statement = encode_atomic_payment_statement_v4(&fixture.statement).unwrap();
        assert_eq!(
            &statement[48..80],
            &encode_digest_canonical(&fixture.statement.spend.anchor)
        );
    }
}
