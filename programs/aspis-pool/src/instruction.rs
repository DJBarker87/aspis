//! Exact top-level Pool V1 instruction and successful-transition receipt wires.
//!
//! Every decoder is fixed-width (except the already-frozen bounded deposit
//! payload), rejects trailing bytes, and checks duplicated common fields.  The
//! private-transfer and withdrawal statement bodies are forwarded byte-for-
//! byte to the registry-selected verifier; the Pool applies only the outputs
//! decoded from those same bytes.

use aspis_core::field::{M31, P};
use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        decode_historical_anchor_envelope_v1, decode_verifier_policy_v1,
        encode_historical_anchor_envelope_v1, encode_verifier_policy_v1,
        HistoricalAnchorEnvelopeV1, PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION,
        POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES,
    },
    poseidon2::Digest,
    VALUE_LIMIT,
};
use solana_program::{program_error::ProgramError, pubkey::Pubkey};

use crate::{
    deposit::DepositRequestV1,
    deposit_transport::{decode_deposit_instruction_v1, DepositInstructionFormatErrorV1},
    state::PoolInitializationV1,
    vault::LEGACY_SPL_TOKEN_PROGRAM_ID,
};

pub const POOL_V1_INITIALIZE_INSTRUCTION_MAGIC: [u8; 4] = *b"ASIN";
pub const POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC: [u8; 4] = *b"ASPT";
pub const POOL_V1_PAIR_PRIVATE_TRANSFER_INSTRUCTION_MAGIC: [u8; 4] = *b"ASJP";
pub const POOL_V1_PAIR_WITHDRAWAL_INSTRUCTION_MAGIC: [u8; 4] = *b"ASJW";
pub const POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC: [u8; 4] = *b"ASWD";
pub const POOL_V1_INSTRUCTION_VERSION: u8 = 1;

pub const POOL_V1_INITIALIZE_INSTRUCTION_BYTES: usize = 184;
pub const POOL_V1_TRANSITION_STATEMENT_BYTES: usize = 216;
pub const POOL_V1_SPEND_INSTRUCTION_BYTES: usize =
    8 + POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES + POOL_V1_TRANSITION_STATEMENT_BYTES;

pub const POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC: [u8; 4] = *b"ASCP";
pub const POOL_V1_WITHDRAWAL_STATEMENT_MAGIC: [u8; 4] = *b"ASWP";
pub const POOL_V1_TRANSITION_STATEMENT_VERSION: u8 = 1;

pub const POOL_V1_INITIALIZATION_RECEIPT_MAGIC: [u8; 4] = *b"ASIR";
pub const POOL_V1_INITIALIZATION_RECEIPT_BYTES: usize = 104;
pub const POOL_V1_TRANSITION_RECEIPT_MAGIC: [u8; 4] = *b"ASTR";
pub const POOL_V1_TRANSITION_RECEIPT_BYTES: usize = 200;

const INITIALIZE_MINT_OFFSET: usize = 8;
const INITIALIZE_ASSET_ID_OFFSET: usize = 40;
const INITIALIZE_DOMAIN_OFFSET: usize = 48;
const INITIALIZE_POLICY_OFFSET: usize = 80;

const SPEND_ENVELOPE_OFFSET: usize = 8;
const SPEND_STATEMENT_OFFSET: usize =
    SPEND_ENVELOPE_OFFSET + POOL_V1_HISTORICAL_ANCHOR_ENVELOPE_BYTES;

const STATEMENT_POOL_OFFSET: usize = 8;
const STATEMENT_DOMAIN_OFFSET: usize = 40;
const STATEMENT_SEQUENCE_OFFSET: usize = 72;
const STATEMENT_ROOT_OFFSET: usize = 80;
const STATEMENT_NULLIFIER_OFFSET: usize = 112;
const STATEMENT_ASSET_ID_OFFSET: usize = 144;
const STATEMENT_FIRST_OUTPUT_OFFSET: usize = 152;
const STATEMENT_SECOND_OUTPUT_OFFSET: usize = 184;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    InvalidEnvelope,
    EnvelopeStatementMismatch,
    InvalidPolicy,
    NonCanonicalField,
    InvalidWithdrawalAmount,
    InvalidDestination,
    InvalidDeposit,
}

impl From<PoolInstructionFormatErrorV1> for ProgramError {
    fn from(_: PoolInstructionFormatErrorV1) -> Self {
        ProgramError::InvalidInstructionData
    }
}

impl From<DepositInstructionFormatErrorV1> for PoolInstructionFormatErrorV1 {
    fn from(_: DepositInstructionFormatErrorV1) -> Self {
        Self::InvalidDeposit
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateTransferStatementV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub recipient_commitment: Digest,
    pub change_commitment: Digest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawalStatementV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub amount: u32,
    pub destination_token_account: [u8; 32],
    pub change_commitment: Digest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateTransferInstructionV1<'a> {
    pub envelope: HistoricalAnchorEnvelopeV1,
    pub statement: PrivateTransferStatementV1,
    /// Exact bytes authenticated by the selected verifier.
    pub statement_payload: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawalInstructionV1<'a> {
    pub envelope: HistoricalAnchorEnvelopeV1,
    pub statement: WithdrawalStatementV1,
    /// Exact bytes authenticated by the selected verifier.
    pub statement_payload: &'a [u8],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StatementCommonV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    asset_id: M31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TransitionReceiptV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub pool: [u8; 32],
    pub nullifier: Digest,
    /// Recipient commitment for a private transfer; change commitment for a
    /// withdrawal.
    pub first_output: Digest,
    /// Change commitment for a private transfer; destination token-account
    /// pubkey bytes for a withdrawal.
    pub second_output_or_destination: [u8; 32],
    /// Zero for private transfer.
    pub withdrawal_amount: u32,
    pub first_leaf_index: u64,
    /// Zero when the receipt contains only one appended output.
    pub second_leaf_index: u64,
    pub root_sequence: u64,
    pub root: Digest,
}

fn digest_is_canonical(digest: &Digest) -> bool {
    digest.iter().all(|limb| limb.0 < P)
}

fn exact_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], PoolInstructionFormatErrorV1> {
    bytes
        .try_into()
        .map_err(|_| PoolInstructionFormatErrorV1::WrongLength)
}

fn require_exact_header(
    bytes: &[u8],
    expected_magic: &[u8; 4],
    expected_kind: PoolV1TransitionKind,
) -> Result<(), PoolInstructionFormatErrorV1> {
    if bytes[..4] != *expected_magic {
        return Err(PoolInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5] != expected_kind as u8 {
        return Err(PoolInstructionFormatErrorV1::WrongTransitionKind);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolInstructionFormatErrorV1::NonZeroReserved);
    }
    Ok(())
}

fn decode_statement_common(
    bytes: &[u8],
    expected_magic: &[u8; 4],
    expected_kind: PoolV1TransitionKind,
) -> Result<StatementCommonV1, PoolInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_TRANSITION_STATEMENT_BYTES {
        return Err(PoolInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != *expected_magic {
        return Err(PoolInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_TRANSITION_STATEMENT_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5] != expected_kind as u8 {
        return Err(PoolInstructionFormatErrorV1::WrongTransitionKind);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolInstructionFormatErrorV1::NonZeroReserved);
    }
    let raw_asset_id = u32::from_le_bytes(exact_array(
        &bytes[STATEMENT_ASSET_ID_OFFSET..STATEMENT_ASSET_ID_OFFSET + 4],
    )?);
    if raw_asset_id >= P {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    let anchor_root = decode_digest_canonical(&exact_array(
        &bytes[STATEMENT_ROOT_OFFSET..STATEMENT_NULLIFIER_OFFSET],
    )?)
    .map_err(|_| PoolInstructionFormatErrorV1::NonCanonicalField)?;
    let nullifier = decode_digest_canonical(&exact_array(
        &bytes[STATEMENT_NULLIFIER_OFFSET..STATEMENT_ASSET_ID_OFFSET],
    )?)
    .map_err(|_| PoolInstructionFormatErrorV1::NonCanonicalField)?;
    Ok(StatementCommonV1 {
        pool: exact_array(&bytes[STATEMENT_POOL_OFFSET..STATEMENT_DOMAIN_OFFSET])?,
        deployment_domain: exact_array(&bytes[STATEMENT_DOMAIN_OFFSET..STATEMENT_SEQUENCE_OFFSET])?,
        anchor_sequence: u64::from_le_bytes(exact_array(
            &bytes[STATEMENT_SEQUENCE_OFFSET..STATEMENT_ROOT_OFFSET],
        )?),
        anchor_root,
        nullifier,
        asset_id: M31(raw_asset_id),
    })
}

fn require_envelope_statement_match(
    envelope: &HistoricalAnchorEnvelopeV1,
    expected_kind: PoolV1TransitionKind,
    pool: &[u8; 32],
    deployment_domain: &[u8; 32],
    anchor_sequence: u64,
    anchor_root: &Digest,
    nullifier: &Digest,
) -> Result<(), PoolInstructionFormatErrorV1> {
    if envelope.transition_kind != expected_kind
        || envelope.pool != *pool
        || envelope.deployment_domain != *deployment_domain
        || envelope.anchor_sequence != anchor_sequence
        || envelope.anchor_root != *anchor_root
        || envelope.nullifier != *nullifier
    {
        return Err(PoolInstructionFormatErrorV1::EnvelopeStatementMismatch);
    }
    Ok(())
}

pub fn encode_initialize_instruction_v1(
    initialization: &PoolInitializationV1,
) -> Result<[u8; POOL_V1_INITIALIZE_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    if initialization.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || initialization.asset_id.0 >= P
    {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    let policy = encode_verifier_policy_v1(&initialization.verifier_policy)
        .map_err(|_| PoolInstructionFormatErrorV1::InvalidPolicy)?;
    let mut bytes = [0u8; POOL_V1_INITIALIZE_INSTRUCTION_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_INITIALIZE_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[INITIALIZE_MINT_OFFSET..INITIALIZE_ASSET_ID_OFFSET]
        .copy_from_slice(&initialization.asset_mint);
    bytes[INITIALIZE_ASSET_ID_OFFSET..INITIALIZE_ASSET_ID_OFFSET + 4]
        .copy_from_slice(&initialization.asset_id.to_le_bytes());
    bytes[INITIALIZE_DOMAIN_OFFSET..INITIALIZE_POLICY_OFFSET]
        .copy_from_slice(&initialization.deployment_domain);
    bytes[INITIALIZE_POLICY_OFFSET..].copy_from_slice(&policy);
    Ok(bytes)
}

pub fn decode_initialize_instruction_v1(
    bytes: &[u8],
) -> Result<PoolInitializationV1, PoolInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_INITIALIZE_INSTRUCTION_BYTES {
        return Err(PoolInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_INITIALIZE_INSTRUCTION_MAGIC {
        return Err(PoolInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5..8] != [0u8; 3] || bytes[44..48] != [0u8; 4] {
        return Err(PoolInstructionFormatErrorV1::NonZeroReserved);
    }
    let raw_asset_id = u32::from_le_bytes(exact_array(&bytes[40..44])?);
    if raw_asset_id >= P {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    let verifier_policy = decode_verifier_policy_v1(&bytes[INITIALIZE_POLICY_OFFSET..])
        .map_err(|_| PoolInstructionFormatErrorV1::InvalidPolicy)?;
    Ok(PoolInitializationV1 {
        asset_mint: exact_array(&bytes[INITIALIZE_MINT_OFFSET..INITIALIZE_ASSET_ID_OFFSET])?,
        token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
        asset_id: M31(raw_asset_id),
        deployment_domain: exact_array(&bytes[INITIALIZE_DOMAIN_OFFSET..INITIALIZE_POLICY_OFFSET])?,
        verifier_policy,
    })
}

fn encode_statement_common(
    bytes: &mut [u8; POOL_V1_TRANSITION_STATEMENT_BYTES],
    magic: &[u8; 4],
    kind: PoolV1TransitionKind,
    common: StatementCommonV1,
) -> Result<(), PoolInstructionFormatErrorV1> {
    if common.asset_id.0 >= P
        || !digest_is_canonical(&common.anchor_root)
        || !digest_is_canonical(&common.nullifier)
    {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    bytes[..4].copy_from_slice(magic);
    bytes[4] = POOL_V1_TRANSITION_STATEMENT_VERSION;
    bytes[5] = kind as u8;
    bytes[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[STATEMENT_POOL_OFFSET..STATEMENT_DOMAIN_OFFSET].copy_from_slice(&common.pool);
    bytes[STATEMENT_DOMAIN_OFFSET..STATEMENT_SEQUENCE_OFFSET]
        .copy_from_slice(&common.deployment_domain);
    bytes[STATEMENT_SEQUENCE_OFFSET..STATEMENT_ROOT_OFFSET]
        .copy_from_slice(&common.anchor_sequence.to_le_bytes());
    bytes[STATEMENT_ROOT_OFFSET..STATEMENT_NULLIFIER_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.anchor_root));
    bytes[STATEMENT_NULLIFIER_OFFSET..STATEMENT_ASSET_ID_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.nullifier));
    bytes[STATEMENT_ASSET_ID_OFFSET..STATEMENT_ASSET_ID_OFFSET + 4]
        .copy_from_slice(&common.asset_id.to_le_bytes());
    Ok(())
}

pub fn encode_private_transfer_instruction_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    statement: &PrivateTransferStatementV1,
) -> Result<[u8; POOL_V1_SPEND_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    require_envelope_statement_match(
        envelope,
        PoolV1TransitionKind::PrivateTransfer,
        &statement.pool,
        &statement.deployment_domain,
        statement.anchor_sequence,
        &statement.anchor_root,
        &statement.nullifier,
    )?;
    if !digest_is_canonical(&statement.recipient_commitment)
        || !digest_is_canonical(&statement.change_commitment)
    {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    let envelope_bytes = encode_historical_anchor_envelope_v1(envelope)
        .map_err(|_| PoolInstructionFormatErrorV1::InvalidEnvelope)?;
    let mut statement_bytes = [0u8; POOL_V1_TRANSITION_STATEMENT_BYTES];
    encode_statement_common(
        &mut statement_bytes,
        &POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
        PoolV1TransitionKind::PrivateTransfer,
        StatementCommonV1 {
            pool: statement.pool,
            deployment_domain: statement.deployment_domain,
            anchor_sequence: statement.anchor_sequence,
            anchor_root: statement.anchor_root,
            nullifier: statement.nullifier,
            asset_id: statement.asset_id,
        },
    )?;
    statement_bytes[148..152].fill(0);
    statement_bytes[STATEMENT_FIRST_OUTPUT_OFFSET..STATEMENT_SECOND_OUTPUT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&statement.recipient_commitment));
    statement_bytes[STATEMENT_SECOND_OUTPUT_OFFSET..]
        .copy_from_slice(&encode_digest_canonical(&statement.change_commitment));

    let mut bytes = [0u8; POOL_V1_SPEND_INSTRUCTION_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[5] = PoolV1TransitionKind::PrivateTransfer as u8;
    bytes[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[SPEND_ENVELOPE_OFFSET..SPEND_STATEMENT_OFFSET].copy_from_slice(&envelope_bytes);
    bytes[SPEND_STATEMENT_OFFSET..].copy_from_slice(&statement_bytes);
    Ok(bytes)
}

pub fn encode_pair_private_transfer_instruction_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    statement: &PrivateTransferStatementV1,
) -> Result<[u8; POOL_V1_SPEND_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    let mut bytes = encode_private_transfer_instruction_v1(envelope, statement)?;
    bytes[..4].copy_from_slice(&POOL_V1_PAIR_PRIVATE_TRANSFER_INSTRUCTION_MAGIC);
    Ok(bytes)
}

pub fn decode_private_transfer_instruction_v1(
    bytes: &[u8],
) -> Result<PrivateTransferInstructionV1<'_>, PoolInstructionFormatErrorV1> {
    decode_private_transfer_with_magic_v1(bytes, &POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC)
}

pub fn decode_pair_private_transfer_instruction_v1(
    bytes: &[u8],
) -> Result<PrivateTransferInstructionV1<'_>, PoolInstructionFormatErrorV1> {
    decode_private_transfer_with_magic_v1(bytes, &POOL_V1_PAIR_PRIVATE_TRANSFER_INSTRUCTION_MAGIC)
}

fn decode_private_transfer_with_magic_v1<'a>(
    bytes: &'a [u8],
    magic: &[u8; 4],
) -> Result<PrivateTransferInstructionV1<'a>, PoolInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_SPEND_INSTRUCTION_BYTES {
        return Err(PoolInstructionFormatErrorV1::WrongLength);
    }
    require_exact_header(bytes, magic, PoolV1TransitionKind::PrivateTransfer)?;
    let envelope =
        decode_historical_anchor_envelope_v1(&bytes[SPEND_ENVELOPE_OFFSET..SPEND_STATEMENT_OFFSET])
            .map_err(|_| PoolInstructionFormatErrorV1::InvalidEnvelope)?;
    let payload = &bytes[SPEND_STATEMENT_OFFSET..];
    let common = decode_statement_common(
        payload,
        &POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
        PoolV1TransitionKind::PrivateTransfer,
    )?;
    if payload[148..152] != [0u8; 4] {
        return Err(PoolInstructionFormatErrorV1::NonZeroReserved);
    }
    let recipient_commitment = decode_digest_canonical(&exact_array(
        &payload[STATEMENT_FIRST_OUTPUT_OFFSET..STATEMENT_SECOND_OUTPUT_OFFSET],
    )?)
    .map_err(|_| PoolInstructionFormatErrorV1::NonCanonicalField)?;
    let change_commitment =
        decode_digest_canonical(&exact_array(&payload[STATEMENT_SECOND_OUTPUT_OFFSET..])?)
            .map_err(|_| PoolInstructionFormatErrorV1::NonCanonicalField)?;
    require_envelope_statement_match(
        &envelope,
        PoolV1TransitionKind::PrivateTransfer,
        &common.pool,
        &common.deployment_domain,
        common.anchor_sequence,
        &common.anchor_root,
        &common.nullifier,
    )?;
    Ok(PrivateTransferInstructionV1 {
        envelope,
        statement: PrivateTransferStatementV1 {
            pool: common.pool,
            deployment_domain: common.deployment_domain,
            anchor_sequence: common.anchor_sequence,
            anchor_root: common.anchor_root,
            nullifier: common.nullifier,
            asset_id: common.asset_id,
            recipient_commitment,
            change_commitment,
        },
        statement_payload: payload,
    })
}

pub fn encode_withdrawal_instruction_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    statement: &WithdrawalStatementV1,
) -> Result<[u8; POOL_V1_SPEND_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    require_envelope_statement_match(
        envelope,
        PoolV1TransitionKind::Withdrawal,
        &statement.pool,
        &statement.deployment_domain,
        statement.anchor_sequence,
        &statement.anchor_root,
        &statement.nullifier,
    )?;
    if statement.amount == 0 || statement.amount >= VALUE_LIMIT {
        return Err(PoolInstructionFormatErrorV1::InvalidWithdrawalAmount);
    }
    if statement.destination_token_account == [0u8; 32] {
        return Err(PoolInstructionFormatErrorV1::InvalidDestination);
    }
    if !digest_is_canonical(&statement.change_commitment) {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    let envelope_bytes = encode_historical_anchor_envelope_v1(envelope)
        .map_err(|_| PoolInstructionFormatErrorV1::InvalidEnvelope)?;
    let mut statement_bytes = [0u8; POOL_V1_TRANSITION_STATEMENT_BYTES];
    encode_statement_common(
        &mut statement_bytes,
        &POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
        PoolV1TransitionKind::Withdrawal,
        StatementCommonV1 {
            pool: statement.pool,
            deployment_domain: statement.deployment_domain,
            anchor_sequence: statement.anchor_sequence,
            anchor_root: statement.anchor_root,
            nullifier: statement.nullifier,
            asset_id: statement.asset_id,
        },
    )?;
    statement_bytes[148..152].copy_from_slice(&statement.amount.to_le_bytes());
    statement_bytes[STATEMENT_FIRST_OUTPUT_OFFSET..STATEMENT_SECOND_OUTPUT_OFFSET]
        .copy_from_slice(&statement.destination_token_account);
    statement_bytes[STATEMENT_SECOND_OUTPUT_OFFSET..]
        .copy_from_slice(&encode_digest_canonical(&statement.change_commitment));

    let mut bytes = [0u8; POOL_V1_SPEND_INSTRUCTION_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[5] = PoolV1TransitionKind::Withdrawal as u8;
    bytes[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[SPEND_ENVELOPE_OFFSET..SPEND_STATEMENT_OFFSET].copy_from_slice(&envelope_bytes);
    bytes[SPEND_STATEMENT_OFFSET..].copy_from_slice(&statement_bytes);
    Ok(bytes)
}

pub fn encode_pair_withdrawal_instruction_v1(
    envelope: &HistoricalAnchorEnvelopeV1,
    statement: &WithdrawalStatementV1,
) -> Result<[u8; POOL_V1_SPEND_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    let mut bytes = encode_withdrawal_instruction_v1(envelope, statement)?;
    bytes[..4].copy_from_slice(&POOL_V1_PAIR_WITHDRAWAL_INSTRUCTION_MAGIC);
    Ok(bytes)
}

pub fn decode_withdrawal_instruction_v1(
    bytes: &[u8],
) -> Result<WithdrawalInstructionV1<'_>, PoolInstructionFormatErrorV1> {
    decode_withdrawal_with_magic_v1(bytes, &POOL_V1_WITHDRAWAL_INSTRUCTION_MAGIC)
}

pub fn decode_pair_withdrawal_instruction_v1(
    bytes: &[u8],
) -> Result<WithdrawalInstructionV1<'_>, PoolInstructionFormatErrorV1> {
    decode_withdrawal_with_magic_v1(bytes, &POOL_V1_PAIR_WITHDRAWAL_INSTRUCTION_MAGIC)
}

fn decode_withdrawal_with_magic_v1<'a>(
    bytes: &'a [u8],
    magic: &[u8; 4],
) -> Result<WithdrawalInstructionV1<'a>, PoolInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_SPEND_INSTRUCTION_BYTES {
        return Err(PoolInstructionFormatErrorV1::WrongLength);
    }
    require_exact_header(bytes, magic, PoolV1TransitionKind::Withdrawal)?;
    let envelope =
        decode_historical_anchor_envelope_v1(&bytes[SPEND_ENVELOPE_OFFSET..SPEND_STATEMENT_OFFSET])
            .map_err(|_| PoolInstructionFormatErrorV1::InvalidEnvelope)?;
    let payload = &bytes[SPEND_STATEMENT_OFFSET..];
    let common = decode_statement_common(
        payload,
        &POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
        PoolV1TransitionKind::Withdrawal,
    )?;
    let amount = u32::from_le_bytes(exact_array(&payload[148..152])?);
    if amount == 0 || amount >= VALUE_LIMIT {
        return Err(PoolInstructionFormatErrorV1::InvalidWithdrawalAmount);
    }
    let destination_token_account =
        exact_array(&payload[STATEMENT_FIRST_OUTPUT_OFFSET..STATEMENT_SECOND_OUTPUT_OFFSET])?;
    if destination_token_account == [0u8; 32] {
        return Err(PoolInstructionFormatErrorV1::InvalidDestination);
    }
    let change_commitment =
        decode_digest_canonical(&exact_array(&payload[STATEMENT_SECOND_OUTPUT_OFFSET..])?)
            .map_err(|_| PoolInstructionFormatErrorV1::NonCanonicalField)?;
    require_envelope_statement_match(
        &envelope,
        PoolV1TransitionKind::Withdrawal,
        &common.pool,
        &common.deployment_domain,
        common.anchor_sequence,
        &common.anchor_root,
        &common.nullifier,
    )?;
    Ok(WithdrawalInstructionV1 {
        envelope,
        statement: WithdrawalStatementV1 {
            pool: common.pool,
            deployment_domain: common.deployment_domain,
            anchor_sequence: common.anchor_sequence,
            anchor_root: common.anchor_root,
            nullifier: common.nullifier,
            asset_id: common.asset_id,
            amount,
            destination_token_account,
            change_commitment,
        },
        statement_payload: payload,
    })
}

pub fn decode_deposit_top_level_v1(
    bytes: &[u8],
) -> Result<DepositRequestV1<'_>, PoolInstructionFormatErrorV1> {
    decode_deposit_instruction_v1(bytes).map_err(Into::into)
}

pub fn encode_initialization_receipt_v1(
    pool: &Pubkey,
    root_page_zero: &Pubkey,
    vault_token_account: &Pubkey,
) -> [u8; POOL_V1_INITIALIZATION_RECEIPT_BYTES] {
    let mut bytes = [0u8; POOL_V1_INITIALIZATION_RECEIPT_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_INITIALIZATION_RECEIPT_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[8..40].copy_from_slice(pool.as_ref());
    bytes[40..72].copy_from_slice(root_page_zero.as_ref());
    bytes[72..104].copy_from_slice(vault_token_account.as_ref());
    bytes
}

pub fn encode_transition_receipt_v1(
    receipt: &TransitionReceiptV1,
) -> Result<[u8; POOL_V1_TRANSITION_RECEIPT_BYTES], PoolInstructionFormatErrorV1> {
    if !digest_is_canonical(&receipt.nullifier)
        || !digest_is_canonical(&receipt.first_output)
        || !digest_is_canonical(&receipt.root)
    {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    let output_count = match receipt.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => {
            decode_digest_canonical(&receipt.second_output_or_destination)
                .map_err(|_| PoolInstructionFormatErrorV1::NonCanonicalField)?;
            if receipt.withdrawal_amount != 0
                || receipt.second_leaf_index != receipt.first_leaf_index.saturating_add(1)
            {
                return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
            }
            2
        }
        PoolV1TransitionKind::Withdrawal => {
            if receipt.withdrawal_amount == 0
                || receipt.withdrawal_amount >= VALUE_LIMIT
                || receipt.second_output_or_destination == [0u8; 32]
                || receipt.second_leaf_index != 0
            {
                return Err(PoolInstructionFormatErrorV1::InvalidWithdrawalAmount);
            }
            1
        }
    };
    let mut bytes = [0u8; POOL_V1_TRANSITION_RECEIPT_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_TRANSITION_RECEIPT_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[5] = receipt.transition_kind as u8;
    bytes[6] = output_count;
    bytes[7] = POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[8..40].copy_from_slice(&receipt.pool);
    bytes[40..72].copy_from_slice(&encode_digest_canonical(&receipt.nullifier));
    bytes[72..104].copy_from_slice(&encode_digest_canonical(&receipt.first_output));
    bytes[104..136].copy_from_slice(&receipt.second_output_or_destination);
    bytes[136..140].copy_from_slice(&receipt.withdrawal_amount.to_le_bytes());
    bytes[144..152].copy_from_slice(&receipt.first_leaf_index.to_le_bytes());
    bytes[152..160].copy_from_slice(&receipt.second_leaf_index.to_le_bytes());
    bytes[160..168].copy_from_slice(&receipt.root_sequence.to_le_bytes());
    bytes[168..200].copy_from_slice(&encode_digest_canonical(&receipt.root));
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_statement::pool_v1::{
        VerifierPolicyV1, POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn policy() -> VerifierPolicyV1 {
        VerifierPolicyV1 {
            flags: POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY,
            registry_program: [6u8; 32],
            registry_authority: [0u8; 32],
            policy_binding: [8u8; 32],
        }
    }

    fn envelope(kind: PoolV1TransitionKind) -> HistoricalAnchorEnvelopeV1 {
        HistoricalAnchorEnvelopeV1 {
            transition_kind: kind,
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 7,
            anchor_root: digest(10),
            nullifier: digest(100),
            verifier_profile: [3u8; 32],
            verifier_release: [4u8; 32],
        }
    }

    #[test]
    fn initialization_is_exact_and_rejects_trailing_reserved_and_policy_confusion() {
        let initialization = PoolInitializationV1 {
            asset_mint: [9u8; 32],
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(11),
            deployment_domain: [12u8; 32],
            verifier_policy: policy(),
        };
        let encoded = encode_initialize_instruction_v1(&initialization).unwrap();
        assert_eq!(
            decode_initialize_instruction_v1(&encoded),
            Ok(initialization)
        );

        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_initialize_instruction_v1(&trailing),
            Err(PoolInstructionFormatErrorV1::WrongLength)
        );
        let mut reserved = encoded;
        reserved[44] = 1;
        assert_eq!(
            decode_initialize_instruction_v1(&reserved),
            Err(PoolInstructionFormatErrorV1::NonZeroReserved)
        );
        let mut changed_policy = encoded;
        changed_policy[INITIALIZE_POLICY_OFFSET + 4] = 2;
        assert_eq!(
            decode_initialize_instruction_v1(&changed_policy),
            Err(PoolInstructionFormatErrorV1::InvalidPolicy)
        );
    }

    #[test]
    fn private_transfer_round_trip_binds_both_outputs_and_all_common_fields() {
        let envelope = envelope(PoolV1TransitionKind::PrivateTransfer);
        let statement = PrivateTransferStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(7),
            recipient_commitment: digest(200),
            change_commitment: digest(300),
        };
        let encoded = encode_private_transfer_instruction_v1(&envelope, &statement).unwrap();
        let decoded = decode_private_transfer_instruction_v1(&encoded).unwrap();
        assert_eq!(decoded.envelope, envelope);
        assert_eq!(decoded.statement, statement);
        assert_eq!(
            decoded.statement_payload,
            &encoded[SPEND_STATEMENT_OFFSET..]
        );

        let mut changed = encoded;
        changed[SPEND_STATEMENT_OFFSET + STATEMENT_POOL_OFFSET] ^= 1;
        assert_eq!(
            decode_private_transfer_instruction_v1(&changed),
            Err(PoolInstructionFormatErrorV1::EnvelopeStatementMismatch)
        );
        let mut noncanonical = encoded;
        noncanonical[SPEND_STATEMENT_OFFSET + STATEMENT_FIRST_OUTPUT_OFFSET
            ..SPEND_STATEMENT_OFFSET + STATEMENT_FIRST_OUTPUT_OFFSET + 4]
            .copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            decode_private_transfer_instruction_v1(&noncanonical),
            Err(PoolInstructionFormatErrorV1::NonCanonicalField)
        );
    }

    #[test]
    fn withdrawal_round_trip_rejects_zero_amount_wrong_kind_and_trailing_data() {
        let envelope = envelope(PoolV1TransitionKind::Withdrawal);
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(7),
            amount: 25,
            destination_token_account: [5u8; 32],
            change_commitment: digest(400),
        };
        let encoded = encode_withdrawal_instruction_v1(&envelope, &statement).unwrap();
        assert_eq!(
            decode_withdrawal_instruction_v1(&encoded)
                .unwrap()
                .statement,
            statement
        );

        let mut zero_amount = encoded;
        zero_amount[SPEND_STATEMENT_OFFSET + 148..SPEND_STATEMENT_OFFSET + 152].fill(0);
        assert_eq!(
            decode_withdrawal_instruction_v1(&zero_amount),
            Err(PoolInstructionFormatErrorV1::InvalidWithdrawalAmount)
        );
        let mut wrong_kind = encoded;
        wrong_kind[5] = PoolV1TransitionKind::PrivateTransfer as u8;
        assert_eq!(
            decode_withdrawal_instruction_v1(&wrong_kind),
            Err(PoolInstructionFormatErrorV1::WrongTransitionKind)
        );
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_withdrawal_instruction_v1(&trailing),
            Err(PoolInstructionFormatErrorV1::WrongLength)
        );
    }
}
