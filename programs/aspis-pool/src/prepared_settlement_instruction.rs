//! Exact public instruction wire for preparing a state-bound Pool V1 plan.
//!
//! The payload wraps one already-canonical `ASPT` or `ASWD` instruction. It
//! does not invoke the verifier: preparation consumes the finalized verifier
//! authorization-receipt account named in the account list.

use aspis_statement::pool_v1::{PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION};
use solana_program::program_error::ProgramError;

use crate::instruction::{
    decode_private_transfer_instruction_v1, decode_withdrawal_instruction_v1,
    POOL_V1_INSTRUCTION_VERSION, POOL_V1_SPEND_INSTRUCTION_BYTES,
};

pub const POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC: [u8; 4] = *b"ASPP";
pub const POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES: usize = 24;
pub const POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES: usize =
    POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES + POOL_V1_SPEND_INSTRUCTION_BYTES;

const NOT_BEFORE_SLOT_OFFSET: usize = 8;
const EXPIRES_AT_SLOT_OFFSET: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrepareSettlementInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    InvalidTimeRange,
    InvalidNestedSpend,
}

impl From<PrepareSettlementInstructionFormatErrorV1> for ProgramError {
    fn from(_: PrepareSettlementInstructionFormatErrorV1) -> Self {
        ProgramError::InvalidInstructionData
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrepareSettlementInstructionV1<'a> {
    pub transition_kind: PoolV1TransitionKind,
    pub not_before_slot: u64,
    pub expires_at_slot: u64,
    pub spend_instruction: &'a [u8],
}

fn exact_array<const N: usize>(
    bytes: &[u8],
) -> Result<[u8; N], PrepareSettlementInstructionFormatErrorV1> {
    bytes
        .try_into()
        .map_err(|_| PrepareSettlementInstructionFormatErrorV1::WrongLength)
}

fn transition_kind(
    value: u8,
) -> Result<PoolV1TransitionKind, PrepareSettlementInstructionFormatErrorV1> {
    match value {
        1 => Ok(PoolV1TransitionKind::PrivateTransfer),
        2 => Ok(PoolV1TransitionKind::Withdrawal),
        _ => Err(PrepareSettlementInstructionFormatErrorV1::WrongTransitionKind),
    }
}

fn validate_nested_spend(
    kind: PoolV1TransitionKind,
    spend_instruction: &[u8],
) -> Result<(), PrepareSettlementInstructionFormatErrorV1> {
    match kind {
        PoolV1TransitionKind::PrivateTransfer => {
            decode_private_transfer_instruction_v1(spend_instruction)
                .map(|_| ())
                .map_err(|_| PrepareSettlementInstructionFormatErrorV1::InvalidNestedSpend)
        }
        PoolV1TransitionKind::Withdrawal => decode_withdrawal_instruction_v1(spend_instruction)
            .map(|_| ())
            .map_err(|_| PrepareSettlementInstructionFormatErrorV1::InvalidNestedSpend),
    }
}

pub fn decode_prepare_settlement_instruction_v1(
    bytes: &[u8],
) -> Result<PrepareSettlementInstructionV1<'_>, PrepareSettlementInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES {
        return Err(PrepareSettlementInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC {
        return Err(PrepareSettlementInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(PrepareSettlementInstructionFormatErrorV1::WrongVersion);
    }
    let transition_kind = transition_kind(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PrepareSettlementInstructionFormatErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PrepareSettlementInstructionFormatErrorV1::NonZeroReserved);
    }
    let not_before_slot = u64::from_le_bytes(exact_array(
        &bytes[NOT_BEFORE_SLOT_OFFSET..EXPIRES_AT_SLOT_OFFSET],
    )?);
    let expires_at_slot = u64::from_le_bytes(exact_array(
        &bytes[EXPIRES_AT_SLOT_OFFSET..POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES],
    )?);
    if not_before_slot > expires_at_slot {
        return Err(PrepareSettlementInstructionFormatErrorV1::InvalidTimeRange);
    }
    let spend_instruction = &bytes[POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES..];
    validate_nested_spend(transition_kind, spend_instruction)?;
    Ok(PrepareSettlementInstructionV1 {
        transition_kind,
        not_before_slot,
        expires_at_slot,
        spend_instruction,
    })
}

pub fn encode_prepare_settlement_instruction_v1(
    transition_kind: PoolV1TransitionKind,
    not_before_slot: u64,
    expires_at_slot: u64,
    spend_instruction: &[u8],
) -> Result<
    [u8; POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES],
    PrepareSettlementInstructionFormatErrorV1,
> {
    if not_before_slot > expires_at_slot {
        return Err(PrepareSettlementInstructionFormatErrorV1::InvalidTimeRange);
    }
    validate_nested_spend(transition_kind, spend_instruction)?;
    let mut bytes = [0u8; POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[5] = transition_kind as u8;
    bytes[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[NOT_BEFORE_SLOT_OFFSET..EXPIRES_AT_SLOT_OFFSET]
        .copy_from_slice(&not_before_slot.to_le_bytes());
    bytes[EXPIRES_AT_SLOT_OFFSET..POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES]
        .copy_from_slice(&expires_at_slot.to_le_bytes());
    bytes[POOL_V1_PREPARE_SETTLEMENT_HEADER_BYTES..].copy_from_slice(spend_instruction);
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{pool_v1::HistoricalAnchorEnvelopeV1, poseidon2::Digest};

    use crate::instruction::{encode_private_transfer_instruction_v1, PrivateTransferStatementV1};

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    #[test]
    fn prepared_settlement_instruction_is_exact_and_nested_kind_bound() {
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 3,
            anchor_root: digest(4),
            nullifier: digest(5),
            verifier_profile: [6u8; 32],
            verifier_release: [7u8; 32],
        };
        let spend = encode_private_transfer_instruction_v1(
            &envelope,
            &PrivateTransferStatementV1 {
                pool: envelope.pool,
                deployment_domain: envelope.deployment_domain,
                anchor_sequence: envelope.anchor_sequence,
                anchor_root: envelope.anchor_root,
                nullifier: envelope.nullifier,
                asset_id: M31(8),
                recipient_commitment: digest(9),
                change_commitment: digest(10),
            },
        )
        .unwrap();
        let encoded = encode_prepare_settlement_instruction_v1(
            PoolV1TransitionKind::PrivateTransfer,
            11,
            12,
            &spend,
        )
        .unwrap();
        let decoded = decode_prepare_settlement_instruction_v1(&encoded).unwrap();
        assert_eq!(
            decoded.transition_kind,
            PoolV1TransitionKind::PrivateTransfer
        );
        assert_eq!(decoded.not_before_slot, 11);
        assert_eq!(decoded.expires_at_slot, 12);
        assert_eq!(decoded.spend_instruction, spend);

        let mut wrong_kind = encoded;
        wrong_kind[5] = PoolV1TransitionKind::Withdrawal as u8;
        assert_eq!(
            decode_prepare_settlement_instruction_v1(&wrong_kind),
            Err(PrepareSettlementInstructionFormatErrorV1::InvalidNestedSpend)
        );
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_prepare_settlement_instruction_v1(&trailing),
            Err(PrepareSettlementInstructionFormatErrorV1::WrongLength)
        );
    }
}
