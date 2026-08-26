//! Exact public instruction wire for atomically consuming a prepared Pool V1
//! settlement.
//!
//! The committed `ASPS`/optional `ASRS` accounts already authenticate the
//! historical-anchor envelope. Final settlement therefore carries only the
//! byte-identical canonical payment statement needed to reauthenticate the
//! finalized verifier receipt and the withdrawal custody fields.

use aspis_statement::pool_v1::{
    decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
    PoolV1TransitionKind, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_PAYMENT_STATEMENT_BYTES,
};
use solana_program::program_error::ProgramError;

use crate::instruction::POOL_V1_INSTRUCTION_VERSION;

pub const POOL_V1_SETTLE_PREPARED_INSTRUCTION_MAGIC: [u8; 4] = *b"ASPF";
pub const POOL_V1_SETTLE_PREPARED_HEADER_BYTES: usize = 8;
pub const POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES: usize =
    POOL_V1_SETTLE_PREPARED_HEADER_BYTES + POOL_V1_PAYMENT_STATEMENT_BYTES;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SettlePreparedInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    InvalidStatement,
}

impl From<SettlePreparedInstructionFormatErrorV1> for ProgramError {
    fn from(_: SettlePreparedInstructionFormatErrorV1) -> Self {
        ProgramError::InvalidInstructionData
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SettlePreparedInstructionV1<'a> {
    pub transition_kind: PoolV1TransitionKind,
    pub statement_payload: &'a [u8],
}

fn transition_kind(
    value: u8,
) -> Result<PoolV1TransitionKind, SettlePreparedInstructionFormatErrorV1> {
    match value {
        1 => Ok(PoolV1TransitionKind::PrivateTransfer),
        2 => Ok(PoolV1TransitionKind::Withdrawal),
        _ => Err(SettlePreparedInstructionFormatErrorV1::WrongTransitionKind),
    }
}

fn validate_statement(
    transition_kind: PoolV1TransitionKind,
    statement_payload: &[u8],
) -> Result<(), SettlePreparedInstructionFormatErrorV1> {
    match transition_kind {
        PoolV1TransitionKind::PrivateTransfer => {
            decode_pool_v1_private_transfer_public_v1(statement_payload)
                .map(|_| ())
                .map_err(|_| SettlePreparedInstructionFormatErrorV1::InvalidStatement)
        }
        PoolV1TransitionKind::Withdrawal => decode_pool_v1_withdrawal_public_v1(statement_payload)
            .map(|_| ())
            .map_err(|_| SettlePreparedInstructionFormatErrorV1::InvalidStatement),
    }
}

pub fn decode_settle_prepared_instruction_v1(
    bytes: &[u8],
) -> Result<SettlePreparedInstructionV1<'_>, SettlePreparedInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES {
        return Err(SettlePreparedInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_SETTLE_PREPARED_INSTRUCTION_MAGIC {
        return Err(SettlePreparedInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(SettlePreparedInstructionFormatErrorV1::WrongVersion);
    }
    let transition_kind = transition_kind(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(SettlePreparedInstructionFormatErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(SettlePreparedInstructionFormatErrorV1::NonZeroReserved);
    }
    let statement_payload = &bytes[POOL_V1_SETTLE_PREPARED_HEADER_BYTES..];
    validate_statement(transition_kind, statement_payload)?;
    Ok(SettlePreparedInstructionV1 {
        transition_kind,
        statement_payload,
    })
}

pub fn encode_settle_prepared_instruction_v1(
    transition_kind: PoolV1TransitionKind,
    statement_payload: &[u8],
) -> Result<[u8; POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES], SettlePreparedInstructionFormatErrorV1>
{
    validate_statement(transition_kind, statement_payload)?;
    let mut bytes = [0u8; POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_SETTLE_PREPARED_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[5] = transition_kind as u8;
    bytes[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    bytes[POOL_V1_SETTLE_PREPARED_HEADER_BYTES..].copy_from_slice(statement_payload);
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{encode_pool_v1_private_transfer_public_v1, PoolV1PrivateTransferPublicV1},
        poseidon2::Digest,
    };

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    #[test]
    fn settle_prepared_wire_is_exact_and_nested_kind_bound() {
        let payload = encode_pool_v1_private_transfer_public_v1(&PoolV1PrivateTransferPublicV1 {
            pool: [1u8; 32],
            deployment_domain: [2u8; 32],
            anchor_sequence: 3,
            anchor_root: digest(4),
            nullifier: digest(5),
            asset_id: M31(6),
            recipient_commitment: digest(7),
            change_commitment: digest(8),
        })
        .unwrap();
        let encoded =
            encode_settle_prepared_instruction_v1(PoolV1TransitionKind::PrivateTransfer, &payload)
                .unwrap();
        let decoded = decode_settle_prepared_instruction_v1(&encoded).unwrap();
        assert_eq!(
            decoded.transition_kind,
            PoolV1TransitionKind::PrivateTransfer
        );
        assert_eq!(decoded.statement_payload, payload);

        let mut wrong_kind = encoded;
        wrong_kind[5] = PoolV1TransitionKind::Withdrawal as u8;
        assert_eq!(
            decode_settle_prepared_instruction_v1(&wrong_kind),
            Err(SettlePreparedInstructionFormatErrorV1::InvalidStatement)
        );
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_settle_prepared_instruction_v1(&trailing),
            Err(SettlePreparedInstructionFormatErrorV1::WrongLength)
        );
    }
}
