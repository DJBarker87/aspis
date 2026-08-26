//! Exact public instruction wire for cancelling and refunding one prepared
//! Pool V1 settlement plan.
//!
//! Cancellation carries no state or timing claim. The shape byte commits the
//! exact account cardinality needed to authenticate and close either an `ASPS`
//! core alone or an `ASPS` core plus its `ASRS` rollover shard.

use solana_program::program_error::ProgramError;

use crate::instruction::POOL_V1_INSTRUCTION_VERSION;

pub const POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_MAGIC: [u8; 4] = *b"ASPX";
pub const POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_BYTES: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CancelPreparedSettlementAccountShapeV1 {
    CoreOnly = 1,
    CoreAndRolloverShard = 2,
}

impl CancelPreparedSettlementAccountShapeV1 {
    pub const fn account_count(self) -> usize {
        match self {
            Self::CoreOnly => 2,
            Self::CoreAndRolloverShard => 3,
        }
    }

    pub const fn has_rollover_shard(self) -> bool {
        matches!(self, Self::CoreAndRolloverShard)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CancelPreparedSettlementInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongAccountShape,
    NonZeroReserved,
}

impl From<CancelPreparedSettlementInstructionFormatErrorV1> for ProgramError {
    fn from(_: CancelPreparedSettlementInstructionFormatErrorV1) -> Self {
        ProgramError::InvalidInstructionData
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CancelPreparedSettlementInstructionV1 {
    pub account_shape: CancelPreparedSettlementAccountShapeV1,
}

pub fn decode_cancel_prepared_settlement_instruction_v1(
    bytes: &[u8],
) -> Result<CancelPreparedSettlementInstructionV1, CancelPreparedSettlementInstructionFormatErrorV1>
{
    if bytes.len() != POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_BYTES {
        return Err(CancelPreparedSettlementInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_MAGIC {
        return Err(CancelPreparedSettlementInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(CancelPreparedSettlementInstructionFormatErrorV1::WrongVersion);
    }
    let account_shape = match bytes[5] {
        1 => CancelPreparedSettlementAccountShapeV1::CoreOnly,
        2 => CancelPreparedSettlementAccountShapeV1::CoreAndRolloverShard,
        _ => return Err(CancelPreparedSettlementInstructionFormatErrorV1::WrongAccountShape),
    };
    if bytes[6..] != [0u8; 2] {
        return Err(CancelPreparedSettlementInstructionFormatErrorV1::NonZeroReserved);
    }
    Ok(CancelPreparedSettlementInstructionV1 { account_shape })
}

pub fn encode_cancel_prepared_settlement_instruction_v1(
    account_shape: CancelPreparedSettlementAccountShapeV1,
) -> [u8; POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_BYTES] {
    let mut bytes = [0u8; POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_BYTES];
    bytes[..4].copy_from_slice(&POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_MAGIC);
    bytes[4] = POOL_V1_INSTRUCTION_VERSION;
    bytes[5] = account_shape as u8;
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cancel_prepared_wire_is_exact_shape_bound_and_canonical() {
        for shape in [
            CancelPreparedSettlementAccountShapeV1::CoreOnly,
            CancelPreparedSettlementAccountShapeV1::CoreAndRolloverShard,
        ] {
            let encoded = encode_cancel_prepared_settlement_instruction_v1(shape);
            assert_eq!(
                encoded.len(),
                POOL_V1_CANCEL_PREPARED_SETTLEMENT_INSTRUCTION_BYTES
            );
            assert_eq!(
                decode_cancel_prepared_settlement_instruction_v1(&encoded),
                Ok(CancelPreparedSettlementInstructionV1 {
                    account_shape: shape,
                })
            );
        }

        let encoded = encode_cancel_prepared_settlement_instruction_v1(
            CancelPreparedSettlementAccountShapeV1::CoreOnly,
        );
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert_eq!(
            decode_cancel_prepared_settlement_instruction_v1(&trailing),
            Err(CancelPreparedSettlementInstructionFormatErrorV1::WrongLength)
        );
        assert_eq!(
            decode_cancel_prepared_settlement_instruction_v1(&encoded[..7]),
            Err(CancelPreparedSettlementInstructionFormatErrorV1::WrongLength)
        );

        for (offset, expected) in [
            (
                0,
                CancelPreparedSettlementInstructionFormatErrorV1::WrongMagic,
            ),
            (
                4,
                CancelPreparedSettlementInstructionFormatErrorV1::WrongVersion,
            ),
            (
                5,
                CancelPreparedSettlementInstructionFormatErrorV1::WrongAccountShape,
            ),
            (
                6,
                CancelPreparedSettlementInstructionFormatErrorV1::NonZeroReserved,
            ),
            (
                7,
                CancelPreparedSettlementInstructionFormatErrorV1::NonZeroReserved,
            ),
        ] {
            let mut mutated = encoded;
            mutated[offset] ^= 0xff;
            assert_eq!(
                decode_cancel_prepared_settlement_instruction_v1(&mutated),
                Err(expected)
            );
        }
    }
}
