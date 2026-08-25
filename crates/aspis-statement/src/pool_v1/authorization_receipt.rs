//! Immutable verifier-issued authorization receipt for split verification and
//! atomic Pool settlement.
//!
//! A receipt contains the exact authenticated `ASVS` binding that a direct
//! verifier CPI would return.  It does not weaken or reinterpret that binding:
//! the Pool must still select the same active registry entry, recompute the
//! statement payload digest, authenticate the verifier-owned receipt PDA and
//! atomically enforce anchor/nullifier/custody effects.  Nullifier freshness,
//! rather than mutable receipt state, makes settlement one-shot.

use aspis_core::transcript::HashFn;

use super::{
    decode_verifier_dispatch_result_v1, encode_verifier_dispatch_result_v1,
    PoolV1VerifierDispatchFormatError, VerifierDispatchBindingV1, VerifierDispatchResultV1,
    POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES, POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
};

pub const POOL_V1_AUTHORIZATION_RECEIPT_MAGIC: [u8; 4] = *b"ASVA";
pub const POOL_V1_AUTHORIZATION_RECEIPT_VERSION: u8 = 1;
pub const POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256: u8 = 1;
pub const POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED: u8 = 1;
pub const POOL_V1_AUTHORIZATION_RECEIPT_SEED: &[u8] = b"aspis-verify-receipt-v1";
pub const POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/authorization-receipt/v1";
pub const POOL_V1_AUTHORIZATION_RECEIPT_PREFIX_BYTES: usize = 16;
pub const POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_BYTES: usize = 32;
pub const POOL_V1_AUTHORIZATION_RECEIPT_BYTES: usize =
    POOL_V1_AUTHORIZATION_RECEIPT_PREFIX_BYTES
        + POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES
        + POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_BYTES;

const RESULT_OFFSET: usize = POOL_V1_AUTHORIZATION_RECEIPT_PREFIX_BYTES;
const DIGEST_OFFSET: usize = RESULT_OFFSET + POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES;

const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_SEED.len() <= 32);
const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_BYTES == 432);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1AuthorizationReceiptV1 {
    pub pda_bump: u8,
    pub verified_slot: u64,
    pub binding: VerifierDispatchBindingV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1AuthorizationReceiptError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongHashAlgorithm,
    WrongStatus,
    DigestMismatch,
    FutureReceipt,
    BindingMismatch,
    Dispatch(PoolV1VerifierDispatchFormatError),
}

impl From<PoolV1VerifierDispatchFormatError> for PoolV1AuthorizationReceiptError {
    fn from(error: PoolV1VerifierDispatchFormatError) -> Self {
        Self::Dispatch(error)
    }
}

fn receipt_digest_v1(prefix_and_result: &[u8], hash: HashFn) -> [u8; 32] {
    hash(&[
        POOL_V1_AUTHORIZATION_RECEIPT_DIGEST_DOMAIN,
        prefix_and_result,
    ])
}

pub fn encode_pool_v1_authorization_receipt_v1(
    receipt: &PoolV1AuthorizationReceiptV1,
    hash: HashFn,
) -> Result<[u8; POOL_V1_AUTHORIZATION_RECEIPT_BYTES], PoolV1AuthorizationReceiptError> {
    let result = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
        success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        binding: receipt.binding,
    })?;
    let mut output = [0u8; POOL_V1_AUTHORIZATION_RECEIPT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_AUTHORIZATION_RECEIPT_MAGIC);
    output[4] = POOL_V1_AUTHORIZATION_RECEIPT_VERSION;
    output[5] = POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256;
    output[6] = POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED;
    output[7] = receipt.pda_bump;
    output[8..16].copy_from_slice(&receipt.verified_slot.to_le_bytes());
    output[RESULT_OFFSET..DIGEST_OFFSET].copy_from_slice(&result);
    let digest = receipt_digest_v1(&output[..DIGEST_OFFSET], hash);
    output[DIGEST_OFFSET..].copy_from_slice(&digest);
    Ok(output)
}

pub fn decode_pool_v1_authorization_receipt_v1(
    bytes: &[u8],
    hash: HashFn,
) -> Result<PoolV1AuthorizationReceiptV1, PoolV1AuthorizationReceiptError> {
    let bytes: &[u8; POOL_V1_AUTHORIZATION_RECEIPT_BYTES] = bytes
        .try_into()
        .map_err(|_| PoolV1AuthorizationReceiptError::WrongLength)?;
    if bytes[..4] != POOL_V1_AUTHORIZATION_RECEIPT_MAGIC {
        return Err(PoolV1AuthorizationReceiptError::WrongMagic);
    }
    if bytes[4] != POOL_V1_AUTHORIZATION_RECEIPT_VERSION {
        return Err(PoolV1AuthorizationReceiptError::WrongVersion);
    }
    if bytes[5] != POOL_V1_AUTHORIZATION_RECEIPT_HASH_SHA256 {
        return Err(PoolV1AuthorizationReceiptError::WrongHashAlgorithm);
    }
    if bytes[6] != POOL_V1_AUTHORIZATION_RECEIPT_STATUS_VERIFIED {
        return Err(PoolV1AuthorizationReceiptError::WrongStatus);
    }
    let expected = receipt_digest_v1(&bytes[..DIGEST_OFFSET], hash);
    if bytes[DIGEST_OFFSET..] != expected {
        return Err(PoolV1AuthorizationReceiptError::DigestMismatch);
    }
    let result = decode_verifier_dispatch_result_v1(&bytes[RESULT_OFFSET..DIGEST_OFFSET])?;
    Ok(PoolV1AuthorizationReceiptV1 {
        pda_bump: bytes[7],
        verified_slot: u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
        binding: result.binding,
    })
}

/// Exact settlement-time gate after account owner/PDA and registry selection
/// have already been authenticated by the Pool program.
pub fn validate_pool_v1_authorization_receipt_for_settlement_v1(
    receipt: &PoolV1AuthorizationReceiptV1,
    expected_binding: &VerifierDispatchBindingV1,
    settlement_slot: u64,
) -> Result<(), PoolV1AuthorizationReceiptError> {
    if receipt.verified_slot > settlement_slot {
        return Err(PoolV1AuthorizationReceiptError::FutureReceipt);
    }
    if &receipt.binding != expected_binding {
        return Err(PoolV1AuthorizationReceiptError::BindingMismatch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use sha2::{Digest as _, Sha256};

    use super::*;
    use crate::{
        pool_v1::PoolV1TransitionKind,
        poseidon2::Digest,
    };
    use aspis_core::field::M31;

    fn sha256(inputs: &[&[u8]]) -> [u8; 32] {
        let mut state = Sha256::new();
        for input in inputs {
            state.update(input);
        }
        state.finalize().into()
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn binding() -> VerifierDispatchBindingV1 {
        VerifierDispatchBindingV1 {
            statement_version: 1,
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            verifier_program: [1u8; 32],
            profile_binding: [2u8; 32],
            release_binding: [3u8; 32],
            pool: [4u8; 32],
            deployment_domain: [5u8; 32],
            anchor_sequence: 19,
            anchor_root: digest(100),
            nullifier: digest(300),
            statement_digest: [6u8; 32],
            envelope_digest: [7u8; 32],
            proof_account: [8u8; 32],
            proof_body_digest: [9u8; 32],
            proof_body_length: 30_504,
            statement_payload_length: 216,
        }
    }

    #[test]
    fn exact_receipt_roundtrip_and_settlement_binding() {
        let receipt = PoolV1AuthorizationReceiptV1 {
            pda_bump: 251,
            verified_slot: 900,
            binding: binding(),
        };
        let encoded = encode_pool_v1_authorization_receipt_v1(&receipt, sha256).unwrap();
        assert_eq!(encoded.len(), 432);
        assert_eq!(&encoded[..4], b"ASVA");
        assert_eq!(
            decode_pool_v1_authorization_receipt_v1(&encoded, sha256),
            Ok(receipt)
        );
        assert_eq!(
            validate_pool_v1_authorization_receipt_for_settlement_v1(
                &receipt,
                &receipt.binding,
                receipt.verified_slot
            ),
            Ok(())
        );
    }

    #[test]
    fn every_receipt_byte_is_authenticated() {
        let receipt = PoolV1AuthorizationReceiptV1 {
            pda_bump: 17,
            verified_slot: 901,
            binding: binding(),
        };
        let encoded = encode_pool_v1_authorization_receipt_v1(&receipt, sha256).unwrap();
        for offset in 0..encoded.len() {
            let mut changed = encoded;
            changed[offset] ^= 1;
            assert!(
                decode_pool_v1_authorization_receipt_v1(&changed, sha256).is_err(),
                "mutation at byte {offset} accepted"
            );
        }
    }

    #[test]
    fn future_or_substituted_receipt_rejects() {
        let receipt = PoolV1AuthorizationReceiptV1 {
            pda_bump: 17,
            verified_slot: 901,
            binding: binding(),
        };
        assert_eq!(
            validate_pool_v1_authorization_receipt_for_settlement_v1(
                &receipt,
                &receipt.binding,
                900
            ),
            Err(PoolV1AuthorizationReceiptError::FutureReceipt)
        );
        let mut changed = receipt.binding;
        changed.statement_digest[0] ^= 1;
        assert_eq!(
            validate_pool_v1_authorization_receipt_for_settlement_v1(&receipt, &changed, 901),
            Err(PoolV1AuthorizationReceiptError::BindingMismatch)
        );
    }
}
