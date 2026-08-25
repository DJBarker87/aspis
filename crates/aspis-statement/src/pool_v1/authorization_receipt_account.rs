//! Canonical verifier-owned account wrapper for Pool V1 authorization receipts.
//!
//! This pure state machine wraps the committed 432-byte `ASVA` receipt in one
//! fixed-size pending/finalized account image.  It deliberately does not read
//! Solana accounts, derive a PDA, verify a signature, transfer lamports, or
//! delete an account.  Program integration must authenticate the verifier
//! owner, derive the PDA from the returned seed inputs, read the exact `ASPU`
//! upload authority, and supply the signer facts modeled by this module.
//!
//! Exact 720-byte layout:
//!
//! ```text
//!   0..4    magic `ASRA`
//!   4       wrapper version 1
//!   5       SHA-256 identifier 1
//!   6       status: 0 pending, 1 verified
//!   7       receipt PDA bump
//!   8..16   verified slot (zero while pending)
//!  16..48   verifier program
//!  48..80   proof account
//!  80..112  outer/profile statement digest
//! 112..144  complete dispatch-binding digest
//! 144..176  exact full `ASVQ` request digest
//! 176..208  required proof-upload-authority signer
//! 208..240  immutable close/refund authority
//! 240..256  canonical zero padding
//! 256..688  canonical zero pending body or exact 432-byte `ASVA`
//! 688..720  wrapper digest over the domain and bytes 0..688
//! ```
//!
//! The PDA seeds are the existing authorization-receipt seed plus the proof
//! account, outer statement digest, and complete binding digest.  The bump is
//! returned separately.  The complete binding digest is computed from the
//! canonical 384-byte successful `ASVS` image, so it commits every binding
//! field without including this wrapper address or bump and is non-circular.

use aspis_core::transcript::HashFn;

use super::{
    authorization_receipt::{
        decode_pool_v1_authorization_receipt_v1, encode_pool_v1_authorization_receipt_v1,
        PoolV1AuthorizationReceiptError, PoolV1AuthorizationReceiptV1,
        POOL_V1_AUTHORIZATION_RECEIPT_BYTES, POOL_V1_AUTHORIZATION_RECEIPT_SEED,
    },
    verifier_dispatch::{
        encode_verifier_dispatch_request_v1, encode_verifier_dispatch_result_v1,
        PoolV1VerifierDispatchFormatError, VerifierDispatchBindingV1, VerifierDispatchRequestV1,
        VerifierDispatchResultV1, POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES,
        POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
    },
};

pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_MAGIC: [u8; 4] = *b"ASRA";
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_VERSION: u8 = 1;
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HASH_SHA256: u8 = 1;
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_PENDING: u8 = 0;
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_VERIFIED: u8 = 1;
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HEADER_BYTES: usize = 256;
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_BYTES: usize = 32;
pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES: usize =
    POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HEADER_BYTES
        + POOL_V1_AUTHORIZATION_RECEIPT_BYTES
        + POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_BYTES;

pub const POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/authorization-receipt-account/v1";
pub const POOL_V1_AUTHORIZATION_RECEIPT_BINDING_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/authorization-receipt-binding/v1";
pub const POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN: &[u8] =
    b"aspis/pool-v1/authorization-receipt-request/v1";

const VERIFIED_SLOT_OFFSET: usize = 8;
const VERIFIER_PROGRAM_OFFSET: usize = 16;
const PROOF_ACCOUNT_OFFSET: usize = 48;
const STATEMENT_DIGEST_OFFSET: usize = 80;
const BINDING_DIGEST_OFFSET: usize = 112;
const REQUEST_DIGEST_OFFSET: usize = 144;
const PROOF_UPLOAD_AUTHORITY_OFFSET: usize = 176;
const CLOSE_REFUND_AUTHORITY_OFFSET: usize = 208;
const RESERVED_OFFSET: usize = 240;
const RECEIPT_OFFSET: usize = POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HEADER_BYTES;
const WRAPPER_DIGEST_OFFSET: usize = RECEIPT_OFFSET + POOL_V1_AUTHORIZATION_RECEIPT_BYTES;

const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_BYTES == 432);
const _: () = assert!(POOL_V1_VERIFIER_DISPATCH_RESULT_BYTES == 384);
const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES == 720);
const _: () = assert!(POOL_V1_AUTHORIZATION_RECEIPT_SEED.len() <= 32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1AuthorizationReceiptAccountStatusV1 {
    Pending,
    Verified,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1AuthorizationReceiptPdaInputsV1 {
    pub proof_account: [u8; 32],
    pub statement_digest: [u8; 32],
    pub binding_digest: [u8; 32],
    pub bump: u8,
}

impl PoolV1AuthorizationReceiptPdaInputsV1 {
    /// Ordered seed values following the static
    /// `POOL_V1_AUTHORIZATION_RECEIPT_SEED` prefix.
    pub fn dynamic_seeds(&self) -> [[u8; 32]; 3] {
        [
            self.proof_account,
            self.statement_digest,
            self.binding_digest,
        ]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1AuthorizationReceiptAccountV1 {
    pub status: PoolV1AuthorizationReceiptAccountStatusV1,
    pub pda_bump: u8,
    pub verified_slot: u64,
    pub verifier_program: [u8; 32],
    pub proof_account: [u8; 32],
    pub statement_digest: [u8; 32],
    pub binding_digest: [u8; 32],
    pub request_digest: [u8; 32],
    /// Exact nonzero authority read from the unsealed `ASPU` header.  Program
    /// initialization must require this key as a transaction signer.
    pub proof_upload_authority: [u8; 32],
    /// The only signer and refund destination accepted by the pure close gate.
    pub close_refund_authority: [u8; 32],
    pub receipt: Option<PoolV1AuthorizationReceiptV1>,
}

impl PoolV1AuthorizationReceiptAccountV1 {
    pub fn pda_inputs(&self) -> PoolV1AuthorizationReceiptPdaInputsV1 {
        PoolV1AuthorizationReceiptPdaInputsV1 {
            proof_account: self.proof_account,
            statement_digest: self.statement_digest,
            binding_digest: self.binding_digest,
            bump: self.pda_bump,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1AuthorizationReceiptCloseAuthorizationV1 {
    pub close_authority: [u8; 32],
    pub refund_destination: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1AuthorizationReceiptAccountErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongHashAlgorithm,
    WrongStatus,
    NonZeroReserved,
    ZeroProofUploadAuthority,
    ZeroCloseRefundAuthority,
    WrapperDigestMismatch,
    NonZeroPendingSlot,
    NonZeroPendingBody,
    MissingProofUploadAuthoritySignature,
    ProofUploadAuthorityMismatch,
    ProofAccountMismatch,
    VerifierProgramMismatch,
    StatementDigestMismatch,
    BindingDigestMismatch,
    RequestDigestMismatch,
    PdaInputsMismatch,
    ReceiptBumpMismatch,
    ReceiptSlotMismatch,
    ReceiptBindingMismatch,
    AlreadyFinalized,
    CloseAuthorityMismatch,
    RefundDestinationMismatch,
    Dispatch(PoolV1VerifierDispatchFormatError),
    Receipt(PoolV1AuthorizationReceiptError),
}

impl From<PoolV1VerifierDispatchFormatError> for PoolV1AuthorizationReceiptAccountErrorV1 {
    fn from(error: PoolV1VerifierDispatchFormatError) -> Self {
        Self::Dispatch(error)
    }
}

impl From<PoolV1AuthorizationReceiptError> for PoolV1AuthorizationReceiptAccountErrorV1 {
    fn from(error: PoolV1AuthorizationReceiptError) -> Self {
        Self::Receipt(error)
    }
}

fn wrapper_digest_v1(prefix_and_body: &[u8], hash: HashFn) -> [u8; 32] {
    hash(&[
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_DIGEST_DOMAIN,
        prefix_and_body,
    ])
}

pub fn pool_v1_authorization_receipt_binding_digest_v1(
    binding: &VerifierDispatchBindingV1,
    hash: HashFn,
) -> Result<[u8; 32], PoolV1AuthorizationReceiptAccountErrorV1> {
    let canonical = encode_verifier_dispatch_result_v1(&VerifierDispatchResultV1 {
        success_code: POOL_V1_VERIFIER_DISPATCH_SUCCESS_CODE,
        binding: *binding,
    })?;
    Ok(hash(&[
        POOL_V1_AUTHORIZATION_RECEIPT_BINDING_DIGEST_DOMAIN,
        &canonical,
    ]))
}

pub fn pool_v1_authorization_receipt_request_digest_v1(
    request: &VerifierDispatchRequestV1<'_>,
    hash: HashFn,
) -> Result<[u8; 32], PoolV1AuthorizationReceiptAccountErrorV1> {
    let canonical = encode_verifier_dispatch_request_v1(request, hash)?;
    Ok(hash(&[
        POOL_V1_AUTHORIZATION_RECEIPT_REQUEST_DIGEST_DOMAIN,
        &canonical,
    ]))
}

pub fn pool_v1_authorization_receipt_pda_inputs_for_binding_v1(
    binding: &VerifierDispatchBindingV1,
    pda_bump: u8,
    hash: HashFn,
) -> Result<PoolV1AuthorizationReceiptPdaInputsV1, PoolV1AuthorizationReceiptAccountErrorV1> {
    Ok(PoolV1AuthorizationReceiptPdaInputsV1 {
        proof_account: binding.proof_account,
        statement_digest: binding.statement_digest,
        binding_digest: pool_v1_authorization_receipt_binding_digest_v1(binding, hash)?,
        bump: pda_bump,
    })
}

fn encode_pending_after_authority_check(
    request: &VerifierDispatchRequestV1<'_>,
    pda_bump: u8,
    proof_upload_authority: [u8; 32],
    close_refund_authority: [u8; 32],
    hash: HashFn,
) -> Result<
    [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
    PoolV1AuthorizationReceiptAccountErrorV1,
> {
    if proof_upload_authority == [0u8; 32] {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ZeroProofUploadAuthority);
    }
    if close_refund_authority == [0u8; 32] {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ZeroCloseRefundAuthority);
    }
    let binding_digest = pool_v1_authorization_receipt_binding_digest_v1(&request.binding, hash)?;
    let request_digest = pool_v1_authorization_receipt_request_digest_v1(request, hash)?;

    let mut output = [0u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_MAGIC);
    output[4] = POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_VERSION;
    output[5] = POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HASH_SHA256;
    output[6] = POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_PENDING;
    output[7] = pda_bump;
    output[VERIFIER_PROGRAM_OFFSET..PROOF_ACCOUNT_OFFSET]
        .copy_from_slice(&request.binding.verifier_program);
    output[PROOF_ACCOUNT_OFFSET..STATEMENT_DIGEST_OFFSET]
        .copy_from_slice(&request.binding.proof_account);
    output[STATEMENT_DIGEST_OFFSET..BINDING_DIGEST_OFFSET]
        .copy_from_slice(&request.binding.statement_digest);
    output[BINDING_DIGEST_OFFSET..REQUEST_DIGEST_OFFSET].copy_from_slice(&binding_digest);
    output[REQUEST_DIGEST_OFFSET..PROOF_UPLOAD_AUTHORITY_OFFSET].copy_from_slice(&request_digest);
    output[PROOF_UPLOAD_AUTHORITY_OFFSET..CLOSE_REFUND_AUTHORITY_OFFSET]
        .copy_from_slice(&proof_upload_authority);
    output[CLOSE_REFUND_AUTHORITY_OFFSET..RESERVED_OFFSET].copy_from_slice(&close_refund_authority);
    // verified slot, reserved bytes, and the complete pending body remain zero.
    let digest = wrapper_digest_v1(&output[..WRAPPER_DIGEST_OFFSET], hash);
    output[WRAPPER_DIGEST_OFFSET..].copy_from_slice(&digest);
    Ok(output)
}

/// Construct the canonical pending image only after the observed unsealed
/// proof account key and upload authority match the request and the authority
/// is present as a signer.  These explicit inputs are the pure defense against
/// an unrelated caller preinitializing the deterministic receipt PDA.
pub fn initialize_pool_v1_authorization_receipt_account_v1(
    request: &VerifierDispatchRequestV1<'_>,
    observed_proof_account: [u8; 32],
    proof_header_upload_authority: [u8; 32],
    signed_upload_authority: Option<[u8; 32]>,
    close_refund_authority: [u8; 32],
    pda_bump: u8,
    hash: HashFn,
) -> Result<
    [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
    PoolV1AuthorizationReceiptAccountErrorV1,
> {
    if observed_proof_account != request.binding.proof_account {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ProofAccountMismatch);
    }
    let signer = signed_upload_authority
        .ok_or(PoolV1AuthorizationReceiptAccountErrorV1::MissingProofUploadAuthoritySignature)?;
    if signer != proof_header_upload_authority {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ProofUploadAuthorityMismatch);
    }
    encode_pending_after_authority_check(
        request,
        pda_bump,
        proof_header_upload_authority,
        close_refund_authority,
        hash,
    )
}

pub fn decode_pool_v1_authorization_receipt_account_v1(
    bytes: &[u8],
    hash: HashFn,
) -> Result<PoolV1AuthorizationReceiptAccountV1, PoolV1AuthorizationReceiptAccountErrorV1> {
    let bytes: &[u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] = bytes
        .try_into()
        .map_err(|_| PoolV1AuthorizationReceiptAccountErrorV1::WrongLength)?;
    if bytes[..4] != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_MAGIC {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_VERSION {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_HASH_SHA256 {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::WrongHashAlgorithm);
    }
    if bytes[RESERVED_OFFSET..RECEIPT_OFFSET] != [0u8; RECEIPT_OFFSET - RESERVED_OFFSET] {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::NonZeroReserved);
    }
    let expected_digest = wrapper_digest_v1(&bytes[..WRAPPER_DIGEST_OFFSET], hash);
    if bytes[WRAPPER_DIGEST_OFFSET..] != expected_digest {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::WrapperDigestMismatch);
    }

    let proof_upload_authority: [u8; 32] = bytes
        [PROOF_UPLOAD_AUTHORITY_OFFSET..CLOSE_REFUND_AUTHORITY_OFFSET]
        .try_into()
        .unwrap();
    if proof_upload_authority == [0u8; 32] {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ZeroProofUploadAuthority);
    }
    let close_refund_authority: [u8; 32] = bytes[CLOSE_REFUND_AUTHORITY_OFFSET..RESERVED_OFFSET]
        .try_into()
        .unwrap();
    if close_refund_authority == [0u8; 32] {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ZeroCloseRefundAuthority);
    }

    let status = match bytes[6] {
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_PENDING => {
            PoolV1AuthorizationReceiptAccountStatusV1::Pending
        }
        POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_VERIFIED => {
            PoolV1AuthorizationReceiptAccountStatusV1::Verified
        }
        _ => return Err(PoolV1AuthorizationReceiptAccountErrorV1::WrongStatus),
    };
    let pda_bump = bytes[7];
    let verified_slot = u64::from_le_bytes(
        bytes[VERIFIED_SLOT_OFFSET..VERIFIER_PROGRAM_OFFSET]
            .try_into()
            .unwrap(),
    );
    let verifier_program: [u8; 32] = bytes[VERIFIER_PROGRAM_OFFSET..PROOF_ACCOUNT_OFFSET]
        .try_into()
        .unwrap();
    let proof_account: [u8; 32] = bytes[PROOF_ACCOUNT_OFFSET..STATEMENT_DIGEST_OFFSET]
        .try_into()
        .unwrap();
    let statement_digest: [u8; 32] = bytes[STATEMENT_DIGEST_OFFSET..BINDING_DIGEST_OFFSET]
        .try_into()
        .unwrap();
    let binding_digest: [u8; 32] = bytes[BINDING_DIGEST_OFFSET..REQUEST_DIGEST_OFFSET]
        .try_into()
        .unwrap();
    let request_digest: [u8; 32] = bytes[REQUEST_DIGEST_OFFSET..PROOF_UPLOAD_AUTHORITY_OFFSET]
        .try_into()
        .unwrap();

    let receipt = match status {
        PoolV1AuthorizationReceiptAccountStatusV1::Pending => {
            if verified_slot != 0 {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::NonZeroPendingSlot);
            }
            if bytes[RECEIPT_OFFSET..WRAPPER_DIGEST_OFFSET]
                .iter()
                .any(|byte| *byte != 0)
            {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::NonZeroPendingBody);
            }
            None
        }
        PoolV1AuthorizationReceiptAccountStatusV1::Verified => {
            let receipt = decode_pool_v1_authorization_receipt_v1(
                &bytes[RECEIPT_OFFSET..WRAPPER_DIGEST_OFFSET],
                hash,
            )?;
            if receipt.pda_bump != pda_bump {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::ReceiptBumpMismatch);
            }
            if receipt.verified_slot != verified_slot {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::ReceiptSlotMismatch);
            }
            if receipt.binding.verifier_program != verifier_program {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::VerifierProgramMismatch);
            }
            if receipt.binding.proof_account != proof_account {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::ProofAccountMismatch);
            }
            if receipt.binding.statement_digest != statement_digest {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::StatementDigestMismatch);
            }
            if pool_v1_authorization_receipt_binding_digest_v1(&receipt.binding, hash)?
                != binding_digest
            {
                return Err(PoolV1AuthorizationReceiptAccountErrorV1::BindingDigestMismatch);
            }
            Some(receipt)
        }
    };

    Ok(PoolV1AuthorizationReceiptAccountV1 {
        status,
        pda_bump,
        verified_slot,
        verifier_program,
        proof_account,
        statement_digest,
        binding_digest,
        request_digest,
        proof_upload_authority,
        close_refund_authority,
        receipt,
    })
}

pub fn validate_pool_v1_authorization_receipt_account_request_v1(
    account: &PoolV1AuthorizationReceiptAccountV1,
    request: &VerifierDispatchRequestV1<'_>,
    hash: HashFn,
) -> Result<(), PoolV1AuthorizationReceiptAccountErrorV1> {
    if account.verifier_program != request.binding.verifier_program {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::VerifierProgramMismatch);
    }
    if account.proof_account != request.binding.proof_account {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ProofAccountMismatch);
    }
    if account.statement_digest != request.binding.statement_digest {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::StatementDigestMismatch);
    }
    if account.binding_digest
        != pool_v1_authorization_receipt_binding_digest_v1(&request.binding, hash)?
    {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::BindingDigestMismatch);
    }
    if account.request_digest != pool_v1_authorization_receipt_request_digest_v1(request, hash)? {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::RequestDigestMismatch);
    }
    if let Some(receipt) = account.receipt {
        if receipt.binding != request.binding {
            return Err(PoolV1AuthorizationReceiptAccountErrorV1::ReceiptBindingMismatch);
        }
    }
    Ok(())
}

pub fn validate_pool_v1_authorization_receipt_account_pda_inputs_v1(
    account: &PoolV1AuthorizationReceiptAccountV1,
    expected: &PoolV1AuthorizationReceiptPdaInputsV1,
) -> Result<(), PoolV1AuthorizationReceiptAccountErrorV1> {
    if account.pda_inputs() != *expected {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::PdaInputsMismatch);
    }
    Ok(())
}

/// The only state-changing operation: a canonical pending image becomes one
/// canonical finalized image.  Every commitment/authority byte is copied
/// unchanged; only status, verified slot, nested ASVA body and wrapper digest
/// change.  Supplying a finalized image fails before any output is returned.
pub fn finalize_pool_v1_authorization_receipt_account_v1(
    pending_bytes: &[u8],
    request: &VerifierDispatchRequestV1<'_>,
    receipt: &PoolV1AuthorizationReceiptV1,
    hash: HashFn,
) -> Result<
    [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES],
    PoolV1AuthorizationReceiptAccountErrorV1,
> {
    let pending = decode_pool_v1_authorization_receipt_account_v1(pending_bytes, hash)?;
    if pending.status != PoolV1AuthorizationReceiptAccountStatusV1::Pending {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::AlreadyFinalized);
    }
    validate_pool_v1_authorization_receipt_account_request_v1(&pending, request, hash)?;
    if receipt.binding != request.binding {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ReceiptBindingMismatch);
    }
    if receipt.pda_bump != pending.pda_bump {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::ReceiptBumpMismatch);
    }
    let encoded_receipt = encode_pool_v1_authorization_receipt_v1(receipt, hash)?;

    let pending_bytes: &[u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] = pending_bytes
        .try_into()
        .map_err(|_| PoolV1AuthorizationReceiptAccountErrorV1::WrongLength)?;
    let mut output = *pending_bytes;
    output[6] = POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_STATUS_VERIFIED;
    output[VERIFIED_SLOT_OFFSET..VERIFIER_PROGRAM_OFFSET]
        .copy_from_slice(&receipt.verified_slot.to_le_bytes());
    output[RECEIPT_OFFSET..WRAPPER_DIGEST_OFFSET].copy_from_slice(&encoded_receipt);
    let digest = wrapper_digest_v1(&output[..WRAPPER_DIGEST_OFFSET], hash);
    output[WRAPPER_DIGEST_OFFSET..].copy_from_slice(&digest);

    let finalized = decode_pool_v1_authorization_receipt_account_v1(&output, hash)?;
    validate_pool_v1_authorization_receipt_account_request_v1(&finalized, request, hash)?;
    Ok(output)
}

/// Pure close/refund authorization.  The account bytes are borrowed
/// immutably and this function returns only an authorization record; a Solana
/// implementation may then delete the verifier-owned account and refund its
/// lamports, but must not rewrite data as part of close authorization.
pub fn authorize_close_pool_v1_authorization_receipt_account_v1(
    account_bytes: &[u8],
    signed_close_authority: Option<[u8; 32]>,
    refund_destination: [u8; 32],
    hash: HashFn,
) -> Result<PoolV1AuthorizationReceiptCloseAuthorizationV1, PoolV1AuthorizationReceiptAccountErrorV1>
{
    let account = decode_pool_v1_authorization_receipt_account_v1(account_bytes, hash)?;
    let signer = signed_close_authority
        .ok_or(PoolV1AuthorizationReceiptAccountErrorV1::CloseAuthorityMismatch)?;
    if signer != account.close_refund_authority {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::CloseAuthorityMismatch);
    }
    if refund_destination != account.close_refund_authority {
        return Err(PoolV1AuthorizationReceiptAccountErrorV1::RefundDestinationMismatch);
    }
    Ok(PoolV1AuthorizationReceiptCloseAuthorizationV1 {
        close_authority: signer,
        refund_destination,
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use sha2::{Digest as _, Sha256};

    use super::*;
    use crate::{
        pool_v1::{
            verifier_statement_payload_digest_v1, PoolV1TransitionKind,
            POOL_V1_HISTORICAL_ANCHOR_VERSION,
        },
        poseidon2::Digest,
    };

    const STATEMENT_PAYLOAD: [u8; 216] = [42u8; 216];
    const UPLOAD_AUTHORITY: [u8; 32] = [10u8; 32];
    const CLOSE_AUTHORITY: [u8; 32] = [11u8; 32];
    const PDA_BUMP: u8 = 247;

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
        let profile_binding = [2u8; 32];
        let release_binding = [3u8; 32];
        let statement_digest = verifier_statement_payload_digest_v1(
            POOL_V1_HISTORICAL_ANCHOR_VERSION,
            &profile_binding,
            &release_binding,
            &STATEMENT_PAYLOAD,
            sha256,
        )
        .unwrap();
        VerifierDispatchBindingV1 {
            statement_version: POOL_V1_HISTORICAL_ANCHOR_VERSION,
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            verifier_program: [1u8; 32],
            profile_binding,
            release_binding,
            pool: [4u8; 32],
            deployment_domain: [5u8; 32],
            anchor_sequence: 19,
            anchor_root: digest(100),
            nullifier: digest(300),
            statement_digest,
            envelope_digest: [7u8; 32],
            proof_account: [8u8; 32],
            proof_body_digest: [9u8; 32],
            proof_body_length: 30_504,
            statement_payload_length: STATEMENT_PAYLOAD.len() as u32,
        }
    }

    fn request() -> VerifierDispatchRequestV1<'static> {
        VerifierDispatchRequestV1 {
            binding: binding(),
            statement_payload: &STATEMENT_PAYLOAD,
        }
    }

    fn pending() -> [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] {
        let request = request();
        initialize_pool_v1_authorization_receipt_account_v1(
            &request,
            request.binding.proof_account,
            UPLOAD_AUTHORITY,
            Some(UPLOAD_AUTHORITY),
            CLOSE_AUTHORITY,
            PDA_BUMP,
            sha256,
        )
        .unwrap()
    }

    fn receipt() -> PoolV1AuthorizationReceiptV1 {
        PoolV1AuthorizationReceiptV1 {
            pda_bump: PDA_BUMP,
            verified_slot: 900,
            binding: binding(),
        }
    }

    fn finalized() -> [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES] {
        finalize_pool_v1_authorization_receipt_account_v1(
            &pending(),
            &request(),
            &receipt(),
            sha256,
        )
        .unwrap()
    }

    fn refresh_wrapper_digest(bytes: &mut [u8; POOL_V1_AUTHORIZATION_RECEIPT_ACCOUNT_BYTES]) {
        let digest = wrapper_digest_v1(&bytes[..WRAPPER_DIGEST_OFFSET], sha256);
        bytes[WRAPPER_DIGEST_OFFSET..].copy_from_slice(&digest);
    }

    #[test]
    fn pending_and_finalized_roundtrip_with_exact_layout() {
        let request = request();
        let pending = pending();
        assert_eq!(pending.len(), 720);
        assert_eq!(&pending[..4], b"ASRA");
        assert_eq!(pending[6], 0);
        assert_eq!(&pending[8..16], &[0u8; 8]);
        assert_eq!(&pending[240..256], &[0u8; 16]);
        assert!(pending[256..688].iter().all(|byte| *byte == 0));

        let decoded_pending =
            decode_pool_v1_authorization_receipt_account_v1(&pending, sha256).unwrap();
        assert_eq!(
            decoded_pending.status,
            PoolV1AuthorizationReceiptAccountStatusV1::Pending
        );
        assert_eq!(decoded_pending.receipt, None);
        validate_pool_v1_authorization_receipt_account_request_v1(
            &decoded_pending,
            &request,
            sha256,
        )
        .unwrap();

        let finalized = finalize_pool_v1_authorization_receipt_account_v1(
            &pending,
            &request,
            &receipt(),
            sha256,
        )
        .unwrap();
        let decoded = decode_pool_v1_authorization_receipt_account_v1(&finalized, sha256).unwrap();
        assert_eq!(
            decoded.status,
            PoolV1AuthorizationReceiptAccountStatusV1::Verified
        );
        assert_eq!(decoded.verified_slot, 900);
        assert_eq!(decoded.receipt, Some(receipt()));
        validate_pool_v1_authorization_receipt_account_request_v1(&decoded, &request, sha256)
            .unwrap();

        // Finalization changes only status, slot, nested receipt and wrapper
        // digest. Every authority and binding byte is immutable.
        assert_eq!(&pending[0..6], &finalized[0..6]);
        assert_eq!(pending[7], finalized[7]);
        assert_eq!(&pending[16..256], &finalized[16..256]);
    }

    #[test]
    fn every_pending_and_finalized_byte_is_authenticated() {
        for original in [pending(), finalized()] {
            for offset in 0..original.len() {
                let mut changed = original;
                changed[offset] ^= 1;
                assert!(
                    decode_pool_v1_authorization_receipt_account_v1(&changed, sha256).is_err(),
                    "mutation at byte {offset} accepted"
                );
            }
        }
    }

    #[test]
    fn wrong_upload_authority_and_preinitialization_inputs_reject() {
        let request = request();
        assert_eq!(
            initialize_pool_v1_authorization_receipt_account_v1(
                &request,
                [99u8; 32],
                UPLOAD_AUTHORITY,
                Some(UPLOAD_AUTHORITY),
                CLOSE_AUTHORITY,
                PDA_BUMP,
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::ProofAccountMismatch)
        );
        assert_eq!(
            initialize_pool_v1_authorization_receipt_account_v1(
                &request,
                request.binding.proof_account,
                UPLOAD_AUTHORITY,
                None,
                CLOSE_AUTHORITY,
                PDA_BUMP,
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::MissingProofUploadAuthoritySignature)
        );
        assert_eq!(
            initialize_pool_v1_authorization_receipt_account_v1(
                &request,
                request.binding.proof_account,
                UPLOAD_AUTHORITY,
                Some([12u8; 32]),
                CLOSE_AUTHORITY,
                PDA_BUMP,
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::ProofUploadAuthorityMismatch)
        );
        assert_eq!(
            initialize_pool_v1_authorization_receipt_account_v1(
                &request,
                request.binding.proof_account,
                [0u8; 32],
                Some([0u8; 32]),
                CLOSE_AUTHORITY,
                PDA_BUMP,
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::ZeroProofUploadAuthority)
        );
    }

    #[test]
    fn wrong_request_binding_and_pda_inputs_reject() {
        let account = decode_pool_v1_authorization_receipt_account_v1(&pending(), sha256).unwrap();
        let mut wrong_binding = binding();
        wrong_binding.proof_body_digest[0] ^= 1;
        let wrong_request = VerifierDispatchRequestV1 {
            binding: wrong_binding,
            statement_payload: &STATEMENT_PAYLOAD,
        };
        assert_eq!(
            validate_pool_v1_authorization_receipt_account_request_v1(
                &account,
                &wrong_request,
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::BindingDigestMismatch)
        );

        let correct =
            pool_v1_authorization_receipt_pda_inputs_for_binding_v1(&binding(), PDA_BUMP, sha256)
                .unwrap();
        assert_eq!(account.pda_inputs(), correct);
        for wrong in [
            PoolV1AuthorizationReceiptPdaInputsV1 {
                proof_account: [21u8; 32],
                ..correct
            },
            PoolV1AuthorizationReceiptPdaInputsV1 {
                statement_digest: [22u8; 32],
                ..correct
            },
            PoolV1AuthorizationReceiptPdaInputsV1 {
                binding_digest: [23u8; 32],
                ..correct
            },
            PoolV1AuthorizationReceiptPdaInputsV1 {
                bump: correct.bump.wrapping_add(1),
                ..correct
            },
        ] {
            assert_eq!(
                validate_pool_v1_authorization_receipt_account_pda_inputs_v1(&account, &wrong),
                Err(PoolV1AuthorizationReceiptAccountErrorV1::PdaInputsMismatch)
            );
        }
    }

    #[test]
    fn nested_receipt_and_double_finalize_fail_closed() {
        let mut wrong_receipt = receipt();
        wrong_receipt.binding.release_binding[0] ^= 1;
        assert_eq!(
            finalize_pool_v1_authorization_receipt_account_v1(
                &pending(),
                &request(),
                &wrong_receipt,
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::ReceiptBindingMismatch)
        );

        let finalized = finalized();
        assert_eq!(
            finalize_pool_v1_authorization_receipt_account_v1(
                &finalized,
                &request(),
                &receipt(),
                sha256,
            ),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::AlreadyFinalized)
        );

        // Even an attacker able to recompute the outer checksum cannot turn a
        // malformed nested body into a valid finalized account.
        let mut malformed = finalized;
        malformed[RECEIPT_OFFSET] ^= 1;
        refresh_wrapper_digest(&mut malformed);
        assert!(matches!(
            decode_pool_v1_authorization_receipt_account_v1(&malformed, sha256),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::Receipt(_))
        ));
    }

    #[test]
    fn close_authority_is_exact_and_authorization_never_rewrites_data() {
        for bytes in [pending(), finalized()] {
            let before = bytes;
            assert_eq!(
                authorize_close_pool_v1_authorization_receipt_account_v1(
                    &bytes,
                    Some(CLOSE_AUTHORITY),
                    CLOSE_AUTHORITY,
                    sha256,
                ),
                Ok(PoolV1AuthorizationReceiptCloseAuthorizationV1 {
                    close_authority: CLOSE_AUTHORITY,
                    refund_destination: CLOSE_AUTHORITY,
                })
            );
            assert_eq!(bytes, before);
            assert_eq!(
                authorize_close_pool_v1_authorization_receipt_account_v1(
                    &bytes,
                    Some([31u8; 32]),
                    CLOSE_AUTHORITY,
                    sha256,
                ),
                Err(PoolV1AuthorizationReceiptAccountErrorV1::CloseAuthorityMismatch)
            );
            assert_eq!(
                authorize_close_pool_v1_authorization_receipt_account_v1(
                    &bytes,
                    Some(CLOSE_AUTHORITY),
                    [32u8; 32],
                    sha256,
                ),
                Err(PoolV1AuthorizationReceiptAccountErrorV1::RefundDestinationMismatch)
            );
        }
    }

    #[test]
    fn canonical_reserved_pending_slot_and_body_checks_survive_rehashing() {
        let mut changed = pending();
        changed[RESERVED_OFFSET] = 1;
        refresh_wrapper_digest(&mut changed);
        assert_eq!(
            decode_pool_v1_authorization_receipt_account_v1(&changed, sha256),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::NonZeroReserved)
        );

        let mut changed = pending();
        changed[VERIFIED_SLOT_OFFSET] = 1;
        refresh_wrapper_digest(&mut changed);
        assert_eq!(
            decode_pool_v1_authorization_receipt_account_v1(&changed, sha256),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::NonZeroPendingSlot)
        );

        let mut changed = pending();
        changed[RECEIPT_OFFSET + 17] = 1;
        refresh_wrapper_digest(&mut changed);
        assert_eq!(
            decode_pool_v1_authorization_receipt_account_v1(&changed, sha256),
            Err(PoolV1AuthorizationReceiptAccountErrorV1::NonZeroPendingBody)
        );
    }
}
