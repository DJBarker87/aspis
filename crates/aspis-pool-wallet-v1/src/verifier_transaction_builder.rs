//! Exact unsigned transaction plumbing for the native Pool V1 Tag-73 verifier.
//!
//! This module owns no key material and performs no RPC, simulation, signing,
//! or submission.  It constructs the canonical 600-byte `ASVQ` request, its
//! verifier-owned authorization-receipt PDA, and the append-only proof/receipt
//! lifecycle instructions used by the production verifier program.

use std::collections::BTreeSet;

use aspis_statement::pool_v1::{
    encode_pool_v1_private_transfer_public_v1, encode_pool_v1_withdrawal_public_v1,
    encode_verifier_dispatch_request_v1, pool_v1_authorization_receipt_binding_digest_v1,
    v7_pool_native_tag73_proof_body_bytes, verifier_dispatch_binding_from_envelope_v1,
    verifier_proof_body_digest_v1, HistoricalAnchorEnvelopeV1, PoolV1PrivateTransferPublicV1,
    PoolV1TransitionKind, PoolV1WithdrawalPublicV1, VerifierDispatchBindingV1,
    VerifierDispatchRequestV1, POOL_V1_AUTHORIZATION_RECEIPT_SEED, POOL_V1_PAYMENT_STATEMENT_BYTES,
    POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES,
    V7_POOL_NATIVE_TAG73_PROFILE_BINDING, V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
    V7_POOL_NATIVE_TAG73_REQUEST_BYTES,
};
use sha2::{Digest as _, Sha256};
use solana_program::{
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    system_instruction,
};
use solana_sdk_ids::system_program;

use crate::transaction_builder::PreparedSettlementRouteAccountsV1;

/// Frozen numeric verifier tags.  They are append-only production ABI bytes,
/// not Borsh values reconstructed from a local enum.
pub const V7_POOL_PROOF_INIT_TAG: u8 = 0;
pub const V7_POOL_PROOF_UPLOAD_TAG: u8 = 1;
pub const V7_POOL_PROOF_FINALIZE_TAG: u8 = 62;
pub const V7_POOL_PROOF_CLOSE_TAG: u8 = 64;
pub const V7_POOL_RECEIPT_INITIALIZE_TAG: u8 = 74;
pub const V7_POOL_RECEIPT_FINALIZE_TAG: u8 = 75;
pub const V7_POOL_RECEIPT_CLOSE_TAG: u8 = 76;

/// Conservative upload payload used by the V6/V7 release lifecycle.  Each
/// chunk is a separate transaction instruction; no transaction is assembled
/// or submitted here.
pub const V7_POOL_PROOF_UPLOAD_CHUNK_BYTES: usize = 960;

const _: () = assert!(V7_POOL_NATIVE_TAG73_REQUEST_BYTES == 600);
const _: () = assert!(POOL_V1_PAYMENT_STATEMENT_BYTES == 216);
const _: () = assert!(POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES == 40);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolVerifierTransactionBuilderErrorV1 {
    UnpinnedProgramId,
    ZeroAccount,
    AccountAlias,
    ProofLengthOverflow,
    InvalidNativeProofLength,
    StatementFormat,
    DispatchFormat,
    ReceiptBindingFormat,
    WrongRequestLength,
}

/// Secret-free identity and canonical request for one proof authorization.
/// The proof bytes themselves are deliberately not retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePoolTag73AuthorizationPlanV1 {
    pub verifier_program: Pubkey,
    pub proof_account: Pubkey,
    pub receipt_account: Pubkey,
    pub receipt_bump: u8,
    pub frontier_nodes: usize,
    pub binding: VerifierDispatchBindingV1,
    pub request: [u8; V7_POOL_NATIVE_TAG73_REQUEST_BYTES],
}

fn sha256_parts_v1(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

fn require_program_and_accounts(
    verifier_program: Pubkey,
    accounts: &[Pubkey],
) -> Result<(), PoolVerifierTransactionBuilderErrorV1> {
    if verifier_program == Pubkey::default() {
        return Err(PoolVerifierTransactionBuilderErrorV1::UnpinnedProgramId);
    }
    if accounts.iter().any(|key| *key == Pubkey::default()) {
        return Err(PoolVerifierTransactionBuilderErrorV1::ZeroAccount);
    }
    if accounts.iter().any(|key| *key == verifier_program) {
        return Err(PoolVerifierTransactionBuilderErrorV1::AccountAlias);
    }
    let mut unique = BTreeSet::new();
    if !accounts.iter().all(|key| unique.insert(key.to_bytes())) {
        return Err(PoolVerifierTransactionBuilderErrorV1::AccountAlias);
    }
    Ok(())
}

fn frontier_nodes_for_exact_proof_length(proof_body_length: u32) -> Option<usize> {
    let mut nodes = V7_POOL_NATIVE_TAG73_MIN_FRONTIER_NODES;
    loop {
        match v7_pool_native_tag73_proof_body_bytes(nodes) {
            Some(length) if length == proof_body_length => return Some(nodes),
            Some(_) => nodes = nodes.checked_add(1)?,
            None => return None,
        }
    }
}

fn native_envelope_v1(
    transition_kind: PoolV1TransitionKind,
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor_sequence: u64,
    anchor_root: aspis_statement::Digest,
    nullifier: aspis_statement::Digest,
) -> HistoricalAnchorEnvelopeV1 {
    HistoricalAnchorEnvelopeV1 {
        transition_kind,
        pool,
        deployment_domain,
        anchor_sequence,
        anchor_root,
        nullifier,
        verifier_profile: V7_POOL_NATIVE_TAG73_PROFILE_BINDING,
        verifier_release: V7_POOL_NATIVE_TAG73_RELEASE_BINDING,
    }
}

fn build_native_authorization_plan_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    envelope: &HistoricalAnchorEnvelopeV1,
    statement_payload: &[u8; POOL_V1_PAYMENT_STATEMENT_BYTES],
    proof_body: &[u8],
) -> Result<NativePoolTag73AuthorizationPlanV1, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[proof_account])?;
    let proof_body_length = u32::try_from(proof_body.len())
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
    let frontier_nodes = frontier_nodes_for_exact_proof_length(proof_body_length)
        .ok_or(PoolVerifierTransactionBuilderErrorV1::InvalidNativeProofLength)?;
    let proof_body_digest = verifier_proof_body_digest_v1(proof_body, sha256_parts_v1);
    let binding = verifier_dispatch_binding_from_envelope_v1(
        verifier_program.to_bytes(),
        envelope,
        statement_payload,
        proof_account.to_bytes(),
        proof_body_digest,
        proof_body_length,
        sha256_parts_v1,
    )
    .map_err(|_| PoolVerifierTransactionBuilderErrorV1::DispatchFormat)?;
    let encoded = encode_verifier_dispatch_request_v1(
        &VerifierDispatchRequestV1 {
            binding,
            statement_payload,
        },
        sha256_parts_v1,
    )
    .map_err(|_| PoolVerifierTransactionBuilderErrorV1::DispatchFormat)?;
    let request: [u8; V7_POOL_NATIVE_TAG73_REQUEST_BYTES] = encoded
        .try_into()
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::WrongRequestLength)?;
    let binding_digest = pool_v1_authorization_receipt_binding_digest_v1(&binding, sha256_parts_v1)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::ReceiptBindingFormat)?;
    let (receipt_account, receipt_bump) = Pubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            proof_account.as_ref(),
            &binding.statement_digest,
            &binding_digest,
        ],
        &verifier_program,
    );
    Ok(NativePoolTag73AuthorizationPlanV1 {
        verifier_program,
        proof_account,
        receipt_account,
        receipt_bump,
        frontier_nodes,
        binding,
        request,
    })
}

/// Construct the exact native private-transfer `ASVQ` and receipt PDA from a
/// complete proof body and its public relation statement.
pub fn build_native_private_transfer_authorization_plan_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    statement: &PoolV1PrivateTransferPublicV1,
    proof_body: &[u8],
) -> Result<NativePoolTag73AuthorizationPlanV1, PoolVerifierTransactionBuilderErrorV1> {
    let payload = encode_pool_v1_private_transfer_public_v1(statement)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::StatementFormat)?;
    let envelope = native_envelope_v1(
        PoolV1TransitionKind::PrivateTransfer,
        statement.pool,
        statement.deployment_domain,
        statement.anchor_sequence,
        statement.anchor_root,
        statement.nullifier,
    );
    build_native_authorization_plan_v1(
        verifier_program,
        proof_account,
        &envelope,
        &payload,
        proof_body,
    )
}

/// Construct the exact native withdrawal `ASVQ` and receipt PDA from a
/// complete proof body and its public relation statement.
pub fn build_native_withdrawal_authorization_plan_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    statement: &PoolV1WithdrawalPublicV1,
    proof_body: &[u8],
) -> Result<NativePoolTag73AuthorizationPlanV1, PoolVerifierTransactionBuilderErrorV1> {
    let payload = encode_pool_v1_withdrawal_public_v1(statement)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::StatementFormat)?;
    let envelope = native_envelope_v1(
        PoolV1TransitionKind::Withdrawal,
        statement.pool,
        statement.deployment_domain,
        statement.anchor_sequence,
        statement.anchor_root,
        statement.nullifier,
    );
    build_native_authorization_plan_v1(
        verifier_program,
        proof_account,
        &envelope,
        &payload,
        proof_body,
    )
}

/// Create the exact-sized verifier-owned proof account.  Both payer and proof
/// account are signers when this instruction is later assembled and signed.
pub fn build_create_native_proof_account_instruction_v1(
    verifier_program: Pubkey,
    payer: Pubkey,
    proof_account: Pubkey,
    proof_body_length: u32,
    rent_lamports: u64,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[payer, proof_account])?;
    frontier_nodes_for_exact_proof_length(proof_body_length)
        .ok_or(PoolVerifierTransactionBuilderErrorV1::InvalidNativeProofLength)?;
    let space = (POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES as u64)
        .checked_add(u64::from(proof_body_length))
        .ok_or(PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
    Ok(system_instruction::create_account(
        &payer,
        &proof_account,
        rent_lamports,
        space,
        &verifier_program,
    ))
}

/// Bridge a finalized verifier receipt into the existing Pool prepared-plan
/// builders without allowing a relayer to substitute another receipt address.
pub fn prepared_settlement_route_from_authorization_plan_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
    plan_authority: Pubkey,
    registry_program: Pubkey,
) -> Result<PreparedSettlementRouteAccountsV1, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(
        plan.verifier_program,
        &[
            plan.proof_account,
            plan.receipt_account,
            plan_authority,
            registry_program,
        ],
    )?;
    Ok(PreparedSettlementRouteAccountsV1 {
        plan_authority,
        registry_program,
        authorization_receipt: plan.receipt_account,
    })
}

/// Initialize the exact `ASPU` header after the account has been created.
pub fn build_initialize_native_proof_instruction_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    upload_authority: Pubkey,
    proof_body_length: u32,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[proof_account, upload_authority])?;
    frontier_nodes_for_exact_proof_length(proof_body_length)
        .ok_or(PoolVerifierTransactionBuilderErrorV1::InvalidNativeProofLength)?;
    let mut data = Vec::with_capacity(5);
    data.push(V7_POOL_PROOF_INIT_TAG);
    data.extend_from_slice(&proof_body_length.to_le_bytes());
    Ok(Instruction {
        program_id: verifier_program,
        accounts: vec![
            AccountMeta::new(proof_account, true),
            AccountMeta::new_readonly(upload_authority, true),
        ],
        data,
    })
}

/// Split a complete proof into the frozen 960-byte upload instructions.  The
/// final chunk is shorter; offsets cover the body exactly once in order.
pub fn build_native_proof_upload_instructions_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    upload_authority: Pubkey,
    proof_body: &[u8],
) -> Result<Vec<Instruction>, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[proof_account, upload_authority])?;
    let length = u32::try_from(proof_body.len())
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
    frontier_nodes_for_exact_proof_length(length)
        .ok_or(PoolVerifierTransactionBuilderErrorV1::InvalidNativeProofLength)?;
    let mut instructions =
        Vec::with_capacity(proof_body.len().div_ceil(V7_POOL_PROOF_UPLOAD_CHUNK_BYTES));
    for (chunk_index, chunk) in proof_body
        .chunks(V7_POOL_PROOF_UPLOAD_CHUNK_BYTES)
        .enumerate()
    {
        let offset = chunk_index
            .checked_mul(V7_POOL_PROOF_UPLOAD_CHUNK_BYTES)
            .and_then(|value| u32::try_from(value).ok())
            .ok_or(PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
        let chunk_length = u32::try_from(chunk.len())
            .map_err(|_| PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
        let mut data = Vec::with_capacity(9 + chunk.len());
        data.push(V7_POOL_PROOF_UPLOAD_TAG);
        data.extend_from_slice(&offset.to_le_bytes());
        data.extend_from_slice(&chunk_length.to_le_bytes());
        data.extend_from_slice(chunk);
        instructions.push(Instruction {
            program_id: verifier_program,
            accounts: vec![
                AccountMeta::new(proof_account, false),
                AccountMeta::new_readonly(upload_authority, true),
            ],
            data,
        });
    }
    Ok(instructions)
}

/// Create the pending verifier receipt while the proof remains unsealed.
pub fn build_initialize_native_authorization_receipt_instruction_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
    upload_authority: Pubkey,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(
        plan.verifier_program,
        &[plan.proof_account, plan.receipt_account, upload_authority],
    )?;
    let mut data = Vec::with_capacity(1 + V7_POOL_NATIVE_TAG73_REQUEST_BYTES);
    data.push(V7_POOL_RECEIPT_INITIALIZE_TAG);
    data.extend_from_slice(&plan.request);
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new_readonly(plan.proof_account, false),
            AccountMeta::new(plan.receipt_account, false),
            AccountMeta::new(upload_authority, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data,
    })
}

/// Irreversibly seal the proof upload after its pending receipt exists.
pub fn build_finalize_native_proof_instruction_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    upload_authority: Pubkey,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[proof_account, upload_authority])?;
    Ok(Instruction {
        program_id: verifier_program,
        accounts: vec![
            AccountMeta::new(proof_account, false),
            AccountMeta::new_readonly(upload_authority, true),
        ],
        data: vec![V7_POOL_PROOF_FINALIZE_TAG],
    })
}

/// Verify the sealed proof and atomically finalize its exact pending receipt.
pub fn build_finalize_native_authorization_receipt_instruction_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(
        plan.verifier_program,
        &[plan.proof_account, plan.receipt_account],
    )?;
    let mut data = Vec::with_capacity(1 + V7_POOL_NATIVE_TAG73_REQUEST_BYTES);
    data.push(V7_POOL_RECEIPT_FINALIZE_TAG);
    data.extend_from_slice(&plan.request);
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new_readonly(plan.proof_account, false),
            AccountMeta::new(plan.receipt_account, false),
        ],
        data,
    })
}

/// Build a read-only native `ASVQ` verification instruction.  The successful
/// program return data is the exact 384-byte `ASVS` result.
pub fn build_verify_native_asvq_instruction_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(plan.verifier_program, &[plan.proof_account])?;
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![AccountMeta::new_readonly(plan.proof_account, false)],
        data: plan.request.to_vec(),
    })
}

/// Close a pending or verified authorization receipt to its immutable refund
/// authority.  The on-chain receipt image authenticates that authority.
pub fn build_close_native_authorization_receipt_instruction_v1(
    verifier_program: Pubkey,
    receipt_account: Pubkey,
    refund_authority: Pubkey,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[receipt_account, refund_authority])?;
    Ok(Instruction {
        program_id: verifier_program,
        accounts: vec![
            AccountMeta::new(receipt_account, false),
            AccountMeta::new(refund_authority, true),
        ],
        data: vec![V7_POOL_RECEIPT_CLOSE_TAG],
    })
}

/// Close a sealed proof account and refund its rent.  Both accounts sign so a
/// third party cannot steal the ephemeral proof account's balance.
pub fn build_close_native_proof_instruction_v1(
    verifier_program: Pubkey,
    proof_account: Pubkey,
    refund_account: Pubkey,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(verifier_program, &[proof_account, refund_account])?;
    Ok(Instruction {
        program_id: verifier_program,
        accounts: vec![
            AccountMeta::new(proof_account, true),
            AccountMeta::new(refund_account, true),
        ],
        data: vec![V7_POOL_PROOF_CLOSE_TAG],
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_statement::{
        pool_v1::{
            decode_verifier_dispatch_request_v1,
            pool_v1_authorization_receipt_pda_inputs_for_binding_v1,
            v7_pool_native_tag73_proof_body_bytes,
        },
        Digest,
    };

    use super::*;

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + index as u32))
    }

    fn proof() -> Vec<u8> {
        vec![0x5a; v7_pool_native_tag73_proof_body_bytes(203).unwrap() as usize]
    }

    fn transfer() -> PoolV1PrivateTransferPublicV1 {
        PoolV1PrivateTransferPublicV1 {
            pool: key(3).to_bytes(),
            deployment_domain: [4u8; 32],
            anchor_sequence: 17,
            anchor_root: digest(100),
            nullifier: digest(200),
            asset_id: M31(7),
            recipient_commitment: digest(300),
            change_commitment: digest(400),
        }
    }

    fn withdrawal() -> PoolV1WithdrawalPublicV1 {
        PoolV1WithdrawalPublicV1 {
            pool: key(3).to_bytes(),
            deployment_domain: [4u8; 32],
            anchor_sequence: 17,
            anchor_root: digest(100),
            nullifier: digest(200),
            asset_id: M31(7),
            amount: 9,
            destination_token_account: key(8).to_bytes(),
            change_commitment: digest(400),
        }
    }

    #[test]
    fn native_requests_are_exact_and_receipt_pda_is_canonical_for_both_kinds() {
        let verifier = key(1);
        let proof_key = key(2);
        for plan in [
            build_native_private_transfer_authorization_plan_v1(
                verifier,
                proof_key,
                &transfer(),
                &proof(),
            )
            .unwrap(),
            build_native_withdrawal_authorization_plan_v1(
                verifier,
                proof_key,
                &withdrawal(),
                &proof(),
            )
            .unwrap(),
        ] {
            assert_eq!(plan.request.len(), 600);
            assert_eq!(plan.frontier_nodes, 203);
            assert_eq!(
                plan.binding.profile_binding,
                V7_POOL_NATIVE_TAG73_PROFILE_BINDING
            );
            assert_eq!(
                plan.binding.release_binding,
                V7_POOL_NATIVE_TAG73_RELEASE_BINDING
            );
            assert_eq!(plan.binding.proof_account, proof_key.to_bytes());
            let decoded =
                decode_verifier_dispatch_request_v1(&plan.request, sha256_parts_v1).unwrap();
            assert_eq!(decoded.binding, plan.binding);

            let inputs = pool_v1_authorization_receipt_pda_inputs_for_binding_v1(
                &plan.binding,
                plan.receipt_bump,
                sha256_parts_v1,
            )
            .unwrap();
            let dynamic = inputs.dynamic_seeds();
            assert_eq!(
                Pubkey::create_program_address(
                    &[
                        POOL_V1_AUTHORIZATION_RECEIPT_SEED,
                        &dynamic[0],
                        &dynamic[1],
                        &dynamic[2],
                        &[plan.receipt_bump],
                    ],
                    &verifier,
                )
                .unwrap(),
                plan.receipt_account
            );
        }
    }

    #[test]
    fn proof_upload_and_receipt_lifecycle_freeze_exact_wires_accounts_and_order() {
        let verifier = key(1);
        let proof_key = key(2);
        let upload_authority = key(9);
        let proof = proof();
        let plan = build_native_private_transfer_authorization_plan_v1(
            verifier,
            proof_key,
            &transfer(),
            &proof,
        )
        .unwrap();

        let init = build_initialize_native_proof_instruction_v1(
            verifier,
            proof_key,
            upload_authority,
            proof.len() as u32,
        )
        .unwrap();
        assert_eq!(init.data[0], V7_POOL_PROOF_INIT_TAG);
        assert_eq!(&init.data[1..], &(proof.len() as u32).to_le_bytes());
        assert!(init.accounts[0].is_signer && init.accounts[0].is_writable);
        assert!(init.accounts[1].is_signer && !init.accounts[1].is_writable);

        let create = build_create_native_proof_account_instruction_v1(
            verifier,
            key(10),
            proof_key,
            proof.len() as u32,
            123_456,
        )
        .unwrap();
        assert_eq!(create.program_id, system_program::id());
        assert_eq!(create.accounts[0], AccountMeta::new(key(10), true));
        assert_eq!(create.accounts[1], AccountMeta::new(proof_key, true));

        let uploads = build_native_proof_upload_instructions_v1(
            verifier,
            proof_key,
            upload_authority,
            &proof,
        )
        .unwrap();
        assert_eq!(uploads.len(), proof.len().div_ceil(960));
        let mut recovered = vec![0u8; proof.len()];
        for instruction in &uploads {
            assert_eq!(instruction.data[0], V7_POOL_PROOF_UPLOAD_TAG);
            let offset = u32::from_le_bytes(instruction.data[1..5].try_into().unwrap()) as usize;
            let length = u32::from_le_bytes(instruction.data[5..9].try_into().unwrap()) as usize;
            assert_eq!(instruction.data.len(), 9 + length);
            recovered[offset..offset + length].copy_from_slice(&instruction.data[9..]);
        }
        assert_eq!(recovered, proof);

        let receipt_init =
            build_initialize_native_authorization_receipt_instruction_v1(&plan, upload_authority)
                .unwrap();
        assert_eq!(receipt_init.data[0], V7_POOL_RECEIPT_INITIALIZE_TAG);
        assert_eq!(&receipt_init.data[1..], &plan.request);
        assert_eq!(receipt_init.accounts.len(), 4);
        assert_eq!(
            receipt_init.accounts[0],
            AccountMeta::new_readonly(proof_key, false)
        );
        assert_eq!(
            receipt_init.accounts[1],
            AccountMeta::new(plan.receipt_account, false)
        );
        assert_eq!(
            receipt_init.accounts[2],
            AccountMeta::new(upload_authority, true)
        );

        let seal =
            build_finalize_native_proof_instruction_v1(verifier, proof_key, upload_authority)
                .unwrap();
        assert_eq!(seal.data, [V7_POOL_PROOF_FINALIZE_TAG]);
        let receipt_finalize =
            build_finalize_native_authorization_receipt_instruction_v1(&plan).unwrap();
        assert_eq!(receipt_finalize.data[0], V7_POOL_RECEIPT_FINALIZE_TAG);
        assert_eq!(&receipt_finalize.data[1..], &plan.request);
        assert_eq!(
            receipt_finalize.accounts,
            vec![
                AccountMeta::new_readonly(proof_key, false),
                AccountMeta::new(plan.receipt_account, false),
            ]
        );
        let direct = build_verify_native_asvq_instruction_v1(&plan).unwrap();
        assert_eq!(direct.data, plan.request);
        assert_eq!(
            direct.accounts,
            [AccountMeta::new_readonly(proof_key, false)]
        );

        let route =
            prepared_settlement_route_from_authorization_plan_v1(&plan, key(11), key(12)).unwrap();
        assert_eq!(route.authorization_receipt, plan.receipt_account);
        let close_receipt = build_close_native_authorization_receipt_instruction_v1(
            verifier,
            plan.receipt_account,
            upload_authority,
        )
        .unwrap();
        assert_eq!(close_receipt.data, [V7_POOL_RECEIPT_CLOSE_TAG]);
        let close_proof =
            build_close_native_proof_instruction_v1(verifier, proof_key, upload_authority).unwrap();
        assert_eq!(close_proof.data, [V7_POOL_PROOF_CLOSE_TAG]);
        assert!(close_proof.accounts.iter().all(|meta| meta.is_signer));
    }

    #[test]
    fn invalid_lengths_aliases_and_zero_or_unpinned_accounts_fail_closed() {
        let verifier = key(1);
        let proof_key = key(2);
        let mut short = proof();
        short.pop();
        assert_eq!(
            build_native_private_transfer_authorization_plan_v1(
                verifier,
                proof_key,
                &transfer(),
                &short,
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidNativeProofLength
        );
        assert_eq!(
            build_initialize_native_proof_instruction_v1(
                verifier,
                proof_key,
                proof_key,
                proof().len() as u32,
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::AccountAlias
        );
        assert_eq!(
            build_close_native_proof_instruction_v1(verifier, proof_key, proof_key).unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::AccountAlias
        );
        assert_eq!(
            build_create_native_proof_account_instruction_v1(
                Pubkey::default(),
                key(3),
                proof_key,
                proof().len() as u32,
                1,
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::UnpinnedProgramId
        );
    }
}
