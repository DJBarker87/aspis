//! Exact unsigned transaction plumbing for the native Pool V1 Tag-73 verifier.
//!
//! This module owns no key material and performs no RPC, simulation, signing,
//! or submission.  It constructs the canonical 600-byte `ASVQ` request, its
//! verifier-owned authorization-receipt PDA, and the append-only proof/receipt
//! lifecycle instructions used by the production verifier program.

use std::collections::BTreeSet;

use aspis_pool::{PrivateTransferStatementV1, WithdrawalStatementV1};
use aspis_statement::pool_v1::{
    decode_pool_v1_private_transfer_public_v1, decode_pool_v1_withdrawal_public_v1,
    decode_verifier_dispatch_request_v1, encode_pool_v1_private_transfer_public_v1,
    encode_pool_v1_withdrawal_public_v1, encode_verifier_dispatch_request_v1,
    pool_v1_authorization_receipt_binding_digest_v1, v7_pool_native_tag73_proof_body_bytes,
    verifier_dispatch_binding_from_envelope_v1, verifier_proof_body_digest_v1,
    HistoricalAnchorEnvelopeV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
    PoolV1WithdrawalPublicV1, VerifierDispatchBindingV1, VerifierDispatchRequestV1,
    POOL_V1_AUTHORIZATION_RECEIPT_SEED, POOL_V1_PAYMENT_STATEMENT_BYTES,
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
use solana_sdk_ids::{
    address_lookup_table, bpf_loader, bpf_loader_deprecated, bpf_loader_upgradeable,
    compute_budget, config, ed25519_program, feature, incinerator, loader_v4, native_loader,
    secp256k1_program, secp256r1_program, stake, system_program, vote, zk_elgamal_proof_program,
    zk_token_proof_program,
};

use crate::transaction_builder::{
    build_prepare_private_transfer_instruction_v1, build_prepare_withdrawal_instruction_v1,
    PoolTransactionBuilderErrorV1, PreparedSettlementRouteAccountsV1,
};

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
    InvalidAuthorizationPlan,
    ProofBodyMismatch,
    WrongTransitionKind,
    PreparedSettlement(PoolTransactionBuilderErrorV1),
}

impl From<PoolTransactionBuilderErrorV1> for PoolVerifierTransactionBuilderErrorV1 {
    fn from(error: PoolTransactionBuilderErrorV1) -> Self {
        Self::PreparedSettlement(error)
    }
}

/// Secret-free identity and canonical request for one proof authorization.
/// The proof bytes themselves are deliberately not retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePoolTag73AuthorizationPlanV1 {
    verifier_program: Pubkey,
    proof_account: Pubkey,
    receipt_account: Pubkey,
    receipt_bump: u8,
    frontier_nodes: usize,
    binding: VerifierDispatchBindingV1,
    request: [u8; V7_POOL_NATIVE_TAG73_REQUEST_BYTES],
}

impl NativePoolTag73AuthorizationPlanV1 {
    pub fn verifier_program(&self) -> Pubkey {
        self.verifier_program
    }

    pub fn proof_account(&self) -> Pubkey {
        self.proof_account
    }

    pub fn receipt_account(&self) -> Pubkey {
        self.receipt_account
    }

    pub fn receipt_bump(&self) -> u8 {
        self.receipt_bump
    }

    pub fn frontier_nodes(&self) -> usize {
        self.frontier_nodes
    }

    pub fn binding(&self) -> VerifierDispatchBindingV1 {
        self.binding
    }

    pub fn request(&self) -> &[u8; V7_POOL_NATIVE_TAG73_REQUEST_BYTES] {
        &self.request
    }

    pub fn transition_kind(&self) -> PoolV1TransitionKind {
        self.binding.transition_kind
    }
}

/// Opaque proof lifecycle identity. Every emitted stage is derived from one
/// validated plan, the exact proof body committed by that plan, its immutable
/// upload/receipt-refund authority, and the selected proof-refund authority.
#[derive(Debug)]
pub struct NativePoolTag73LifecycleContextV1<'a> {
    plan: &'a NativePoolTag73AuthorizationPlanV1,
    proof_body: &'a [u8],
    upload_authority: Pubkey,
    proof_refund_authority: Pubkey,
}

impl<'a> NativePoolTag73LifecycleContextV1<'a> {
    pub fn new(
        plan: &'a NativePoolTag73AuthorizationPlanV1,
        proof_body: &'a [u8],
        upload_authority: Pubkey,
        proof_refund_authority: Pubkey,
    ) -> Result<Self, PoolVerifierTransactionBuilderErrorV1> {
        validate_native_pool_tag73_authorization_plan_v1(plan)?;
        require_program_and_accounts(
            plan.verifier_program,
            &[plan.proof_account, plan.receipt_account, upload_authority],
        )?;
        require_program_and_accounts(
            plan.verifier_program,
            &[plan.proof_account, proof_refund_authority],
        )?;
        if proof_refund_authority == plan.receipt_account {
            return Err(PoolVerifierTransactionBuilderErrorV1::AccountAlias);
        }
        let proof_body_length = u32::try_from(proof_body.len())
            .map_err(|_| PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
        if proof_body_length != plan.binding.proof_body_length
            || verifier_proof_body_digest_v1(proof_body, sha256_parts_v1)
                != plan.binding.proof_body_digest
        {
            return Err(PoolVerifierTransactionBuilderErrorV1::ProofBodyMismatch);
        }
        Ok(Self {
            plan,
            proof_body,
            upload_authority,
            proof_refund_authority,
        })
    }

    pub fn plan(&self) -> &NativePoolTag73AuthorizationPlanV1 {
        self.plan
    }

    pub fn upload_authority(&self) -> Pubkey {
        self.upload_authority
    }

    /// The receipt refund is fixed by Tag 74 to the upload authority.
    pub fn receipt_refund_authority(&self) -> Pubkey {
        self.upload_authority
    }

    pub fn proof_refund_authority(&self) -> Pubkey {
        self.proof_refund_authority
    }

    fn validate(&self) -> Result<(), PoolVerifierTransactionBuilderErrorV1> {
        validate_native_pool_tag73_authorization_plan_v1(self.plan)?;
        let proof_body_length = u32::try_from(self.proof_body.len())
            .map_err(|_| PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
        if proof_body_length != self.plan.binding.proof_body_length
            || verifier_proof_body_digest_v1(self.proof_body, sha256_parts_v1)
                != self.plan.binding.proof_body_digest
        {
            return Err(PoolVerifierTransactionBuilderErrorV1::ProofBodyMismatch);
        }
        require_program_and_accounts(
            self.plan.verifier_program,
            &[
                self.plan.proof_account,
                self.plan.receipt_account,
                self.upload_authority,
            ],
        )?;
        require_program_and_accounts(
            self.plan.verifier_program,
            &[self.plan.proof_account, self.proof_refund_authority],
        )?;
        if self.proof_refund_authority == self.plan.receipt_account {
            return Err(PoolVerifierTransactionBuilderErrorV1::AccountAlias);
        }
        Ok(())
    }
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
    if verifier_program == Pubkey::default() || is_fixed_builtin(verifier_program) {
        return Err(PoolVerifierTransactionBuilderErrorV1::UnpinnedProgramId);
    }
    if accounts.iter().any(|key| *key == Pubkey::default()) {
        return Err(PoolVerifierTransactionBuilderErrorV1::ZeroAccount);
    }
    if accounts
        .iter()
        .any(|key| *key == verifier_program || is_fixed_builtin(*key))
    {
        return Err(PoolVerifierTransactionBuilderErrorV1::AccountAlias);
    }
    let mut unique = BTreeSet::new();
    if !accounts.iter().all(|key| unique.insert(key.to_bytes())) {
        return Err(PoolVerifierTransactionBuilderErrorV1::AccountAlias);
    }
    Ok(())
}

fn is_fixed_builtin(key: Pubkey) -> bool {
    key == system_program::id()
        || key == address_lookup_table::id()
        || key == native_loader::id()
        || key == bpf_loader::id()
        || key == bpf_loader_deprecated::id()
        || key == bpf_loader_upgradeable::id()
        || key == loader_v4::id()
        || key == compute_budget::id()
        || key == config::id()
        || key == ed25519_program::id()
        || key == feature::id()
        || key == incinerator::id()
        || key == secp256k1_program::id()
        || key == secp256r1_program::id()
        || key == stake::id()
        || key == vote::id()
        || key == zk_elgamal_proof_program::id()
        || key == zk_token_proof_program::id()
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

/// Revalidate every derived field of an authorization plan from its canonical
/// request bytes. Consumers call this before emitting any instruction so an
/// internally corrupted plan cannot become a partial route.
pub fn validate_native_pool_tag73_authorization_plan_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
) -> Result<(), PoolVerifierTransactionBuilderErrorV1> {
    require_program_and_accounts(
        plan.verifier_program,
        &[plan.proof_account, plan.receipt_account],
    )?;
    let decoded = decode_verifier_dispatch_request_v1(&plan.request, sha256_parts_v1)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
    if decoded.binding != plan.binding
        || decoded.binding.verifier_program != plan.verifier_program.to_bytes()
        || decoded.binding.proof_account != plan.proof_account.to_bytes()
        || decoded.binding.profile_binding != V7_POOL_NATIVE_TAG73_PROFILE_BINDING
        || decoded.binding.release_binding != V7_POOL_NATIVE_TAG73_RELEASE_BINDING
        || decoded.statement_payload.len() != POOL_V1_PAYMENT_STATEMENT_BYTES
    {
        return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
    }
    let canonical_request = encode_verifier_dispatch_request_v1(&decoded, sha256_parts_v1)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
    if canonical_request.as_slice() != plan.request {
        return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
    }

    let envelope = match decoded.binding.transition_kind {
        PoolV1TransitionKind::PrivateTransfer => {
            let statement = decode_pool_v1_private_transfer_public_v1(decoded.statement_payload)
                .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
            let canonical_payload = encode_pool_v1_private_transfer_public_v1(&statement)
                .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
            if canonical_payload.as_slice() != decoded.statement_payload {
                return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
            }
            native_envelope_v1(
                PoolV1TransitionKind::PrivateTransfer,
                statement.pool,
                statement.deployment_domain,
                statement.anchor_sequence,
                statement.anchor_root,
                statement.nullifier,
            )
        }
        PoolV1TransitionKind::Withdrawal => {
            let statement = decode_pool_v1_withdrawal_public_v1(decoded.statement_payload)
                .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
            let canonical_payload = encode_pool_v1_withdrawal_public_v1(&statement)
                .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
            if canonical_payload.as_slice() != decoded.statement_payload {
                return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
            }
            native_envelope_v1(
                PoolV1TransitionKind::Withdrawal,
                statement.pool,
                statement.deployment_domain,
                statement.anchor_sequence,
                statement.anchor_root,
                statement.nullifier,
            )
        }
    };
    let expected_binding = verifier_dispatch_binding_from_envelope_v1(
        plan.verifier_program.to_bytes(),
        &envelope,
        decoded.statement_payload,
        plan.proof_account.to_bytes(),
        decoded.binding.proof_body_digest,
        decoded.binding.proof_body_length,
        sha256_parts_v1,
    )
    .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
    if expected_binding != decoded.binding
        || frontier_nodes_for_exact_proof_length(decoded.binding.proof_body_length)
            != Some(plan.frontier_nodes)
    {
        return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
    }
    let binding_digest =
        pool_v1_authorization_receipt_binding_digest_v1(&decoded.binding, sha256_parts_v1)
            .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
    let (receipt_account, receipt_bump) = Pubkey::find_program_address(
        &[
            POOL_V1_AUTHORIZATION_RECEIPT_SEED,
            plan.proof_account.as_ref(),
            &decoded.binding.statement_digest,
            &binding_digest,
        ],
        &plan.verifier_program,
    );
    if receipt_account != plan.receipt_account || receipt_bump != plan.receipt_bump {
        return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
    }
    Ok(())
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
    let plan = NativePoolTag73AuthorizationPlanV1 {
        verifier_program,
        proof_account,
        receipt_account,
        receipt_bump,
        frontier_nodes,
        binding,
        request,
    };
    validate_native_pool_tag73_authorization_plan_v1(&plan)?;
    Ok(plan)
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

fn prepared_settlement_route_from_authorization_plan_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
    pool_program: Pubkey,
    plan_authority: Pubkey,
    registry_program: Pubkey,
) -> Result<PreparedSettlementRouteAccountsV1, PoolVerifierTransactionBuilderErrorV1> {
    validate_native_pool_tag73_authorization_plan_v1(plan)?;
    require_program_and_accounts(
        plan.verifier_program,
        &[
            plan.proof_account,
            plan.receipt_account,
            pool_program,
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

/// Build an exact private-transfer `ASPP` only after the typed statement has
/// round-tripped canonically and matched the plan's full request payload and
/// dispatch binding.
#[allow(clippy::too_many_arguments)]
pub fn build_prepare_native_private_transfer_instruction_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
    pool_program: Pubkey,
    current_root_sequence: u64,
    statement: &PoolV1PrivateTransferPublicV1,
    not_before_slot: u64,
    expires_at_slot: u64,
    plan_authority: Pubkey,
    registry_program: Pubkey,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    validate_native_pool_tag73_authorization_plan_v1(plan)?;
    if plan.transition_kind() != PoolV1TransitionKind::PrivateTransfer {
        return Err(PoolVerifierTransactionBuilderErrorV1::WrongTransitionKind);
    }
    let payload = encode_pool_v1_private_transfer_public_v1(statement)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::StatementFormat)?;
    let decoded_statement = decode_pool_v1_private_transfer_public_v1(&payload)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::StatementFormat)?;
    let decoded_request = decode_verifier_dispatch_request_v1(&plan.request, sha256_parts_v1)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
    if decoded_statement != *statement
        || decoded_request.binding != plan.binding
        || decoded_request.statement_payload != payload
    {
        return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
    }
    let envelope = native_envelope_v1(
        PoolV1TransitionKind::PrivateTransfer,
        decoded_statement.pool,
        decoded_statement.deployment_domain,
        decoded_statement.anchor_sequence,
        decoded_statement.anchor_root,
        decoded_statement.nullifier,
    );
    let pool_statement = PrivateTransferStatementV1 {
        pool: decoded_statement.pool,
        deployment_domain: decoded_statement.deployment_domain,
        anchor_sequence: decoded_statement.anchor_sequence,
        anchor_root: decoded_statement.anchor_root,
        nullifier: decoded_statement.nullifier,
        asset_id: decoded_statement.asset_id,
        recipient_commitment: decoded_statement.recipient_commitment,
        change_commitment: decoded_statement.change_commitment,
    };
    let route = prepared_settlement_route_from_authorization_plan_v1(
        plan,
        pool_program,
        plan_authority,
        registry_program,
    )?;
    Ok(build_prepare_private_transfer_instruction_v1(
        pool_program,
        current_root_sequence,
        &envelope,
        &pool_statement,
        not_before_slot,
        expires_at_slot,
        route,
    )?)
}

/// Build an exact withdrawal `ASPP` only after the typed statement has
/// round-tripped canonically and matched the plan's full request payload and
/// dispatch binding.
#[allow(clippy::too_many_arguments)]
pub fn build_prepare_native_withdrawal_instruction_v1(
    plan: &NativePoolTag73AuthorizationPlanV1,
    pool_program: Pubkey,
    current_root_sequence: u64,
    statement: &PoolV1WithdrawalPublicV1,
    not_before_slot: u64,
    expires_at_slot: u64,
    plan_authority: Pubkey,
    registry_program: Pubkey,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    validate_native_pool_tag73_authorization_plan_v1(plan)?;
    if plan.transition_kind() != PoolV1TransitionKind::Withdrawal {
        return Err(PoolVerifierTransactionBuilderErrorV1::WrongTransitionKind);
    }
    let payload = encode_pool_v1_withdrawal_public_v1(statement)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::StatementFormat)?;
    let decoded_statement = decode_pool_v1_withdrawal_public_v1(&payload)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::StatementFormat)?;
    let decoded_request = decode_verifier_dispatch_request_v1(&plan.request, sha256_parts_v1)
        .map_err(|_| PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan)?;
    if decoded_statement != *statement
        || decoded_request.binding != plan.binding
        || decoded_request.statement_payload != payload
    {
        return Err(PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan);
    }
    let envelope = native_envelope_v1(
        PoolV1TransitionKind::Withdrawal,
        decoded_statement.pool,
        decoded_statement.deployment_domain,
        decoded_statement.anchor_sequence,
        decoded_statement.anchor_root,
        decoded_statement.nullifier,
    );
    let pool_statement = WithdrawalStatementV1 {
        pool: decoded_statement.pool,
        deployment_domain: decoded_statement.deployment_domain,
        anchor_sequence: decoded_statement.anchor_sequence,
        anchor_root: decoded_statement.anchor_root,
        nullifier: decoded_statement.nullifier,
        asset_id: decoded_statement.asset_id,
        amount: decoded_statement.amount,
        destination_token_account: decoded_statement.destination_token_account,
        change_commitment: decoded_statement.change_commitment,
    };
    let route = prepared_settlement_route_from_authorization_plan_v1(
        plan,
        pool_program,
        plan_authority,
        registry_program,
    )?;
    Ok(build_prepare_withdrawal_instruction_v1(
        pool_program,
        current_root_sequence,
        &envelope,
        &pool_statement,
        not_before_slot,
        expires_at_slot,
        route,
    )?)
}

/// Create the exact-sized verifier-owned proof account derived from a bound
/// lifecycle. Both payer and proof account sign the returned System call.
pub fn build_create_native_proof_account_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
    payer: Pubkey,
    rent_lamports: u64,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    require_program_and_accounts(plan.verifier_program, &[payer, plan.proof_account])?;
    let space = (POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES as u64)
        .checked_add(u64::from(plan.binding.proof_body_length))
        .ok_or(PoolVerifierTransactionBuilderErrorV1::ProofLengthOverflow)?;
    Ok(system_instruction::create_account(
        &payer,
        &plan.proof_account,
        rent_lamports,
        space,
        &plan.verifier_program,
    ))
}

/// Initialize the exact `ASPU` header after the account has been created.
pub fn build_initialize_native_proof_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    let mut data = Vec::with_capacity(5);
    data.push(V7_POOL_PROOF_INIT_TAG);
    data.extend_from_slice(&plan.binding.proof_body_length.to_le_bytes());
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new(plan.proof_account, true),
            AccountMeta::new_readonly(lifecycle.upload_authority, true),
        ],
        data,
    })
}

/// Split a complete proof into the frozen 960-byte upload instructions.  The
/// final chunk is shorter; offsets cover the body exactly once in order.
pub fn build_native_proof_upload_instructions_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Vec<Instruction>, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    let mut instructions = Vec::with_capacity(
        lifecycle
            .proof_body
            .len()
            .div_ceil(V7_POOL_PROOF_UPLOAD_CHUNK_BYTES),
    );
    for (chunk_index, chunk) in lifecycle
        .proof_body
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
            program_id: plan.verifier_program,
            accounts: vec![
                AccountMeta::new(plan.proof_account, false),
                AccountMeta::new_readonly(lifecycle.upload_authority, true),
            ],
            data,
        });
    }
    Ok(instructions)
}

/// Create the pending verifier receipt while the proof remains unsealed.
pub fn build_initialize_native_authorization_receipt_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    let mut data = Vec::with_capacity(1 + V7_POOL_NATIVE_TAG73_REQUEST_BYTES);
    data.push(V7_POOL_RECEIPT_INITIALIZE_TAG);
    data.extend_from_slice(&plan.request);
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new_readonly(plan.proof_account, false),
            AccountMeta::new(plan.receipt_account, false),
            AccountMeta::new(lifecycle.upload_authority, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data,
    })
}

/// Irreversibly seal the proof upload after its pending receipt exists.
pub fn build_finalize_native_proof_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new(plan.proof_account, false),
            AccountMeta::new_readonly(lifecycle.upload_authority, true),
        ],
        data: vec![V7_POOL_PROOF_FINALIZE_TAG],
    })
}

/// Verify the sealed proof and atomically finalize its exact pending receipt.
pub fn build_finalize_native_authorization_receipt_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
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
    validate_native_pool_tag73_authorization_plan_v1(plan)?;
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![AccountMeta::new_readonly(plan.proof_account, false)],
        data: plan.request.to_vec(),
    })
}

/// Close a pending or verified authorization receipt to its immutable refund
/// authority.  The on-chain receipt image authenticates that authority.
pub fn build_close_native_authorization_receipt_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new(plan.receipt_account, false),
            AccountMeta::new(lifecycle.receipt_refund_authority(), true),
        ],
        data: vec![V7_POOL_RECEIPT_CLOSE_TAG],
    })
}

/// Close a sealed proof account and refund its rent.  Both accounts sign so a
/// third party cannot steal the ephemeral proof account's balance.
pub fn build_close_native_proof_instruction_v1(
    lifecycle: &NativePoolTag73LifecycleContextV1<'_>,
) -> Result<Instruction, PoolVerifierTransactionBuilderErrorV1> {
    lifecycle.validate()?;
    let plan = lifecycle.plan;
    Ok(Instruction {
        program_id: plan.verifier_program,
        accounts: vec![
            AccountMeta::new(plan.proof_account, true),
            AccountMeta::new(lifecycle.proof_refund_authority, true),
        ],
        data: vec![V7_POOL_PROOF_CLOSE_TAG],
    })
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use aspis_pool::{
        decode_prepare_settlement_instruction_v1, POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC,
    };
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
            validate_native_pool_tag73_authorization_plan_v1(&plan).unwrap();
            assert_eq!(plan.request().len(), 600);
            assert_eq!(plan.frontier_nodes(), 203);
            assert_eq!(
                plan.binding().profile_binding,
                V7_POOL_NATIVE_TAG73_PROFILE_BINDING
            );
            assert_eq!(
                plan.binding().release_binding,
                V7_POOL_NATIVE_TAG73_RELEASE_BINDING
            );
            assert_eq!(plan.binding().proof_account, proof_key.to_bytes());
            let decoded =
                decode_verifier_dispatch_request_v1(plan.request(), sha256_parts_v1).unwrap();
            assert_eq!(decoded.binding, plan.binding());

            let inputs = pool_v1_authorization_receipt_pda_inputs_for_binding_v1(
                &plan.binding(),
                plan.receipt_bump(),
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
                        &[plan.receipt_bump()],
                    ],
                    &verifier,
                )
                .unwrap(),
                plan.receipt_account()
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
        let lifecycle =
            NativePoolTag73LifecycleContextV1::new(&plan, &proof, upload_authority, key(13))
                .unwrap();
        assert_eq!(lifecycle.plan(), &plan);
        assert_eq!(lifecycle.upload_authority(), upload_authority);
        assert_eq!(lifecycle.receipt_refund_authority(), upload_authority);
        assert_eq!(lifecycle.proof_refund_authority(), key(13));

        let init = build_initialize_native_proof_instruction_v1(&lifecycle).unwrap();
        assert_eq!(init.data[0], V7_POOL_PROOF_INIT_TAG);
        assert_eq!(&init.data[1..], &(proof.len() as u32).to_le_bytes());
        assert!(init.accounts[0].is_signer && init.accounts[0].is_writable);
        assert!(init.accounts[1].is_signer && !init.accounts[1].is_writable);

        let create =
            build_create_native_proof_account_instruction_v1(&lifecycle, key(10), 123_456).unwrap();
        assert_eq!(create.program_id, system_program::id());
        assert_eq!(create.accounts[0], AccountMeta::new(key(10), true));
        assert_eq!(create.accounts[1], AccountMeta::new(proof_key, true));

        let uploads = build_native_proof_upload_instructions_v1(&lifecycle).unwrap();
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
            build_initialize_native_authorization_receipt_instruction_v1(&lifecycle).unwrap();
        assert_eq!(receipt_init.data[0], V7_POOL_RECEIPT_INITIALIZE_TAG);
        assert_eq!(&receipt_init.data[1..], plan.request());
        assert_eq!(receipt_init.accounts.len(), 4);
        assert_eq!(
            receipt_init.accounts[0],
            AccountMeta::new_readonly(proof_key, false)
        );
        assert_eq!(
            receipt_init.accounts[1],
            AccountMeta::new(plan.receipt_account(), false)
        );
        assert_eq!(
            receipt_init.accounts[2],
            AccountMeta::new(upload_authority, true)
        );

        let seal = build_finalize_native_proof_instruction_v1(&lifecycle).unwrap();
        assert_eq!(seal.data, [V7_POOL_PROOF_FINALIZE_TAG]);
        let receipt_finalize =
            build_finalize_native_authorization_receipt_instruction_v1(&lifecycle).unwrap();
        assert_eq!(receipt_finalize.data[0], V7_POOL_RECEIPT_FINALIZE_TAG);
        assert_eq!(&receipt_finalize.data[1..], plan.request());
        assert_eq!(
            receipt_finalize.accounts,
            vec![
                AccountMeta::new_readonly(proof_key, false),
                AccountMeta::new(plan.receipt_account(), false),
            ]
        );
        let direct = build_verify_native_asvq_instruction_v1(&plan).unwrap();
        assert_eq!(direct.data, plan.request());
        assert_eq!(
            direct.accounts,
            [AccountMeta::new_readonly(proof_key, false)]
        );

        let close_receipt =
            build_close_native_authorization_receipt_instruction_v1(&lifecycle).unwrap();
        assert_eq!(close_receipt.data, [V7_POOL_RECEIPT_CLOSE_TAG]);
        assert_eq!(
            close_receipt.accounts[1],
            AccountMeta::new(upload_authority, true)
        );
        let close_proof = build_close_native_proof_instruction_v1(&lifecycle).unwrap();
        assert_eq!(close_proof.data, [V7_POOL_PROOF_CLOSE_TAG]);
        assert_eq!(close_proof.accounts[1], AccountMeta::new(key(13), true));
        assert!(close_proof.accounts.iter().all(|meta| meta.is_signer));
    }

    #[test]
    fn typed_prepared_bridges_bind_the_full_plan_payload_and_transition_kind() {
        let proof = proof();
        let transfer = transfer();
        let withdrawal = withdrawal();
        let transfer_plan =
            build_native_private_transfer_authorization_plan_v1(key(1), key(2), &transfer, &proof)
                .unwrap();
        let withdrawal_plan =
            build_native_withdrawal_authorization_plan_v1(key(1), key(2), &withdrawal, &proof)
                .unwrap();
        let private_prepare = build_prepare_native_private_transfer_instruction_v1(
            &transfer_plan,
            key(20),
            20,
            &transfer,
            21,
            40,
            key(11),
            key(12),
        )
        .unwrap();
        assert_eq!(
            &private_prepare.data[..4],
            &POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_MAGIC
        );
        let decoded_private =
            decode_prepare_settlement_instruction_v1(&private_prepare.data).unwrap();
        assert_eq!(
            decoded_private.transition_kind,
            PoolV1TransitionKind::PrivateTransfer
        );
        assert!(private_prepare
            .accounts
            .iter()
            .any(|meta| meta.pubkey == transfer_plan.receipt_account()));

        let withdrawal_prepare = build_prepare_native_withdrawal_instruction_v1(
            &withdrawal_plan,
            key(20),
            20,
            &withdrawal,
            21,
            40,
            key(11),
            key(12),
        )
        .unwrap();
        assert_eq!(
            decode_prepare_settlement_instruction_v1(&withdrawal_prepare.data)
                .unwrap()
                .transition_kind,
            PoolV1TransitionKind::Withdrawal
        );

        assert_eq!(
            build_prepare_native_private_transfer_instruction_v1(
                &withdrawal_plan,
                key(20),
                20,
                &transfer,
                21,
                40,
                key(11),
                key(12),
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::WrongTransitionKind
        );
        let mut other_transfer = transfer;
        other_transfer.change_commitment = digest(900);
        assert_eq!(
            build_prepare_native_private_transfer_instruction_v1(
                &transfer_plan,
                key(20),
                20,
                &other_transfer,
                21,
                40,
                key(11),
                key(12),
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan
        );
    }

    #[test]
    fn corrupted_plan_mismatched_proof_and_fixed_builtins_fail_closed() {
        let verifier = key(1);
        let proof_key = key(2);
        let proof = proof();
        let mut short = proof.clone();
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

        let plan = build_native_private_transfer_authorization_plan_v1(
            verifier,
            proof_key,
            &transfer(),
            &proof,
        )
        .unwrap();
        let mut wrong_proof = proof.clone();
        wrong_proof[0] ^= 1;
        assert_eq!(
            NativePoolTag73LifecycleContextV1::new(&plan, &wrong_proof, key(9), key(10),)
                .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::ProofBodyMismatch
        );
        assert_eq!(
            NativePoolTag73LifecycleContextV1::new(&plan, &proof, key(9), plan.receipt_account(),)
                .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::AccountAlias
        );
        assert_eq!(
            NativePoolTag73LifecycleContextV1::new(&plan, &proof, system_program::id(), key(10),)
                .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::ZeroAccount
        );
        assert_eq!(
            build_native_private_transfer_authorization_plan_v1(
                system_program::id(),
                proof_key,
                &transfer(),
                &proof,
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::UnpinnedProgramId
        );
        assert_eq!(
            build_prepare_native_private_transfer_instruction_v1(
                &plan,
                key(20),
                20,
                &transfer(),
                21,
                40,
                key(11),
                native_loader::id(),
            )
            .unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::AccountAlias
        );

        let mut corrupt_request = plan.clone();
        corrupt_request.request[20] ^= 1;
        assert_eq!(
            validate_native_pool_tag73_authorization_plan_v1(&corrupt_request).unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan
        );
        assert_eq!(
            build_verify_native_asvq_instruction_v1(&corrupt_request).unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan
        );
        let mut corrupt_binding = plan.clone();
        corrupt_binding.binding.proof_body_digest[0] ^= 1;
        assert_eq!(
            validate_native_pool_tag73_authorization_plan_v1(&corrupt_binding).unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan
        );
        let mut corrupt_receipt = plan.clone();
        corrupt_receipt.receipt_account = key(30);
        assert_eq!(
            validate_native_pool_tag73_authorization_plan_v1(&corrupt_receipt).unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan
        );
        let mut corrupt_frontier = plan;
        corrupt_frontier.frontier_nodes += 1;
        assert_eq!(
            validate_native_pool_tag73_authorization_plan_v1(&corrupt_frontier).unwrap_err(),
            PoolVerifierTransactionBuilderErrorV1::InvalidAuthorizationPlan
        );
    }
}
