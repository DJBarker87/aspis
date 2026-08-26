//! Permissionless, unsigned Pool V1 relayer boundary.
//!
//! Anyone may submit a canonical unsigned instruction for validation. The
//! result is a deterministic request id plus the exact instruction an external
//! operator may place in a transaction. Admission additionally binds the
//! authenticated Pool-state snapshot and applies an explicit pause, freshness,
//! fee-reserve, queue, inflight and global rate-window policy. This module has
//! no allowlist, private key, signer, network client, fee transfer, or
//! send/simulate path.

use sha2::{Digest as _, Sha256};
use solana_program::{instruction::Instruction, pubkey::Pubkey};

use crate::transaction_builder::{validate_pool_instruction_v1, PoolTransactionBuilderErrorV1};

pub const POOL_V1_RELAYER_REQUEST_DOMAIN: &[u8] =
    b"aspis:pool-v1:permissionless-relayer-request:sha256:v1";
pub const POOL_V1_RELAYER_POLICY_DOMAIN: &[u8] = b"aspis:pool-v1:relayer-operator-policy:sha256:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerRequestKindV1 {
    Initialize,
    Deposit,
    PrepareSettlement,
    PrivateTransfer,
    Withdrawal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerSnapshotV1 {
    pub pinned_program_id: Pubkey,
    pub registry_program: Pubkey,
    pub current_root_sequence: u64,
    /// Finalized slot at which the complete canonical Pool account image was
    /// authenticated.
    pub observed_slot: u64,
    /// SHA-256 of the exact canonical Pool account bytes at `observed_slot`.
    /// It is an idempotency/freshness binding, not a replacement for decoding
    /// and authenticating those bytes before constructing this snapshot.
    pub pool_state_sha256: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelayerPlanV1 {
    pub request_id: [u8; 32],
    pub kind: RelayerRequestKindV1,
    pub snapshot: RelayerSnapshotV1,
    /// Public transaction fee-payer address only. No signing material is ever
    /// accepted or retained by this crate.
    pub fee_payer: Pubkey,
    pub instruction: Instruction,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerErrorV1 {
    InvalidFeePayer,
    UnauthenticatedSnapshot,
    LengthOverflow,
    InvalidInstruction(PoolTransactionBuilderErrorV1),
}

fn request_kind_v1(instruction: &Instruction) -> Result<RelayerRequestKindV1, RelayerErrorV1> {
    match instruction.data.get(..4) {
        Some(b"ASIN") => Ok(RelayerRequestKindV1::Initialize),
        Some(b"ASDI") => Ok(RelayerRequestKindV1::Deposit),
        Some(b"ASPP") => Ok(RelayerRequestKindV1::PrepareSettlement),
        Some(b"ASPT") => Ok(RelayerRequestKindV1::PrivateTransfer),
        Some(b"ASWD") => Ok(RelayerRequestKindV1::Withdrawal),
        _ => Err(RelayerErrorV1::InvalidInstruction(
            PoolTransactionBuilderErrorV1::WrongAccountLayout,
        )),
    }
}

/// Validate an untrusted unsigned request against the frozen ABI and derive
/// its stable idempotency key. Canonical requests are permissionless: there is
/// deliberately no submitter or authority field.
pub fn prepare_permissionless_relayer_plan_v1(
    snapshot: RelayerSnapshotV1,
    fee_payer: Pubkey,
    instruction: &Instruction,
) -> Result<RelayerPlanV1, RelayerErrorV1> {
    if fee_payer == Pubkey::default() {
        return Err(RelayerErrorV1::InvalidFeePayer);
    }
    if snapshot.observed_slot == 0 || snapshot.pool_state_sha256 == [0u8; 32] {
        return Err(RelayerErrorV1::UnauthenticatedSnapshot);
    }
    validate_pool_instruction_v1(
        snapshot.pinned_program_id,
        snapshot.current_root_sequence,
        snapshot.registry_program,
        instruction,
    )
    .map_err(RelayerErrorV1::InvalidInstruction)?;
    let kind = request_kind_v1(instruction)?;

    let account_count =
        u16::try_from(instruction.accounts.len()).map_err(|_| RelayerErrorV1::LengthOverflow)?;
    let data_length =
        u32::try_from(instruction.data.len()).map_err(|_| RelayerErrorV1::LengthOverflow)?;
    let mut hasher = Sha256::new();
    hasher.update(POOL_V1_RELAYER_REQUEST_DOMAIN);
    hasher.update(snapshot.pinned_program_id.as_ref());
    hasher.update(snapshot.registry_program.as_ref());
    hasher.update(snapshot.current_root_sequence.to_le_bytes());
    hasher.update(snapshot.observed_slot.to_le_bytes());
    hasher.update(snapshot.pool_state_sha256);
    hasher.update(fee_payer.as_ref());
    hasher.update(account_count.to_le_bytes());
    for account in &instruction.accounts {
        hasher.update(account.pubkey.as_ref());
        hasher.update([u8::from(account.is_signer), u8::from(account.is_writable)]);
    }
    hasher.update(data_length.to_le_bytes());
    hasher.update(&instruction.data);
    Ok(RelayerPlanV1 {
        request_id: hasher.finalize().into(),
        kind,
        snapshot,
        fee_payer,
        instruction: instruction.clone(),
    })
}

/// Public, secret-free operator policy. A production service persists this
/// policy beside its deployment manifest and changes it only through the
/// separately authenticated operator-control workflow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerPolicyV1 {
    pub paused: bool,
    pub operator_fee_payer: Pubkey,
    pub allow_initialize: bool,
    pub allow_deposit: bool,
    pub allow_prepare_settlement: bool,
    pub allow_private_transfer: bool,
    pub allow_withdrawal: bool,
    pub max_snapshot_age_slots: u64,
    pub max_queue_depth: u32,
    pub max_inflight: u32,
    pub rate_window_slots: u64,
    pub max_admissions_per_window: u32,
    pub max_estimated_fee_lamports: u64,
    pub minimum_fee_payer_reserve_lamports: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerAdmissionContextV1 {
    pub now_slot: u64,
    pub queue_depth: u32,
    pub inflight: u32,
    pub rate_window_start_slot: u64,
    pub admissions_in_window: u32,
    pub estimated_fee_lamports: u64,
    pub fee_payer_balance_lamports: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelayerAdmissionV1 {
    pub request_id: [u8; 32],
    pub policy_id: [u8; 32],
    pub kind: RelayerRequestKindV1,
    pub admitted_at_slot: u64,
    pub rate_window_start_slot: u64,
    pub admissions_in_window_after: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerAdmissionErrorV1 {
    InvalidPolicy,
    Paused,
    WrongFeePayer,
    FutureSnapshot,
    StaleSnapshot,
    InstructionKindDisabled,
    OperatorSignerMismatch,
    QueueFull,
    InflightFull,
    FutureRateWindow,
    RateLimited,
    FeeEstimateTooHigh,
    InsufficientFeeReserve,
}

fn kind_enabled(policy: RelayerPolicyV1, kind: RelayerRequestKindV1) -> bool {
    match kind {
        RelayerRequestKindV1::Initialize => policy.allow_initialize,
        RelayerRequestKindV1::Deposit => policy.allow_deposit,
        RelayerRequestKindV1::PrepareSettlement => policy.allow_prepare_settlement,
        RelayerRequestKindV1::PrivateTransfer => policy.allow_private_transfer,
        RelayerRequestKindV1::Withdrawal => policy.allow_withdrawal,
    }
}

/// Stable public identifier for the exact operator controls applied to one
/// admission. This lets the durable queue and monitoring trail reject an
/// admission made under a different local policy revision.
pub fn relayer_policy_id_v1(policy: RelayerPolicyV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(POOL_V1_RELAYER_POLICY_DOMAIN);
    hasher.update([u8::from(policy.paused)]);
    hasher.update(policy.operator_fee_payer.as_ref());
    hasher.update([
        u8::from(policy.allow_initialize),
        u8::from(policy.allow_deposit),
        u8::from(policy.allow_prepare_settlement),
        u8::from(policy.allow_private_transfer),
        u8::from(policy.allow_withdrawal),
    ]);
    hasher.update(policy.max_snapshot_age_slots.to_le_bytes());
    hasher.update(policy.max_queue_depth.to_le_bytes());
    hasher.update(policy.max_inflight.to_le_bytes());
    hasher.update(policy.rate_window_slots.to_le_bytes());
    hasher.update(policy.max_admissions_per_window.to_le_bytes());
    hasher.update(policy.max_estimated_fee_lamports.to_le_bytes());
    hasher.update(policy.minimum_fee_payer_reserve_lamports.to_le_bytes());
    hasher.finalize().into()
}

/// Initialization and proof-authorized spends carry one canonical payer
/// signer in the instruction itself. Deposits instead carry the depositor's
/// token authority and may use a distinct outer transaction fee payer.
fn operator_signer_matches(plan: &RelayerPlanV1) -> bool {
    if plan.kind == RelayerRequestKindV1::Deposit {
        return true;
    }
    let mut signers = plan
        .instruction
        .accounts
        .iter()
        .filter(|account| account.is_signer);
    matches!(signers.next(), Some(account) if account.pubkey == plan.fee_payer)
        && signers.next().is_none()
}

/// Apply the complete pure operator admission gate. This function mutates no
/// queue or counter: the returned `admissions_in_window_after` and request id
/// must be committed atomically by the durable store before signing.
pub fn admit_relayer_plan_v1(
    policy: RelayerPolicyV1,
    context: RelayerAdmissionContextV1,
    plan: &RelayerPlanV1,
) -> Result<RelayerAdmissionV1, RelayerAdmissionErrorV1> {
    if policy.operator_fee_payer == Pubkey::default()
        || policy.max_snapshot_age_slots == 0
        || policy.max_queue_depth == 0
        || policy.max_inflight == 0
        || policy.rate_window_slots == 0
        || policy.max_admissions_per_window == 0
    {
        return Err(RelayerAdmissionErrorV1::InvalidPolicy);
    }
    if policy.paused {
        return Err(RelayerAdmissionErrorV1::Paused);
    }
    if plan.fee_payer != policy.operator_fee_payer {
        return Err(RelayerAdmissionErrorV1::WrongFeePayer);
    }
    if plan.snapshot.observed_slot > context.now_slot {
        return Err(RelayerAdmissionErrorV1::FutureSnapshot);
    }
    if context.now_slot - plan.snapshot.observed_slot > policy.max_snapshot_age_slots {
        return Err(RelayerAdmissionErrorV1::StaleSnapshot);
    }
    if !kind_enabled(policy, plan.kind) {
        return Err(RelayerAdmissionErrorV1::InstructionKindDisabled);
    }
    if !operator_signer_matches(plan) {
        return Err(RelayerAdmissionErrorV1::OperatorSignerMismatch);
    }
    if context.queue_depth >= policy.max_queue_depth {
        return Err(RelayerAdmissionErrorV1::QueueFull);
    }
    if context.inflight >= policy.max_inflight {
        return Err(RelayerAdmissionErrorV1::InflightFull);
    }
    if context.estimated_fee_lamports > policy.max_estimated_fee_lamports {
        return Err(RelayerAdmissionErrorV1::FeeEstimateTooHigh);
    }
    let required_balance = policy
        .minimum_fee_payer_reserve_lamports
        .checked_add(context.estimated_fee_lamports)
        .ok_or(RelayerAdmissionErrorV1::InsufficientFeeReserve)?;
    if context.fee_payer_balance_lamports < required_balance {
        return Err(RelayerAdmissionErrorV1::InsufficientFeeReserve);
    }
    if context.rate_window_start_slot > context.now_slot {
        return Err(RelayerAdmissionErrorV1::FutureRateWindow);
    }
    let elapsed = context.now_slot - context.rate_window_start_slot;
    let (rate_window_start_slot, admissions_before) = if elapsed >= policy.rate_window_slots {
        (context.now_slot, 0)
    } else {
        (context.rate_window_start_slot, context.admissions_in_window)
    };
    if admissions_before >= policy.max_admissions_per_window {
        return Err(RelayerAdmissionErrorV1::RateLimited);
    }
    let admissions_in_window_after = admissions_before
        .checked_add(1)
        .ok_or(RelayerAdmissionErrorV1::RateLimited)?;
    Ok(RelayerAdmissionV1 {
        request_id: plan.request_id,
        policy_id: relayer_policy_id_v1(policy),
        kind: plan.kind,
        admitted_at_slot: context.now_slot,
        rate_window_start_slot,
        admissions_in_window_after,
    })
}

/// Durable queue/database implementations use this outcome to make request-id
/// insertion idempotent. Persistence, rate limits and operator fee policy stay
/// outside this cryptographic/ABI crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelayerEnqueueOutcomeV1 {
    Inserted,
    AlreadyPresent,
}

pub trait RelayerRequestStoreV1 {
    type Error;

    fn insert_if_absent_v1(
        &mut self,
        plan: &RelayerPlanV1,
    ) -> Result<RelayerEnqueueOutcomeV1, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::M31;
    use aspis_pool::{deposit::DepositRequestV1, pool_v1_state_address, WithdrawalStatementV1};
    use aspis_statement::{
        pool_v1::{HistoricalAnchorEnvelopeV1, PoolV1TransitionKind},
        poseidon2::Digest,
    };

    use crate::transaction_builder::{
        build_deposit_instruction_v1, build_prepare_withdrawal_instruction_v1,
        PreparedSettlementRouteAccountsV1,
    };

    fn key(seed: u8) -> Pubkey {
        Pubkey::new_from_array([seed; 32])
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    #[test]
    fn canonical_request_id_is_stable_and_aliasing_is_rejected() {
        let program_id = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(20),
            encrypted_note_payload: &[],
        };
        let instruction =
            build_deposit_instruction_v1(program_id, pool, mint, 7, key(3), key(4), None, &request)
                .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 900,
            pool_state_sha256: [0xabu8; 32],
        };
        let first = prepare_permissionless_relayer_plan_v1(snapshot, key(6), &instruction).unwrap();
        let replay =
            prepare_permissionless_relayer_plan_v1(snapshot, key(6), &instruction).unwrap();
        assert_eq!(first.request_id, replay.request_id);
        assert_eq!(first.kind, RelayerRequestKindV1::Deposit);
        assert_eq!(first.instruction, instruction);

        let mut aliased = instruction;
        aliased.accounts[4].pubkey = aliased.accounts[3].pubkey;
        assert_eq!(
            prepare_permissionless_relayer_plan_v1(snapshot, key(6), &aliased).err(),
            Some(RelayerErrorV1::InvalidInstruction(
                PoolTransactionBuilderErrorV1::AccountAlias
            ))
        );
    }

    #[test]
    fn admission_binds_snapshot_pause_capacity_rate_and_fee_reserve() {
        let program_id = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let request = DepositRequestV1 {
            owner_key: digest(10),
            amount: 77,
            salt: digest(20),
            encrypted_note_payload: &[],
        };
        let instruction =
            build_deposit_instruction_v1(program_id, pool, mint, 7, key(3), key(4), None, &request)
                .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 900,
            pool_state_sha256: [0xabu8; 32],
        };
        let plan = prepare_permissionless_relayer_plan_v1(snapshot, key(6), &instruction).unwrap();
        let policy = RelayerPolicyV1 {
            paused: false,
            operator_fee_payer: key(6),
            allow_initialize: false,
            allow_deposit: true,
            allow_prepare_settlement: true,
            allow_private_transfer: true,
            allow_withdrawal: true,
            max_snapshot_age_slots: 32,
            max_queue_depth: 64,
            max_inflight: 4,
            rate_window_slots: 16,
            max_admissions_per_window: 8,
            max_estimated_fee_lamports: 10_000,
            minimum_fee_payer_reserve_lamports: 1_000_000,
        };
        let context = RelayerAdmissionContextV1 {
            now_slot: 910,
            queue_depth: 3,
            inflight: 1,
            rate_window_start_slot: 904,
            admissions_in_window: 2,
            estimated_fee_lamports: 5_000,
            fee_payer_balance_lamports: 1_005_000,
        };
        let admitted = admit_relayer_plan_v1(policy, context, &plan).unwrap();
        assert_eq!(admitted.request_id, plan.request_id);
        assert_eq!(admitted.policy_id, relayer_policy_id_v1(policy));
        assert_eq!(admitted.admissions_in_window_after, 3);

        let changed_snapshot = RelayerSnapshotV1 {
            observed_slot: 901,
            ..snapshot
        };
        let changed =
            prepare_permissionless_relayer_plan_v1(changed_snapshot, key(6), &instruction).unwrap();
        assert_ne!(changed.request_id, plan.request_id);

        assert_eq!(
            admit_relayer_plan_v1(
                RelayerPolicyV1 {
                    paused: true,
                    ..policy
                },
                context,
                &plan
            ),
            Err(RelayerAdmissionErrorV1::Paused)
        );
        assert_eq!(
            admit_relayer_plan_v1(
                policy,
                RelayerAdmissionContextV1 {
                    queue_depth: policy.max_queue_depth,
                    ..context
                },
                &plan,
            ),
            Err(RelayerAdmissionErrorV1::QueueFull)
        );
        assert_eq!(
            admit_relayer_plan_v1(
                policy,
                RelayerAdmissionContextV1 {
                    admissions_in_window: policy.max_admissions_per_window,
                    ..context
                },
                &plan,
            ),
            Err(RelayerAdmissionErrorV1::RateLimited)
        );
        assert_eq!(
            admit_relayer_plan_v1(
                policy,
                RelayerAdmissionContextV1 {
                    fee_payer_balance_lamports: 1_004_999,
                    ..context
                },
                &plan,
            ),
            Err(RelayerAdmissionErrorV1::InsufficientFeeReserve)
        );
        assert_eq!(
            admit_relayer_plan_v1(
                policy,
                RelayerAdmissionContextV1 {
                    now_slot: snapshot.observed_slot + policy.max_snapshot_age_slots + 1,
                    ..context
                },
                &plan,
            ),
            Err(RelayerAdmissionErrorV1::StaleSnapshot)
        );
    }

    #[test]
    fn prepared_settlement_replay_is_stable_and_requires_explicit_operator_policy() {
        let program_id = key(1);
        let mint = key(2);
        let pool = pool_v1_state_address(&program_id, &mint).0;
        let fee_payer = key(6);
        let envelope = HistoricalAnchorEnvelopeV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            pool: pool.to_bytes(),
            deployment_domain: [8; 32],
            anchor_sequence: 7,
            anchor_root: digest(30),
            nullifier: digest(40),
            verifier_profile: [11; 32],
            verifier_release: [12; 32],
        };
        let statement = WithdrawalStatementV1 {
            pool: envelope.pool,
            deployment_domain: envelope.deployment_domain,
            anchor_sequence: envelope.anchor_sequence,
            anchor_root: envelope.anchor_root,
            nullifier: envelope.nullifier,
            asset_id: M31(9),
            amount: 77,
            destination_token_account: [13; 32],
            change_commitment: digest(50),
        };
        let instruction = build_prepare_withdrawal_instruction_v1(
            program_id,
            7,
            &envelope,
            &statement,
            910,
            930,
            PreparedSettlementRouteAccountsV1 {
                plan_authority: fee_payer,
                registry_program: key(5),
                authorization_receipt: key(10),
            },
        )
        .unwrap();
        let snapshot = RelayerSnapshotV1 {
            pinned_program_id: program_id,
            registry_program: key(5),
            current_root_sequence: 7,
            observed_slot: 900,
            pool_state_sha256: [0xab; 32],
        };
        let first =
            prepare_permissionless_relayer_plan_v1(snapshot, fee_payer, &instruction).unwrap();
        let replay =
            prepare_permissionless_relayer_plan_v1(snapshot, fee_payer, &instruction).unwrap();
        assert_eq!(first.request_id, replay.request_id);
        assert_eq!(first.kind, RelayerRequestKindV1::PrepareSettlement);

        let policy = RelayerPolicyV1 {
            paused: false,
            operator_fee_payer: fee_payer,
            allow_initialize: false,
            allow_deposit: false,
            allow_prepare_settlement: false,
            allow_private_transfer: false,
            allow_withdrawal: false,
            max_snapshot_age_slots: 32,
            max_queue_depth: 4,
            max_inflight: 2,
            rate_window_slots: 16,
            max_admissions_per_window: 2,
            max_estimated_fee_lamports: 10_000,
            minimum_fee_payer_reserve_lamports: 1_000_000,
        };
        let context = RelayerAdmissionContextV1 {
            now_slot: 910,
            queue_depth: 0,
            inflight: 0,
            rate_window_start_slot: 904,
            admissions_in_window: 0,
            estimated_fee_lamports: 5_000,
            fee_payer_balance_lamports: 1_005_000,
        };
        assert_eq!(
            admit_relayer_plan_v1(policy, context, &first),
            Err(RelayerAdmissionErrorV1::InstructionKindDisabled)
        );
        let enabled = RelayerPolicyV1 {
            allow_prepare_settlement: true,
            ..policy
        };
        let admission = admit_relayer_plan_v1(enabled, context, &first).unwrap();
        assert_eq!(admission.kind, RelayerRequestKindV1::PrepareSettlement);
        assert_ne!(relayer_policy_id_v1(enabled), relayer_policy_id_v1(policy));
    }
}
