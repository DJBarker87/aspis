//! Fail-closed Profile23 devnet rehearsal.
//!
//! `readiness` performs only filesystem and read-only RPC calls. `execute`
//! exists as a separate surface and requires two explicit interlocks. Every
//! path and RPC endpoint is supplied on the command line; Solana CLI ambient
//! configuration is never consulted.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    fs::{self, OpenOptions},
    io::Write,
    os::unix::fs::PermissionsExt,
    path::{Component, Path, PathBuf},
    process::Command,
    str::FromStr,
    thread,
    time::{Duration, Instant},
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine};
use borsh::to_vec;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
#[allow(deprecated)]
use solana_sdk::system_instruction;
use solana_sdk::{
    bpf_loader_upgradeable::{self, UpgradeableLoaderState},
    compute_budget::ComputeBudgetInstruction,
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    message::VersionedMessage,
    pubkey::Pubkey,
    signature::{read_keypair_file, Keypair, Signature, Signer},
    system_program,
    transaction::{Transaction, VersionedTransaction},
};

use aspis_verifier::{
    atomic_payment::{
        atomic_nullifier_address, AtomicPaymentPublicInputs, AtomicPoolStateV1,
        ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT, ATOMIC_NULLIFIER_MAGIC, ATOMIC_NULLIFIER_MARKER_LEN,
        ATOMIC_NULLIFIER_VERSION, ATOMIC_POOL_STATE_LEN,
    },
    AspisInstruction, PROOF_ACCOUNT_HEADER_LEN,
};

use crate::profile23_statement::{
    canonical_profile23_public_input_digest, decode_profile23_statement_sidecar, profile23_hex,
};

const DEVNET_GENESIS_HASH: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG";
const MAINNET_BETA_GENESIS_HASH: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const EXECUTE_ACK: &str =
    "I_ACKNOWLEDGE_PROFILE23_DEVNET_REHEARSAL_MUTATES_DEVNET_AND_SPENDS_DEVNET_SOL";
const MAINNET_EXECUTE_ACK: &str =
    "I_ACKNOWLEDGE_PROFILE23_MAINNET_DEMO_MUTATES_MAINNET_AND_SPENDS_CAPPED_SOL";
const UPLOAD_SMOKE_ACK: &str =
    "I_ACKNOWLEDGE_PROFILE23_DEVNET_UPLOAD_SMOKE_MUTATES_DEVNET_AND_SPENDS_DEVNET_SOL";
const CU_LIMIT: u32 = 1_400_000;
const HEAP_FRAME_BYTES: u32 = 262_144;
// A legacy UploadChunk transaction is `chunk.len() + 213` bytes with the
// current account layout. 960 therefore serializes to 1,173 bytes: comfortably
// below Solana's 1,232-byte packet cap while reducing the frozen 64,447-byte
// proof to 68 upload transactions.
const UPLOAD_CHUNK_BYTES: usize = 960;
const UPLOAD_WINDOW_TRANSACTIONS: usize = 16;
const UPLOAD_MAX_IDENTICAL_RETRIES: u8 = 3;
const UPLOAD_REBROADCAST_INTERVAL: Duration = Duration::from_secs(6);
const MAX_TRANSACTION_WIRE_BYTES: usize = 1_232;
const PROOF_MAGIC: &[u8; 4] = b"ASPU";
const PROOF_SHA256_LOG_MARKER: &[u8] = b"aspis-proof-sha256-v1";
const PROOF_AUTHORITY_OFFSET: usize = 8;
const PROGRAMDATA_METADATA_BYTES: usize = 45;
const PROGRAM_ACCOUNT_BYTES: usize = 36;
const BUFFER_METADATA_BYTES: usize = 37;
const DEFAULT_CONFIRM_TIMEOUT: Duration = Duration::from_secs(180);
const READ_ONLY_RPC_RATE_LIMIT_RETRIES: u8 = 12;
const SIGNATURE_POLL_INTERVAL: Duration = Duration::from_secs(2);
const IN_PROGRESS_WARNING: &str = "If this file remains in_progress, execution did not reach the finalized evidence commit. Inspect chain state by recorded signer history before retrying.";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CommandMode {
    Readiness,
    Execute,
    ExecuteMainnet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClusterPolicy {
    Devnet,
    MainnetBeta,
}

impl ClusterPolicy {
    fn expected_genesis_hash(self) -> &'static str {
        match self {
            Self::Devnet => DEVNET_GENESIS_HASH,
            Self::MainnetBeta => MAINNET_BETA_GENESIS_HASH,
        }
    }

    fn execution_acknowledgement(self) -> &'static str {
        match self {
            Self::Devnet => EXECUTE_ACK,
            Self::MainnetBeta => MAINNET_EXECUTE_ACK,
        }
    }

    fn evidence_artifact(self) -> &'static str {
        match self {
            Self::Devnet => "profile23_devnet_finalized_rehearsal",
            Self::MainnetBeta => "profile23_mainnet_beta_finalized_demo",
        }
    }

    fn network(self) -> &'static str {
        match self {
            Self::Devnet => "devnet",
            Self::MainnetBeta => "mainnet-beta",
        }
    }

    fn requires_explicit_recovery_signers(self) -> bool {
        self == Self::MainnetBeta
    }
}

#[derive(Clone, Debug)]
struct DevnetConfig {
    rpc_url: String,
    payer_keypair: PathBuf,
    program_keypair: PathBuf,
    pool_keypair: PathBuf,
    proof_account_keypair: PathBuf,
    replay_probe_keypair: Option<PathBuf>,
    upgrade_authority_keypair: Option<PathBuf>,
    deployment_buffer_keypair: Option<PathBuf>,
    use_tpu_client: bool,
    release: PathBuf,
    sbf: PathBuf,
    proof: PathBuf,
    statement: PathBuf,
    solana_cli: PathBuf,
    evidence: PathBuf,
    program_max_len: usize,
    fee_reserve_lamports: u64,
    execute_interlock: bool,
    resume_in_progress: bool,
    resume_pool_create_signature: Option<Signature>,
    resume_pool_init_signature: Option<Signature>,
    resume_proof_create_signature: Option<Signature>,
    acknowledgement: Option<String>,
}

#[derive(Clone, Debug)]
struct UploadSmokeConfig {
    rpc_url: String,
    payer_keypair: PathBuf,
    proof_account_keypair: PathBuf,
    sbf: PathBuf,
    proof: PathBuf,
    evidence: PathBuf,
    program_max_len: usize,
    fee_reserve_lamports: u64,
    execute_interlock: bool,
    acknowledgement: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DevnetGate {
    pub name: String,
    pub passed: bool,
    pub evidence: String,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct DevnetRentBudget {
    pub program_buffer_lamports: Option<u64>,
    pub programdata_lamports: Option<u64>,
    pub program_account_lamports: Option<u64>,
    pub pool_account_lamports: Option<u64>,
    pub proof_account_lamports: Option<u64>,
    pub nullifier_account_lamports: Option<u64>,
    pub fee_reserve_lamports: u64,
    pub conservative_required_lamports: Option<u64>,
    pub payer_balance_lamports: Option<u64>,
    pub surplus_lamports: Option<i128>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile23DevnetReadiness {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub mode: &'static str,
    pub mutations_performed: bool,
    pub ready: bool,
    pub expected_genesis_hash: &'static str,
    pub observed_genesis_hash: Option<String>,
    pub rpc_origin_redacted: Option<String>,
    pub program_id: String,
    pub payer_pubkey: Option<String>,
    pub pool_pubkey: Option<String>,
    pub proof_account_pubkey: Option<String>,
    pub proof_sha256: Option<String>,
    pub sbf_sha256: Option<String>,
    pub release_sha256: Option<String>,
    pub statement_sha256: Option<String>,
    pub nullifier_address: Option<String>,
    pub program_already_deployed: Option<bool>,
    pub rent_budget: DevnetRentBudget,
    pub gates: Vec<DevnetGate>,
    pub blockers: Vec<String>,
    pub explicit_nonclaims: Vec<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
pub struct TransactionEvidence {
    pub label: String,
    pub signature: String,
    pub finalized_slot: u64,
    pub message_sha256: String,
    pub serialized_transaction_sha256: String,
    pub compute_units_consumed: Option<u64>,
    pub identical_wire_retries: u8,
}

#[derive(Clone, Debug, Serialize)]
pub struct AccountEvidence {
    pub address: String,
    pub lamports: u64,
    pub owner: String,
    pub executable: bool,
    pub data_len: usize,
    pub data_sha256: String,
    pub raw_account_image_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct RefundBalanceEvidence {
    pub fee_lamports: u64,
    pub payer_account_index: usize,
    pub proof_account_index: usize,
    pub nullifier_account_index: usize,
    pub payer_pre_lamports: u64,
    pub payer_post_lamports: u64,
    pub proof_pre_lamports: u64,
    pub proof_post_lamports: u64,
    pub nullifier_pre_lamports: u64,
    pub nullifier_post_lamports: u64,
    pub proof_refund_lamports: u64,
    pub nullifier_funding_lamports: u64,
    pub exact_balance_equation_reconciled: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct ProgramProofDigestLogEvidence {
    pub marker: &'static str,
    pub raw_log_line: String,
    pub logged_proof_sha256: String,
    pub release_proof_sha256: String,
    pub exact_release_proof_digest: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReplayProbeRefundEvidence {
    pub fee_lamports: u64,
    pub payer_account_index: usize,
    pub replay_probe_account_index: usize,
    pub payer_pre_lamports: u64,
    pub payer_post_lamports: u64,
    pub replay_probe_pre_lamports: u64,
    pub replay_probe_post_lamports: u64,
    pub replay_probe_refund_lamports: u64,
    pub exact_balance_equation_reconciled: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct UpgradeableProgramSnapshotEvidence {
    pub program_account: AccountEvidence,
    pub programdata_address: String,
    pub programdata_account: AccountEvidence,
    pub programdata_slot: u64,
    pub upgrade_authority_address: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct UpgradeableProgramContinuityChecks {
    pub programdata_address_unchanged: bool,
    pub program_raw_account_image_unchanged: bool,
    pub program_data_unchanged: bool,
    pub programdata_raw_account_image_unchanged: bool,
    pub programdata_data_unchanged: bool,
}

impl UpgradeableProgramContinuityChecks {
    fn all_unchanged(self) -> bool {
        self.programdata_address_unchanged
            && self.program_raw_account_image_unchanged
            && self.program_data_unchanged
            && self.programdata_raw_account_image_unchanged
            && self.programdata_data_unchanged
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile23DevnetEvidence {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub network: &'static str,
    pub genesis_hash: String,
    pub program_id: String,
    pub release_certificate_path: String,
    pub release_certificate_sha256: String,
    pub release_gate_count: usize,
    pub release_instance_proof_identity_exact: bool,
    pub release_instance_statement_identity_exact: bool,
    pub release_instance_selector_binding_exact: bool,
    pub release_instance_good23_fingerprint_exact: bool,
    pub release_instance_declared_host_verification_green: bool,
    pub production_host_verification_green: bool,
    pub canonical_public_input_digest: String,
    pub serialized_selector: u8,
    pub least_good_selector: u8,
    pub good23_definition_fingerprint: String,
    pub sbf_path: String,
    pub sbf_bytes: usize,
    pub sbf_sha256: String,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub proof_upload_chunk_bytes: usize,
    pub proof_upload_window_transactions: usize,
    pub proof_upload_transaction_count: usize,
    pub proof_upload_finality_windows: usize,
    pub statement_path: String,
    pub statement_sha256: String,
    pub program_max_len: usize,
    pub resumed_from_in_progress: bool,
    pub resume_checkpoint: Option<String>,
    pub preexisting_pool_before_resume: Option<AccountEvidence>,
    pub preexisting_proof_account_before_resume: Option<AccountEvidence>,
    pub upgradeable_program_before_setup: UpgradeableProgramSnapshotEvidence,
    pub upgradeable_program_before_setup_exact_release_sbf_max_len_authority: bool,
    pub upgradeable_program_before_final_simulation: UpgradeableProgramSnapshotEvidence,
    pub upgradeable_program_before_final_simulation_exact_release_sbf_max_len_authority: bool,
    pub upgradeable_program_before_final_simulation_continuity: UpgradeableProgramContinuityChecks,
    pub upgradeable_program_after_finality: UpgradeableProgramSnapshotEvidence,
    pub upgradeable_program_after_finality_exact_release_sbf_max_len_authority: bool,
    pub upgradeable_program_after_finality_continuity: UpgradeableProgramContinuityChecks,
    pub deployment: Option<TransactionEvidence>,
    pub setup_transactions: Vec<TransactionEvidence>,
    pub final_transaction: TransactionEvidence,
    pub final_transaction_simulation_cu: u64,
    pub final_transaction_simulation_proof_digest_log: ProgramProofDigestLogEvidence,
    pub final_transaction_finalized_proof_digest_log: ProgramProofDigestLogEvidence,
    pub final_transaction_proof_digest_logs_both_exact: bool,
    pub final_transaction_wire_sha256: String,
    pub final_transaction_message_sha256: String,
    pub final_transaction_submitted_identically_to_simulation: bool,
    pub proof_account_before_refund: AccountEvidence,
    pub proof_account_finalized_before_refund: bool,
    pub proof_account_absent_after_refund: bool,
    pub final_transaction_refund_balances: RefundBalanceEvidence,
    pub post_finalize_upload_rejected: bool,
    pub post_finalize_second_finalize_rejected: bool,
    pub pool_before: AccountEvidence,
    pub pool_after: AccountEvidence,
    pub sequence_before: u64,
    pub sequence_after: u64,
    pub nullifier_before: Option<AccountEvidence>,
    pub nullifier_after: AccountEvidence,
    pub duplicate_simulation_rejected: bool,
    pub duplicate_simulation_error: Value,
    pub duplicate_simulation_expected_nullifier_error_exact: bool,
    pub duplicate_simulation_pool_unchanged: bool,
    pub duplicate_simulation_nullifier_unchanged: bool,
    pub duplicate_simulation_replay_probe_unchanged: bool,
    pub replay_probe_pubkey: String,
    pub replay_probe_payload_bytes: usize,
    pub replay_probe_rent_lamports: u64,
    pub replay_probe_setup_transactions: Vec<TransactionEvidence>,
    pub replay_probe_before_close: AccountEvidence,
    pub replay_probe_close_transaction: TransactionEvidence,
    pub replay_probe_absent_after_close: bool,
    pub replay_probe_refund_balances: ReplayProbeRefundEvidence,
    pub evidence_path: String,
    pub evidence_file_mode: u32,
    pub explicit_scope: Vec<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile23DevnetUploadSmokeEvidence {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub network: &'static str,
    pub genesis_hash: String,
    pub rpc_origin_redacted: String,
    pub program_id: String,
    pub payer_pubkey: String,
    pub proof_account_pubkey: String,
    pub sbf_path: String,
    pub sbf_bytes: usize,
    pub sbf_sha256: String,
    pub proof_path: String,
    pub proof_bytes: usize,
    pub proof_sha256: String,
    pub program_max_len: usize,
    pub upgradeable_program_before: UpgradeableProgramSnapshotEvidence,
    pub upgradeable_program_after: UpgradeableProgramSnapshotEvidence,
    pub upgradeable_program_continuity: UpgradeableProgramContinuityChecks,
    pub proof_upload_chunk_bytes: usize,
    pub proof_upload_window_transactions: usize,
    pub proof_upload_transaction_count: usize,
    pub proof_upload_finality_windows: usize,
    pub upload_wall_milliseconds: u64,
    pub total_wall_milliseconds: u64,
    pub upload_first_finalized_slot: u64,
    pub upload_last_finalized_slot: u64,
    pub upload_identical_wire_retries: u64,
    pub setup_transactions: Vec<TransactionEvidence>,
    pub proof_account: AccountEvidence,
    pub full_unsealed_image_verified: bool,
    pub sealed_image_verified: bool,
    pub post_finalize_upload_rejected: bool,
    pub post_finalize_upload_error: Value,
    pub post_finalize_second_finalize_rejected: bool,
    pub post_finalize_second_finalize_error: Value,
    pub evidence_path: String,
    pub evidence_file_mode: u32,
}

fn statement_public_inputs(
    statement: &aspis_statement::AtomicPaymentStatementV3,
) -> AtomicPaymentPublicInputs {
    AtomicPaymentPublicInputs {
        current_anchor: aspis_statement::encode_digest_canonical(&statement.spend.anchor),
        nullifier: aspis_statement::encode_digest_canonical(&statement.spend.nullifier),
        output_commitment: aspis_statement::encode_digest_canonical(
            &statement.spend.output_commitment,
        ),
        output_anchor: aspis_statement::encode_digest_canonical(&statement.output_anchor),
        asset_id: statement.spend.asset_id.0,
        fee: statement.spend.fee,
    }
}

#[derive(Clone, Debug, Deserialize)]
struct ReleaseGood23Branch {
    selector: u8,
    accepted: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReleaseInstance {
    proof_path: String,
    proof_bytes: u64,
    proof_sha256: String,
    statement_path: String,
    statement_bytes: u64,
    statement_sha256: String,
    statement_pool_hex: String,
    statement_sequence: u64,
    canonical_public_input_digest: String,
    selector_candidates: u8,
    serialized_selector: Option<u8>,
    least_good_selector: Option<u8>,
    good23_branches: Vec<ReleaseGood23Branch>,
    good23_definition_fingerprint: String,
    production_host_verification_green: bool,
    evaluation_error: Option<String>,
}

#[derive(Debug)]
struct ReleaseInstanceValidation {
    instance: ReleaseInstance,
    statement: aspis_statement::AtomicPaymentStatementV3,
    actual_proof_path: String,
    actual_statement_path: String,
    actual_proof_sha256: String,
    actual_statement_sha256: String,
    proof_identity_exact: bool,
    statement_identity_exact: bool,
    selector_binding_exact: bool,
    good23_fingerprint_exact: bool,
    declared_host_verification_green: bool,
    host_verification_green: bool,
    host_verification_error: Option<String>,
}

impl ReleaseInstanceValidation {
    fn all_green(&self) -> bool {
        self.proof_identity_exact
            && self.statement_identity_exact
            && self.selector_binding_exact
            && self.good23_fingerprint_exact
            && self.declared_host_verification_green
            && self.host_verification_green
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RpcAccount {
    lamports: u64,
    owner: Pubkey,
    executable: bool,
    data: Vec<u8>,
}

impl RpcAccount {
    fn evidence(&self, address: Pubkey) -> AccountEvidence {
        let mut raw = Vec::with_capacity(8 + 32 + 1 + self.data.len());
        raw.extend_from_slice(&self.lamports.to_le_bytes());
        raw.extend_from_slice(self.owner.as_ref());
        raw.push(u8::from(self.executable));
        raw.extend_from_slice(&self.data);
        AccountEvidence {
            address: address.to_string(),
            lamports: self.lamports,
            owner: self.owner.to_string(),
            executable: self.executable,
            data_len: self.data.len(),
            data_sha256: sha256(&self.data),
            raw_account_image_sha256: sha256(&raw),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct UpgradeableProgramSnapshot {
    program_id: Pubkey,
    program: RpcAccount,
    programdata_address: Pubkey,
    programdata: RpcAccount,
    programdata_slot: u64,
    upgrade_authority_address: Pubkey,
}

impl UpgradeableProgramSnapshot {
    fn evidence(&self) -> UpgradeableProgramSnapshotEvidence {
        UpgradeableProgramSnapshotEvidence {
            program_account: self.program.evidence(self.program_id),
            programdata_address: self.programdata_address.to_string(),
            programdata_account: self.programdata.evidence(self.programdata_address),
            programdata_slot: self.programdata_slot,
            upgrade_authority_address: self.upgrade_authority_address.to_string(),
        }
    }

    fn continuity_from(&self, baseline: &Self) -> UpgradeableProgramContinuityChecks {
        UpgradeableProgramContinuityChecks {
            programdata_address_unchanged: self.programdata_address == baseline.programdata_address,
            program_raw_account_image_unchanged: self.program == baseline.program,
            program_data_unchanged: self.program.data == baseline.program.data,
            programdata_raw_account_image_unchanged: self.programdata == baseline.programdata,
            programdata_data_unchanged: self.programdata.data == baseline.programdata.data,
        }
    }
}

struct Rpc {
    endpoint: String,
    client: reqwest::blocking::Client,
}

#[derive(Clone, Debug)]
struct Simulation {
    units: Option<u64>,
    error: Option<Value>,
    logs: Vec<String>,
}

fn invalid_account_data_simulation_error(instruction_index: u64) -> Value {
    json!({"InstructionError": [instruction_index, "InvalidAccountData"]})
}

fn custom_simulation_error(instruction_index: u64, code: u32) -> Value {
    json!({"InstructionError": [instruction_index, {"Custom": code}]})
}

#[derive(Clone, Copy, Debug)]
struct RecentBlockhash {
    hash: Hash,
    last_valid_block_height: u64,
}

#[derive(Clone, Debug)]
struct PendingTransaction {
    label: String,
    signature: Signature,
    wire: Vec<u8>,
    message_sha256: String,
    serialized_transaction_sha256: String,
    identical_wire_retries: u8,
    max_identical_wire_retries: u8,
}

impl PendingTransaction {
    fn into_evidence(self, finalized_slot: u64, compute_units: Option<u64>) -> TransactionEvidence {
        TransactionEvidence {
            label: self.label,
            signature: self.signature.to_string(),
            finalized_slot,
            message_sha256: self.message_sha256,
            serialized_transaction_sha256: self.serialized_transaction_sha256,
            compute_units_consumed: compute_units,
            identical_wire_retries: self.identical_wire_retries,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConfirmationProgress {
    Processed,
    Confirmed,
    Finalized,
}

impl ConfirmationProgress {
    fn as_str(self) -> &'static str {
        match self {
            Self::Processed => "processed",
            Self::Confirmed => "confirmed",
            Self::Finalized => "finalized",
        }
    }
}

#[derive(Clone, Debug)]
struct SignatureStatusObservation {
    slot: u64,
    error: Option<Value>,
    progress: ConfirmationProgress,
}

fn parse_signature_status_batch(
    result: &Value,
    expected_len: usize,
) -> Result<Vec<Option<SignatureStatusObservation>>> {
    let values = result["value"]
        .as_array()
        .context("signature-status batch omitted value array")?;
    ensure!(
        values.len() == expected_len,
        "signature-status batch length drift: expected {expected_len}, got {}",
        values.len()
    );
    values
        .iter()
        .map(|value| {
            if value.is_null() {
                return Ok(None);
            }
            let confirmation_status = value
                .get("confirmationStatus")
                .context("signature status omitted confirmationStatus")?;
            let progress = match confirmation_status.as_str() {
                Some("processed") => ConfirmationProgress::Processed,
                Some("confirmed") => ConfirmationProgress::Confirmed,
                Some("finalized") => ConfirmationProgress::Finalized,
                Some(other) => bail!("unknown signature confirmation status {other:?}"),
                None if confirmation_status.is_null() => {
                    let confirmations = value
                        .get("confirmations")
                        .context("nullable confirmationStatus omitted confirmations")?;
                    if confirmations.is_null() {
                        ConfirmationProgress::Finalized
                    } else {
                        confirmations.as_u64().context(
                            "nullable confirmationStatus had invalid confirmations field",
                        )?;
                        ConfirmationProgress::Processed
                    }
                }
                None => bail!("signature confirmationStatus was not string or null"),
            };
            Ok(Some(SignatureStatusObservation {
                slot: value["slot"]
                    .as_u64()
                    .context("signature status omitted slot")?,
                error: (!value["err"].is_null()).then(|| value["err"].clone()),
                progress,
            }))
        })
        .collect()
}

#[derive(Clone, Copy, Debug)]
struct TrackedFinalization {
    slot: u64,
    progress: ConfirmationProgress,
}

/// Fail-closed, order-preserving state machine for submitted writes.
///
/// The caller may observe the signatures in any finalization order, but a
/// successful result is available only after every signature is finalized. A
/// load-balanced RPC may transiently report pre-finality fork regressions, so
/// only finalized observations are latched; response-shape drift and on-chain
/// errors still abort the batch.
struct FinalizationTracker {
    signatures: Vec<Signature>,
    observations: Vec<Option<TrackedFinalization>>,
}

impl FinalizationTracker {
    fn new(signatures: Vec<Signature>) -> Result<Self> {
        ensure!(
            !signatures.is_empty(),
            "finalization batch must not be empty"
        );
        let unique = signatures
            .iter()
            .map(ToString::to_string)
            .collect::<BTreeSet<_>>();
        ensure!(
            unique.len() == signatures.len(),
            "finalization batch contains duplicate signatures"
        );
        let observations = vec![None; signatures.len()];
        Ok(Self {
            signatures,
            observations,
        })
    }

    fn observe(&mut self, statuses: Vec<Option<SignatureStatusObservation>>) -> Result<bool> {
        ensure!(
            statuses.len() == self.signatures.len(),
            "signature-status observation length drift"
        );
        for (index, status) in statuses.into_iter().enumerate() {
            let signature = &self.signatures[index];
            let Some(status) = status else {
                if !self.observations[index]
                    .is_some_and(|previous| previous.progress == ConfirmationProgress::Finalized)
                {
                    self.observations[index] = None;
                }
                continue;
            };
            if let Some(error) = status.error {
                bail!("transaction {signature} failed: {error}");
            }
            if self.observations[index]
                .is_some_and(|previous| previous.progress == ConfirmationProgress::Finalized)
            {
                continue;
            }
            self.observations[index] = Some(TrackedFinalization {
                slot: status.slot,
                progress: status.progress,
            });
        }
        Ok(self.observations.iter().all(|observation| {
            observation.is_some_and(|status| status.progress == ConfirmationProgress::Finalized)
        }))
    }

    fn ensure_unseen_not_expired(
        &self,
        current_block_height: u64,
        last_valid_block_height: u64,
    ) -> Result<()> {
        if current_block_height > last_valid_block_height {
            let unseen = self
                .observations
                .iter()
                .enumerate()
                .filter_map(|(index, observation)| {
                    observation
                        .is_none()
                        .then_some(self.signatures[index].to_string())
                })
                .collect::<Vec<_>>();
            ensure!(
                unseen.is_empty(),
                "blockhash expired with {} unobserved transaction(s): {}",
                unseen.len(),
                unseen.join(", ")
            );
        }
        Ok(())
    }

    fn unobserved_indices(&self) -> Vec<usize> {
        self.observations
            .iter()
            .enumerate()
            .filter_map(|(index, observation)| observation.is_none().then_some(index))
            .collect()
    }

    fn finalized_slots_in_submission_order(&self) -> Result<Vec<u64>> {
        self.observations
            .iter()
            .map(|observation| match observation {
                Some(status) if status.progress == ConfirmationProgress::Finalized => {
                    Ok(status.slot)
                }
                _ => bail!("finalization batch is incomplete"),
            })
            .collect()
    }
}

fn rpc_read_retryable(error: &anyhow::Error) -> bool {
    let rendered = format!("{error:#}");
    rendered.contains("\"code\":429")
        || rendered.contains("HTTP 429")
        || rendered.contains("Too Many Requests")
        || rendered.contains("transport failure")
        || rendered.contains("HTTP 502")
        || rendered.contains("HTTP 503")
        || rendered.contains("HTTP 504")
}

impl Rpc {
    fn new(endpoint: String) -> Result<Self> {
        Ok(Self {
            endpoint,
            client: reqwest::blocking::Client::builder()
                .timeout(Duration::from_secs(60))
                .build()?,
        })
    }

    fn call(&self, method: &str, params: Value) -> Result<Value> {
        let response = self
            .client
            .post(&self.endpoint)
            .json(&json!({"jsonrpc":"2.0","id":1,"method":method,"params":params}))
            .send()
            .map_err(|_| anyhow!("RPC {method} transport failure (endpoint redacted)"))?;
        let status = response.status();
        let value: Value = response.json().with_context(|| {
            format!("RPC {method} non-JSON response (HTTP {})", status.as_u16())
        })?;
        if let Some(error) = value.get("error") {
            bail!("RPC {method} error: {error}");
        }
        value
            .get("result")
            .cloned()
            .ok_or_else(|| anyhow!("RPC {method} omitted result"))
    }

    fn call_read(&self, method: &str, params: Value) -> Result<Value> {
        let mut retries = 0u8;
        loop {
            match self.call(method, params.clone()) {
                Ok(value) => return Ok(value),
                Err(error)
                    if retries < READ_ONLY_RPC_RATE_LIMIT_RETRIES && rpc_read_retryable(&error) =>
                {
                    retries += 1;
                    thread::sleep(Duration::from_secs(2));
                }
                Err(error) => return Err(error),
            }
        }
    }

    fn genesis_hash(&self) -> Result<String> {
        self.call_read("getGenesisHash", json!([]))?
            .as_str()
            .map(ToOwned::to_owned)
            .context("getGenesisHash result was not a string")
    }

    fn latest_blockhash_with_expiry(&self) -> Result<RecentBlockhash> {
        let result = self.call_read("getLatestBlockhash", json!([{"commitment":"finalized"}]))?;
        let value = &result["value"];
        Ok(RecentBlockhash {
            hash: value["blockhash"]
                .as_str()
                .context("latest blockhash missing")?
                .parse()
                .context("latest blockhash invalid")?,
            last_valid_block_height: value["lastValidBlockHeight"]
                .as_u64()
                .context("latest blockhash omitted lastValidBlockHeight")?,
        })
    }

    fn latest_blockhash(&self) -> Result<Hash> {
        Ok(self.latest_blockhash_with_expiry()?.hash)
    }

    fn block_height(&self) -> Result<u64> {
        self.call_read("getBlockHeight", json!([{"commitment":"finalized"}]))?
            .as_u64()
            .context("block height was not u64")
    }

    fn account(&self, address: &Pubkey) -> Result<Option<RpcAccount>> {
        let result = self.call_read(
            "getAccountInfo",
            json!([address.to_string(), {"encoding":"base64","commitment":"finalized"}]),
        )?;
        let value = &result["value"];
        if value.is_null() {
            return Ok(None);
        }
        Ok(Some(RpcAccount {
            lamports: value["lamports"]
                .as_u64()
                .context("account lamports missing")?,
            owner: value["owner"]
                .as_str()
                .context("account owner missing")?
                .parse()?,
            executable: value["executable"]
                .as_bool()
                .context("account executable flag missing")?,
            data: BASE64.decode(
                value["data"][0]
                    .as_str()
                    .context("account base64 data missing")?,
            )?,
        }))
    }

    fn rent(&self, bytes: usize) -> Result<u64> {
        self.call_read("getMinimumBalanceForRentExemption", json!([bytes]))?
            .as_u64()
            .context("rent result was not u64")
    }

    fn balance(&self, address: &Pubkey) -> Result<u64> {
        self.call_read(
            "getBalance",
            json!([address.to_string(), {"commitment":"finalized"}]),
        )?["value"]
            .as_u64()
            .context("balance result was not u64")
    }

    fn simulate_exact(&self, wire: &[u8]) -> Result<Simulation> {
        let result = self.call_read(
            "simulateTransaction",
            json!([BASE64.encode(wire), {
                "encoding":"base64",
                "sigVerify":true,
                "replaceRecentBlockhash":false,
                "commitment":"finalized"
            }]),
        )?;
        let error = if result["value"]["err"].is_null() {
            None
        } else {
            Some(result["value"]["err"].clone())
        };
        let logs = result["value"]["logs"]
            .as_array()
            .context("simulation omitted logs")?
            .iter()
            .map(|line| {
                line.as_str()
                    .map(ToOwned::to_owned)
                    .context("simulation log was not a string")
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Simulation {
            units: result["value"]["unitsConsumed"].as_u64(),
            error,
            logs,
        })
    }

    fn signature_statuses(
        &self,
        signatures: &[Signature],
    ) -> Result<Vec<Option<SignatureStatusObservation>>> {
        ensure!(
            !signatures.is_empty() && signatures.len() <= 256,
            "signature-status batch must contain 1..=256 signatures"
        );
        let result = self.call_read(
            "getSignatureStatuses",
            json!([
                signatures.iter().map(ToString::to_string).collect::<Vec<_>>(),
                {"searchTransactionHistory":true}
            ]),
        )?;
        parse_signature_status_batch(&result, signatures.len())
    }

    fn signature_status(
        &self,
        signature: &Signature,
    ) -> Result<Option<(u64, Option<Value>, String)>> {
        let status = self
            .signature_statuses(&[*signature])?
            .pop()
            .context("single-signature status parser returned no entry")?;
        Ok(status.map(|status| {
            (
                status.slot,
                status.error,
                status.progress.as_str().to_owned(),
            )
        }))
    }

    fn wait_finalized(&self, signature: &Signature) -> Result<u64> {
        let started = Instant::now();
        loop {
            if let Some((slot, error, confirmation)) = self.signature_status(signature)? {
                if let Some(error) = error {
                    bail!("transaction {signature} failed: {error}");
                }
                if confirmation == "finalized" {
                    return Ok(slot);
                }
            }
            ensure!(
                started.elapsed() < DEFAULT_CONFIRM_TIMEOUT,
                "transaction {signature} did not finalize before timeout"
            );
            thread::sleep(SIGNATURE_POLL_INTERVAL);
        }
    }

    fn transaction_cu(&self, signature: &Signature) -> Result<Option<u64>> {
        let result = self.call_read(
            "getTransaction",
            json!([signature.to_string(), {
                "encoding":"json",
                "commitment":"finalized",
                "maxSupportedTransactionVersion":0
            }]),
        )?;
        Ok(result["meta"]["computeUnitsConsumed"].as_u64())
    }

    fn transaction_fee_balances_and_logs(
        &self,
        signature: &Signature,
    ) -> Result<(u64, Vec<u64>, Vec<u64>, Vec<String>)> {
        let result = self.call_read(
            "getTransaction",
            json!([signature.to_string(), {
                "encoding":"json",
                "commitment":"finalized",
                "maxSupportedTransactionVersion":0
            }]),
        )?;
        ensure!(
            result["meta"]["err"].is_null(),
            "finalized transaction failed"
        );
        let fee = result["meta"]["fee"]
            .as_u64()
            .context("finalized transaction omitted fee")?;
        let parse_balances = |field: &str| -> Result<Vec<u64>> {
            result["meta"][field]
                .as_array()
                .with_context(|| format!("finalized transaction omitted {field}"))?
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .with_context(|| format!("{field} contained a non-u64 balance"))
                })
                .collect()
        };
        let logs = result["meta"]["logMessages"]
            .as_array()
            .context("finalized transaction omitted logMessages")?
            .iter()
            .map(|line| {
                line.as_str()
                    .map(ToOwned::to_owned)
                    .context("finalized transaction log was not a string")
            })
            .collect::<Result<Vec<_>>>()?;
        Ok((
            fee,
            parse_balances("preBalances")?,
            parse_balances("postBalances")?,
            logs,
        ))
    }

    fn transaction_wire(&self, signature: &Signature) -> Result<(Vec<u8>, VersionedTransaction)> {
        let result = self.call_read(
            "getTransaction",
            json!([signature.to_string(), {
                "encoding":"base64",
                "commitment":"finalized",
                "maxSupportedTransactionVersion":0
            }]),
        )?;
        let encoded = result["transaction"][0]
            .as_str()
            .context("finalized transaction base64 missing")?;
        let wire = BASE64.decode(encoded)?;
        let transaction: VersionedTransaction =
            bincode::deserialize(&wire).context("decode finalized versioned transaction")?;
        Ok((wire, transaction))
    }

    fn transaction_wire_and_message_hash(&self, signature: &Signature) -> Result<(String, String)> {
        let (wire, transaction) = self.transaction_wire(signature)?;
        Ok((
            sha256(&wire),
            sha256(&bincode::serialize(&transaction.message)?),
        ))
    }

    fn send_wire_once(&self, wire: &[u8]) -> Result<Value> {
        self.call(
            "sendTransaction",
            json!([BASE64.encode(wire), {
                "encoding":"base64",
                "skipPreflight":false,
                "preflightCommitment":"finalized",
                "maxRetries":0
            }]),
        )
    }

    fn submit_wire_pending(
        &self,
        wire: &[u8],
        expected_signature: Signature,
        max_identical_retries: u8,
        label: &str,
        message_sha256: String,
    ) -> Result<PendingTransaction> {
        let mut retries = 0u8;
        let first = self.send_wire_once(wire);
        match first {
            Ok(value) => {
                ensure!(
                    value.as_str() == Some(expected_signature.to_string().as_str()),
                    "RPC returned a different signature for {label}"
                );
            }
            Err(first_error) => {
                let observed = self.signature_status(&expected_signature)?;
                if observed.is_none() {
                    if max_identical_retries == 0 || !rpc_read_retryable(&first_error) {
                        return Err(first_error).with_context(|| format!("submit {label}"));
                    }
                    retries = 1;
                    match self.send_wire_once(wire) {
                        Ok(value) => ensure!(
                            value.as_str() == Some(expected_signature.to_string().as_str()),
                            "RPC returned a different signature on identical retry"
                        ),
                        Err(retry_error) => {
                            let observed_after_retry =
                                self.signature_status(&expected_signature)?;
                            if observed_after_retry.is_none()
                                && (!rpc_read_retryable(&retry_error)
                                    || retries >= max_identical_retries)
                            {
                                return Err(retry_error).with_context(|| {
                                    format!(
                                        "identical-wire retry failed after ambiguous first submit: {first_error}"
                                    )
                                });
                            }
                        }
                    }
                }
            }
        }
        Ok(PendingTransaction {
            label: label.to_owned(),
            signature: expected_signature,
            wire: wire.to_vec(),
            message_sha256,
            serialized_transaction_sha256: sha256(wire),
            identical_wire_retries: retries,
            max_identical_wire_retries: max_identical_retries,
        })
    }

    fn wait_finalized_batch(
        &self,
        mut pending: Vec<PendingTransaction>,
        last_valid_block_height: u64,
    ) -> Result<Vec<TransactionEvidence>> {
        let signatures = pending
            .iter()
            .map(|transaction| transaction.signature)
            .collect::<Vec<_>>();
        let mut tracker = FinalizationTracker::new(signatures.clone())?;
        let started = Instant::now();
        let mut next_rebroadcast = UPLOAD_REBROADCAST_INTERVAL;
        loop {
            if tracker.observe(self.signature_statuses(&signatures)?)? {
                break;
            }
            tracker.ensure_unseen_not_expired(self.block_height()?, last_valid_block_height)?;
            if started.elapsed() >= next_rebroadcast {
                for index in tracker.unobserved_indices() {
                    let transaction = &mut pending[index];
                    if transaction.identical_wire_retries >= transaction.max_identical_wire_retries
                    {
                        continue;
                    }
                    transaction.identical_wire_retries += 1;
                    match self.send_wire_once(&transaction.wire) {
                        Ok(value) => ensure!(
                            value.as_str() == Some(transaction.signature.to_string().as_str()),
                            "RPC returned a different signature while rebroadcasting {}",
                            transaction.label
                        ),
                        Err(error) if rpc_read_retryable(&error) => {}
                        Err(error) => {
                            ensure!(
                                self.signature_status(&transaction.signature)?.is_some(),
                                "non-retryable identical-wire rebroadcast failed for {}: {error}",
                                transaction.label
                            );
                        }
                    }
                }
                next_rebroadcast += UPLOAD_REBROADCAST_INTERVAL;
            }
            ensure!(
                started.elapsed() < DEFAULT_CONFIRM_TIMEOUT,
                "transaction batch did not finalize before timeout"
            );
            thread::sleep(SIGNATURE_POLL_INTERVAL);
        }
        let slots = tracker.finalized_slots_in_submission_order()?;
        pending
            .into_iter()
            .zip(slots)
            .map(|(transaction, slot)| {
                let compute_units = self.transaction_cu(&transaction.signature)?;
                Ok(transaction.into_evidence(slot, compute_units))
            })
            .collect()
    }

    fn submit_wire(
        &self,
        wire: &[u8],
        expected_signature: Signature,
        allow_one_identical_retry: bool,
        label: &str,
        message_sha256: String,
    ) -> Result<TransactionEvidence> {
        let pending = self.submit_wire_pending(
            wire,
            expected_signature,
            u8::from(allow_one_identical_retry),
            label,
            message_sha256,
        )?;
        let slot = self.wait_finalized(&pending.signature)?;
        let compute_units = self.transaction_cu(&pending.signature)?;
        Ok(pending.into_evidence(slot, compute_units))
    }

    fn submit_transaction_pending(
        &self,
        transaction: &Transaction,
        label: &str,
        max_identical_retries: u8,
    ) -> Result<PendingTransaction> {
        let wire = bincode::serialize(transaction)?;
        self.submit_wire_pending(
            &wire,
            transaction.signatures[0],
            max_identical_retries,
            label,
            sha256(&bincode::serialize(&transaction.message)?),
        )
    }

    fn submit_transaction(
        &self,
        transaction: &Transaction,
        label: &str,
    ) -> Result<TransactionEvidence> {
        let wire = bincode::serialize(transaction)?;
        self.submit_wire(
            &wire,
            transaction.signatures[0],
            true,
            label,
            sha256(&bincode::serialize(&transaction.message)?),
        )
    }
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn require_program_proof_digest_log(
    logs: &[String],
    release_proof_sha256: &str,
) -> Result<ProgramProofDigestLogEvidence> {
    let mut matching = Vec::new();
    for line in logs {
        let Some(encoded) = line.strip_prefix("Program data: ") else {
            continue;
        };
        let chunks = encoded
            .split_ascii_whitespace()
            .map(|chunk| {
                BASE64
                    .decode(chunk)
                    .context("decode Program data log chunk")
            })
            .collect::<Result<Vec<_>>>()?;
        if chunks.first().map(Vec::as_slice) != Some(PROOF_SHA256_LOG_MARKER) {
            continue;
        }
        ensure!(
            chunks.len() == 2 && chunks[1].len() == 32,
            "proof-digest Program data log had malformed framing"
        );
        matching.push((line.clone(), chunks[1].clone()));
    }
    ensure!(
        matching.len() == 1,
        "expected exactly one aspis-proof-sha256-v1 log, observed {}",
        matching.len()
    );
    let (raw_log_line, digest) = matching.pop().unwrap();
    let logged_proof_sha256 = digest
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let exact_release_proof_digest = logged_proof_sha256 == release_proof_sha256;
    ensure!(
        exact_release_proof_digest,
        "program-logged proof digest differs from the release proof digest"
    );
    Ok(ProgramProofDigestLogEvidence {
        marker: "aspis-proof-sha256-v1",
        raw_log_line,
        logged_proof_sha256,
        release_proof_sha256: release_proof_sha256.to_owned(),
        exact_release_proof_digest,
    })
}

fn parse_args(arguments: &[String], mode: CommandMode) -> Result<DevnetConfig> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_devnet_interlock = false;
    let mut execute_mainnet_interlock = false;
    let mut use_tpu_client = false;
    let mut resume_in_progress = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-devnet" {
            ensure!(!execute_devnet_interlock, "duplicate --execute-devnet");
            execute_devnet_interlock = true;
            index += 1;
            continue;
        }
        if key == "--execute-mainnet" {
            ensure!(!execute_mainnet_interlock, "duplicate --execute-mainnet");
            execute_mainnet_interlock = true;
            index += 1;
            continue;
        }
        if key == "--use-tpu-client" {
            ensure!(!use_tpu_client, "duplicate --use-tpu-client");
            use_tpu_client = true;
            index += 1;
            continue;
        }
        if key == "--resume-in-progress" {
            ensure!(!resume_in_progress, "duplicate --resume-in-progress");
            resume_in_progress = true;
            index += 1;
            continue;
        }
        ensure!(
            key.starts_with("--"),
            "unexpected positional argument {key}"
        );
        let value = arguments
            .get(index + 1)
            .ok_or_else(|| anyhow!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), value.clone()).is_none(),
            "duplicate argument {key}"
        );
        index += 2;
    }
    let allowed = [
        "--rpc-url",
        "--payer-keypair",
        "--program-keypair",
        "--pool-keypair",
        "--proof-account-keypair",
        "--replay-probe-keypair",
        "--upgrade-authority-keypair",
        "--deployment-buffer-keypair",
        "--release",
        "--sbf",
        "--proof",
        "--statement",
        "--solana-cli",
        "--evidence",
        "--program-max-len",
        "--fee-reserve-lamports",
        "--acknowledgement",
        "--resume-pool-create-signature",
        "--resume-pool-init-signature",
        "--resume-proof-create-signature",
    ];
    for key in values.keys() {
        ensure!(allowed.contains(&key.as_str()), "unknown argument {key}");
    }
    match mode {
        CommandMode::Readiness => ensure!(
            !execute_devnet_interlock
                && !execute_mainnet_interlock
                && !values.contains_key("--acknowledgement"),
            "readiness refuses execution interlocks"
        ),
        CommandMode::Execute => ensure!(
            !execute_mainnet_interlock,
            "devnet execution refuses --execute-mainnet"
        ),
        CommandMode::ExecuteMainnet => ensure!(
            !execute_devnet_interlock,
            "mainnet execution refuses --execute-devnet"
        ),
    }
    ensure!(
        resume_in_progress == values.contains_key("--resume-pool-create-signature"),
        "--resume-in-progress and --resume-pool-create-signature must be supplied together"
    );
    let has_pool_init_signature = values.contains_key("--resume-pool-init-signature");
    let has_proof_create_signature = values.contains_key("--resume-proof-create-signature");
    ensure!(
        has_pool_init_signature == has_proof_create_signature,
        "resume pool-init and proof-create signatures must be supplied together"
    );
    ensure!(
        !has_pool_init_signature || resume_in_progress,
        "resume checkpoint signatures require --resume-in-progress"
    );
    let required = |key: &str| {
        values
            .get(key)
            .cloned()
            .ok_or_else(|| anyhow!("missing required explicit argument {key}"))
    };
    let absolute = |key: &str| -> Result<PathBuf> {
        let path = PathBuf::from(required(key)?);
        ensure!(path.is_absolute(), "{key} must be an absolute path");
        Ok(path)
    };
    let optional_absolute = |key: &str| -> Result<Option<PathBuf>> {
        values
            .get(key)
            .map(|value| {
                let path = PathBuf::from(value);
                ensure!(path.is_absolute(), "{key} must be an absolute path");
                Ok(path)
            })
            .transpose()
    };
    Ok(DevnetConfig {
        rpc_url: required("--rpc-url")?,
        payer_keypair: absolute("--payer-keypair")?,
        program_keypair: absolute("--program-keypair")?,
        pool_keypair: absolute("--pool-keypair")?,
        proof_account_keypair: absolute("--proof-account-keypair")?,
        replay_probe_keypair: optional_absolute("--replay-probe-keypair")?,
        upgrade_authority_keypair: optional_absolute("--upgrade-authority-keypair")?,
        deployment_buffer_keypair: optional_absolute("--deployment-buffer-keypair")?,
        use_tpu_client,
        release: absolute("--release")?,
        sbf: absolute("--sbf")?,
        proof: absolute("--proof")?,
        statement: absolute("--statement")?,
        solana_cli: absolute("--solana-cli")?,
        evidence: absolute("--evidence")?,
        program_max_len: required("--program-max-len")?
            .parse()
            .context("--program-max-len is not usize")?,
        fee_reserve_lamports: required("--fee-reserve-lamports")?
            .parse()
            .context("--fee-reserve-lamports is not u64")?,
        execute_interlock: match mode {
            CommandMode::Readiness => false,
            CommandMode::Execute => execute_devnet_interlock,
            CommandMode::ExecuteMainnet => execute_mainnet_interlock,
        },
        resume_in_progress,
        resume_pool_create_signature: values
            .get("--resume-pool-create-signature")
            .map(|value| Signature::from_str(value).context("invalid resume pool signature"))
            .transpose()?,
        resume_pool_init_signature: values
            .get("--resume-pool-init-signature")
            .map(|value| Signature::from_str(value).context("invalid resume pool-init signature"))
            .transpose()?,
        resume_proof_create_signature: values
            .get("--resume-proof-create-signature")
            .map(|value| {
                Signature::from_str(value).context("invalid resume proof-create signature")
            })
            .transpose()?,
        acknowledgement: values.get("--acknowledgement").cloned(),
    })
}

fn validate_execution_policy(config: &DevnetConfig, policy: ClusterPolicy) -> Result<()> {
    ensure!(
        config.execute_interlock,
        "missing exact execution interlock"
    );
    ensure!(
        config.acknowledgement.as_deref() == Some(policy.execution_acknowledgement()),
        "missing exact {} mutation acknowledgement",
        policy.network()
    );
    if policy.requires_explicit_recovery_signers() {
        ensure!(
            config.replay_probe_keypair.is_some(),
            "mainnet requires --replay-probe-keypair"
        );
        ensure!(
            config.upgrade_authority_keypair.is_some(),
            "mainnet requires --upgrade-authority-keypair"
        );
        ensure!(
            config.deployment_buffer_keypair.is_some(),
            "mainnet requires --deployment-buffer-keypair"
        );
        ensure!(config.use_tpu_client, "mainnet requires --use-tpu-client");
    }
    Ok(())
}

fn parse_upload_smoke_args(arguments: &[String]) -> Result<UploadSmokeConfig> {
    let mut values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == "--execute-devnet" {
            ensure!(!execute_interlock, "duplicate --execute-devnet");
            execute_interlock = true;
            index += 1;
            continue;
        }
        ensure!(
            key.starts_with("--"),
            "unexpected positional argument {key}"
        );
        let value = arguments
            .get(index + 1)
            .ok_or_else(|| anyhow!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), value.clone()).is_none(),
            "duplicate argument {key}"
        );
        index += 2;
    }
    let allowed = [
        "--rpc-url",
        "--payer-keypair",
        "--proof-account-keypair",
        "--sbf",
        "--proof",
        "--evidence",
        "--program-max-len",
        "--fee-reserve-lamports",
        "--acknowledgement",
    ];
    for key in values.keys() {
        ensure!(allowed.contains(&key.as_str()), "unknown argument {key}");
    }
    let required = |key: &str| {
        values
            .get(key)
            .cloned()
            .ok_or_else(|| anyhow!("missing required explicit argument {key}"))
    };
    let absolute = |key: &str| -> Result<PathBuf> {
        let path = PathBuf::from(required(key)?);
        ensure!(path.is_absolute(), "{key} must be an absolute path");
        Ok(path)
    };
    Ok(UploadSmokeConfig {
        rpc_url: required("--rpc-url")?,
        payer_keypair: absolute("--payer-keypair")?,
        proof_account_keypair: absolute("--proof-account-keypair")?,
        sbf: absolute("--sbf")?,
        proof: absolute("--proof")?,
        evidence: absolute("--evidence")?,
        program_max_len: required("--program-max-len")?
            .parse()
            .context("--program-max-len is not usize")?,
        fee_reserve_lamports: required("--fee-reserve-lamports")?
            .parse()
            .context("--fee-reserve-lamports is not u64")?,
        execute_interlock,
        acknowledgement: values.get("--acknowledgement").cloned(),
    })
}

fn secure_keypair(path: &Path) -> Result<Keypair> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("keypair unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "keypair must be a regular non-symlink file"
    );
    ensure!(
        metadata.permissions().mode() & 0o077 == 0,
        "keypair permissions must exclude group/other access"
    );
    read_keypair_file(path).map_err(|_| anyhow!("could not decode keypair {}", path.display()))
}

fn exact_regular_file(path: &Path) -> Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("file unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "input must be a regular non-symlink file: {}",
        path.display()
    );
    fs::read(path).with_context(|| format!("read {}", path.display()))
}

fn rpc_origin(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("invalid RPC URL")?;
    ensure!(url.scheme() == "https", "devnet RPC must use HTTPS");
    ensure!(
        url.username().is_empty() && url.password().is_none(),
        "RPC credentials may not use URL userinfo"
    );
    let host = url.host_str().context("RPC URL omitted host")?;
    Ok(format!(
        "https://{}{}<redacted>",
        host,
        url.port()
            .map(|port| format!(":{port}/"))
            .unwrap_or_else(|| "/".to_owned())
    ))
}

fn release_artifacts_exact(release: &Value, workspace_root: &Path) -> Result<()> {
    let artifacts = release["source_artifacts"]
        .as_array()
        .context("release source_artifacts missing")?;
    ensure!(
        !artifacts.is_empty(),
        "release source_artifacts must be nonempty"
    );
    for artifact in artifacts {
        let path = artifact["path"]
            .as_str()
            .context("release source path missing")?;
        let expected_len = artifact["bytes"]
            .as_u64()
            .context("release source bytes missing")?;
        let expected_sha = artifact["sha256"]
            .as_str()
            .context("release source hash missing")?;
        let path = if Path::new(path).is_absolute() {
            PathBuf::from(path)
        } else {
            workspace_root.join(path)
        };
        let bytes = exact_regular_file(&path)?;
        ensure!(
            bytes.len() as u64 == expected_len,
            "release source length drift: {}",
            path.display()
        );
        ensure!(
            sha256(&bytes) == expected_sha,
            "release source hash drift: {}",
            path.display()
        );
    }
    Ok(())
}

fn release_certificate_green_gate_count(release: &Value) -> Option<usize> {
    let gates = release["gates"].as_array()?;
    let failed_gates = release["failed_gates"].as_array()?;
    (release["artifact"].as_str() == Some("profile23_one_transaction_release")
        && release["released"].as_bool() == Some(true)
        && release["status"].as_str() == Some("released_all_required_gates_green")
        && !gates.is_empty()
        && gates
            .iter()
            .all(|gate| gate["passed"].as_bool() == Some(true))
        && failed_gates.is_empty())
    .then_some(gates.len())
}

fn release_without_generation_time(release: &Value) -> Result<Value> {
    let mut release = release.clone();
    let object = release
        .as_object_mut()
        .context("release certificate must be a JSON object")?;
    ensure!(
        object
            .remove("generated_at_utc")
            .is_some_and(|value| value.is_string()),
        "release certificate omitted a string generated_at_utc"
    );
    Ok(release)
}

fn release_matches_live_evaluation(
    supplied: &Value,
    live: &crate::profile23_release::Profile23OneTransactionRelease,
) -> Result<bool> {
    let live = serde_json::to_value(live).context("serialize live release evaluation")?;
    release_values_match_ignoring_generation_time(supplied, &live)
}

fn release_values_match_ignoring_generation_time(left: &Value, right: &Value) -> Result<bool> {
    Ok(release_without_generation_time(left)? == release_without_generation_time(right)?)
}

fn is_normal_workspace_relative(path: &str) -> bool {
    let path = Path::new(path);
    !path.is_absolute()
        && path.components().next().is_some()
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

fn recorded_workspace_path(workspace_root: &Path, path: &Path) -> Result<String> {
    let workspace_root = workspace_root
        .canonicalize()
        .with_context(|| format!("canonicalize workspace {}", workspace_root.display()))?;
    let path = path
        .canonicalize()
        .with_context(|| format!("canonicalize release-instance input {}", path.display()))?;
    let relative = path.strip_prefix(&workspace_root).with_context(|| {
        format!(
            "release-instance input resolves outside workspace: {}",
            path.display()
        )
    })?;
    ensure!(
        relative.components().next().is_some()
            && relative
                .components()
                .all(|component| matches!(component, Component::Normal(_))),
        "release-instance input is not a normal workspace-relative path: {}",
        relative.display()
    );
    Ok(relative.display().to_string())
}

fn decode_release_instance(release: &Value) -> Result<ReleaseInstance> {
    serde_json::from_value(
        release
            .get("release_instance")
            .context("release certificate omitted release_instance")?
            .clone(),
    )
    .context("decode exact release_instance schema")
}

fn live_good23_definition_fingerprint() -> String {
    format!(
        "0x{}",
        profile23_hex(
            &aspis_prover::state_only_good23::profile23_good_schedule_definition_fingerprint(
                aspis_prover::HOST_HASH,
            )
        )
    )
}

fn validate_release_instance(
    release: &Value,
    workspace_root: &Path,
    proof_path: &Path,
    proof: &[u8],
    statement_path: &Path,
    statement_bytes: &[u8],
) -> Result<ReleaseInstanceValidation> {
    let instance = decode_release_instance(release)?;
    let actual_proof_path = recorded_workspace_path(workspace_root, proof_path)?;
    let actual_statement_path = recorded_workspace_path(workspace_root, statement_path)?;
    let actual_proof_sha256 = sha256(proof);
    let actual_statement_sha256 = sha256(statement_bytes);
    let statement = decode_profile23_statement_sidecar(statement_bytes)?;
    let statement_digest = canonical_profile23_public_input_digest(&statement)?;

    let proof_identity_exact = is_normal_workspace_relative(&instance.proof_path)
        && instance.proof_path == actual_proof_path
        && instance.proof_bytes == proof.len() as u64
        && instance.proof_sha256 == actual_proof_sha256;
    let statement_identity_exact = is_normal_workspace_relative(&instance.statement_path)
        && instance.statement_path == actual_statement_path
        && instance.statement_bytes == statement_bytes.len() as u64
        && instance.statement_sha256 == actual_statement_sha256
        && instance.statement_pool_hex == profile23_hex(&statement.pool)
        && instance.statement_sequence == statement.sequence
        && instance.canonical_public_input_digest == statement_digest;

    let candidate_count = usize::from(instance.selector_candidates);
    let recomputed_least_good = instance
        .good23_branches
        .iter()
        .find(|branch| branch.accepted)
        .map(|branch| branch.selector);
    let parsed_proof_selector =
        aspis_core::state_only_prefix::StateOnlyProfile23Prefix::parse_from_proof(proof)
            .ok()
            .and_then(|(prefix, suffix)| (!suffix.is_empty()).then_some(prefix.query_selector));
    let selector_binding_exact = candidate_count
        == usize::from(aspis_core::state_only_prefix::STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT)
        && candidate_count == 3
        && instance.good23_branches.len() == candidate_count
        && instance
            .good23_branches
            .iter()
            .enumerate()
            .all(|(selector, branch)| usize::from(branch.selector) == selector)
        && recomputed_least_good.is_some()
        && instance.least_good_selector == recomputed_least_good
        && instance.serialized_selector == recomputed_least_good
        && parsed_proof_selector == instance.serialized_selector
        && instance.evaluation_error.is_none();
    let good23_fingerprint_exact =
        instance.good23_definition_fingerprint == live_good23_definition_fingerprint();
    let declared_host_verification_green = instance.production_host_verification_green;
    let host_result = aspis_statement::state_only_profile23::verify_atomic_state_only_profile23_v3(
        proof,
        &statement,
        aspis_prover::HOST_HASH,
        None,
    );
    let host_verification_green = host_result.is_ok();
    let host_verification_error = host_result.err().map(|error| format!("{error:?}"));

    Ok(ReleaseInstanceValidation {
        instance,
        statement,
        actual_proof_path,
        actual_statement_path,
        actual_proof_sha256,
        actual_statement_sha256,
        proof_identity_exact,
        statement_identity_exact,
        selector_binding_exact,
        good23_fingerprint_exact,
        declared_host_verification_green,
        host_verification_green,
        host_verification_error,
    })
}

fn parse_program(account: &RpcAccount) -> Result<Pubkey> {
    ensure!(
        account.owner == bpf_loader_upgradeable::id() && account.executable,
        "program account is not executable BPFLoaderUpgradeable"
    );
    match bincode::deserialize(&account.data)? {
        UpgradeableLoaderState::Program {
            programdata_address,
        } => Ok(programdata_address),
        _ => bail!("declared program address is not a Program account"),
    }
}

fn deployed_program_exact(
    rpc: &Rpc,
    program_id: &Pubkey,
    expected_sbf: &[u8],
    expected_max_len: usize,
    expected_authority: &Pubkey,
) -> Result<Option<UpgradeableProgramSnapshot>> {
    let Some(program) = rpc.account(program_id)? else {
        return Ok(None);
    };
    let programdata_address = parse_program(&program)?;
    let programdata = rpc
        .account(&programdata_address)?
        .context("ProgramData account missing")?;
    ensure!(programdata.owner == bpf_loader_upgradeable::id());
    let state: UpgradeableLoaderState = bincode::deserialize(&programdata.data)?;
    let UpgradeableLoaderState::ProgramData {
        slot: programdata_slot,
        upgrade_authority_address,
    } = state
    else {
        bail!("linked account is not ProgramData")
    };
    let upgrade_authority_address = upgrade_authority_address
        .context("devnet rehearsal ProgramData has no upgrade authority")?;
    ensure!(
        upgrade_authority_address == *expected_authority,
        "devnet rehearsal upgrade authority does not equal explicit payer"
    );
    let code = programdata
        .data
        .get(PROGRAMDATA_METADATA_BYTES..)
        .context("ProgramData shorter than metadata")?;
    ensure!(
        code.len() == expected_max_len,
        "ProgramData max length mismatch"
    );
    ensure!(
        code.get(..expected_sbf.len()) == Some(expected_sbf),
        "deployed program bytes differ from release SBF"
    );
    ensure!(
        code[expected_sbf.len()..].iter().all(|byte| *byte == 0),
        "deployed ProgramData padding is nonzero"
    );
    Ok(Some(UpgradeableProgramSnapshot {
        program_id: *program_id,
        program,
        programdata_address,
        programdata,
        programdata_slot,
        upgrade_authority_address,
    }))
}

fn nullifier_compatible(account: Option<&RpcAccount>, program_id: &Pubkey) -> bool {
    match account {
        None => true,
        Some(account) if account.owner == system_program::id() => {
            !account.executable && account.data.is_empty()
        }
        Some(account) if account.owner == *program_id => {
            !account.executable
                && account.data.len() == ATOMIC_NULLIFIER_MARKER_LEN
                && account.data.iter().all(|byte| *byte == 0)
        }
        Some(_) => false,
    }
}

fn gate(gates: &mut Vec<DevnetGate>, name: &str, passed: bool, evidence: impl Into<String>) {
    gates.push(DevnetGate {
        name: name.to_owned(),
        passed,
        evidence: evidence.into(),
    });
}

fn inspect_with_policy(
    workspace_root: &Path,
    config: &DevnetConfig,
    policy: ClusterPolicy,
) -> Result<Profile23DevnetReadiness> {
    let mut gates = Vec::new();
    let rpc_origin = rpc_origin(&config.rpc_url).ok();
    gate(
        &mut gates,
        "explicit_https_rpc",
        rpc_origin.is_some(),
        format!("redacted_origin={rpc_origin:?}"),
    );
    let rpc = Rpc::new(config.rpc_url.clone())?;
    let observed_genesis = rpc.genesis_hash().ok();
    gate(
        &mut gates,
        "exact_cluster_genesis",
        observed_genesis.as_deref() == Some(policy.expected_genesis_hash()),
        format!(
            "network={}, observed={observed_genesis:?}, expected={}",
            policy.network(),
            policy.expected_genesis_hash()
        ),
    );

    let payer = secure_keypair(&config.payer_keypair).ok();
    let program = secure_keypair(&config.program_keypair).ok();
    let pool = secure_keypair(&config.pool_keypair).ok();
    let proof_account = secure_keypair(&config.proof_account_keypair).ok();
    let replay_probe = config
        .replay_probe_keypair
        .as_ref()
        .and_then(|path| secure_keypair(path).ok());
    let upgrade_authority = config
        .upgrade_authority_keypair
        .as_ref()
        .and_then(|path| secure_keypair(path).ok());
    let deployment_buffer = config
        .deployment_buffer_keypair
        .as_ref()
        .and_then(|path| secure_keypair(path).ok());
    gate(
        &mut gates,
        "payer_keypair_secure",
        payer.is_some(),
        "explicit secure keypair",
    );
    gate(
        &mut gates,
        "program_keypair_secure",
        program.is_some(),
        "explicit secure keypair",
    );
    gate(
        &mut gates,
        "pool_keypair_secure",
        pool.is_some(),
        "explicit secure keypair",
    );
    gate(
        &mut gates,
        "proof_account_keypair_secure",
        proof_account.is_some(),
        "explicit secure keypair",
    );
    let runtime_program_id = program.as_ref().map(Signer::pubkey);
    gate(
        &mut gates,
        "runtime_program_id_from_explicit_program_keypair",
        runtime_program_id.is_some(),
        format!("runtime_program_id={runtime_program_id:?}"),
    );
    let replay_probe_ready = replay_probe.is_some()
        || (!policy.requires_explicit_recovery_signers() && config.replay_probe_keypair.is_none());
    gate(
        &mut gates,
        "replay_probe_keypair_secure_or_devnet_ephemeral_fallback",
        replay_probe_ready,
        format!(
            "explicit={}, pubkey={:?}, devnet_ephemeral_fallback={}",
            config.replay_probe_keypair.is_some(),
            replay_probe.as_ref().map(Signer::pubkey),
            config.replay_probe_keypair.is_none(),
        ),
    );
    let expected_upgrade_authority = upgrade_authority
        .as_ref()
        .map(Signer::pubkey)
        .or_else(|| payer.as_ref().map(Signer::pubkey));
    let upgrade_authority_ready = upgrade_authority.is_some()
        || (!policy.requires_explicit_recovery_signers()
            && config.upgrade_authority_keypair.is_none()
            && payer.is_some());
    gate(
        &mut gates,
        "upgrade_authority_secure_and_policy_compliant",
        upgrade_authority_ready,
        format!(
            "explicit={}, expected={expected_upgrade_authority:?}, mainnet_required={}",
            config.upgrade_authority_keypair.is_some(),
            policy.requires_explicit_recovery_signers(),
        ),
    );
    let deployment_buffer_ready = deployment_buffer.is_some()
        || (!policy.requires_explicit_recovery_signers()
            && config.deployment_buffer_keypair.is_none());
    gate(
        &mut gates,
        "deployment_buffer_secure_and_policy_compliant",
        deployment_buffer_ready,
        format!(
            "explicit={}, pubkey={:?}, mainnet_required={}",
            config.deployment_buffer_keypair.is_some(),
            deployment_buffer.as_ref().map(Signer::pubkey),
            policy.requires_explicit_recovery_signers(),
        ),
    );
    gate(
        &mut gates,
        "direct_tpu_loader_policy",
        config.use_tpu_client || !policy.requires_explicit_recovery_signers(),
        format!(
            "use_tpu_client={}, mainnet_required={}",
            config.use_tpu_client,
            policy.requires_explicit_recovery_signers(),
        ),
    );
    let distinct_keys = payer
        .as_ref()
        .zip(program.as_ref())
        .zip(pool.as_ref())
        .zip(proof_account.as_ref())
        .is_some_and(|(((payer, program), pool), proof_account)| {
            let mut keys = vec![
                payer.pubkey(),
                program.pubkey(),
                pool.pubkey(),
                proof_account.pubkey(),
            ];
            if let Some(replay_probe) = replay_probe.as_ref() {
                keys.push(replay_probe.pubkey());
            }
            if let Some(upgrade_authority) = upgrade_authority.as_ref() {
                keys.push(upgrade_authority.pubkey());
            }
            if let Some(deployment_buffer) = deployment_buffer.as_ref() {
                keys.push(deployment_buffer.pubkey());
            }
            (0..keys.len())
                .all(|left| (left + 1..keys.len()).all(|right| keys[left] != keys[right]))
        });
    gate(
        &mut gates,
        "all_explicit_signer_roles_distinct",
        distinct_keys,
        "all explicit signer identities are pairwise distinct",
    );

    let release_bytes = exact_regular_file(&config.release).ok();
    let release_sha = release_bytes.as_deref().map(sha256);
    let release = release_bytes
        .as_deref()
        .and_then(|bytes| serde_json::from_slice::<Value>(bytes).ok());
    let release_gates = release.as_ref().and_then(|value| value["gates"].as_array());
    let release_green_gate_count = release
        .as_ref()
        .and_then(release_certificate_green_gate_count);
    let release_green = release_green_gate_count.is_some();
    gate(
        &mut gates,
        "release_certificate_nonempty_all_declared_gates_green",
        release_green,
        format!(
            "gate_count={:?}, green_gate_count={release_green_gate_count:?}, released={release_green}",
            release_gates.map(Vec::len),
        ),
    );
    let live_release_evaluation = crate::profile23_release::evaluate_existing(workspace_root);
    let live_release_error = live_release_evaluation
        .as_ref()
        .err()
        .map(|error| format!("{error:#}"));
    let release_matches_live = release
        .as_ref()
        .zip(live_release_evaluation.as_ref().ok())
        .is_some_and(|(release, live)| {
            release_matches_live_evaluation(release, live).unwrap_or(false)
        });
    gate(
        &mut gates,
        "release_certificate_matches_live_read_only_evaluation",
        release_matches_live,
        format!("error={live_release_error:?}"),
    );
    let source_exact = release
        .as_ref()
        .is_some_and(|release| release_artifacts_exact(release, workspace_root).is_ok());
    gate(
        &mut gates,
        "release_source_hashes_exact",
        source_exact,
        "all release-pinned source artifacts rehashed",
    );

    let proof = exact_regular_file(&config.proof).ok();
    let sbf = exact_regular_file(&config.sbf).ok();
    let statement_bytes = exact_regular_file(&config.statement).ok();
    let proof_sha = proof.as_deref().map(sha256);
    let sbf_sha = sbf.as_deref().map(sha256);
    let statement_sha = statement_bytes.as_deref().map(sha256);
    let release_instance_validation = match (
        release.as_ref(),
        proof.as_deref(),
        statement_bytes.as_deref(),
    ) {
        (Some(release), Some(proof), Some(statement_bytes)) => validate_release_instance(
            release,
            workspace_root,
            &config.proof,
            proof,
            &config.statement,
            statement_bytes,
        ),
        _ => Err(anyhow!(
            "release certificate, proof, or statement sidecar unavailable"
        )),
    };
    let release_instance_error = release_instance_validation
        .as_ref()
        .err()
        .map(|error| format!("{error:#}"));
    let release_sbf_exact = release.as_ref().is_some_and(|release| {
        release["default_production_sbf"]["bytes"].as_u64()
            == sbf.as_ref().map(|bytes| bytes.len() as u64)
            && release["default_production_sbf"]["sha256"].as_str() == sbf_sha.as_deref()
    });
    gate(
        &mut gates,
        "explicit_proof_matches_release_instance",
        release_instance_validation
            .as_ref()
            .is_ok_and(|validation| validation.proof_identity_exact),
        release_instance_validation.as_ref().map_or_else(
            |_| format!("error={release_instance_error:?}, sha256={proof_sha:?}"),
            |validation| {
                format!(
                    "path={}, bytes={:?}, sha256={}",
                    validation.actual_proof_path,
                    proof.as_ref().map(Vec::len),
                    validation.actual_proof_sha256
                )
            },
        ),
    );
    gate(
        &mut gates,
        "explicit_statement_matches_release_instance",
        release_instance_validation
            .as_ref()
            .is_ok_and(|validation| validation.statement_identity_exact),
        release_instance_validation.as_ref().map_or_else(
            |_| format!("error={release_instance_error:?}, sha256={statement_sha:?}"),
            |validation| {
                format!(
                    "path={}, bytes={:?}, sha256={}, pool={}, sequence={}, digest={}",
                    validation.actual_statement_path,
                    statement_bytes.as_ref().map(Vec::len),
                    validation.actual_statement_sha256,
                    profile23_hex(&validation.statement.pool),
                    validation.statement.sequence,
                    canonical_profile23_public_input_digest(&validation.statement)
                        .unwrap_or_else(|_| "unavailable".to_owned())
                )
            },
        ),
    );
    gate(
        &mut gates,
        "release_instance_selector_is_live_least_good",
        release_instance_validation
            .as_ref()
            .is_ok_and(|validation| validation.selector_binding_exact),
        release_instance_validation.as_ref().map_or_else(
            |_| format!("error={release_instance_error:?}"),
            |validation| {
                format!(
                    "candidates={}, serialized={:?}, least={:?}, branches={}",
                    validation.instance.selector_candidates,
                    validation.instance.serialized_selector,
                    validation.instance.least_good_selector,
                    validation.instance.good23_branches.len()
                )
            },
        ),
    );
    gate(
        &mut gates,
        "release_instance_good23_fingerprint_matches_live_code",
        release_instance_validation
            .as_ref()
            .is_ok_and(|validation| validation.good23_fingerprint_exact),
        release_instance_validation.as_ref().map_or_else(
            |_| format!("error={release_instance_error:?}"),
            |validation| {
                format!(
                    "release={}, live={}",
                    validation.instance.good23_definition_fingerprint,
                    live_good23_definition_fingerprint()
                )
            },
        ),
    );
    gate(
        &mut gates,
        "release_instance_declares_production_host_verification_green",
        release_instance_validation
            .as_ref()
            .is_ok_and(|validation| validation.declared_host_verification_green),
        release_instance_validation.as_ref().map_or_else(
            |_| format!("error={release_instance_error:?}"),
            |validation| {
                format!(
                    "declared={}",
                    validation.instance.production_host_verification_green
                )
            },
        ),
    );
    gate(
        &mut gates,
        "production_host_verifies_exact_proof_and_statement",
        release_instance_validation
            .as_ref()
            .is_ok_and(|validation| validation.host_verification_green),
        release_instance_validation.as_ref().map_or_else(
            |_| format!("error={release_instance_error:?}"),
            |validation| format!("error={:?}", validation.host_verification_error),
        ),
    );
    gate(
        &mut gates,
        "explicit_sbf_matches_release",
        release_sbf_exact,
        format!("sha256={sbf_sha:?}"),
    );
    gate(
        &mut gates,
        "program_max_len_explicit_and_sufficient",
        sbf.as_ref()
            .is_some_and(|bytes| config.program_max_len >= bytes.len()),
        format!(
            "max_len={}, sbf_len={:?}",
            config.program_max_len,
            sbf.as_ref().map(Vec::len)
        ),
    );

    let statement = release_instance_validation
        .as_ref()
        .ok()
        .map(|validation| &validation.statement);
    let pool_pubkey = pool.as_ref().map(Signer::pubkey);
    let sidecar_valid = statement
        .is_some_and(|statement| Some(Pubkey::new_from_array(statement.pool)) == pool_pubkey);
    gate(
        &mut gates,
        "fresh_pool_known_before_proof_and_release",
        sidecar_valid,
        format!("pool_pubkey={pool_pubkey:?}, sidecar_sha256={statement_sha:?}"),
    );

    let program_already_deployed = runtime_program_id
        .and_then(|program_id| rpc.account(&program_id).ok())
        .map(|value| value.is_some());
    let program_ready = match (
        runtime_program_id,
        program_already_deployed,
        sbf.as_ref(),
        expected_upgrade_authority,
    ) {
        (Some(_), Some(false), Some(_), Some(_)) => true,
        (Some(program_id), Some(true), Some(sbf), Some(expected_upgrade_authority)) => {
            deployed_program_exact(
                &rpc,
                &program_id,
                sbf,
                config.program_max_len,
                &expected_upgrade_authority,
            )
            .is_ok_and(|snapshot| snapshot.is_some())
        }
        _ => false,
    };
    gate(
        &mut gates,
        "program_absent_or_exact_release_deployment",
        program_ready,
        format!("already_deployed={program_already_deployed:?}"),
    );

    let pool_absent = pool_pubkey
        .and_then(|key| rpc.account(&key).ok())
        .is_some_and(|account| account.is_none());
    let resume_validation = if config.resume_in_progress {
        Some(
            match (
                payer.as_ref(),
                pool.as_ref(),
                proof_account.as_ref(),
                config.resume_pool_create_signature.as_ref(),
                statement,
                proof.as_ref(),
            ) {
                (
                    Some(payer),
                    Some(pool),
                    Some(proof_account),
                    Some(pool_create_signature),
                    Some(statement),
                    Some(proof),
                ) => {
                    let public = statement_public_inputs(statement);
                    recover_resume_state(
                        &rpc,
                        &runtime_program_id.context("runtime program id unavailable")?,
                        payer,
                        pool,
                        proof_account,
                        pool_create_signature,
                        config.resume_pool_init_signature.as_ref(),
                        config.resume_proof_create_signature.as_ref(),
                        statement.sequence,
                        public.current_anchor,
                        proof.len(),
                    )
                    .map(|state| state.checkpoint)
                }
                _ => Err(anyhow!("resume inputs unavailable")),
            },
        )
    } else {
        None
    };
    let resume_error = resume_validation
        .as_ref()
        .and_then(|result| result.as_ref().err())
        .map(|error| format!("{error:#}"));
    let pool_ready = if config.resume_in_progress {
        resume_validation
            .as_ref()
            .is_some_and(|result| result.is_ok())
    } else {
        pool_absent
    };
    let proof_account_pubkey = proof_account.as_ref().map(Signer::pubkey);
    let proof_account_absent = proof_account_pubkey
        .and_then(|key| rpc.account(&key).ok())
        .is_some_and(|account| account.is_none());
    let proof_account_ready = if config.resume_in_progress {
        resume_validation
            .as_ref()
            .is_some_and(|result| result.is_ok())
    } else {
        proof_account_absent
    };
    gate(
        &mut gates,
        "fresh_pool_account_absent_or_exact_explicit_resume",
        pool_ready,
        format!(
            "pool={pool_pubkey:?}, resume={}, checkpoint={:?}, resume_error={resume_error:?}",
            config.resume_in_progress,
            resume_validation
                .as_ref()
                .and_then(|result| result.as_ref().ok())
                .map(|checkpoint| checkpoint.label()),
        ),
    );
    gate(
        &mut gates,
        "fresh_proof_account_absent_or_exact_explicit_resume",
        proof_account_ready,
        format!(
            "proof_account={proof_account_pubkey:?}, resume={}, resume_error={resume_error:?}",
            config.resume_in_progress
        ),
    );

    let nullifier_address = statement
        .map(statement_public_inputs)
        .zip(runtime_program_id)
        .map(|(public, program_id)| atomic_nullifier_address(&program_id, &public.nullifier).0);
    let nullifier_state = nullifier_address
        .and_then(|address| rpc.account(&address).ok())
        .flatten();
    let nullifier_ready = nullifier_address.is_some()
        && runtime_program_id
            .is_some_and(|program_id| nullifier_compatible(nullifier_state.as_ref(), &program_id));
    gate(
        &mut gates,
        "canonical_nullifier_absent_or_prefunded_compatible",
        nullifier_ready,
        format!(
            "address={nullifier_address:?}, observed={}",
            nullifier_state.is_some()
        ),
    );

    let solana_cli_ok = fs::symlink_metadata(&config.solana_cli).is_ok_and(|metadata| {
        metadata.file_type().is_file()
            && !metadata.file_type().is_symlink()
            && metadata.permissions().mode() & 0o111 != 0
    });
    gate(
        &mut gates,
        "explicit_solana_cli_executable",
        solana_cli_ok,
        format!("path={}", config.solana_cli.display()),
    );
    gate(
        &mut gates,
        "evidence_path_fresh_or_exact_explicit_resume_marker",
        (!config.resume_in_progress && !config.evidence.exists())
            || (config.resume_in_progress && exact_in_progress_evidence_marker(&config.evidence)),
        format!(
            "path={}, resume={}",
            config.evidence.display(),
            config.resume_in_progress
        ),
    );

    let mut rent_budget = DevnetRentBudget {
        fee_reserve_lamports: config.fee_reserve_lamports,
        ..DevnetRentBudget::default()
    };
    if let (Some(payer), Some(proof), Some(sbf)) = (payer.as_ref(), proof.as_ref(), sbf.as_ref()) {
        rent_budget.program_buffer_lamports = rpc
            .rent(BUFFER_METADATA_BYTES + config.program_max_len)
            .ok();
        rent_budget.programdata_lamports = rpc
            .rent(PROGRAMDATA_METADATA_BYTES + config.program_max_len)
            .ok();
        rent_budget.program_account_lamports = rpc.rent(PROGRAM_ACCOUNT_BYTES).ok();
        rent_budget.pool_account_lamports = rpc.rent(ATOMIC_POOL_STATE_LEN).ok();
        rent_budget.proof_account_lamports = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len()).ok();
        rent_budget.nullifier_account_lamports = rpc.rent(ATOMIC_NULLIFIER_MARKER_LEN).ok();
        rent_budget.payer_balance_lamports = rpc.balance(&payer.pubkey()).ok();
        let setup = rent_budget
            .pool_account_lamports
            .zip(rent_budget.proof_account_lamports)
            .and_then(|(pool, proof)| pool.checked_add(proof))
            .and_then(|sum| {
                rent_budget
                    .nullifier_account_lamports
                    .and_then(|marker| sum.checked_add(marker))
            })
            .and_then(|sum| sum.checked_add(config.fee_reserve_lamports));
        let fresh = rent_budget
            .program_buffer_lamports
            .zip(rent_budget.programdata_lamports)
            // Loader-v3 drains the temporary buffer back to the payer before
            // creating ProgramData, so one rent deposit funds both in turn.
            .map(|(buffer, data)| buffer.max(data))
            .and_then(|sum| {
                rent_budget
                    .program_account_lamports
                    .and_then(|program| sum.checked_add(program))
            })
            .and_then(|sum| setup.and_then(|setup| sum.checked_add(setup)));
        rent_budget.conservative_required_lamports = match program_already_deployed {
            Some(true) => setup,
            Some(false) => fresh,
            None => None,
        };
        rent_budget.surplus_lamports = rent_budget
            .payer_balance_lamports
            .zip(rent_budget.conservative_required_lamports)
            .map(|(balance, required)| i128::from(balance) - i128::from(required));
        let _ = sbf;
    }
    let funded = rent_budget
        .surplus_lamports
        .is_some_and(|surplus| surplus >= 0);
    gate(
        &mut gates,
        "payer_covers_conservative_rent_and_fees",
        funded,
        format!(
            "balance={:?}, required={:?}, surplus={:?}",
            rent_budget.payer_balance_lamports,
            rent_budget.conservative_required_lamports,
            rent_budget.surplus_lamports
        ),
    );

    let blockers = gates
        .iter()
        .filter(|gate| !gate.passed)
        .map(|gate| gate.name.clone())
        .collect::<Vec<_>>();
    Ok(Profile23DevnetReadiness {
        artifact: "profile23_devnet_readiness",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        mode: "read_only",
        mutations_performed: false,
        ready: blockers.is_empty(),
        expected_genesis_hash: policy.expected_genesis_hash(),
        observed_genesis_hash: observed_genesis,
        rpc_origin_redacted: rpc_origin,
        program_id: runtime_program_id
            .map(|program_id| program_id.to_string())
            .unwrap_or_else(|| "unavailable".to_owned()),
        payer_pubkey: payer.as_ref().map(|key| key.pubkey().to_string()),
        pool_pubkey: pool_pubkey.map(|key| key.to_string()),
        proof_account_pubkey: proof_account_pubkey.map(|key| key.to_string()),
        proof_sha256: proof_sha,
        sbf_sha256: sbf_sha,
        release_sha256: release_sha,
        statement_sha256: statement_sha,
        nullifier_address: nullifier_address.map(|key| key.to_string()),
        program_already_deployed,
        rent_budget,
        gates,
        blockers,
        explicit_nonclaims: vec![
            "Readiness never signs, deploys, creates accounts, uploads proof bytes, or submits transactions.",
            "A devnet rehearsal is not mainnet-beta evidence.",
            "Proof upload/finalization and pool initialization are setup transactions, not the one-transaction verification/state-transition claim.",
        ],
    })
}

pub fn readiness(workspace_root: &Path, arguments: &[String]) -> Result<Profile23DevnetReadiness> {
    let config = parse_args(arguments, CommandMode::Readiness)?;
    inspect_with_policy(workspace_root, &config, ClusterPolicy::Devnet)
}

fn signed_transaction(
    payer: &Keypair,
    signers: &[&Keypair],
    instructions: &[Instruction],
    blockhash: Hash,
) -> Transaction {
    let mut all_signers = Vec::<&Keypair>::with_capacity(signers.len() + 1);
    all_signers.push(payer);
    for signer in signers {
        if signer.pubkey() != payer.pubkey() {
            all_signers.push(*signer);
        }
    }
    Transaction::new_signed_with_payer(instructions, Some(&payer.pubkey()), &all_signers, blockhash)
}

fn proof_instruction(
    program_id: &Pubkey,
    payer: Pubkey,
    proof_account: Pubkey,
    instruction: &AspisInstruction,
) -> Result<Instruction> {
    Ok(Instruction {
        program_id: *program_id,
        accounts: vec![
            AccountMeta::new(
                proof_account,
                matches!(instruction, AspisInstruction::InitProof { .. }),
            ),
            AccountMeta::new_readonly(payer, true),
        ],
        data: to_vec(instruction)?,
    })
}

fn create_account_transaction(
    rpc: &Rpc,
    program_id: &Pubkey,
    payer: &Keypair,
    account: &Keypair,
    lamports: u64,
    space: usize,
    label: &str,
) -> Result<TransactionEvidence> {
    let instruction = system_instruction::create_account(
        &payer.pubkey(),
        &account.pubkey(),
        lamports,
        space as u64,
        program_id,
    );
    let transaction =
        signed_transaction(payer, &[account], &[instruction], rpc.latest_blockhash()?);
    rpc.submit_transaction(&transaction, label)
}

fn create_and_init_proof_instructions(
    program_id: &Pubkey,
    payer: Pubkey,
    proof_account: Pubkey,
    proof_rent_lamports: u64,
    proof_len: usize,
) -> Result<Vec<Instruction>> {
    let total_len = u32::try_from(proof_len).context("proof length exceeds tag0 u32 encoding")?;
    let account_len = PROOF_ACCOUNT_HEADER_LEN
        .checked_add(proof_len)
        .context("proof account length overflow")?;
    let create = system_instruction::create_account(
        &payer,
        &proof_account,
        proof_rent_lamports,
        u64::try_from(account_len).context("proof account length exceeds u64")?,
        program_id,
    );
    let init = proof_instruction(
        program_id,
        payer,
        proof_account,
        &AspisInstruction::InitProof { total_len },
    )?;
    Ok(vec![
        ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
        create,
        init,
    ])
}

fn create_and_init_proof_transaction(
    program_id: &Pubkey,
    payer: &Keypair,
    proof_account: &Keypair,
    proof_rent_lamports: u64,
    proof_len: usize,
    blockhash: Hash,
) -> Result<Transaction> {
    let instructions = create_and_init_proof_instructions(
        program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        proof_rent_lamports,
        proof_len,
    )?;
    Ok(signed_transaction(
        payer,
        &[proof_account],
        &instructions,
        blockhash,
    ))
}

pub(crate) fn finalize_and_close_partial_proof_transaction(
    program_id: &Pubkey,
    payer: &Keypair,
    proof_account: &Keypair,
    blockhash: Hash,
) -> Result<Transaction> {
    let finalize = proof_instruction(
        program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let close = Instruction {
        program_id: *program_id,
        accounts: vec![
            AccountMeta::new(proof_account.pubkey(), true),
            AccountMeta::new(payer.pubkey(), true),
        ],
        data: to_vec(&AspisInstruction::CloseFinalizedProof)?,
    };
    Ok(signed_transaction(
        payer,
        &[proof_account],
        &[finalize, close],
        blockhash,
    ))
}

fn upload_proof_chunks(
    rpc: &Rpc,
    program_id: &Pubkey,
    payer: &Keypair,
    proof_account: &Keypair,
    proof: &[u8],
) -> Result<Vec<TransactionEvidence>> {
    let upload_chunks = proof
        .chunks(UPLOAD_CHUNK_BYTES)
        .enumerate()
        .collect::<Vec<_>>();
    let finality_windows = upload_chunks.len().div_ceil(UPLOAD_WINDOW_TRANSACTIONS);
    let mut evidence = Vec::with_capacity(upload_chunks.len());
    for (window_index, window) in upload_chunks.chunks(UPLOAD_WINDOW_TRANSACTIONS).enumerate() {
        eprintln!(
            "proof upload window {}/{}: submitting {} transaction(s)",
            window_index + 1,
            finality_windows,
            window.len()
        );
        let recent_blockhash = rpc.latest_blockhash_with_expiry()?;
        let mut pending = Vec::with_capacity(window.len());
        for &(index, chunk) in window {
            let upload = proof_instruction(
                program_id,
                payer.pubkey(),
                proof_account.pubkey(),
                &AspisInstruction::UploadChunk {
                    offset: (index * UPLOAD_CHUNK_BYTES) as u32,
                    chunk: chunk.to_vec(),
                },
            )?;
            let upload_tx = signed_transaction(payer, &[], &[upload], recent_blockhash.hash);
            let wire = bincode::serialize(&upload_tx)?;
            ensure!(
                wire.len() <= MAX_TRANSACTION_WIRE_BYTES,
                "upload transaction {index} is {} bytes, above the {}-byte packet cap",
                wire.len(),
                MAX_TRANSACTION_WIRE_BYTES
            );
            pending.push(rpc.submit_transaction_pending(
                &upload_tx,
                &format!("upload_proof_chunk_{index}"),
                UPLOAD_MAX_IDENTICAL_RETRIES,
            )?);
        }
        evidence
            .extend(rpc.wait_finalized_batch(pending, recent_blockhash.last_valid_block_height)?);
        eprintln!(
            "proof upload window {}/{} finalized",
            window_index + 1,
            finality_windows
        );
    }
    Ok(evidence)
}

fn extract_deploy_signature(stdout: &[u8]) -> Result<Signature> {
    if let Ok(value) = serde_json::from_slice::<Value>(stdout) {
        for key in ["signature", "transactionSignature"] {
            if let Some(value) = value[key].as_str() {
                return Signature::from_str(value).context("invalid deployment signature");
            }
        }
    }
    let text = std::str::from_utf8(stdout).context("deployment output was not UTF-8")?;
    for line in text.lines() {
        if let Some(value) = line.strip_prefix("Signature: ") {
            return Signature::from_str(value.trim()).context("invalid deployment signature");
        }
    }
    bail!("Solana CLI deployment output omitted a parseable signature")
}

fn deploy_cli_args(config: &DevnetConfig, policy: ClusterPolicy) -> Result<Vec<OsString>> {
    if policy == ClusterPolicy::MainnetBeta {
        ensure!(
            config.upgrade_authority_keypair.is_some(),
            "mainnet deploy requires --upgrade-authority-keypair"
        );
        ensure!(
            config.deployment_buffer_keypair.is_some(),
            "mainnet deploy requires --deployment-buffer-keypair"
        );
        ensure!(
            config.use_tpu_client,
            "mainnet deploy requires --use-tpu-client"
        );
    }
    let upgrade_authority = config
        .upgrade_authority_keypair
        .as_ref()
        .unwrap_or(&config.payer_keypair);
    let mut arguments = vec![
        OsString::from("--url"),
        config.rpc_url.clone().into(),
        OsString::from("--keypair"),
        config.payer_keypair.as_os_str().to_owned(),
        OsString::from("--output"),
        OsString::from("json"),
    ];
    if policy == ClusterPolicy::MainnetBeta {
        arguments.extend([OsString::from("--commitment"), OsString::from("finalized")]);
    }
    arguments.extend([
        OsString::from("program"),
        OsString::from("deploy"),
        config.sbf.as_os_str().to_owned(),
        OsString::from("--program-id"),
        config.program_keypair.as_os_str().to_owned(),
        OsString::from("--upgrade-authority"),
        upgrade_authority.as_os_str().to_owned(),
        OsString::from("--max-len"),
        config.program_max_len.to_string().into(),
    ]);
    if let Some(buffer) = config.deployment_buffer_keypair.as_ref() {
        arguments.extend([OsString::from("--buffer"), buffer.as_os_str().to_owned()]);
    }
    if config.use_tpu_client {
        arguments.push(OsString::from("--use-tpu-client"));
    }
    if policy == ClusterPolicy::MainnetBeta {
        arguments.extend([
            OsString::from("--max-sign-attempts"),
            OsString::from("1"),
            OsString::from("--with-compute-unit-price"),
            OsString::from("0"),
        ]);
    }
    Ok(arguments)
}

fn deploy_if_needed(
    rpc: &Rpc,
    program_id: &Pubkey,
    expected_upgrade_authority: &Pubkey,
    policy: ClusterPolicy,
    config: &DevnetConfig,
    sbf: &[u8],
) -> Result<Option<TransactionEvidence>> {
    if deployed_program_exact(
        rpc,
        program_id,
        sbf,
        config.program_max_len,
        expected_upgrade_authority,
    )?
    .is_some()
    {
        return Ok(None);
    }
    ensure!(
        rpc.account(program_id)?.is_none(),
        "program address exists but does not match the exact release"
    );
    let output = Command::new(&config.solana_cli)
        .args(deploy_cli_args(config, policy)?)
        .output()
        .context("run explicit Solana CLI deploy")?;
    ensure!(
        output.status.success(),
        "Solana CLI deploy failed with status {}",
        output.status
    );
    let signature = extract_deploy_signature(&output.stdout)?;
    let slot = rpc.wait_finalized(&signature)?;
    ensure!(
        deployed_program_exact(
            rpc,
            program_id,
            sbf,
            config.program_max_len,
            expected_upgrade_authority,
        )?
        .is_some(),
        "finalized deployed program did not match release bytes/max-len/authority"
    );
    let (wire_sha256, message_sha256) = rpc.transaction_wire_and_message_hash(&signature)?;
    Ok(Some(TransactionEvidence {
        label: "deploy_exact_release_sbf".to_owned(),
        signature: signature.to_string(),
        finalized_slot: slot,
        // The CLI owns construction, so both hashes are refetched from the
        // finalized transaction rather than inferred from its stdout.
        message_sha256,
        serialized_transaction_sha256: wire_sha256,
        compute_units_consumed: rpc.transaction_cu(&signature)?,
        identical_wire_retries: 0,
    }))
}

fn expected_proof_account(proof: &[u8], authority: Pubkey, finalized: bool) -> Vec<u8> {
    let mut expected = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof.len()];
    expected[..4].copy_from_slice(PROOF_MAGIC);
    expected[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
    if !finalized {
        expected[PROOF_AUTHORITY_OFFSET..PROOF_AUTHORITY_OFFSET + 32]
            .copy_from_slice(authority.as_ref());
    }
    expected[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(proof);
    expected
}

fn expected_nullifier_marker(pool: Pubkey, nullifier: [u8; 32]) -> Vec<u8> {
    let mut expected = vec![0u8; ATOMIC_NULLIFIER_MARKER_LEN];
    expected[..4].copy_from_slice(&ATOMIC_NULLIFIER_MAGIC);
    expected[4] = ATOMIC_NULLIFIER_VERSION;
    expected[8..40].copy_from_slice(pool.as_ref());
    expected[40..72].copy_from_slice(&nullifier);
    expected
}

fn exact_in_progress_evidence_marker(path: &Path) -> bool {
    let Ok(metadata) = fs::symlink_metadata(path) else {
        return false;
    };
    if !metadata.file_type().is_file()
        || metadata.file_type().is_symlink()
        || metadata.permissions().mode() & 0o022 != 0
    {
        return false;
    }
    let Ok(bytes) = fs::read(path) else {
        return false;
    };
    let Ok(value) = serde_json::from_slice::<Value>(&bytes) else {
        return false;
    };
    value.as_object().is_some_and(|object| object.len() == 4)
        && value["artifact"] == "profile23_devnet_finalized_rehearsal"
        && value["status"] == "in_progress_no_claim"
        && value["reserved_at_utc"].as_str().is_some()
        && value["warning"] == IN_PROGRESS_WARNING
}

fn zeroed_pool_account_exact(account: &RpcAccount, program_id: &Pubkey, pool_rent: u64) -> bool {
    account.lamports == pool_rent
        && account.owner == *program_id
        && !account.executable
        && account.data.len() == ATOMIC_POOL_STATE_LEN
        && account.data.iter().all(|byte| *byte == 0)
}

fn zeroed_proof_account_exact(
    account: &RpcAccount,
    program_id: &Pubkey,
    proof_rent: u64,
    proof_len: usize,
) -> bool {
    account.lamports == proof_rent
        && account.owner == *program_id
        && !account.executable
        && account.data.len() == PROOF_ACCOUNT_HEADER_LEN + proof_len
        && account.data.iter().all(|byte| *byte == 0)
}

fn resumed_proof_checkpoint(
    account: &RpcAccount,
    program_id: &Pubkey,
    proof_rent: u64,
    proof_len: usize,
    authority: Pubkey,
) -> Option<ResumeCheckpoint> {
    if zeroed_proof_account_exact(account, program_id, proof_rent, proof_len) {
        Some(ResumeCheckpoint::ProofAccountCreated)
    } else if account.lamports == proof_rent
        && account.owner == *program_id
        && !account.executable
        && account.data == expected_proof_account(&vec![0u8; proof_len], authority, false)
    {
        Some(ResumeCheckpoint::ProofInitialized)
    } else {
        None
    }
}

fn initialized_pool_account_exact(
    account: &RpcAccount,
    program_id: &Pubkey,
    pool_rent: u64,
    sequence: u64,
    anchor: [u8; 32],
) -> bool {
    let mut expected = vec![0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV1 { sequence, anchor }
        .encode(&mut expected)
        .is_ok()
        && account.lamports == pool_rent
        && account.owner == *program_id
        && !account.executable
        && account.data == expected
}

fn recover_exact_transaction_evidence(
    rpc: &Rpc,
    payer: &Keypair,
    signers: &[&Keypair],
    instructions: &[Instruction],
    signature: &Signature,
    label: &str,
) -> Result<TransactionEvidence> {
    let (slot, error, confirmation) = rpc
        .signature_status(signature)?
        .with_context(|| format!("resume {label} signature missing from history"))?;
    ensure!(error.is_none(), "resume {label} transaction failed");
    ensure!(
        confirmation == "finalized",
        "resume {label} transaction is not finalized"
    );
    let (wire, transaction) = rpc.transaction_wire(signature)?;
    ensure!(
        transaction.signatures.first() == Some(signature),
        "resume {label} signature is not the transaction identifier"
    );
    let VersionedMessage::Legacy(message) = &transaction.message else {
        bail!("resume {label} transaction is not legacy format");
    };
    let expected_transaction =
        signed_transaction(payer, signers, instructions, message.recent_blockhash);
    ensure!(
        wire == bincode::serialize(&expected_transaction)?,
        "resume {label} transaction is not byte-identical to the reconstructed transaction"
    );
    let message_sha256 = sha256(&bincode::serialize(&transaction.message)?);
    Ok(TransactionEvidence {
        label: label.to_owned(),
        signature: signature.to_string(),
        finalized_slot: slot,
        message_sha256,
        serialized_transaction_sha256: sha256(&wire),
        compute_units_consumed: rpc.transaction_cu(signature)?,
        identical_wire_retries: 0,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResumeCheckpoint {
    PoolCreated,
    /// Historical checkpoint produced by the old separate create-account
    /// transaction, before tag0 initialization.
    ProofAccountCreated,
    /// Current checkpoint produced by atomic create-account + tag0.
    ProofInitialized,
}

impl ResumeCheckpoint {
    fn label(self) -> &'static str {
        match self {
            Self::PoolCreated => "pool_created_zeroed",
            Self::ProofAccountCreated => "pool_initialized_proof_account_created_zeroed",
            Self::ProofInitialized => "pool_initialized_proof_account_tag0_initialized",
        }
    }
}

struct RecoveredResumeState {
    checkpoint: ResumeCheckpoint,
    pool: RpcAccount,
    proof_account: Option<RpcAccount>,
    setup_transactions: Vec<TransactionEvidence>,
}

#[allow(clippy::too_many_arguments)]
fn recover_resume_state(
    rpc: &Rpc,
    program_id: &Pubkey,
    payer: &Keypair,
    pool: &Keypair,
    proof_account: &Keypair,
    pool_create_signature: &Signature,
    pool_init_signature: Option<&Signature>,
    proof_create_signature: Option<&Signature>,
    sequence: u64,
    current_anchor: [u8; 32],
    proof_len: usize,
) -> Result<RecoveredResumeState> {
    let pool_rent = rpc.rent(ATOMIC_POOL_STATE_LEN)?;
    let proof_rent = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof_len)?;
    let pool_create = system_instruction::create_account(
        &payer.pubkey(),
        &pool.pubkey(),
        pool_rent,
        ATOMIC_POOL_STATE_LEN as u64,
        program_id,
    );
    let mut setup_transactions = vec![recover_exact_transaction_evidence(
        rpc,
        payer,
        &[pool],
        &[pool_create],
        pool_create_signature,
        "create_pool_account",
    )?];
    let pool_state = rpc
        .account(&pool.pubkey())?
        .context("resume pool account missing")?;

    let (checkpoint, proof_state) = match (pool_init_signature, proof_create_signature) {
        (None, None) => {
            ensure!(
                zeroed_pool_account_exact(&pool_state, program_id, pool_rent),
                "pool-created resume checkpoint has unexpected pool image"
            );
            ensure!(
                rpc.account(&proof_account.pubkey())?.is_none(),
                "pool-created resume checkpoint requires an absent proof account"
            );
            (ResumeCheckpoint::PoolCreated, None)
        }
        (Some(pool_init_signature), Some(proof_create_signature)) => {
            ensure!(
                initialized_pool_account_exact(
                    &pool_state,
                    program_id,
                    pool_rent,
                    sequence,
                    current_anchor,
                ),
                "proof-created resume checkpoint has unexpected initialized pool image"
            );
            let initialize_pool = Instruction {
                program_id: *program_id,
                accounts: vec![AccountMeta::new(pool.pubkey(), true)],
                data: to_vec(&AspisInstruction::InitializeAtomicPool {
                    sequence,
                    anchor: current_anchor,
                })?,
            };
            setup_transactions.push(recover_exact_transaction_evidence(
                rpc,
                payer,
                &[pool],
                &[initialize_pool],
                pool_init_signature,
                "tag63_initialize_pool",
            )?);
            let proof_create = system_instruction::create_account(
                &payer.pubkey(),
                &proof_account.pubkey(),
                proof_rent,
                (PROOF_ACCOUNT_HEADER_LEN + proof_len) as u64,
                program_id,
            );
            let proof_state = rpc
                .account(&proof_account.pubkey())?
                .context("proof-created resume checkpoint is missing proof account")?;
            let checkpoint = resumed_proof_checkpoint(
                &proof_state,
                program_id,
                proof_rent,
                proof_len,
                payer.pubkey(),
            )
            .context("proof-created resume checkpoint has unexpected proof account image")?;
            if checkpoint == ResumeCheckpoint::ProofAccountCreated {
                setup_transactions.push(recover_exact_transaction_evidence(
                    rpc,
                    payer,
                    &[proof_account],
                    &[proof_create],
                    proof_create_signature,
                    "create_proof_account",
                )?);
            } else {
                let create_and_init = create_and_init_proof_instructions(
                    program_id,
                    payer.pubkey(),
                    proof_account.pubkey(),
                    proof_rent,
                    proof_len,
                )?;
                setup_transactions.push(recover_exact_transaction_evidence(
                    rpc,
                    payer,
                    &[proof_account],
                    &create_and_init,
                    proof_create_signature,
                    "create_and_init_proof_account",
                )?);
            }
            (checkpoint, Some(proof_state))
        }
        _ => bail!("resume pool-init and proof-create signatures must be supplied together"),
    };
    ensure!(
        setup_transactions
            .windows(2)
            .all(|pair| pair[0].finalized_slot <= pair[1].finalized_slot),
        "recovered setup transaction slots are out of order"
    );
    Ok(RecoveredResumeState {
        checkpoint,
        pool: pool_state,
        proof_account: proof_state,
        setup_transactions,
    })
}

struct EvidenceReservation {
    file: fs::File,
    path: PathBuf,
}

impl EvidenceReservation {
    fn reserve(path: &Path, artifact: &'static str) -> Result<Self> {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(path)
            .with_context(|| format!("reserve evidence path {}", path.display()))?;
        let placeholder = json!({
            "artifact": artifact,
            "status": "in_progress_no_claim",
            "reserved_at_utc": chrono::Utc::now().to_rfc3339(),
            "warning": IN_PROGRESS_WARNING
        });
        let mut bytes = serde_json::to_vec_pretty(&placeholder)?;
        bytes.push(b'\n');
        file.write_all(&bytes)?;
        file.sync_all()?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    fn resume(path: &Path) -> Result<Self> {
        ensure!(
            exact_in_progress_evidence_marker(path),
            "resume evidence path is not the exact in-progress marker"
        );
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)
            .with_context(|| format!("open in-progress evidence {}", path.display()))?;
        Ok(Self {
            file,
            path: path.to_path_buf(),
        })
    }

    fn commit(self, value: &impl Serialize) -> Result<u32> {
        let mut bytes = serde_json::to_vec_pretty(value)?;
        bytes.push(b'\n');
        self.file.sync_all()?;
        let parent = self.path.parent().context("evidence path omitted parent")?;
        let name = self
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .context("evidence filename is not UTF-8")?;
        let temporary_path = parent.join(format!(".{name}.complete-{}", std::process::id()));
        let mut completed = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary_path)
            .with_context(|| format!("create completed evidence {}", temporary_path.display()))?;
        completed.write_all(&bytes)?;
        completed.sync_all()?;
        let mut permissions = completed.metadata()?.permissions();
        permissions.set_mode(0o444);
        fs::set_permissions(&temporary_path, permissions)?;
        fs::rename(&temporary_path, &self.path)?;
        fs::File::open(parent)?.sync_all()?;
        Ok(0o444)
    }
}

#[allow(clippy::too_many_lines)]
pub fn upload_smoke(arguments: &[String]) -> Result<Profile23DevnetUploadSmokeEvidence> {
    let config = parse_upload_smoke_args(arguments)?;
    ensure!(
        config.execute_interlock,
        "upload smoke requires --execute-devnet"
    );
    ensure!(
        config.acknowledgement.as_deref() == Some(UPLOAD_SMOKE_ACK),
        "upload smoke acknowledgement mismatch"
    );

    let rpc_origin_redacted = rpc_origin(&config.rpc_url)?;
    let rpc = Rpc::new(config.rpc_url.clone())?;
    ensure!(
        rpc.genesis_hash()? == DEVNET_GENESIS_HASH,
        "upload smoke requires the pinned devnet genesis"
    );
    let payer = secure_keypair(&config.payer_keypair)?;
    let proof_account = secure_keypair(&config.proof_account_keypair)?;
    let program_id = aspis_verifier::id();
    ensure!(
        payer.pubkey() != proof_account.pubkey(),
        "payer and proof-account keypairs must differ"
    );
    let sbf = exact_regular_file(&config.sbf)?;
    let proof = exact_regular_file(&config.proof)?;
    ensure!(!proof.is_empty(), "upload smoke proof must not be empty");
    ensure!(
        u32::try_from(proof.len()).is_ok(),
        "upload smoke proof exceeds u32 framing"
    );
    let upgradeable_program_before = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.program_max_len,
        &payer.pubkey(),
    )?
    .context("deployed program does not match the supplied SBF/max-len/authority")?;
    ensure!(
        rpc.account(&proof_account.pubkey())?.is_none(),
        "upload-smoke proof account is not fresh"
    );
    let proof_rent = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len())?;
    let required_balance = proof_rent
        .checked_add(config.fee_reserve_lamports)
        .context("upload-smoke balance requirement overflow")?;
    ensure!(
        rpc.balance(&payer.pubkey())? >= required_balance,
        "payer balance is below proof rent plus fee reserve"
    );

    let evidence_reservation =
        EvidenceReservation::reserve(&config.evidence, "profile23_devnet_upload_smoke")?;
    ensure!(
        rpc.account(&proof_account.pubkey())?.is_none(),
        "upload-smoke proof account ceased to be fresh"
    );
    let total_started = Instant::now();
    let mut setup_transactions = Vec::new();
    setup_transactions.push(create_account_transaction(
        &rpc,
        &program_id,
        &payer,
        &proof_account,
        proof_rent,
        PROOF_ACCOUNT_HEADER_LEN + proof.len(),
        "create_proof_account",
    )?);

    let init = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::InitProof {
            total_len: proof.len() as u32,
        },
    )?;
    let init_tx = signed_transaction(
        &payer,
        &[&proof_account],
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            init,
        ],
        rpc.latest_blockhash()?,
    );
    let init_simulation = rpc.simulate_exact(&bincode::serialize(&init_tx)?)?;
    ensure!(
        init_simulation.error.is_none()
            && init_simulation
                .units
                .is_some_and(|units| units < u64::from(CU_LIMIT)),
        "upload-smoke InitProof simulation failed or exceeded its CU limit"
    );
    setup_transactions.push(rpc.submit_transaction(&init_tx, "init_proof_account")?);

    let upload_started = Instant::now();
    let upload_transactions =
        upload_proof_chunks(&rpc, &program_id, &payer, &proof_account, &proof)?;
    let upload_wall_milliseconds = u64::try_from(upload_started.elapsed().as_millis())
        .context("upload-smoke duration overflow")?;
    let upload_first_finalized_slot = upload_transactions
        .iter()
        .map(|transaction| transaction.finalized_slot)
        .min()
        .context("upload smoke produced no upload transaction")?;
    let upload_last_finalized_slot = upload_transactions
        .iter()
        .map(|transaction| transaction.finalized_slot)
        .max()
        .context("upload smoke produced no upload transaction")?;
    let upload_identical_wire_retries = upload_transactions
        .iter()
        .map(|transaction| u64::from(transaction.identical_wire_retries))
        .sum();
    let proof_upload_transaction_count = upload_transactions.len();
    setup_transactions.extend(upload_transactions);

    let uploaded = rpc
        .account(&proof_account.pubkey())?
        .context("uploaded proof account missing")?;
    ensure!(
        uploaded.data == expected_proof_account(&proof, payer.pubkey(), false),
        "full pre-finalization proof account bytes differ"
    );
    let finalize = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let finalize_tx = signed_transaction(&payer, &[], &[finalize], rpc.latest_blockhash()?);
    setup_transactions.push(rpc.submit_transaction(&finalize_tx, "tag62_finalize_proof")?);
    let finalized_proof = rpc
        .account(&proof_account.pubkey())?
        .context("finalized proof account missing")?;
    ensure!(
        finalized_proof.data == expected_proof_account(&proof, payer.pubkey(), true),
        "finalized proof bytes/header drift"
    );

    let forbidden_upload = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![proof[0] ^ 1],
        },
    )?;
    let forbidden_upload_tx =
        signed_transaction(&payer, &[], &[forbidden_upload], rpc.latest_blockhash()?);
    let post_finalize_upload_error = rpc
        .simulate_exact(&bincode::serialize(&forbidden_upload_tx)?)?
        .error
        .context("sealed proof account accepted a forbidden upload simulation")?;
    let post_finalize_upload_rejected =
        post_finalize_upload_error == invalid_account_data_simulation_error(0);
    let second_finalize = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let second_finalize_tx =
        signed_transaction(&payer, &[], &[second_finalize], rpc.latest_blockhash()?);
    let post_finalize_second_finalize_error = rpc
        .simulate_exact(&bincode::serialize(&second_finalize_tx)?)?
        .error
        .context("sealed proof account accepted a second-finalize simulation")?;
    let post_finalize_second_finalize_rejected =
        post_finalize_second_finalize_error == invalid_account_data_simulation_error(0);
    ensure!(
        post_finalize_upload_rejected && post_finalize_second_finalize_rejected,
        "sealed proof account returned an unexpected rejection: upload={post_finalize_upload_error}, second_finalize={post_finalize_second_finalize_error}"
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.as_ref() == Some(&finalized_proof),
        "negative simulations changed the sealed proof account"
    );

    let upgradeable_program_after = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.program_max_len,
        &payer.pubkey(),
    )?
    .context("exact deployed program missing after upload smoke")?;
    let upgradeable_program_continuity =
        upgradeable_program_after.continuity_from(&upgradeable_program_before);
    ensure!(
        upgradeable_program_continuity.all_unchanged(),
        "deployed program changed during upload smoke"
    );

    let mut evidence = Profile23DevnetUploadSmokeEvidence {
        artifact: "profile23_devnet_upload_smoke",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network: "devnet",
        genesis_hash: DEVNET_GENESIS_HASH.to_owned(),
        rpc_origin_redacted,
        program_id: program_id.to_string(),
        payer_pubkey: payer.pubkey().to_string(),
        proof_account_pubkey: proof_account.pubkey().to_string(),
        sbf_path: config.sbf.display().to_string(),
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        proof_path: config.proof.display().to_string(),
        proof_bytes: proof.len(),
        proof_sha256: sha256(&proof),
        program_max_len: config.program_max_len,
        upgradeable_program_before: upgradeable_program_before.evidence(),
        upgradeable_program_after: upgradeable_program_after.evidence(),
        upgradeable_program_continuity,
        proof_upload_chunk_bytes: UPLOAD_CHUNK_BYTES,
        proof_upload_window_transactions: UPLOAD_WINDOW_TRANSACTIONS,
        proof_upload_transaction_count,
        proof_upload_finality_windows: proof_upload_transaction_count
            .div_ceil(UPLOAD_WINDOW_TRANSACTIONS),
        upload_wall_milliseconds,
        total_wall_milliseconds: u64::try_from(total_started.elapsed().as_millis())
            .context("upload-smoke total duration overflow")?,
        upload_first_finalized_slot,
        upload_last_finalized_slot,
        upload_identical_wire_retries,
        setup_transactions,
        proof_account: finalized_proof.evidence(proof_account.pubkey()),
        full_unsealed_image_verified: true,
        sealed_image_verified: true,
        post_finalize_upload_rejected,
        post_finalize_upload_error,
        post_finalize_second_finalize_rejected,
        post_finalize_second_finalize_error,
        evidence_path: config.evidence.display().to_string(),
        evidence_file_mode: 0o444,
    };
    evidence.evidence_file_mode = evidence_reservation.commit(&evidence)?;
    Ok(evidence)
}

pub fn execute(workspace_root: &Path, arguments: &[String]) -> Result<Profile23DevnetEvidence> {
    let config = parse_args(arguments, CommandMode::Execute)?;
    validate_execution_policy(&config, ClusterPolicy::Devnet)?;
    execute_with_policy(workspace_root, config, ClusterPolicy::Devnet)
}

pub fn execute_mainnet(
    workspace_root: &Path,
    arguments: &[String],
) -> Result<Profile23DevnetEvidence> {
    let config = parse_args(arguments, CommandMode::ExecuteMainnet)?;
    validate_execution_policy(&config, ClusterPolicy::MainnetBeta)?;
    execute_with_policy(workspace_root, config, ClusterPolicy::MainnetBeta)
}

fn execute_with_policy(
    workspace_root: &Path,
    config: DevnetConfig,
    policy: ClusterPolicy,
) -> Result<Profile23DevnetEvidence> {
    let readiness = inspect_with_policy(workspace_root, &config, policy)?;
    ensure!(
        readiness.ready,
        "devnet readiness blocked: {}",
        readiness.blockers.join(", ")
    );

    let rpc = Rpc::new(config.rpc_url.clone())?;
    ensure!(
        rpc.genesis_hash()? == policy.expected_genesis_hash(),
        "{} genesis changed after readiness",
        policy.network()
    );
    let payer = secure_keypair(&config.payer_keypair)?;
    let program = secure_keypair(&config.program_keypair)?;
    let pool = secure_keypair(&config.pool_keypair)?;
    let proof_account = secure_keypair(&config.proof_account_keypair)?;
    let replay_probe = match config.replay_probe_keypair.as_ref() {
        Some(path) => secure_keypair(path)?,
        None => Keypair::new(),
    };
    let expected_upgrade_authority = match config.upgrade_authority_keypair.as_ref() {
        Some(path) => secure_keypair(path)?.pubkey(),
        None => payer.pubkey(),
    };
    let deployment_buffer = config
        .deployment_buffer_keypair
        .as_ref()
        .map(|path| secure_keypair(path))
        .transpose()?;
    let program_id = program.pubkey();
    let mut signer_keys = vec![
        payer.pubkey(),
        program.pubkey(),
        pool.pubkey(),
        proof_account.pubkey(),
        replay_probe.pubkey(),
    ];
    if config.upgrade_authority_keypair.is_some() {
        signer_keys.push(expected_upgrade_authority);
    }
    if let Some(buffer) = deployment_buffer.as_ref() {
        signer_keys.push(buffer.pubkey());
    }
    ensure!((0..signer_keys.len()).all(|left| {
        (left + 1..signer_keys.len()).all(|right| signer_keys[left] != signer_keys[right])
    }));
    let release_bytes = exact_regular_file(&config.release)?;
    let release: Value = serde_json::from_slice(&release_bytes)?;
    let release_gate_count = release_certificate_green_gate_count(&release)
        .context("release certificate is not nonempty/all-declared-green")?;
    let live_release = crate::profile23_release::evaluate_existing(workspace_root)
        .context("read-only live release re-evaluation before first write")?;
    ensure!(
        release_matches_live_evaluation(&release, &live_release)?,
        "release certificate ceased to match the complete live release evaluation"
    );
    release_artifacts_exact(&release, workspace_root)?;
    let sbf = exact_regular_file(&config.sbf)?;
    let proof = exact_regular_file(&config.proof)?;
    let release_proof_sha256 = sha256(&proof);
    let statement_bytes = exact_regular_file(&config.statement)?;
    let sbf_sha256 = sha256(&sbf);
    ensure!(
        release["default_production_sbf"]["bytes"].as_u64() == Some(sbf.len() as u64)
            && release["default_production_sbf"]["sha256"].as_str() == Some(sbf_sha256.as_str()),
        "explicit SBF ceased to match release certificate"
    );
    let release_instance = validate_release_instance(
        &release,
        workspace_root,
        &config.proof,
        &proof,
        &config.statement,
        &statement_bytes,
    )?;
    ensure!(
        release_instance.all_green(),
        "release-instance recheck failed before first write: proof_identity={}, statement_identity={}, selector_binding={}, good23_fingerprint={}, declared_host={}, direct_host={}, host_error={:?}",
        release_instance.proof_identity_exact,
        release_instance.statement_identity_exact,
        release_instance.selector_binding_exact,
        release_instance.good23_fingerprint_exact,
        release_instance.declared_host_verification_green,
        release_instance.host_verification_green,
        release_instance.host_verification_error
    );
    let canonical_public_input_digest =
        canonical_profile23_public_input_digest(&release_instance.statement)?;
    let serialized_selector = release_instance
        .instance
        .serialized_selector
        .context("green release instance omitted serialized selector")?;
    let least_good_selector = release_instance
        .instance
        .least_good_selector
        .context("green release instance omitted least-Good selector")?;
    let good23_definition_fingerprint = release_instance
        .instance
        .good23_definition_fingerprint
        .clone();
    let release_instance_proof_identity_exact = release_instance.proof_identity_exact;
    let release_instance_statement_identity_exact = release_instance.statement_identity_exact;
    let release_instance_selector_binding_exact = release_instance.selector_binding_exact;
    let release_instance_good23_fingerprint_exact = release_instance.good23_fingerprint_exact;
    let release_instance_declared_host_verification_green =
        release_instance.declared_host_verification_green;
    let production_host_verification_green = release_instance.host_verification_green;
    let statement = release_instance.statement;
    let public = statement_public_inputs(&statement);
    ensure!(Pubkey::new_from_array(statement.pool) == pool.pubkey());

    if rpc.account(&program_id)?.is_some() {
        ensure!(
            deployed_program_exact(
                &rpc,
                &program_id,
                &sbf,
                config.program_max_len,
                &expected_upgrade_authority,
            )?
            .is_some(),
            "already-deployed program ceased to match release bytes/max-len/authority"
        );
    }

    // Recheck all fresh-account predicates immediately before the first write.
    // Resume checkpoints are reconstructed from explicit finalized signatures
    // and exact account images; no prior transaction is resent.
    let recovered_resume = if config.resume_in_progress {
        let pool_create_signature = config
            .resume_pool_create_signature
            .as_ref()
            .context("resume pool creation signature omitted")?;
        Some(recover_resume_state(
            &rpc,
            &program_id,
            &payer,
            &pool,
            &proof_account,
            pool_create_signature,
            config.resume_pool_init_signature.as_ref(),
            config.resume_proof_create_signature.as_ref(),
            statement.sequence,
            public.current_anchor,
            proof.len(),
        )?)
    } else {
        ensure!(
            rpc.account(&pool.pubkey())?.is_none(),
            "pool account ceased to be fresh"
        );
        ensure!(
            rpc.account(&proof_account.pubkey())?.is_none(),
            "proof account ceased to be fresh"
        );
        None
    };
    let resume_checkpoint = recovered_resume.as_ref().map(|state| state.checkpoint);
    let preexisting_pool_snapshot = recovered_resume.as_ref().map(|state| state.pool.clone());
    let preexisting_proof_snapshot = recovered_resume
        .as_ref()
        .and_then(|state| state.proof_account.clone());
    let (nullifier_address, _) = atomic_nullifier_address(&program_id, &public.nullifier);
    let nullifier_before_snapshot = rpc.account(&nullifier_address)?;
    ensure!(nullifier_compatible(
        nullifier_before_snapshot.as_ref(),
        &program_id
    ));

    // Reserve the evidence filename before the first network mutation. If the
    // process fails later, a synced `in_progress_no_claim` record remains and
    // prevents a blind rerun from reusing the same setup identities.
    let evidence_reservation = if config.resume_in_progress {
        EvidenceReservation::resume(&config.evidence)?
    } else {
        EvidenceReservation::reserve(&config.evidence, policy.evidence_artifact())?
    };

    let deployment = deploy_if_needed(
        &rpc,
        &program_id,
        &expected_upgrade_authority,
        policy,
        &config,
        &sbf,
    )?;
    // This is the baseline for the exact executable that all subsequent setup
    // and the final atomic transition are intended to exercise. The snapshot
    // comes from the same finalized RPC reads that passed byte/max-len/authority
    // validation, so the evidence does not have a validation/refetch gap.
    let upgradeable_program_before_setup = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.program_max_len,
        &expected_upgrade_authority,
    )?
    .context("exact deployed program missing immediately before rehearsal setup")?;
    let mut setup_transactions = recovered_resume
        .as_ref()
        .map(|state| state.setup_transactions.clone())
        .unwrap_or_default();

    let pool_rent = rpc.rent(ATOMIC_POOL_STATE_LEN)?;
    if resume_checkpoint.is_none() {
        setup_transactions.push(create_account_transaction(
            &rpc,
            &program_id,
            &payer,
            &pool,
            pool_rent,
            ATOMIC_POOL_STATE_LEN,
            "create_pool_account",
        )?);
    }
    let pool_before_snapshot = if matches!(
        resume_checkpoint,
        Some(ResumeCheckpoint::ProofAccountCreated | ResumeCheckpoint::ProofInitialized)
    ) {
        preexisting_pool_snapshot
            .clone()
            .context("proof-created resume checkpoint omitted pool snapshot")?
    } else {
        let initialize_pool = Instruction {
            program_id,
            accounts: vec![AccountMeta::new(pool.pubkey(), true)],
            data: to_vec(&AspisInstruction::InitializeAtomicPool {
                sequence: statement.sequence,
                anchor: public.current_anchor,
            })?,
        };
        let initialize_pool_tx = signed_transaction(
            &payer,
            &[&pool],
            &[initialize_pool],
            rpc.latest_blockhash()?,
        );
        setup_transactions
            .push(rpc.submit_transaction(&initialize_pool_tx, "tag63_initialize_pool")?);
        rpc.account(&pool.pubkey())?
            .context("initialized pool missing")?
    };
    ensure!(pool_before_snapshot.owner == program_id);
    let pool_before_state = AtomicPoolStateV1::decode(&pool_before_snapshot.data)
        .map_err(|error| anyhow!("decode initialized pool: {error:?}"))?;
    ensure!(
        pool_before_state.sequence == statement.sequence
            && pool_before_state.anchor == public.current_anchor
    );

    let proof_rent = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len())?;
    if resume_checkpoint != Some(ResumeCheckpoint::ProofInitialized) {
        let (init_tx, label) = if resume_checkpoint == Some(ResumeCheckpoint::ProofAccountCreated) {
            let init = proof_instruction(
                &program_id,
                payer.pubkey(),
                proof_account.pubkey(),
                &AspisInstruction::InitProof {
                    total_len: proof.len() as u32,
                },
            )?;
            (
                signed_transaction(
                    &payer,
                    &[&proof_account],
                    &[
                        ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
                        init,
                    ],
                    rpc.latest_blockhash()?,
                ),
                "init_historical_zeroed_proof_account",
            )
        } else {
            (
                create_and_init_proof_transaction(
                    &program_id,
                    &payer,
                    &proof_account,
                    proof_rent,
                    proof.len(),
                    rpc.latest_blockhash()?,
                )?,
                "create_and_init_proof_account",
            )
        };
        let init_simulation = rpc.simulate_exact(&bincode::serialize(&init_tx)?)?;
        ensure!(
            init_simulation.error.is_none(),
            "compute-budgeted proof create/init simulation rejected: {:?}",
            init_simulation.error
        );
        ensure!(
            init_simulation
                .units
                .is_some_and(|units| units < u64::from(CU_LIMIT)),
            "compute-budgeted proof create/init simulation omitted or exceeded its CU limit"
        );
        setup_transactions.push(rpc.submit_transaction(&init_tx, label)?);
    }
    let initialized_proof = rpc
        .account(&proof_account.pubkey())?
        .context("initialized proof account missing")?;
    ensure!(
        initialized_proof.lamports == proof_rent
            && initialized_proof.owner == program_id
            && !initialized_proof.executable
            && initialized_proof.data
                == expected_proof_account(&vec![0u8; proof.len()], payer.pubkey(), false),
        "tag0-initialized proof account image differs before upload"
    );
    let proof_upload_transaction_count = proof.len().div_ceil(UPLOAD_CHUNK_BYTES);
    let proof_upload_finality_windows =
        proof_upload_transaction_count.div_ceil(UPLOAD_WINDOW_TRANSACTIONS);
    setup_transactions.extend(upload_proof_chunks(
        &rpc,
        &program_id,
        &payer,
        &proof_account,
        &proof,
    )?);
    let uploaded = rpc
        .account(&proof_account.pubkey())?
        .context("uploaded proof account missing")?;
    ensure!(
        uploaded.data == expected_proof_account(&proof, payer.pubkey(), false),
        "full pre-finalization proof account bytes differ"
    );
    let finalize = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let finalize_tx = signed_transaction(&payer, &[], &[finalize], rpc.latest_blockhash()?);
    setup_transactions.push(rpc.submit_transaction(&finalize_tx, "tag62_finalize_proof")?);
    let finalized_proof = rpc
        .account(&proof_account.pubkey())?
        .context("finalized proof account missing")?;
    ensure!(
        finalized_proof.data == expected_proof_account(&proof, payer.pubkey(), true),
        "finalized proof bytes/header drift"
    );

    let post_finalize_before = finalized_proof.clone();
    let forbidden_upload = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::UploadChunk {
            offset: 0,
            chunk: vec![proof[0] ^ 1],
        },
    )?;
    let forbidden_upload_tx =
        signed_transaction(&payer, &[], &[forbidden_upload], rpc.latest_blockhash()?);
    let post_finalize_upload_error = rpc
        .simulate_exact(&bincode::serialize(&forbidden_upload_tx)?)?
        .error
        .context("sealed proof accepted an upload simulation")?;
    let post_finalize_upload_rejected =
        post_finalize_upload_error == invalid_account_data_simulation_error(0);
    ensure!(
        post_finalize_upload_rejected,
        "sealed proof upload returned an unexpected rejection: {post_finalize_upload_error}"
    );
    let second_finalize = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let second_finalize_tx =
        signed_transaction(&payer, &[], &[second_finalize], rpc.latest_blockhash()?);
    let post_finalize_second_finalize_error = rpc
        .simulate_exact(&bincode::serialize(&second_finalize_tx)?)?
        .error
        .context("sealed proof accepted second finalization")?;
    let post_finalize_second_finalize_rejected =
        post_finalize_second_finalize_error == invalid_account_data_simulation_error(0);
    ensure!(
        post_finalize_second_finalize_rejected,
        "sealed proof second finalization returned an unexpected rejection: {post_finalize_second_finalize_error}"
    );
    ensure!(rpc.account(&proof_account.pubkey())?.as_ref() == Some(&post_finalize_before));

    let tag65 = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(proof_account.pubkey(), true),
            AccountMeta::new(pool.pubkey(), false),
            AccountMeta::new(nullifier_address, false),
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: to_vec(
            &AspisInstruction::ApplyAtomicStateOnlyProfile23V3WithProofRefund {
                current_anchor: public.current_anchor,
                nullifier: public.nullifier,
                output_commitment: public.output_commitment,
                output_anchor: public.output_anchor,
                asset_id: public.asset_id,
                fee: public.fee,
            },
        )?,
    };
    let final_tx = signed_transaction(
        &payer,
        &[&proof_account],
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            tag65.clone(),
        ],
        rpc.latest_blockhash()?,
    );
    let final_wire = bincode::serialize(&final_tx)?;
    let final_message_hash = sha256(&bincode::serialize(&final_tx.message)?);
    let final_wire_hash = sha256(&final_wire);
    // No RPC call may intervene between this exact executable recheck and the
    // tag65 simulation. In particular, an upgrade that preserves the program
    // address but changes ProgramData cannot inherit the baseline evidence.
    let upgradeable_program_before_final_simulation = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.program_max_len,
        &expected_upgrade_authority,
    )?
    .context("exact deployed program missing immediately before tag65 simulation")?;
    let upgradeable_program_before_final_simulation_continuity =
        upgradeable_program_before_final_simulation
            .continuity_from(&upgradeable_program_before_setup);
    ensure!(
        upgradeable_program_before_final_simulation_continuity.all_unchanged(),
        "upgradeable program or ProgramData identity changed between setup baseline and tag65 simulation"
    );
    let simulation = rpc.simulate_exact(&final_wire)?;
    ensure!(
        simulation.error.is_none(),
        "exact signed tag65 simulation rejected: {:?}",
        simulation.error
    );
    let simulation_cu = simulation.units.context("tag65 simulation omitted CU")?;
    ensure!(
        simulation_cu < u64::from(CU_LIMIT),
        "tag65 simulation exceeded CU limit"
    );
    let final_transaction_simulation_proof_digest_log =
        require_program_proof_digest_log(&simulation.logs, &release_proof_sha256)?;
    ensure!(rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_before_snapshot));
    ensure!(rpc.account(&nullifier_address)? == nullifier_before_snapshot);
    ensure!(rpc.account(&proof_account.pubkey())?.as_ref() == Some(&finalized_proof));

    // Submit the exact byte string that was simulated. On an ambiguous RPC
    // response only that same byte string may be retried once.
    let final_transaction = rpc.submit_wire(
        &final_wire,
        final_tx.signatures[0],
        true,
        "tag65_atomic_verify_and_apply",
        final_message_hash.clone(),
    )?;
    // `submit_wire` returns only after finality. Revalidate both exact release
    // identity and byte-for-byte account continuity before inspecting the
    // resulting state accounts.
    let upgradeable_program_after_finality = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.program_max_len,
        &expected_upgrade_authority,
    )?
    .context("exact deployed program missing after finalized tag65 transaction")?;
    let upgradeable_program_after_finality_continuity =
        upgradeable_program_after_finality.continuity_from(&upgradeable_program_before_setup);
    ensure!(
        upgradeable_program_after_finality_continuity.all_unchanged(),
        "upgradeable program or ProgramData identity changed between setup baseline and tag65 finality"
    );
    ensure!(final_transaction.serialized_transaction_sha256 == final_wire_hash);
    let landed_cu = final_transaction
        .compute_units_consumed
        .context("finalized tag65 transaction omitted computeUnitsConsumed")?;
    ensure!(
        landed_cu < u64::from(CU_LIMIT),
        "finalized tag65 exceeded CU limit"
    );
    let pool_after_snapshot = rpc
        .account(&pool.pubkey())?
        .context("pool missing after tag65")?;
    let pool_after_state = AtomicPoolStateV1::decode(&pool_after_snapshot.data)
        .map_err(|error| anyhow!("decode poststate pool: {error:?}"))?;
    ensure!(
        pool_after_state.sequence
            == statement
                .sequence
                .checked_add(1)
                .context("sequence overflow")?
    );
    ensure!(pool_after_state.anchor == public.output_anchor);
    let nullifier_after_snapshot = rpc
        .account(&nullifier_address)?
        .context("nullifier missing after tag65")?;
    ensure!(nullifier_after_snapshot.owner == program_id);
    ensure!(
        nullifier_after_snapshot.data == expected_nullifier_marker(pool.pubkey(), public.nullifier)
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.is_none(),
        "proof account still exists after successful tag65 refund"
    );

    let account_index = |key: Pubkey| -> Result<usize> {
        final_tx
            .message
            .account_keys
            .iter()
            .position(|candidate| *candidate == key)
            .with_context(|| format!("final tag65 message omitted account {key}"))
    };
    let payer_account_index = account_index(payer.pubkey())?;
    let proof_account_index = account_index(proof_account.pubkey())?;
    let nullifier_account_index = account_index(nullifier_address)?;
    let (final_fee_lamports, pre_balances, post_balances, final_transaction_logs) =
        rpc.transaction_fee_balances_and_logs(&final_tx.signatures[0])?;
    let final_transaction_finalized_proof_digest_log =
        require_program_proof_digest_log(&final_transaction_logs, &release_proof_sha256)?;
    let final_transaction_proof_digest_logs_both_exact =
        final_transaction_simulation_proof_digest_log.exact_release_proof_digest
            && final_transaction_finalized_proof_digest_log.exact_release_proof_digest;
    ensure!(
        final_transaction_proof_digest_logs_both_exact,
        "simulation/finalized program proof-digest logs were not both exact"
    );
    ensure!(pre_balances.len() == final_tx.message.account_keys.len());
    ensure!(post_balances.len() == final_tx.message.account_keys.len());
    let payer_pre_lamports = pre_balances[payer_account_index];
    let payer_post_lamports = post_balances[payer_account_index];
    let proof_pre_lamports = pre_balances[proof_account_index];
    let proof_post_lamports = post_balances[proof_account_index];
    let nullifier_pre_lamports = pre_balances[nullifier_account_index];
    let nullifier_post_lamports = post_balances[nullifier_account_index];
    let proof_refund_lamports = proof_pre_lamports
        .checked_sub(proof_post_lamports)
        .context("proof balance increased during refund")?;
    let nullifier_funding_lamports = nullifier_post_lamports
        .checked_sub(nullifier_pre_lamports)
        .context("nullifier balance decreased during tag65")?;
    ensure!(proof_pre_lamports == finalized_proof.lamports);
    ensure!(proof_post_lamports == 0);
    ensure!(proof_refund_lamports == finalized_proof.lamports);
    let exact_balance_equation_reconciled = i128::from(payer_post_lamports)
        - i128::from(payer_pre_lamports)
        + i128::from(final_fee_lamports)
        + i128::from(nullifier_funding_lamports)
        == i128::from(proof_refund_lamports);
    ensure!(
        exact_balance_equation_reconciled,
        "final tag65 payer/proof/nullifier balances do not reconcile"
    );
    let final_transaction_refund_balances = RefundBalanceEvidence {
        fee_lamports: final_fee_lamports,
        payer_account_index,
        proof_account_index,
        nullifier_account_index,
        payer_pre_lamports,
        payer_post_lamports,
        proof_pre_lamports,
        proof_post_lamports,
        nullifier_pre_lamports,
        nullifier_post_lamports,
        proof_refund_lamports,
        nullifier_funding_lamports,
        exact_balance_equation_reconciled,
    };

    // The successful tag65 transaction closed its proof account. Exercise the
    // replay/nullifier path with a distinct, minimally sized sealed proof so
    // the rejection cannot be an artifact of referring to the closed account.
    // The already-spent nullifier is checked before proof parsing, while the
    // post-success anchor keeps the replay on that exact validation branch.
    let replay_probe_payload = [0u8];
    let replay_probe_rent_lamports =
        rpc.rent(PROOF_ACCOUNT_HEADER_LEN + replay_probe_payload.len())?;
    let mut replay_probe_setup_transactions = vec![create_account_transaction(
        &rpc,
        &program_id,
        &payer,
        &replay_probe,
        replay_probe_rent_lamports,
        PROOF_ACCOUNT_HEADER_LEN + replay_probe_payload.len(),
        "create_replay_probe_account",
    )?];
    let replay_probe_init = proof_instruction(
        &program_id,
        payer.pubkey(),
        replay_probe.pubkey(),
        &AspisInstruction::InitProof {
            total_len: replay_probe_payload.len() as u32,
        },
    )?;
    let replay_probe_upload = proof_instruction(
        &program_id,
        payer.pubkey(),
        replay_probe.pubkey(),
        &AspisInstruction::UploadChunk {
            offset: 0,
            chunk: replay_probe_payload.to_vec(),
        },
    )?;
    let replay_probe_finalize = proof_instruction(
        &program_id,
        payer.pubkey(),
        replay_probe.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let seal_replay_probe_tx = signed_transaction(
        &payer,
        &[&replay_probe],
        &[
            replay_probe_init,
            replay_probe_upload,
            replay_probe_finalize,
        ],
        rpc.latest_blockhash()?,
    );
    let seal_replay_probe_simulation =
        rpc.simulate_exact(&bincode::serialize(&seal_replay_probe_tx)?)?;
    ensure!(
        seal_replay_probe_simulation.error.is_none(),
        "replay-probe sealing simulation rejected: {:?}",
        seal_replay_probe_simulation.error
    );
    replay_probe_setup_transactions
        .push(rpc.submit_transaction(&seal_replay_probe_tx, "seal_replay_probe_account")?);
    let replay_probe_before_close = rpc
        .account(&replay_probe.pubkey())?
        .context("sealed replay-probe account missing")?;
    ensure!(
        replay_probe_before_close.lamports == replay_probe_rent_lamports
            && replay_probe_before_close.owner == program_id
            && !replay_probe_before_close.executable
            && replay_probe_before_close.data
                == expected_proof_account(&replay_probe_payload, payer.pubkey(), true),
        "sealed replay-probe account image differs"
    );

    let mut replay_public = public;
    replay_public.current_anchor = pool_after_state.anchor;
    let replay_tag65 = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(replay_probe.pubkey(), true),
            AccountMeta::new(pool.pubkey(), false),
            AccountMeta::new(nullifier_address, false),
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: to_vec(
            &AspisInstruction::ApplyAtomicStateOnlyProfile23V3WithProofRefund {
                current_anchor: replay_public.current_anchor,
                nullifier: replay_public.nullifier,
                output_commitment: replay_public.output_commitment,
                output_anchor: replay_public.output_anchor,
                asset_id: replay_public.asset_id,
                fee: replay_public.fee,
            },
        )?,
    };
    let duplicate_tx = signed_transaction(
        &payer,
        &[&replay_probe],
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
            ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
            replay_tag65,
        ],
        rpc.latest_blockhash()?,
    );
    let duplicate_simulation_error = rpc
        .simulate_exact(&bincode::serialize(&duplicate_tx)?)?
        .error
        .context("duplicate tag65 simulation unexpectedly accepted")?;
    let duplicate_simulation_expected_nullifier_error_exact = duplicate_simulation_error
        == custom_simulation_error(2, ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT);
    ensure!(
        duplicate_simulation_expected_nullifier_error_exact,
        "duplicate tag65 returned an unexpected rejection: {duplicate_simulation_error}"
    );
    let duplicate_simulation_rejected = true;
    let duplicate_simulation_pool_unchanged =
        rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_after_snapshot);
    let duplicate_simulation_nullifier_unchanged =
        rpc.account(&nullifier_address)?.as_ref() == Some(&nullifier_after_snapshot);
    let duplicate_simulation_replay_probe_unchanged =
        rpc.account(&replay_probe.pubkey())?.as_ref() == Some(&replay_probe_before_close);
    ensure!(
        duplicate_simulation_pool_unchanged
            && duplicate_simulation_nullifier_unchanged
            && duplicate_simulation_replay_probe_unchanged,
        "duplicate tag65 simulation changed pool, nullifier, or replay-probe state"
    );

    // Close the replay probe through append-only tag64 and prove the exact
    // rent flow from finalized transaction metadata.
    let close_replay_probe = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(replay_probe.pubkey(), true),
            AccountMeta::new(payer.pubkey(), true),
        ],
        data: to_vec(&AspisInstruction::CloseFinalizedProof)?,
    };
    let close_replay_probe_tx = signed_transaction(
        &payer,
        &[&replay_probe],
        &[close_replay_probe],
        rpc.latest_blockhash()?,
    );
    let close_replay_probe_wire = bincode::serialize(&close_replay_probe_tx)?;
    let close_replay_probe_simulation = rpc.simulate_exact(&close_replay_probe_wire)?;
    ensure!(
        close_replay_probe_simulation.error.is_none(),
        "tag64 replay-probe close simulation rejected: {:?}",
        close_replay_probe_simulation.error
    );
    ensure!(
        rpc.account(&replay_probe.pubkey())?.as_ref() == Some(&replay_probe_before_close),
        "tag64 close simulation changed the replay probe"
    );
    let replay_probe_close_transaction = rpc.submit_wire(
        &close_replay_probe_wire,
        close_replay_probe_tx.signatures[0],
        true,
        "tag64_close_replay_probe",
        sha256(&bincode::serialize(&close_replay_probe_tx.message)?),
    )?;
    ensure!(
        replay_probe_close_transaction.serialized_transaction_sha256
            == sha256(&close_replay_probe_wire),
        "submitted tag64 close wire differed from its simulation"
    );
    let close_account_index = |key: Pubkey| -> Result<usize> {
        close_replay_probe_tx
            .message
            .account_keys
            .iter()
            .position(|candidate| *candidate == key)
            .with_context(|| format!("tag64 close message omitted account {key}"))
    };
    let close_payer_account_index = close_account_index(payer.pubkey())?;
    let close_replay_probe_account_index = close_account_index(replay_probe.pubkey())?;
    let (close_fee_lamports, close_pre_balances, close_post_balances, _) =
        rpc.transaction_fee_balances_and_logs(&close_replay_probe_tx.signatures[0])?;
    ensure!(
        close_pre_balances.len() == close_replay_probe_tx.message.account_keys.len()
            && close_post_balances.len() == close_replay_probe_tx.message.account_keys.len(),
        "tag64 close balance-vector length drift"
    );
    let close_payer_pre_lamports = close_pre_balances[close_payer_account_index];
    let close_payer_post_lamports = close_post_balances[close_payer_account_index];
    let close_replay_probe_pre_lamports = close_pre_balances[close_replay_probe_account_index];
    let close_replay_probe_post_lamports = close_post_balances[close_replay_probe_account_index];
    let replay_probe_refund_lamports = close_replay_probe_pre_lamports
        .checked_sub(close_replay_probe_post_lamports)
        .context("replay-probe balance increased during tag64 close")?;
    ensure!(
        close_replay_probe_pre_lamports == replay_probe_before_close.lamports
            && close_replay_probe_post_lamports == 0
            && replay_probe_refund_lamports == replay_probe_rent_lamports,
        "tag64 did not refund the replay probe's exact rent balance"
    );
    let replay_probe_refund_exact_balance_equation = i128::from(close_payer_post_lamports)
        - i128::from(close_payer_pre_lamports)
        + i128::from(close_fee_lamports)
        == i128::from(replay_probe_refund_lamports);
    ensure!(
        replay_probe_refund_exact_balance_equation,
        "tag64 replay-probe payer/refund balances do not reconcile"
    );
    let replay_probe_absent_after_close = rpc.account(&replay_probe.pubkey())?.is_none();
    ensure!(
        replay_probe_absent_after_close,
        "replay-probe account still exists after finalized tag64 close"
    );
    ensure!(
        rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_after_snapshot)
            && rpc.account(&nullifier_address)?.as_ref() == Some(&nullifier_after_snapshot),
        "tag64 replay-probe cleanup changed pool or nullifier state"
    );
    let replay_probe_refund_balances = ReplayProbeRefundEvidence {
        fee_lamports: close_fee_lamports,
        payer_account_index: close_payer_account_index,
        replay_probe_account_index: close_replay_probe_account_index,
        payer_pre_lamports: close_payer_pre_lamports,
        payer_post_lamports: close_payer_post_lamports,
        replay_probe_pre_lamports: close_replay_probe_pre_lamports,
        replay_probe_post_lamports: close_replay_probe_post_lamports,
        replay_probe_refund_lamports,
        exact_balance_equation_reconciled: replay_probe_refund_exact_balance_equation,
    };

    let mut evidence = Profile23DevnetEvidence {
        artifact: policy.evidence_artifact(),
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network: policy.network(),
        genesis_hash: policy.expected_genesis_hash().to_owned(),
        program_id: program_id.to_string(),
        release_certificate_path: config.release.display().to_string(),
        release_certificate_sha256: sha256(&release_bytes),
        release_gate_count,
        release_instance_proof_identity_exact,
        release_instance_statement_identity_exact,
        release_instance_selector_binding_exact,
        release_instance_good23_fingerprint_exact,
        release_instance_declared_host_verification_green,
        production_host_verification_green,
        canonical_public_input_digest,
        serialized_selector,
        least_good_selector,
        good23_definition_fingerprint,
        sbf_path: config.sbf.display().to_string(),
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        proof_path: config.proof.display().to_string(),
        proof_bytes: proof.len(),
        proof_sha256: release_proof_sha256,
        proof_upload_chunk_bytes: UPLOAD_CHUNK_BYTES,
        proof_upload_window_transactions: UPLOAD_WINDOW_TRANSACTIONS,
        proof_upload_transaction_count,
        proof_upload_finality_windows,
        statement_path: config.statement.display().to_string(),
        statement_sha256: sha256(&statement_bytes),
        program_max_len: config.program_max_len,
        resumed_from_in_progress: config.resume_in_progress,
        resume_checkpoint: resume_checkpoint.map(|checkpoint| checkpoint.label().to_owned()),
        preexisting_pool_before_resume: preexisting_pool_snapshot
            .as_ref()
            .map(|account| account.evidence(pool.pubkey())),
        preexisting_proof_account_before_resume: preexisting_proof_snapshot
            .as_ref()
            .map(|account| account.evidence(proof_account.pubkey())),
        upgradeable_program_before_setup: upgradeable_program_before_setup.evidence(),
        upgradeable_program_before_setup_exact_release_sbf_max_len_authority: true,
        upgradeable_program_before_final_simulation:
            upgradeable_program_before_final_simulation.evidence(),
        upgradeable_program_before_final_simulation_exact_release_sbf_max_len_authority: true,
        upgradeable_program_before_final_simulation_continuity,
        upgradeable_program_after_finality: upgradeable_program_after_finality.evidence(),
        upgradeable_program_after_finality_exact_release_sbf_max_len_authority: true,
        upgradeable_program_after_finality_continuity,
        deployment,
        setup_transactions,
        final_transaction,
        final_transaction_simulation_cu: simulation_cu,
        final_transaction_simulation_proof_digest_log,
        final_transaction_finalized_proof_digest_log,
        final_transaction_proof_digest_logs_both_exact,
        final_transaction_wire_sha256: final_wire_hash,
        final_transaction_message_sha256: final_message_hash,
        final_transaction_submitted_identically_to_simulation: true,
        proof_account_before_refund: finalized_proof.evidence(proof_account.pubkey()),
        proof_account_finalized_before_refund: true,
        proof_account_absent_after_refund: true,
        final_transaction_refund_balances,
        post_finalize_upload_rejected,
        post_finalize_second_finalize_rejected,
        pool_before: pool_before_snapshot.evidence(pool.pubkey()),
        pool_after: pool_after_snapshot.evidence(pool.pubkey()),
        sequence_before: pool_before_state.sequence,
        sequence_after: pool_after_state.sequence,
        nullifier_before: nullifier_before_snapshot.map(|account| account.evidence(nullifier_address)),
        nullifier_after: nullifier_after_snapshot.evidence(nullifier_address),
        duplicate_simulation_rejected,
        duplicate_simulation_error,
        duplicate_simulation_expected_nullifier_error_exact,
        duplicate_simulation_pool_unchanged,
        duplicate_simulation_nullifier_unchanged,
        duplicate_simulation_replay_probe_unchanged,
        replay_probe_pubkey: replay_probe.pubkey().to_string(),
        replay_probe_payload_bytes: replay_probe_payload.len(),
        replay_probe_rent_lamports,
        replay_probe_setup_transactions,
        replay_probe_before_close: replay_probe_before_close.evidence(replay_probe.pubkey()),
        replay_probe_close_transaction,
        replay_probe_absent_after_close,
        replay_probe_refund_balances,
        evidence_path: config.evidence.display().to_string(),
        evidence_file_mode: 0,
        explicit_scope: vec![
            match policy {
                ClusterPolicy::Devnet => "Devnet rehearsal only; this is not mainnet-beta evidence.",
                ClusterPolicy::MainnetBeta => "Finalized mainnet-beta demo evidence under the pinned mainnet genesis.",
            },
            "The single tag65 transaction verifies and closes a previously finalized proof account, refunds its full rent, and atomically mutates pool/nullifier state.",
            "Deployment, pool initialization, proof-account creation, uploads, and finalization are setup transactions.",
            match (policy, config.upgrade_authority_keypair.is_some()) {
                (ClusterPolicy::Devnet, false) => "The rehearsal deployment remains upgradeable under the explicit payer.",
                (ClusterPolicy::Devnet, true) => "The rehearsal deployment remains upgradeable under the explicit dedicated upgrade authority.",
                (ClusterPolicy::MainnetBeta, _) => "The mainnet deployment remains upgradeable under the explicit dedicated upgrade authority retained for ProgramData recovery.",
            },
        ],
    };
    evidence.evidence_file_mode = 0o444;
    evidence_reservation.commit(&evidence)?;
    Ok(evidence)
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;
    use solana_sdk::{account_info::AccountInfo, clock::Epoch};

    use super::*;
    use crate::profile23_statement::{
        PROFILE23_STATEMENT_ARTIFACT, PROFILE23_STATEMENT_SELECTION_RULE,
    };

    struct TempRoot(PathBuf);

    impl TempRoot {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "aspis-profile23-devnet-release-instance-{}-{}",
                std::process::id(),
                chrono::Utc::now().timestamp_nanos_opt().unwrap()
            ));
            fs::create_dir_all(&path).unwrap();
            Self(fs::canonicalize(path).unwrap())
        }
    }

    impl Drop for TempRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn proof_digest_log_requires_one_exact_release_digest() {
        let digest = [7u8; 32];
        let expected = digest
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let line = format!(
            "Program data: {} {}",
            BASE64.encode(PROOF_SHA256_LOG_MARKER),
            BASE64.encode(digest)
        );
        let evidence = require_program_proof_digest_log(&[line.clone()], &expected).unwrap();
        assert_eq!(evidence.raw_log_line, line);
        assert_eq!(evidence.logged_proof_sha256, expected);
        assert!(evidence.exact_release_proof_digest);
        assert!(
            require_program_proof_digest_log(&[line.clone(), line], &expected).is_err(),
            "duplicate proof-digest logs must fail closed"
        );
        assert!(
            require_program_proof_digest_log(
                &[format!(
                    "Program data: {} {}",
                    BASE64.encode(PROOF_SHA256_LOG_MARKER),
                    BASE64.encode([8u8; 32])
                )],
                &expected,
            )
            .is_err(),
            "a different logged proof digest must fail closed"
        );
    }

    fn statement(seed: u32) -> aspis_statement::AtomicPaymentStatementV3 {
        let digest =
            |offset: u32| core::array::from_fn(|index| M31(seed + offset + 17 * index as u32));
        aspis_statement::AtomicPaymentStatementV3 {
            pool: [seed as u8; 32],
            sequence: u64::from(seed) + 7,
            spend: aspis_statement::SpendPublic {
                anchor: digest(11),
                nullifier: digest(101),
                output_commitment: digest(201),
                asset_id: M31(17),
                fee: 1,
            },
            output_anchor: digest(301),
        }
    }

    fn sidecar(statement: &aspis_statement::AtomicPaymentStatementV3) -> Vec<u8> {
        serde_json::to_vec_pretty(&json!({
            "artifact": PROFILE23_STATEMENT_ARTIFACT,
            "pool_hex": profile23_hex(&statement.pool),
            "sequence": statement.sequence,
            "current_anchor_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.anchor)
            ),
            "nullifier_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.nullifier)
            ),
            "output_commitment_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.spend.output_commitment)
            ),
            "output_anchor_hex": profile23_hex(
                &aspis_statement::encode_digest_canonical(&statement.output_anchor)
            ),
            "asset_id": statement.spend.asset_id.0,
            "fee": statement.spend.fee,
            "selection_rule": PROFILE23_STATEMENT_SELECTION_RULE,
            "witness_independent_public_metadata": true,
        }))
        .unwrap()
    }

    fn release_for(
        proof_path: &str,
        proof: &[u8],
        statement_path: &str,
        statement_bytes: &[u8],
    ) -> Value {
        let statement = decode_profile23_statement_sidecar(statement_bytes).unwrap();
        json!({
            "release_instance": {
                "proof_path": proof_path,
                "proof_bytes": proof.len(),
                "proof_sha256": sha256(proof),
                "statement_path": statement_path,
                "statement_bytes": statement_bytes.len(),
                "statement_sha256": sha256(statement_bytes),
                "statement_pool_hex": profile23_hex(&statement.pool),
                "statement_sequence": statement.sequence,
                "canonical_public_input_digest": canonical_profile23_public_input_digest(&statement).unwrap(),
                "selector_candidates": 3,
                "serialized_selector": 0,
                "least_good_selector": 0,
                "good23_branches": [
                    {"selector": 0, "accepted": true},
                    {"selector": 1, "accepted": false},
                    {"selector": 2, "accepted": true}
                ],
                "good23_definition_fingerprint": live_good23_definition_fingerprint(),
                "production_host_verification_green": true,
                "evaluation_error": null
            }
        })
    }

    fn complete_args() -> Vec<String> {
        vec![
            "--rpc-url",
            "https://api.devnet.solana.com",
            "--payer-keypair",
            "/tmp/payer.json",
            "--program-keypair",
            "/tmp/program.json",
            "--pool-keypair",
            "/tmp/pool.json",
            "--proof-account-keypair",
            "/tmp/proof-account.json",
            "--release",
            "/tmp/release.json",
            "--sbf",
            "/tmp/program.so",
            "--proof",
            "/tmp/proof.bin",
            "--statement",
            "/tmp/proof.statement.json",
            "--solana-cli",
            "/usr/local/bin/solana",
            "--evidence",
            "/tmp/evidence.json",
            "--program-max-len",
            "7000000",
            "--fee-reserve-lamports",
            "100000000",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect()
    }

    fn complete_mainnet_args() -> Vec<String> {
        let mut arguments = complete_args();
        let rpc = arguments
            .iter()
            .position(|argument| argument == "--rpc-url")
            .unwrap();
        arguments[rpc + 1] = "https://api.mainnet-beta.solana.com".to_owned();
        arguments.extend(
            [
                "--replay-probe-keypair",
                "/tmp/replay-probe.json",
                "--upgrade-authority-keypair",
                "/tmp/upgrade-authority.json",
                "--deployment-buffer-keypair",
                "/tmp/deployment-buffer.json",
                "--use-tpu-client",
                "--execute-mainnet",
                "--acknowledgement",
                MAINNET_EXECUTE_ACK,
            ]
            .into_iter()
            .map(str::to_owned),
        );
        arguments
    }

    fn string_arguments(arguments: Vec<OsString>) -> Vec<String> {
        arguments
            .into_iter()
            .map(|argument| argument.into_string().unwrap())
            .collect()
    }

    fn complete_upload_smoke_args() -> Vec<String> {
        vec![
            "--rpc-url",
            "https://api.devnet.solana.com",
            "--payer-keypair",
            "/tmp/payer.json",
            "--proof-account-keypair",
            "/tmp/proof-account.json",
            "--sbf",
            "/tmp/program.so",
            "--proof",
            "/tmp/proof.bin",
            "--evidence",
            "/tmp/upload-smoke.json",
            "--program-max-len",
            "925760",
            "--fee-reserve-lamports",
            "100000000",
            "--execute-devnet",
            "--acknowledgement",
            UPLOAD_SMOKE_ACK,
        ]
        .into_iter()
        .map(str::to_owned)
        .collect()
    }

    fn test_signature(label: &[u8]) -> Signature {
        Keypair::new().sign_message(label)
    }

    fn status(slot: u64, progress: &str) -> Option<SignatureStatusObservation> {
        Some(SignatureStatusObservation {
            slot,
            error: None,
            progress: match progress {
                "processed" => ConfirmationProgress::Processed,
                "confirmed" => ConfirmationProgress::Confirmed,
                "finalized" => ConfirmationProgress::Finalized,
                _ => panic!("unsupported test progress"),
            },
        })
    }

    fn upload_wire_len(chunk_len: usize) -> usize {
        let payer = Keypair::new();
        let proof_account = Keypair::new();
        let program_id = Pubkey::new_unique();
        let upload = proof_instruction(
            &program_id,
            payer.pubkey(),
            proof_account.pubkey(),
            &AspisInstruction::UploadChunk {
                offset: 0,
                chunk: vec![0x5a; chunk_len],
            },
        )
        .unwrap();
        bincode::serialize(&signed_transaction(&payer, &[], &[upload], Hash::default()))
            .unwrap()
            .len()
    }

    #[test]
    fn upload_geometry_fits_packet_cap_and_uses_five_finality_windows() {
        assert_eq!(upload_wire_len(UPLOAD_CHUNK_BYTES), 1_173);
        assert_eq!(upload_wire_len(1_019), MAX_TRANSACTION_WIRE_BYTES);
        assert_eq!(upload_wire_len(1_020), MAX_TRANSACTION_WIRE_BYTES + 1);

        let proof_len = 64_447usize;
        let chunk_lengths = (0..proof_len)
            .step_by(UPLOAD_CHUNK_BYTES)
            .map(|offset| (proof_len - offset).min(UPLOAD_CHUNK_BYTES))
            .collect::<Vec<_>>();
        assert_eq!(chunk_lengths.len(), 68);
        assert_eq!(chunk_lengths.last(), Some(&127));
        assert_eq!(
            chunk_lengths
                .chunks(UPLOAD_WINDOW_TRANSACTIONS)
                .map(<[usize]>::len)
                .collect::<Vec<_>>(),
            vec![16, 16, 16, 16, 4]
        );
    }

    #[test]
    fn primary_create_and_tag0_use_the_explicit_runtime_program_id_atomically() {
        let payer = Keypair::new();
        let proof_account = Keypair::new();
        let program_id = Pubkey::new_unique();
        assert_ne!(program_id, aspis_verifier::id());
        let transaction = create_and_init_proof_transaction(
            &program_id,
            &payer,
            &proof_account,
            123_456,
            64_447,
            Hash::new_unique(),
        )
        .unwrap();
        transaction.verify().unwrap();
        assert_eq!(transaction.signatures.len(), 2);
        assert_eq!(transaction.message.instructions.len(), 3);
        let create = &transaction.message.instructions[1];
        let init = &transaction.message.instructions[2];
        assert_eq!(
            transaction.message.account_keys[create.program_id_index as usize],
            system_program::id()
        );
        let create: system_instruction::SystemInstruction =
            bincode::deserialize(&create.data).unwrap();
        assert!(matches!(
            create,
            system_instruction::SystemInstruction::CreateAccount {
                owner,
                space,
                ..
            } if owner == program_id && space == (PROOF_ACCOUNT_HEADER_LEN + 64_447) as u64
        ));
        assert_eq!(
            transaction.message.account_keys[init.program_id_index as usize],
            program_id
        );
        assert_eq!(
            init.data.first(),
            Some(&0),
            "tag0 must follow create-account"
        );
    }

    #[test]
    fn resume_classifier_preserves_legacy_zeroed_and_atomic_tag0_checkpoints() {
        let program_id = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let rent = 99_000;
        let proof_len = 11;
        let legacy = RpcAccount {
            lamports: rent,
            owner: program_id,
            executable: false,
            data: vec![0u8; PROOF_ACCOUNT_HEADER_LEN + proof_len],
        };
        assert_eq!(
            resumed_proof_checkpoint(&legacy, &program_id, rent, proof_len, authority),
            Some(ResumeCheckpoint::ProofAccountCreated)
        );
        let initialized = RpcAccount {
            data: expected_proof_account(&vec![0u8; proof_len], authority, false),
            ..legacy.clone()
        };
        assert_eq!(
            resumed_proof_checkpoint(&initialized, &program_id, rent, proof_len, authority),
            Some(ResumeCheckpoint::ProofInitialized)
        );
        let mut drifted = initialized;
        drifted.data[PROOF_ACCOUNT_HEADER_LEN] = 1;
        assert_eq!(
            resumed_proof_checkpoint(&drifted, &program_id, rent, proof_len, authority),
            None
        );
    }

    #[test]
    fn partial_proof_cleanup_is_one_ordered_tag62_tag64_transaction() {
        let payer = Keypair::new();
        let proof_account = Keypair::new();
        let program_id = Pubkey::new_unique();
        let transaction = finalize_and_close_partial_proof_transaction(
            &program_id,
            &payer,
            &proof_account,
            Hash::new_unique(),
        )
        .unwrap();
        transaction.verify().unwrap();
        assert_eq!(transaction.signatures.len(), 2);
        assert_eq!(transaction.message.instructions.len(), 2);
        for (instruction, tag) in transaction.message.instructions.iter().zip([62, 64]) {
            assert_eq!(
                transaction.message.account_keys[instruction.program_id_index as usize],
                program_id
            );
            assert_eq!(instruction.data.first(), Some(&tag));
        }

        let proof_key = proof_account.pubkey();
        let payer_key = payer.pubkey();
        let system_owner = system_program::id();
        let mut proof_lamports = 777_000;
        let mut payer_lamports = 12_000;
        let original_total = proof_lamports + payer_lamports;
        let mut proof_data = expected_proof_account(&[0u8; 8], payer_key, false);
        proof_data[PROOF_ACCOUNT_HEADER_LEN..PROOF_ACCOUNT_HEADER_LEN + 3]
            .copy_from_slice(&[0xa1, 0xb2, 0xc3]);
        let mut payer_data = [];
        {
            let proof_info = AccountInfo::new(
                &proof_key,
                true,
                true,
                &mut proof_lamports,
                &mut proof_data,
                &program_id,
                false,
                Epoch::default(),
            );
            let payer_info = AccountInfo::new(
                &payer_key,
                true,
                true,
                &mut payer_lamports,
                &mut payer_data,
                &system_owner,
                false,
                Epoch::default(),
            );
            let accounts = [proof_info, payer_info];
            aspis_verifier::process_instruction(
                &program_id,
                &accounts,
                &transaction.message.instructions[0].data,
            )
            .unwrap();
            assert!(accounts[0].try_borrow_data().unwrap()
                [PROOF_AUTHORITY_OFFSET..PROOF_AUTHORITY_OFFSET + 32]
                .iter()
                .all(|byte| *byte == 0));
            aspis_verifier::process_instruction(
                &program_id,
                &accounts,
                &transaction.message.instructions[1].data,
            )
            .unwrap();
        }
        assert_eq!(proof_lamports, 0);
        assert_eq!(payer_lamports, original_total);
    }

    #[test]
    fn signature_status_batch_parser_is_shape_and_state_strict() {
        let parsed = parse_signature_status_batch(
            &json!({
                "value": [
                    null,
                    {
                        "slot": 71,
                        "confirmations": null,
                        "err": null,
                        "confirmationStatus": "finalized"
                    }
                ]
            }),
            2,
        )
        .unwrap();
        assert!(parsed[0].is_none());
        assert_eq!(parsed[1].as_ref().unwrap().slot, 71);
        assert_eq!(
            parsed[1].as_ref().unwrap().progress,
            ConfirmationProgress::Finalized
        );

        let nullable = parse_signature_status_batch(
            &json!({
                "value": [
                    {"slot": 72, "confirmations": null, "err": null, "confirmationStatus": null},
                    {"slot": 73, "confirmations": 2, "err": null, "confirmationStatus": null}
                ]
            }),
            2,
        )
        .unwrap();
        assert_eq!(
            nullable[0].as_ref().unwrap().progress,
            ConfirmationProgress::Finalized
        );
        assert_eq!(
            nullable[1].as_ref().unwrap().progress,
            ConfirmationProgress::Processed
        );

        assert!(parse_signature_status_batch(&json!({"value": [null]}), 2).is_err());
        assert!(parse_signature_status_batch(
            &json!({"value": [{
                "slot": 1,
                "err": null,
                "confirmationStatus": "optimistic"
            }]}),
            1,
        )
        .is_err());
        assert!(parse_signature_status_batch(
            &json!({"value": [{"err": null, "confirmationStatus": "confirmed"}]}),
            1,
        )
        .is_err());
    }

    #[test]
    fn finalization_tracker_accepts_out_of_order_progress_and_preserves_submission_order() {
        let first = test_signature(b"first");
        let second = test_signature(b"second");
        let mut tracker =
            FinalizationTracker::new(vec![first, second]).expect("unique nonempty batch");

        assert!(!tracker
            .observe(vec![status(31, "confirmed"), status(29, "finalized")])
            .unwrap());
        assert!(tracker
            .observe(vec![status(31, "finalized"), status(29, "finalized")])
            .unwrap());
        assert_eq!(
            tracker.finalized_slots_in_submission_order().unwrap(),
            vec![31, 29]
        );
    }

    #[test]
    fn finalization_tracker_fails_on_transaction_error_and_tolerates_prefinality_forks() {
        let signature = test_signature(b"partial-failure");
        assert!(FinalizationTracker::new(Vec::new()).is_err());
        assert!(FinalizationTracker::new(vec![signature, signature]).is_err());

        let mut failed = FinalizationTracker::new(vec![signature]).unwrap();
        assert!(failed
            .observe(vec![Some(SignatureStatusObservation {
                slot: 17,
                error: Some(json!({"InstructionError": [0, "InvalidAccountData"]})),
                progress: ConfirmationProgress::Confirmed,
            })])
            .is_err());

        let mut disappeared = FinalizationTracker::new(vec![signature]).unwrap();
        assert!(!disappeared.observe(vec![status(17, "processed")]).unwrap());
        assert!(!disappeared.observe(vec![None]).unwrap());
        assert!(disappeared.ensure_unseen_not_expired(18, 17).is_err());

        let mut regressed = FinalizationTracker::new(vec![signature]).unwrap();
        assert!(!regressed.observe(vec![status(17, "confirmed")]).unwrap());
        assert!(!regressed.observe(vec![status(17, "processed")]).unwrap());

        let mut moved = FinalizationTracker::new(vec![signature]).unwrap();
        assert!(!moved.observe(vec![status(17, "confirmed")]).unwrap());
        assert!(moved.observe(vec![status(18, "finalized")]).unwrap());
        assert!(moved.observe(vec![None]).unwrap());
        assert_eq!(
            moved.finalized_slots_in_submission_order().unwrap(),
            vec![18]
        );
    }

    #[test]
    fn blockhash_expiry_rejects_never_observed_transactions() {
        let signature = test_signature(b"expiry");
        let mut unseen = FinalizationTracker::new(vec![signature]).unwrap();
        unseen.ensure_unseen_not_expired(100, 100).unwrap();
        assert!(unseen.ensure_unseen_not_expired(101, 100).is_err());
        assert!(unseen.finalized_slots_in_submission_order().is_err());

        assert!(!unseen.observe(vec![status(41, "processed")]).unwrap());
        unseen.ensure_unseen_not_expired(101, 100).unwrap();
    }

    #[test]
    fn readiness_refuses_execution_interlocks() {
        let mut args = complete_args();
        args.push("--execute-devnet".to_owned());
        assert!(parse_args(&args, CommandMode::Readiness).is_err());
    }

    #[test]
    fn executor_requires_both_interlocks() {
        let args = complete_args();
        let parsed = parse_args(&args, CommandMode::Execute).unwrap();
        assert!(!parsed.execute_interlock);
        assert_ne!(parsed.acknowledgement.as_deref(), Some(EXECUTE_ACK));
    }

    #[test]
    fn cluster_policies_pin_genesis_acknowledgement_and_evidence_identity() {
        assert_eq!(
            ClusterPolicy::Devnet.expected_genesis_hash(),
            DEVNET_GENESIS_HASH
        );
        assert_eq!(ClusterPolicy::Devnet.network(), "devnet");
        assert_eq!(
            ClusterPolicy::Devnet.evidence_artifact(),
            "profile23_devnet_finalized_rehearsal"
        );
        assert_eq!(
            ClusterPolicy::MainnetBeta.expected_genesis_hash(),
            MAINNET_BETA_GENESIS_HASH
        );
        assert_eq!(ClusterPolicy::MainnetBeta.network(), "mainnet-beta");
        assert_eq!(
            ClusterPolicy::MainnetBeta.evidence_artifact(),
            "profile23_mainnet_beta_finalized_demo"
        );
        assert_eq!(
            ClusterPolicy::MainnetBeta.execution_acknowledgement(),
            MAINNET_EXECUTE_ACK
        );
    }

    #[test]
    fn mainnet_execution_policy_requires_every_exact_interlock_and_recovery_role() {
        let complete = complete_mainnet_args();
        let parsed = parse_args(&complete, CommandMode::ExecuteMainnet).unwrap();
        validate_execution_policy(&parsed, ClusterPolicy::MainnetBeta).unwrap();

        for required_pair in [
            "--replay-probe-keypair",
            "--upgrade-authority-keypair",
            "--deployment-buffer-keypair",
        ] {
            let mut incomplete = complete.clone();
            let index = incomplete
                .iter()
                .position(|argument| argument == required_pair)
                .unwrap();
            incomplete.drain(index..=index + 1);
            let parsed = parse_args(&incomplete, CommandMode::ExecuteMainnet).unwrap();
            assert!(
                validate_execution_policy(&parsed, ClusterPolicy::MainnetBeta).is_err(),
                "mainnet policy accepted missing {required_pair}"
            );
        }

        for required_flag in ["--use-tpu-client", "--execute-mainnet"] {
            let mut incomplete = complete.clone();
            let index = incomplete
                .iter()
                .position(|argument| argument == required_flag)
                .unwrap();
            incomplete.remove(index);
            let parsed = parse_args(&incomplete, CommandMode::ExecuteMainnet).unwrap();
            assert!(
                validate_execution_policy(&parsed, ClusterPolicy::MainnetBeta).is_err(),
                "mainnet policy accepted missing {required_flag}"
            );
        }

        let mut wrong_acknowledgement = complete.clone();
        let acknowledgement = wrong_acknowledgement
            .iter()
            .position(|argument| argument == "--acknowledgement")
            .unwrap();
        wrong_acknowledgement[acknowledgement + 1] = EXECUTE_ACK.to_owned();
        let parsed = parse_args(&wrong_acknowledgement, CommandMode::ExecuteMainnet).unwrap();
        assert!(validate_execution_policy(&parsed, ClusterPolicy::MainnetBeta).is_err());

        let mut wrong_cluster = complete;
        let interlock = wrong_cluster
            .iter()
            .position(|argument| argument == "--execute-mainnet")
            .unwrap();
        wrong_cluster[interlock] = "--execute-devnet".to_owned();
        assert!(parse_args(&wrong_cluster, CommandMode::ExecuteMainnet).is_err());
    }

    #[test]
    fn devnet_policy_and_deploy_cli_defaults_remain_backward_compatible() {
        let readiness_config = parse_args(&complete_args(), CommandMode::Readiness).unwrap();
        assert_eq!(
            string_arguments(deploy_cli_args(&readiness_config, ClusterPolicy::Devnet).unwrap()),
            vec![
                "--url",
                "https://api.devnet.solana.com",
                "--keypair",
                "/tmp/payer.json",
                "--output",
                "json",
                "program",
                "deploy",
                "/tmp/program.so",
                "--program-id",
                "/tmp/program.json",
                "--upgrade-authority",
                "/tmp/payer.json",
                "--max-len",
                "7000000",
            ]
        );

        let mut execute_arguments = complete_args();
        execute_arguments.extend(
            ["--execute-devnet", "--acknowledgement", EXECUTE_ACK]
                .into_iter()
                .map(str::to_owned),
        );
        let parsed = parse_args(&execute_arguments, CommandMode::Execute).unwrap();
        validate_execution_policy(&parsed, ClusterPolicy::Devnet).unwrap();
        assert!(parsed.replay_probe_keypair.is_none());
        assert!(parsed.upgrade_authority_keypair.is_none());
        assert!(parsed.deployment_buffer_keypair.is_none());
        assert!(!parsed.use_tpu_client);
    }

    #[test]
    fn mainnet_deploy_cli_is_finalized_direct_tpu_single_attempt_and_zero_price() {
        let config = parse_args(&complete_mainnet_args(), CommandMode::ExecuteMainnet).unwrap();
        assert_eq!(
            string_arguments(deploy_cli_args(&config, ClusterPolicy::MainnetBeta).unwrap()),
            vec![
                "--url",
                "https://api.mainnet-beta.solana.com",
                "--keypair",
                "/tmp/payer.json",
                "--output",
                "json",
                "--commitment",
                "finalized",
                "program",
                "deploy",
                "/tmp/program.so",
                "--program-id",
                "/tmp/program.json",
                "--upgrade-authority",
                "/tmp/upgrade-authority.json",
                "--max-len",
                "7000000",
                "--buffer",
                "/tmp/deployment-buffer.json",
                "--use-tpu-client",
                "--max-sign-attempts",
                "1",
                "--with-compute-unit-price",
                "0",
            ]
        );

        let incomplete = parse_args(&complete_args(), CommandMode::Readiness).unwrap();
        assert!(deploy_cli_args(&incomplete, ClusterPolicy::MainnetBeta).is_err());
    }

    #[test]
    fn upload_smoke_parser_requires_explicit_safe_arguments() {
        let parsed = parse_upload_smoke_args(&complete_upload_smoke_args()).unwrap();
        assert!(parsed.execute_interlock);
        assert_eq!(parsed.acknowledgement.as_deref(), Some(UPLOAD_SMOKE_ACK));
        assert_eq!(parsed.program_max_len, 925_760);

        let mut relative = complete_upload_smoke_args();
        let proof = relative.iter().position(|arg| arg == "--proof").unwrap();
        relative[proof + 1] = "relative.bin".to_owned();
        assert!(parse_upload_smoke_args(&relative).is_err());

        let mut duplicate = complete_upload_smoke_args();
        duplicate.push("--execute-devnet".to_owned());
        assert!(parse_upload_smoke_args(&duplicate).is_err());

        let mut unknown = complete_upload_smoke_args();
        unknown.push("--unexpected".to_owned());
        unknown.push("value".to_owned());
        assert!(parse_upload_smoke_args(&unknown).is_err());
    }

    #[test]
    fn exact_negative_simulation_error_is_pinned() {
        assert_eq!(
            invalid_account_data_simulation_error(0),
            json!({"InstructionError": [0, "InvalidAccountData"]})
        );
        assert_ne!(
            invalid_account_data_simulation_error(0),
            json!({"InstructionError": [1, "InvalidAccountData"]})
        );
    }

    #[test]
    fn explicit_resume_requires_and_parses_creation_signature() {
        let mut missing_signature = complete_args();
        missing_signature.push("--resume-in-progress".to_owned());
        assert!(parse_args(&missing_signature, CommandMode::Execute).is_err());

        let mut args = complete_args();
        args.push("--resume-in-progress".to_owned());
        args.push("--resume-pool-create-signature".to_owned());
        args.push(Signature::default().to_string());
        let parsed = parse_args(&args, CommandMode::Readiness).unwrap();
        assert!(parsed.resume_in_progress);
        assert_eq!(
            parsed.resume_pool_create_signature,
            Some(Signature::default())
        );
    }

    #[test]
    fn explicit_paths_are_mandatory() {
        let mut args = complete_args();
        let index = args.iter().position(|arg| arg == "--proof").unwrap();
        args[index + 1] = "relative.bin".to_owned();
        assert!(parse_args(&args, CommandMode::Readiness).is_err());
    }

    #[test]
    fn replay_probe_keypair_is_optional_on_devnet_but_explicit_paths_are_absolute() {
        let parsed = parse_args(&complete_args(), CommandMode::Readiness).unwrap();
        assert!(parsed.replay_probe_keypair.is_none());

        let mut explicit = complete_args();
        explicit.push("--replay-probe-keypair".to_owned());
        explicit.push("/tmp/replay-probe.json".to_owned());
        let parsed = parse_args(&explicit, CommandMode::Readiness).unwrap();
        assert_eq!(
            parsed.replay_probe_keypair,
            Some(PathBuf::from("/tmp/replay-probe.json"))
        );

        let mut relative = complete_args();
        relative.push("--replay-probe-keypair".to_owned());
        relative.push("replay-probe.json".to_owned());
        assert!(parse_args(&relative, CommandMode::Readiness).is_err());
    }

    #[test]
    fn release_gate_count_is_flexible_but_never_empty_or_partially_green() {
        let release = |gates: Vec<Value>, failed_gates: Vec<Value>| {
            json!({
                "artifact": "profile23_one_transaction_release",
                "released": true,
                "status": "released_all_required_gates_green",
                "gates": gates,
                "failed_gates": failed_gates,
            })
        };
        assert_eq!(
            release_certificate_green_gate_count(&release(
                vec![json!({"name": "one", "passed": true})],
                Vec::new(),
            )),
            Some(1)
        );
        assert_eq!(
            release_certificate_green_gate_count(&release(
                (0..37)
                    .map(|index| json!({"name": format!("gate_{index}"), "passed": true}))
                    .collect(),
                Vec::new(),
            )),
            Some(37)
        );
        assert_eq!(
            release_certificate_green_gate_count(&release(Vec::new(), Vec::new())),
            None
        );
        assert_eq!(
            release_certificate_green_gate_count(&release(
                vec![json!({"name": "bad", "passed": false})],
                Vec::new(),
            )),
            None
        );
        assert_eq!(
            release_certificate_green_gate_count(&release(
                vec![json!({"name": "claimed", "passed": true})],
                vec![json!("claimed")],
            )),
            None
        );
        let mut wrong_artifact =
            release(vec![json!({"name": "claimed", "passed": true})], Vec::new());
        wrong_artifact["artifact"] = Value::String("unrelated_release".to_owned());
        assert_eq!(release_certificate_green_gate_count(&wrong_artifact), None);
    }

    #[test]
    fn live_release_comparison_ignores_only_generation_time() {
        let left = json!({
            "artifact": "profile23_one_transaction_release",
            "generated_at_utc": "2026-07-13T20:00:00Z",
            "gates": [{"name": "required", "passed": true}],
            "released": true,
        });
        let mut right = left.clone();
        right["generated_at_utc"] = Value::String("2026-07-13T20:00:01Z".to_owned());
        assert!(release_values_match_ignoring_generation_time(&left, &right).unwrap());

        right["gates"][0]["passed"] = Value::Bool(false);
        assert!(!release_values_match_ignoring_generation_time(&left, &right).unwrap());

        let mut missing_time = left.clone();
        missing_time
            .as_object_mut()
            .unwrap()
            .remove("generated_at_utc");
        assert!(release_values_match_ignoring_generation_time(&left, &missing_time).is_err());
    }

    #[test]
    fn whole_live_release_comparison_rejects_truncated_gates_branch_drift_and_source_drift() {
        let live = json!({
            "artifact": "profile23_one_transaction_release",
            "generated_at_utc": "2026-07-13T20:00:00Z",
            "status": "released_all_required_gates_green",
            "released": true,
            "gates": [
                {"name": "soundness", "passed": true, "evidence": "live"},
                {"name": "hiding", "passed": true, "evidence": "live"}
            ],
            "failed_gates": [],
            "source_artifacts": [
                {
                    "label": "soundness",
                    "path": "results/stage2/soundness.json",
                    "bytes": 17,
                    "sha256": "11".repeat(32)
                },
                {
                    "label": "production_proof",
                    "path": "results/stage2/proofs/profile23.bin",
                    "bytes": 61_599,
                    "sha256": "22".repeat(32)
                }
            ],
            "release_instance": {
                "serialized_selector": 1,
                "least_good_selector": 1,
                "good23_branches": [
                    {"selector": 0, "accepted": false},
                    {"selector": 1, "accepted": true},
                    {"selector": 2, "accepted": true}
                ]
            }
        });

        let mut fabricated_one_gate = live.clone();
        fabricated_one_gate["gates"] = json!([
            {"name": "soundness", "passed": true, "evidence": "live"}
        ]);
        assert!(
            !release_values_match_ignoring_generation_time(&fabricated_one_gate, &live).unwrap()
        );

        let mut mutated_good23_branch = live.clone();
        mutated_good23_branch["release_instance"]["good23_branches"][0]["accepted"] =
            Value::Bool(true);
        assert!(
            !release_values_match_ignoring_generation_time(&mutated_good23_branch, &live).unwrap()
        );

        let mut arbitrary_source_list = live.clone();
        arbitrary_source_list["source_artifacts"] = json!([{
            "label": "unrelated",
            "path": "/tmp/unrelated.json",
            "bytes": 1,
            "sha256": "33".repeat(32)
        }]);
        assert!(
            !release_values_match_ignoring_generation_time(&arbitrary_source_list, &live).unwrap()
        );
    }

    #[test]
    fn release_instance_rejects_swapped_or_tampered_proof_and_sidecar() {
        let root = TempRoot::new();
        let proof_a = b"profile23-proof-a".to_vec();
        let proof_b = b"profile23-proof-b".to_vec();
        let statement_a = sidecar(&statement(11));
        let statement_b = sidecar(&statement(29));
        let proof_a_path = root.0.join("proof-a.bin");
        let proof_b_path = root.0.join("proof-b.bin");
        let statement_a_path = root.0.join("statement-a.json");
        let statement_b_path = root.0.join("statement-b.json");
        fs::write(&proof_a_path, &proof_a).unwrap();
        fs::write(&proof_b_path, &proof_b).unwrap();
        fs::write(&statement_a_path, &statement_a).unwrap();
        fs::write(&statement_b_path, &statement_b).unwrap();
        let release = release_for("proof-a.bin", &proof_a, "statement-a.json", &statement_a);

        let baseline = validate_release_instance(
            &release,
            &root.0,
            &proof_a_path,
            &proof_a,
            &statement_a_path,
            &statement_a,
        )
        .unwrap();
        assert!(baseline.proof_identity_exact);
        assert!(baseline.statement_identity_exact);

        let swapped_proof = validate_release_instance(
            &release,
            &root.0,
            &proof_b_path,
            &proof_b,
            &statement_a_path,
            &statement_a,
        )
        .unwrap();
        assert!(!swapped_proof.proof_identity_exact);
        assert!(swapped_proof.statement_identity_exact);

        let mut tampered_proof = proof_a.clone();
        tampered_proof[0] ^= 1;
        let tampered_proof = validate_release_instance(
            &release,
            &root.0,
            &proof_a_path,
            &tampered_proof,
            &statement_a_path,
            &statement_a,
        )
        .unwrap();
        assert!(!tampered_proof.proof_identity_exact);

        let swapped_statement = validate_release_instance(
            &release,
            &root.0,
            &proof_a_path,
            &proof_a,
            &statement_b_path,
            &statement_b,
        )
        .unwrap();
        assert!(swapped_statement.proof_identity_exact);
        assert!(!swapped_statement.statement_identity_exact);

        let same_path_tampered_statement = validate_release_instance(
            &release,
            &root.0,
            &proof_a_path,
            &proof_a,
            &statement_a_path,
            &statement_b,
        )
        .unwrap();
        assert!(!same_path_tampered_statement.statement_identity_exact);

        let mut schema_tampered: Value = serde_json::from_slice(&statement_a).unwrap();
        schema_tampered["unreviewed"] = Value::Bool(true);
        assert!(validate_release_instance(
            &release,
            &root.0,
            &proof_a_path,
            &proof_a,
            &statement_a_path,
            &serde_json::to_vec(&schema_tampered).unwrap(),
        )
        .is_err());
    }

    #[test]
    fn nullifier_accepts_only_absent_or_supported_prefunding_shapes() {
        let program_id = Pubkey::new_unique();
        assert!(nullifier_compatible(None, &program_id));
        assert!(nullifier_compatible(
            Some(&RpcAccount {
                lamports: 1,
                owner: system_program::id(),
                executable: false,
                data: Vec::new(),
            }),
            &program_id
        ));
        assert!(!nullifier_compatible(
            Some(&RpcAccount {
                lamports: 1,
                owner: Pubkey::new_unique(),
                executable: false,
                data: Vec::new(),
            }),
            &program_id
        ));
    }

    fn upgradeable_program_snapshot(seed: u8) -> UpgradeableProgramSnapshot {
        UpgradeableProgramSnapshot {
            program_id: Pubkey::new_unique(),
            program: RpcAccount {
                lamports: 11,
                owner: bpf_loader_upgradeable::id(),
                executable: true,
                data: vec![seed, 1, 2],
            },
            programdata_address: Pubkey::new_unique(),
            programdata: RpcAccount {
                lamports: 29,
                owner: bpf_loader_upgradeable::id(),
                executable: false,
                data: vec![seed, 3, 4, 5],
            },
            programdata_slot: 73,
            upgrade_authority_address: Pubkey::new_unique(),
        }
    }

    #[test]
    fn upgradeable_program_continuity_distinguishes_raw_and_data_drift() {
        let baseline = upgradeable_program_snapshot(7);
        assert!(baseline.continuity_from(&baseline).all_unchanged());

        let mut programdata_lamports_changed = baseline.clone();
        programdata_lamports_changed.programdata.lamports += 1;
        let checks = programdata_lamports_changed.continuity_from(&baseline);
        assert!(!checks.programdata_raw_account_image_unchanged);
        assert!(checks.programdata_data_unchanged);
        assert!(checks.programdata_address_unchanged);

        let mut programdata_bytes_changed = baseline.clone();
        programdata_bytes_changed.programdata.data[0] ^= 1;
        let checks = programdata_bytes_changed.continuity_from(&baseline);
        assert!(!checks.programdata_raw_account_image_unchanged);
        assert!(!checks.programdata_data_unchanged);
        assert!(checks.program_raw_account_image_unchanged);
        assert!(checks.program_data_unchanged);

        let mut linked_address_changed = baseline.clone();
        linked_address_changed.programdata_address = Pubkey::new_unique();
        assert!(
            !linked_address_changed
                .continuity_from(&baseline)
                .programdata_address_unchanged
        );

        let mut program_bytes_changed = baseline.clone();
        program_bytes_changed.program.data[0] ^= 1;
        let checks = program_bytes_changed.continuity_from(&baseline);
        assert!(!checks.program_raw_account_image_unchanged);
        assert!(!checks.program_data_unchanged);
        assert!(checks.programdata_raw_account_image_unchanged);
        assert!(checks.programdata_data_unchanged);
    }

    #[test]
    fn upgradeable_program_snapshot_evidence_binds_both_account_addresses() {
        let snapshot = upgradeable_program_snapshot(19);
        let evidence = snapshot.evidence();
        assert_eq!(
            evidence.program_account.address,
            snapshot.program_id.to_string()
        );
        assert_eq!(
            evidence.programdata_address,
            snapshot.programdata_address.to_string()
        );
        assert_eq!(
            evidence.programdata_account.address,
            snapshot.programdata_address.to_string()
        );
        assert_eq!(evidence.programdata_slot, snapshot.programdata_slot);
        assert_eq!(
            evidence.upgrade_authority_address,
            snapshot.upgrade_authority_address.to_string()
        );
    }

    #[test]
    fn evidence_reservation_commits_read_only_json() {
        let path = std::env::temp_dir().join(format!(
            "aspis-profile23-devnet-evidence-test-{}-{}.json",
            std::process::id(),
            chrono::Utc::now().timestamp_nanos_opt().unwrap()
        ));
        let reservation =
            EvidenceReservation::reserve(&path, "profile23_devnet_upload_smoke").unwrap();
        let in_progress: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(in_progress["artifact"], "profile23_devnet_upload_smoke");
        assert_eq!(in_progress["status"], "in_progress_no_claim");
        reservation
            .commit(&json!({"status":"finalized_evidence"}))
            .unwrap();
        let completed: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(completed["status"], "finalized_evidence");
        assert_eq!(
            fs::metadata(&path).unwrap().permissions().mode() & 0o777,
            0o444
        );
        let mut permissions = fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o600);
        fs::set_permissions(&path, permissions).unwrap();
        fs::remove_file(path).unwrap();
    }
}
