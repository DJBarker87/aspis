//! V5/tag-67 devnet and mainnet-beta artifact, readiness, and execution tooling.
//!
//! Artifact generation performs no RPC calls. Readiness performs only
//! filesystem reads and finalized/read-only RPC calls. Each network has a
//! separate execution surface and acknowledgement. Devnet accepts either the
//! isolated probe SBF or frozen production SBF. Mainnet-beta accepts only the
//! frozen SBF, provenance, program ID, genesis, and runtime policy.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, OpenOptions},
    io::Write,
    os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt},
    path::{Component, Path, PathBuf},
    process::Command,
    str::FromStr,
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use borsh::to_vec;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use solana_sdk::{
    account_info::AccountInfo,
    clock::Epoch,
    compute_budget::ComputeBudgetInstruction,
    instruction::{AccountMeta, Instruction},
    message::VersionedMessage,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    transaction::Transaction,
};
#[allow(deprecated)]
use solana_sdk::{system_instruction, system_program};

use aspis_statement::AtomicPaymentStatementV4;
use aspis_verifier::{
    atomic_payment::{
        atomic_nullifier_address, AtomicPoolStateV2, ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT,
        ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_POOL_STATE_LEN,
    },
    AspisInstruction, PROOF_ACCOUNT_HEADER_LEN,
};

use super::{
    custom_simulation_error, deploy_if_needed, deployed_program_exact, exact_regular_file,
    expected_nullifier_marker, expected_proof_account, initialized_pool_account_exact,
    invalid_account_data_simulation_error, proof_instruction, rpc_origin, secure_keypair, sha256,
    signed_transaction, statement_public_inputs, upload_proof_chunks, zeroed_pool_account_exact,
    AccountEvidence, ClusterPolicy, DevnetConfig, EvidenceReservation, Rpc, TransactionEvidence,
    UpgradeableProgramContinuityChecks, UpgradeableProgramSnapshotEvidence, BUFFER_METADATA_BYTES,
    CU_LIMIT, HEAP_FRAME_BYTES, PROGRAMDATA_METADATA_BYTES, PROGRAM_ACCOUNT_BYTES,
    UPLOAD_CHUNK_BYTES, UPLOAD_WINDOW_TRANSACTIONS,
};
use crate::{
    spend_statement::{
        canonical_spend_public_input_digest, decode_spend_statement_sidecar, spend_hex,
        SPEND_STATEMENT_ARTIFACT, SPEND_STATEMENT_SELECTION_RULE,
    },
    v5_cu_probe::{
        build_v5_runtime_bound_production_demo_proof_body, build_v5_tag67_transaction_wire,
    },
};

const DEVNET_DOMAIN_TAG: &[u8] = b"devnet";
const DEVNET_GENESIS_HASH: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG";
const MAINNET_BETA_DOMAIN_TAG: &[u8] = b"mainnet-beta";
const MAINNET_BETA_GENESIS_HASH: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const SBF_PROVENANCE_ARTIFACT: &str = "aspis_v5_devnet_sbf_provenance";
const SBF_PROVENANCE_SCHEMA_VERSION: u32 = 1;
const SBF_FEATURE: &str = "v5-cu-probe";
const FROZEN_PRODUCTION_PROVENANCE_ARTIFACT: &str = "aspis_v5_production_tag67_sbf_provenance";
const FROZEN_PRODUCTION_PROVENANCE_SCHEMA_VERSION: u32 = 2;
const FROZEN_PRODUCTION_FEATURE: &str = "v5-production-tag67";
const FROZEN_PRODUCTION_SBF_BYTES: usize = 1_258_496;
const FROZEN_PRODUCTION_SBF_SHA256: &str =
    "4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40";
const FROZEN_PRODUCTION_PROVENANCE_SHA256: &str =
    "a7c9f7bea70d9805d8aff093fad309c911c752f2d47f6ad489c2f2eda1d7c3ec";
const FROZEN_PRODUCTION_SOURCE_IDENTITIES: usize = 77;
const FROZEN_PRODUCTION_TOOLCHAIN_IDENTITIES: usize = 91;
const PLATFORM_TOOLS_VERSION: &str = "v1.48";
const MAINNET_RUNTIME_SOLANA_CORE: &str = "4.1.0";
const MAINNET_RUNTIME_FEATURE_SET: u64 = 3_345_198_602;
const MAINNET_RUNTIME_REPLAY_SHA256: &str =
    "00323072e02a9836db8bb4947e1dea0a17f1d0ab1088be0940580c319587e154";
const MAINNET_PREFUNDED_MARKER_REPLAY_SHA256: &str =
    "2d62930963fa67b247a746ec81e3b1614391710a69df528fc2a28361407e819f";
const MAINNET_SOLANA_CLI_SHA256: &str =
    "ad541533b992ff4ee1ea0f24e583a0ef26a5b80fa3482b5f930b5e6db707747c";
const MAINNET_SOLANA_CLI_VERSION: &str =
    "solana-cli 4.1.0 (src:d3f1f55c; feat:c763ae0a, client:Agave)";
const MAX_MAINNET_COMPUTE_UNIT_PRICE_MICROLAMPORTS: u64 = 1_000_000;
const CONSERVATIVE_SIGNATURE_FEE_LAMPORTS_PER_TRANSACTION: u64 = 200_000;
const SBF_OUTPUT_NAME: &str = "aspis_verifier.so";
const DEVNET_EXECUTE_ACK: &str =
    "I_ACKNOWLEDGE_V5_TAG67_DEVNET_EXECUTION_MUTATES_DEVNET_AND_SPENDS_DEVNET_SOL";
const MAINNET_EXECUTE_ACK: &str = "I_ACKNOWLEDGE_V5_TAG67_MAINNET_BETA_EXECUTION_IS_IRREVERSIBLE_MUTATES_MAINNET_AND_SPENDS_REAL_SOL";
const DEVNET_TAG67_INSTRUCTION_INDEX: u64 = 2;
const MAINNET_TAG67_INSTRUCTION_INDEX: u64 = 3;
const READINESS_VALUE_ARGUMENTS: [&str; 18] = [
    "--rpc-url",
    "--ws-url",
    "--payer-keypair",
    "--program-keypair",
    "--pool-keypair",
    "--proof-account-keypair",
    "--sbf",
    "--sbf-provenance",
    "--proof",
    "--statement",
    "--program-max-len",
    "--fee-reserve-lamports",
    "--expected-solana-core",
    "--expected-feature-set",
    "--upgrade-authority-keypair",
    "--deployment-buffer-keypair",
    "--runtime-replay",
    "--compute-unit-price-microlamports",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V5NetworkPolicy {
    Devnet,
    MainnetBeta,
}

impl V5NetworkPolicy {
    const fn network(self) -> &'static str {
        match self {
            Self::Devnet => "devnet",
            Self::MainnetBeta => "mainnet-beta",
        }
    }

    const fn domain_tag(self) -> &'static [u8] {
        match self {
            Self::Devnet => DEVNET_DOMAIN_TAG,
            Self::MainnetBeta => MAINNET_BETA_DOMAIN_TAG,
        }
    }

    const fn expected_genesis_hash(self) -> &'static str {
        match self {
            Self::Devnet => DEVNET_GENESIS_HASH,
            Self::MainnetBeta => MAINNET_BETA_GENESIS_HASH,
        }
    }

    const fn execute_flag(self) -> &'static str {
        match self {
            Self::Devnet => "--execute-devnet",
            Self::MainnetBeta => "--execute-mainnet-beta",
        }
    }

    const fn execute_acknowledgement(self) -> &'static str {
        match self {
            Self::Devnet => DEVNET_EXECUTE_ACK,
            Self::MainnetBeta => MAINNET_EXECUTE_ACK,
        }
    }

    const fn artifact_name(self) -> &'static str {
        match self {
            Self::Devnet => "aspis_v5_devnet_artifact",
            Self::MainnetBeta => "aspis_v5_mainnet_beta_artifact",
        }
    }

    const fn readiness_name(self) -> &'static str {
        match self {
            Self::Devnet => "aspis_v5_devnet_readiness",
            Self::MainnetBeta => "aspis_v5_mainnet_beta_readiness",
        }
    }

    const fn evidence_name(self) -> &'static str {
        match self {
            Self::Devnet => "aspis_v5_tag67_devnet_execution",
            Self::MainnetBeta => "aspis_v5_tag67_mainnet_beta_execution",
        }
    }

    const fn cluster_policy(self) -> ClusterPolicy {
        match self {
            Self::Devnet => ClusterPolicy::Devnet,
            Self::MainnetBeta => ClusterPolicy::MainnetBeta,
        }
    }

    const fn requires_frozen_production(self) -> bool {
        matches!(self, Self::MainnetBeta)
    }

    fn validate_program_id(self, program_id: Pubkey) -> Result<()> {
        if self == Self::MainnetBeta {
            ensure!(
                program_id == aspis_verifier::id(),
                "v5 mainnet-beta requires the program keypair to equal aspis_verifier::id()"
            );
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct ArtifactConfig {
    network: V5NetworkPolicy,
    program_id: Pubkey,
    pool: Pubkey,
    proof_output: PathBuf,
    statement_output: PathBuf,
}

#[derive(Clone, Debug)]
struct BuildConfig {
    cargo_build_sbf: PathBuf,
    sbf_sdk: PathBuf,
    platform_tools_root: PathBuf,
    build_output_dir: PathBuf,
    sbf_output: PathBuf,
    provenance_output: PathBuf,
}

#[derive(Clone, Debug)]
struct ReadinessConfig {
    network: V5NetworkPolicy,
    rpc_url: String,
    ws_url: Option<String>,
    payer_keypair: PathBuf,
    program_keypair: PathBuf,
    pool_keypair: PathBuf,
    proof_account_keypair: PathBuf,
    sbf: PathBuf,
    sbf_provenance: PathBuf,
    proof: PathBuf,
    statement: PathBuf,
    program_max_len: usize,
    fee_reserve_lamports: u64,
    expected_solana_core: Option<String>,
    expected_feature_set: Option<u64>,
    upgrade_authority_keypair: Option<PathBuf>,
    deployment_buffer_keypair: Option<PathBuf>,
    runtime_replay: Option<PathBuf>,
    compute_unit_price_microlamports: Option<u64>,
}

#[derive(Clone, Debug)]
struct ExecuteConfig {
    readiness: ReadinessConfig,
    readiness_arguments: Vec<String>,
    solana_cli: PathBuf,
    evidence: PathBuf,
    run_directory: Option<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceFileIdentity {
    path: String,
    bytes: usize,
    sha256: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct V5SbfProvenance {
    artifact: String,
    schema_version: u32,
    generated_at_utc: String,
    git_head: String,
    cargo_build_sbf_path: String,
    cargo_build_sbf_bytes: usize,
    cargo_build_sbf_sha256: String,
    cargo_build_sbf_version: String,
    sbf_sdk_path: String,
    platform_tools_root: String,
    platform_tools_version: String,
    toolchain_files: Vec<SourceFileIdentity>,
    manifest_path: String,
    no_default_features: bool,
    features: Vec<String>,
    command: Vec<String>,
    build_output_dir: String,
    cargo_target_dir: String,
    built_artifact_path: String,
    build_stdout_sha256: Option<String>,
    build_stderr_sha256: Option<String>,
    cargo_lock_sha256: String,
    source_files: Vec<SourceFileIdentity>,
    sbf_path: String,
    sbf_bytes: usize,
    sbf_sha256: String,
    #[serde(default)]
    capture_note: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V5SbfProfile {
    FeatureProbe,
    FrozenProduction,
}

impl V5SbfProfile {
    const fn feature(self) -> &'static str {
        match self {
            Self::FeatureProbe => SBF_FEATURE,
            Self::FrozenProduction => FROZEN_PRODUCTION_FEATURE,
        }
    }

    const fn label(self) -> &'static str {
        match self {
            Self::FeatureProbe => "v5-cu-probe",
            Self::FrozenProduction => "frozen-production-tag67",
        }
    }

    const fn execution_scope(self) -> &'static str {
        match self {
            Self::FeatureProbe => {
                "Feature-only tag-67 devnet execution through the isolated probe entrypoint."
            }
            Self::FrozenProduction => {
                "Exact frozen production Tag-67 SBF executed through the default atomic dispatcher."
            }
        }
    }
}

fn validate_sbf_profile_for_network(network: V5NetworkPolicy, profile: V5SbfProfile) -> Result<()> {
    ensure!(
        !network.requires_frozen_production() || profile == V5SbfProfile::FrozenProduction,
        "v5 mainnet-beta accepts only the exact frozen-production SBF and provenance"
    );
    Ok(())
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V5DevnetBuildOutcome {
    pub(crate) artifact: &'static str,
    pub(crate) sbf_path: String,
    pub(crate) sbf_bytes: usize,
    pub(crate) sbf_sha256: String,
    pub(crate) provenance_path: String,
    pub(crate) provenance_bytes: usize,
    pub(crate) provenance_sha256: String,
    pub(crate) git_head: String,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V5DevnetArtifactOutcome {
    pub(crate) artifact: &'static str,
    pub(crate) network: &'static str,
    pub(crate) program_id: String,
    pub(crate) pool: String,
    pub(crate) sequence: u64,
    pub(crate) deployment_domain_hex: String,
    pub(crate) proof_path: String,
    pub(crate) proof_bytes: usize,
    pub(crate) proof_sha256: String,
    pub(crate) statement_path: String,
    pub(crate) statement_bytes: usize,
    pub(crate) statement_sha256: String,
    pub(crate) canonical_public_input_digest: String,
    pub(crate) least_good_selector: u8,
    pub(crate) successful_attempt_index: u8,
    pub(crate) host_verification_green: bool,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V5DevnetReadiness {
    pub(crate) artifact: &'static str,
    pub(crate) generated_at_utc: String,
    pub(crate) mode: &'static str,
    pub(crate) mutations_performed: bool,
    pub(crate) ready: bool,
    pub(crate) execution_enabled: bool,
    pub(crate) execution_stop_reason: Option<&'static str>,
    pub(crate) rpc_origin_redacted: String,
    pub(crate) ws_origin_redacted: Option<String>,
    pub(crate) expected_genesis_hash: &'static str,
    pub(crate) observed_genesis_hash: String,
    pub(crate) expected_solana_core: Option<String>,
    pub(crate) observed_solana_core: Option<String>,
    pub(crate) expected_feature_set: Option<u64>,
    pub(crate) observed_feature_set: Option<u64>,
    pub(crate) runtime_replay_path: Option<String>,
    pub(crate) runtime_replay_sha256: Option<String>,
    pub(crate) compute_unit_price_microlamports: Option<u64>,
    pub(crate) program_id: String,
    pub(crate) upgrade_authority: Option<String>,
    pub(crate) deployment_buffer: Option<String>,
    pub(crate) pool: String,
    pub(crate) proof_account: String,
    pub(crate) nullifier_address: String,
    pub(crate) program_already_deployed: bool,
    pub(crate) proof_bytes: usize,
    pub(crate) proof_sha256: String,
    pub(crate) statement_bytes: usize,
    pub(crate) statement_sha256: String,
    pub(crate) sbf_bytes: usize,
    pub(crate) sbf_sha256: String,
    pub(crate) sbf_provenance_path: String,
    pub(crate) sbf_provenance_sha256: String,
    pub(crate) sbf_profile: &'static str,
    pub(crate) sbf_build_command: Vec<String>,
    pub(crate) sbf_source_file_count: usize,
    pub(crate) canonical_public_input_digest: String,
    pub(crate) least_good_selector: u8,
    pub(crate) good_candidates: [bool; 3],
    pub(crate) payer_balance_lamports: u64,
    pub(crate) required_lamports: u64,
    pub(crate) surplus_lamports: i128,
    pub(crate) rust_signed_transaction_count: Option<usize>,
    pub(crate) rust_signed_priority_and_signature_fee_bound_lamports: Option<u64>,
    pub(crate) explicit_nonclaims: [&'static str; 3],
}

#[derive(Clone, Debug, Serialize)]
struct V5Tag67AccountMetaEvidence {
    index: usize,
    role: &'static str,
    address: String,
    is_signer: bool,
    is_writable: bool,
}

#[derive(Clone, Debug, Serialize)]
struct V5RetainedProofBalanceEvidence {
    fee_lamports: u64,
    payer_account_index: usize,
    proof_account_index: usize,
    nullifier_account_index: usize,
    payer_pre_lamports: u64,
    payer_post_lamports: u64,
    proof_pre_lamports: u64,
    proof_post_lamports: u64,
    nullifier_pre_lamports: u64,
    nullifier_post_lamports: u64,
    nullifier_funding_lamports: u64,
    exact_balance_equation_reconciled: bool,
    proof_balance_retained_exactly: bool,
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct V5DevnetExecutionEvidence {
    pub(crate) artifact: &'static str,
    pub(crate) generated_at_utc: String,
    pub(crate) network: &'static str,
    pub(crate) genesis_hash: String,
    rpc_origin_redacted: String,
    ws_origin_redacted: Option<String>,
    readiness: V5DevnetReadiness,
    program_id: String,
    payer: String,
    pool: String,
    proof_account: String,
    nullifier_address: String,
    solana_cli_path: String,
    solana_cli_bytes: usize,
    solana_cli_sha256: String,
    solana_cli_version: Option<String>,
    sbf_path: String,
    sbf_bytes: usize,
    sbf_sha256: String,
    sbf_provenance_path: String,
    sbf_provenance_sha256: String,
    proof_path: String,
    proof_bytes: usize,
    proof_sha256: String,
    statement_path: String,
    statement_sha256: String,
    canonical_public_input_digest: String,
    least_good_selector: u8,
    good_candidates: [bool; 3],
    program_max_len: usize,
    deployment: Option<TransactionEvidence>,
    setup_transactions: Vec<TransactionEvidence>,
    proof_upload_chunk_bytes: usize,
    proof_upload_transaction_count: usize,
    proof_upload_finality_windows: usize,
    upgradeable_program_before_setup: UpgradeableProgramSnapshotEvidence,
    upgradeable_program_before_final_simulation: UpgradeableProgramSnapshotEvidence,
    upgradeable_program_before_final_simulation_continuity: UpgradeableProgramContinuityChecks,
    upgradeable_program_after_finality: UpgradeableProgramSnapshotEvidence,
    upgradeable_program_after_finality_continuity: UpgradeableProgramContinuityChecks,
    pool_before: AccountEvidence,
    pool_after: AccountEvidence,
    sequence_before: u64,
    sequence_after: u64,
    current_anchor_hex: String,
    output_anchor_hex: String,
    deployment_domain_hex: String,
    sealed_proof_before: AccountEvidence,
    retained_proof_after: AccountEvidence,
    retained_proof_byte_for_byte_exact: bool,
    post_finalize_upload_rejected: bool,
    post_finalize_upload_error: Value,
    post_finalize_second_finalize_rejected: bool,
    post_finalize_second_finalize_error: Value,
    tag67_instruction_bytes: usize,
    tag67_instruction_sha256: String,
    tag67_account_metas: Vec<V5Tag67AccountMetaEvidence>,
    tag67_compute_unit_limit: u32,
    tag67_heap_frame_bytes: u32,
    tag67_compute_unit_price_microlamports: Option<u64>,
    pub(crate) final_transaction: TransactionEvidence,
    final_transaction_simulation_cu: u64,
    final_transaction_landed_cu: u64,
    final_transaction_wire_sha256: String,
    final_transaction_message_sha256: String,
    final_transaction_submitted_identically_to_simulation: bool,
    final_transaction_refetched_wire_exact: bool,
    final_transaction_refetched_message_exact: bool,
    final_transaction_program_success_log_exact: bool,
    retained_proof_balance_equation: V5RetainedProofBalanceEvidence,
    nullifier_observed_before_simulation: Option<AccountEvidence>,
    nullifier_landing_path: &'static str,
    nullifier_after: AccountEvidence,
    nullifier_marker_rent_lamports: u64,
    replay_simulation_rejected: bool,
    replay_simulation_error: Value,
    replay_expected_nullifier_error_exact: bool,
    replay_pool_unchanged: bool,
    replay_nullifier_unchanged: bool,
    replay_proof_unchanged: bool,
    pub(crate) evidence_path: String,
    evidence_file_mode: u32,
    explicit_scope: [&'static str; 4],
}

fn parse_explicit_arguments(
    arguments: &[String],
    allowed_values: &[&str],
) -> Result<BTreeMap<String, String>> {
    let mut values = BTreeMap::new();
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        ensure!(
            key.starts_with("--"),
            "unexpected positional argument {key}"
        );
        ensure!(
            allowed_values.contains(&key.as_str()),
            "unknown argument {key}"
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
    Ok(values)
}

fn required(values: &BTreeMap<String, String>, key: &str) -> Result<String> {
    values
        .get(key)
        .cloned()
        .ok_or_else(|| anyhow!("missing required explicit argument {key}"))
}

fn absolute(values: &BTreeMap<String, String>, key: &str) -> Result<PathBuf> {
    let path = PathBuf::from(required(values, key)?);
    ensure!(path.is_absolute(), "{key} must be an absolute path");
    ensure!(
        path.components()
            .all(|component| matches!(component, Component::RootDir | Component::Normal(_))),
        "{key} must be lexically normal"
    );
    Ok(path)
}

fn parse_build_args(arguments: &[String]) -> Result<BuildConfig> {
    let values = parse_explicit_arguments(
        arguments,
        &[
            "--cargo-build-sbf",
            "--sbf-sdk",
            "--platform-tools-root",
            "--build-output-dir",
            "--sbf-out",
            "--provenance-out",
        ],
    )?;
    let config = BuildConfig {
        cargo_build_sbf: absolute(&values, "--cargo-build-sbf")?,
        sbf_sdk: absolute(&values, "--sbf-sdk")?,
        platform_tools_root: absolute(&values, "--platform-tools-root")?,
        build_output_dir: absolute(&values, "--build-output-dir")?,
        sbf_output: absolute(&values, "--sbf-out")?,
        provenance_output: absolute(&values, "--provenance-out")?,
    };
    ensure!(
        config.sbf_output != config.provenance_output,
        "SBF and provenance outputs must differ"
    );
    ensure!(
        config.build_output_dir != config.sbf_output
            && config.build_output_dir != config.provenance_output,
        "isolated build directory must differ from durable outputs"
    );
    ensure!(
        !config.sbf_output.starts_with(&config.build_output_dir)
            && !config
                .provenance_output
                .starts_with(&config.build_output_dir),
        "durable outputs must be outside the isolated build directory"
    );
    Ok(config)
}

fn parse_artifact_args_for(
    arguments: &[String],
    network: V5NetworkPolicy,
) -> Result<ArtifactConfig> {
    let values = parse_explicit_arguments(
        arguments,
        &[
            "--network",
            "--program-id",
            "--pool",
            "--sequence",
            "--proof-out",
            "--statement-out",
        ],
    )?;
    ensure!(
        required(&values, "--network")? == network.network(),
        "v5 artifact network must be {}",
        network.network()
    );
    ensure!(
        required(&values, "--sequence")? == "0",
        "v5 artifact generation is restricted to fresh sequence 0"
    );
    let proof_output = absolute(&values, "--proof-out")?;
    let statement_output = absolute(&values, "--statement-out")?;
    ensure!(
        proof_output != statement_output,
        "proof and statement outputs must differ"
    );
    let program_id =
        Pubkey::from_str(&required(&values, "--program-id")?).context("invalid --program-id")?;
    network.validate_program_id(program_id)?;
    Ok(ArtifactConfig {
        network,
        program_id,
        pool: Pubkey::from_str(&required(&values, "--pool")?).context("invalid --pool")?,
        proof_output,
        statement_output,
    })
}

fn parse_artifact_args(arguments: &[String]) -> Result<ArtifactConfig> {
    parse_artifact_args_for(arguments, V5NetworkPolicy::Devnet)
}

fn parse_mainnet_artifact_args(arguments: &[String]) -> Result<ArtifactConfig> {
    parse_artifact_args_for(arguments, V5NetworkPolicy::MainnetBeta)
}

fn parse_readiness_args_for(
    arguments: &[String],
    network: V5NetworkPolicy,
) -> Result<ReadinessConfig> {
    let values = parse_explicit_arguments(arguments, &READINESS_VALUE_ARGUMENTS)?;
    let (
        expected_solana_core,
        expected_feature_set,
        upgrade_authority_keypair,
        deployment_buffer_keypair,
        runtime_replay,
        compute_unit_price_microlamports,
    ) = match network {
        V5NetworkPolicy::Devnet => {
            ensure!(
                !values.contains_key("--ws-url")
                    && !values.contains_key("--expected-solana-core")
                    && !values.contains_key("--expected-feature-set")
                    && !values.contains_key("--upgrade-authority-keypair")
                    && !values.contains_key("--deployment-buffer-keypair")
                    && !values.contains_key("--runtime-replay")
                    && !values.contains_key("--compute-unit-price-microlamports"),
                "runtime and deployment-authority gates are mainnet-beta-only arguments"
            );
            (None, None, None, None, None, None)
        }
        V5NetworkPolicy::MainnetBeta => {
            let expected_solana_core = required(&values, "--expected-solana-core")?;
            ensure!(
                expected_solana_core == MAINNET_RUNTIME_SOLANA_CORE,
                "v5 mainnet-beta is pinned to the replayed solana-core {MAINNET_RUNTIME_SOLANA_CORE}; a new runtime replay and policy update are required"
            );
            let expected_feature_set = required(&values, "--expected-feature-set")?
                .parse::<u64>()
                .context("--expected-feature-set is not u64")?;
            ensure!(
                expected_feature_set == MAINNET_RUNTIME_FEATURE_SET,
                "v5 mainnet-beta is pinned to feature-set {MAINNET_RUNTIME_FEATURE_SET}; a new runtime replay and policy update are required"
            );
            let compute_unit_price_microlamports =
                required(&values, "--compute-unit-price-microlamports")?
                    .parse::<u64>()
                    .context("--compute-unit-price-microlamports is not u64")?;
            ensure!(
                compute_unit_price_microlamports
                    <= MAX_MAINNET_COMPUTE_UNIT_PRICE_MICROLAMPORTS,
                "--compute-unit-price-microlamports exceeds the operator safety cap of {MAX_MAINNET_COMPUTE_UNIT_PRICE_MICROLAMPORTS}"
            );
            (
                Some(expected_solana_core),
                Some(expected_feature_set),
                Some(absolute(&values, "--upgrade-authority-keypair")?),
                Some(absolute(&values, "--deployment-buffer-keypair")?),
                Some(absolute(&values, "--runtime-replay")?),
                Some(compute_unit_price_microlamports),
            )
        }
    };
    Ok(ReadinessConfig {
        network,
        rpc_url: required(&values, "--rpc-url")?,
        ws_url: match network {
            V5NetworkPolicy::Devnet => None,
            V5NetworkPolicy::MainnetBeta => Some(required(&values, "--ws-url")?),
        },
        payer_keypair: absolute(&values, "--payer-keypair")?,
        program_keypair: absolute(&values, "--program-keypair")?,
        pool_keypair: absolute(&values, "--pool-keypair")?,
        proof_account_keypair: absolute(&values, "--proof-account-keypair")?,
        sbf: absolute(&values, "--sbf")?,
        sbf_provenance: absolute(&values, "--sbf-provenance")?,
        proof: absolute(&values, "--proof")?,
        statement: absolute(&values, "--statement")?,
        program_max_len: required(&values, "--program-max-len")?
            .parse()
            .context("--program-max-len is not usize")?,
        fee_reserve_lamports: required(&values, "--fee-reserve-lamports")?
            .parse()
            .context("--fee-reserve-lamports is not u64")?,
        expected_solana_core,
        expected_feature_set,
        upgrade_authority_keypair,
        deployment_buffer_keypair,
        runtime_replay,
        compute_unit_price_microlamports,
    })
}

fn parse_readiness_args(arguments: &[String]) -> Result<ReadinessConfig> {
    parse_readiness_args_for(arguments, V5NetworkPolicy::Devnet)
}

fn parse_mainnet_readiness_args(arguments: &[String]) -> Result<ReadinessConfig> {
    parse_readiness_args_for(arguments, V5NetworkPolicy::MainnetBeta)
}

fn parse_execute_args_for(arguments: &[String], network: V5NetworkPolicy) -> Result<ExecuteConfig> {
    let mut readiness_arguments = Vec::new();
    let mut execution_values = BTreeMap::<String, String>::new();
    let mut execute_interlock = false;
    let mut index = 0usize;
    while index < arguments.len() {
        let key = &arguments[index];
        if key == network.execute_flag() {
            ensure!(!execute_interlock, "duplicate {}", network.execute_flag());
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
        if READINESS_VALUE_ARGUMENTS.contains(&key.as_str()) {
            readiness_arguments.push(key.clone());
            readiness_arguments.push(value.clone());
        } else {
            let allowed_execution_values: &[&str] = match network {
                V5NetworkPolicy::Devnet => &["--solana-cli", "--evidence", "--acknowledgement"],
                V5NetworkPolicy::MainnetBeta => &[
                    "--solana-cli",
                    "--evidence",
                    "--acknowledgement",
                    "--run-directory",
                ],
            };
            ensure!(
                allowed_execution_values.contains(&key.as_str()),
                "unknown v5 {} execution argument {key}",
                network.network()
            );
            ensure!(
                execution_values
                    .insert(key.clone(), value.clone())
                    .is_none(),
                "duplicate argument {key}"
            );
        }
        index += 2;
    }
    ensure!(
        execute_interlock,
        "v5 tag-67 {} execution requires {}",
        network.network(),
        network.execute_flag()
    );
    ensure!(
        required(&execution_values, "--acknowledgement")? == network.execute_acknowledgement(),
        "v5 tag-67 {} execution acknowledgement mismatch",
        network.network()
    );
    let readiness = parse_readiness_args_for(&readiness_arguments, network)?;
    let solana_cli = absolute(&execution_values, "--solana-cli")?;
    let evidence = absolute(&execution_values, "--evidence")?;
    let run_directory = match network {
        V5NetworkPolicy::Devnet => None,
        V5NetworkPolicy::MainnetBeta => Some(absolute(&execution_values, "--run-directory")?),
    };
    ensure!(
        solana_cli != evidence,
        "Solana CLI and evidence paths must differ"
    );
    for protected in [
        &readiness.payer_keypair,
        &readiness.program_keypair,
        &readiness.pool_keypair,
        &readiness.proof_account_keypair,
        &readiness.sbf,
        &readiness.sbf_provenance,
        &readiness.proof,
        &readiness.statement,
    ] {
        ensure!(
            &evidence != protected,
            "evidence path aliases a v5 execution input"
        );
    }
    for protected in [
        readiness.upgrade_authority_keypair.as_ref(),
        readiness.deployment_buffer_keypair.as_ref(),
        readiness.runtime_replay.as_ref(),
    ]
    .into_iter()
    .flatten()
    {
        ensure!(
            &evidence != protected,
            "evidence path aliases a v5 mainnet deployment input"
        );
    }
    if let Some(run_directory) = &run_directory {
        ensure!(
            run_directory != &evidence
                && !evidence.starts_with(run_directory)
                && !run_directory.starts_with(&evidence),
            "mainnet run directory and evidence path must not overlap"
        );
        for protected in [
            &readiness.payer_keypair,
            &readiness.program_keypair,
            &readiness.pool_keypair,
            &readiness.proof_account_keypair,
            &readiness.sbf,
            &readiness.sbf_provenance,
            &readiness.proof,
            &readiness.statement,
            &solana_cli,
        ] {
            ensure!(
                !protected.starts_with(run_directory) && !run_directory.starts_with(protected),
                "mainnet run directory overlaps a v5 execution input"
            );
        }
        for protected in [
            readiness.upgrade_authority_keypair.as_ref(),
            readiness.deployment_buffer_keypair.as_ref(),
            readiness.runtime_replay.as_ref(),
        ]
        .into_iter()
        .flatten()
        {
            ensure!(
                !protected.starts_with(run_directory) && !run_directory.starts_with(protected),
                "mainnet run directory overlaps a v5 deployment input"
            );
        }
    }
    Ok(ExecuteConfig {
        readiness,
        readiness_arguments,
        solana_cli,
        evidence,
        run_directory,
    })
}

fn parse_execute_args(arguments: &[String]) -> Result<ExecuteConfig> {
    parse_execute_args_for(arguments, V5NetworkPolicy::Devnet)
}

fn parse_mainnet_execute_args(arguments: &[String]) -> Result<ExecuteConfig> {
    parse_execute_args_for(arguments, V5NetworkPolicy::MainnetBeta)
}

fn workspace_root() -> Result<PathBuf> {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .map(Path::to_path_buf)
        .context("xtask manifest has no workspace parent")
}

fn path_string(path: &Path) -> Result<String> {
    path.to_str()
        .map(ToOwned::to_owned)
        .with_context(|| format!("path is not UTF-8: {}", path.display()))
}

fn ensure_normal_absolute_path(path: &Path, label: &str) -> Result<()> {
    ensure!(path.is_absolute(), "{label} must be absolute");
    ensure!(
        path.components()
            .all(|component| matches!(component, Component::RootDir | Component::Normal(_))),
        "{label} must be lexically normal"
    );
    Ok(())
}

fn collect_regular_files(path: &Path, output: &mut BTreeSet<PathBuf>) -> Result<()> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("inventory path unavailable: {}", path.display()))?;
    ensure!(
        !metadata.file_type().is_symlink(),
        "inventory rejects symlink: {}",
        path.display()
    );
    if metadata.file_type().is_file() {
        output.insert(path.to_path_buf());
        return Ok(());
    }
    ensure!(
        metadata.file_type().is_dir(),
        "inventory path is neither file nor directory: {}",
        path.display()
    );
    let mut children = fs::read_dir(path)
        .with_context(|| format!("read inventory directory: {}", path.display()))?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<std::io::Result<Vec<_>>>()?;
    children.sort();
    for child in children {
        collect_regular_files(&child, output)?;
    }
    Ok(())
}

fn identities_from_paths(
    paths: BTreeSet<PathBuf>,
    label_base: Option<&Path>,
) -> Result<Vec<SourceFileIdentity>> {
    paths
        .into_iter()
        .map(|path| {
            let bytes = exact_regular_file(&path)?;
            let label_path = match label_base {
                Some(base) => path.strip_prefix(base).with_context(|| {
                    format!(
                        "inventory path {} escaped base {}",
                        path.display(),
                        base.display()
                    )
                })?,
                None => path.as_path(),
            };
            Ok(SourceFileIdentity {
                path: path_string(label_path)?,
                bytes: bytes.len(),
                sha256: sha256(&bytes),
            })
        })
        .collect()
}

fn source_inventory(root: &Path) -> Result<Vec<SourceFileIdentity>> {
    let mut paths = BTreeSet::new();
    for relative in [
        "Cargo.toml",
        "Cargo.lock",
        "programs/aspis-verifier/Cargo.toml",
        "programs/aspis-verifier/src",
        "crates/aspis-core/Cargo.toml",
        "crates/aspis-core/src",
        "crates/aspis-statement/Cargo.toml",
        "crates/aspis-statement/src",
    ] {
        collect_regular_files(&root.join(relative), &mut paths)?;
    }
    for relative in [
        "programs/aspis-verifier/build.rs",
        "crates/aspis-core/build.rs",
        "crates/aspis-statement/build.rs",
    ] {
        let path = root.join(relative);
        if path.try_exists()? {
            collect_regular_files(&path, &mut paths)?;
        }
    }
    identities_from_paths(paths, Some(root))
}

fn validate_sdk_dependency_links(config: &BuildConfig) -> Result<()> {
    let platform_tools_link = config.sbf_sdk.join("dependencies/platform-tools");
    let metadata = fs::symlink_metadata(&platform_tools_link).with_context(|| {
        format!(
            "SBF SDK platform-tools link unavailable: {}",
            platform_tools_link.display()
        )
    })?;
    ensure!(
        metadata.file_type().is_symlink(),
        "SBF SDK platform-tools dependency must be an explicit symlink"
    );
    ensure!(
        fs::canonicalize(&platform_tools_link)? == fs::canonicalize(&config.platform_tools_root)?,
        "SBF SDK platform-tools dependency differs from --platform-tools-root"
    );

    let criterion_link = config.sbf_sdk.join("dependencies/criterion");
    let criterion_metadata = fs::symlink_metadata(&criterion_link).with_context(|| {
        format!(
            "SBF SDK criterion link unavailable: {}",
            criterion_link.display()
        )
    })?;
    ensure!(
        criterion_metadata.file_type().is_symlink(),
        "SBF SDK criterion dependency must remain an explicit, untraversed symlink"
    );
    Ok(())
}

fn toolchain_inventory(config: &BuildConfig) -> Result<Vec<SourceFileIdentity>> {
    validate_sdk_dependency_links(config)?;
    let mut paths = BTreeSet::new();
    for relative in [
        "c",
        "scripts",
        "env.sh",
        "syscalls.txt",
        "dependencies/criterion-v2.3.2.md",
        "dependencies/platform-tools-v1.48.md",
    ] {
        collect_regular_files(&config.sbf_sdk.join(relative), &mut paths)?;
    }
    for relative in [
        "rust/bin/cargo",
        "rust/bin/rustc",
        "rust/lib/rustlib/sbpf-solana-solana",
        "llvm/bin/clang-19",
        "llvm/bin/llc",
        "llvm/bin/lld",
        "llvm/bin/llvm-ar",
        "llvm/bin/llvm-objcopy",
        "llvm/bin/llvm-objdump",
        "llvm/bin/llvm-readobj",
        "llvm/lib/sbpf",
    ] {
        collect_regular_files(&config.platform_tools_root.join(relative), &mut paths)?;
    }
    identities_from_paths(paths, None)
}

fn exact_executable(path: &Path) -> Result<Vec<u8>> {
    let bytes = exact_regular_file(path)?;
    let metadata = fs::symlink_metadata(path)?;
    ensure!(
        metadata.permissions().mode() & 0o111 != 0,
        "build tool is not executable: {}",
        path.display()
    );
    Ok(bytes)
}

fn websocket_origin(endpoint: &str) -> Result<String> {
    let url = reqwest::Url::parse(endpoint).context("invalid WebSocket URL")?;
    ensure!(
        url.scheme() == "wss",
        "mainnet WebSocket endpoint must use WSS"
    );
    ensure!(
        url.username().is_empty() && url.password().is_none(),
        "WebSocket credentials may not use URL userinfo"
    );
    let host = url.host_str().context("WebSocket URL omitted host")?;
    Ok(format!(
        "wss://{}{}<redacted>",
        host,
        url.port()
            .map(|port| format!(":{port}/"))
            .unwrap_or_else(|| "/".to_owned())
    ))
}

fn validate_execution_solana_cli(
    network: V5NetworkPolicy,
    path: &Path,
    bytes: &[u8],
) -> Result<Option<String>> {
    if network == V5NetworkPolicy::Devnet {
        return Ok(None);
    }
    ensure!(
        sha256(bytes) == MAINNET_SOLANA_CLI_SHA256,
        "mainnet execution requires the exact reviewed Agave 4.1.0 Solana CLI binary"
    );
    let version = command_output_utf8(
        Command::new(path).arg("--version"),
        "mainnet solana --version",
    )?;
    ensure!(
        version == MAINNET_SOLANA_CLI_VERSION,
        "mainnet Solana CLI version differs from the reviewed Agave 4.1.0 identity"
    );
    Ok(Some(version))
}

fn command_output_utf8(command: &mut Command, label: &str) -> Result<String> {
    let output = command.output().with_context(|| format!("run {label}"))?;
    ensure!(output.status.success(), "{label} failed: {}", output.status);
    let mut text = String::from_utf8(output.stdout).with_context(|| format!("{label} stdout"))?;
    if !output.stderr.is_empty() {
        text.push_str(
            &String::from_utf8(output.stderr).with_context(|| format!("{label} stderr"))?,
        );
    }
    Ok(text.trim().to_owned())
}

fn cargo_build_sbf_version(path: &Path) -> Result<String> {
    let version = command_output_utf8(
        Command::new(path).arg("--version"),
        "cargo-build-sbf --version",
    )?;
    ensure!(
        version
            .lines()
            .any(|line| line.trim() == format!("platform-tools {PLATFORM_TOOLS_VERSION}")),
        "cargo-build-sbf reports an unexpected platform-tools version"
    );
    Ok(version)
}

fn git_head(root: &Path) -> Result<String> {
    let head = command_output_utf8(
        Command::new("git")
            .current_dir(root)
            .args(["rev-parse", "HEAD"]),
        "git rev-parse HEAD",
    )?;
    ensure!(
        head.len() == 40
            && head
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "git HEAD is not an exact lowercase SHA-1"
    );
    Ok(head)
}

fn expected_build_command(
    config: &BuildConfig,
    manifest: &Path,
    feature: &str,
) -> Result<Vec<String>> {
    Ok(vec![
        path_string(&config.cargo_build_sbf)?,
        "--manifest-path".to_owned(),
        path_string(manifest)?,
        "--no-default-features".to_owned(),
        "--features".to_owned(),
        feature.to_owned(),
        "--arch".to_owned(),
        "v0".to_owned(),
        "--offline".to_owned(),
        "--skip-tools-install".to_owned(),
        "--tools-version".to_owned(),
        PLATFORM_TOOLS_VERSION.to_owned(),
        "--sbf-sdk".to_owned(),
        path_string(&config.sbf_sdk)?,
        "--sbf-out-dir".to_owned(),
        path_string(&config.build_output_dir)?,
        "--".to_owned(),
        "--locked".to_owned(),
    ])
}

fn create_isolated_build_directory(path: &Path) -> Result<()> {
    let parent = path.parent().context("build directory omitted parent")?;
    let parent_metadata = fs::symlink_metadata(parent)
        .with_context(|| format!("build parent unavailable: {}", parent.display()))?;
    ensure!(
        parent_metadata.file_type().is_dir() && !parent_metadata.file_type().is_symlink(),
        "build parent must be an existing non-symlink directory"
    );
    fs::DirBuilder::new()
        .mode(0o700)
        .create(path)
        .with_context(|| format!("create isolated build directory {}", path.display()))
}

fn validate_identity_list(identities: &[SourceFileIdentity], label: &str) -> Result<()> {
    ensure!(!identities.is_empty(), "{label} inventory is empty");
    let mut prior: Option<&str> = None;
    for identity in identities {
        ensure!(!identity.path.is_empty(), "{label} contains an empty path");
        ensure!(
            identity.sha256.len() == 64
                && identity
                    .sha256
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
            "{label} contains an invalid SHA-256"
        );
        if let Some(previous) = prior {
            ensure!(
                previous < identity.path.as_str(),
                "{label} is not strictly sorted"
            );
        }
        prior = Some(&identity.path);
    }
    Ok(())
}

fn build_config_from_provenance(provenance: &V5SbfProvenance) -> Result<BuildConfig> {
    let config = BuildConfig {
        cargo_build_sbf: PathBuf::from(&provenance.cargo_build_sbf_path),
        sbf_sdk: PathBuf::from(&provenance.sbf_sdk_path),
        platform_tools_root: PathBuf::from(&provenance.platform_tools_root),
        build_output_dir: PathBuf::from(&provenance.build_output_dir),
        sbf_output: PathBuf::from(&provenance.sbf_path),
        provenance_output: PathBuf::new(),
    };
    for (path, label) in [
        (&config.cargo_build_sbf, "provenance cargo-build-sbf path"),
        (&config.sbf_sdk, "provenance SBF SDK path"),
        (
            &config.platform_tools_root,
            "provenance platform-tools root",
        ),
        (&config.build_output_dir, "provenance build directory"),
        (&config.sbf_output, "provenance SBF path"),
    ] {
        ensure_normal_absolute_path(path, label)?;
    }
    Ok(config)
}

fn validate_provenance_shape(
    provenance: &V5SbfProvenance,
    expected_sbf: &Path,
    root: &Path,
) -> Result<(BuildConfig, V5SbfProfile)> {
    let profile = match (
        provenance.artifact.as_str(),
        provenance.schema_version,
        provenance.features.as_slice(),
    ) {
        (SBF_PROVENANCE_ARTIFACT, SBF_PROVENANCE_SCHEMA_VERSION, [feature])
            if feature == SBF_FEATURE =>
        {
            V5SbfProfile::FeatureProbe
        }
        (
            FROZEN_PRODUCTION_PROVENANCE_ARTIFACT,
            FROZEN_PRODUCTION_PROVENANCE_SCHEMA_VERSION,
            [feature],
        ) if feature == FROZEN_PRODUCTION_FEATURE => V5SbfProfile::FrozenProduction,
        _ => bail!("unknown v5 SBF provenance artifact, schema, or feature set"),
    };
    ensure!(
        provenance.no_default_features,
        "default features were not disabled"
    );
    ensure!(
        provenance.platform_tools_version == PLATFORM_TOOLS_VERSION,
        "unexpected platform-tools version in provenance"
    );
    let config = build_config_from_provenance(provenance)?;
    ensure!(
        config.sbf_output == expected_sbf,
        "provenance binds a different SBF path"
    );
    ensure!(
        !config.sbf_output.starts_with(&config.build_output_dir),
        "provenance SBF output is not durable outside the isolated build directory"
    );
    for protected in [
        root,
        config.sbf_sdk.as_path(),
        config.platform_tools_root.as_path(),
    ] {
        ensure!(
            !config.build_output_dir.starts_with(protected),
            "provenance build directory overlaps a protected source/toolchain tree"
        );
    }
    let manifest = root.join("programs/aspis-verifier/Cargo.toml");
    ensure!(
        provenance.manifest_path == path_string(&manifest)?,
        "provenance binds a different verifier manifest"
    );
    ensure!(
        provenance.command == expected_build_command(&config, &manifest, profile.feature())?,
        "provenance build command is not the exact declared-profile command"
    );
    ensure!(
        provenance.cargo_target_dir == path_string(&config.build_output_dir.join("cargo-target"))?,
        "provenance does not isolate CARGO_TARGET_DIR"
    );
    ensure!(
        provenance.built_artifact_path
            == path_string(&config.build_output_dir.join(SBF_OUTPUT_NAME))?,
        "provenance binds an unexpected builder artifact"
    );
    validate_identity_list(&provenance.source_files, "source")?;
    validate_identity_list(&provenance.toolchain_files, "toolchain")?;
    if profile == V5SbfProfile::FrozenProduction {
        ensure!(
            provenance.sbf_bytes == FROZEN_PRODUCTION_SBF_BYTES
                && provenance.sbf_sha256 == FROZEN_PRODUCTION_SBF_SHA256,
            "production provenance does not identify the frozen Tag-67 SBF"
        );
        ensure!(
            provenance.source_files.len() == FROZEN_PRODUCTION_SOURCE_IDENTITIES
                && provenance.toolchain_files.len() == FROZEN_PRODUCTION_TOOLCHAIN_IDENTITIES,
            "production provenance identity counts differ from the freeze"
        );
    }
    Ok((config, profile))
}

fn validate_current_provenance(
    provenance_bytes: &[u8],
    expected_sbf: &Path,
    sbf: &[u8],
) -> Result<(V5SbfProvenance, V5SbfProfile)> {
    let provenance: V5SbfProvenance =
        serde_json::from_slice(provenance_bytes).context("decode strict v5 SBF provenance")?;
    let root = workspace_root()?;
    let (config, profile) = validate_provenance_shape(&provenance, expected_sbf, &root)?;
    match profile {
        V5SbfProfile::FeatureProbe => {
            ensure!(
                provenance.git_head == git_head(&root)?,
                "SBF provenance HEAD is stale"
            );
            ensure!(
                provenance.source_files == source_inventory(&root)?,
                "SBF provenance source inventory is stale"
            );
            let cargo_lock = exact_regular_file(&root.join("Cargo.lock"))?;
            ensure!(
                provenance.cargo_lock_sha256 == sha256(&cargo_lock),
                "SBF provenance Cargo.lock hash is stale"
            );
        }
        V5SbfProfile::FrozenProduction => {
            ensure!(
                sha256(provenance_bytes) == FROZEN_PRODUCTION_PROVENANCE_SHA256,
                "production provenance bytes differ from the frozen release record"
            );
        }
    }
    let build_tool = exact_executable(&config.cargo_build_sbf)?;
    ensure!(
        provenance.cargo_build_sbf_bytes == build_tool.len()
            && provenance.cargo_build_sbf_sha256 == sha256(&build_tool),
        "cargo-build-sbf bytes differ from provenance"
    );
    ensure!(
        provenance.cargo_build_sbf_version == cargo_build_sbf_version(&config.cargo_build_sbf)?,
        "cargo-build-sbf version differs from provenance"
    );
    ensure!(
        provenance.toolchain_files == toolchain_inventory(&config)?,
        "SBF toolchain inventory differs from provenance"
    );
    ensure!(
        provenance.sbf_bytes == sbf.len() && provenance.sbf_sha256 == sha256(sbf),
        "SBF bytes differ from build provenance"
    );
    Ok((provenance, profile))
}

fn ensure_distinct_keys(keys: &[Pubkey]) -> Result<()> {
    let unique = keys.iter().copied().collect::<BTreeSet<_>>();
    ensure!(unique.len() == keys.len(), "runtime keypair roles collide");
    Ok(())
}

#[derive(Serialize)]
struct StrictStatementSidecar {
    artifact: &'static str,
    pool_hex: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    deployment_domain_hex: String,
    selection_rule: &'static str,
    witness_independent_public_metadata: bool,
}

fn runtime_domain(network: V5NetworkPolicy, program_id: Pubkey) -> [u8; 32] {
    aspis_statement::atomic_deployment_domain(
        aspis_prover::HOST_HASH,
        &program_id.to_bytes(),
        network.domain_tag(),
    )
}

fn strict_statement_bytes(statement: &AtomicPaymentStatementV4) -> Result<Vec<u8>> {
    let sidecar = StrictStatementSidecar {
        artifact: SPEND_STATEMENT_ARTIFACT,
        pool_hex: spend_hex(&statement.pool),
        sequence: statement.sequence,
        current_anchor_hex: spend_hex(&aspis_statement::encode_digest_canonical(
            &statement.spend.anchor,
        )),
        nullifier_hex: spend_hex(&aspis_statement::encode_digest_canonical(
            &statement.spend.nullifier,
        )),
        output_commitment_hex: spend_hex(&aspis_statement::encode_digest_canonical(
            &statement.spend.output_commitment,
        )),
        output_anchor_hex: spend_hex(&aspis_statement::encode_digest_canonical(
            &statement.output_anchor,
        )),
        asset_id: statement.spend.asset_id.0,
        fee: statement.spend.fee,
        deployment_domain_hex: spend_hex(&statement.deployment_domain),
        selection_rule: SPEND_STATEMENT_SELECTION_RULE,
        witness_independent_public_metadata: true,
    };
    let mut bytes = serde_json::to_vec_pretty(&sidecar)?;
    bytes.push(b'\n');
    ensure!(
        decode_spend_statement_sidecar(&bytes)? == *statement,
        "generated strict statement sidecar failed exact round-trip"
    );
    Ok(bytes)
}

fn create_new_0600(path: &Path) -> Result<fs::File> {
    let parent = path.parent().context("output path omitted parent")?;
    let parent_metadata = fs::symlink_metadata(parent)
        .with_context(|| format!("output parent unavailable: {}", parent.display()))?;
    ensure!(
        parent_metadata.file_type().is_dir() && !parent_metadata.file_type().is_symlink(),
        "output parent must be an existing non-symlink directory: {}",
        parent.display()
    );
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .with_context(|| format!("create new output {}", path.display()))
}

fn write_artifact_pair_create_new(
    proof_path: &Path,
    proof: &[u8],
    statement_path: &Path,
    statement: &[u8],
) -> Result<()> {
    let mut proof_file = create_new_0600(proof_path)?;
    let mut statement_file = match create_new_0600(statement_path) {
        Ok(file) => file,
        Err(error) => {
            drop(proof_file);
            fs::remove_file(proof_path).with_context(|| {
                format!(
                    "remove newly reserved proof output after statement reservation failed: {}",
                    proof_path.display()
                )
            })?;
            return Err(error);
        }
    };
    proof_file.write_all(proof)?;
    proof_file.sync_all()?;
    statement_file.write_all(statement)?;
    statement_file.sync_all()?;
    ensure!(
        fs::read(proof_path)? == proof && fs::read(statement_path)? == statement,
        "create-new artifact bytes changed after durable write"
    );
    Ok(())
}

fn secure_keypair_0600(path: &Path) -> Result<Keypair> {
    let metadata = fs::symlink_metadata(path)
        .with_context(|| format!("keypair unavailable: {}", path.display()))?;
    ensure!(
        metadata.file_type().is_file() && !metadata.file_type().is_symlink(),
        "keypair must be a regular non-symlink file: {}",
        path.display()
    );
    ensure!(
        metadata.permissions().mode() & 0o777 == 0o600,
        "keypair mode must be exactly 0600: {}",
        path.display()
    );
    secure_keypair(path)
}

fn checked_add_lamports(left: u64, right: u64, label: &str) -> Result<u64> {
    left.checked_add(right)
        .with_context(|| format!("{label} lamport budget overflow"))
}

#[allow(deprecated)]
fn verify_host_proof_and_least_good(
    program_id: Pubkey,
    proof_account: Pubkey,
    proof: &[u8],
    statement: &AtomicPaymentStatementV4,
) -> Result<(u8, [bool; 3])> {
    let selector = *proof
        .get(aspis_verifier::v5_cu_probe::V5_CU_PROBE_QUERY_SELECTOR_OFFSET)
        .context("v5 proof omitted its selector byte")?;
    let evaluations =
        aspis_verifier::v5_cu_probe::v5_good_gate_evaluations(aspis_prover::HOST_HASH, proof)
            .map_err(|error| anyhow!("replay all v5 Good candidates: {error:?}"))?;
    let good_candidates = evaluations.map(|evaluation| evaluation.is_good());
    ensure!(
        aspis_verifier::v5_cu_probe::good_gate_probe::selected_is_least_good(
            selector,
            &good_candidates
        ),
        "serialized selector {selector} is not the least Good candidate: {good_candidates:?}"
    );

    let statement_digest =
        aspis_statement::atomic_payment_statement_digest_v4(statement, aspis_prover::HOST_HASH)
            .map_err(|error| anyhow!("digest v5 statement for host verification: {error:?}"))?;
    let mut account_data = expected_proof_account(proof, Pubkey::default(), true);
    let mut lamports = 1u64;
    let account = AccountInfo::new(
        &proof_account,
        false,
        false,
        &mut lamports,
        &mut account_data,
        &program_id,
        false,
        Epoch::default(),
    );
    aspis_verifier::v5_cu_probe::verify_uploaded_v5_mode9_cu_fixture(
        &account,
        statement,
        &statement_digest,
    )
    .map_err(|error| anyhow!("exact v5 host proof verification failed: {error:?}"))?;
    Ok((selector, good_candidates))
}

fn verify_runtime_statement_and_wire(
    network: V5NetworkPolicy,
    program_id: Pubkey,
    pool: Pubkey,
    statement: &AtomicPaymentStatementV4,
) -> Result<()> {
    network.validate_program_id(program_id)?;
    ensure!(
        statement.sequence == 0,
        "v5 {} statement is not sequence 0",
        network.network()
    );
    ensure!(
        statement.pool == pool.to_bytes(),
        "v5 {} statement pool differs from the explicit pool keypair",
        network.network()
    );
    ensure!(
        statement.deployment_domain == runtime_domain(network, program_id),
        "v5 statement deployment domain differs from the program-id/{} runtime domain",
        network.network()
    );
    let wire = build_v5_tag67_transaction_wire(statement);
    let decoded = aspis_verifier::v5_full_transaction::parse_v5_full_cu_public_inputs(&wire)
        .map_err(|error| anyhow!("decode exact tag-67 public wire: {error:?}"))?;
    ensure!(
        decoded == statement_public_inputs(statement),
        "tag-67 wire differs from the strict statement"
    );
    Ok(())
}

fn parse_rpc_runtime_identity(value: &Value) -> Result<(String, u64)> {
    let solana_core = value["solana-core"]
        .as_str()
        .context("getVersion omitted solana-core")?
        .to_owned();
    let feature_set = value["feature-set"]
        .as_u64()
        .context("getVersion omitted feature-set")?;
    ensure!(
        !solana_core.is_empty(),
        "getVersion returned empty solana-core"
    );
    ensure!(feature_set > 0, "getVersion returned zero feature-set");
    Ok((solana_core, feature_set))
}

fn rpc_runtime_identity(rpc: &Rpc) -> Result<(String, u64)> {
    parse_rpc_runtime_identity(&rpc.call_read("getVersion", serde_json::json!([]))?)
}

fn validate_runtime_replay(config: &ReadinessConfig) -> Result<Option<(String, String)>> {
    let Some(path) = config.runtime_replay.as_ref() else {
        ensure!(
            config.network == V5NetworkPolicy::Devnet,
            "v5 mainnet-beta requires the pinned runtime replay"
        );
        return Ok(None);
    };
    ensure!(
        config.network == V5NetworkPolicy::MainnetBeta,
        "runtime replay is mainnet-beta-only"
    );
    let bytes = exact_regular_file(path)?;
    let digest = sha256(&bytes);
    ensure!(
        digest == MAINNET_RUNTIME_REPLAY_SHA256,
        "mainnet runtime replay differs from the reviewed Agave 4.1.0 record"
    );
    let value: Value = serde_json::from_slice(&bytes).context("decode mainnet runtime replay")?;
    ensure!(
        value["artifact"] == "aspis_v5_mainnet_runtime_replay"
            && value["schema_version"] == 1
            && value["mainnet_beta"]["solana_core"] == MAINNET_RUNTIME_SOLANA_CORE
            && value["mainnet_beta"]["feature_set"] == MAINNET_RUNTIME_FEATURE_SET
            && value["agave_release"]["solana_cli_sha256"] == MAINNET_SOLANA_CLI_SHA256
            && value["agave_release"]["solana_cli_version"] == MAINNET_SOLANA_CLI_VERSION
            && value["sbf"]["bytes"] == FROZEN_PRODUCTION_SBF_BYTES
            && value["sbf"]["sha256"] == FROZEN_PRODUCTION_SBF_SHA256
            && value["mainnet_transaction_shape"]["compute_unit_price_microlamports"] == 1
            && value["mainnet_transaction_shape"]["instruction_order"]
                == serde_json::json!([
                    "set_compute_unit_limit",
                    "request_heap_frame",
                    "set_compute_unit_price",
                    "tag67"
                ])
            && value["mainnet_transaction_shape"]["tag67_instruction_index"] == 3
            && value["mainnet_transaction_shape"]["compute_unit_price_instruction_delta_cu"] == 150
            && value["mainnet_transaction_shape"]["prefunded_marker_evidence_path"]
                == "prefunded-system-marker-cu.json"
            && value["mainnet_transaction_shape"]["prefunded_marker_evidence_sha256"]
                == MAINNET_PREFUNDED_MARKER_REPLAY_SHA256
            && value["accepted_input_policy"]["grammar_topology_ceiling_cu"] == 1_353_616
            && value["accepted_input_policy"]["grammar_topology_headroom_cu"] == 46_384
            && value["accepted_input_policy"]["agave_4_1_0_unpriced_missing_marker_delta_cu"]
                == -54
            && value["accepted_input_policy"]["compute_unit_price_instruction_delta_cu"] == 150
            && value["accepted_input_policy"]["prefunded_marker_delta_from_priced_missing_cu"]
                == 3_200
            && value["accepted_input_policy"]["prefunded_system_marker_evidence_path"]
                == "prefunded-system-marker-cu.json"
            && value["accepted_input_policy"]["prefunded_system_marker_evidence_sha256"]
                == MAINNET_PREFUNDED_MARKER_REPLAY_SHA256
            && value["accepted_input_policy"]["accepted_state_ceiling_cu"] == 1_356_912
            && value["accepted_input_policy"]["accepted_state_headroom_cu"] == 43_088
            && value["accepted_input_policy"]["governing_selector"] == 2
            && value["accepted_input_policy"]["agave_4_1_0_result"]
                == "the exact priced transaction shape, release grammar, and every accepted marker pre-state remain below the transaction limit",
        "mainnet runtime replay fields differ from the reviewed Agave 4.1.0 record"
    );
    let measurements = value["measurements"]
        .as_array()
        .context("mainnet runtime replay measurements must be an array")?;
    ensure!(
        measurements.len() == 7,
        "mainnet runtime replay measurement count differs from the reviewed record"
    );
    for (index, selector, total_cu) in [(4, 0, 1_334_528), (5, 1, 1_337_192), (6, 2, 1_329_776)] {
        let measurement = &measurements[index];
        ensure!(
            measurement["selector"] == selector
                && measurement["marker_mode"] == "prefunded_system_owned_one_lamport"
                && measurement["totals_cu"]
                    == serde_json::json!([total_cu, total_cu, total_cu])
                && measurement["system_program_invokes_per_repeat"] == 3
                && measurement["system_program_successes_per_repeat"] == 3
                && measurement["prefunded_lamports"] == 1
                && measurement["compute_unit_price_microlamports"] == 1
                && measurement["delta_from_unpriced_4_1_missing_cu"] == 3_350
                && measurement["delta_from_priced_4_1_missing_cu"] == 3_200,
            "mainnet runtime replay priced prefunded selector {selector} differs from the reviewed record"
        );
    }
    let replay_parent = path
        .parent()
        .context("mainnet runtime replay path omitted parent")?;
    let prefunded_replay =
        exact_regular_file(&replay_parent.join("prefunded-system-marker-cu.json"))?;
    ensure!(
        sha256(&prefunded_replay) == MAINNET_PREFUNDED_MARKER_REPLAY_SHA256,
        "prefunded System-owned marker replay differs from the reviewed Agave 4.1.0 record"
    );
    Ok(Some((path_string(path)?, digest)))
}

fn validate_fresh_evidence_destination(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(_) => bail!("v5 execution evidence path already exists"),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(error).with_context(|| format!("inspect evidence path {}", path.display()));
        }
    }
    let parent = path.parent().context("evidence path omitted parent")?;
    let metadata = fs::symlink_metadata(parent)
        .with_context(|| format!("evidence parent unavailable: {}", parent.display()))?;
    ensure!(
        metadata.file_type().is_dir() && !metadata.file_type().is_symlink(),
        "evidence parent must be an existing non-symlink directory"
    );
    path.file_name()
        .and_then(|name| name.to_str())
        .context("evidence filename is not UTF-8")?;
    Ok(())
}

fn deployment_adapter(config: &ExecuteConfig) -> DevnetConfig {
    DevnetConfig {
        rpc_url: config.readiness.rpc_url.clone(),
        payer_keypair: config.readiness.payer_keypair.clone(),
        program_keypair: config.readiness.program_keypair.clone(),
        pool_keypair: config.readiness.pool_keypair.clone(),
        proof_account_keypair: config.readiness.proof_account_keypair.clone(),
        replay_probe_keypair: None,
        upgrade_authority_keypair: config.readiness.upgrade_authority_keypair.clone(),
        deployment_buffer_keypair: config.readiness.deployment_buffer_keypair.clone(),
        // The parent argument builder requires an explicit transport. The
        // mainnet path replaces this placeholder with reviewed RPC+WSS flags
        // before persisting or invoking the command.
        use_tpu_client: config.readiness.network == V5NetworkPolicy::MainnetBeta,
        // deploy_if_needed consumes none of these release/proof/statement
        // fields. Keep them tied to the exact v5 inputs so any future use is
        // visible in review.
        release: config.readiness.statement.clone(),
        sbf: config.readiness.sbf.clone(),
        proof: config.readiness.proof.clone(),
        statement: config.readiness.statement.clone(),
        solana_cli: config.solana_cli.clone(),
        evidence: config.evidence.clone(),
        program_max_len: config.readiness.program_max_len,
        fee_reserve_lamports: config.readiness.fee_reserve_lamports,
        execute_interlock: true,
        resume_in_progress: false,
        resume_pool_create_signature: None,
        resume_pool_init_signature: None,
        resume_proof_create_signature: None,
        acknowledgement: Some(
            config
                .readiness
                .network
                .execute_acknowledgement()
                .to_owned(),
        ),
    }
}

fn compute_unit_price_instruction(config: &ReadinessConfig) -> Option<Instruction> {
    config
        .compute_unit_price_microlamports
        .map(ComputeBudgetInstruction::set_compute_unit_price)
}

fn submit_signed_transaction(
    rpc: &Rpc,
    network: V5NetworkPolicy,
    recovery_journal: &mut Option<crate::spend_mainnet_journal::RecoveryJournal>,
    transaction: &Transaction,
    wire_id: &str,
    label: &str,
) -> Result<TransactionEvidence> {
    if network == V5NetworkPolicy::Devnet {
        return rpc.submit_transaction(transaction, label);
    }
    let journal = recovery_journal
        .as_mut()
        .context("mainnet signed transaction has no recovery journal")?;
    let wire = bincode::serialize(transaction)?;
    journal.spool_signed_wire_submit_ready(
        wire_id,
        crate::spend_mainnet_journal::TransactionClass::Forward,
        &wire,
    )?;
    let persisted_wire = journal.load_submit_ready_wire(wire_id)?;
    ensure!(
        persisted_wire == wire,
        "recovery spool differs from signed transaction {wire_id}"
    );
    let evidence = rpc.submit_wire(
        &persisted_wire,
        transaction.signatures[0],
        true,
        label,
        sha256(&bincode::serialize(&transaction.message)?),
    )?;
    journal.record_submission(wire_id, evidence.signature.clone())?;
    journal.record_finalization(wire_id, evidence.finalized_slot)?;
    Ok(evidence)
}

fn upload_proof_chunks_for_network(
    rpc: &Rpc,
    config: &ReadinessConfig,
    recovery_journal: &mut Option<crate::spend_mainnet_journal::RecoveryJournal>,
    program_id: &Pubkey,
    payer: &Keypair,
    proof_account: &Keypair,
    proof: &[u8],
) -> Result<Vec<TransactionEvidence>> {
    if config.network == V5NetworkPolicy::Devnet {
        return upload_proof_chunks(rpc, program_id, payer, proof_account, proof);
    }
    let mut evidence = Vec::with_capacity(proof.len().div_ceil(UPLOAD_CHUNK_BYTES));
    for (index, chunk) in proof.chunks(UPLOAD_CHUNK_BYTES).enumerate() {
        let upload = proof_instruction(
            program_id,
            payer.pubkey(),
            proof_account.pubkey(),
            &AspisInstruction::UploadChunk {
                offset: u32::try_from(index * UPLOAD_CHUNK_BYTES)
                    .context("proof upload offset exceeds u32")?,
                chunk: chunk.to_vec(),
            },
        )?;
        let mut instructions = Vec::with_capacity(2);
        if let Some(price) = compute_unit_price_instruction(config) {
            instructions.push(price);
        }
        instructions.push(upload);
        let transaction = signed_transaction(payer, &[], &instructions, rpc.latest_blockhash()?);
        evidence.push(submit_signed_transaction(
            rpc,
            config.network,
            recovery_journal,
            &transaction,
            &format!("proof_upload_{index:04}"),
            &format!("upload_proof_chunk_{index}"),
        )?);
    }
    Ok(evidence)
}

fn deploy_mainnet_if_needed(
    rpc: &Rpc,
    config: &ExecuteConfig,
    recovery_journal: &mut crate::spend_mainnet_journal::RecoveryJournal,
    program_id: &Pubkey,
    expected_upgrade_authority: &Pubkey,
    sbf: &[u8],
) -> Result<Option<TransactionEvidence>> {
    if deployed_program_exact(
        rpc,
        program_id,
        sbf,
        config.readiness.program_max_len,
        expected_upgrade_authority,
    )?
    .is_some()
    {
        recovery_journal.record_checkpoint(
            "exact_program_already_deployed",
            serde_json::json!({
                "program_id": program_id.to_string(),
                "sbf_sha256": sha256(sbf),
                "program_max_len": config.readiness.program_max_len,
                "upgrade_authority": expected_upgrade_authority.to_string(),
            }),
        )?;
        return Ok(None);
    }
    ensure!(
        rpc.account(program_id)?.is_none(),
        "program address exists but does not match the exact frozen SBF"
    );
    let deploy_config = deployment_adapter(config);
    let mut arguments = super::deploy_cli_args(
        &deploy_config,
        V5NetworkPolicy::MainnetBeta.cluster_policy(),
    )?;
    let price = config
        .readiness
        .compute_unit_price_microlamports
        .context("mainnet deploy omitted explicit compute-unit price")?;
    let price_flag = arguments
        .iter()
        .position(|argument| argument == "--with-compute-unit-price")
        .context("mainnet deploy command omitted compute-unit price flag")?;
    *arguments
        .get_mut(price_flag + 1)
        .context("mainnet deploy command omitted compute-unit price value")? =
        price.to_string().into();
    let tpu_flag = arguments
        .iter()
        .position(|argument| argument == "--use-tpu-client")
        .context("mainnet deploy argument builder omitted its transport placeholder")?;
    arguments.remove(tpu_flag);
    arguments.push("--use-rpc".into());
    arguments.push("--ws".into());
    arguments.push(
        config
            .readiness
            .ws_url
            .as_ref()
            .context("mainnet deploy omitted explicit WSS endpoint")?
            .into(),
    );
    let argument_strings = arguments
        .iter()
        .map(|argument| {
            argument
                .to_str()
                .map(ToOwned::to_owned)
                .context("mainnet deploy argument is not UTF-8")
        })
        .collect::<Result<Vec<_>>>()?;
    recovery_journal.record_checkpoint(
        "deploy_command_persisted_before_cli",
        serde_json::json!({
            "solana_cli": path_string(&config.solana_cli)?,
            "arguments": argument_strings,
            "program_id": program_id.to_string(),
            "program_keypair": path_string(&config.readiness.program_keypair)?,
            "upgrade_authority": expected_upgrade_authority.to_string(),
            "upgrade_authority_keypair": config.readiness.upgrade_authority_keypair.as_ref().map(|path| path_string(path)).transpose()?,
            "deployment_buffer": config.readiness.deployment_buffer_keypair.as_ref().map(|path| path_string(path)).transpose()?,
            "sbf_sha256": sha256(sbf),
            "program_max_len": config.readiness.program_max_len,
            "compute_unit_price_microlamports": price,
            "recovery": "Do not rerun automatically. Reconcile the program and buffer accounts plus the CLI output before any next action.",
        }),
    )?;
    let output = Command::new(&config.solana_cli)
        .args(&arguments)
        .output()
        .context("run persisted Solana CLI deploy command")?;
    ensure!(
        output.status.success(),
        "Solana CLI deploy failed with status {}; reconcile the persisted program and buffer identities before continuing",
        output.status
    );
    let signature = super::extract_deploy_signature(&output.stdout)?;
    let slot = rpc.wait_finalized(&signature)?;
    ensure!(
        deployed_program_exact(
            rpc,
            program_id,
            sbf,
            config.readiness.program_max_len,
            expected_upgrade_authority,
        )?
        .is_some(),
        "finalized deployed program differs from frozen bytes/max-len/authority"
    );
    let (wire_sha256, message_sha256) = rpc.transaction_wire_and_message_hash(&signature)?;
    let evidence = TransactionEvidence {
        label: "deploy_exact_frozen_v5_sbf".to_owned(),
        signature: signature.to_string(),
        finalized_slot: slot,
        message_sha256,
        serialized_transaction_sha256: wire_sha256,
        compute_units_consumed: rpc.transaction_cu(&signature)?,
        identical_wire_retries: 0,
    };
    recovery_journal.record_checkpoint(
        "deploy_finalized_and_exact_program_verified",
        serde_json::json!({
            "signature": evidence.signature,
            "finalized_slot": evidence.finalized_slot,
            "serialized_transaction_sha256": evidence.serialized_transaction_sha256,
            "message_sha256": evidence.message_sha256,
            "program_id": program_id.to_string(),
            "sbf_sha256": sha256(sbf),
        }),
    )?;
    Ok(Some(evidence))
}

fn build_tag67_instruction(
    program_id: Pubkey,
    proof_account: Pubkey,
    pool: Pubkey,
    nullifier: Pubkey,
    payer: Pubkey,
    statement: &AtomicPaymentStatementV4,
) -> Result<Instruction> {
    let data = build_v5_tag67_transaction_wire(statement).to_vec();
    ensure!(
        data.len() == aspis_verifier::v5_full_transaction::V5_FULL_CU_TRANSACTION_WIRE_BYTES
            && data.len() == 169,
        "tag-67 instruction is not the exact 169-byte public wire"
    );
    ensure!(
        aspis_verifier::v5_full_transaction::parse_v5_full_cu_public_inputs(&data)
            .map_err(|error| anyhow!("parse tag-67 public wire: {error:?}"))?
            == statement_public_inputs(statement),
        "tag-67 public wire differs from the strict statement"
    );
    let instruction = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new_readonly(proof_account, false),
            AccountMeta::new(pool, false),
            AccountMeta::new(nullifier, false),
            AccountMeta::new(payer, true),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data,
    };
    validate_tag67_instruction(
        &instruction,
        program_id,
        proof_account,
        pool,
        nullifier,
        payer,
    )?;
    Ok(instruction)
}

fn validate_tag67_instruction(
    instruction: &Instruction,
    program_id: Pubkey,
    proof_account: Pubkey,
    pool: Pubkey,
    nullifier: Pubkey,
    payer: Pubkey,
) -> Result<()> {
    let expected_accounts = vec![
        AccountMeta::new_readonly(proof_account, false),
        AccountMeta::new(pool, false),
        AccountMeta::new(nullifier, false),
        AccountMeta::new(payer, true),
        AccountMeta::new_readonly(system_program::id(), false),
    ];
    ensure!(
        instruction.program_id == program_id,
        "tag-67 targets a different program"
    );
    ensure!(
        instruction.accounts == expected_accounts,
        "tag-67 account order/access differs from retained-proof semantics"
    );
    ensure!(
        instruction.data.len()
            == aspis_verifier::v5_full_transaction::V5_FULL_CU_TRANSACTION_WIRE_BYTES,
        "tag-67 instruction length drift"
    );
    Ok(())
}

fn tag67_meta_evidence(instruction: &Instruction) -> Result<Vec<V5Tag67AccountMetaEvidence>> {
    let roles = ["proof", "pool", "nullifier", "payer", "system_program"];
    ensure!(
        instruction.accounts.len() == roles.len(),
        "tag-67 evidence account count drift"
    );
    Ok(instruction
        .accounts
        .iter()
        .zip(roles)
        .enumerate()
        .map(|(index, (account, role))| V5Tag67AccountMetaEvidence {
            index,
            role,
            address: account.pubkey.to_string(),
            is_signer: account.is_signer,
            is_writable: account.is_writable,
        })
        .collect())
}

fn require_exact_program_success(logs: &[String], program_id: Pubkey) -> Result<()> {
    let expected = format!("Program {program_id} success");
    let count = logs.iter().filter(|line| *line == &expected).count();
    ensure!(
        count == 1,
        "expected exactly one top-level tag-67 program success log, observed {count}"
    );
    Ok(())
}

fn retained_proof_balance_evidence(
    account_keys: &[Pubkey],
    fee_lamports: u64,
    pre_balances: &[u64],
    post_balances: &[u64],
    payer: Pubkey,
    proof: Pubkey,
    nullifier: Pubkey,
    expected_proof_lamports: u64,
) -> Result<V5RetainedProofBalanceEvidence> {
    ensure!(
        pre_balances.len() == account_keys.len() && post_balances.len() == account_keys.len(),
        "tag-67 balance-vector length drift"
    );
    let index = |key: Pubkey| -> Result<usize> {
        account_keys
            .iter()
            .position(|candidate| *candidate == key)
            .with_context(|| format!("tag-67 message omitted balance account {key}"))
    };
    let payer_account_index = index(payer)?;
    let proof_account_index = index(proof)?;
    let nullifier_account_index = index(nullifier)?;
    let payer_pre_lamports = pre_balances[payer_account_index];
    let payer_post_lamports = post_balances[payer_account_index];
    let proof_pre_lamports = pre_balances[proof_account_index];
    let proof_post_lamports = post_balances[proof_account_index];
    let nullifier_pre_lamports = pre_balances[nullifier_account_index];
    let nullifier_post_lamports = post_balances[nullifier_account_index];
    let payer_spend = payer_pre_lamports
        .checked_sub(payer_post_lamports)
        .context("tag-67 payer balance increased")?;
    let nullifier_funding_lamports = nullifier_post_lamports
        .checked_sub(nullifier_pre_lamports)
        .context("tag-67 nullifier balance decreased")?;
    let proof_balance_retained_exactly = proof_pre_lamports == expected_proof_lamports
        && proof_post_lamports == expected_proof_lamports;
    ensure!(
        proof_balance_retained_exactly,
        "tag-67 did not retain the proof account balance exactly"
    );
    let exact_balance_equation_reconciled = payer_spend
        == fee_lamports
            .checked_add(nullifier_funding_lamports)
            .context("tag-67 fee plus marker funding overflow")?;
    ensure!(
        exact_balance_equation_reconciled,
        "tag-67 payer/fee/nullifier balance equation does not reconcile"
    );
    Ok(V5RetainedProofBalanceEvidence {
        fee_lamports,
        payer_account_index,
        proof_account_index,
        nullifier_account_index,
        payer_pre_lamports,
        payer_post_lamports,
        proof_pre_lamports,
        proof_post_lamports,
        nullifier_pre_lamports,
        nullifier_post_lamports,
        nullifier_funding_lamports,
        exact_balance_equation_reconciled,
        proof_balance_retained_exactly,
    })
}

fn mainnet_priority_and_signature_fee_bound(
    proof_bytes: usize,
    compute_unit_price_microlamports: u64,
) -> Result<(usize, u64)> {
    let transaction_count = proof_bytes
        .div_ceil(UPLOAD_CHUNK_BYTES)
        .checked_add(5)
        .context("mainnet transaction-count bound overflow")?;
    let priority_per_transaction = u128::from(CU_LIMIT)
        .checked_mul(u128::from(compute_unit_price_microlamports))
        .and_then(|value| value.checked_add(999_999))
        .context("mainnet priority-fee bound overflow")?
        / 1_000_000;
    let fee_per_transaction = priority_per_transaction
        .checked_add(u128::from(
            CONSERVATIVE_SIGNATURE_FEE_LAMPORTS_PER_TRANSACTION,
        ))
        .context("mainnet per-transaction fee bound overflow")?;
    let total = fee_per_transaction
        .checked_mul(
            u128::try_from(transaction_count)
                .context("mainnet transaction count does not fit u128")?,
        )
        .context("mainnet total fee bound overflow")?;
    Ok((
        transaction_count,
        u64::try_from(total).context("mainnet total fee bound exceeds u64")?,
    ))
}

fn generate_artifact_from_config(config: ArtifactConfig) -> Result<V5DevnetArtifactOutcome> {
    ensure!(
        config.program_id != config.pool,
        "program and pool IDs collide"
    );
    config.network.validate_program_id(config.program_id)?;
    let deployment_domain = runtime_domain(config.network, config.program_id);
    let (statement, proof, least_good_selector, successful_attempt_index) =
        build_v5_runtime_bound_production_demo_proof_body(
            config.pool.to_bytes(),
            0,
            deployment_domain,
        )?;
    verify_runtime_statement_and_wire(config.network, config.program_id, config.pool, &statement)?;
    let host_check_account =
        Pubkey::find_program_address(&[b"v5-runtime-artifact-host-check"], &config.program_id).0;
    let (verified_selector, _) = verify_host_proof_and_least_good(
        config.program_id,
        host_check_account,
        &proof,
        &statement,
    )?;
    ensure!(
        verified_selector == least_good_selector,
        "cap-17 wrapper and verifier disagree on least-Good selector"
    );
    let statement_bytes = strict_statement_bytes(&statement)?;
    write_artifact_pair_create_new(
        &config.proof_output,
        &proof,
        &config.statement_output,
        &statement_bytes,
    )?;
    Ok(V5DevnetArtifactOutcome {
        artifact: config.network.artifact_name(),
        network: config.network.network(),
        program_id: config.program_id.to_string(),
        pool: config.pool.to_string(),
        sequence: 0,
        deployment_domain_hex: spend_hex(&deployment_domain),
        proof_path: config.proof_output.display().to_string(),
        proof_bytes: proof.len(),
        proof_sha256: sha256(&proof),
        statement_path: config.statement_output.display().to_string(),
        statement_bytes: statement_bytes.len(),
        statement_sha256: sha256(&statement_bytes),
        canonical_public_input_digest: canonical_spend_public_input_digest(&statement)?,
        least_good_selector,
        successful_attempt_index,
        host_verification_green: true,
    })
}

pub(crate) fn generate_artifact(arguments: &[String]) -> Result<V5DevnetArtifactOutcome> {
    generate_artifact_from_config(parse_artifact_args(arguments)?)
}

pub(crate) fn generate_mainnet_artifact(arguments: &[String]) -> Result<V5DevnetArtifactOutcome> {
    generate_artifact_from_config(parse_mainnet_artifact_args(arguments)?)
}

pub(crate) fn build_sbf(arguments: &[String]) -> Result<V5DevnetBuildOutcome> {
    let config = parse_build_args(arguments)?;
    let root = workspace_root()?;
    for protected in [
        root.as_path(),
        config.sbf_sdk.as_path(),
        config.platform_tools_root.as_path(),
    ] {
        ensure!(
            !config.build_output_dir.starts_with(protected),
            "isolated build directory overlaps a protected source/toolchain tree"
        );
    }
    let manifest = root.join("programs/aspis-verifier/Cargo.toml");
    let cargo_lock = exact_regular_file(&root.join("Cargo.lock"))?;
    let head_before = git_head(&root)?;
    let sources_before = source_inventory(&root)?;
    let toolchain_before = toolchain_inventory(&config)?;
    let build_tool_before = exact_executable(&config.cargo_build_sbf)?;
    let build_tool_version = cargo_build_sbf_version(&config.cargo_build_sbf)?;
    let command = expected_build_command(&config, &manifest, SBF_FEATURE)?;
    let cargo_target_dir = config.build_output_dir.join("cargo-target");
    let built_artifact_path = config.build_output_dir.join(SBF_OUTPUT_NAME);

    create_isolated_build_directory(&config.build_output_dir)?;
    let output = Command::new(&config.cargo_build_sbf)
        .current_dir(&root)
        .args(&command[1..])
        .env("NO_DNA", "1")
        .env("CARGO_TARGET_DIR", &cargo_target_dir)
        .output()
        .context("run exact isolated feature-only cargo-build-sbf")?;
    ensure!(
        output.status.success(),
        "feature-only cargo-build-sbf failed with {}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let sbf = exact_regular_file(&built_artifact_path)?;
    ensure!(
        !sbf.is_empty(),
        "feature-only cargo-build-sbf produced an empty SBF"
    );
    ensure!(
        head_before == git_head(&root)?,
        "git HEAD changed during the SBF build"
    );
    ensure!(
        sources_before == source_inventory(&root)?,
        "verifier source inventory changed during the SBF build"
    );
    ensure!(
        toolchain_before == toolchain_inventory(&config)?,
        "SBF toolchain inventory changed during the build"
    );
    ensure!(
        build_tool_before == exact_executable(&config.cargo_build_sbf)?,
        "cargo-build-sbf changed during the build"
    );
    ensure!(
        build_tool_version == cargo_build_sbf_version(&config.cargo_build_sbf)?,
        "cargo-build-sbf version changed during the build"
    );

    let provenance = V5SbfProvenance {
        artifact: SBF_PROVENANCE_ARTIFACT.to_owned(),
        schema_version: SBF_PROVENANCE_SCHEMA_VERSION,
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        git_head: head_before.clone(),
        cargo_build_sbf_path: path_string(&config.cargo_build_sbf)?,
        cargo_build_sbf_bytes: build_tool_before.len(),
        cargo_build_sbf_sha256: sha256(&build_tool_before),
        cargo_build_sbf_version: build_tool_version,
        sbf_sdk_path: path_string(&config.sbf_sdk)?,
        platform_tools_root: path_string(&config.platform_tools_root)?,
        platform_tools_version: PLATFORM_TOOLS_VERSION.to_owned(),
        toolchain_files: toolchain_before,
        manifest_path: path_string(&manifest)?,
        no_default_features: true,
        features: vec![SBF_FEATURE.to_owned()],
        command,
        build_output_dir: path_string(&config.build_output_dir)?,
        cargo_target_dir: path_string(&cargo_target_dir)?,
        built_artifact_path: path_string(&built_artifact_path)?,
        build_stdout_sha256: Some(sha256(&output.stdout)),
        build_stderr_sha256: Some(sha256(&output.stderr)),
        cargo_lock_sha256: sha256(&cargo_lock),
        source_files: sources_before,
        sbf_path: path_string(&config.sbf_output)?,
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        capture_note: None,
    };
    validate_provenance_shape(&provenance, &config.sbf_output, &root)?;
    let mut provenance_bytes = serde_json::to_vec_pretty(&provenance)?;
    provenance_bytes.push(b'\n');
    write_artifact_pair_create_new(
        &config.sbf_output,
        &sbf,
        &config.provenance_output,
        &provenance_bytes,
    )?;

    Ok(V5DevnetBuildOutcome {
        artifact: "aspis_v5_devnet_sbf_build",
        sbf_path: path_string(&config.sbf_output)?,
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        provenance_path: path_string(&config.provenance_output)?,
        provenance_bytes: provenance_bytes.len(),
        provenance_sha256: sha256(&provenance_bytes),
        git_head: head_before,
    })
}

fn readiness_from_config(config: ReadinessConfig) -> Result<V5DevnetReadiness> {
    let payer = secure_keypair_0600(&config.payer_keypair)?;
    let program = secure_keypair_0600(&config.program_keypair)?;
    let pool = secure_keypair_0600(&config.pool_keypair)?;
    let proof_account = secure_keypair_0600(&config.proof_account_keypair)?;
    let upgrade_authority = config
        .upgrade_authority_keypair
        .as_ref()
        .map(|path| secure_keypair_0600(path))
        .transpose()?;
    let deployment_buffer = config
        .deployment_buffer_keypair
        .as_ref()
        .map(|path| secure_keypair_0600(path))
        .transpose()?;
    let mut runtime_keys = vec![
        payer.pubkey(),
        program.pubkey(),
        pool.pubkey(),
        proof_account.pubkey(),
    ];
    runtime_keys.extend(upgrade_authority.as_ref().map(Signer::pubkey));
    runtime_keys.extend(deployment_buffer.as_ref().map(Signer::pubkey));
    ensure_distinct_keys(&runtime_keys)?;
    config.network.validate_program_id(program.pubkey())?;
    let expected_upgrade_authority = upgrade_authority
        .as_ref()
        .map(Signer::pubkey)
        .unwrap_or_else(|| payer.pubkey());

    let sbf = exact_regular_file(&config.sbf)?;
    let sbf_provenance_bytes = exact_regular_file(&config.sbf_provenance)?;
    let proof = exact_regular_file(&config.proof)?;
    let statement_bytes = exact_regular_file(&config.statement)?;
    let runtime_replay = validate_runtime_replay(&config)?;
    ensure!(!sbf.is_empty(), "v5 SBF is empty");
    ensure!(!proof.is_empty(), "v5 proof is empty");
    ensure!(
        u32::try_from(proof.len()).is_ok(),
        "v5 proof exceeds tag-0 u32 framing"
    );
    ensure!(
        config.program_max_len >= sbf.len(),
        "program max length is smaller than the exact v5 SBF"
    );
    let (sbf_provenance, sbf_profile) =
        validate_current_provenance(&sbf_provenance_bytes, &config.sbf, &sbf)?;
    validate_sbf_profile_for_network(config.network, sbf_profile)?;
    let statement = decode_spend_statement_sidecar(&statement_bytes)?;
    verify_runtime_statement_and_wire(config.network, program.pubkey(), pool.pubkey(), &statement)?;
    let (least_good_selector, good_candidates) = verify_host_proof_and_least_good(
        program.pubkey(),
        proof_account.pubkey(),
        &proof,
        &statement,
    )?;

    let rpc_origin_redacted = rpc_origin(&config.rpc_url)?;
    let ws_origin_redacted = config.ws_url.as_deref().map(websocket_origin).transpose()?;
    let rpc = Rpc::new(config.rpc_url.clone())?;
    let observed_genesis_hash = rpc.genesis_hash()?;
    ensure!(
        observed_genesis_hash == config.network.expected_genesis_hash(),
        "v5 readiness requires the exact {} genesis",
        config.network.network()
    );
    let (observed_solana_core, observed_feature_set) =
        match (&config.expected_solana_core, config.expected_feature_set) {
            (Some(expected_solana_core), Some(expected_feature_set)) => {
                let (observed_solana_core, observed_feature_set) = rpc_runtime_identity(&rpc)?;
                ensure!(
                    observed_solana_core == *expected_solana_core,
                    "RPC solana-core version differs from the frozen runtime gate"
                );
                ensure!(
                    observed_feature_set == expected_feature_set,
                    "RPC feature-set differs from the explicit runtime gate"
                );
                (Some(observed_solana_core), Some(observed_feature_set))
            }
            (None, None) => (None, None),
            _ => bail!("runtime-version gate is incomplete"),
        };

    let program_snapshot = deployed_program_exact(
        &rpc,
        &program.pubkey(),
        &sbf,
        config.program_max_len,
        &expected_upgrade_authority,
    )?;
    if let Some(deployment_buffer) = deployment_buffer.as_ref() {
        ensure!(
            rpc.account(&deployment_buffer.pubkey())?.is_none(),
            "v5 mainnet deployment buffer account is not fresh"
        );
    }
    ensure!(
        rpc.account(&pool.pubkey())?.is_none(),
        "v5 pool account is not fresh"
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.is_none(),
        "v5 proof account is not fresh"
    );
    let public = statement_public_inputs(&statement);
    let (nullifier_address, _) = atomic_nullifier_address(&program.pubkey(), &public.nullifier);
    ensure_distinct_keys(&[
        payer.pubkey(),
        program.pubkey(),
        pool.pubkey(),
        proof_account.pubkey(),
        nullifier_address,
    ])?;
    ensure!(
        rpc.account(&nullifier_address)?.is_none(),
        "canonical v5 nullifier PDA must be absent"
    );

    let pool_rent = rpc.rent(ATOMIC_POOL_STATE_LEN)?;
    let proof_rent = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len())?;
    let nullifier_rent = rpc.rent(ATOMIC_NULLIFIER_MARKER_LEN)?;
    let (rust_signed_transaction_count, rust_signed_priority_and_signature_fee_bound_lamports) =
        match config.compute_unit_price_microlamports {
            Some(price) => {
                let (transaction_count, fee_bound) =
                    mainnet_priority_and_signature_fee_bound(proof.len(), price)?;
                ensure!(
                    config.fee_reserve_lamports >= fee_bound,
                    "fee reserve is below the checked Rust-signed transaction priority/signature fee bound of {fee_bound} lamports"
                );
                (Some(transaction_count), Some(fee_bound))
            }
            None => (None, None),
        };
    let mut required_lamports = checked_add_lamports(pool_rent, proof_rent, "setup")?;
    required_lamports =
        checked_add_lamports(required_lamports, nullifier_rent, "setup plus nullifier")?;
    required_lamports = checked_add_lamports(
        required_lamports,
        config.fee_reserve_lamports,
        "setup plus fee reserve",
    )?;
    if program_snapshot.is_none() {
        let buffer_rent = rpc.rent(BUFFER_METADATA_BYTES + config.program_max_len)?;
        let programdata_rent = rpc.rent(PROGRAMDATA_METADATA_BYTES + config.program_max_len)?;
        let program_rent = rpc.rent(PROGRAM_ACCOUNT_BYTES)?;
        required_lamports = checked_add_lamports(
            required_lamports,
            buffer_rent.max(programdata_rent),
            "fresh deployment",
        )?;
        required_lamports =
            checked_add_lamports(required_lamports, program_rent, "fresh program account")?;
    }
    let payer_balance_lamports = rpc.balance(&payer.pubkey())?;
    let surplus_lamports = i128::from(payer_balance_lamports) - i128::from(required_lamports);
    ensure!(
        surplus_lamports >= 0,
        "payer does not cover exact rent budget plus explicit fee reserve"
    );

    Ok(V5DevnetReadiness {
        artifact: config.network.readiness_name(),
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        mode: "read_only",
        mutations_performed: false,
        ready: true,
        execution_enabled: true,
        execution_stop_reason: None,
        rpc_origin_redacted,
        ws_origin_redacted,
        expected_genesis_hash: config.network.expected_genesis_hash(),
        observed_genesis_hash,
        expected_solana_core: config.expected_solana_core,
        observed_solana_core,
        expected_feature_set: config.expected_feature_set,
        observed_feature_set,
        runtime_replay_path: runtime_replay.as_ref().map(|(path, _)| path.clone()),
        runtime_replay_sha256: runtime_replay.map(|(_, digest)| digest),
        compute_unit_price_microlamports: config.compute_unit_price_microlamports,
        program_id: program.pubkey().to_string(),
        upgrade_authority: upgrade_authority
            .as_ref()
            .map(|keypair| keypair.pubkey().to_string()),
        deployment_buffer: deployment_buffer
            .as_ref()
            .map(|keypair| keypair.pubkey().to_string()),
        pool: pool.pubkey().to_string(),
        proof_account: proof_account.pubkey().to_string(),
        nullifier_address: nullifier_address.to_string(),
        program_already_deployed: program_snapshot.is_some(),
        proof_bytes: proof.len(),
        proof_sha256: sha256(&proof),
        statement_bytes: statement_bytes.len(),
        statement_sha256: sha256(&statement_bytes),
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        sbf_provenance_path: path_string(&config.sbf_provenance)?,
        sbf_provenance_sha256: sha256(&sbf_provenance_bytes),
        sbf_profile: sbf_profile.label(),
        sbf_build_command: sbf_provenance.command,
        sbf_source_file_count: sbf_provenance.source_files.len(),
        canonical_public_input_digest: canonical_spend_public_input_digest(&statement)?,
        least_good_selector,
        good_candidates,
        payer_balance_lamports,
        required_lamports,
        surplus_lamports,
        rust_signed_transaction_count,
        rust_signed_priority_and_signature_fee_bound_lamports,
        explicit_nonclaims: [
            "Readiness signs and submits no transaction and performs no network mutation.",
            sbf_profile.execution_scope(),
            match config.network {
                V5NetworkPolicy::Devnet => {
                    "A passed devnet readiness result is not a mainnet transaction."
                }
                V5NetworkPolicy::MainnetBeta => {
                    "Mainnet readiness is tied to the exact genesis, runtime identity, SBF, provenance, keys, proof, and statement checked here."
                }
            },
        ],
    })
}

pub(crate) fn readiness(arguments: &[String]) -> Result<V5DevnetReadiness> {
    readiness_from_config(parse_readiness_args(arguments)?)
}

pub(crate) fn mainnet_readiness(arguments: &[String]) -> Result<V5DevnetReadiness> {
    readiness_from_config(parse_mainnet_readiness_args(arguments)?)
}

#[allow(clippy::too_many_lines)]
fn execute_from_config(config: ExecuteConfig) -> Result<V5DevnetExecutionEvidence> {
    let solana_cli_before = exact_executable(&config.solana_cli)?;
    let solana_cli_version = validate_execution_solana_cli(
        config.readiness.network,
        &config.solana_cli,
        &solana_cli_before,
    )?;
    validate_fresh_evidence_destination(&config.evidence)?;

    // This is the last operation before reserving the one-shot evidence file,
    // which is itself the first write of any kind. It repeats every read-only
    // local/RPC readiness gate on the exact execution arguments.
    let readiness = readiness_from_config(config.readiness.clone())?;
    ensure!(
        readiness.ready,
        "v5 {} execution blocked: {}",
        config.readiness.network.network(),
        readiness
            .execution_stop_reason
            .unwrap_or("readiness did not return ready")
    );
    let mut recovery_journal = match &config.run_directory {
        Some(run_directory) => {
            let run_id = format!("v5-mainnet-{}", chrono::Utc::now().format("%Y%m%dT%H%M%SZ"));
            let mut journal =
                crate::spend_mainnet_journal::RecoveryJournal::create(run_directory, run_id)?;
            journal.record_checkpoint(
                "readiness_passed_before_first_network_mutation",
                serde_json::json!({
                    "network": config.readiness.network.network(),
                    "program_id": readiness.program_id,
                    "upgrade_authority": readiness.upgrade_authority,
                    "deployment_buffer": readiness.deployment_buffer,
                    "pool": readiness.pool,
                    "proof_account": readiness.proof_account,
                    "nullifier_address": readiness.nullifier_address,
                    "sbf_sha256": readiness.sbf_sha256,
                    "sbf_provenance_sha256": readiness.sbf_provenance_sha256,
                    "proof_sha256": readiness.proof_sha256,
                    "statement_sha256": readiness.statement_sha256,
                    "expected_solana_core": readiness.expected_solana_core,
                    "expected_feature_set": readiness.expected_feature_set,
                    "runtime_replay_path": readiness.runtime_replay_path,
                    "runtime_replay_sha256": readiness.runtime_replay_sha256,
                    "compute_unit_price_microlamports": readiness.compute_unit_price_microlamports,
                    "solana_cli_sha256": sha256(&solana_cli_before),
                    "solana_cli_version": solana_cli_version.clone(),
                    "rpc_origin_redacted": readiness.rpc_origin_redacted,
                    "ws_origin_redacted": readiness.ws_origin_redacted,
                    "evidence_path": config.evidence,
                    "recovery_policy": "one-shot fail-closed; an incomplete run directory must be reconciled manually and is never resumed automatically",
                }),
            )?;
            Some(journal)
        }
        None => None,
    };
    let evidence_reservation =
        EvidenceReservation::reserve(&config.evidence, config.readiness.network.evidence_name())?;

    let rpc_origin_redacted = rpc_origin(&config.readiness.rpc_url)?;
    let ws_origin_redacted = config
        .readiness
        .ws_url
        .as_deref()
        .map(websocket_origin)
        .transpose()?;
    ensure!(
        ws_origin_redacted == readiness.ws_origin_redacted,
        "mainnet WebSocket endpoint changed after readiness"
    );
    let rpc = Rpc::new(config.readiness.rpc_url.clone())?;
    let genesis_hash = rpc.genesis_hash()?;
    ensure!(
        genesis_hash == config.readiness.network.expected_genesis_hash(),
        "{} genesis changed after readiness",
        config.readiness.network.network()
    );
    if let (Some(expected_solana_core), Some(expected_feature_set)) = (
        config.readiness.expected_solana_core.as_deref(),
        config.readiness.expected_feature_set,
    ) {
        let (observed_solana_core, observed_feature_set) = rpc_runtime_identity(&rpc)?;
        ensure!(
            observed_solana_core == expected_solana_core
                && observed_feature_set == expected_feature_set
                && readiness.observed_solana_core.as_deref() == Some(expected_solana_core)
                && readiness.observed_feature_set == Some(expected_feature_set),
            "mainnet runtime identity changed after readiness"
        );
    }
    let runtime_replay = validate_runtime_replay(&config.readiness)?;
    ensure!(
        readiness.runtime_replay_path == runtime_replay.as_ref().map(|(path, _)| path.clone())
            && readiness.runtime_replay_sha256 == runtime_replay.map(|(_, digest)| digest),
        "mainnet runtime replay changed after readiness"
    );

    let payer = secure_keypair_0600(&config.readiness.payer_keypair)?;
    let program = secure_keypair_0600(&config.readiness.program_keypair)?;
    let pool = secure_keypair_0600(&config.readiness.pool_keypair)?;
    let proof_account = secure_keypair_0600(&config.readiness.proof_account_keypair)?;
    let upgrade_authority = config
        .readiness
        .upgrade_authority_keypair
        .as_ref()
        .map(|path| secure_keypair_0600(path))
        .transpose()?;
    let deployment_buffer = config
        .readiness
        .deployment_buffer_keypair
        .as_ref()
        .map(|path| secure_keypair_0600(path))
        .transpose()?;
    let mut runtime_keys = vec![
        payer.pubkey(),
        program.pubkey(),
        pool.pubkey(),
        proof_account.pubkey(),
    ];
    runtime_keys.extend(upgrade_authority.as_ref().map(Signer::pubkey));
    runtime_keys.extend(deployment_buffer.as_ref().map(Signer::pubkey));
    ensure_distinct_keys(&runtime_keys)?;
    let program_id = program.pubkey();
    config.readiness.network.validate_program_id(program_id)?;
    let expected_upgrade_authority = upgrade_authority
        .as_ref()
        .map(Signer::pubkey)
        .unwrap_or_else(|| payer.pubkey());
    ensure!(
        readiness.program_id == program_id.to_string()
            && readiness.upgrade_authority
                == upgrade_authority
                    .as_ref()
                    .map(|keypair| keypair.pubkey().to_string())
            && readiness.deployment_buffer
                == deployment_buffer
                    .as_ref()
                    .map(|keypair| keypair.pubkey().to_string())
            && readiness.pool == pool.pubkey().to_string()
            && readiness.proof_account == proof_account.pubkey().to_string(),
        "execution keypairs differ from the immediately preceding readiness result"
    );

    let solana_cli = exact_executable(&config.solana_cli)?;
    ensure!(
        solana_cli == solana_cli_before,
        "Solana CLI changed after readiness"
    );
    let sbf = exact_regular_file(&config.readiness.sbf)?;
    let sbf_provenance_bytes = exact_regular_file(&config.readiness.sbf_provenance)?;
    let (_sbf_provenance, sbf_profile) =
        validate_current_provenance(&sbf_provenance_bytes, &config.readiness.sbf, &sbf)?;
    validate_sbf_profile_for_network(config.readiness.network, sbf_profile)?;
    ensure!(
        readiness.sbf_profile == sbf_profile.label(),
        "SBF profile changed after readiness"
    );
    let proof = exact_regular_file(&config.readiness.proof)?;
    let statement_bytes = exact_regular_file(&config.readiness.statement)?;
    ensure!(!proof.is_empty(), "v5 execution proof is empty");
    ensure!(
        config.readiness.program_max_len >= sbf.len(),
        "v5 SBF exceeds explicit program max length"
    );
    let statement = decode_spend_statement_sidecar(&statement_bytes)?;
    verify_runtime_statement_and_wire(
        config.readiness.network,
        program_id,
        pool.pubkey(),
        &statement,
    )?;
    let (least_good_selector, good_candidates) =
        verify_host_proof_and_least_good(program_id, proof_account.pubkey(), &proof, &statement)?;
    ensure!(
        statement.sequence == 0,
        "v5 execution is restricted to fresh sequence 0"
    );
    ensure!(
        readiness.sbf_sha256 == sha256(&sbf)
            && readiness.sbf_provenance_sha256 == sha256(&sbf_provenance_bytes)
            && readiness.proof_sha256 == sha256(&proof)
            && readiness.statement_sha256 == sha256(&statement_bytes)
            && readiness.least_good_selector == least_good_selector
            && readiness.good_candidates == good_candidates,
        "execution artifacts differ from the immediately preceding readiness result"
    );
    ensure!(
        rpc.balance(&payer.pubkey())? >= readiness.required_lamports,
        "payer balance fell below the readiness budget before deployment"
    );

    let public = statement_public_inputs(&statement);
    let (nullifier_address, _) = atomic_nullifier_address(&program_id, &public.nullifier);
    ensure_distinct_keys(&[
        payer.pubkey(),
        program_id,
        pool.pubkey(),
        proof_account.pubkey(),
        nullifier_address,
    ])?;
    ensure!(
        readiness.nullifier_address == nullifier_address.to_string(),
        "runtime nullifier PDA differs from readiness"
    );
    ensure!(
        rpc.account(&pool.pubkey())?.is_none()
            && rpc.account(&proof_account.pubkey())?.is_none()
            && rpc.account(&nullifier_address)?.is_none(),
        "pool, proof, or nullifier ceased to be fresh after evidence reservation"
    );
    if let Some(deployment_buffer) = deployment_buffer.as_ref() {
        ensure!(
            rpc.account(&deployment_buffer.pubkey())?.is_none(),
            "mainnet deployment buffer ceased to be fresh after evidence reservation"
        );
    }
    if rpc.account(&program_id)?.is_some() {
        ensure!(
            deployed_program_exact(
                &rpc,
                &program_id,
                &sbf,
                config.readiness.program_max_len,
                &expected_upgrade_authority,
            )?
            .is_some(),
            "existing program differs from the exact declared-profile SBF"
        );
    }

    let deployment = match config.readiness.network {
        V5NetworkPolicy::Devnet => {
            let deploy_config = deployment_adapter(&config);
            deploy_if_needed(
                &rpc,
                &program_id,
                &expected_upgrade_authority,
                config.readiness.network.cluster_policy(),
                &deploy_config,
                &sbf,
            )?
        }
        V5NetworkPolicy::MainnetBeta => deploy_mainnet_if_needed(
            &rpc,
            &config,
            recovery_journal
                .as_mut()
                .context("mainnet deployment has no recovery journal")?,
            &program_id,
            &expected_upgrade_authority,
            &sbf,
        )?,
    };
    let upgradeable_program_before_setup = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.readiness.program_max_len,
        &expected_upgrade_authority,
    )?
    .context("exact declared-profile program missing before v5 setup")?;
    ensure!(
        rpc.account(&pool.pubkey())?.is_none()
            && rpc.account(&proof_account.pubkey())?.is_none()
            && rpc.account(&nullifier_address)?.is_none(),
        "deployment raced with fresh v5 state identities"
    );

    let pool_rent = rpc.rent(ATOMIC_POOL_STATE_LEN)?;
    let proof_rent = rpc.rent(PROOF_ACCOUNT_HEADER_LEN + proof.len())?;
    let nullifier_marker_rent_lamports = rpc.rent(ATOMIC_NULLIFIER_MARKER_LEN)?;
    let post_deploy_required = pool_rent
        .checked_add(proof_rent)
        .and_then(|value| value.checked_add(nullifier_marker_rent_lamports))
        .and_then(|value| value.checked_add(config.readiness.fee_reserve_lamports))
        .context("post-deployment v5 budget overflow")?;
    ensure!(
        rpc.balance(&payer.pubkey())? >= post_deploy_required,
        "payer cannot cover pool/proof/nullifier rent plus fee reserve after deployment"
    );

    let mut setup_transactions = Vec::new();
    let create_pool = system_instruction::create_account(
        &payer.pubkey(),
        &pool.pubkey(),
        pool_rent,
        u64::try_from(ATOMIC_POOL_STATE_LEN).context("pool account length exceeds u64")?,
        &program_id,
    );
    let mut create_pool_instructions = Vec::with_capacity(2);
    if let Some(price) = compute_unit_price_instruction(&config.readiness) {
        create_pool_instructions.push(price);
    }
    create_pool_instructions.push(create_pool);
    let create_pool_tx = signed_transaction(
        &payer,
        &[&pool],
        &create_pool_instructions,
        rpc.latest_blockhash()?,
    );
    setup_transactions.push(submit_signed_transaction(
        &rpc,
        config.readiness.network,
        &mut recovery_journal,
        &create_pool_tx,
        "pool_create",
        "v5_create_pool_account",
    )?);
    let zeroed_pool = rpc
        .account(&pool.pubkey())?
        .context("new v5 pool account missing")?;
    ensure!(
        zeroed_pool_account_exact(&zeroed_pool, &program_id, pool_rent),
        "new v5 pool account image is not exactly zeroed"
    );

    let initialize_pool = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(pool.pubkey(), true)],
        data: to_vec(&AspisInstruction::InitializeAtomicPool {
            sequence: 0,
            anchor: public.current_anchor,
            domain_tag: config.readiness.network.domain_tag().to_vec(),
        })?,
    };
    let mut initialize_pool_instructions = Vec::with_capacity(2);
    if let Some(price) = compute_unit_price_instruction(&config.readiness) {
        initialize_pool_instructions.push(price);
    }
    initialize_pool_instructions.push(initialize_pool);
    let initialize_pool_tx = signed_transaction(
        &payer,
        &[&pool],
        &initialize_pool_instructions,
        rpc.latest_blockhash()?,
    );
    let initialize_pool_wire = bincode::serialize(&initialize_pool_tx)?;
    let initialize_pool_simulation = rpc.simulate_exact(&initialize_pool_wire)?;
    ensure!(
        initialize_pool_simulation.error.is_none(),
        "tag-63 pool initialization simulation rejected: {:?}",
        initialize_pool_simulation.error
    );
    ensure!(
        rpc.account(&pool.pubkey())?.as_ref() == Some(&zeroed_pool),
        "tag-63 simulation changed the pool"
    );
    setup_transactions.push(submit_signed_transaction(
        &rpc,
        config.readiness.network,
        &mut recovery_journal,
        &initialize_pool_tx,
        "pool_initialize_tag63",
        "v5_tag63_initialize_pool",
    )?);
    let pool_before_snapshot = rpc
        .account(&pool.pubkey())?
        .context("initialized v5 pool missing")?;
    ensure!(
        initialized_pool_account_exact(
            &pool_before_snapshot,
            &program_id,
            pool_rent,
            0,
            public.current_anchor,
            public.deployment_domain,
        ),
        "tag-63 pool image differs from sequence-0 statement/domain"
    );
    let pool_before_state = AtomicPoolStateV2::decode(&pool_before_snapshot.data)
        .map_err(|error| anyhow!("decode initialized v5 pool: {error:?}"))?;

    let mut create_and_init_proof_instructions = super::create_and_init_proof_instructions(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        proof_rent,
        proof.len(),
    )?;
    if let Some(price) = compute_unit_price_instruction(&config.readiness) {
        create_and_init_proof_instructions.insert(1, price);
    }
    let create_and_init_proof = signed_transaction(
        &payer,
        &[&proof_account],
        &create_and_init_proof_instructions,
        rpc.latest_blockhash()?,
    );
    let create_and_init_wire = bincode::serialize(&create_and_init_proof)?;
    let create_and_init_simulation = rpc.simulate_exact(&create_and_init_wire)?;
    ensure!(
        create_and_init_simulation.error.is_none()
            && create_and_init_simulation
                .units
                .is_some_and(|units| units < u64::from(CU_LIMIT)),
        "atomic proof create/tag-0 simulation failed or exceeded CU"
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.is_none(),
        "proof create/tag-0 simulation changed the proof account"
    );
    setup_transactions.push(submit_signed_transaction(
        &rpc,
        config.readiness.network,
        &mut recovery_journal,
        &create_and_init_proof,
        "proof_create_and_initialize_tag0",
        "v5_create_and_tag0_proof",
    )?);
    let initialized_proof = rpc
        .account(&proof_account.pubkey())?
        .context("tag-0 proof account missing")?;
    ensure!(
        initialized_proof.owner == program_id
            && !initialized_proof.executable
            && initialized_proof.lamports == proof_rent
            && initialized_proof.data
                == expected_proof_account(&vec![0u8; proof.len()], payer.pubkey(), false),
        "tag-0 proof image differs before upload"
    );

    let proof_upload_transaction_count = proof.len().div_ceil(UPLOAD_CHUNK_BYTES);
    let proof_upload_finality_windows =
        proof_upload_transaction_count.div_ceil(UPLOAD_WINDOW_TRANSACTIONS);
    let upload_transactions = upload_proof_chunks_for_network(
        &rpc,
        &config.readiness,
        &mut recovery_journal,
        &program_id,
        &payer,
        &proof_account,
        &proof,
    )?;
    ensure!(
        upload_transactions.len() == proof_upload_transaction_count,
        "proof upload transaction count drift"
    );
    setup_transactions.extend(upload_transactions);
    let uploaded_proof = rpc
        .account(&proof_account.pubkey())?
        .context("uploaded v5 proof account missing")?;
    ensure!(
        uploaded_proof.data == expected_proof_account(&proof, payer.pubkey(), false),
        "uploaded proof bytes/header differ before tag-62"
    );

    let finalize_proof = proof_instruction(
        &program_id,
        payer.pubkey(),
        proof_account.pubkey(),
        &AspisInstruction::FinalizeProof,
    )?;
    let mut finalize_proof_instructions = Vec::with_capacity(2);
    if let Some(price) = compute_unit_price_instruction(&config.readiness) {
        finalize_proof_instructions.push(price);
    }
    finalize_proof_instructions.push(finalize_proof);
    let finalize_proof_tx = signed_transaction(
        &payer,
        &[],
        &finalize_proof_instructions,
        rpc.latest_blockhash()?,
    );
    let finalize_proof_wire = bincode::serialize(&finalize_proof_tx)?;
    let finalize_proof_simulation = rpc.simulate_exact(&finalize_proof_wire)?;
    ensure!(
        finalize_proof_simulation.error.is_none(),
        "tag-62 proof finalization simulation rejected: {:?}",
        finalize_proof_simulation.error
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.as_ref() == Some(&uploaded_proof),
        "tag-62 simulation changed the uploaded proof"
    );
    setup_transactions.push(submit_signed_transaction(
        &rpc,
        config.readiness.network,
        &mut recovery_journal,
        &finalize_proof_tx,
        "proof_finalize_tag62",
        "v5_tag62_finalize_proof",
    )?);
    let finalized_proof = rpc
        .account(&proof_account.pubkey())?
        .context("sealed v5 proof account missing")?;
    ensure!(
        finalized_proof.owner == program_id
            && !finalized_proof.executable
            && finalized_proof.lamports == proof_rent
            && finalized_proof.data == expected_proof_account(&proof, payer.pubkey(), true),
        "tag-62 sealed proof image differs byte-for-byte"
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
        .context("sealed v5 proof accepted a hostile upload")?;
    let post_finalize_upload_rejected =
        post_finalize_upload_error == invalid_account_data_simulation_error(0);
    ensure!(
        post_finalize_upload_rejected,
        "sealed proof returned an unexpected upload rejection: {post_finalize_upload_error}"
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
        .context("sealed v5 proof accepted a second finalization")?;
    let post_finalize_second_finalize_rejected =
        post_finalize_second_finalize_error == invalid_account_data_simulation_error(0);
    ensure!(
        post_finalize_second_finalize_rejected,
        "sealed proof returned an unexpected second-finalize rejection: {post_finalize_second_finalize_error}"
    );
    ensure!(
        rpc.account(&proof_account.pubkey())?.as_ref() == Some(&finalized_proof),
        "hostile sealed-proof simulations changed the retained proof"
    );

    let tag67 = build_tag67_instruction(
        program_id,
        proof_account.pubkey(),
        pool.pubkey(),
        nullifier_address,
        payer.pubkey(),
        &statement,
    )?;
    let tag67_account_metas = tag67_meta_evidence(&tag67)?;
    let tag67_instruction_sha256 = sha256(&tag67.data);
    let tag67_instruction_bytes = tag67.data.len();
    let mut final_instructions = vec![
        ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
        ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
    ];
    if let Some(price) = compute_unit_price_instruction(&config.readiness) {
        final_instructions.push(price);
    }
    final_instructions.push(tag67.clone());
    let final_tx = signed_transaction(&payer, &[], &final_instructions, rpc.latest_blockhash()?);
    let final_wire = bincode::serialize(&final_tx)?;
    let final_wire_sha256 = sha256(&final_wire);
    let final_message_sha256 = sha256(&bincode::serialize(&final_tx.message)?);

    // No RPC call intervenes between this exact executable/ProgramData
    // snapshot and simulation of the one serialized signed wire.
    let upgradeable_program_before_final_simulation = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.readiness.program_max_len,
        &expected_upgrade_authority,
    )?
    .context("exact declared-profile program missing before tag-67 simulation")?;
    let upgradeable_program_before_final_simulation_continuity =
        upgradeable_program_before_final_simulation
            .continuity_from(&upgradeable_program_before_setup);
    ensure!(
        upgradeable_program_before_final_simulation_continuity.all_unchanged(),
        "program/ProgramData changed between setup and tag-67 simulation"
    );
    let final_simulation = rpc.simulate_exact(&final_wire)?;
    ensure!(
        final_simulation.error.is_none(),
        "exact signed tag-67 simulation rejected: {:?}",
        final_simulation.error
    );
    let final_transaction_simulation_cu = final_simulation
        .units
        .context("tag-67 simulation omitted CU")?;
    ensure!(
        final_transaction_simulation_cu < u64::from(CU_LIMIT),
        "tag-67 simulation exceeded the 1.4M CU limit"
    );
    require_exact_program_success(&final_simulation.logs, program_id)?;
    ensure!(
        rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_before_snapshot)
            && rpc.account(&nullifier_address)?.is_none()
            && rpc.account(&proof_account.pubkey())?.as_ref() == Some(&finalized_proof),
        "tag-67 simulation changed pool/nullifier/proof state"
    );

    let final_transaction = submit_signed_transaction(
        &rpc,
        config.readiness.network,
        &mut recovery_journal,
        &final_tx,
        "tag67_verify_and_apply",
        "v5_tag67_verify_and_apply_retaining_proof",
    )?;
    ensure!(
        final_transaction.serialized_transaction_sha256 == final_wire_sha256,
        "submitted tag-67 wire hash differs from simulated wire"
    );
    let final_transaction_landed_cu = final_transaction
        .compute_units_consumed
        .context("finalized tag-67 omitted computeUnitsConsumed")?;
    ensure!(
        final_transaction_landed_cu < u64::from(CU_LIMIT),
        "finalized tag-67 exceeded the 1.4M CU limit"
    );
    let final_signature = final_tx.signatures[0];
    let (refetched_wire, refetched_transaction) = rpc.transaction_wire(&final_signature)?;
    let final_transaction_refetched_wire_exact =
        refetched_wire == final_wire && refetched_transaction.signatures == final_tx.signatures;
    let expected_versioned_message = VersionedMessage::Legacy(final_tx.message.clone());
    let final_transaction_refetched_message_exact =
        refetched_transaction.message == expected_versioned_message;
    ensure!(
        final_transaction_refetched_wire_exact && final_transaction_refetched_message_exact,
        "finalized tag-67 transaction differs from the simulated/submitted bytes"
    );

    let upgradeable_program_after_finality = deployed_program_exact(
        &rpc,
        &program_id,
        &sbf,
        config.readiness.program_max_len,
        &expected_upgrade_authority,
    )?
    .context("exact declared-profile program missing after tag-67 finality")?;
    let upgradeable_program_after_finality_continuity =
        upgradeable_program_after_finality.continuity_from(&upgradeable_program_before_setup);
    ensure!(
        upgradeable_program_after_finality_continuity.all_unchanged(),
        "program/ProgramData changed across finalized tag-67"
    );

    let pool_after_snapshot = rpc
        .account(&pool.pubkey())?
        .context("v5 pool missing after tag-67")?;
    let pool_after_state = AtomicPoolStateV2::decode(&pool_after_snapshot.data)
        .map_err(|error| anyhow!("decode v5 pool after tag-67: {error:?}"))?;
    ensure!(
        pool_after_snapshot.owner == program_id
            && !pool_after_snapshot.executable
            && pool_after_snapshot.lamports == pool_before_snapshot.lamports
            && pool_after_state.sequence == 1
            && pool_after_state.anchor == public.output_anchor
            && pool_after_state.deployment_domain == public.deployment_domain,
        "tag-67 pool poststate differs from sequence-1/output-anchor/same-domain state"
    );
    let nullifier_after_snapshot = rpc
        .account(&nullifier_address)?
        .context("v5 nullifier marker missing after tag-67")?;
    ensure!(
        nullifier_after_snapshot.owner == program_id
            && !nullifier_after_snapshot.executable
            && nullifier_after_snapshot.lamports >= nullifier_marker_rent_lamports
            && nullifier_after_snapshot.data
                == expected_nullifier_marker(pool.pubkey(), public.nullifier),
        "tag-67 nullifier marker differs from the canonical image or is below rent"
    );
    let retained_proof_after = rpc
        .account(&proof_account.pubkey())?
        .context("tag-67 did not retain the sealed proof account")?;
    let retained_proof_byte_for_byte_exact = retained_proof_after == finalized_proof;
    ensure!(
        retained_proof_byte_for_byte_exact,
        "tag-67 changed retained proof bytes/lamports/owner"
    );

    let (final_fee_lamports, pre_balances, post_balances, final_logs) =
        rpc.transaction_fee_balances_and_logs(&final_signature)?;
    require_exact_program_success(&final_logs, program_id)?;
    let final_transaction_program_success_log_exact = true;
    let retained_proof_balance_equation = retained_proof_balance_evidence(
        &final_tx.message.account_keys,
        final_fee_lamports,
        &pre_balances,
        &post_balances,
        payer.pubkey(),
        proof_account.pubkey(),
        nullifier_address,
        finalized_proof.lamports,
    )?;
    ensure!(
        retained_proof_balance_equation.nullifier_funding_lamports
            == nullifier_marker_rent_lamports
                .saturating_sub(retained_proof_balance_equation.nullifier_pre_lamports)
            && retained_proof_balance_equation.nullifier_post_lamports
                == retained_proof_balance_equation
                    .nullifier_pre_lamports
                    .checked_add(retained_proof_balance_equation.nullifier_funding_lamports)
                    .context("tag-67 nullifier balance overflow")?,
        "tag-67 nullifier funding does not match the supported absent/prefunded marker path"
    );

    let mut replay_tag67 = tag67;
    replay_tag67.data[1..33].copy_from_slice(&public.output_anchor);
    validate_tag67_instruction(
        &replay_tag67,
        program_id,
        proof_account.pubkey(),
        pool.pubkey(),
        nullifier_address,
        payer.pubkey(),
    )?;
    let replay_public =
        aspis_verifier::v5_full_transaction::parse_v5_full_cu_public_inputs(&replay_tag67.data)
            .map_err(|error| anyhow!("parse replay tag-67 public wire: {error:?}"))?;
    ensure!(
        replay_public.current_anchor == pool_after_state.anchor
            && replay_public.nullifier == public.nullifier,
        "replay wire is not bound to poststate anchor and the same nullifier"
    );
    let mut replay_instructions = vec![
        ComputeBudgetInstruction::set_compute_unit_limit(CU_LIMIT),
        ComputeBudgetInstruction::request_heap_frame(HEAP_FRAME_BYTES),
    ];
    if let Some(price) = compute_unit_price_instruction(&config.readiness) {
        replay_instructions.push(price);
    }
    replay_instructions.push(replay_tag67);
    let replay_tx = signed_transaction(&payer, &[], &replay_instructions, rpc.latest_blockhash()?);
    let replay_simulation_error = rpc
        .simulate_exact(&bincode::serialize(&replay_tx)?)?
        .error
        .context("same-nullifier poststate replay unexpectedly accepted")?;
    let replay_expected_nullifier_error_exact = replay_simulation_error
        == custom_simulation_error(
            match config.readiness.network {
                V5NetworkPolicy::Devnet => DEVNET_TAG67_INSTRUCTION_INDEX,
                V5NetworkPolicy::MainnetBeta => MAINNET_TAG67_INSTRUCTION_INDEX,
            },
            ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT,
        );
    ensure!(
        replay_expected_nullifier_error_exact,
        "same-nullifier replay returned an unexpected rejection: {replay_simulation_error}"
    );
    let replay_pool_unchanged = rpc.account(&pool.pubkey())?.as_ref() == Some(&pool_after_snapshot);
    let replay_nullifier_unchanged =
        rpc.account(&nullifier_address)?.as_ref() == Some(&nullifier_after_snapshot);
    let replay_proof_unchanged =
        rpc.account(&proof_account.pubkey())?.as_ref() == Some(&retained_proof_after);
    ensure!(
        replay_pool_unchanged && replay_nullifier_unchanged && replay_proof_unchanged,
        "same-nullifier replay simulation changed pool/nullifier/proof"
    );
    let nullifier_landing_path = if retained_proof_balance_equation.nullifier_pre_lamports == 0 {
        "absent_create_account"
    } else {
        "system_owned_prefunded_transfer_if_needed_allocate_assign"
    };

    let mut evidence = V5DevnetExecutionEvidence {
        artifact: config.readiness.network.evidence_name(),
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        network: config.readiness.network.network(),
        genesis_hash,
        rpc_origin_redacted,
        ws_origin_redacted,
        readiness,
        program_id: program_id.to_string(),
        payer: payer.pubkey().to_string(),
        pool: pool.pubkey().to_string(),
        proof_account: proof_account.pubkey().to_string(),
        nullifier_address: nullifier_address.to_string(),
        solana_cli_path: path_string(&config.solana_cli)?,
        solana_cli_bytes: solana_cli.len(),
        solana_cli_sha256: sha256(&solana_cli),
        solana_cli_version,
        sbf_path: path_string(&config.readiness.sbf)?,
        sbf_bytes: sbf.len(),
        sbf_sha256: sha256(&sbf),
        sbf_provenance_path: path_string(&config.readiness.sbf_provenance)?,
        sbf_provenance_sha256: sha256(&sbf_provenance_bytes),
        proof_path: path_string(&config.readiness.proof)?,
        proof_bytes: proof.len(),
        proof_sha256: sha256(&proof),
        statement_path: path_string(&config.readiness.statement)?,
        statement_sha256: sha256(&statement_bytes),
        canonical_public_input_digest: canonical_spend_public_input_digest(&statement)?,
        least_good_selector,
        good_candidates,
        program_max_len: config.readiness.program_max_len,
        deployment,
        setup_transactions,
        proof_upload_chunk_bytes: UPLOAD_CHUNK_BYTES,
        proof_upload_transaction_count,
        proof_upload_finality_windows,
        upgradeable_program_before_setup: upgradeable_program_before_setup.evidence(),
        upgradeable_program_before_final_simulation:
            upgradeable_program_before_final_simulation.evidence(),
        upgradeable_program_before_final_simulation_continuity,
        upgradeable_program_after_finality: upgradeable_program_after_finality.evidence(),
        upgradeable_program_after_finality_continuity,
        pool_before: pool_before_snapshot.evidence(pool.pubkey()),
        pool_after: pool_after_snapshot.evidence(pool.pubkey()),
        sequence_before: pool_before_state.sequence,
        sequence_after: pool_after_state.sequence,
        current_anchor_hex: spend_hex(&public.current_anchor),
        output_anchor_hex: spend_hex(&public.output_anchor),
        deployment_domain_hex: spend_hex(&public.deployment_domain),
        sealed_proof_before: finalized_proof.evidence(proof_account.pubkey()),
        retained_proof_after: retained_proof_after.evidence(proof_account.pubkey()),
        retained_proof_byte_for_byte_exact,
        post_finalize_upload_rejected,
        post_finalize_upload_error,
        post_finalize_second_finalize_rejected,
        post_finalize_second_finalize_error,
        tag67_instruction_bytes,
        tag67_instruction_sha256,
        tag67_account_metas,
        tag67_compute_unit_limit: CU_LIMIT,
        tag67_heap_frame_bytes: HEAP_FRAME_BYTES,
        tag67_compute_unit_price_microlamports: config
            .readiness
            .compute_unit_price_microlamports,
        final_transaction,
        final_transaction_simulation_cu,
        final_transaction_landed_cu,
        final_transaction_wire_sha256: final_wire_sha256,
        final_transaction_message_sha256: final_message_sha256,
        final_transaction_submitted_identically_to_simulation: true,
        final_transaction_refetched_wire_exact,
        final_transaction_refetched_message_exact,
        final_transaction_program_success_log_exact,
        retained_proof_balance_equation,
        nullifier_observed_before_simulation: None,
        nullifier_landing_path,
        nullifier_after: nullifier_after_snapshot.evidence(nullifier_address),
        nullifier_marker_rent_lamports,
        replay_simulation_rejected: true,
        replay_simulation_error,
        replay_expected_nullifier_error_exact,
        replay_pool_unchanged,
        replay_nullifier_unchanged,
        replay_proof_unchanged,
        evidence_path: path_string(&config.evidence)?,
        evidence_file_mode: 0o444,
        explicit_scope: [
            sbf_profile.execution_scope(),
            "The retained proof account is sealed, read-only, non-signing, and unchanged by tag 67.",
            "Deployment, pool creation/tag63, proof creation/tag0, uploads, and tag62 are setup writes.",
            match config.readiness.network {
                V5NetworkPolicy::Devnet => {
                    "This finalized evidence records the devnet rehearsal; mainnet remains a separate deployment."
                }
                V5NetworkPolicy::MainnetBeta => {
                    "This finalized evidence records the exact frozen-production Tag-67 mainnet-beta execution."
                }
            },
        ],
    };
    let evidence_mode = evidence_reservation.commit(&evidence)?;
    ensure!(
        evidence_mode == 0o444,
        "final v5 evidence mode is not immutable 0444"
    );
    evidence.evidence_file_mode = evidence_mode;
    if let Some(journal) = recovery_journal.as_mut() {
        journal.record_checkpoint(
            "tag67_finalized_and_evidence_committed",
            serde_json::json!({
                "signature": evidence.final_transaction.signature,
                "finalized_slot": evidence.final_transaction.finalized_slot,
                "landed_cu": evidence.final_transaction_landed_cu,
                "evidence_path": evidence.evidence_path,
                "pool_after": evidence.pool_after.address,
                "nullifier_after": evidence.nullifier_after.address,
            }),
        )?;
        journal.complete("v5_tag67_finalized_and_evidence_committed")?;
    }
    Ok(evidence)
}

pub(crate) fn execute(arguments: &[String]) -> Result<V5DevnetExecutionEvidence> {
    execute_from_config(parse_execute_args(arguments)?)
}

pub(crate) fn execute_mainnet(arguments: &[String]) -> Result<V5DevnetExecutionEvidence> {
    execute_from_config(parse_mainnet_execute_args(arguments)?)
}

#[cfg(test)]
mod tests {
    use aspis_core::field::M31;

    use super::*;

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    fn sample_provenance(root: &Path, sbf: &Path) -> V5SbfProvenance {
        let config = BuildConfig {
            cargo_build_sbf: PathBuf::from("/tools/cargo-build-sbf"),
            sbf_sdk: PathBuf::from("/sdk/sbf"),
            platform_tools_root: PathBuf::from("/tools/platform-tools"),
            build_output_dir: PathBuf::from("/isolated/build"),
            sbf_output: sbf.to_path_buf(),
            provenance_output: PathBuf::new(),
        };
        let identity = SourceFileIdentity {
            path: "Cargo.lock".to_owned(),
            bytes: 1,
            sha256: "00".repeat(32),
        };
        V5SbfProvenance {
            artifact: SBF_PROVENANCE_ARTIFACT.to_owned(),
            schema_version: SBF_PROVENANCE_SCHEMA_VERSION,
            generated_at_utc: "2026-07-22T00:00:00Z".to_owned(),
            git_head: "0".repeat(40),
            cargo_build_sbf_path: path_string(&config.cargo_build_sbf).unwrap(),
            cargo_build_sbf_bytes: 1,
            cargo_build_sbf_sha256: "00".repeat(32),
            cargo_build_sbf_version:
                "solana-cargo-build-sbf 2.3.0\nplatform-tools v1.48\nrustc 1.84.1".to_owned(),
            sbf_sdk_path: path_string(&config.sbf_sdk).unwrap(),
            platform_tools_root: path_string(&config.platform_tools_root).unwrap(),
            platform_tools_version: PLATFORM_TOOLS_VERSION.to_owned(),
            toolchain_files: vec![SourceFileIdentity {
                path: "/tools/platform-tools/rust/bin/rustc".to_owned(),
                ..identity.clone()
            }],
            manifest_path: path_string(&root.join("programs/aspis-verifier/Cargo.toml")).unwrap(),
            no_default_features: true,
            features: vec![SBF_FEATURE.to_owned()],
            command: expected_build_command(
                &config,
                &root.join("programs/aspis-verifier/Cargo.toml"),
                SBF_FEATURE,
            )
            .unwrap(),
            build_output_dir: path_string(&config.build_output_dir).unwrap(),
            cargo_target_dir: path_string(&config.build_output_dir.join("cargo-target")).unwrap(),
            built_artifact_path: path_string(&config.build_output_dir.join(SBF_OUTPUT_NAME))
                .unwrap(),
            build_stdout_sha256: Some("00".repeat(32)),
            build_stderr_sha256: Some("00".repeat(32)),
            cargo_lock_sha256: "00".repeat(32),
            source_files: vec![identity],
            sbf_path: path_string(sbf).unwrap(),
            sbf_bytes: 1,
            sbf_sha256: "00".repeat(32),
            capture_note: None,
        }
    }

    fn execute_arguments() -> Vec<String> {
        strings(&[
            "--rpc-url",
            "https://api.devnet.solana.com",
            "--payer-keypair",
            "/keys/payer.json",
            "--program-keypair",
            "/keys/program.json",
            "--pool-keypair",
            "/keys/pool.json",
            "--proof-account-keypair",
            "/keys/proof.json",
            "--sbf",
            "/artifacts/v5.so",
            "--sbf-provenance",
            "/artifacts/v5.provenance.json",
            "--proof",
            "/artifacts/proof.bin",
            "--statement",
            "/artifacts/statement.json",
            "--program-max-len",
            "1200000",
            "--fee-reserve-lamports",
            "100000000",
            "--solana-cli",
            "/tools/solana",
            "--evidence",
            "/evidence/v5-final.json",
            "--acknowledgement",
            DEVNET_EXECUTE_ACK,
            "--execute-devnet",
        ])
    }

    fn mainnet_execute_arguments() -> Vec<String> {
        strings(&[
            "--rpc-url",
            "https://mainnet.example.invalid",
            "--ws-url",
            "wss://mainnet.example.invalid",
            "--payer-keypair",
            "/keys/payer.json",
            "--program-keypair",
            "/keys/program.json",
            "--pool-keypair",
            "/keys/pool.json",
            "--proof-account-keypair",
            "/keys/proof.json",
            "--sbf",
            "/artifacts/v5.so",
            "--sbf-provenance",
            "/artifacts/v5.provenance.json",
            "--proof",
            "/artifacts/proof.bin",
            "--statement",
            "/artifacts/statement.json",
            "--program-max-len",
            "1300000",
            "--fee-reserve-lamports",
            "100000000",
            "--expected-solana-core",
            MAINNET_RUNTIME_SOLANA_CORE,
            "--expected-feature-set",
            "3345198602",
            "--upgrade-authority-keypair",
            "/keys/upgrade-authority.json",
            "--deployment-buffer-keypair",
            "/keys/deployment-buffer.json",
            "--runtime-replay",
            "/artifacts/runtime-replay.json",
            "--compute-unit-price-microlamports",
            "1000",
            "--solana-cli",
            "/tools/solana",
            "--evidence",
            "/evidence/v5-mainnet-final.json",
            "--run-directory",
            "/recovery/v5-mainnet-run",
            "--acknowledgement",
            MAINNET_EXECUTE_ACK,
            "--execute-mainnet-beta",
        ])
    }

    fn statement() -> AtomicPaymentStatementV4 {
        let digest =
            |seed: u32| core::array::from_fn(|index| M31(seed + u32::try_from(index).unwrap()));
        AtomicPaymentStatementV4 {
            pool: [9u8; 32],
            sequence: 0,
            spend: aspis_statement::SpendPublic {
                anchor: digest(10),
                nullifier: digest(20),
                output_commitment: digest(30),
                asset_id: M31(17),
                fee: 1,
            },
            output_anchor: digest(40),
            deployment_domain: [5u8; 32],
        }
    }

    #[test]
    fn build_parser_requires_explicit_isolated_absolute_paths() {
        let parsed = parse_build_args(&strings(&[
            "--cargo-build-sbf",
            "/tools/cargo-build-sbf",
            "--sbf-sdk",
            "/sdk/sbf",
            "--platform-tools-root",
            "/tools/platform-tools",
            "--build-output-dir",
            "/tmp/v5-build",
            "--sbf-out",
            "/artifacts/v5.so",
            "--provenance-out",
            "/artifacts/v5.provenance.json",
        ]))
        .unwrap();
        assert_eq!(parsed.build_output_dir, Path::new("/tmp/v5-build"));

        let traversal = strings(&[
            "--cargo-build-sbf",
            "/tools/cargo-build-sbf",
            "--sbf-sdk",
            "/sdk/sbf",
            "--platform-tools-root",
            "/tools/platform-tools",
            "--build-output-dir",
            "/tmp/v5-build",
            "--sbf-out",
            "/artifacts/../production.so",
            "--provenance-out",
            "/artifacts/v5.provenance.json",
        ]);
        assert!(parse_build_args(&traversal).is_err());
    }

    #[test]
    fn artifact_parser_rejects_nonzero_sequence() {
        let program = Pubkey::new_unique().to_string();
        let pool = Pubkey::new_unique().to_string();
        let arguments = vec![
            "--network".to_owned(),
            "devnet".to_owned(),
            "--program-id".to_owned(),
            program,
            "--pool".to_owned(),
            pool,
            "--sequence".to_owned(),
            "1".to_owned(),
            "--proof-out".to_owned(),
            "/artifacts/proof.bin".to_owned(),
            "--statement-out".to_owned(),
            "/artifacts/statement.json".to_owned(),
        ];
        assert!(parse_artifact_args(&arguments).is_err());
    }

    #[test]
    fn mainnet_artifact_parser_pins_network_and_canonical_program_id() {
        let pool = Pubkey::new_unique().to_string();
        let valid = vec![
            "--network".to_owned(),
            "mainnet-beta".to_owned(),
            "--program-id".to_owned(),
            aspis_verifier::id().to_string(),
            "--pool".to_owned(),
            pool.clone(),
            "--sequence".to_owned(),
            "0".to_owned(),
            "--proof-out".to_owned(),
            "/artifacts/proof.bin".to_owned(),
            "--statement-out".to_owned(),
            "/artifacts/statement.json".to_owned(),
        ];
        let parsed = parse_mainnet_artifact_args(&valid).unwrap();
        assert_eq!(parsed.network, V5NetworkPolicy::MainnetBeta);
        assert_eq!(parsed.program_id, aspis_verifier::id());

        let mut wrong_program = valid.clone();
        wrong_program[3] = Pubkey::new_unique().to_string();
        assert!(parse_mainnet_artifact_args(&wrong_program).is_err());

        let mut devnet = valid;
        devnet[1] = "devnet".to_owned();
        assert!(parse_mainnet_artifact_args(&devnet).is_err());
    }

    #[test]
    fn readiness_parser_has_no_execute_surface() {
        assert!(parse_readiness_args(&strings(&["--execute", "true"])).is_err());
    }

    #[test]
    fn execute_parser_requires_both_devnet_interlocks_and_rejects_other_surfaces() {
        let parsed = parse_execute_args(&execute_arguments()).unwrap();
        assert_eq!(parsed.evidence, Path::new("/evidence/v5-final.json"));
        assert_eq!(parsed.readiness_arguments.len(), 22);

        let mut no_flag = execute_arguments();
        no_flag.pop();
        assert!(parse_execute_args(&no_flag).is_err());

        let mut wrong_ack = execute_arguments();
        let ack = wrong_ack
            .iter()
            .position(|value| value == DEVNET_EXECUTE_ACK)
            .unwrap();
        wrong_ack[ack] = "I_ACKNOWLEDGE_MAINNET".to_owned();
        assert!(parse_execute_args(&wrong_ack).is_err());

        let mut mainnet = execute_arguments();
        mainnet.extend(["--execute-mainnet".to_owned(), "true".to_owned()]);
        assert!(parse_execute_args(&mainnet).is_err());

        let mut resume = execute_arguments();
        resume.extend(["--resume-in-progress".to_owned(), "true".to_owned()]);
        assert!(parse_execute_args(&resume).is_err());
    }

    #[test]
    fn mainnet_parser_requires_frozen_runtime_gate_and_irreversible_interlocks() {
        let parsed = parse_mainnet_execute_args(&mainnet_execute_arguments()).unwrap();
        assert_eq!(parsed.readiness.network, V5NetworkPolicy::MainnetBeta);
        assert_eq!(
            parsed.readiness.expected_solana_core.as_deref(),
            Some(MAINNET_RUNTIME_SOLANA_CORE)
        );
        assert_eq!(
            parsed.readiness.expected_feature_set,
            Some(MAINNET_RUNTIME_FEATURE_SET)
        );
        assert_eq!(
            parsed.run_directory.as_deref(),
            Some(Path::new("/recovery/v5-mainnet-run"))
        );
        assert_eq!(
            parsed.readiness.ws_url.as_deref(),
            Some("wss://mainnet.example.invalid")
        );

        let mut no_flag = mainnet_execute_arguments();
        no_flag.pop();
        assert!(parse_mainnet_execute_args(&no_flag).is_err());

        let mut wrong_ack = mainnet_execute_arguments();
        let ack = wrong_ack
            .iter()
            .position(|value| value == MAINNET_EXECUTE_ACK)
            .unwrap();
        wrong_ack[ack] = DEVNET_EXECUTE_ACK.to_owned();
        assert!(parse_mainnet_execute_args(&wrong_ack).is_err());

        let mut new_runtime_without_refreeze = mainnet_execute_arguments();
        let version = new_runtime_without_refreeze
            .iter()
            .position(|value| value == MAINNET_RUNTIME_SOLANA_CORE)
            .unwrap();
        new_runtime_without_refreeze[version] = "4.1.1".to_owned();
        assert!(parse_mainnet_execute_args(&new_runtime_without_refreeze).is_err());

        let mut new_feature_set_without_replay = mainnet_execute_arguments();
        let feature_set = new_feature_set_without_replay
            .iter()
            .position(|value| value == "3345198602")
            .unwrap();
        new_feature_set_without_replay[feature_set] = "3345198603".to_owned();
        assert!(parse_mainnet_execute_args(&new_feature_set_without_replay).is_err());

        let mut devnet_flag = mainnet_execute_arguments();
        devnet_flag.pop();
        devnet_flag.push("--execute-devnet".to_owned());
        assert!(parse_mainnet_execute_args(&devnet_flag).is_err());

        let mut no_ws = mainnet_execute_arguments();
        let ws = no_ws.iter().position(|value| value == "--ws-url").unwrap();
        no_ws.drain(ws..=ws + 1);
        assert!(parse_mainnet_execute_args(&no_ws).is_err());

        let mut tpu = mainnet_execute_arguments();
        tpu.insert(tpu.len() - 1, "--use-tpu-client".to_owned());
        assert!(parse_mainnet_execute_args(&tpu).is_err());

        let mut no_upgrade_authority = mainnet_execute_arguments();
        let authority = no_upgrade_authority
            .iter()
            .position(|value| value == "--upgrade-authority-keypair")
            .unwrap();
        no_upgrade_authority.drain(authority..=authority + 1);
        assert!(parse_mainnet_execute_args(&no_upgrade_authority).is_err());
    }

    #[test]
    fn runtime_domain_is_bound_to_network_and_canonical_mainnet_program() {
        let program = aspis_verifier::id();
        assert_ne!(
            runtime_domain(V5NetworkPolicy::Devnet, program),
            runtime_domain(V5NetworkPolicy::MainnetBeta, program)
        );
        V5NetworkPolicy::MainnetBeta
            .validate_program_id(program)
            .unwrap();
        assert!(V5NetworkPolicy::MainnetBeta
            .validate_program_id(Pubkey::new_unique())
            .is_err());
    }

    #[test]
    fn mainnet_accepts_only_the_frozen_production_sbf_profile() {
        validate_sbf_profile_for_network(
            V5NetworkPolicy::MainnetBeta,
            V5SbfProfile::FrozenProduction,
        )
        .unwrap();
        assert!(validate_sbf_profile_for_network(
            V5NetworkPolicy::MainnetBeta,
            V5SbfProfile::FeatureProbe
        )
        .is_err());
        validate_sbf_profile_for_network(V5NetworkPolicy::Devnet, V5SbfProfile::FeatureProbe)
            .unwrap();
    }

    #[test]
    fn mainnet_compute_unit_price_is_explicit_bounded_and_budgeted() {
        let parsed = parse_mainnet_execute_args(&mainnet_execute_arguments()).unwrap();
        assert_eq!(
            parsed.readiness.compute_unit_price_microlamports,
            Some(1_000)
        );
        let mut excessive = mainnet_execute_arguments();
        let price = excessive.iter().position(|value| value == "1000").unwrap();
        excessive[price] = (MAX_MAINNET_COMPUTE_UNIT_PRICE_MICROLAMPORTS + 1).to_string();
        assert!(parse_mainnet_execute_args(&excessive).is_err());

        let mut explicit_zero = mainnet_execute_arguments();
        let price = explicit_zero
            .iter()
            .position(|value| value == "1000")
            .unwrap();
        explicit_zero[price] = "0".to_owned();
        assert_eq!(
            parse_mainnet_execute_args(&explicit_zero)
                .unwrap()
                .readiness
                .compute_unit_price_microlamports,
            Some(0)
        );

        let mut omitted = mainnet_execute_arguments();
        let price_flag = omitted
            .iter()
            .position(|value| value == "--compute-unit-price-microlamports")
            .unwrap();
        omitted.drain(price_flag..=price_flag + 1);
        assert!(parse_mainnet_execute_args(&omitted).is_err());

        let (transactions, fees) = mainnet_priority_and_signature_fee_bound(77_278, 1_000).unwrap();
        assert_eq!(transactions, 86);
        assert_eq!(fees, 17_320_400);
    }

    #[test]
    fn mainnet_transport_and_cli_identity_are_fail_closed() {
        assert_eq!(
            websocket_origin("wss://example.invalid/private-key").unwrap(),
            "wss://example.invalid/<redacted>"
        );
        assert!(websocket_origin("ws://example.invalid").is_err());
        assert!(websocket_origin("wss://user:secret@example.invalid").is_err());
        assert!(validate_execution_solana_cli(
            V5NetworkPolicy::Devnet,
            Path::new("/unused"),
            b"any"
        )
        .unwrap()
        .is_none());
        assert!(validate_execution_solana_cli(
            V5NetworkPolicy::MainnetBeta,
            Path::new("/unused"),
            b"wrong binary"
        )
        .is_err());
    }

    #[test]
    fn runtime_identity_parser_requires_both_exact_fields() {
        assert_eq!(
            parse_rpc_runtime_identity(&serde_json::json!({
                "solana-core": "4.1.0",
                "feature-set": 3_345_198_602_u64,
            }))
            .unwrap(),
            ("4.1.0".to_owned(), 3_345_198_602)
        );
        assert!(parse_rpc_runtime_identity(&serde_json::json!({
            "solana-core": "4.1.0"
        }))
        .is_err());
        assert!(parse_rpc_runtime_identity(&serde_json::json!({
            "feature-set": 3_345_198_602_u64
        }))
        .is_err());
    }

    #[test]
    fn mainnet_runtime_replay_is_exactly_pinned() {
        let replay = workspace_root()
            .unwrap()
            .join("results/spend/v5-mainnet-runtime-4.1.0-20260723/runtime-replay.json");
        let mut arguments = mainnet_execute_arguments();
        let replay_value = arguments
            .iter()
            .position(|value| value == "/artifacts/runtime-replay.json")
            .unwrap();
        arguments[replay_value] = replay.display().to_string();
        let config = parse_mainnet_execute_args(&arguments).unwrap().readiness;
        let (_, digest) = validate_runtime_replay(&config).unwrap().unwrap();
        assert_eq!(digest, MAINNET_RUNTIME_REPLAY_SHA256);

        let mut wrong = config;
        wrong.runtime_replay = Some(
            workspace_root()
                .unwrap()
                .join("results/spend/v5-mainnet-runtime-4.1.0-20260723/README.md"),
        );
        assert!(validate_runtime_replay(&wrong).is_err());
    }

    #[test]
    fn tag67_wire_and_retained_proof_account_metas_are_exact() {
        let program = Pubkey::new_unique();
        let proof = Pubkey::new_unique();
        let pool = Pubkey::new_unique();
        let nullifier = Pubkey::new_unique();
        let payer = Pubkey::new_unique();
        let instruction =
            build_tag67_instruction(program, proof, pool, nullifier, payer, &statement()).unwrap();
        assert_eq!(instruction.data.len(), 169);
        assert_eq!(
            instruction.accounts,
            vec![
                AccountMeta::new_readonly(proof, false),
                AccountMeta::new(pool, false),
                AccountMeta::new(nullifier, false),
                AccountMeta::new(payer, true),
                AccountMeta::new_readonly(system_program::id(), false),
            ]
        );

        let mut writable_proof = instruction.clone();
        writable_proof.accounts[0] = AccountMeta::new(proof, false);
        assert!(validate_tag67_instruction(
            &writable_proof,
            program,
            proof,
            pool,
            nullifier,
            payer
        )
        .is_err());

        let mut swapped = instruction;
        swapped.accounts.swap(1, 2);
        assert!(
            validate_tag67_instruction(&swapped, program, proof, pool, nullifier, payer).is_err()
        );
    }

    #[test]
    fn retained_proof_balance_equation_is_exact() {
        let payer = Pubkey::new_unique();
        let proof = Pubkey::new_unique();
        let nullifier = Pubkey::new_unique();
        let other = Pubkey::new_unique();
        let keys = [payer, proof, nullifier, other];
        let valid = retained_proof_balance_evidence(
            &keys,
            10,
            &[1_000, 500, 0, 1],
            &[890, 500, 100, 1],
            payer,
            proof,
            nullifier,
            500,
        )
        .unwrap();
        assert!(valid.exact_balance_equation_reconciled);
        assert!(valid.proof_balance_retained_exactly);

        let prefunded = retained_proof_balance_evidence(
            &keys,
            10,
            &[1_000, 500, 40, 1],
            &[930, 500, 100, 1],
            payer,
            proof,
            nullifier,
            500,
        )
        .unwrap();
        assert_eq!(prefunded.nullifier_funding_lamports, 60);

        let overfunded = retained_proof_balance_evidence(
            &keys,
            10,
            &[1_000, 500, 120, 1],
            &[990, 500, 120, 1],
            payer,
            proof,
            nullifier,
            500,
        )
        .unwrap();
        assert_eq!(overfunded.nullifier_funding_lamports, 0);

        assert!(retained_proof_balance_evidence(
            &keys,
            10,
            &[1_000, 500, 0, 1],
            &[890, 499, 100, 1],
            payer,
            proof,
            nullifier,
            500,
        )
        .is_err());
        assert!(retained_proof_balance_evidence(
            &keys,
            9,
            &[1_000, 500, 0, 1],
            &[890, 500, 100, 1],
            payer,
            proof,
            nullifier,
            500,
        )
        .is_err());
    }

    #[test]
    fn program_success_log_must_be_present_exactly_once() {
        let program = Pubkey::new_unique();
        let line = format!("Program {program} success");
        require_exact_program_success(std::slice::from_ref(&line), program).unwrap();
        assert!(require_exact_program_success(&[], program).is_err());
        assert!(require_exact_program_success(&[line.clone(), line], program).is_err());
    }

    #[test]
    fn provenance_shape_accepts_exact_profiles_and_rejects_unknown_artifacts() {
        let root = Path::new("/workspace");
        let sbf = Path::new("/artifacts/v5.so");
        let valid = sample_provenance(root, sbf);
        assert_eq!(
            validate_provenance_shape(&valid, sbf, root).unwrap().1,
            V5SbfProfile::FeatureProbe
        );

        let mut production = valid.clone();
        production.artifact = FROZEN_PRODUCTION_PROVENANCE_ARTIFACT.to_owned();
        production.schema_version = FROZEN_PRODUCTION_PROVENANCE_SCHEMA_VERSION;
        production.features = vec![FROZEN_PRODUCTION_FEATURE.to_owned()];
        production.command = expected_build_command(
            &build_config_from_provenance(&production).unwrap(),
            &root.join("programs/aspis-verifier/Cargo.toml"),
            FROZEN_PRODUCTION_FEATURE,
        )
        .unwrap();
        production.sbf_bytes = FROZEN_PRODUCTION_SBF_BYTES;
        production.sbf_sha256 = FROZEN_PRODUCTION_SBF_SHA256.to_owned();
        production.source_files =
            vec![production.source_files[0].clone(); FROZEN_PRODUCTION_SOURCE_IDENTITIES];
        for (index, identity) in production.source_files.iter_mut().enumerate() {
            identity.path = format!("source/{index:03}");
        }
        production.toolchain_files =
            vec![production.toolchain_files[0].clone(); FROZEN_PRODUCTION_TOOLCHAIN_IDENTITIES];
        for (index, identity) in production.toolchain_files.iter_mut().enumerate() {
            identity.path = format!("/toolchain/{index:03}");
        }
        assert_eq!(
            validate_provenance_shape(&production, sbf, root).unwrap().1,
            V5SbfProfile::FrozenProduction
        );

        let mut unknown = valid;
        unknown.artifact = "untrusted_sbf_provenance".to_owned();
        assert!(validate_provenance_shape(&unknown, sbf, root).is_err());
    }
}
