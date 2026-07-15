use std::{
    fs,
    path::{Component, Path},
    process::Command,
};

use anyhow::{bail, ensure, Context, Result};
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::spend_statement::{
    load_spend_statement_file, spend_hex, spend_recorded_path, SpendStatementFile,
};

const CU_LIMIT: u64 = 1_400_000;
const MIN_SECURITY_BITS: f64 = 100.0;
const SPEND_NUMERIC_TOLERANCE: f64 = 1.0e-9;
const SPEND_SOUNDNESS_RECONSTRUCTION_GATE: &str = "spend_q18_soundness_liveness_epro_reconstructed";

const SPEND_Q18_TERM_PINS: [(&str, f64); 16] = [
    ("polynomial_batch_width_29", 107.316_020_114_355_38),
    ("four_fold_union", 108.985_432_265_750_69),
    ("final_q18_miss_times_3", 110.183_739_133_643_48),
    ("two_sample_ood_list_union", 213.100_018_394_892_15),
    ("relation_ood_mixers_24", 119.415_037_496_591_61),
    (
        "nonzero_gamma_and_three_point_batch_30",
        119.093_109_401_704_25,
    ),
    ("copy_inactive_nonzero_gamma_28", 119.192_645_075_255_17),
    ("atomic_tuple_compression", 112.396_837_317_778_39),
    ("atomic_copy_range_poles", 111.762_790_036_557_75),
    ("atomic_theta_collision", 119.415_037_496_591_61),
    ("zerocheck_equality_point", 120.678_071_902_425_4),
    ("zero_sum_h1_helper", 123.999_999_997_312_77),
    ("mask_original_nonzero_eta", 123.999_999_997_312_77),
    ("ten_degree_27_zerocheck_rounds", 115.923_184_400_261_93),
    ("poseidon2_assumption", 124.0),
    ("sha256_rom_assumption", 128.0),
];

const SPEND_Q18_FOLD_ROW_PINS: [f64; 4] = [
    109.529_942_692_338_42,
    111.226_281_804_531_75,
    112.858_135_080_222_61,
    113.840_648_013_834_85,
];

const ACCEPTANCE_PATH: &str = "results/spend/atomic_state_only_spend_acceptance.json";
const MUTATION_PATH: &str = "results/spend/atomic_state_only_spend_mutation.json";
const PRODUCTION_ACCEPTANCE_PATH: &str =
    "results/spend/atomic_state_only_spend_acceptance_production_mined.json";
const PRODUCTION_MUTATION_PATH: &str =
    "results/spend/atomic_state_only_spend_mutation_production_mined.json";
const SOUNDNESS_PATH: &str = "results/spend/spend_d_after_g_soundness_epro.json";
const COMPLETE_GOOD_PATH: &str = "results/spend/spend_complete_good_product.json";
const HVZK_PATH: &str = "results/spend/spend_computational_hvzk_closure.json";
const PROGRAM_MANIFEST_PATH: &str = "programs/aspis-verifier/Cargo.toml";
const WORKSPACE_MANIFEST_PATH: &str = "Cargo.toml";
const XTASK_MANIFEST_PATH: &str = "xtask/Cargo.toml";
const DEFAULT_SBF_PATH: &str = "target/deploy/aspis_verifier.so";
const SPEND_PRODUCTION_ALIAS_FEATURES: [&str; 2] =
    ["spend-minimal-dispatch", "spend-dynamic-rate512"];
const PRODUCTION_FORBIDDEN_FEATURES: [&str; 6] = [
    "diagnostic-unmined-spend-acceptance",
    "diagnostic-unmined-spend-mutation",
    "insecure-spend-fixture",
    "insecure-test-framing",
    "insecure-test-logup-compression",
    "insecure-test-ordering",
];

#[derive(Clone, Debug, Serialize)]
pub struct SourceArtifact {
    pub label: String,
    pub path: String,
    pub bytes: usize,
    pub sha256: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReleaseGate {
    pub name: &'static str,
    pub passed: bool,
    pub evidence: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReleaseScope {
    pub included: &'static str,
    pub proof_account_precondition: &'static str,
    pub excluded: [&'static str; 2],
}

#[derive(Clone, Debug, Serialize)]
pub struct ReleaseProofIdentity {
    pub sha256: Option<String>,
    pub bytes: Option<u64>,
    pub actual_path: Option<String>,
    pub acceptance_path: Option<String>,
    pub mutation_path: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReleaseGoodSpendBranch {
    pub selector: u8,
    pub accepted: bool,
    pub rejection: Option<String>,
    pub root_neutral_rank_m31: usize,
    pub remaining_gd_query_rank_m31: usize,
    pub remaining_gd_terminal_rank_m31: usize,
    pub h1_query_rank_m31: usize,
    pub h1_terminal_rank_m31: usize,
    pub dynamic_root_minor_fingerprint: String,
    pub dynamic_remaining_gd_minor_fingerprint: String,
    pub dynamic_h1_minor_fingerprint: String,
    pub dynamic_product_fingerprint: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReleaseInstance {
    pub proof_path: String,
    pub proof_bytes: u64,
    pub proof_sha256: String,
    pub statement_path: String,
    pub statement_bytes: u64,
    pub statement_sha256: String,
    pub statement_pool_hex: String,
    pub statement_sequence: u64,
    pub canonical_public_input_digest: String,
    pub selector_candidates: u8,
    pub serialized_selector: Option<u8>,
    pub least_good_selector: Option<u8>,
    pub good_spend_branches: Vec<ReleaseGoodSpendBranch>,
    pub good_spend_definition_fingerprint: String,
    pub production_host_verification_green: bool,
    pub evaluation_error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DefaultProductionSbfIdentity {
    pub path: &'static str,
    pub build_command: &'static str,
    pub freshly_built_by_release_command: bool,
    pub bytes: Option<u64>,
    pub sha256: Option<String>,
    pub mutation_recorded_bytes: Option<u64>,
    pub mutation_recorded_sha256: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SpendOneTransactionRelease {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub command: &'static str,
    pub status: &'static str,
    pub released: bool,
    pub scope: ReleaseScope,
    pub compute_unit_limit: u64,
    pub max_literal_production_tag65_cu: Option<u64>,
    pub exact_headroom_under_1_4m_cu: Option<i64>,
    /// The selected Spend union ledger after the factor-40 release
    /// sensitivity. This is the primary soundness number.
    pub selected_soundness_floor_bits: Option<f64>,
    /// A deliberately coarser sensitivity that applies the explicit
    /// work-normalized BCS R=32 endpoint bound and a whole-ledger factor of
    /// three.
    pub coarse_whole_soundness_floor_bits: Option<f64>,
    /// One real execution versus the common witness-independent simulator.
    pub computational_hiding_real_vs_simulator_bound_bits: Option<f64>,
    /// Two real witnesses after the explicit triangle factor. This is the
    /// publication number and the value gated at 100 bits.
    pub computational_hiding_pairwise_witness_bound_bits: Option<f64>,
    pub proof: ReleaseProofIdentity,
    pub release_instance: ReleaseInstance,
    pub default_production_sbf: DefaultProductionSbfIdentity,
    pub source_artifacts: Vec<SourceArtifact>,
    pub gates: Vec<ReleaseGate>,
    pub failed_gates: Vec<&'static str>,
    pub notes: [&'static str; 5],
}

#[derive(Clone)]
struct LoadedArtifacts {
    sources: Vec<SourceArtifact>,
    acceptance: Value,
    mutation: Value,
    soundness: Value,
    complete_good: Value,
    hvzk: Value,
    program_manifest: String,
    workspace_manifest: String,
    xtask_manifest: String,
    actual_proof_path: String,
    actual_proof_bytes: u64,
    actual_proof_sha256: String,
    release_instance: ReleaseInstance,
    default_sbf_bytes: u64,
    default_sbf_sha256: String,
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn load_one(
    workspace_root: &Path,
    label: &'static str,
    relative_path: &'static str,
) -> Result<(SourceArtifact, Value)> {
    let path = workspace_root.join(relative_path);
    let bytes = fs::read(&path).with_context(|| format!("read {}", path.display()))?;
    let value =
        serde_json::from_slice(&bytes).with_context(|| format!("parse {}", path.display()))?;
    Ok((
        SourceArtifact {
            label: label.to_string(),
            path: relative_path.to_string(),
            bytes: bytes.len(),
            sha256: hex_sha256(&bytes),
        },
        value,
    ))
}

fn load_raw_source(
    workspace_root: &Path,
    label: &'static str,
    relative_path: &'static str,
) -> Result<(SourceArtifact, Vec<u8>)> {
    let path = workspace_root.join(relative_path);
    let bytes = fs::read(&path).with_context(|| format!("read {}", path.display()))?;
    Ok((
        SourceArtifact {
            label: label.to_string(),
            path: relative_path.to_string(),
            bytes: bytes.len(),
            sha256: hex_sha256(&bytes),
        },
        bytes,
    ))
}

fn load_selected_proof(
    workspace_root: &Path,
    acceptance: &Value,
) -> Result<(SourceArtifact, String, Vec<u8>, String)> {
    let acceptance_path = str_at(acceptance, "/proof_path")
        .context("selected Spend acceptance artifact omitted proof_path")?;
    let relative = Path::new(acceptance_path);
    ensure!(
        !relative.is_absolute()
            && relative
                .components()
                .all(|component| { matches!(component, Component::Normal(_) | Component::CurDir) }),
        "selected Spend proof path must be a workspace-relative normal path: {acceptance_path}"
    );
    let workspace_root = workspace_root
        .canonicalize()
        .with_context(|| format!("canonicalize {}", workspace_root.display()))?;
    let path = workspace_root.join(relative);
    let canonical_path = path
        .canonicalize()
        .with_context(|| format!("canonicalize selected Spend proof {}", path.display()))?;
    ensure!(
        canonical_path.starts_with(&workspace_root),
        "selected Spend proof resolves outside the workspace: {}",
        canonical_path.display()
    );
    let bytes = fs::read(&canonical_path)
        .with_context(|| format!("read selected Spend proof {}", canonical_path.display()))?;
    let sha256 = hex_sha256(&bytes);
    Ok((
        SourceArtifact {
            label: "production_proof".to_string(),
            path: acceptance_path.to_string(),
            bytes: bytes.len(),
            sha256: sha256.clone(),
        },
        acceptance_path.to_string(),
        bytes,
        sha256,
    ))
}

fn load_selected_statement(
    workspace_root: &Path,
    acceptance: &Value,
) -> Result<(SourceArtifact, String, SpendStatementFile)> {
    let acceptance_path = str_at(acceptance, "/statement_path")
        .context("selected Spend acceptance artifact omitted statement_path")?;
    let relative = Path::new(acceptance_path);
    ensure!(
        !relative.is_absolute()
            && relative
                .components()
                .all(|component| matches!(component, Component::Normal(_))),
        "selected Spend statement path must be a workspace-relative normal path: {acceptance_path}"
    );
    let workspace_root = workspace_root
        .canonicalize()
        .with_context(|| format!("canonicalize {}", workspace_root.display()))?;
    let expected_path = workspace_root
        .join(relative)
        .canonicalize()
        .with_context(|| {
            format!(
                "canonicalize selected Spend statement {}",
                workspace_root.join(relative).display()
            )
        })?;
    ensure!(
        expected_path.starts_with(&workspace_root),
        "selected Spend statement resolves outside the workspace: {}",
        expected_path.display()
    );
    let statement_file = load_spend_statement_file(&workspace_root, relative)?;
    ensure!(
        statement_file.path == expected_path,
        "shared Spend statement loader resolved a different file"
    );
    let recorded_path = spend_recorded_path(&workspace_root, &statement_file.path);
    ensure!(
        recorded_path == acceptance_path,
        "selected Spend statement path is not canonical: recorded={recorded_path}, acceptance={acceptance_path}"
    );
    Ok((
        SourceArtifact {
            label: "production_statement".to_string(),
            path: recorded_path.clone(),
            bytes: statement_file.bytes,
            sha256: statement_file.sha256.clone(),
        },
        recorded_path,
        statement_file,
    ))
}

fn release_good_spend_branch(
    selector: usize,
    decision: &aspis_prover::state_only_good_spend::SpendGoodScheduleDecision,
) -> ReleaseGoodSpendBranch {
    ReleaseGoodSpendBranch {
        selector: selector as u8,
        accepted: decision.accepted,
        rejection: decision.rejection.map(|rejection| format!("{rejection:?}")),
        root_neutral_rank_m31: decision.root_neutral_rank_m31,
        remaining_gd_query_rank_m31: decision.remaining_gd_query_rank_m31,
        remaining_gd_terminal_rank_m31: decision.remaining_gd_terminal_rank_m31,
        h1_query_rank_m31: decision.h1_query_rank_m31,
        h1_terminal_rank_m31: decision.h1_terminal_rank_m31,
        dynamic_root_minor_fingerprint: format!(
            "0x{:016x}",
            decision.dynamic_root_minor_fingerprint
        ),
        dynamic_remaining_gd_minor_fingerprint: format!(
            "0x{:016x}",
            decision.dynamic_remaining_gd_minor_fingerprint
        ),
        dynamic_h1_minor_fingerprint: format!("0x{:016x}", decision.dynamic_h1_minor_fingerprint),
        dynamic_product_fingerprint: format!("0x{:016x}", decision.dynamic_product_fingerprint),
    }
}

fn build_release_instance(
    proof_path: String,
    proof_sha256: String,
    proof: &[u8],
    statement_path: String,
    statement_file: &SpendStatementFile,
) -> ReleaseInstance {
    let mut errors = Vec::new();
    let host_result = aspis_statement::state_only_spend::verify_atomic_state_only_spend_v4(
        proof,
        &statement_file.statement,
        aspis_prover::HOST_HASH,
        None,
    );
    let production_host_verification_green = host_result.is_ok();
    if let Err(error) = host_result {
        errors.push(format!("production host verification failed: {error:?}"));
    }

    let parsed_prefix =
        match aspis_core::state_only_prefix::StateOnlySpendPrefix::parse_from_proof(proof) {
            Ok((prefix, suffix)) if !suffix.is_empty() => Some(prefix),
            Ok(_) => {
                errors.push("Spend proof has no private-opening suffix".to_string());
                None
            }
            Err(error) => {
                errors.push(format!("Spend prefix parse failed: {error:?}"));
                None
            }
        };
    let serialized_selector = parsed_prefix.map(|prefix| prefix.query_selector);
    let mut least_good_selector = None;
    let mut good_spend_branches = Vec::new();

    if production_host_verification_green {
        if let Some(prefix) = parsed_prefix {
            match aspis_statement::atomic_payment_statement_digest_v4(
                &statement_file.statement,
                aspis_prover::HOST_HASH,
            ) {
                Ok(statement_digest) => {
                    match aspis_prover::state_only_good_spend::evaluate_spend_query_candidates_host(
                        aspis_prover::HOST_HASH,
                        &prefix,
                        &statement_digest,
                    ) {
                        Ok(evaluation) => {
                            least_good_selector = evaluation.selected_selector;
                            good_spend_branches = evaluation
                                .decisions
                                .iter()
                                .enumerate()
                                .map(|(selector, decision)| {
                                    release_good_spend_branch(selector, decision)
                                })
                                .collect();
                        }
                        Err(error) => {
                            errors.push(format!("complete-GoodSpend replay failed: {error:?}"));
                        }
                    }
                }
                Err(error) => errors.push(format!("statement digest failed: {error:?}")),
            }
        }
    } else {
        errors.push("complete-GoodSpend replay skipped after host rejection".to_string());
    }

    ReleaseInstance {
        proof_path,
        proof_bytes: proof.len() as u64,
        proof_sha256,
        statement_path,
        statement_bytes: statement_file.bytes as u64,
        statement_sha256: statement_file.sha256.clone(),
        statement_pool_hex: spend_hex(&statement_file.statement.pool),
        statement_sequence: statement_file.statement.sequence,
        canonical_public_input_digest: statement_file.canonical_public_input_digest.clone(),
        selector_candidates: aspis_core::state_only_prefix::STATE_ONLY_SPEND_QUERY_CANDIDATE_COUNT,
        serialized_selector,
        least_good_selector,
        good_spend_branches,
        good_spend_definition_fingerprint: expected_good_spend_fingerprint(),
        production_host_verification_green,
        evaluation_error: (!errors.is_empty()).then(|| errors.join("; ")),
    }
}

fn release_instance_selector_is_least_good(instance: &ReleaseInstance) -> bool {
    let candidate_count = usize::from(instance.selector_candidates);
    if candidate_count != 3
        || instance.good_spend_branches.len() != candidate_count
        || instance
            .good_spend_branches
            .iter()
            .enumerate()
            .any(|(selector, branch)| usize::from(branch.selector) != selector)
    {
        return false;
    }
    let recomputed_least_good = instance
        .good_spend_branches
        .iter()
        .find(|branch| branch.accepted)
        .map(|branch| branch.selector);
    instance.evaluation_error.is_none()
        && recomputed_least_good.is_some()
        && instance.least_good_selector == recomputed_least_good
        && instance.serialized_selector == recomputed_least_good
}

fn load_artifacts(workspace_root: &Path) -> Result<LoadedArtifacts> {
    let use_production_pair = workspace_root.join(PRODUCTION_ACCEPTANCE_PATH).is_file()
        && workspace_root.join(PRODUCTION_MUTATION_PATH).is_file();
    let acceptance_path = if use_production_pair {
        PRODUCTION_ACCEPTANCE_PATH
    } else {
        ACCEPTANCE_PATH
    };
    let mutation_path = if use_production_pair {
        PRODUCTION_MUTATION_PATH
    } else {
        MUTATION_PATH
    };
    let (acceptance_source, acceptance) = load_one(workspace_root, "acceptance", acceptance_path)?;
    let (mutation_source, mutation) = load_one(workspace_root, "mutation", mutation_path)?;
    let (soundness_source, soundness) = load_one(workspace_root, "soundness", SOUNDNESS_PATH)?;
    let (complete_good_source, complete_good) =
        load_one(workspace_root, "complete_good", COMPLETE_GOOD_PATH)?;
    let (hvzk_source, hvzk) = load_one(workspace_root, "computational_hvzk", HVZK_PATH)?;
    let (program_manifest_source, program_manifest) =
        load_raw_source(workspace_root, "program_manifest", PROGRAM_MANIFEST_PATH)?;
    let (workspace_manifest_source, workspace_manifest) = load_raw_source(
        workspace_root,
        "workspace_manifest",
        WORKSPACE_MANIFEST_PATH,
    )?;
    let (xtask_manifest_source, xtask_manifest) =
        load_raw_source(workspace_root, "xtask_manifest", XTASK_MANIFEST_PATH)?;
    let (proof_source, actual_proof_path, proof_bytes, actual_proof_sha256) =
        load_selected_proof(workspace_root, &acceptance)?;
    let actual_proof_bytes = proof_bytes.len() as u64;
    let (statement_source, actual_statement_path, statement_file) =
        load_selected_statement(workspace_root, &acceptance)?;
    let release_instance = build_release_instance(
        actual_proof_path.clone(),
        actual_proof_sha256.clone(),
        &proof_bytes,
        actual_statement_path,
        &statement_file,
    );
    let (default_sbf_source, default_sbf) =
        load_raw_source(workspace_root, "default_production_sbf", DEFAULT_SBF_PATH)?;
    Ok(LoadedArtifacts {
        sources: vec![
            acceptance_source,
            mutation_source,
            soundness_source,
            complete_good_source,
            hvzk_source,
            program_manifest_source,
            workspace_manifest_source,
            xtask_manifest_source,
            proof_source,
            statement_source,
            default_sbf_source.clone(),
        ],
        acceptance,
        mutation,
        soundness,
        complete_good,
        hvzk,
        program_manifest: String::from_utf8(program_manifest)
            .context("program manifest is not UTF-8")?,
        workspace_manifest: String::from_utf8(workspace_manifest)
            .context("workspace manifest is not UTF-8")?,
        xtask_manifest: String::from_utf8(xtask_manifest).context("xtask manifest is not UTF-8")?,
        actual_proof_path,
        actual_proof_bytes,
        actual_proof_sha256,
        release_instance,
        default_sbf_bytes: default_sbf.len() as u64,
        default_sbf_sha256: default_sbf_source.sha256,
    })
}

fn bool_at(value: &Value, pointer: &str) -> Option<bool> {
    value.pointer(pointer).and_then(Value::as_bool)
}

fn u64_at(value: &Value, pointer: &str) -> Option<u64> {
    value.pointer(pointer).and_then(Value::as_u64)
}

fn i64_at(value: &Value, pointer: &str) -> Option<i64> {
    value.pointer(pointer).and_then(Value::as_i64)
}

fn f64_at(value: &Value, pointer: &str) -> Option<f64> {
    value.pointer(pointer).and_then(Value::as_f64)
}

fn str_at<'a>(value: &'a Value, pointer: &str) -> Option<&'a str> {
    value.pointer(pointer).and_then(Value::as_str)
}

fn u64_array_at(value: &Value, pointer: &str) -> Option<Vec<u64>> {
    value
        .pointer(pointer)?
        .as_array()?
        .iter()
        .map(Value::as_u64)
        .collect()
}

fn valid_sha256(value: Option<&str>) -> bool {
    value.is_some_and(|value| {
        value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
    })
}

fn valid_lower_hex_32(value: Option<&str>) -> bool {
    value.is_some_and(|value| {
        value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    })
}

fn add_gate(
    gates: &mut Vec<ReleaseGate>,
    name: &'static str,
    passed: bool,
    evidence: impl Into<String>,
) {
    gates.push(ReleaseGate {
        name,
        passed,
        evidence: evidence.into(),
    });
}

fn all_true(value: &Value, pointers: &[&str]) -> bool {
    pointers
        .iter()
        .all(|pointer| bool_at(value, pointer) == Some(true))
}

fn checked_sum_at(value: &Value, pointers: &[&str]) -> Option<u64> {
    pointers.iter().try_fold(0u64, |sum, pointer| {
        sum.checked_add(u64_at(value, pointer)?)
    })
}

fn manifest_section<'a>(manifest: &'a str, name: &str) -> Option<&'a str> {
    let header = format!("[{name}]");
    let start = manifest
        .lines()
        .scan(0usize, |offset, line| {
            let line_start = *offset;
            *offset += line.len() + 1;
            Some((line_start, line))
        })
        .find_map(|(offset, line)| (line.trim() == header).then_some(offset + line.len() + 1))?;
    let tail = &manifest[start..];
    let end = tail
        .lines()
        .scan(0usize, |offset, line| {
            let line_start = *offset;
            *offset += line.len() + 1;
            Some((line_start, line))
        })
        .find_map(|(offset, line)| line.trim().starts_with('[').then_some(offset))
        .unwrap_or(tail.len());
    Some(&tail[..end])
}

fn manifest_assignment(section: &str, key: &str) -> Option<String> {
    let mut lines = section.lines();
    while let Some(line) = lines.next() {
        let uncommented = line.split('#').next().unwrap_or_default().trim();
        let Some((candidate, value)) = uncommented.split_once('=') else {
            continue;
        };
        if candidate.trim() != key {
            continue;
        }
        let mut value = value.trim().to_string();
        let mut square_balance =
            value.matches('[').count() as isize - value.matches(']').count() as isize;
        let mut brace_balance =
            value.matches('{').count() as isize - value.matches('}').count() as isize;
        while square_balance > 0 || brace_balance > 0 {
            let next = lines.next()?.split('#').next()?.trim();
            value.push(' ');
            value.push_str(next);
            square_balance +=
                next.matches('[').count() as isize - next.matches(']').count() as isize;
            brace_balance +=
                next.matches('{').count() as isize - next.matches('}').count() as isize;
        }
        return Some(value);
    }
    None
}

fn manifest_string_array(value: &str) -> Option<Vec<String>> {
    let value = value.trim();
    if !value.starts_with('[') || !value.ends_with(']') {
        return None;
    }
    let mut values = Vec::new();
    let mut parts = value.split('"');
    parts.next()?;
    loop {
        let Some(item) = parts.next() else {
            break;
        };
        values.push(item.to_string());
        if parts.next().is_none() {
            break;
        }
    }
    Some(values)
}

fn spend_program_defaults_match(
    manifest: &str,
) -> (Option<Vec<String>>, Option<Vec<String>>, bool) {
    let default_features = manifest_section(manifest, "features")
        .and_then(|section| manifest_assignment(section, "default"))
        .and_then(|value| manifest_string_array(&value));
    let production_alias = manifest_section(manifest, "features")
        .and_then(|section| manifest_assignment(section, "spend-production"))
        .and_then(|value| manifest_string_array(&value));
    let matches = default_features
        .as_deref()
        .is_some_and(|features| features == ["spend-production".to_string()])
        && production_alias.as_deref().is_some_and(|features| {
            features
                .iter()
                .map(String::as_str)
                .eq(SPEND_PRODUCTION_ALIAS_FEATURES)
        });
    (default_features, production_alias, matches)
}

fn manifest_dependency_disables_defaults(manifest: &str, section: &str, key: &str) -> bool {
    manifest_section(manifest, section)
        .and_then(|section| manifest_assignment(section, key))
        .is_some_and(|value| {
            let compact = value
                .chars()
                .filter(|character| !character.is_ascii_whitespace())
                .collect::<String>();
            value.trim().starts_with('{')
                && value.trim().ends_with('}')
                && compact.contains("default-features=false")
        })
}

fn expected_good_spend_fingerprint() -> String {
    let digest = aspis_prover::state_only_good_spend::spend_good_schedule_definition_fingerprint(
        aspis_prover::HOST_HASH,
    );
    format!("0x{}", hex_sha256_bytes(&digest))
}

fn hex_sha256_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn expected_layout_fingerprint() -> String {
    format!(
        "0x{:016x}",
        aspis_core::state_only_hiding::state_only_spend_hiding_layout_factor_fingerprint_v3()
    )
}

fn require_u64(value: &Value, pointer: &str, expected: u64) -> Result<()> {
    let actual = u64_at(value, pointer);
    ensure!(
        actual == Some(expected),
        "{pointer}: expected {expected}, got {actual:?}"
    );
    Ok(())
}

fn require_bool(value: &Value, pointer: &str, expected: bool) -> Result<()> {
    let actual = bool_at(value, pointer);
    ensure!(
        actual == Some(expected),
        "{pointer}: expected {expected}, got {actual:?}"
    );
    Ok(())
}

fn require_str(value: &Value, pointer: &str, expected: &str) -> Result<()> {
    let actual = str_at(value, pointer);
    ensure!(
        actual == Some(expected),
        "{pointer}: expected {expected:?}, got {actual:?}"
    );
    Ok(())
}

fn require_close(actual: f64, expected: f64, label: &str) -> Result<()> {
    ensure!(actual.is_finite(), "{label}: non-finite value {actual}");
    ensure!(
        (actual - expected).abs() < SPEND_NUMERIC_TOLERANCE,
        "{label}: expected {expected:.15}, got {actual:.15}"
    );
    Ok(())
}

fn require_f64(value: &Value, pointer: &str, expected: f64) -> Result<()> {
    let actual = f64_at(value, pointer).with_context(|| format!("{pointer}: missing f64"))?;
    require_close(actual, expected, pointer)
}

fn probability_union_bits(bits: impl IntoIterator<Item = f64>) -> f64 {
    -bits
        .into_iter()
        .map(|bits| 2.0_f64.powf(-bits))
        .sum::<f64>()
        .log2()
}

fn bcs_work_normalized_bits(round_bits: f64, boundaries: f64, queries: f64) -> f64 {
    let epsilon_round = 2.0_f64.powf(-round_bits);
    let epsilon = (1.0 + boundaries / queries) * epsilon_round
        + 3.0 * (queries + queries.recip()) * 2.0_f64.powi(-256);
    -epsilon.log2()
}

fn reconstruct_spend_q18_ledger(
    soundness: &Value,
    complete_good: &Value,
    hvzk: &Value,
) -> Result<String> {
    use aspis_prover::state_only_good_spend::{
        spend_selector_scope_definition_fingerprint, verify_spend_selector_scope_lemma,
        SPEND_GOOD_SCHEDULE_COMPLETE_Z_DEGREE, SPEND_GOOD_SCHEDULE_CONTINUOUS_DEGREE,
        SPEND_GOOD_SCHEDULE_DOMAIN_LOG, SPEND_GOOD_SCHEDULE_GAMMA_DEGREE,
        SPEND_GOOD_SCHEDULE_GD_ANCHOR_FINGERPRINT, SPEND_GOOD_SCHEDULE_H1_ANCHOR_FINGERPRINT,
        SPEND_GOOD_SCHEDULE_INVERSE_RATE, SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS,
        SPEND_GOOD_SCHEDULE_PRODUCT_ANCHOR_FINGERPRINT, SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES,
        SPEND_GOOD_SCHEDULE_QUERY_COUNT, SPEND_GOOD_SCHEDULE_QUERY_FIBERS,
        SPEND_GOOD_SCHEDULE_Q_DEGREE, SPEND_GOOD_SCHEDULE_RAW_QUERY_RANK_M31,
        SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31, SPEND_GOOD_SCHEDULE_ROOT_ANCHOR_FINGERPRINT,
        SPEND_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31, SPEND_GOOD_SCHEDULE_ROOT_Z_DEGREE,
        SPEND_SELECTOR_SCOPE_PROPOSITIONAL_CASES,
    };

    let query_count = SPEND_GOOD_SCHEDULE_QUERY_COUNT as u64;
    let selectors = SPEND_GOOD_SCHEDULE_QUERY_CANDIDATES as u64;
    let attempt_cap = SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS as u64;
    ensure!(query_count == 18, "live GoodSpend query count is not q18");
    ensure!(selectors == 3, "live GoodSpend selector count is not three");
    ensure!(attempt_cap == 17, "live GoodSpend attempt cap is not 17");
    let selector_scope_cases = verify_spend_selector_scope_lemma();
    ensure!(
        selector_scope_cases == SPEND_SELECTOR_SCOPE_PROPOSITIONAL_CASES,
        "live selector-scope propositional proof did not cover 48 cases"
    );
    require_bool(soundness, "/selector_scope_proof/lemma_proved", true)?;
    require_bool(
        soundness,
        "/selector_scope_proof/release_authorizing",
        false,
    )?;
    require_bool(
        soundness,
        "/selector_scope_proof/only_final_query_miss_receives_factor_three",
        true,
    )?;
    require_u64(
        soundness,
        "/selector_scope_proof/propositional_cases_checked",
        selector_scope_cases as u64,
    )?;
    require_str(
        soundness,
        "/selector_scope_proof/scope",
        "arbitrary selector correlated with all three q18 schedules",
    )?;
    let selector_scope_fingerprint = hex_sha256_bytes(
        &spend_selector_scope_definition_fingerprint(aspis_prover::HOST_HASH),
    );
    require_str(
        soundness,
        "/selector_scope_proof/definition_fingerprint",
        &selector_scope_fingerprint,
    )?;
    require_u64(soundness, "/candidate/query_count", query_count)?;
    require_u64(
        soundness,
        "/candidate/inverse_rate",
        SPEND_GOOD_SCHEDULE_INVERSE_RATE as u64,
    )?;
    require_u64(soundness, "/candidate/query_candidates", selectors)?;
    require_u64(soundness, "/candidate/attempt_cap", attempt_cap)?;
    require_u64(
        soundness,
        "/host_first_good_release_integration/attempt_cap",
        attempt_cap,
    )?;

    let terms = soundness
        .pointer("/soundness/terms_bits")
        .and_then(Value::as_array)
        .context("/soundness/terms_bits: missing array")?;
    ensure!(
        terms.len() == SPEND_Q18_TERM_PINS.len(),
        "/soundness/terms_bits: expected exactly 16 terms, got {}",
        terms.len()
    );
    let mut term_bits = Vec::with_capacity(terms.len());
    for (index, (term, (expected_name, expected_bits))) in
        terms.iter().zip(SPEND_Q18_TERM_PINS).enumerate()
    {
        let name = str_at(term, "/name");
        ensure!(
            name == Some(expected_name),
            "/soundness/terms_bits/{index}/name: expected {expected_name:?}, got {name:?}"
        );
        let bits = f64_at(term, "/bits")
            .with_context(|| format!("/soundness/terms_bits/{index}/bits: missing f64"))?;
        require_close(
            bits,
            expected_bits,
            &format!("/soundness/terms_bits/{index}/bits"),
        )?;
        require_str(
            term,
            "/selector_scope",
            if index == 2 {
                "selector_dependent_final_query"
            } else {
                "common_preselector"
            },
        )?;
        term_bits.push(bits);
    }

    let fold_rows = terms[1]
        .pointer("/rows")
        .and_then(Value::as_array)
        .context("/soundness/terms_bits/1/rows: missing array")?;
    ensure!(
        fold_rows.len() == SPEND_Q18_FOLD_ROW_PINS.len(),
        "/soundness/terms_bits/1/rows: expected four rows"
    );
    let mut parsed_fold_rows = Vec::with_capacity(fold_rows.len());
    for (index, (row, expected)) in fold_rows.iter().zip(SPEND_Q18_FOLD_ROW_PINS).enumerate() {
        let actual = row
            .as_f64()
            .with_context(|| format!("/soundness/terms_bits/1/rows/{index}: missing f64"))?;
        require_close(
            actual,
            expected,
            &format!("/soundness/terms_bits/1/rows/{index}"),
        )?;
        parsed_fold_rows.push(actual);
    }
    require_close(
        probability_union_bits(parsed_fold_rows),
        term_bits[1],
        "four-fold row union",
    )?;

    let raw_final_bits =
        f64_at(&terms[2], "/raw_bits").context("/soundness/terms_bits/2/raw_bits: missing f64")?;
    require_close(
        raw_final_bits,
        111.768_701_634_364_65,
        "/soundness/terms_bits/2/raw_bits",
    )?;
    require_close(
        raw_final_bits - (selectors as f64).log2(),
        term_bits[2],
        "selected q18 term",
    )?;

    let event_union_bits = probability_union_bits(term_bits.iter().copied());
    require_close(
        event_union_bits,
        106.702_033_487_302_9,
        "reconstructed selected event union",
    )?;
    require_f64(soundness, "/soundness/event_union_bits", event_union_bits)?;

    let factor40_bits = event_union_bits - 40.0_f64.log2();
    require_close(
        factor40_bits,
        101.380_105_392_415_53,
        "reconstructed factor-40 floor",
    )?;
    require_f64(soundness, "/soundness/after_factor40_bits", factor40_bits)?;
    require_f64(soundness, "/soundness/selected_floor_bits", factor40_bits)?;

    let coarse_event_union_bits =
        probability_union_bits(term_bits.iter().enumerate().map(|(index, bits)| {
            if index == 2 {
                raw_final_bits
            } else {
                *bits
            }
        }));
    require_close(
        coarse_event_union_bits,
        106.790_806_002_954_17,
        "reconstructed unselected event union",
    )?;
    require_f64(
        soundness,
        "/soundness/coarse_unselected_event_union_bits",
        coarse_event_union_bits,
    )?;

    let bcs = soundness
        .pointer("/soundness/bcs_work_normalized")
        .context("/soundness/bcs_work_normalized: missing object")?;
    require_str(
        bcs,
        "/metric",
        "success probability per random-oracle query",
    )?;
    require_u64(bcs, "/message_boundaries_r", 32)?;
    require_u64(bcs, "/lambda", 256)?;
    require_u64(bcs, "/query_budget_min", 1)?;
    require_str(bcs, "/query_budget_max", "2^128")?;
    require_str(
        bcs,
        "/formula",
        "epsilon_BCS(T)/T <= (1+R/T)*epsilon_round + 3*(T+1/T)/2^lambda",
    )?;
    let t_min = 1.0_f64;
    let t_max = 2.0_f64.powi(128);
    let selected_t1_bits = bcs_work_normalized_bits(event_union_bits, 32.0, t_min);
    let selected_t2p128_bits = bcs_work_normalized_bits(event_union_bits, 32.0, t_max);
    let selected_bcs_worst_bits = selected_t1_bits.min(selected_t2p128_bits);
    let coarse_t1_bits = bcs_work_normalized_bits(coarse_event_union_bits, 32.0, t_min);
    let coarse_t2p128_bits = bcs_work_normalized_bits(coarse_event_union_bits, 32.0, t_max);
    let coarse_bcs_worst_bits = coarse_t1_bits.min(coarse_t2p128_bits);
    for (pointer, actual, expected) in [
        (
            "/selected_t1_bits",
            selected_t1_bits,
            101.657_639_367_944_44,
        ),
        (
            "/selected_t2p128_bits",
            selected_t2p128_bits,
            106.702_031_808_619_58,
        ),
        (
            "/selected_worst_endpoint_bits",
            selected_bcs_worst_bits,
            101.657_639_367_944_44,
        ),
        ("/coarse_t1_bits", coarse_t1_bits, 101.746_411_883_595_71),
        (
            "/coarse_t2p128_bits",
            coarse_t2p128_bits,
            106.790_804_217_733_32,
        ),
        (
            "/coarse_worst_endpoint_bits",
            coarse_bcs_worst_bits,
            101.746_411_883_595_71,
        ),
    ] {
        require_close(actual, expected, &format!("reconstructed BCS {pointer}"))?;
        require_f64(bcs, pointer, actual)?;
    }
    let coarse_whole_bits = coarse_bcs_worst_bits - (selectors as f64).log2();
    require_close(
        coarse_whole_bits,
        100.161_449_382_874_55,
        "reconstructed coarse BCS-times-three floor",
    )?;
    require_f64(
        soundness,
        "/soundness/coarse_whole_ledger_times_three_bits",
        coarse_whole_bits,
    )?;

    require_u64(
        soundness,
        "/query_domain_guard/implemented_log_domain",
        SPEND_GOOD_SCHEDULE_DOMAIN_LOG as u64,
    )?;
    require_u64(
        soundness,
        "/query_domain_guard/fibers_exhaustively_checked",
        SPEND_GOOD_SCHEDULE_QUERY_FIBERS as u64,
    )?;
    require_str(
        soundness,
        "/query_domain_guard/fiber_to_root_map",
        "t=2*x^2-1",
    )?;
    require_u64(
        soundness,
        "/query_domain_guard/distinct_roots",
        SPEND_GOOD_SCHEDULE_QUERY_FIBERS as u64,
    )?;
    require_bool(soundness, "/query_domain_guard/injective", true)?;
    require_u64(soundness, "/query_domain_guard/root_one_count", 0)?;

    let q_degree = SPEND_GOOD_SCHEDULE_Q_DEGREE as u64;
    let root_z_degree = SPEND_GOOD_SCHEDULE_ROOT_Z_DEGREE as u64;
    let complete_z_degree = SPEND_GOOD_SCHEDULE_COMPLETE_Z_DEGREE as u64;
    let gamma_degree = SPEND_GOOD_SCHEDULE_GAMMA_DEGREE as u64;
    let continuous_degree = SPEND_GOOD_SCHEDULE_CONTINUOUS_DEGREE as u64;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/joint_rank_m31",
        SPEND_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31 as u64,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/joint_target_rank_m31",
        SPEND_GOOD_SCHEDULE_ROOT_NEUTRAL_RANK_M31 as u64,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/q_individual_degree_bound",
        q_degree / query_count,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/q_total_degree_bound",
        q_degree,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/root_neutral_minor_z_degree_bound",
        root_z_degree,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/complete_good_remaining_gd_terminal_z_degree_addition",
        120,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/complete_good_h1_padding_z_degree_addition",
        120,
    )?;
    ensure!(
        complete_z_degree == root_z_degree + 120 + 120,
        "live complete-Good z degree does not reconstruct"
    );
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/complete_good_z_degree_bound",
        complete_z_degree,
    )?;
    require_u64(
        soundness,
        "/root_neutral_polynomial_minor/gamma_coordinate_total_degree_bound",
        gamma_degree,
    )?;
    ensure!(
        continuous_degree == complete_z_degree + gamma_degree,
        "live continuous degree does not reconstruct"
    );

    let fingerprint = |value: u64| format!("0x{value:016x}");
    let root_fingerprint = fingerprint(SPEND_GOOD_SCHEDULE_ROOT_ANCHOR_FINGERPRINT);
    let gd_fingerprint = fingerprint(SPEND_GOOD_SCHEDULE_GD_ANCHOR_FINGERPRINT);
    let h1_fingerprint = fingerprint(SPEND_GOOD_SCHEDULE_H1_ANCHOR_FINGERPRINT);
    let product_fingerprint = fingerprint(SPEND_GOOD_SCHEDULE_PRODUCT_ANCHOR_FINGERPRINT);
    require_str(
        soundness,
        "/root_neutral_polynomial_minor/minor_fingerprint",
        &root_fingerprint,
    )?;
    require_bool(soundness, "/root_neutral_polynomial_minor/complete", true)?;
    require_u64(
        soundness,
        "/complete_good_product/remaining_gd_query_rank_m31",
        SPEND_GOOD_SCHEDULE_RAW_QUERY_RANK_M31 as u64,
    )?;
    require_u64(
        soundness,
        "/complete_good_product/remaining_gd_terminal_schur_rank_m31",
        SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31 as u64,
    )?;
    require_str(
        soundness,
        "/complete_good_product/remaining_gd_terminal_schur_fingerprint",
        &gd_fingerprint,
    )?;
    require_u64(
        soundness,
        "/complete_good_product/h1_query_rank_m31",
        SPEND_GOOD_SCHEDULE_RAW_QUERY_RANK_M31 as u64,
    )?;
    require_u64(
        soundness,
        "/complete_good_product/h1_terminal_schur_rank_m31",
        SPEND_GOOD_SCHEDULE_RAW_TERMINAL_RANK_M31 as u64,
    )?;
    require_str(
        soundness,
        "/complete_good_product/h1_terminal_schur_fingerprint",
        &h1_fingerprint,
    )?;
    require_str(
        soundness,
        "/complete_good_product/product_fingerprint",
        &product_fingerprint,
    )?;
    require_u64(
        soundness,
        "/complete_good_product/continuous_degree_bound",
        continuous_degree,
    )?;
    require_bool(soundness, "/complete_good_product/complete", true)?;

    for (pointer, expected) in [
        ("/root_neutral_minor/fingerprint", root_fingerprint.as_str()),
        (
            "/remaining_gd_terminal_schur/fingerprint",
            gd_fingerprint.as_str(),
        ),
        (
            "/h1_inactive_padding_terminal_schur/fingerprint",
            h1_fingerprint.as_str(),
        ),
        ("/bound_product/fingerprint", product_fingerprint.as_str()),
    ] {
        require_str(complete_good, pointer, expected)?;
    }
    for (pointer, expected) in [
        ("/bound_product/q_total_degree_bound", q_degree),
        ("/bound_product/root_neutral_z_degree_bound", root_z_degree),
        (
            "/bound_product/complete_good_z_degree_bound",
            complete_z_degree,
        ),
        (
            "/bound_product/gamma_coordinate_total_degree_bound",
            gamma_degree,
        ),
        (
            "/bound_product/continuous_total_degree_bound",
            continuous_degree,
        ),
    ] {
        require_u64(complete_good, pointer, expected)?;
    }
    require_bool(complete_good, "/bound_product/complete", true)?;

    let query_denominator = SPEND_GOOD_SCHEDULE_QUERY_FIBERS as u64 - (query_count - 1);
    let rho_query = q_degree as f64 / query_denominator as f64;
    let m31_modulus = aspis_core::field::P as f64;
    let beta_attempt = continuous_degree as f64 / m31_modulus + rho_query.powi(selectors as i32);
    let bits_per_attempt = -beta_attempt.log2();
    let rank_exhaustion_bits = attempt_cap as f64 * bits_per_attempt;
    let build_abort = 128.0 / m31_modulus.powi(6);
    let public_abort_probability =
        attempt_cap as f64 * build_abort + beta_attempt.powi(attempt_cap as i32);
    let public_abort_bits = -public_abort_probability.log2();
    for (pointer, expected) in [
        ("/liveness/query_degree", q_degree as f64),
        (
            "/liveness/query_sampling_denominator",
            query_denominator as f64,
        ),
        ("/liveness/rho_query", rho_query),
        ("/liveness/continuous_degree", continuous_degree as f64),
        ("/liveness/selectors", selectors as f64),
        ("/liveness/beta_per_attempt", beta_attempt),
        ("/liveness/bits_per_attempt", bits_per_attempt),
        ("/liveness/rank_exhaustion_cap17_bits", rank_exhaustion_bits),
        ("/liveness/public_abort_bits", public_abort_bits),
    ] {
        require_f64(soundness, pointer, expected)?;
    }
    require_close(rho_query, 0.238_983_632_825_912_78, "live rho_query")?;
    require_close(
        beta_attempt,
        0.013_705_910_239_932_412,
        "live beta_per_attempt",
    )?;
    require_close(
        bits_per_attempt,
        6.189_058_045_848_226,
        "live bits_per_attempt",
    )?;
    require_close(
        rank_exhaustion_bits,
        105.213_986_779_419_84,
        "live cap-17 exhaustion bits",
    )?;
    require_close(
        public_abort_bits,
        105.213_986_779_419_83,
        "live public abort bits",
    )?;
    require_str(
        soundness,
        "/liveness/build_abort_per_attempt",
        "128/(2^31-1)^6",
    )?;
    require_str(
        soundness,
        "/liveness/public_abort_formula",
        &format!("{attempt_cap}*epsilon_build + beta_per_attempt^{attempt_cap}"),
    )?;
    require_u64(hvzk, "/q3_cap17_release/attempt_cap", attempt_cap)?;
    require_f64(
        hvzk,
        "/q3_cap17_release/rank_exhaustion_abort_bits",
        rank_exhaustion_bits,
    )?;

    let draw_limit =
        u64::try_from(aspis_core::circle_hiding_prefix::PAYMENT_HIDING_QUERY_DRAW_LIMIT)
            .context("Spend query draw limit does not fit u64")?;
    let max_unique_on_failure = query_count - 1;
    let duplicate_draws = draw_limit - max_unique_on_failure;
    ensure!(
        (draw_limit, max_unique_on_failure, duplicate_draws) == (64, 17, 47),
        "live q18 sampler inventory drifted"
    );
    let log2_binomial = (1..=duplicate_draws)
        .map(|i| ((draw_limit - duplicate_draws + i) as f64 / i as f64).log2())
        .sum::<f64>();
    let sampler_one_bits = -(log2_binomial
        + duplicate_draws as f64
            * (max_unique_on_failure as f64 / SPEND_GOOD_SCHEDULE_QUERY_FIBERS as f64).log2());
    let sampler_union_bits = sampler_one_bits - (attempt_cap as f64 * selectors as f64).log2();
    require_close(
        sampler_union_bits,
        550.923_890_017_650_6,
        "live q18 sampler cap-17 selector union",
    )?;
    require_f64(
        soundness,
        "/liveness/q18_sampler_cap17_m3_union_bits",
        sampler_union_bits,
    )?;

    let leaves = 305_152u64;
    let field_expander_inputs = 53_892u64;
    let programmed_squeeze_inputs = 292u64;
    let programmed_advance_inputs = 292u64;
    let literal_absorb_inputs = 47u64;
    let work_predicate_inputs =
        aspis_core::state_only_prefix::STATE_ONLY_SPEND_FOLD_GRINDING_BITS.len() as u64 + 2;
    let transcript_inputs = literal_absorb_inputs
        + programmed_squeeze_inputs
        + programmed_advance_inputs
        + work_predicate_inputs;
    let total_c = 3 * leaves + field_expander_inputs + 8 + transcript_inputs;
    let qh_log2 = 128u64;
    for (pointer, expected) in [
        ("/epro/attempts", attempt_cap),
        ("/epro/qh_log2", qh_log2),
        ("/epro/tree_leaves", leaves),
        ("/epro/field_expander_inputs", field_expander_inputs),
        ("/epro/programmed_squeeze_inputs", programmed_squeeze_inputs),
        ("/epro/programmed_advance_inputs", programmed_advance_inputs),
        ("/epro/literal_absorb_inputs", literal_absorb_inputs),
        ("/epro/work_predicate_inputs", work_predicate_inputs),
        ("/epro/transcript_inputs", transcript_inputs),
        ("/epro/total_c", total_c),
    ] {
        require_u64(soundness, pointer, expected)?;
    }
    ensure!(
        (transcript_inputs, total_c) == (637, 969_993),
        "live EPRO inventory reconstruction drifted"
    );
    let programmed_inputs = attempt_cap as f64 * total_c as f64;
    let leading_epro_bits = 256.0 - qh_log2 as f64 - programmed_inputs.log2();
    let pairwise_epro_bits = leading_epro_bits - 1.0;
    let collision_bits = 256.0 - (programmed_inputs * (programmed_inputs - 1.0) / 2.0).log2();
    let max_work_bits = aspis_core::state_only_prefix::STATE_ONLY_SPEND_FOLD_GRINDING_BITS
        .into_iter()
        .chain([
            aspis_core::state_only_prefix::STATE_ONLY_SPEND_BATCH_GRINDING_BITS,
            aspis_core::state_only_prefix::STATE_ONLY_SPEND_GRINDING_BITS,
        ])
        .max()
        .context("empty Spend work schedule")?;
    let expected_hits_exponent = 64 - i32::from(max_work_bits);
    let work_exhaustion_bits = 2.0_f64.powi(expected_hits_exponent) / std::f64::consts::LN_2
        - (work_predicate_inputs as f64 * attempt_cap as f64).log2();
    for (pointer, expected) in [
        ("/epro/leading_no_prequery_bits", leading_epro_bits),
        ("/epro/pairwise_witness_bits", pairwise_epro_bits),
        (
            "/epro/programming_collision_bits_lower_bound",
            collision_bits,
        ),
        (
            "/epro/six_work_nonce_exhaustion_bits_lower_bound",
            work_exhaustion_bits,
        ),
        (
            "/computational_hvzk/real_vs_simulator_bound_bits",
            leading_epro_bits,
        ),
        (
            "/computational_hvzk/pairwise_witness_bound_bits",
            pairwise_epro_bits,
        ),
    ] {
        require_f64(soundness, pointer, expected)?;
    }
    require_close(
        leading_epro_bits,
        104.024_922_348_251_98,
        "live EPRO real-vs-simulator bound",
    )?;
    require_close(
        pairwise_epro_bits,
        103.024_922_348_251_98,
        "live EPRO pairwise bound",
    )?;
    require_close(
        collision_bits,
        209.049_844_783_993_68,
        "live EPRO programming-collision bound",
    )?;
    require_close(
        work_exhaustion_bits,
        193_635_243.912_558_44,
        "live EPRO work-exhaustion bound",
    )?;
    for (pointer, expected) in [
        ("/epro/attempts", attempt_cap),
        ("/epro/qh_log2", qh_log2),
        ("/epro/tree_leaves", leaves),
        (
            "/epro/field_expander_inputs_including_d",
            field_expander_inputs,
        ),
        ("/epro/distinct_transcript_inputs", transcript_inputs),
        ("/epro/total_c", total_c),
    ] {
        require_u64(hvzk, pointer, expected)?;
    }
    for (pointer, expected) in [
        ("/epro/leading_no_prequery_bits", leading_epro_bits),
        (
            "/epro/programming_collision_bits_lower_bound",
            collision_bits,
        ),
        (
            "/epro/six_work_nonce_exhaustion_bits_lower_bound",
            work_exhaustion_bits,
        ),
        (
            "/epro/complete_view_real_vs_simulator_bound_bits",
            leading_epro_bits,
        ),
        (
            "/epro/complete_view_pairwise_witness_bound_bits",
            pairwise_epro_bits,
        ),
    ] {
        require_f64(hvzk, pointer, expected)?;
    }

    ensure!(
        coarse_whole_bits >= MIN_SECURITY_BITS
            && rank_exhaustion_bits >= MIN_SECURITY_BITS
            && public_abort_bits >= MIN_SECURITY_BITS
            && pairwise_epro_bits >= MIN_SECURITY_BITS,
        "reconstructed q18 conservative whole-ledger floor is below 100 bits"
    );
    Ok(format!(
        "terms=16, selected_factor40={factor40_bits:.15}, selected_bcs_worst={selected_bcs_worst_bits:.15}, conservative_coarse_bcs_times3={coarse_whole_bits:.15}, selector_scope_diagnostic_cases={selector_scope_cases}, cap={attempt_cap}, public_abort={public_abort_bits:.15}, epro_pairwise={pairwise_epro_bits:.15}"
    ))
}

fn evaluate_loaded(loaded: LoadedArtifacts) -> SpendOneTransactionRelease {
    let acceptance = &loaded.acceptance;
    let mutation = &loaded.mutation;
    let soundness = &loaded.soundness;
    let complete_good = &loaded.complete_good;
    let hvzk = &loaded.hvzk;
    let release_instance = &loaded.release_instance;
    let mut gates = Vec::new();

    let production_artifact_pair =
        loaded.sources.iter().any(|source| {
            source.label == "acceptance" && source.path == PRODUCTION_ACCEPTANCE_PATH
        }) && loaded
            .sources
            .iter()
            .any(|source| source.label == "mutation" && source.path == PRODUCTION_MUTATION_PATH);
    add_gate(
        &mut gates,
        "production_mined_artifact_pair_selected",
        production_artifact_pair,
        format!(
            "acceptance_path={:?}, mutation_path={:?}",
            loaded
                .sources
                .iter()
                .find(|source| source.label == "acceptance")
                .map(|source| source.path.as_str()),
            loaded
                .sources
                .iter()
                .find(|source| source.label == "mutation")
                .map(|source| source.path.as_str())
        ),
    );

    let acceptance_sha = str_at(acceptance, "/proof_sha256");
    let mutation_sha = str_at(mutation, "/proof_sha256");
    let acceptance_proof_path = str_at(acceptance, "/proof_path");
    let mutation_proof_path = str_at(mutation, "/proof_path");
    let acceptance_bytes = u64_at(acceptance, "/proof_bytes");
    let mutation_bytes = u64_at(mutation, "/proof_bytes");
    let proof_identity_matches = valid_sha256(acceptance_sha)
        && acceptance_proof_path == mutation_proof_path
        && acceptance_proof_path == Some(loaded.actual_proof_path.as_str())
        && acceptance_proof_path == Some(release_instance.proof_path.as_str())
        && acceptance_sha == mutation_sha
        && acceptance_sha == Some(loaded.actual_proof_sha256.as_str())
        && acceptance_sha == Some(release_instance.proof_sha256.as_str())
        && acceptance_bytes.is_some()
        && acceptance_bytes == mutation_bytes
        && acceptance_bytes == Some(loaded.actual_proof_bytes)
        && acceptance_bytes == Some(release_instance.proof_bytes);
    add_gate(
        &mut gates,
        "production_proof_identity_matches",
        proof_identity_matches,
        format!(
            "actual=({:?},{},{}), acceptance=({acceptance_proof_path:?},{acceptance_sha:?},{acceptance_bytes:?}), mutation=({mutation_proof_path:?},{mutation_sha:?},{mutation_bytes:?}), release_instance=({},{},{})",
            loaded.actual_proof_path,
            loaded.actual_proof_sha256,
            loaded.actual_proof_bytes,
            release_instance.proof_path,
            release_instance.proof_sha256,
            release_instance.proof_bytes,
        ),
    );

    let acceptance_statement_path = str_at(acceptance, "/statement_path");
    let mutation_statement_path = str_at(mutation, "/statement_path");
    let acceptance_statement_sha = str_at(acceptance, "/statement_sha256");
    let mutation_statement_sha = str_at(mutation, "/statement_sha256");
    let acceptance_statement_pool = str_at(acceptance, "/statement_pool_hex");
    let mutation_statement_pool = str_at(mutation, "/statement_pool_hex");
    let acceptance_statement_sequence = u64_at(acceptance, "/statement_sequence");
    let mutation_statement_sequence = u64_at(mutation, "/statement_sequence");
    let acceptance_statement_digest = str_at(acceptance, "/canonical_public_input_digest");
    let mutation_statement_digest = str_at(mutation, "/canonical_public_input_digest");
    let statement_identity_matches = bool_at(acceptance, "/statement_source_override")
        == Some(true)
        && bool_at(mutation, "/statement_source_override") == Some(true)
        && acceptance_statement_path == mutation_statement_path
        && acceptance_statement_path == Some(release_instance.statement_path.as_str())
        && valid_sha256(acceptance_statement_sha)
        && acceptance_statement_sha == mutation_statement_sha
        && acceptance_statement_sha == Some(release_instance.statement_sha256.as_str())
        && valid_lower_hex_32(acceptance_statement_pool)
        && acceptance_statement_pool == mutation_statement_pool
        && acceptance_statement_pool == Some(release_instance.statement_pool_hex.as_str())
        && acceptance_statement_sequence.is_some()
        && acceptance_statement_sequence == mutation_statement_sequence
        && acceptance_statement_sequence == Some(release_instance.statement_sequence)
        && valid_lower_hex_32(acceptance_statement_digest)
        && acceptance_statement_digest == mutation_statement_digest
        && acceptance_statement_digest
            == Some(release_instance.canonical_public_input_digest.as_str());
    add_gate(
        &mut gates,
        "production_statement_identity_matches",
        statement_identity_matches,
        format!(
            "actual=({},{},{},{},{},{}), acceptance=({acceptance_statement_path:?},{acceptance_statement_sha:?},{acceptance_statement_pool:?},{acceptance_statement_sequence:?},{acceptance_statement_digest:?},override={:?}), mutation=({mutation_statement_path:?},{mutation_statement_sha:?},{mutation_statement_pool:?},{mutation_statement_sequence:?},{mutation_statement_digest:?},override={:?})",
            release_instance.statement_path,
            release_instance.statement_bytes,
            release_instance.statement_sha256,
            release_instance.statement_pool_hex,
            release_instance.statement_sequence,
            release_instance.canonical_public_input_digest,
            bool_at(acceptance, "/statement_source_override"),
            bool_at(mutation, "/statement_source_override"),
        ),
    );

    add_gate(
        &mut gates,
        "release_instance_production_host_verification_green",
        release_instance.production_host_verification_green,
        format!(
            "proof={} statement={} host_green={} evaluation_error={:?}",
            release_instance.proof_path,
            release_instance.statement_path,
            release_instance.production_host_verification_green,
            release_instance.evaluation_error,
        ),
    );

    let selector_is_least_good = release_instance_selector_is_least_good(release_instance)
        && release_instance.good_spend_definition_fingerprint == expected_good_spend_fingerprint();
    add_gate(
        &mut gates,
        "release_instance_serialized_selector_is_least_good_spend",
        selector_is_least_good,
        format!(
            "candidates={}, serialized={:?}, least_good={:?}, branch_acceptance={:?}, definition_fingerprint={}, expected_fingerprint={}, evaluation_error={:?}",
            release_instance.selector_candidates,
            release_instance.serialized_selector,
            release_instance.least_good_selector,
            release_instance
                .good_spend_branches
                .iter()
                .map(|branch| (branch.selector, branch.accepted))
                .collect::<Vec<_>>(),
            release_instance.good_spend_definition_fingerprint,
            expected_good_spend_fingerprint(),
            release_instance.evaluation_error,
        ),
    );

    let proof_is_mined = bool_at(acceptance, "/proof_unmined") == Some(false)
        && bool_at(mutation, "/proof_unmined") == Some(false);
    add_gate(
        &mut gates,
        "proof_is_mined",
        proof_is_mined,
        format!(
            "acceptance.proof_unmined={:?}, mutation.proof_unmined={:?}",
            bool_at(acceptance, "/proof_unmined"),
            bool_at(mutation, "/proof_unmined")
        ),
    );

    let mined_override = bool_at(acceptance, "/proof_source_override") == Some(true)
        && bool_at(mutation, "/proof_source_override") == Some(true)
        && bool_at(mutation, "/production_only_mined_override_exercised") == Some(true);
    add_gate(
        &mut gates,
        "production_only_mined_override_exercised",
        mined_override,
        format!(
            "acceptance_override={:?}, mutation_override={:?}, production_only_exercised={:?}",
            bool_at(acceptance, "/proof_source_override"),
            bool_at(mutation, "/proof_source_override"),
            bool_at(mutation, "/production_only_mined_override_exercised")
        ),
    );

    let production_paths = mutation
        .pointer("/production_paths")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let all_path_tag59 = production_paths
        .iter()
        .all(|path| bool_at(path, "/production_tag59_accepted_mined_sbf") == Some(true));
    let production_tag59_green = proof_is_mined
        && bool_at(acceptance, "/production_api_accepted_mined_sbf") == Some(true)
        && all_path_tag59;
    add_gate(
        &mut gates,
        "production_host_and_sbf_tag59_accepted",
        production_tag59_green,
        format!(
            "host_production_classification_mined={proof_is_mined}, acceptance_sbf={:?}, production_path_sbf_all={all_path_tag59}",
            bool_at(acceptance, "/production_api_accepted_mined_sbf")
        ),
    );

    let baseline_fail_closed = bool_at(acceptance, "/default_tag59_fail_closed_host") == Some(true)
        && bool_at(mutation, "/default_tag65_fail_closed_host") == Some(true);
    add_gate(
        &mut gates,
        "no_default_host_dependencies_fail_closed",
        baseline_fail_closed,
        format!(
            "tag59_no-default={:?}, tag65_no-default={:?}",
            bool_at(acceptance, "/default_tag59_fail_closed_host"),
            bool_at(mutation, "/default_tag65_fail_closed_host")
        ),
    );

    let committed_unmined_controls = bool_at(mutation, "/production_only_unmined_tag59_rejected")
        == Some(true)
        && bool_at(mutation, "/production_only_unmined_tag65_rejected") == Some(true)
        && bool_at(mutation, "/production_only_unmined_tag65_rollback_green") == Some(true)
        && bool_at(mutation, "/production_pow_bypass_exposed") == Some(false);
    add_gate(
        &mut gates,
        "production_committed_unmined_negative_controls",
        committed_unmined_controls,
        format!(
            "tag59_rejected={:?}, tag65_rejected={:?}, tag65_rollback={:?}, pow_bypass_exposed={:?}",
            bool_at(mutation, "/production_only_unmined_tag59_rejected"),
            bool_at(mutation, "/production_only_unmined_tag65_rejected"),
            bool_at(
                mutation,
                "/production_only_unmined_tag65_rollback_green"
            ),
            bool_at(mutation, "/production_pow_bypass_exposed")
        ),
    );

    let mut marker_paths = production_paths
        .iter()
        .filter_map(|path| str_at(path, "/marker_path"))
        .collect::<Vec<_>>();
    marker_paths.sort_unstable();
    let exact_marker_paths =
        marker_paths == vec!["canonical_system_owned_create", "program_owned_zeroed"];
    add_gate(
        &mut gates,
        "exactly_two_production_tag65_marker_paths",
        production_paths.len() == 2 && exact_marker_paths,
        format!(
            "count={}, marker_paths={marker_paths:?}",
            production_paths.len()
        ),
    );

    let finalized_proof_accounts = u64_at(mutation, "/finalize_proof_instruction_wire_ordinal")
        == Some(62)
        && bool_at(acceptance, "/proof_account_finalized_before_verification") == Some(true)
        && production_paths.iter().all(|path| {
            bool_at(
                path,
                "/proof_accounts_finalized_before_production_verification",
            ) == Some(true)
        });
    add_gate(
        &mut gates,
        "production_proof_accounts_irreversibly_finalized",
        production_paths.len() == 2 && finalized_proof_accounts,
        format!(
            "finalize_wire={:?}, acceptance_finalized={:?}, all production paths finalized={finalized_proof_accounts}",
            u64_at(mutation, "/finalize_proof_instruction_wire_ordinal"),
            bool_at(acceptance, "/proof_account_finalized_before_verification")
        ),
    );

    let legacy_tag60 = mutation.pointer("/production_legacy_tag60_compatibility");
    let legacy_tag60_compatibility = legacy_tag60.is_some_and(|legacy| {
        u64_at(legacy, "/instruction_wire_ordinal") == Some(60)
            && all_true(
                legacy,
                &[
                    "/isolated_local_validator_lifecycle",
                    "/proof_meta_read_only",
                    "/proof_meta_non_signer",
                    "/proof_finalized_before_transition",
                    "/committed_transition_succeeded",
                    "/pool_sequence_advanced_exactly_once",
                    "/pool_anchor_replaced",
                    "/nullifier_marker_absent_before",
                    "/nullifier_marker_written_exactly",
                    "/duplicate_rejected_as_already_spent",
                    "/duplicate_rejected_without_second_mutation",
                    "/proof_owner_retained",
                    "/proof_data_retained_bit_for_bit",
                    "/proof_lamports_retained",
                    "/proof_account_retained_exactly",
                ],
            )
            && str_at(legacy, "/proof_owner_before") == str_at(legacy, "/proof_owner_after")
            && str_at(legacy, "/proof_data_sha256_before")
                == str_at(legacy, "/proof_data_sha256_after")
            && u64_at(legacy, "/proof_lamports_before") == u64_at(legacy, "/proof_lamports_after")
    });
    add_gate(
        &mut gates,
        "legacy_tag60_readonly_proof_abi_and_retention",
        legacy_tag60_compatibility,
        format!(
            "legacy tag60 artifact present={}, exact readonly/non-signer ABI and proof retention={legacy_tag60_compatibility}",
            legacy_tag60.is_some()
        ),
    );

    let path_acceptance = production_paths.iter().all(|path| {
        bool_at(path, "/production_tag59_accepted_mined_sbf") == Some(true)
            && bool_at(path, "/production_tag65_clean_simulation_accepted") == Some(true)
            && bool_at(path, "/production_tag65_simulation_proof_sha256_log_exact") == Some(true)
            && str_at(path, "/production_tag65_simulation_logged_proof_sha256")
                == str_at(mutation, "/proof_sha256")
    }) && bool_at(mutation, "/candidate_tag65_accepts_mined_sbf")
        == Some(true);
    add_gate(
        &mut gates,
        "production_tag65_acceptance_teeth",
        production_paths.len() == 2 && path_acceptance,
        format!(
            "candidate_accepts={:?}, all tag59/tag65 path acceptances={path_acceptance}",
            bool_at(mutation, "/candidate_tag65_accepts_mined_sbf")
        ),
    );

    let rollback_teeth = production_paths.iter().all(|path| {
        bool_at(path, "/corrupt_proof_rejected_with_transaction_rollback") == Some(true)
    });
    add_gate(
        &mut gates,
        "production_tag65_rollback_teeth",
        production_paths.len() == 2 && rollback_teeth,
        format!("all corrupt-proof transaction rollbacks={rollback_teeth}"),
    );

    let commit_teeth = production_paths.iter().all(|path| {
        all_true(
            path,
            &[
                "/committed_transition_succeeded",
                "/proof_account_absent_after_success",
                "/pool_sequence_advanced_once",
                "/pool_anchor_replaced",
                "/nullifier_marker_written",
            ],
        )
    });
    add_gate(
        &mut gates,
        "production_tag65_commit_teeth",
        production_paths.len() == 2 && commit_teeth,
        format!("all transition/pool/anchor/nullifier commit teeth={commit_teeth}"),
    );

    let duplicate_teeth = production_paths
        .iter()
        .all(|path| bool_at(path, "/duplicate_rejected_without_second_mutation") == Some(true));
    add_gate(
        &mut gates,
        "production_tag65_duplicate_teeth",
        production_paths.len() == 2 && duplicate_teeth,
        format!("all duplicate rejection teeth={duplicate_teeth}"),
    );

    let exercised_races = production_paths
        .iter()
        .filter_map(|path| {
            bool_at(path, "/concurrent_exactly_one_committed")
                .map(|green| (str_at(path, "/marker_path"), green))
        })
        .collect::<Vec<_>>();
    let race_teeth = !exercised_races.is_empty()
        && exercised_races.iter().all(|(_, green)| *green)
        && exercised_races
            .iter()
            .any(|(path, green)| *path == Some("canonical_system_owned_create") && *green);
    add_gate(
        &mut gates,
        "production_tag65_race_tooth",
        race_teeth,
        format!("exercised_races={exercised_races:?}"),
    );

    let diagnostic_unavailable = bool_at(
        mutation,
        "/production_only_tag59_diagnostic_bit_unavailable",
    ) == Some(true)
        && bool_at(mutation, "/production_only_tag61_unavailable") == Some(true)
        && mutation
            .pointer("/production_only_sbf_features")
            .and_then(Value::as_array)
            .is_some_and(|features| {
                !features
                    .iter()
                    .any(|feature| feature.as_str() == Some("diagnostic-unmined-spend-mutation"))
            });
    add_gate(
        &mut gates,
        "production_diagnostic_unavailable_teeth",
        diagnostic_unavailable,
        format!(
            "tag59_diagnostic_bit_unavailable={:?}, tag61_unavailable={:?}",
            bool_at(
                mutation,
                "/production_only_tag59_diagnostic_bit_unavailable"
            ),
            bool_at(mutation, "/production_only_tag61_unavailable")
        ),
    );

    let acceptance_literal_cu = u64_at(acceptance, "/literal_simulation_cu");
    let acceptance_ledger_sum = checked_sum_at(
        acceptance,
        &[
            "/ledger/transaction_setup_cu",
            "/ledger/proof_load_cu",
            "/ledger/parsed_cu",
            "/ledger/transcript_cu",
            "/ledger/terminal_cu",
            "/ledger/relation_cu",
            "/ledger/openings_cu",
            "/ledger/layer0_queries_cu",
            "/ledger/later_queries_cu",
            "/ledger/completion_cu",
            "/ledger/wrapper_return_cu",
            "/ledger/post_last_marker_cu",
        ],
    );
    let acceptance_ledger_reconciles = acceptance_literal_cu.is_some()
        && acceptance_literal_cu == acceptance_ledger_sum
        && acceptance_literal_cu == u64_at(acceptance, "/ledger/reconciled_total_cu")
        && i64_at(acceptance, "/headroom_under_1_4m_cu")
            == acceptance_literal_cu.map(|cu| CU_LIMIT as i64 - cu as i64);
    add_gate(
        &mut gates,
        "mined_acceptance_cu_ledger_reconciles",
        acceptance_ledger_reconciles,
        format!(
            "literal={acceptance_literal_cu:?}, bucket_sum={acceptance_ledger_sum:?}, reconciled={:?}, headroom={:?}",
            u64_at(acceptance, "/ledger/reconciled_total_cu"),
            i64_at(acceptance, "/headroom_under_1_4m_cu")
        ),
    );

    // Every production tooth exercised against the live validator must be
    // green on every path: the committed-unmined PoW rejections, the sealed
    // duplicate rejection, the concurrency race, the exact refund balance
    // equation, and the cross-deployment-domain rejection with rollback.
    let production_unmined_teeth = production_paths.iter().all(|path| {
        all_true(
            path,
            &[
                "/production_unmined_tag59_rejected",
                "/production_unmined_tag65_rejected",
                "/production_unmined_tag65_rollback_green",
            ],
        )
    });
    let production_duplicate_teeth = production_paths
        .iter()
        .all(|path| bool_at(path, "/duplicate_rejected_without_second_mutation") == Some(true));
    let production_race_teeth = production_paths
        .iter()
        .filter_map(|path| bool_at(path, "/concurrent_exactly_one_committed"))
        .fold((false, true), |(_, all), green| (true, all && green));
    // The refund equation is measured on the landed-commit path; the race
    // path commits through the concurrency probe instead. Require it to be
    // exercised at least once and exact wherever it was measured.
    let production_refund_equation_teeth = production_paths
        .iter()
        .filter_map(|path| bool_at(path, "/refund_balance_equation_exact"))
        .fold((false, true), |(_, all), exact| (true, all && exact));
    let production_deployment_domain_teeth = production_paths.iter().all(|path| {
        all_true(
            path,
            &[
                "/deployment_domain_second_pool_initialized_via_tag63",
                "/deployment_domain_mismatch_rejected_exact",
                "/deployment_domain_mismatch_rollback_green",
            ],
        )
    });
    let production_teeth_green = production_paths.len() == 2
        && production_unmined_teeth
        && production_duplicate_teeth
        && production_race_teeth == (true, true)
        && production_refund_equation_teeth == (true, true)
        && production_deployment_domain_teeth;
    add_gate(
        &mut gates,
        "production_teeth_unmined_duplicate_race_refund_domain_green",
        production_teeth_green,
        format!(
            "unmined={production_unmined_teeth}, duplicate={production_duplicate_teeth}, race(exercised,green)={production_race_teeth:?}, refund_equation(exercised,exact)={production_refund_equation_teeth:?}, deployment_domain={production_deployment_domain_teeth}"
        ),
    );

    let max_tag65_cu = production_paths
        .iter()
        .filter_map(|path| u64_at(path, "/literal_tag65_simulation_cu"))
        .max();
    let cu_ledgers_reconcile = production_paths.iter().all(|path| {
        let literal_tag59 = u64_at(path, "/literal_tag59_simulation_cu");
        let literal_tag65 = u64_at(path, "/literal_tag65_simulation_cu");
        let ledger_tag59 = u64_at(path, "/ledger/production_read_only_tag59_cu");
        let ledger_increment = i64_at(path, "/ledger/production_tag65_increment_over_tag59_cu");
        let expected_increment = literal_tag59
            .zip(literal_tag65)
            .and_then(|(tag59, tag65)| i64::try_from(i128::from(tag65) - i128::from(tag59)).ok());
        literal_tag59.is_some()
            && literal_tag65.is_some()
            && literal_tag59 == ledger_tag59
            && ledger_increment == expected_increment
            && literal_tag65 == u64_at(path, "/ledger/production_tag65_total_cu")
            && literal_tag65 == u64_at(path, "/ledger/reconciled_total_cu")
            && i64_at(path, "/headroom_under_1_4m_cu")
                == literal_tag65.map(|cu| CU_LIMIT as i64 - cu as i64)
    });
    add_gate(
        &mut gates,
        "production_tag65_cu_ledgers_reconcile",
        production_paths.len() == 2 && cu_ledgers_reconcile,
        format!(
            "all exact tag59/tag65/increment/reconciled/headroom identities={cu_ledgers_reconcile}"
        ),
    );
    add_gate(
        &mut gates,
        "production_tag65_under_1_4m_cu",
        max_tag65_cu.is_some_and(|cu| cu <= CU_LIMIT),
        format!("max_literal_production_tag65_cu={max_tag65_cu:?}, limit={CU_LIMIT}"),
    );

    let production_tag59_baselines = production_paths
        .iter()
        .filter_map(|path| u64_at(path, "/literal_tag59_simulation_cu"))
        .collect::<Vec<_>>();
    let production_tag59_baseline_matches = production_tag59_baselines.len() == 2
        && production_tag59_baselines
            .windows(2)
            .all(|pair| pair[0] == pair[1]);
    let same_measurement_context = str_at(acceptance, "/validator_version")
        == str_at(mutation, "/validator_version")
        && u64_at(acceptance, "/instruction_wire_ordinal") == Some(59)
        && u64_at(mutation, "/production_instruction_wire_ordinal") == Some(65)
        && u64_at(mutation, "/diagnostic_instruction_wire_ordinal") == Some(61)
        && u64_at(mutation, "/finalize_proof_instruction_wire_ordinal") == Some(62)
        && production_tag59_baseline_matches;
    add_gate(
        &mut gates,
        "production_measurement_context_matches",
        production_paths.len() == 2 && same_measurement_context,
        format!(
            "validator_equal={}, wires=({:?},{:?},{:?},{:?}), acceptance_tag59={:?}, production_tag59_baselines={production_tag59_baselines:?}",
            str_at(acceptance, "/validator_version") == str_at(mutation, "/validator_version"),
            u64_at(acceptance, "/instruction_wire_ordinal"),
            u64_at(mutation, "/production_instruction_wire_ordinal"),
            u64_at(mutation, "/diagnostic_instruction_wire_ordinal"),
            u64_at(mutation, "/finalize_proof_instruction_wire_ordinal"),
            u64_at(acceptance, "/literal_simulation_cu")
        ),
    );

    let (default_features, production_alias, program_default_enabled) =
        spend_program_defaults_match(&loaded.program_manifest);
    let workspace_host_defaults_disabled = manifest_dependency_disables_defaults(
        &loaded.workspace_manifest,
        "workspace.dependencies",
        "aspis-verifier",
    );
    let xtask_host_defaults_disabled = manifest_dependency_disables_defaults(
        &loaded.xtask_manifest,
        "dependencies",
        "aspis-verifier",
    );
    add_gate(
        &mut gates,
        "spend_default_enabled_and_host_dependencies_isolated",
        program_default_enabled
            && workspace_host_defaults_disabled
            && xtask_host_defaults_disabled,
        format!(
            "program_default={default_features:?}, production_alias={production_alias:?}, workspace_default_features_false={workspace_host_defaults_disabled}, xtask_default_features_false={xtask_host_defaults_disabled}"
        ),
    );

    let measured_production_features = mutation
        .pointer("/production_only_sbf_features")
        .and_then(Value::as_array)
        .map(|features| {
            features
                .iter()
                .filter_map(Value::as_str)
                .collect::<Vec<_>>()
        });
    let explicit_alias_measured =
        measured_production_features.as_deref() == Some(&["spend-production"][..]);
    add_gate(
        &mut gates,
        "production_only_kat_used_explicit_production_alias",
        explicit_alias_measured,
        format!("production_only_sbf_features={measured_production_features:?}"),
    );

    let mut expected_forbidden_unions = PRODUCTION_FORBIDDEN_FEATURES
        .iter()
        .map(|feature| format!("spend-production+{feature}"))
        .collect::<Vec<_>>();
    expected_forbidden_unions.push("spend-production+all-forbidden".to_string());
    expected_forbidden_unions.sort_unstable();
    let mut tested_forbidden_unions = mutation
        .pointer("/production_alias_forbidden_feature_unions_tested")
        .and_then(Value::as_array)
        .map(|values| {
            values
                .iter()
                .filter_map(Value::as_str)
                .map(ToOwned::to_owned)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    tested_forbidden_unions.sort_unstable();
    let forbidden_feature_compile_fail = bool_at(
        mutation,
        "/production_alias_forbidden_feature_unions_rejected",
    ) == Some(true)
        && tested_forbidden_unions == expected_forbidden_unions;
    add_gate(
        &mut gates,
        "production_alias_forbidden_feature_unions_compile_fail",
        forbidden_feature_compile_fail,
        format!(
            "rejected={:?}, tested={tested_forbidden_unions:?}, expected={expected_forbidden_unions:?}",
            bool_at(
                mutation,
                "/production_alias_forbidden_feature_unions_rejected"
            )
        ),
    );

    let mutation_sbf_bytes = u64_at(mutation, "/production_only_sbf_bytes");
    let mutation_sbf_sha = str_at(mutation, "/production_only_sbf_sha256");
    let default_sbf_matches = mutation_sbf_bytes == Some(loaded.default_sbf_bytes)
        && valid_sha256(mutation_sbf_sha)
        && mutation_sbf_sha == Some(loaded.default_sbf_sha256.as_str());
    add_gate(
        &mut gates,
        "default_sbf_matches_production_only_kat_binary",
        default_sbf_matches,
        format!(
            "default=({},{}) mutation=({mutation_sbf_bytes:?},{mutation_sbf_sha:?})",
            loaded.default_sbf_bytes, loaded.default_sbf_sha256
        ),
    );

    let selected_soundness = f64_at(soundness, "/soundness/selected_floor_bits");
    let coarse_soundness = f64_at(soundness, "/soundness/coarse_whole_ledger_times_three_bits");
    let soundness_bookable = bool_at(soundness, "/bookable") == Some(true)
        && bool_at(acceptance, "/soundness_bookable") == Some(true)
        && bool_at(mutation, "/soundness_bookable") == Some(true)
        && bool_at(complete_good, "/spend_soundness_bookable") == Some(true)
        && bool_at(
            complete_good,
            "/liveness_bound_bookable_for_prospective_spend",
        ) == Some(true)
        && selected_soundness.is_some_and(|bits| bits >= MIN_SECURITY_BITS)
        && coarse_soundness.is_some_and(|bits| bits >= MIN_SECURITY_BITS);
    add_gate(
        &mut gates,
        "johnson_selected_and_conservative_coarse_floors_at_least_100_bits",
        soundness_bookable,
        format!(
            "selected_floor={selected_soundness:?}, conservative_coarse_floor={coarse_soundness:?}, theorem_bookable={:?}, acceptance_bookable={:?}, mutation_bookable={:?}, complete_good_bookable={:?}",
            bool_at(soundness, "/bookable"),
            bool_at(acceptance, "/soundness_bookable"),
            bool_at(mutation, "/soundness_bookable"),
            bool_at(complete_good, "/spend_soundness_bookable")
        ),
    );

    let expected_query_count =
        u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_QUERY_COUNT);
    let expected_attempt_cap =
        aspis_prover::state_only_good_spend::SPEND_GOOD_SCHEDULE_MAX_ATTEMPTS as u64;
    let expected_batch_bits =
        u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_BATCH_GRINDING_BITS);
    let expected_final_bits =
        u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_GRINDING_BITS);
    let expected_fold_bits = aspis_core::state_only_prefix::STATE_ONLY_SPEND_FOLD_GRINDING_BITS
        .into_iter()
        .map(u64::from)
        .collect::<Vec<_>>();
    let query_and_work_schedule_match = u64_at(acceptance, "/query_count")
        == Some(expected_query_count)
        && u64_at(mutation, "/query_count") == Some(expected_query_count)
        && u64_at(soundness, "/candidate/query_count") == Some(expected_query_count)
        && u64_at(acceptance, "/batch_grinding_bits") == Some(expected_batch_bits)
        && u64_at(mutation, "/batch_grinding_bits") == Some(expected_batch_bits)
        && u64_at(soundness, "/candidate/batch_work_bits") == Some(expected_batch_bits)
        && u64_at(acceptance, "/final_grinding_bits") == Some(expected_final_bits)
        && u64_at(mutation, "/final_grinding_bits") == Some(expected_final_bits)
        && u64_at(soundness, "/candidate/final_work_bits") == Some(expected_final_bits)
        && u64_array_at(acceptance, "/fold_grinding_bits") == Some(expected_fold_bits.clone())
        && u64_array_at(mutation, "/fold_grinding_bits") == Some(expected_fold_bits.clone())
        && u64_array_at(soundness, "/candidate/fold_work_bits") == Some(expected_fold_bits.clone())
        && release_instance.production_host_verification_green;
    add_gate(
        &mut gates,
        "spend_q18_and_work_schedule_match_live_proof",
        query_and_work_schedule_match,
        format!(
            "expected q={expected_query_count}, batch={expected_batch_bits}, folds={expected_fold_bits:?}, final={expected_final_bits}; acceptance=({:?},{:?},{:?},{:?}), mutation=({:?},{:?},{:?},{:?}), soundness=({:?},{:?},{:?},{:?}), parsed_proof_host_green={}",
            u64_at(acceptance, "/query_count"),
            u64_at(acceptance, "/batch_grinding_bits"),
            u64_array_at(acceptance, "/fold_grinding_bits"),
            u64_at(acceptance, "/final_grinding_bits"),
            u64_at(mutation, "/query_count"),
            u64_at(mutation, "/batch_grinding_bits"),
            u64_array_at(mutation, "/fold_grinding_bits"),
            u64_at(mutation, "/final_grinding_bits"),
            u64_at(soundness, "/candidate/query_count"),
            u64_at(soundness, "/candidate/batch_work_bits"),
            u64_array_at(soundness, "/candidate/fold_work_bits"),
            u64_at(soundness, "/candidate/final_work_bits"),
            release_instance.production_host_verification_green,
        ),
    );

    let reconstructed_ledger = reconstruct_spend_q18_ledger(soundness, complete_good, hvzk);
    let (reconstructed_ledger_passed, reconstructed_ledger_evidence) = match reconstructed_ledger {
        Ok(evidence) => (true, evidence),
        Err(error) => (
            false,
            format!("fail-closed reconstruction error: {error:#}"),
        ),
    };
    add_gate(
        &mut gates,
        SPEND_SOUNDNESS_RECONSTRUCTION_GATE,
        reconstructed_ledger_passed,
        reconstructed_ledger_evidence,
    );

    let johnson_parameters = u64_at(soundness, "/candidate/query_count")
        == Some(expected_query_count)
        && u64_at(soundness, "/candidate/inverse_rate") == Some(512)
        && u64_at(soundness, "/candidate/query_candidates") == Some(3)
        && u64_at(soundness, "/candidate/attempt_cap") == Some(expected_attempt_cap)
        && str_at(soundness, "/soundness/regime").is_some_and(|regime| regime.contains("Johnson"))
        && bool_at(soundness, "/query_domain_guard/injective") == Some(true)
        && u64_at(soundness, "/query_domain_guard/root_one_count") == Some(0);
    add_gate(
        &mut gates,
        "proven_johnson_parameter_regime",
        johnson_parameters,
        format!(
            "q={:?}, inverse_rate={:?}, selectors={:?}, cap={:?}, regime={:?}",
            u64_at(soundness, "/candidate/query_count"),
            u64_at(soundness, "/candidate/inverse_rate"),
            u64_at(soundness, "/candidate/query_candidates"),
            u64_at(soundness, "/candidate/attempt_cap"),
            str_at(soundness, "/soundness/regime")
        ),
    );

    let root_minor_match = bool_at(soundness, "/root_neutral_polynomial_minor/complete")
        == Some(true)
        && bool_at(complete_good, "/root_neutral_minor/complete") == Some(true)
        && str_at(
            soundness,
            "/root_neutral_polynomial_minor/minor_fingerprint",
        ) == str_at(complete_good, "/root_neutral_minor/fingerprint")
        && bool_at(complete_good, "/bound_product/complete") == Some(true);
    add_gate(
        &mut gates,
        "complete_good_theorem_product_bound",
        root_minor_match,
        format!(
            "soundness_minor={:?}, complete_good_minor={:?}, complete_product={:?}",
            str_at(
                soundness,
                "/root_neutral_polynomial_minor/minor_fingerprint"
            ),
            str_at(complete_good, "/root_neutral_minor/fingerprint"),
            bool_at(complete_good, "/bound_product/complete")
        ),
    );

    let expected_good = expected_good_spend_fingerprint();
    let expected_layout = expected_layout_fingerprint();
    let fingerprints_match = str_at(hvzk, "/affine_closure/good_spend_definition_fingerprint")
        == Some(expected_good.as_str())
        && str_at(hvzk, "/affine_closure/layout_factor_fingerprint")
            == Some(expected_layout.as_str())
        && u64_at(hvzk, "/affine_closure/d_factor_identifier") == Some(0)
        && u64_at(soundness, "/candidate/d_factor") == Some(0);
    add_gate(
        &mut gates,
        "layout_and_good_spend_fingerprints_match_live_code",
        fingerprints_match,
        format!(
            "good expected={expected_good}, artifact={:?}; layout expected={expected_layout}, artifact={:?}; D factors=({:?},{:?})",
            str_at(hvzk, "/affine_closure/good_spend_definition_fingerprint"),
            str_at(hvzk, "/affine_closure/layout_factor_fingerprint"),
            u64_at(hvzk, "/affine_closure/d_factor_identifier"),
            u64_at(soundness, "/candidate/d_factor")
        ),
    );

    let cap17_bits = f64_at(hvzk, "/q3_cap17_release/rank_exhaustion_abort_bits");
    let cap17_fixed_release = all_true(
        hvzk,
        &[
            "/q3_cap17_release/independent_post_final_branches_from_common_prefix",
            "/q3_cap17_release/all_three_evaluated_before_selection",
            "/q3_cap17_release/only_selected_openings_serialized",
            "/q3_cap17_release/all_bad_attempt_retryable",
            "/q3_cap17_release/other_gate_build_errors_fatal_and_opaque",
            "/q3_cap17_release/abort_joint_law_witness_independent_in_epro_hybrid",
            "/q3_cap17_release/fixed_release_controller_implemented",
            "/q3_cap17_release/production_example_keeps_boundary_live_while_worker_runs",
        ],
    ) && u64_at(hvzk, "/q3_cap17_release/query_candidates") == Some(3)
        && u64_at(hvzk, "/q3_cap17_release/attempt_cap") == Some(expected_attempt_cap)
        && str_at(hvzk, "/q3_cap17_release/selection_rule") == Some("least GoodSpend selector")
        && cap17_bits.is_some_and(|bits| bits >= MIN_SECURITY_BITS)
        && all_true(
            soundness,
            &[
                "/host_first_good_release_integration/two_phase_common_attempt",
                "/host_first_good_release_integration/all_three_post_final_schedules_evaluated",
                "/host_first_good_release_integration/opening_serialization_after_selection",
                "/host_first_good_release_integration/distinct_spend_public_release_type",
                "/host_first_good_release_integration/fixed_boundary_controller",
                "/host_first_good_release_integration/valid_selector_proofs_0_1_2_built_and_verified",
            ],
        );
    add_gate(
        &mut gates,
        "q3_cap17_fixed_release_gates",
        cap17_fixed_release,
        format!(
            "selectors={:?}, cap={:?}, abort_bits={cap17_bits:?}, selection={:?}",
            u64_at(hvzk, "/q3_cap17_release/query_candidates"),
            u64_at(hvzk, "/q3_cap17_release/attempt_cap"),
            str_at(hvzk, "/q3_cap17_release/selection_rule")
        ),
    );

    let real_vs_simulator_hiding_bits =
        f64_at(hvzk, "/epro/complete_view_real_vs_simulator_bound_bits");
    let pairwise_hiding_bits = f64_at(hvzk, "/epro/complete_view_pairwise_witness_bound_bits");
    let declared_model_hiding = pairwise_hiding_bits.is_some_and(|bits| bits >= MIN_SECURITY_BITS)
        && real_vs_simulator_hiding_bits
            .zip(pairwise_hiding_bits)
            .is_some_and(|(real_vs_simulator, pairwise)| real_vs_simulator >= pairwise)
        && u64_at(hvzk, "/epro/pairwise_triangle_factor") == Some(2)
        && bool_at(hvzk, "/epro/pairwise_above_100_bits") == Some(true)
        && bool_at(
            hvzk,
            "/claim/complete_system_computational_privacy_quotable_in_declared_model",
        ) == Some(true)
        && bool_at(
            hvzk,
            "/theorem_gates/complete_view_computational_hvzk_in_declared_model",
        ) == Some(true)
        && bool_at(
            soundness,
            "/computational_hvzk/complete_view_closed_in_declared_model",
        ) == Some(true)
        && bool_at(
            complete_good,
            "/computational_hvzk/complete_view_closed_in_declared_model",
        ) == Some(true);
    add_gate(
        &mut gates,
        "computational_hiding_at_least_100_bits_in_declared_model",
        declared_model_hiding,
        format!(
            "proof-independent theorem evidence: real_vs_simulator={real_vs_simulator_hiding_bits:?}, pairwise_witness={pairwise_hiding_bits:?}, triangle_factor={:?}, complete_view={:?}, complete_system={:?}; concrete release applicability is gated separately by exact proof+statement host/SBF/Good checks",
            u64_at(hvzk, "/epro/pairwise_triangle_factor"),
            bool_at(
                hvzk,
                "/theorem_gates/complete_view_computational_hvzk_in_declared_model"
            ),
            bool_at(
                hvzk,
                "/claim/complete_system_computational_privacy_quotable_in_declared_model"
            )
        ),
    );

    let failed_gates = gates
        .iter()
        .filter(|gate| !gate.passed)
        .map(|gate| gate.name)
        .collect::<Vec<_>>();
    let released = failed_gates.is_empty();
    SpendOneTransactionRelease {
        artifact: "spend_one_transaction_release",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-spend-one-transaction-release",
        status: if released {
            "released_all_required_gates_green"
        } else {
            "blocked_fail_closed"
        },
        released,
        scope: ReleaseScope {
            included: "one atomic Solana transaction that verifies the finalized Spend proof and commits the nullifier marker plus pool-state mutation",
            proof_account_precondition: "the transaction consumes a finalized, pre-uploaded proof account",
            excluded: [
                "proof-account creation",
                "proof-account chunk-upload transactions and their compute/fees",
            ],
        },
        compute_unit_limit: CU_LIMIT,
        max_literal_production_tag65_cu: max_tag65_cu,
        exact_headroom_under_1_4m_cu: max_tag65_cu
            .map(|cu| CU_LIMIT as i64 - cu as i64),
        selected_soundness_floor_bits: selected_soundness,
        coarse_whole_soundness_floor_bits: coarse_soundness,
        computational_hiding_real_vs_simulator_bound_bits: real_vs_simulator_hiding_bits,
        computational_hiding_pairwise_witness_bound_bits: pairwise_hiding_bits,
        proof: ReleaseProofIdentity {
            sha256: Some(loaded.actual_proof_sha256.clone()),
            bytes: Some(loaded.actual_proof_bytes),
            actual_path: Some(loaded.actual_proof_path.clone()),
            acceptance_path: str_at(acceptance, "/proof_path").map(ToOwned::to_owned),
            mutation_path: str_at(mutation, "/proof_path").map(ToOwned::to_owned),
        },
        release_instance: loaded.release_instance.clone(),
        default_production_sbf: DefaultProductionSbfIdentity {
            path: DEFAULT_SBF_PATH,
            build_command:
                "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml",
            freshly_built_by_release_command: true,
            bytes: Some(loaded.default_sbf_bytes),
            sha256: Some(loaded.default_sbf_sha256),
            mutation_recorded_bytes: mutation_sbf_bytes,
            mutation_recorded_sha256: mutation_sbf_sha.map(ToOwned::to_owned),
        },
        source_artifacts: loaded.sources,
        gates,
        failed_gates,
        notes: [
            "This certificate is fail-closed: released=true only when every listed gate passes in one evaluation.",
            "Soundness and complete-Good are proof-independent theorem artifacts; their exact files are bound by SHA-256 and their layout/Good identities are checked against live code.",
            "The production proof and canonical public-statement sidecar are read directly; their identities must agree with both acceptance and mutation, and the exact pair must pass the production host verifier plus the live three-branch least-Good replay.",
            "Concrete-proof KAT fields under the static HVZK artifact's complete_public_view object are non-authorizing regression metadata; production_release explicitly omits duplicated concrete identities, and neither object can authorize this release instance.",
            "The release command removes and freshly rebuilds the plain manifest-default SBF before comparing it with the explicit production-alias KAT; proof-account creation and chunk uploads remain outside this one-transaction CU claim.",
        ],
    }
}

fn freshly_build_plain_default_sbf(workspace_root: &Path) -> Result<()> {
    let output = workspace_root.join(DEFAULT_SBF_PATH);
    if output.exists() {
        fs::remove_file(&output)
            .with_context(|| format!("remove stale default SBF {}", output.display()))?;
    }
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .current_dir(workspace_root)
        .arg("--manifest-path")
        .arg(workspace_root.join(PROGRAM_MANIFEST_PATH))
        .status()
        .context("cargo-build-sbf not found on PATH — install the Solana toolchain")?;
    if !status.success() {
        bail!("plain manifest-default cargo-build-sbf failed");
    }
    ensure!(
        output.is_file(),
        "plain manifest-default build omitted {}",
        output.display()
    );
    Ok(())
}

pub fn evaluate(workspace_root: &Path) -> Result<SpendOneTransactionRelease> {
    freshly_build_plain_default_sbf(workspace_root)?;
    Ok(evaluate_loaded(load_artifacts(workspace_root)?))
}

/// Re-evaluate the complete release certificate against the files currently
/// present in the workspace without rebuilding or writing anything.
///
/// The devnet preflight uses this read-only path to prove that a supplied
/// certificate is the output of the live release policy, rather than trusting
/// an arbitrary JSON document whose self-declared gates happen to be green.
pub(crate) fn evaluate_existing(workspace_root: &Path) -> Result<SpendOneTransactionRelease> {
    Ok(evaluate_loaded(load_artifacts(workspace_root)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::sync::OnceLock;

    fn workspace_root() -> std::path::PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .to_path_buf()
    }

    fn gate<'a>(report: &'a SpendOneTransactionRelease, name: &str) -> &'a ReleaseGate {
        report.gates.iter().find(|gate| gate.name == name).unwrap()
    }

    /// The synthetic default-production SBF used by gate-logic tests. The
    /// mutation fixture records this content's exact sha256/byte count, so
    /// the binary-identity gate logic is exercised without depending on a
    /// locally built `target/deploy/aspis_verifier.so` (CI has no
    /// cargo-build-sbf). Fresh production certificates are produced by the
    /// release command against a freshly built SBF.
    const SYNTHETIC_DEFAULT_SBF: &[u8; 208] =
        b"synthetic-spend-production-sbf-for-gate-logic-tests\n\
          synthetic-spend-production-sbf-for-gate-logic-tests\n\
          synthetic-spend-production-sbf-for-gate-logic-tests\n\
          synthetic-spend-production-sbf-for-gate-logic-tests\n";

    fn fixture_json(
        name: &str,
        label: &'static str,
        recorded_path: &str,
    ) -> (SourceArtifact, Value) {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("fixtures")
            .join(name);
        let bytes = fs::read(&path).unwrap();
        let value: Value = serde_json::from_slice(&bytes).unwrap();
        (
            SourceArtifact {
                label: label.to_string(),
                path: recorded_path.to_string(),
                bytes: bytes.len(),
                sha256: hex_sha256(&bytes),
            },
            value,
        )
    }

    fn frozen_release_instance(acceptance: &Value) -> ReleaseInstance {
        let branch =
            |selector: u8, root: &str, gd: &str, h1: &str, product: &str| ReleaseGoodSpendBranch {
                selector,
                accepted: true,
                rejection: None,
                root_neutral_rank_m31: 1_404,
                remaining_gd_query_rank_m31: 288,
                remaining_gd_terminal_rank_m31: 12,
                h1_query_rank_m31: 288,
                h1_terminal_rank_m31: 12,
                dynamic_root_minor_fingerprint: root.to_string(),
                dynamic_remaining_gd_minor_fingerprint: gd.to_string(),
                dynamic_h1_minor_fingerprint: h1.to_string(),
                dynamic_product_fingerprint: product.to_string(),
            };
        // The three branch fingerprints below are the frozen release proof's
        // recorded values; the ignored full-replay test recomputes them from
        // the committed fixture bytes through the complete host verifier and
        // GoodSpend gate.
        ReleaseInstance {
            proof_path: str_at(acceptance, "/proof_path").unwrap().to_string(),
            proof_bytes: u64_at(acceptance, "/proof_bytes").unwrap(),
            proof_sha256: str_at(acceptance, "/proof_sha256").unwrap().to_string(),
            statement_path: str_at(acceptance, "/statement_path").unwrap().to_string(),
            statement_bytes: 767,
            statement_sha256: str_at(acceptance, "/statement_sha256").unwrap().to_string(),
            statement_pool_hex: str_at(acceptance, "/statement_pool_hex")
                .unwrap()
                .to_string(),
            statement_sequence: u64_at(acceptance, "/statement_sequence").unwrap(),
            canonical_public_input_digest: str_at(acceptance, "/canonical_public_input_digest")
                .unwrap()
                .to_string(),
            selector_candidates: 3,
            serialized_selector: Some(0),
            least_good_selector: Some(0),
            good_spend_branches: vec![
                branch(
                    0,
                    "0x5a2f5acd02246d75",
                    "0x3eda3a0ca1f69161",
                    "0xc93dc240cebd8de2",
                    "0x9e4ed9793b22724c",
                ),
                branch(
                    1,
                    "0xdbc0b98028536659",
                    "0x91de71ee39ef727d",
                    "0x5fab1419924e1e76",
                    "0x85f68d6019c06a7b",
                ),
                branch(
                    2,
                    "0x0a96f53988a87997",
                    "0x1cd9241f4e4703c4",
                    "0x10e79da529c574ed",
                    "0x690e5657f3587507",
                ),
            ],
            good_spend_definition_fingerprint: expected_good_spend_fingerprint(),
            production_host_verification_green: true,
            evaluation_error: None,
        }
    }

    fn build_fixture_artifacts() -> LoadedArtifacts {
        let (acceptance_source, acceptance) = fixture_json(
            "spend_acceptance_production_mined.json",
            "acceptance",
            PRODUCTION_ACCEPTANCE_PATH,
        );
        let (mutation_source, mutation) = fixture_json(
            "spend_mutation_production_mined.json",
            "mutation",
            PRODUCTION_MUTATION_PATH,
        );
        let (soundness_source, soundness) = fixture_json(
            "spend_d_after_g_soundness_epro.json",
            "soundness",
            SOUNDNESS_PATH,
        );
        let (complete_good_source, complete_good) = fixture_json(
            "spend_complete_good_product.json",
            "complete_good",
            COMPLETE_GOOD_PATH,
        );
        let (hvzk_source, hvzk) = fixture_json(
            "spend_computational_hvzk_closure.json",
            "computational_hvzk",
            HVZK_PATH,
        );
        let workspace_root = workspace_root();
        let (program_manifest_source, program_manifest) =
            load_raw_source(&workspace_root, "program_manifest", PROGRAM_MANIFEST_PATH).unwrap();
        let (workspace_manifest_source, workspace_manifest) = load_raw_source(
            &workspace_root,
            "workspace_manifest",
            WORKSPACE_MANIFEST_PATH,
        )
        .unwrap();
        let (xtask_manifest_source, xtask_manifest) =
            load_raw_source(&workspace_root, "xtask_manifest", XTASK_MANIFEST_PATH).unwrap();
        let (proof_source, actual_proof_path, proof_bytes, actual_proof_sha256) =
            load_selected_proof(&workspace_root, &acceptance).unwrap();
        let (statement_source, _, statement_file) =
            load_selected_statement(&workspace_root, &acceptance).unwrap();
        let release_instance = frozen_release_instance(&acceptance);
        let default_sbf_source = SourceArtifact {
            label: "default_production_sbf".to_string(),
            path: DEFAULT_SBF_PATH.to_string(),
            bytes: SYNTHETIC_DEFAULT_SBF.len(),
            sha256: hex_sha256(SYNTHETIC_DEFAULT_SBF),
        };
        assert_eq!(release_instance.statement_sha256, statement_file.sha256);
        LoadedArtifacts {
            sources: vec![
                acceptance_source,
                mutation_source,
                soundness_source,
                complete_good_source,
                hvzk_source,
                program_manifest_source,
                workspace_manifest_source,
                xtask_manifest_source,
                proof_source,
                statement_source,
                default_sbf_source.clone(),
            ],
            acceptance,
            mutation,
            soundness,
            complete_good,
            hvzk,
            program_manifest: String::from_utf8(program_manifest).unwrap(),
            workspace_manifest: String::from_utf8(workspace_manifest).unwrap(),
            xtask_manifest: String::from_utf8(xtask_manifest).unwrap(),
            actual_proof_path,
            actual_proof_bytes: proof_bytes.len() as u64,
            actual_proof_sha256,
            release_instance,
            default_sbf_bytes: SYNTHETIC_DEFAULT_SBF.len() as u64,
            default_sbf_sha256: hex_sha256(SYNTHETIC_DEFAULT_SBF),
        }
    }

    fn loaded_artifacts() -> LoadedArtifacts {
        static LOADED: OnceLock<LoadedArtifacts> = OnceLock::new();
        LOADED.get_or_init(build_fixture_artifacts).clone()
    }

    /// Full-strength release-instance replay over the committed frozen
    /// fixture: complete production host verification plus the PoW-checked
    /// three-branch GoodSpend evaluation, compared field-for-field against
    /// the synthetic instance the gate-logic tests use.
    #[test]
    #[ignore = "slow exact q3 complete-product replay; run in --release"]
    fn frozen_release_fixture_replays_the_recorded_instance_exactly() {
        let loaded = loaded_artifacts();
        let (_, proof_path, proof_bytes, proof_sha256) =
            load_selected_proof(&workspace_root(), &loaded.acceptance).unwrap();
        let (_, statement_path, statement_file) =
            load_selected_statement(&workspace_root(), &loaded.acceptance).unwrap();
        let replayed = build_release_instance(
            proof_path,
            proof_sha256,
            &proof_bytes,
            statement_path,
            &statement_file,
        );
        assert!(replayed.production_host_verification_green);
        assert_eq!(replayed.evaluation_error, None);
        let expected = &loaded.release_instance;
        assert_eq!(replayed.proof_sha256, expected.proof_sha256);
        assert_eq!(replayed.proof_bytes, expected.proof_bytes);
        assert_eq!(replayed.statement_sha256, expected.statement_sha256);
        assert_eq!(
            replayed.canonical_public_input_digest,
            expected.canonical_public_input_digest
        );
        assert_eq!(replayed.serialized_selector, expected.serialized_selector);
        assert_eq!(replayed.least_good_selector, expected.least_good_selector);
        assert_eq!(
            replayed.good_spend_definition_fingerprint,
            expected.good_spend_definition_fingerprint
        );
        for (replayed_branch, expected_branch) in replayed
            .good_spend_branches
            .iter()
            .zip(&expected.good_spend_branches)
        {
            assert_eq!(replayed_branch.selector, expected_branch.selector);
            assert!(replayed_branch.accepted);
            assert_eq!(
                replayed_branch.dynamic_root_minor_fingerprint,
                expected_branch.dynamic_root_minor_fingerprint
            );
            assert_eq!(
                replayed_branch.dynamic_remaining_gd_minor_fingerprint,
                expected_branch.dynamic_remaining_gd_minor_fingerprint
            );
            assert_eq!(
                replayed_branch.dynamic_h1_minor_fingerprint,
                expected_branch.dynamic_h1_minor_fingerprint
            );
            assert_eq!(
                replayed_branch.dynamic_product_fingerprint,
                expected_branch.dynamic_product_fingerprint
            );
        }
        assert!(release_instance_selector_is_least_good(&replayed));
    }

    const SPEND_SCHEDULE_GATE: &str = "spend_q18_and_work_schedule_match_live_proof";

    fn live_q18_schedule_artifacts() -> LoadedArtifacts {
        let mut loaded = loaded_artifacts();
        let query_count = u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_QUERY_COUNT);
        let batch_work_bits =
            u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_BATCH_GRINDING_BITS);
        let fold_work_bits = aspis_core::state_only_prefix::STATE_ONLY_SPEND_FOLD_GRINDING_BITS
            .into_iter()
            .map(u64::from)
            .collect::<Vec<_>>();
        let final_work_bits =
            u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_GRINDING_BITS);

        for artifact in [&mut loaded.acceptance, &mut loaded.mutation] {
            artifact["query_count"] = Value::from(query_count);
            artifact["batch_grinding_bits"] = Value::from(batch_work_bits);
            artifact["fold_grinding_bits"] = json!(fold_work_bits);
            artifact["final_grinding_bits"] = Value::from(final_work_bits);
        }
        loaded.soundness["candidate"]["query_count"] = Value::from(query_count);
        loaded.soundness["candidate"]["batch_work_bits"] = Value::from(batch_work_bits);
        loaded.soundness["candidate"]["fold_work_bits"] = json!(fold_work_bits);
        loaded.soundness["candidate"]["final_work_bits"] = Value::from(final_work_bits);
        loaded.release_instance.production_host_verification_green = true;
        loaded
    }

    fn assert_live_schedule_gate(loaded: &LoadedArtifacts, expected: bool) {
        assert_eq!(
            gate(&evaluate_loaded(loaded.clone()), SPEND_SCHEDULE_GATE).passed,
            expected
        );
    }

    fn assert_reconstruction_gate(loaded: &LoadedArtifacts, expected: bool) {
        let report = evaluate_loaded(loaded.clone());
        let reconstruction = gate(&report, SPEND_SOUNDNESS_RECONSTRUCTION_GATE);
        assert_eq!(
            reconstruction.passed, expected,
            "{}",
            reconstruction.evidence
        );
    }

    fn good_branch(selector: u8, accepted: bool) -> ReleaseGoodSpendBranch {
        ReleaseGoodSpendBranch {
            selector,
            accepted,
            rejection: (!accepted).then(|| "RootNeutralIncomplete".to_string()),
            root_neutral_rank_m31: accepted as usize,
            remaining_gd_query_rank_m31: accepted as usize,
            remaining_gd_terminal_rank_m31: accepted as usize,
            h1_query_rank_m31: accepted as usize,
            h1_terminal_rank_m31: accepted as usize,
            dynamic_root_minor_fingerprint: "0x0000000000000000".to_string(),
            dynamic_remaining_gd_minor_fingerprint: "0x0000000000000000".to_string(),
            dynamic_h1_minor_fingerprint: "0x0000000000000000".to_string(),
            dynamic_product_fingerprint: "0x0000000000000000".to_string(),
        }
    }

    fn selector_instance(accepted: [bool; 3], serialized_selector: Option<u8>) -> ReleaseInstance {
        let branches = accepted
            .into_iter()
            .enumerate()
            .map(|(selector, accepted)| good_branch(selector as u8, accepted))
            .collect::<Vec<_>>();
        let least_good_selector = branches
            .iter()
            .find(|branch| branch.accepted)
            .map(|branch| branch.selector);
        ReleaseInstance {
            proof_path: "proof.bin".to_string(),
            proof_bytes: 1,
            proof_sha256: "00".repeat(32),
            statement_path: "statement.json".to_string(),
            statement_bytes: 1,
            statement_sha256: "11".repeat(32),
            statement_pool_hex: "22".repeat(32),
            statement_sequence: 1,
            canonical_public_input_digest: "33".repeat(32),
            selector_candidates: 3,
            serialized_selector,
            least_good_selector,
            good_spend_branches: branches,
            good_spend_definition_fingerprint: expected_good_spend_fingerprint(),
            production_host_verification_green: true,
            evaluation_error: None,
        }
    }

    #[test]
    fn q18_schedule_gate_rejects_stale_query_count() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_live_schedule_gate(&loaded, true);

        loaded.soundness["candidate"]["query_count"] = Value::from(16);
        assert_live_schedule_gate(&loaded, false);
    }

    #[test]
    fn q18_schedule_gate_rejects_tampered_batch_work_bits() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_live_schedule_gate(&loaded, true);

        let expected =
            u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_BATCH_GRINDING_BITS);
        loaded.soundness["candidate"]["batch_work_bits"] = Value::from(expected + 1);
        assert_live_schedule_gate(&loaded, false);
    }

    #[test]
    fn q18_schedule_gate_rejects_tampered_fold_work_bits() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_live_schedule_gate(&loaded, true);

        let mut tampered =
            aspis_core::state_only_prefix::STATE_ONLY_SPEND_FOLD_GRINDING_BITS.map(u64::from);
        tampered[2] += 1;
        loaded.soundness["candidate"]["fold_work_bits"] = json!(tampered);
        assert_live_schedule_gate(&loaded, false);
    }

    #[test]
    fn q18_schedule_gate_rejects_tampered_final_work_bits() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_live_schedule_gate(&loaded, true);

        let expected = u64::from(aspis_core::state_only_prefix::STATE_ONLY_SPEND_GRINDING_BITS);
        loaded.soundness["candidate"]["final_work_bits"] = Value::from(expected + 1);
        assert_live_schedule_gate(&loaded, false);
    }

    #[test]
    fn q18_reconstruction_gate_rejects_changed_named_term() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_reconstruction_gate(&loaded, true);

        loaded.soundness["soundness"]["terms_bits"][7]["bits"] =
            Value::from(112.396_837_317_778_39 + 0.01);
        assert_reconstruction_gate(&loaded, false);
    }

    #[test]
    fn q18_reconstruction_gate_rejects_selector_scope_drift() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_reconstruction_gate(&loaded, true);

        loaded.soundness["soundness"]["terms_bits"][0]["selector_scope"] =
            Value::String("selector_dependent_final_query".to_string());
        assert_reconstruction_gate(&loaded, false);

        let mut loaded = live_q18_schedule_artifacts();
        loaded.soundness["selector_scope_proof"]["definition_fingerprint"] =
            Value::String("00".repeat(32));
        assert_reconstruction_gate(&loaded, false);
    }

    #[test]
    fn q18_reconstruction_gate_rejects_changed_derived_floor() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_reconstruction_gate(&loaded, true);

        loaded.soundness["soundness"]["coarse_whole_ledger_times_three_bits"] = Value::from(100.8);
        assert_reconstruction_gate(&loaded, false);
    }

    #[test]
    fn q18_reconstruction_gate_rejects_changed_liveness_value() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_reconstruction_gate(&loaded, true);

        loaded.soundness["liveness"]["beta_per_attempt"] = Value::from(0.02);
        assert_reconstruction_gate(&loaded, false);
    }

    #[test]
    fn q18_reconstruction_gate_rejects_changed_epro_inventory() {
        let mut loaded = live_q18_schedule_artifacts();
        assert_reconstruction_gate(&loaded, true);

        loaded.soundness["epro"]["total_c"] = Value::from(969_994);
        assert_reconstruction_gate(&loaded, false);
    }

    #[test]
    fn current_artifacts_evaluate_to_their_mined_or_unmined_status() {
        let loaded = loaded_artifacts();
        let currently_unmined = bool_at(&loaded.acceptance, "/proof_unmined") == Some(true)
            || bool_at(&loaded.mutation, "/proof_unmined") == Some(true);
        let report = evaluate_loaded(loaded);
        if currently_unmined {
            assert!(!report.released);
            assert_eq!(report.status, "blocked_fail_closed");
            assert!(!gate(&report, "proof_is_mined").passed);
            assert!(report.failed_gates.contains(&"proof_is_mined"));
        } else {
            assert!(report.released, "failed gates: {:?}", report.failed_gates);
            assert_eq!(report.status, "released_all_required_gates_green");
            assert!(report.failed_gates.is_empty());
            assert!(report.gates.iter().all(|gate| gate.passed));
        }
        assert_eq!(report.source_artifacts.len(), 11);
        assert!(report
            .source_artifacts
            .iter()
            .any(|source| source.label == "production_statement"));
    }

    #[test]
    fn production_feature_alias_is_exact_and_fails_closed_if_incomplete() {
        let manifest = fs::read_to_string(workspace_root().join(PROGRAM_MANIFEST_PATH)).unwrap();
        assert!(spend_program_defaults_match(&manifest).2);

        for feature in SPEND_PRODUCTION_ALIAS_FEATURES {
            let manifest_line = format!("    \"{feature}\",\n");
            assert!(manifest.contains(&manifest_line));
            let tampered = manifest.replace(&manifest_line, "");
            assert!(!spend_program_defaults_match(&tampered).2);
        }
    }

    #[test]
    fn an_unmined_classification_can_never_release() {
        let mut loaded = loaded_artifacts();
        loaded.acceptance["proof_unmined"] = Value::Bool(true);
        loaded.mutation["proof_unmined"] = Value::Bool(true);
        loaded.acceptance["production_api_accepted_mined_sbf"] = Value::Bool(true);
        loaded.mutation["production_only_mined_override_exercised"] = Value::Bool(true);
        let report = evaluate_loaded(loaded);
        assert!(!report.released);
        assert!(!gate(&report, "proof_is_mined").passed);
        assert!(!gate(&report, "production_host_and_sbf_tag59_accepted").passed);
    }

    #[test]
    fn actual_proof_bytes_are_part_of_the_identity_gate() {
        let mut loaded = loaded_artifacts();
        let sha256 = loaded.actual_proof_sha256.clone();
        let bytes = loaded.actual_proof_bytes;
        loaded.acceptance["proof_sha256"] = Value::String(sha256.clone());
        loaded.mutation["proof_sha256"] = Value::String(sha256.clone());
        loaded.acceptance["proof_bytes"] = Value::from(bytes);
        loaded.mutation["proof_bytes"] = Value::from(bytes);
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "production_proof_identity_matches"
            )
            .passed
        );

        let mut path_mismatch = loaded.clone();
        path_mismatch.mutation["proof_path"] =
            Value::String("results/spend/proofs/different.bin".to_string());
        assert!(
            !gate(
                &evaluate_loaded(path_mismatch),
                "production_proof_identity_matches"
            )
            .passed
        );

        loaded.actual_proof_sha256 = "00".repeat(32);
        assert!(
            !gate(
                &evaluate_loaded(loaded),
                "production_proof_identity_matches"
            )
            .passed
        );
    }

    #[test]
    fn exact_statement_sidecar_identity_is_required() {
        let loaded = loaded_artifacts();
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "production_statement_identity_matches"
            )
            .passed
        );

        let mut path_mismatch = loaded.clone();
        path_mismatch.mutation["statement_path"] =
            Value::String("results/spend/statements/different.json".to_string());
        assert!(
            !gate(
                &evaluate_loaded(path_mismatch),
                "production_statement_identity_matches"
            )
            .passed
        );

        let mut digest_mismatch = loaded.clone();
        digest_mismatch.mutation["canonical_public_input_digest"] = Value::String("00".repeat(32));
        assert!(
            !gate(
                &evaluate_loaded(digest_mismatch),
                "production_statement_identity_matches"
            )
            .passed
        );

        let mut implicit_fixture = loaded;
        implicit_fixture.acceptance["statement_source_override"] = Value::Bool(false);
        assert!(
            !gate(
                &evaluate_loaded(implicit_fixture),
                "production_statement_identity_matches"
            )
            .passed
        );
    }

    #[test]
    fn release_statement_path_must_be_workspace_relative_and_normal() {
        let loaded = loaded_artifacts();
        for invalid in [
            "/tmp/spend-statement.json",
            "../spend-statement.json",
            "./results/spend/spend-statement.json",
        ] {
            let mut acceptance = loaded.acceptance.clone();
            acceptance["statement_path"] = Value::String(invalid.to_string());
            let error = load_selected_statement(&workspace_root(), &acceptance).unwrap_err();
            assert!(error.to_string().contains("workspace-relative normal path"));
        }
    }

    #[test]
    fn selector_policy_chooses_the_least_good_without_requiring_all_good() {
        for (accepted, selected) in [
            ([true, true, true], Some(0)),
            ([false, true, true], Some(1)),
            ([false, false, true], Some(2)),
        ] {
            assert!(release_instance_selector_is_least_good(&selector_instance(
                accepted, selected
            )));
        }
        assert!(!release_instance_selector_is_least_good(
            &selector_instance([false, false, false], None)
        ));
        assert!(!release_instance_selector_is_least_good(
            &selector_instance([false, true, true], Some(2))
        ));
        let mut malformed = selector_instance([false, true, true], Some(1));
        malformed.good_spend_branches.swap(0, 1);
        assert!(!release_instance_selector_is_least_good(&malformed));
    }

    #[test]
    fn exact_host_and_good_replay_fail_closed_under_mutation() {
        let loaded = loaded_artifacts();
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "release_instance_production_host_verification_green"
            )
            .passed
        );
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "release_instance_serialized_selector_is_least_good_spend"
            )
            .passed
        );

        let mut host_failure = loaded.clone();
        host_failure
            .release_instance
            .production_host_verification_green = false;
        assert!(
            !gate(
                &evaluate_loaded(host_failure),
                "release_instance_production_host_verification_green"
            )
            .passed
        );

        let mut selector_failure = loaded;
        selector_failure.release_instance.serialized_selector = Some(
            selector_failure
                .release_instance
                .least_good_selector
                .unwrap()
                .wrapping_add(1)
                % 3,
        );
        assert!(
            !gate(
                &evaluate_loaded(selector_failure),
                "release_instance_serialized_selector_is_least_good_spend"
            )
            .passed
        );
    }

    #[test]
    fn corrupted_exact_proof_is_rejected_by_direct_host_replay() {
        let loaded = loaded_artifacts();
        let (_, proof_path, mut proof, _) =
            load_selected_proof(&workspace_root(), &loaded.acceptance).unwrap();
        proof[0] ^= 1;
        let (_, statement_path, statement_file) =
            load_selected_statement(&workspace_root(), &loaded.acceptance).unwrap();
        let instance = build_release_instance(
            proof_path,
            hex_sha256(&proof),
            &proof,
            statement_path,
            &statement_file,
        );
        assert!(!instance.production_host_verification_green);
        assert!(instance.evaluation_error.is_some());
        assert!(instance.good_spend_branches.is_empty());
        assert!(!release_instance_selector_is_least_good(&instance));
    }

    #[test]
    fn non_authorizing_hvzk_fixture_fields_do_not_authorize_the_instance() {
        let mut loaded = loaded_artifacts();
        loaded.hvzk["complete_public_view"]["proof_sha256_production"] =
            Value::String("00".repeat(32));
        loaded.hvzk["complete_public_view"]["proof_bytes_production"] = Value::from(0);
        loaded.hvzk["production_release"]["canonically_mined_tag65_host_sbf_kat_green"] =
            Value::Bool(false);
        let report = evaluate_loaded(loaded);
        assert!(gate(&report, "production_proof_identity_matches").passed);
        assert!(
            gate(
                &report,
                "computational_hiding_at_least_100_bits_in_declared_model"
            )
            .passed
        );
    }

    #[test]
    fn acceptance_ledger_is_recomputed_from_every_bucket() {
        let mut loaded = loaded_artifacts();
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "mined_acceptance_cu_ledger_reconciles"
            )
            .passed
        );

        let value = loaded.acceptance["ledger"]["terminal_cu"].as_u64().unwrap();
        loaded.acceptance["ledger"]["terminal_cu"] = Value::from(value + 1);
        assert!(
            !gate(
                &evaluate_loaded(loaded),
                "mined_acceptance_cu_ledger_reconciles"
            )
            .passed
        );
    }

    #[test]
    fn production_ledgers_bind_tag59_tag65_and_the_signed_increment() {
        let mut loaded = loaded_artifacts();
        let path = |marker_path: &str| {
            json!({
                "marker_path": marker_path,
                "literal_tag59_simulation_cu": 1_200_000,
                "literal_tag65_simulation_cu": 1_210_000,
                "headroom_under_1_4m_cu": 190_000,
                "ledger": {
                    "production_read_only_tag59_cu": 1_200_000,
                    "production_tag65_increment_over_tag59_cu": 10_000,
                    "production_tag65_total_cu": 1_210_000,
                    "reconciled_total_cu": 1_210_000
                }
            })
        };
        loaded.mutation["production_paths"] = Value::Array(vec![
            path("program_owned_zeroed"),
            path("canonical_system_owned_create"),
        ]);
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "production_tag65_cu_ledgers_reconcile"
            )
            .passed
        );

        loaded.mutation["production_paths"][0]["ledger"]
            ["production_tag65_increment_over_tag59_cu"] = Value::from(9_999);
        assert!(
            !gate(
                &evaluate_loaded(loaded),
                "production_tag65_cu_ledgers_reconcile"
            )
            .passed
        );
    }

    #[test]
    fn production_teeth_gate_requires_every_negative_tooth_on_every_path() {
        const GATE: &str = "production_teeth_unmined_duplicate_race_refund_domain_green";
        let loaded = loaded_artifacts();
        assert!(gate(&evaluate_loaded(loaded.clone()), GATE).passed);

        for pointer in [
            "production_unmined_tag59_rejected",
            "production_unmined_tag65_rejected",
            "production_unmined_tag65_rollback_green",
            "duplicate_rejected_without_second_mutation",
            "concurrent_exactly_one_committed",
            "refund_balance_equation_exact",
            "deployment_domain_second_pool_initialized_via_tag63",
            "deployment_domain_mismatch_rejected_exact",
            "deployment_domain_mismatch_rollback_green",
        ] {
            let mut broken = loaded.clone();
            broken.mutation["production_paths"][0][pointer] = Value::Bool(false);
            assert!(
                !gate(&evaluate_loaded(broken), GATE).passed,
                "tooth {pointer} did not bite"
            );
        }

        // A race that was never exercised on any path must fail the gate.
        let mut unexercised = loaded;
        for path in unexercised.mutation["production_paths"]
            .as_array_mut()
            .unwrap()
        {
            path["concurrent_exactly_one_committed"] = Value::Null;
        }
        assert!(!gate(&evaluate_loaded(unexercised), GATE).passed);
    }
}
