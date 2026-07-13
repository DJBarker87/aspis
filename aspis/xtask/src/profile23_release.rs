use std::{
    fs,
    path::{Component, Path},
    process::Command,
};

use anyhow::{bail, ensure, Context, Result};
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::profile23_statement::{
    load_profile23_statement_file, profile23_hex, profile23_recorded_path, Profile23StatementFile,
};

const CU_LIMIT: u64 = 1_400_000;
const MIN_SECURITY_BITS: f64 = 100.0;

const ACCEPTANCE_PATH: &str = "results/stage2/atomic_state_only_profile23_acceptance.json";
const MUTATION_PATH: &str = "results/stage2/atomic_state_only_profile23_mutation.json";
const PRODUCTION_ACCEPTANCE_PATH: &str =
    "results/stage2/atomic_state_only_profile23_acceptance_production_mined.json";
const PRODUCTION_MUTATION_PATH: &str =
    "results/stage2/atomic_state_only_profile23_mutation_production_mined.json";
const SOUNDNESS_PATH: &str = "results/stage2/profile23_d_after_g_soundness_epro.json";
const COMPLETE_GOOD_PATH: &str = "results/stage2/profile23_complete_good_product.json";
const HVZK_PATH: &str = "results/stage2/profile23_computational_hvzk_closure.json";
const PROGRAM_MANIFEST_PATH: &str = "programs/aspis-verifier/Cargo.toml";
const WORKSPACE_MANIFEST_PATH: &str = "Cargo.toml";
const XTASK_MANIFEST_PATH: &str = "xtask/Cargo.toml";
const DEFAULT_SBF_PATH: &str = "target/deploy/aspis_verifier.so";
const PRODUCTION_FORBIDDEN_FEATURES: [&str; 11] = [
    "diagnostic-unmined-mutation",
    "diagnostic-unmined-profile21-mutation",
    "diagnostic-unmined-profile22-acceptance",
    "diagnostic-unmined-profile22-mutation",
    "diagnostic-unmined-profile23-acceptance",
    "diagnostic-unmined-profile23-mutation",
    "profile20-mutation-candidate",
    "profile21-integrated-candidate",
    "profile21-mutation-candidate",
    "profile22-integrated-candidate",
    "profile22-mutation-candidate",
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
pub struct ReleaseGood23Branch {
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
    pub good23_branches: Vec<ReleaseGood23Branch>,
    pub good23_definition_fingerprint: String,
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
pub struct Profile23OneTransactionRelease {
    pub artifact: &'static str,
    pub generated_at_utc: String,
    pub command: &'static str,
    pub status: &'static str,
    pub released: bool,
    pub scope: ReleaseScope,
    pub compute_unit_limit: u64,
    pub max_literal_production_tag60_cu: Option<u64>,
    pub exact_headroom_under_1_4m_cu: Option<i64>,
    /// The selected Profile23 union ledger after the factor-40 release
    /// sensitivity. This is the primary soundness number.
    pub selected_soundness_floor_bits: Option<f64>,
    /// A deliberately coarser sensitivity that applies the Profile23-owned
    /// BCS-32 boundary count and a whole-ledger factor of three.
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
        .context("selected Profile23 acceptance artifact omitted proof_path")?;
    let relative = Path::new(acceptance_path);
    ensure!(
        !relative.is_absolute()
            && relative
                .components()
                .all(|component| { matches!(component, Component::Normal(_) | Component::CurDir) }),
        "selected Profile23 proof path must be a workspace-relative normal path: {acceptance_path}"
    );
    let workspace_root = workspace_root
        .canonicalize()
        .with_context(|| format!("canonicalize {}", workspace_root.display()))?;
    let path = workspace_root.join(relative);
    let canonical_path = path
        .canonicalize()
        .with_context(|| format!("canonicalize selected Profile23 proof {}", path.display()))?;
    ensure!(
        canonical_path.starts_with(&workspace_root),
        "selected Profile23 proof resolves outside the workspace: {}",
        canonical_path.display()
    );
    let bytes = fs::read(&canonical_path)
        .with_context(|| format!("read selected Profile23 proof {}", canonical_path.display()))?;
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
) -> Result<(SourceArtifact, String, Profile23StatementFile)> {
    let acceptance_path = str_at(acceptance, "/statement_path")
        .context("selected Profile23 acceptance artifact omitted statement_path")?;
    let relative = Path::new(acceptance_path);
    ensure!(
        !relative.is_absolute()
            && relative
                .components()
                .all(|component| matches!(component, Component::Normal(_))),
        "selected Profile23 statement path must be a workspace-relative normal path: {acceptance_path}"
    );
    let workspace_root = workspace_root
        .canonicalize()
        .with_context(|| format!("canonicalize {}", workspace_root.display()))?;
    let expected_path = workspace_root
        .join(relative)
        .canonicalize()
        .with_context(|| {
            format!(
                "canonicalize selected Profile23 statement {}",
                workspace_root.join(relative).display()
            )
        })?;
    ensure!(
        expected_path.starts_with(&workspace_root),
        "selected Profile23 statement resolves outside the workspace: {}",
        expected_path.display()
    );
    let statement_file = load_profile23_statement_file(&workspace_root, relative)?;
    ensure!(
        statement_file.path == expected_path,
        "shared Profile23 statement loader resolved a different file"
    );
    let recorded_path = profile23_recorded_path(&workspace_root, &statement_file.path);
    ensure!(
        recorded_path == acceptance_path,
        "selected Profile23 statement path is not canonical: recorded={recorded_path}, acceptance={acceptance_path}"
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

fn release_good23_branch(
    selector: usize,
    decision: &aspis_prover::state_only_good23::Profile23GoodScheduleDecision,
) -> ReleaseGood23Branch {
    ReleaseGood23Branch {
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
    statement_file: &Profile23StatementFile,
) -> ReleaseInstance {
    let mut errors = Vec::new();
    let host_result = aspis_statement::state_only_profile23::verify_atomic_state_only_profile23_v3(
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
        match aspis_core::state_only_prefix::StateOnlyProfile23Prefix::parse_from_proof(proof) {
            Ok((prefix, suffix)) if !suffix.is_empty() => Some(prefix),
            Ok(_) => {
                errors.push("Profile23 proof has no private-opening suffix".to_string());
                None
            }
            Err(error) => {
                errors.push(format!("Profile23 prefix parse failed: {error:?}"));
                None
            }
        };
    let serialized_selector = parsed_prefix.map(|prefix| prefix.query_selector);
    let mut least_good_selector = None;
    let mut good23_branches = Vec::new();

    if production_host_verification_green {
        if let Some(prefix) = parsed_prefix {
            match aspis_statement::atomic_payment_statement_digest_v3(
                &statement_file.statement,
                aspis_prover::HOST_HASH,
            ) {
                Ok(statement_digest) => {
                    match aspis_prover::state_only_good23::evaluate_profile23_query_candidates_host(
                        aspis_prover::HOST_HASH,
                        &prefix,
                        &statement_digest,
                    ) {
                        Ok(evaluation) => {
                            least_good_selector = evaluation.selected_selector;
                            good23_branches = evaluation
                                .decisions
                                .iter()
                                .enumerate()
                                .map(|(selector, decision)| {
                                    release_good23_branch(selector, decision)
                                })
                                .collect();
                        }
                        Err(error) => {
                            errors.push(format!("complete-Good23 replay failed: {error:?}"));
                        }
                    }
                }
                Err(error) => errors.push(format!("statement digest failed: {error:?}")),
            }
        }
    } else {
        errors.push("complete-Good23 replay skipped after host rejection".to_string());
    }

    ReleaseInstance {
        proof_path,
        proof_bytes: proof.len() as u64,
        proof_sha256,
        statement_path,
        statement_bytes: statement_file.bytes as u64,
        statement_sha256: statement_file.sha256.clone(),
        statement_pool_hex: profile23_hex(&statement_file.statement.pool),
        statement_sequence: statement_file.statement.sequence,
        canonical_public_input_digest: statement_file.canonical_public_input_digest.clone(),
        selector_candidates:
            aspis_core::state_only_prefix::STATE_ONLY_PROFILE23_QUERY_CANDIDATE_COUNT,
        serialized_selector,
        least_good_selector,
        good23_branches,
        good23_definition_fingerprint: expected_good23_fingerprint(),
        production_host_verification_green,
        evaluation_error: (!errors.is_empty()).then(|| errors.join("; ")),
    }
}

fn release_instance_selector_is_least_good(instance: &ReleaseInstance) -> bool {
    let candidate_count = usize::from(instance.selector_candidates);
    if candidate_count != 3
        || instance.good23_branches.len() != candidate_count
        || instance
            .good23_branches
            .iter()
            .enumerate()
            .any(|(selector, branch)| usize::from(branch.selector) != selector)
    {
        return false;
    }
    let recomputed_least_good = instance
        .good23_branches
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

fn expected_good23_fingerprint() -> String {
    let digest = aspis_prover::state_only_good23::profile23_good_schedule_definition_fingerprint(
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
        aspis_core::state_only_hiding::state_only_profile23_hiding_layout_factor_fingerprint_v3()
    )
}

fn evaluate_loaded(loaded: LoadedArtifacts) -> Profile23OneTransactionRelease {
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
        && release_instance.good23_definition_fingerprint == expected_good23_fingerprint();
    add_gate(
        &mut gates,
        "release_instance_serialized_selector_is_least_good23",
        selector_is_least_good,
        format!(
            "candidates={}, serialized={:?}, least_good={:?}, branch_acceptance={:?}, definition_fingerprint={}, expected_fingerprint={}, evaluation_error={:?}",
            release_instance.selector_candidates,
            release_instance.serialized_selector,
            release_instance.least_good_selector,
            release_instance
                .good23_branches
                .iter()
                .map(|branch| (branch.selector, branch.accepted))
                .collect::<Vec<_>>(),
            release_instance.good23_definition_fingerprint,
            expected_good23_fingerprint(),
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
        && bool_at(mutation, "/default_tag60_fail_closed_host") == Some(true);
    add_gate(
        &mut gates,
        "no_default_host_dependencies_fail_closed",
        baseline_fail_closed,
        format!(
            "tag59_no-default={:?}, tag60_no-default={:?}",
            bool_at(acceptance, "/default_tag59_fail_closed_host"),
            bool_at(mutation, "/default_tag60_fail_closed_host")
        ),
    );

    let committed_unmined_controls = bool_at(mutation, "/production_only_unmined_tag59_rejected")
        == Some(true)
        && bool_at(mutation, "/production_only_unmined_tag60_rejected") == Some(true)
        && bool_at(mutation, "/production_only_unmined_tag60_rollback_green") == Some(true)
        && bool_at(mutation, "/production_pow_bypass_exposed") == Some(false);
    add_gate(
        &mut gates,
        "production_committed_unmined_negative_controls",
        committed_unmined_controls,
        format!(
            "tag59_rejected={:?}, tag60_rejected={:?}, tag60_rollback={:?}, pow_bypass_exposed={:?}",
            bool_at(mutation, "/production_only_unmined_tag59_rejected"),
            bool_at(mutation, "/production_only_unmined_tag60_rejected"),
            bool_at(
                mutation,
                "/production_only_unmined_tag60_rollback_green"
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
        "exactly_two_production_tag60_marker_paths",
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

    let path_acceptance = production_paths.iter().all(|path| {
        bool_at(path, "/production_tag59_accepted_mined_sbf") == Some(true)
            && bool_at(path, "/production_tag60_clean_simulation_accepted") == Some(true)
    }) && bool_at(mutation, "/candidate_tag60_accepts_mined_sbf")
        == Some(true);
    add_gate(
        &mut gates,
        "production_tag60_acceptance_teeth",
        production_paths.len() == 2 && path_acceptance,
        format!(
            "candidate_accepts={:?}, all tag59/tag60 path acceptances={path_acceptance}",
            bool_at(mutation, "/candidate_tag60_accepts_mined_sbf")
        ),
    );

    let rollback_teeth = production_paths.iter().all(|path| {
        bool_at(path, "/corrupt_proof_rejected_with_transaction_rollback") == Some(true)
    });
    add_gate(
        &mut gates,
        "production_tag60_rollback_teeth",
        production_paths.len() == 2 && rollback_teeth,
        format!("all corrupt-proof transaction rollbacks={rollback_teeth}"),
    );

    let commit_teeth = production_paths.iter().all(|path| {
        all_true(
            path,
            &[
                "/committed_transition_succeeded",
                "/pool_sequence_advanced_once",
                "/pool_anchor_replaced",
                "/nullifier_marker_written",
            ],
        )
    });
    add_gate(
        &mut gates,
        "production_tag60_commit_teeth",
        production_paths.len() == 2 && commit_teeth,
        format!("all transition/pool/anchor/nullifier commit teeth={commit_teeth}"),
    );

    let duplicate_teeth = production_paths
        .iter()
        .all(|path| bool_at(path, "/duplicate_rejected_without_second_mutation") == Some(true));
    add_gate(
        &mut gates,
        "production_tag60_duplicate_teeth",
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
        "production_tag60_race_tooth",
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
                !features.iter().any(|feature| {
                    feature.as_str() == Some("diagnostic-unmined-profile23-mutation")
                })
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

    let diagnostic_mutation_paths = mutation
        .pointer("/paths")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let diagnostic_ledgers_link_to_acceptance = acceptance_literal_cu.is_some()
        && diagnostic_mutation_paths.len() == 2
        && diagnostic_mutation_paths.iter().all(|path| {
            let literal = u64_at(path, "/literal_simulation_cu");
            let bucket_sum = checked_sum_at(
                path,
                &[
                    "/ledger/transaction_setup_cu",
                    "/ledger/account_validation_cu",
                    "/ledger/statement_decode_and_digest_cu",
                    "/ledger/exact_profile23_verifier_cu",
                    "/ledger/marker_prepare_or_cpi_cu",
                    "/ledger/mutable_state_recheck_cu",
                    "/ledger/final_account_writes_cu",
                    "/ledger/post_last_marker_cu",
                ],
            );
            let expected_increment = acceptance_literal_cu.zip(literal).and_then(
                |(acceptance_tag59, diagnostic_tag61)| {
                    i64::try_from(i128::from(diagnostic_tag61) - i128::from(acceptance_tag59)).ok()
                },
            );
            literal.is_some()
                && literal == bucket_sum
                && literal == u64_at(path, "/ledger/reconciled_total_cu")
                && i64_at(path, "/headroom_under_1_4m_cu")
                    == literal.map(|cu| CU_LIMIT as i64 - cu as i64)
                && i64_at(path, "/incremental_over_tag59_cu") == expected_increment
        });
    add_gate(
        &mut gates,
        "diagnostic_mutation_ledgers_link_to_mined_acceptance",
        diagnostic_ledgers_link_to_acceptance,
        format!(
            "acceptance_tag59={acceptance_literal_cu:?}, diagnostic_path_count={}, all bucket/reconciled/headroom/increment identities={diagnostic_ledgers_link_to_acceptance}",
            diagnostic_mutation_paths.len()
        ),
    );

    let max_tag60_cu = production_paths
        .iter()
        .filter_map(|path| u64_at(path, "/literal_tag60_simulation_cu"))
        .max();
    let cu_ledgers_reconcile = production_paths.iter().all(|path| {
        let literal_tag59 = u64_at(path, "/literal_tag59_simulation_cu");
        let literal_tag60 = u64_at(path, "/literal_tag60_simulation_cu");
        let ledger_tag59 = u64_at(path, "/ledger/production_read_only_tag59_cu");
        let ledger_increment = i64_at(path, "/ledger/production_tag60_increment_over_tag59_cu");
        let expected_increment = literal_tag59
            .zip(literal_tag60)
            .and_then(|(tag59, tag60)| i64::try_from(i128::from(tag60) - i128::from(tag59)).ok());
        literal_tag59.is_some()
            && literal_tag60.is_some()
            && literal_tag59 == ledger_tag59
            && ledger_increment == expected_increment
            && literal_tag60 == u64_at(path, "/ledger/production_tag60_total_cu")
            && literal_tag60 == u64_at(path, "/ledger/reconciled_total_cu")
            && i64_at(path, "/headroom_under_1_4m_cu")
                == literal_tag60.map(|cu| CU_LIMIT as i64 - cu as i64)
    });
    add_gate(
        &mut gates,
        "production_tag60_cu_ledgers_reconcile",
        production_paths.len() == 2 && cu_ledgers_reconcile,
        format!(
            "all exact tag59/tag60/increment/reconciled/headroom identities={cu_ledgers_reconcile}"
        ),
    );
    add_gate(
        &mut gates,
        "production_tag60_under_1_4m_cu",
        max_tag60_cu.is_some_and(|cu| cu <= CU_LIMIT),
        format!("max_literal_production_tag60_cu={max_tag60_cu:?}, limit={CU_LIMIT}"),
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
        && u64_at(mutation, "/production_instruction_wire_ordinal") == Some(60)
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

    let default_features = manifest_section(&loaded.program_manifest, "features")
        .and_then(|section| manifest_assignment(section, "default"))
        .and_then(|value| manifest_string_array(&value));
    let production_alias = manifest_section(&loaded.program_manifest, "features")
        .and_then(|section| manifest_assignment(section, "profile23-production"))
        .and_then(|value| manifest_string_array(&value));
    let program_default_enabled = default_features
        .as_deref()
        .is_some_and(|features| features == ["profile23-production".to_string()])
        && production_alias
            .as_deref()
            .is_some_and(|features| features == ["profile23-mutation-candidate".to_string()]);
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
        "profile23_default_enabled_and_host_dependencies_isolated",
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
        measured_production_features.as_deref() == Some(&["profile23-production"][..]);
    add_gate(
        &mut gates,
        "production_only_kat_used_explicit_production_alias",
        explicit_alias_measured,
        format!("production_only_sbf_features={measured_production_features:?}"),
    );

    let mut expected_forbidden_unions = PRODUCTION_FORBIDDEN_FEATURES
        .iter()
        .map(|feature| format!("profile23-production+{feature}"))
        .collect::<Vec<_>>();
    expected_forbidden_unions.push("profile23-production+all-forbidden".to_string());
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
        && bool_at(complete_good, "/profile23_soundness_bookable") == Some(true)
        && bool_at(
            complete_good,
            "/liveness_bound_bookable_for_prospective_profile23",
        ) == Some(true)
        && selected_soundness.is_some_and(|bits| bits >= MIN_SECURITY_BITS)
        && coarse_soundness.is_some_and(|bits| bits >= MIN_SECURITY_BITS);
    add_gate(
        &mut gates,
        "johnson_soundness_selected_and_coarse_floors_at_least_100_bits",
        soundness_bookable,
        format!(
            "selected_floor={selected_soundness:?}, coarse_sensitivity={coarse_soundness:?}, theorem_bookable={:?}, acceptance_bookable={:?}, mutation_bookable={:?}, complete_good_bookable={:?}",
            bool_at(soundness, "/bookable"),
            bool_at(acceptance, "/soundness_bookable"),
            bool_at(mutation, "/soundness_bookable"),
            bool_at(complete_good, "/profile23_soundness_bookable")
        ),
    );

    let johnson_parameters = u64_at(soundness, "/candidate/query_count") == Some(16)
        && u64_at(soundness, "/candidate/inverse_rate") == Some(512)
        && u64_at(soundness, "/candidate/query_candidates") == Some(3)
        && u64_at(soundness, "/candidate/attempt_cap") == Some(16)
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

    let expected_good = expected_good23_fingerprint();
    let expected_layout = expected_layout_fingerprint();
    let fingerprints_match = str_at(hvzk, "/affine_closure/good23_definition_fingerprint")
        == Some(expected_good.as_str())
        && str_at(hvzk, "/affine_closure/layout_factor_fingerprint")
            == Some(expected_layout.as_str())
        && u64_at(hvzk, "/affine_closure/d_factor_identifier") == Some(0)
        && u64_at(soundness, "/candidate/d_factor") == Some(0);
    add_gate(
        &mut gates,
        "layout_and_good23_fingerprints_match_live_code",
        fingerprints_match,
        format!(
            "good expected={expected_good}, artifact={:?}; layout expected={expected_layout}, artifact={:?}; D factors=({:?},{:?})",
            str_at(hvzk, "/affine_closure/good23_definition_fingerprint"),
            str_at(hvzk, "/affine_closure/layout_factor_fingerprint"),
            u64_at(hvzk, "/affine_closure/d_factor_identifier"),
            u64_at(soundness, "/candidate/d_factor")
        ),
    );

    let cap16_bits = f64_at(hvzk, "/q3_cap16_release/rank_exhaustion_abort_bits");
    let cap16_fixed_release = all_true(
        hvzk,
        &[
            "/q3_cap16_release/independent_post_final_branches_from_common_prefix",
            "/q3_cap16_release/all_three_evaluated_before_selection",
            "/q3_cap16_release/only_selected_openings_serialized",
            "/q3_cap16_release/all_bad_attempt_retryable",
            "/q3_cap16_release/other_gate_build_errors_fatal_and_opaque",
            "/q3_cap16_release/abort_joint_law_witness_independent_in_epro_hybrid",
            "/q3_cap16_release/fixed_release_controller_implemented",
            "/q3_cap16_release/production_example_keeps_boundary_live_while_worker_runs",
        ],
    ) && u64_at(hvzk, "/q3_cap16_release/query_candidates") == Some(3)
        && u64_at(hvzk, "/q3_cap16_release/attempt_cap") == Some(16)
        && str_at(hvzk, "/q3_cap16_release/selection_rule") == Some("least Good23 selector")
        && cap16_bits.is_some_and(|bits| bits >= MIN_SECURITY_BITS)
        && all_true(
            soundness,
            &[
                "/host_first_good_release_integration/two_phase_common_attempt",
                "/host_first_good_release_integration/all_three_post_final_schedules_evaluated",
                "/host_first_good_release_integration/opening_serialization_after_selection",
                "/host_first_good_release_integration/distinct_profile23_public_release_type",
                "/host_first_good_release_integration/fixed_boundary_controller",
                "/host_first_good_release_integration/valid_selector_proofs_0_1_2_built_and_verified",
            ],
        );
    add_gate(
        &mut gates,
        "q3_cap16_fixed_release_gates",
        cap16_fixed_release,
        format!(
            "selectors={:?}, cap={:?}, abort_bits={cap16_bits:?}, selection={:?}",
            u64_at(hvzk, "/q3_cap16_release/query_candidates"),
            u64_at(hvzk, "/q3_cap16_release/attempt_cap"),
            str_at(hvzk, "/q3_cap16_release/selection_rule")
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
    Profile23OneTransactionRelease {
        artifact: "profile23_one_transaction_release",
        generated_at_utc: chrono::Utc::now().to_rfc3339(),
        command:
            "NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-profile23-one-transaction-release",
        status: if released {
            "released_all_required_gates_green"
        } else {
            "blocked_fail_closed"
        },
        released,
        scope: ReleaseScope {
            included: "one atomic Solana transaction that verifies the finalized Profile23 proof and commits the nullifier marker plus pool-state mutation",
            proof_account_precondition: "the transaction consumes a finalized, pre-uploaded proof account",
            excluded: [
                "proof-account creation",
                "proof-account chunk-upload transactions and their compute/fees",
            ],
        },
        compute_unit_limit: CU_LIMIT,
        max_literal_production_tag60_cu: max_tag60_cu,
        exact_headroom_under_1_4m_cu: max_tag60_cu
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
            "Historical concrete-proof fields under the static HVZK artifact's complete_public_view and production_release objects are retained only as non-authorizing regression metadata; they are not theorem assumptions and cannot authorize this release instance.",
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

pub fn evaluate(workspace_root: &Path) -> Result<Profile23OneTransactionRelease> {
    freshly_build_plain_default_sbf(workspace_root)?;
    Ok(evaluate_loaded(load_artifacts(workspace_root)?))
}

/// Re-evaluate the complete release certificate against the files currently
/// present in the workspace without rebuilding or writing anything.
///
/// The devnet preflight uses this read-only path to prove that a supplied
/// certificate is the output of the live release policy, rather than trusting
/// an arbitrary JSON document whose self-declared gates happen to be green.
pub(crate) fn evaluate_existing(workspace_root: &Path) -> Result<Profile23OneTransactionRelease> {
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

    fn gate<'a>(report: &'a Profile23OneTransactionRelease, name: &str) -> &'a ReleaseGate {
        report.gates.iter().find(|gate| gate.name == name).unwrap()
    }

    fn loaded_artifacts() -> LoadedArtifacts {
        static LOADED: OnceLock<LoadedArtifacts> = OnceLock::new();
        LOADED
            .get_or_init(|| load_artifacts(&workspace_root()).unwrap())
            .clone()
    }

    fn good_branch(selector: u8, accepted: bool) -> ReleaseGood23Branch {
        ReleaseGood23Branch {
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
            good23_branches: branches,
            good23_definition_fingerprint: expected_good23_fingerprint(),
            production_host_verification_green: true,
            evaluation_error: None,
        }
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
            assert!(report.released);
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
            Value::String("results/stage2/proofs/different.bin".to_string());
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
            Value::String("results/stage2/statements/different.json".to_string());
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
            "/tmp/profile23-statement.json",
            "../profile23-statement.json",
            "./results/stage2/profile23-statement.json",
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
        malformed.good23_branches.swap(0, 1);
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
                "release_instance_serialized_selector_is_least_good23"
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
                "release_instance_serialized_selector_is_least_good23"
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
        assert!(instance.good23_branches.is_empty());
        assert!(!release_instance_selector_is_least_good(&instance));
    }

    #[test]
    fn historical_hvzk_fixture_fields_do_not_authorize_the_instance() {
        let mut loaded = loaded_artifacts();
        loaded.hvzk["complete_public_view"]["proof_sha256_production"] =
            Value::String("00".repeat(32));
        loaded.hvzk["complete_public_view"]["proof_bytes_production"] = Value::from(0);
        loaded.hvzk["production_release"]["canonically_mined_tag60_host_sbf_kat_green"] =
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
    fn production_ledgers_bind_tag59_tag60_and_the_signed_increment() {
        let mut loaded = loaded_artifacts();
        let path = |marker_path: &str| {
            json!({
                "marker_path": marker_path,
                "literal_tag59_simulation_cu": 1_200_000,
                "literal_tag60_simulation_cu": 1_210_000,
                "headroom_under_1_4m_cu": 190_000,
                "ledger": {
                    "production_read_only_tag59_cu": 1_200_000,
                    "production_tag60_increment_over_tag59_cu": 10_000,
                    "production_tag60_total_cu": 1_210_000,
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
                "production_tag60_cu_ledgers_reconcile"
            )
            .passed
        );

        loaded.mutation["production_paths"][0]["ledger"]
            ["production_tag60_increment_over_tag59_cu"] = Value::from(9_999);
        assert!(
            !gate(
                &evaluate_loaded(loaded),
                "production_tag60_cu_ledgers_reconcile"
            )
            .passed
        );
    }

    #[test]
    fn diagnostic_mutation_increment_is_bound_to_the_acceptance_tag59_total() {
        let mut loaded = loaded_artifacts();
        assert!(
            gate(
                &evaluate_loaded(loaded.clone()),
                "diagnostic_mutation_ledgers_link_to_mined_acceptance"
            )
            .passed
        );

        let increment = loaded.mutation["paths"][0]["incremental_over_tag59_cu"]
            .as_i64()
            .unwrap();
        loaded.mutation["paths"][0]["incremental_over_tag59_cu"] = Value::from(increment + 1);
        assert!(
            !gate(
                &evaluate_loaded(loaded),
                "diagnostic_mutation_ledgers_link_to_mined_acceptance"
            )
            .passed
        );
    }
}
