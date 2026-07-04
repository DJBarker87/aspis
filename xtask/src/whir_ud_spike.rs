use std::{
    fs,
    panic::{catch_unwind, AssertUnwindSafe},
    path::Path,
    process::Command,
};

use anyhow::{Context, Result};
use chrono::Utc;
use serde::Serialize;
use solana_sdk::hash::hash;
use whir_ud_host::{
    current_hash_mode, mirror_verify_scenario_bytes, mutate_serialized_proof, probe_valid_scenario,
    reference_parameters, reference_verify_scenario_bytes, scenario_metadata, MutationKind,
    ProofSummary, ScenarioConfig, ScenarioMetadata, VectorPattern, VerificationMetrics,
};

use crate::{capture_version_manifest, hex_bytes, workspace_root, write_json};

const TX_LIMIT_BYTES: u64 = 1_232;
const SHA_SYSCALL_FLOOR_CU: f64 = 148.0;

#[derive(Clone, Debug, Serialize)]
struct AttemptRecord {
    id: String,
    config: ScenarioConfig,
    metadata: Option<ScenarioMetadata>,
    status: String,
    proof_path: Option<String>,
    sha256: Option<String>,
    proof_summary: Option<ProofSummary>,
    reference: Option<VerificationMetrics>,
    mirror: Option<VerificationMetrics>,
    variants: Vec<VariantRecord>,
    error: Option<String>,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct VariantRecord {
    variant: String,
    proof_path: Option<String>,
    sha256: Option<String>,
    reference_accepts: bool,
    mirror_accepts: bool,
    expectation: &'static str,
    matched: bool,
    reference_error: Option<String>,
    mirror_error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct HostRoundtripReport {
    generated_at_utc: String,
    command: String,
    reference: whir_ud_host::ReferenceParameters,
    field_selection: String,
    notes: Vec<String>,
    attempts: Vec<AttemptRecord>,
    divergences: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct ProjectionRecord {
    rank: usize,
    attempt_id: String,
    security_target_bits: usize,
    achieved_security_bits: f64,
    num_variables: usize,
    proof_bytes: u64,
    verifier_hashes: u64,
    hash_floor_cu: f64,
    min_tx_count: u64,
    floor_margin_cu: f64,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct SbfProjectionReport {
    generated_at_utc: String,
    methodology: String,
    compilation_status: String,
    command: String,
    stdout_path: String,
    stderr_path: String,
    blockers: Vec<String>,
    ranked: Vec<ProjectionRecord>,
}

#[derive(Clone, Debug, Serialize)]
struct GateDecision {
    generated_at_utc: String,
    gate: &'static str,
    best_attempt_id: Option<String>,
    rationale: Vec<String>,
}

pub fn run_whir_ud_spike() -> Result<()> {
    let root = workspace_root()?;
    let docs_dir = root.join("docs");
    let results_dir = root.join("results/whir-ud-spike");
    let raw_dir = results_dir.join("raw");
    let raw_host_dir = raw_dir.join("host-roundtrip");
    let raw_sbf_dir = raw_dir.join("sbf");
    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&docs_dir)?;
    fs::create_dir_all(&results_dir)?;
    fs::create_dir_all(&raw_dir)?;
    fs::create_dir_all(&raw_host_dir)?;
    fs::create_dir_all(&raw_sbf_dir)?;
    fs::create_dir_all(&proofs_dir)?;

    write_json(
        &results_dir.join("version_manifest.json"),
        &capture_version_manifest()?,
    )?;

    let host_report = run_host_roundtrip(&root, &proofs_dir, &raw_host_dir)?;
    write_json(&raw_dir.join("host-roundtrip.json"), &host_report)?;
    fs::write(
        results_dir.join("host-roundtrip.md"),
        render_host_roundtrip_markdown(&host_report),
    )?;

    let projection_report = run_sbf_projection(&root, &raw_sbf_dir, &host_report)?;
    write_json(&raw_dir.join("sbf-projections.json"), &projection_report)?;
    fs::write(
        results_dir.join("sbf-projections.md"),
        render_sbf_projection_markdown(&projection_report),
    )?;

    let gate = decide_gate(&host_report, &projection_report);
    write_json(&raw_dir.join("gate.json"), &gate)?;
    fs::write(
        docs_dir.join("whir-ud-spike-gate.md"),
        render_gate_markdown(&gate, &projection_report),
    )?;

    Ok(())
}

fn run_host_roundtrip(
    root: &Path,
    proofs_dir: &Path,
    raw_host_dir: &Path,
) -> Result<HostRoundtripReport> {
    let mut attempts = Vec::new();
    let mut divergences = Vec::new();

    for config in host_matrix() {
        let id = config.slug();
        write_json(&raw_host_dir.join(format!("{id}.config.json")), &config)?;
        let run = catch_unwind(AssertUnwindSafe(|| probe_valid_scenario(&config)));
        match run {
            Ok(Ok(probe)) => {
                let proof_path = proofs_dir.join(format!("{id}.cbor"));
                fs::write(&proof_path, &probe.proof_bytes)?;
                let mut variants = Vec::new();
                for mutation in MutationKind::ALL {
                    let mutated = mutate_serialized_proof(&probe.proof_bytes, mutation)
                        .with_context(|| {
                            format!("failed to mutate {id} with {}", mutation.slug())
                        })?;
                    let variant_id = format!("{id}-{}", mutation.slug());
                    let variant_path = proofs_dir.join(format!("{variant_id}.cbor"));
                    fs::write(&variant_path, &mutated)?;
                    let reference_result = reference_verify_scenario_bytes(&config, &mutated);
                    let mirror_result = mirror_verify_scenario_bytes(&config, &mutated);
                    let reference_accepts = reference_result.is_ok();
                    let mirror_accepts = mirror_result.is_ok();
                    let matched = !reference_accepts && !mirror_accepts;
                    if !matched {
                        divergences.push(format!(
                            "{id} {} mismatch: reference_accepts={}, mirror_accepts={}",
                            mutation.slug(),
                            reference_accepts,
                            mirror_accepts
                        ));
                    }
                    variants.push(VariantRecord {
                        variant: mutation.slug().to_string(),
                        proof_path: Some(relative(root, &variant_path)),
                        sha256: Some(hex_bytes(&hash(&mutated).to_bytes())),
                        reference_accepts,
                        mirror_accepts,
                        expectation: "reject",
                        matched,
                        reference_error: reference_result.err().map(|err| err.to_string()),
                        mirror_error: mirror_result.err().map(|err| err.to_string()),
                    });
                }

                let raw_record = serde_json::json!({
                    "id": id,
                    "config": config,
                    "metadata": probe.metadata,
                    "proof_summary": probe.proof_summary,
                    "reference": probe.reference,
                    "mirror": probe.mirror,
                    "variants": variants,
                });
                write_json(&raw_host_dir.join(format!("{id}.result.json")), &raw_record)?;

                attempts.push(AttemptRecord {
                    id,
                    config,
                    metadata: Some(probe.metadata),
                    status: "ok".to_string(),
                    proof_path: Some(relative(root, &proof_path)),
                    sha256: Some(hex_bytes(&hash(&probe.proof_bytes).to_bytes())),
                    proof_summary: Some(probe.proof_summary),
                    reference: Some(probe.reference),
                    mirror: Some(probe.mirror),
                    variants,
                    error: None,
                    notes: vec![
                        "Proof bytes are the upstream `transcript::Proof` serialized with ciborium; the upstream CLI does not export a stable proof file format.".to_string(),
                        "Mutation targeting is coarse at the raw proof-stream level: early/late bytes in `hints` and `narg_string` stand in for the requested query, Merkle, commitment, and final-polynomial corruptions.".to_string(),
                    ],
                });
            }
            Ok(Err(err)) => {
                let metadata = scenario_metadata(&config).ok();
                let notes = metadata
                    .as_ref()
                    .map(|metadata| {
                        vec![format!(
                            "Static metadata: achieved security {:.2} bits, required max PoW {:.2} bits, pow cap satisfied={}.",
                            metadata.achieved_security_bits,
                            metadata.max_required_pow_bits,
                            metadata.pow_cap_satisfied
                        )]
                    })
                    .unwrap_or_default();
                attempts.push(AttemptRecord {
                    id,
                    config,
                    metadata,
                    status: "failed".to_string(),
                    proof_path: None,
                    sha256: None,
                    proof_summary: None,
                    reference: None,
                    mirror: None,
                    variants: Vec::new(),
                    error: Some(err.to_string()),
                    notes,
                });
            }
            Err(payload) => {
                let metadata = scenario_metadata(&config).ok();
                attempts.push(AttemptRecord {
                    id,
                    config,
                    metadata,
                    status: "panic".to_string(),
                    proof_path: None,
                    sha256: None,
                    proof_summary: None,
                    reference: None,
                    mirror: None,
                    variants: Vec::new(),
                    error: Some(panic_payload(payload)),
                    notes: vec![
                        "Reference prove path panicked before roundtrip completed.".to_string()
                    ],
                });
            }
        }
    }

    Ok(HostRoundtripReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo run --release -p xtask -- whir-ud-spike".to_string(),
        reference: reference_parameters(),
        field_selection: "Goldilocks2 confirmed after Phase 1: base Goldilocks source field with quadratic extension target field.".to_string(),
        notes: vec![
            format!("Current upstream Merkle/PoW hash mode observed through the host crate: {}.", current_hash_mode()),
            "The transcript duplex remains Shake128 and domain-separator hashing remains SHA3, regardless of the Blake3 Merkle/PoW setting.".to_string(),
            "Successful roundtrips use unchanged upstream proof objects at the byte level within the chosen ciborium serialization wrapper; no proof bytes are rewritten between reference verify and mirror verify.".to_string(),
        ],
        attempts,
        divergences,
    })
}

fn run_sbf_projection(
    root: &Path,
    raw_sbf_dir: &Path,
    host_report: &HostRoundtripReport,
) -> Result<SbfProjectionReport> {
    let command =
        "cargo-build-sbf --manifest-path experiments/whir-ud-sbf-solo/Cargo.toml --sbf-out-dir target/whir-ud-sbf-solo";
    let output = Command::new("cargo-build-sbf")
        .args([
            "--manifest-path",
            "experiments/whir-ud-sbf-solo/Cargo.toml",
            "--sbf-out-dir",
            "target/whir-ud-sbf-solo",
        ])
        .current_dir(root)
        .output()
        .context("failed to run cargo-build-sbf for the isolated whir-ud-sbf-solo probe")?;
    let stdout_path = raw_sbf_dir.join("build.stdout");
    let stderr_path = raw_sbf_dir.join("build.stderr");
    fs::write(&stdout_path, &output.stdout)?;
    fs::write(&stderr_path, &output.stderr)?;

    let mut ranked = host_report
        .attempts
        .iter()
        .filter(|attempt| attempt.status == "ok")
        .filter_map(|attempt| {
            let metadata = attempt.metadata.as_ref()?;
            let proof_summary = attempt.proof_summary.as_ref()?;
            let mirror = attempt.mirror.as_ref()?;
            let proof_bytes = proof_summary.transcript_bytes as u64;
            let hash_floor_cu = mirror.hash_count as f64 * SHA_SYSCALL_FLOOR_CU;
            let floor_margin_cu = 1_400_000.0 - hash_floor_cu;
            let mut notes = vec![
                "CU figure is a lower bound: hash_count * 148 CU, pretending every verifier hash were a cheap SHA syscall.".to_string(),
                "Real WHIR-UD uses Blake3 plus Shake128/SHA3 in software on SBF, so actual CU is higher.".to_string(),
            ];
            if proof_bytes > TX_LIMIT_BYTES {
                notes.push(format!(
                    "Proof is {}x over the raw transaction byte limit.",
                    ((proof_bytes as f64) / (TX_LIMIT_BYTES as f64)).ceil() as u64
                ));
            }
            Some(ProjectionRecord {
                rank: 0,
                attempt_id: attempt.id.clone(),
                security_target_bits: metadata.security_target_bits,
                achieved_security_bits: metadata.achieved_security_bits,
                num_variables: metadata.num_variables,
                proof_bytes,
                verifier_hashes: mirror.hash_count,
                hash_floor_cu,
                min_tx_count: proof_bytes.div_ceil(TX_LIMIT_BYTES),
                floor_margin_cu,
                notes,
            })
        })
        .collect::<Vec<_>>();
    ranked.sort_by(|left, right| {
        left.hash_floor_cu
            .partial_cmp(&right.hash_floor_cu)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(left.proof_bytes.cmp(&right.proof_bytes))
    });
    for (index, record) in ranked.iter_mut().enumerate() {
        record.rank = index + 1;
    }

    let blockers = extract_blockers(&String::from_utf8_lossy(&output.stderr));
    Ok(SbfProjectionReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        methodology: "Direct SBF compilation was attempted on a minimal wrapper program. Quantitative CU numbers are lower bounds only: verifier hash count multiplied by the SHA syscall floor (148 CU/hash). No Goldilocks-specific arithmetic coefficient was available, and actual WHIR-UD hashes are Blake3/Shake128/SHA3 in software, so real CU is higher than the reported floor.".to_string(),
        compilation_status: if output.status.success() {
            "full".to_string()
        } else {
            "failed".to_string()
        },
        command: command.to_string(),
        stdout_path: relative(root, &stdout_path),
        stderr_path: relative(root, &stderr_path),
        blockers,
        ranked,
    })
}

fn decide_gate(
    host_report: &HostRoundtripReport,
    projection_report: &SbfProjectionReport,
) -> GateDecision {
    let successful = host_report
        .attempts
        .iter()
        .filter(|attempt| attempt.status == "ok")
        .count();
    let best = projection_report.ranked.first();
    let highest_supported_variables = host_report
        .attempts
        .iter()
        .filter(|attempt| attempt.status == "ok")
        .filter_map(|attempt| {
            attempt
                .metadata
                .as_ref()
                .map(|metadata| metadata.num_variables)
        })
        .max()
        .unwrap_or(0);
    let best_largest_trace = projection_report
        .ranked
        .iter()
        .filter(|record| record.num_variables == highest_supported_variables)
        .min_by(|left, right| {
            left.hash_floor_cu
                .partial_cmp(&right.hash_floor_cu)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then(left.proof_bytes.cmp(&right.proof_bytes))
        });
    let selected = best_largest_trace.or(best);

    let mut rationale = Vec::new();
    if !host_report.divergences.is_empty() {
        rationale.push("Reference and mirror verification diverged on at least one valid-or-corrupted proof case.".to_string());
        return GateDecision {
            generated_at_utc: Utc::now().to_rfc3339(),
            gate: "RED",
            best_attempt_id: selected.map(|record| record.attempt_id.clone()),
            rationale,
        };
    }
    if successful == 0 {
        rationale.push(
            "No Goldilocks2 WHIR-UD configuration completed host roundtrip successfully."
                .to_string(),
        );
        return GateDecision {
            generated_at_utc: Utc::now().to_rfc3339(),
            gate: "RED",
            best_attempt_id: None,
            rationale,
        };
    }

    if projection_report.compilation_status != "full" {
        rationale.push("Direct SBF compilation failed for the wrapper program, so there is no proven compilation path yet.".to_string());
    }
    rationale.push(format!(
        "Largest successfully round-tripped trace in this sweep used 2^{} coefficients.",
        highest_supported_variables
    ));
    if let Some(best_overall) = best {
        if let Some(best_largest_trace) = best_largest_trace {
            if best_largest_trace.attempt_id != best_overall.attempt_id {
                rationale.push(format!(
                    "Smaller toy traces produce lower hash-only floors, but the gate is evaluated on the largest trace reached in the sweep: {}.",
                    best_largest_trace.attempt_id
                ));
            }
        }
    }
    if let Some(selected) = selected {
        rationale.push(format!(
            "Best hash-only lower bound is {:.0} CU for {} at 2^{} coefficients and {} bytes.",
            selected.hash_floor_cu,
            selected.attempt_id,
            selected.num_variables,
            selected.proof_bytes
        ));
        if selected.proof_bytes > TX_LIMIT_BYTES {
            rationale.push(format!(
                "Even the best measured proof needs at least {} staged transactions just to upload raw bytes.",
                selected.min_tx_count
            ));
        }
    }

    let gate = if let Some(selected) = selected {
        if projection_report.compilation_status == "full"
            && selected.hash_floor_cu < 1_200_000.0
            && selected.achieved_security_bits >= 100.0
            && selected.num_variables >= 18
        {
            "GREEN"
        } else if selected.hash_floor_cu <= 2_500_000.0 && highest_supported_variables >= 18 {
            "AMBER"
        } else {
            "RED"
        }
    } else {
        "RED"
    };

    GateDecision {
        generated_at_utc: Utc::now().to_rfc3339(),
        gate,
        best_attempt_id: selected.map(|record| record.attempt_id.clone()),
        rationale,
    }
}

fn host_matrix() -> Vec<ScenarioConfig> {
    let mut configs = Vec::new();
    let patterns = [
        VectorPattern::Ascending,
        VectorPattern::Affine3x5,
        VectorPattern::Quadratic7,
    ];
    for &security_level in &[100_usize, 128] {
        for &rate_bits in &[1_usize, 2, 4] {
            for &num_variables in &[4_usize, 8, 12] {
                let pattern_index = (security_level + rate_bits + num_variables) % patterns.len();
                configs.push(ScenarioConfig {
                    name: "whir-ud-goldilocks2".to_string(),
                    security_level,
                    pow_bits: 20,
                    num_variables,
                    evaluations: 1 + usize::from(num_variables == 8 && rate_bits == 2),
                    linear_constraints: usize::from(num_variables == 12 && security_level == 128),
                    rate_bits,
                    initial_folding_factor: 4,
                    folding_factor: 4,
                    unique_decoding: true,
                    vector_pattern: patterns[pattern_index],
                });
            }
        }
    }
    for &(security_level, rate_bits) in &[(100_usize, 1_usize), (100, 2), (128, 1), (128, 2)] {
        configs.push(ScenarioConfig {
            name: "whir-ud-goldilocks2".to_string(),
            security_level,
            pow_bits: 20,
            num_variables: 18,
            evaluations: 1,
            linear_constraints: 0,
            rate_bits,
            initial_folding_factor: 4,
            folding_factor: 4,
            unique_decoding: true,
            vector_pattern: VectorPattern::Affine3x5,
        });
    }
    configs
}

fn render_host_roundtrip_markdown(report: &HostRoundtripReport) -> String {
    let mut out = String::new();
    out.push_str("# WHIR-UD Host Roundtrip\n\n");
    out.push_str(&format!("Generated: `{}`\n\n", report.generated_at_utc));
    out.push_str(&format!(
        "Reference: `{}` at `{}`\n\n",
        report.reference.repo_url, report.reference.git_rev
    ));
    out.push_str(&format!("Field selection: {}\n\n", report.field_selection));
    out.push_str("## Notes\n\n");
    for note in &report.notes {
        out.push_str(&format!("- {}\n", note));
    }
    out.push_str("\n## Attempt Matrix\n\n");
    out.push_str("| id | status | achieved bits | d | rate | proof bytes | ref hashes | mirror hashes | notes |\n");
    out.push_str("| --- | --- | ---: | ---: | --- | ---: | ---: | ---: | --- |\n");
    for attempt in &report.attempts {
        let achieved = attempt
            .metadata
            .as_ref()
            .map(|metadata| format!("{:.2}", metadata.achieved_security_bits))
            .unwrap_or_else(|| "-".to_string());
        let d = attempt
            .metadata
            .as_ref()
            .map(|metadata| metadata.num_variables.to_string())
            .unwrap_or_else(|| "-".to_string());
        let rate = attempt
            .metadata
            .as_ref()
            .map(|metadata| metadata.rate.clone())
            .unwrap_or_else(|| "-".to_string());
        let proof_bytes = attempt
            .proof_summary
            .as_ref()
            .map(|summary| summary.transcript_bytes.to_string())
            .unwrap_or_else(|| "-".to_string());
        let ref_hashes = attempt
            .reference
            .as_ref()
            .map(|metrics| metrics.hash_count.to_string())
            .unwrap_or_else(|| "-".to_string());
        let mirror_hashes = attempt
            .mirror
            .as_ref()
            .map(|metrics| metrics.hash_count.to_string())
            .unwrap_or_else(|| "-".to_string());
        let note = attempt
            .error
            .clone()
            .or_else(|| attempt.notes.first().cloned())
            .unwrap_or_default();
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            attempt.id,
            attempt.status,
            achieved,
            d,
            rate,
            proof_bytes,
            ref_hashes,
            mirror_hashes,
            note.replace('|', "/")
        ));
    }
    out.push_str("\n## Divergences\n\n");
    if report.divergences.is_empty() {
        out.push_str("- None.\n");
    } else {
        for divergence in &report.divergences {
            out.push_str(&format!("- {}\n", divergence));
        }
    }
    out
}

fn render_sbf_projection_markdown(report: &SbfProjectionReport) -> String {
    let mut out = String::new();
    out.push_str("# WHIR-UD SBF Projections\n\n");
    out.push_str(&format!("Generated: `{}`\n\n", report.generated_at_utc));
    out.push_str(&format!(
        "Compilation status: `{}`\n\n",
        report.compilation_status
    ));
    out.push_str(&format!("Methodology: {}\n\n", report.methodology));
    out.push_str("## Ranked Candidates\n\n");
    out.push_str("| rank | id | d | proof bytes | verifier hashes | hash floor CU | floor margin vs 1.4M |\n");
    out.push_str("| ---: | --- | ---: | ---: | ---: | ---: | ---: |\n");
    for record in &report.ranked {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {:.0} | {:.0} |\n",
            record.rank,
            record.attempt_id,
            record.num_variables,
            record.proof_bytes,
            record.verifier_hashes,
            record.hash_floor_cu,
            record.floor_margin_cu
        ));
    }
    out.push_str("\n## Compilation Blockers\n\n");
    if report.blockers.is_empty() {
        out.push_str("- None captured.\n");
    } else {
        for blocker in &report.blockers {
            out.push_str(&format!("- {}\n", blocker));
        }
    }
    out
}

fn render_gate_markdown(gate: &GateDecision, projection_report: &SbfProjectionReport) -> String {
    let mut out = String::new();
    out.push_str("# WHIR-UD Spike Gate\n\n");
    out.push_str(&format!("Conclusion: **{}**\n\n", gate.gate));
    if let Some(best) = &gate.best_attempt_id {
        out.push_str(&format!(
            "Selected configuration for the gate decision: `{}`\n\n",
            best
        ));
    }
    out.push_str("## Rationale\n\n");
    for reason in &gate.rationale {
        out.push_str(&format!("- {}\n", reason));
    }
    out.push_str("\n## Projection Context\n\n");
    out.push_str(&format!(
        "- Compilation status: `{}`.\n- Raw build logs: [{}](/Users/dominic/ZK/{}) and [{}](/Users/dominic/ZK/{}).\n",
        projection_report.compilation_status,
        projection_report.stdout_path,
        projection_report.stdout_path,
        projection_report.stderr_path,
        projection_report.stderr_path,
    ));
    out
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn extract_blockers(stderr: &str) -> Vec<String> {
    let mut blockers = stderr
        .lines()
        .filter(|line| {
            let line = line.trim();
            !line.is_empty()
                && (line.contains("error:")
                    || line.contains("panicked at")
                    || line.contains("unsupported")
                    || line.contains("failed"))
        })
        .map(|line| line.trim().to_string())
        .collect::<Vec<_>>();
    blockers.truncate(12);
    blockers
}

fn panic_payload(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_string()
    }
}
