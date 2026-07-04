use std::{
    fs,
    panic::{catch_unwind, AssertUnwindSafe},
    path::Path,
};

use anyhow::{Context, Result};
use chrono::Utc;
use serde::Serialize;
use serde_json::json;
use solana_sdk::hash::hashv;
use whir_jb_host::{
    current_hash_mode, mirror_verify_scenario, mutate_raw_proof, probe_valid_scenario,
    reference_parameters, reference_verify_scenario, scenario_metadata, MirrorVerificationRecord,
    MutationKind, ProofSummary, RawProof, ScenarioConfig, ScenarioMetadata, TranscriptParity,
    VectorPattern, VerificationRecord,
};

use crate::{capture_version_manifest, hex_bytes, workspace_root, write_json};

#[derive(Clone, Debug, Serialize)]
struct AttemptRecord {
    id: String,
    config: ScenarioConfig,
    metadata: Option<ScenarioMetadata>,
    status: String,
    proof_narg_path: Option<String>,
    proof_hints_path: Option<String>,
    proof_sha256: Option<String>,
    proof_summary: Option<ProofSummary>,
    reference: Option<VerificationRecord>,
    mirror: Option<MirrorVerificationRecord>,
    transcript_parity: Option<TranscriptParity>,
    variants: Vec<VariantRecord>,
    error: Option<String>,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct VariantRecord {
    variant: String,
    proof_narg_path: Option<String>,
    proof_hints_path: Option<String>,
    proof_sha256: Option<String>,
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
    reference: whir_jb_host::ReferenceParameters,
    field_selection: String,
    notes: Vec<String>,
    attempts: Vec<AttemptRecord>,
    divergences: Vec<String>,
}

pub fn run_whir_jb_parity() -> Result<()> {
    let root = workspace_root()?;
    let results_dir = root.join("results/whir-jb-spike");
    let raw_dir = results_dir.join("raw");
    let raw_host_dir = raw_dir.join("host-roundtrip");
    fs::create_dir_all(&results_dir)?;
    fs::create_dir_all(&raw_dir)?;
    fs::create_dir_all(&raw_host_dir)?;

    write_json(
        &results_dir.join("version_manifest.json"),
        &capture_version_manifest()?,
    )?;

    let host_report = run_host_roundtrip(&root, &raw_host_dir)?;
    write_json(&raw_dir.join("host-roundtrip.json"), &host_report)?;
    fs::write(
        results_dir.join("host-roundtrip.md"),
        render_host_roundtrip_markdown(&host_report),
    )?;
    Ok(())
}

fn run_host_roundtrip(root: &Path, raw_host_dir: &Path) -> Result<HostRoundtripReport> {
    let mut attempts = Vec::new();
    let mut divergences = Vec::new();

    for config in host_profiles() {
        let id = config.slug();
        let attempt_dir = raw_host_dir.join(&id);
        fs::create_dir_all(&attempt_dir)?;
        write_json(&attempt_dir.join("config.json"), &config)?;

        let run = catch_unwind(AssertUnwindSafe(|| probe_valid_scenario(&config)));
        match run {
            Ok(Ok(probe)) => {
                let metadata = probe.metadata.clone();
                let proof_summary = probe.proof_summary.clone();
                let reference = probe.reference.clone();
                let mirror = probe.mirror.clone();
                let transcript_parity = probe.transcript_parity.clone();
                let (proof_narg_path, proof_hints_path, proof_sha256) =
                    write_raw_proof(root, &attempt_dir, "valid", &probe.raw_proof)?;

                let mut variants = Vec::new();
                if !probe.transcript_parity.absorb_match
                    || !probe.transcript_parity.squeeze_match
                    || !probe.transcript_parity.ratchet_match
                    || !probe.transcript_parity.final_claim_match
                {
                    divergences.push(format!(
                        "{id} valid-proof parity mismatch: absorb={}, squeeze={}, ratchet={}, final_claim={}",
                        probe.transcript_parity.absorb_match,
                        probe.transcript_parity.squeeze_match,
                        probe.transcript_parity.ratchet_match,
                        probe.transcript_parity.final_claim_match
                    ));
                }

                for mutation in MutationKind::ALL {
                    let mutated =
                        mutate_raw_proof(&probe.raw_proof, mutation).with_context(|| {
                            format!("failed to mutate {id} with {}", mutation.slug())
                        })?;
                    let (variant_narg_path, variant_hints_path, variant_sha256) =
                        write_raw_proof(root, &attempt_dir, mutation.slug(), &mutated)?;
                    let reference_result = reference_verify_scenario(&config, &mutated);
                    let mirror_result = mirror_verify_scenario(&config, &mutated);
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
                        proof_narg_path: Some(variant_narg_path),
                        proof_hints_path: Some(variant_hints_path),
                        proof_sha256: Some(variant_sha256),
                        reference_accepts,
                        mirror_accepts,
                        expectation: "reject",
                        matched,
                        reference_error: reference_result.err().map(|err| err.to_string()),
                        mirror_error: mirror_result.err().map(|err| err.to_string()),
                    });
                }

                write_json(
                    &attempt_dir.join("result.json"),
                    &json!({
                        "id": id,
                        "config": &config,
                        "metadata": &metadata,
                        "proof_summary": &proof_summary,
                        "reference": &reference,
                        "mirror": &mirror,
                        "transcript_parity": &transcript_parity,
                        "variants": &variants,
                    }),
                )?;

                attempts.push(AttemptRecord {
                    id,
                    config,
                    metadata: Some(metadata),
                    status: "ok".to_string(),
                    proof_narg_path: Some(proof_narg_path),
                    proof_hints_path: Some(proof_hints_path),
                    proof_sha256: Some(proof_sha256),
                    proof_summary: Some(proof_summary),
                    reference: Some(reference),
                    mirror: Some(mirror),
                    transcript_parity: Some(transcript_parity),
                    variants,
                    error: None,
                    notes: vec![
                        "Proof artifacts are the exact upstream `narg_string` and `hints` byte streams. Upstream does not define a canonical outer proof-file serialization.".to_string(),
                        "Mirror query indices are reconstructed from verified IRS evaluation points and the pinned upstream evaluation-domain map; no alternate schedule is introduced.".to_string(),
                    ],
                });
            }
            Ok(Err(err)) => {
                let metadata = scenario_metadata(&config).ok();
                attempts.push(AttemptRecord {
                    id,
                    config,
                    metadata,
                    status: "failed".to_string(),
                    proof_narg_path: None,
                    proof_hints_path: None,
                    proof_sha256: None,
                    proof_summary: None,
                    reference: None,
                    mirror: None,
                    transcript_parity: None,
                    variants: Vec::new(),
                    error: Some(err.to_string()),
                    notes: Vec::new(),
                });
            }
            Err(payload) => {
                let metadata = scenario_metadata(&config).ok();
                attempts.push(AttemptRecord {
                    id,
                    config,
                    metadata,
                    status: "panic".to_string(),
                    proof_narg_path: None,
                    proof_hints_path: None,
                    proof_sha256: None,
                    proof_summary: None,
                    reference: None,
                    mirror: None,
                    transcript_parity: None,
                    variants: Vec::new(),
                    error: Some(panic_payload(payload)),
                    notes: vec![
                        "Prove or verify path panicked before host parity completed.".to_string(),
                    ],
                });
            }
        }
    }

    Ok(HostRoundtripReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo run --release -p xtask -- whir-jb-parity".to_string(),
        reference: reference_parameters(),
        field_selection: "Goldilocks3 + Johnson-bound WHIR is the frozen exact-upstream target for this parity phase.".to_string(),
        notes: vec![
            format!(
                "Current upstream Merkle/PoW hash mode observed through the host crate: {}.",
                current_hash_mode()
            ),
            "Reference and mirror verifiers both operate directly on the exact upstream proof byte streams (`narg_string` and `hints`) without any wrapper-level rewriting.".to_string(),
            "Transcript parity is measured byte-for-byte over Shake128 sponge absorb/squeeze traffic, with final-claim equality checked separately.".to_string(),
        ],
        attempts,
        divergences,
    })
}

fn host_profiles() -> Vec<ScenarioConfig> {
    vec![
        ScenarioConfig {
            name: "whir-jb-goldilocks3-dev".to_string(),
            security_level: 100,
            pow_bits: 20,
            num_variables: 8,
            evaluations: 1,
            linear_constraints: 0,
            rate_bits: 4,
            initial_folding_factor: 4,
            folding_factor: 4,
            vector_pattern: VectorPattern::Affine3x5,
        },
        ScenarioConfig {
            name: "whir-jb-goldilocks3-gate".to_string(),
            security_level: 128,
            pow_bits: 20,
            num_variables: 20,
            evaluations: 1,
            linear_constraints: 0,
            rate_bits: 4,
            initial_folding_factor: 4,
            folding_factor: 4,
            vector_pattern: VectorPattern::Quadratic7,
        },
    ]
}

fn write_raw_proof(
    root: &Path,
    attempt_dir: &Path,
    stem: &str,
    proof: &RawProof,
) -> Result<(String, String, String)> {
    let narg_path = attempt_dir.join(format!("{stem}.narg.bin"));
    let hints_path = attempt_dir.join(format!("{stem}.hints.bin"));
    fs::write(&narg_path, &proof.narg_string)?;
    fs::write(&hints_path, &proof.hints)?;
    let proof_hash = hex_bytes(&hashv(&[&proof.narg_string, &proof.hints]).to_bytes());
    Ok((
        relative(root, &narg_path),
        relative(root, &hints_path),
        proof_hash,
    ))
}

fn render_host_roundtrip_markdown(report: &HostRoundtripReport) -> String {
    let mut out = String::new();
    out.push_str("# WHIR-JB Host Roundtrip\n\n");
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
    out.push_str("| id | status | achieved bits | d | rate | proof bytes | ref hashes | mirror hashes | parity | variants |\n");
    out.push_str("| --- | --- | ---: | ---: | --- | ---: | ---: | ---: | --- | --- |\n");
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
            .map(|record| record.metrics.hash_count.to_string())
            .unwrap_or_else(|| "-".to_string());
        let mirror_hashes = attempt
            .mirror
            .as_ref()
            .map(|record| record.metrics.hash_count.to_string())
            .unwrap_or_else(|| "-".to_string());
        let parity = attempt
            .transcript_parity
            .as_ref()
            .map(|parity| {
                format!(
                    "a={} s={} r={} f={}",
                    yes_no(parity.absorb_match),
                    yes_no(parity.squeeze_match),
                    yes_no(parity.ratchet_match),
                    yes_no(parity.final_claim_match)
                )
            })
            .unwrap_or_else(|| "-".to_string());
        let variant_summary = if attempt.variants.is_empty() {
            "-".to_string()
        } else {
            let passed = attempt
                .variants
                .iter()
                .filter(|variant| variant.matched)
                .count();
            format!("{passed}/{}", attempt.variants.len())
        };
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            attempt.id,
            attempt.status,
            achieved,
            d,
            rate,
            proof_bytes,
            ref_hashes,
            mirror_hashes,
            parity,
            variant_summary
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
    out.push_str("\n## Raw Artifacts\n\n");
    for attempt in &report.attempts {
        if let (Some(narg_path), Some(hints_path)) =
            (&attempt.proof_narg_path, &attempt.proof_hints_path)
        {
            out.push_str(&format!(
                "- `{}`: `{}` and `{}`\n",
                attempt.id, narg_path, hints_path
            ));
        }
    }
    out
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn yes_no(value: bool) -> &'static str {
    if value {
        "yes"
    } else {
        "no"
    }
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
