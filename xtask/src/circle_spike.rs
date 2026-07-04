use std::{fs, path::PathBuf, process::Command};

use anyhow::{anyhow, Context, Result};
use chrono::Utc;
use circle_p3_core::{
    instruction_data, mutate_serialized_proof, parse_mirror_proof, reference_parameters,
    reference_prove_scenario, reference_verify_scenario_bytes, scenario_metadata,
    summarize_proof_bytes, MutationKind, ProofSummary, ScenarioKind,
};
use serde::Serialize;
use serde_json::json;
use solana_sdk::hash::hash;
use svm_cost_model::{
    load_summary, score_profile_with_components, CostFeatures, ProfileScoreInput,
    ProfileScoreOutput, SvmLimits,
};

use crate::{
    capture_version_manifest, fri_query_soundness_model, hex_bytes, parameter_choice,
    transport_features, workspace_root, write_json,
};

#[derive(Clone, Debug, Serialize)]
struct ScenarioRecord {
    scenario: String,
    metadata: circle_p3_core::ScenarioMetadata,
    proof_path: String,
    instruction_data_path: String,
    sha256: String,
    proof_summary: ProofSummary,
    reference_accepts: bool,
    mirror_accepts: bool,
    variants: Vec<VariantRecord>,
}

#[derive(Clone, Debug, Serialize)]
struct VariantRecord {
    variant: String,
    proof_path: String,
    sha256: String,
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
    reference: circle_p3_core::ReferenceParameters,
    scenarios: Vec<ScenarioRecord>,
    divergences: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct SolanaPlausibilityReport {
    generated_at_utc: String,
    compilation_status: String,
    command: String,
    stdout_path: String,
    stderr_path: String,
    so_path: Option<String>,
    blockers: Vec<String>,
    proof_sizes: Vec<serde_json::Value>,
    projection: Option<ProfileProjection>,
}

#[derive(Clone, Debug, Serialize)]
struct ProfileProjection {
    profile: ProfileScoreInput,
    score: ProfileScoreOutput,
}

pub fn run_circle_spike() -> Result<()> {
    let root = workspace_root()?;
    let docs_dir = root.join("docs");
    let results_dir = root.join("results/circle-spike");
    let raw_dir = results_dir.join("raw");
    let raw_host_dir = raw_dir.join("host-roundtrip");
    let raw_sbf_dir = raw_dir.join("sbf");
    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&docs_dir)?;
    fs::create_dir_all(&results_dir)?;
    fs::create_dir_all(&raw_host_dir)?;
    fs::create_dir_all(&raw_sbf_dir)?;
    fs::create_dir_all(&proofs_dir)?;

    let version_manifest = capture_version_manifest()?;
    write_json(
        &results_dir.join("version_manifest.json"),
        &version_manifest,
    )?;

    let mut scenario_records = Vec::new();
    let mut divergences = Vec::new();

    for kind in ScenarioKind::ALL {
        let metadata = scenario_metadata(kind);
        let proof_bytes = reference_prove_scenario(kind)
            .with_context(|| format!("failed to generate proof for {}", kind.slug()))?;
        let proof_summary = summarize_proof_bytes(&proof_bytes)?;
        let proof_sha = hex_bytes(&hash(&proof_bytes).to_bytes());
        let proof_path = proofs_dir.join(format!("{}.postcard", kind.slug()));
        fs::write(&proof_path, &proof_bytes)?;
        fs::write(
            raw_host_dir.join(format!("{}.hex", kind.slug())),
            hex_bytes(&proof_bytes),
        )?;
        let encoded_instruction = instruction_data(kind, &proof_bytes);
        let instruction_path = raw_host_dir.join(format!("{}-instruction.bin", kind.slug()));
        fs::write(&instruction_path, encoded_instruction)?;

        let reference_valid = reference_verify_scenario_bytes(kind, &proof_bytes);
        let mirror_valid = circle_p3_core::mirror_verify_scenario_bytes(kind, &proof_bytes);
        let reference_accepts = reference_valid.is_ok();
        let mirror_accepts = mirror_valid.is_ok();
        if !reference_accepts || !mirror_accepts {
            divergences.push(format!(
                "{} valid proof mismatch: reference_accepts={}, mirror_accepts={}",
                kind.slug(),
                reference_accepts,
                mirror_accepts
            ));
        }

        let mut variants = Vec::new();
        for mutation in MutationKind::ALL {
            let mutated = mutate_serialized_proof(&proof_bytes, mutation).with_context(|| {
                format!("failed to mutate {} with {}", kind.slug(), mutation.slug())
            })?;
            let variant_name = format!("{}-{}", kind.slug(), mutation.slug());
            let variant_path = proofs_dir.join(format!("{variant_name}.postcard"));
            fs::write(&variant_path, &mutated)?;
            fs::write(
                raw_host_dir.join(format!("{variant_name}.hex")),
                hex_bytes(&mutated),
            )?;

            let reference_result = reference_verify_scenario_bytes(kind, &mutated);
            let mirror_result = circle_p3_core::mirror_verify_scenario_bytes(kind, &mutated);
            let reference_error = reference_result.as_ref().err().map(ToString::to_string);
            let mirror_error = mirror_result.as_ref().err().map(ToString::to_string);
            let reference_accepts = reference_result.is_ok();
            let mirror_accepts = mirror_result.is_ok();
            let matched = !reference_accepts && !mirror_accepts;
            if !matched {
                divergences.push(format!(
                    "{} mutation {} mismatch: reference_accepts={}, mirror_accepts={}",
                    kind.slug(),
                    mutation.slug(),
                    reference_accepts,
                    mirror_accepts
                ));
            }
            variants.push(VariantRecord {
                variant: mutation.slug().to_string(),
                proof_path: relative(&root, &variant_path),
                sha256: hex_bytes(&hash(&mutated).to_bytes()),
                reference_accepts,
                mirror_accepts,
                expectation: "reject",
                matched,
                reference_error,
                mirror_error,
            });
        }

        let parsed = parse_mirror_proof(&proof_bytes)?;
        write_json(
            &raw_host_dir.join(format!("{}-structure.json", kind.slug())),
            &json!({
                "scenario": kind.slug(),
                "metadata": metadata,
                "summary": proof_summary,
                "parsed": parsed,
            }),
        )?;

        scenario_records.push(ScenarioRecord {
            scenario: kind.slug().to_string(),
            metadata,
            proof_path: relative(&root, &proof_path),
            instruction_data_path: relative(&root, &instruction_path),
            sha256: proof_sha,
            proof_summary,
            reference_accepts,
            mirror_accepts,
            variants,
        });
    }

    let host_report = HostRoundtripReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        reference: reference_parameters(),
        scenarios: scenario_records.clone(),
        divergences: divergences.clone(),
    };
    write_json(&raw_dir.join("host-roundtrip.json"), &host_report)?;
    fs::write(
        results_dir.join("host-roundtrip.md"),
        render_host_roundtrip_markdown(&host_report),
    )?;

    if !divergences.is_empty() {
        fs::write(
            docs_dir.join("circle-spike-gate.md"),
            render_gate_markdown(
                "RED",
                &host_report,
                None,
                &[
                    "Host roundtrip diverged between the reference verifier and the mirror verifier."
                        .to_string(),
                ],
            ),
        )?;
        return Err(anyhow!(
            "host roundtrip divergence detected; stopping before Solana plausibility"
        ));
    }

    let solana_report = run_solana_plausibility(&root, &raw_sbf_dir, &scenario_records)?;
    write_json(&raw_dir.join("solana-plausibility.json"), &solana_report)?;
    fs::write(
        results_dir.join("solana-plausibility.md"),
        render_solana_markdown(&solana_report),
    )?;

    let gate = if solana_report.compilation_status == "full"
        && solana_report
            .projection
            .as_ref()
            .is_some_and(|projection| projection.score.feasible)
    {
        "GREEN"
    } else {
        "AMBER"
    };
    let mut blockers = solana_report.blockers.clone();
    if solana_report
        .proof_sizes
        .iter()
        .any(|entry| entry["exceeds_tx_limit"].as_bool().unwrap_or(false))
    {
        blockers.push(
            "Proof bytes exceed the 1232-byte transaction limit and require staged upload."
                .to_string(),
        );
    }
    if let Some(projection) = &solana_report.projection {
        if !projection.score.feasible {
            blockers.extend(projection.score.feasibility_reasons.clone());
        }
    }
    fs::write(
        docs_dir.join("circle-spike-gate.md"),
        render_gate_markdown(gate, &host_report, Some(&solana_report), &blockers),
    )?;

    Ok(())
}

fn run_solana_plausibility(
    root: &PathBuf,
    raw_sbf_dir: &PathBuf,
    scenarios: &[ScenarioRecord],
) -> Result<SolanaPlausibilityReport> {
    let command = "cargo-build-sbf --manifest-path programs/circle-p3-verifier/Cargo.toml --sbf-out-dir target/circle-p3-sbf";
    let output = Command::new("cargo-build-sbf")
        .args([
            "--manifest-path",
            "programs/circle-p3-verifier/Cargo.toml",
            "--sbf-out-dir",
            "target/circle-p3-sbf",
        ])
        .current_dir(root)
        .output()
        .context("failed to run cargo-build-sbf for circle-p3-verifier")?;
    let stdout_path = raw_sbf_dir.join("build.stdout");
    let stderr_path = raw_sbf_dir.join("build.stderr");
    fs::write(&stdout_path, &output.stdout)?;
    fs::write(&stderr_path, &output.stderr)?;

    let blockers = extract_blockers(&output.stderr);
    let compilation_status = if output.status.success() {
        "full"
    } else {
        "failed"
    }
    .to_string();
    let so_path = root
        .join("target/circle-p3-sbf/deploy/circle_p3_verifier.so")
        .canonicalize()
        .ok()
        .map(|path| path.display().to_string());

    let proof_sizes = scenarios
        .iter()
        .map(|scenario| {
            let proof_bytes = scenario.proof_summary.proof_bytes as u64;
            let tx_limit = 1_232_u64;
            let conservative_chunk_size = 512_u64;
            json!({
                "scenario": scenario.scenario,
                "proof_bytes": proof_bytes,
                "tx_limit_bytes": tx_limit,
                "exceeds_tx_limit": proof_bytes > tx_limit,
                "min_tx_count_at_raw_limit": proof_bytes.div_ceil(tx_limit),
                "estimated_upload_chunks_512b": proof_bytes.div_ceil(conservative_chunk_size),
            })
        })
        .collect::<Vec<_>>();

    let projection = project_cost(scenarios)?;

    Ok(SolanaPlausibilityReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        compilation_status,
        command: command.to_string(),
        stdout_path: relative(root, &stdout_path),
        stderr_path: relative(root, &stderr_path),
        so_path,
        blockers,
        proof_sizes,
        projection,
    })
}

fn project_cost(scenarios: &[ScenarioRecord]) -> Result<Option<ProfileProjection>> {
    let summary_path = workspace_root()?.join("phase1_results/summary.json");
    if !summary_path.exists() {
        return Ok(None);
    }
    let phase1 = load_summary(&summary_path)?;
    let limits = SvmLimits::default();
    let largest = scenarios
        .iter()
        .max_by_key(|scenario| scenario.proof_summary.proof_bytes)
        .ok_or_else(|| anyhow!("missing scenarios for projection"))?;
    let queries = largest.proof_summary.fri_query_count as u64;
    let merkle_levels = largest.proof_summary.total_merkle_siblings as u64;
    let merkle_paths = (largest.proof_summary.total_input_openings
        + largest.proof_summary.fri_query_count
        + largest.proof_summary.fri_query_count * largest.proof_summary.fri_commit_phase_rounds)
        as u64;
    let proof_bytes = largest.proof_summary.proof_bytes as u64;
    let chunk_size = 512_u64;
    let transport = transport_features(proof_bytes, chunk_size);
    let sha_calls = merkle_levels + queries + transport.sha_calls + 4;
    let sha_bytes = merkle_levels * 64 + proof_bytes + 32 * sha_calls + transport.sha_bytes;
    let field_add_sub_ops = queries
        * (largest.proof_summary.trace_local_width as u64
            + largest.proof_summary.trace_next_width as u64
            + largest.proof_summary.quotient_chunk_count as u64 * 12);
    let field_mul_ops = queries * (largest.proof_summary.quotient_chunk_count as u64 * 6 + 20)
        + largest.proof_summary.lambda_count as u64 * 4;
    let field_inv_ops = queries * 3 + largest.proof_summary.quotient_chunk_count as u64;
    let extension_mul_ops = queries
        * ((largest.proof_summary.quotient_chunk_count as u64
            + largest.proof_summary.total_commit_phase_siblings as u64 / queries.max(1))
            * 3
            + 16);
    let heap_frame_bytes_requested = 131_072_u64;

    let profile = ProfileScoreInput {
        name: "circle-p3-largest-proof-projection".to_string(),
        protocol_family: Some("Circle".to_string()),
        features: CostFeatures {
            sha_calls,
            sha_bytes,
            merkle_paths,
            merkle_levels,
            proof_bytes,
            proof_segments: proof_bytes.div_ceil(512),
            upload_bytes: proof_bytes,
            upload_chunks: transport.upload_chunks,
            heap_frame_bytes_requested,
            heap_pages_32k: heap_frame_bytes_requested.div_ceil(32 * 1024),
            ro_account_count: 2,
            rw_account_count: 1,
            account_data_bytes_read: proof_bytes + 4_096,
            account_data_bytes_written: 128,
            field_add_sub_ops,
            field_mul_ops,
            field_inv_ops,
            extension_mul_ops,
        },
        transport,
        parameter_choices: vec![
            parameter_choice(
                "proof_bytes",
                proof_bytes.to_string(),
                "Taken from the largest host-roundtrip proof emitted by the selected p3-circle reference configuration.",
                &["results/circle-spike/host-roundtrip.md"],
            ),
            parameter_choice(
                "query_count",
                queries.to_string(),
                "Literal FRI query count emitted by the reference proof.",
                &["results/circle-spike/host-roundtrip.md"],
            ),
            parameter_choice(
                "upload_chunk_bytes",
                chunk_size.to_string(),
                "Conservative staging chunk size chosen to leave room under Solana's 1232-byte transaction cap.",
                &["phase1_results/summary.json"],
            ),
        ],
        references: vec![
            "results/circle-spike/host-roundtrip.md".to_string(),
            "phase1_results/summary.json".to_string(),
        ],
        query_soundness_model: Some(fri_query_soundness_model(
            queries,
            1,
            8,
            100.0,
            &[
                "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/uni-stark/tests/fib_air.rs",
            ],
            &[
                "Soundness model uses the literal p3-circle test configuration selected for Phase 2.",
            ],
        )),
        notes: vec![
            "Field-operation counts are estimated proxies derived from proof structure, not dynamic counters from an executed SBF verifier.".to_string(),
            "Hash costs use the existing Phase 1 transport methodology as an approximation for a Keccak-heavy verifier path.".to_string(),
        ],
    };
    let score = score_profile_with_components(
        &phase1.model.chosen,
        phase1
            .verification_core_model
            .as_ref()
            .map(|model| &model.chosen),
        phase1.transport_model.as_ref().map(|model| &model.chosen),
        &limits,
        &profile,
    )?;
    Ok(Some(ProfileProjection { profile, score }))
}

fn extract_blockers(stderr: &[u8]) -> Vec<String> {
    let text = String::from_utf8_lossy(stderr);
    let mut blockers = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("error:")
            || trimmed.contains("stack")
            || trimmed.contains("unsupported")
            || trimmed.contains("edition2024")
            || trimmed.contains("Cargo (1.84.0")
        {
            blockers.push(trimmed.to_string());
        }
    }
    blockers.truncate(12);
    blockers
}

fn render_host_roundtrip_markdown(report: &HostRoundtripReport) -> String {
    let mut out = String::new();
    out.push_str("# Circle host roundtrip\n\n");
    out.push_str(&format!(
        "Generated: {}\n\nReference: `{}` at `{}` using {} / {}.\n\n",
        report.generated_at_utc,
        report.reference.fixture_name,
        report.reference.git_rev,
        report.reference.base_field,
        report.reference.transcript_hash
    ));
    out.push_str("## Parameters\n\n");
    out.push_str(&format!(
        "- `log_blowup={}` `log_final_poly_len={}` `max_log_arity={}` `num_queries={}` `query_pow_bits={}`\n\n",
        report.reference.fri.log_blowup,
        report.reference.fri.log_final_poly_len,
        report.reference.fri.max_log_arity,
        report.reference.fri.num_queries,
        report.reference.fri.query_proof_of_work_bits
    ));
    out.push_str("## Results\n\n");
    for scenario in &report.scenarios {
        out.push_str(&format!("### {}\n\n", scenario.metadata.name));
        out.push_str(&format!(
            "- Trace rows: `{}` width: `{}` constraints: `{}` public values: `{}` max degree: `{}`\n",
            scenario.metadata.trace_rows,
            scenario.metadata.trace_width,
            scenario.metadata.constraint_count,
            scenario.metadata.public_value_count,
            scenario.metadata.max_constraint_degree
        ));
        out.push_str(&format!(
            "- Proof bytes: `{}` sha256: `{}`\n",
            scenario.proof_summary.proof_bytes, scenario.sha256
        ));
        out.push_str(&format!(
            "- Structure: degree_bits=`{}` quotient_chunks=`{}` fri_queries=`{}` fri_rounds=`{}` total_merkle_siblings=`{}`\n",
            scenario.proof_summary.degree_bits,
            scenario.proof_summary.quotient_chunk_count,
            scenario.proof_summary.fri_query_count,
            scenario.proof_summary.fri_commit_phase_rounds,
            scenario.proof_summary.total_merkle_siblings
        ));
        out.push_str(&format!(
            "- Valid proof: reference=`{}` mirror=`{}`\n",
            verdict(scenario.reference_accepts),
            verdict(scenario.mirror_accepts)
        ));
        out.push_str("- Mutations:\n");
        for variant in &scenario.variants {
            out.push_str(&format!(
                "  - `{}` reference=`{}` mirror=`{}` matched=`{}`\n",
                variant.variant,
                verdict(variant.reference_accepts),
                verdict(variant.mirror_accepts),
                variant.matched
            ));
        }
        out.push('\n');
    }
    if report.divergences.is_empty() {
        out.push_str("## Divergences\n\nNone.\n");
    } else {
        out.push_str("## Divergences\n\n");
        for divergence in &report.divergences {
            out.push_str(&format!("- {}\n", divergence));
        }
    }
    out
}

fn render_solana_markdown(report: &SolanaPlausibilityReport) -> String {
    let mut out = String::new();
    out.push_str("# Circle Solana plausibility\n\n");
    out.push_str(&format!(
        "Generated: {}\n\nCompilation status: `{}`.\n\n",
        report.generated_at_utc, report.compilation_status
    ));
    out.push_str(&format!("- Command: `{}`\n", report.command));
    out.push_str(&format!("- Stdout: `{}`\n", report.stdout_path));
    out.push_str(&format!("- Stderr: `{}`\n", report.stderr_path));
    if let Some(so_path) = &report.so_path {
        out.push_str(&format!("- SBF artifact: `{}`\n", so_path));
    }
    out.push('\n');

    out.push_str("## Proof sizes\n\n");
    for entry in &report.proof_sizes {
        out.push_str(&format!(
            "- `{}` proof_bytes=`{}` exceeds_tx_limit=`{}` min_tx_count=`{}` upload_chunks_512b=`{}`\n",
            entry["scenario"].as_str().unwrap_or("unknown"),
            entry["proof_bytes"].as_u64().unwrap_or_default(),
            entry["exceeds_tx_limit"].as_bool().unwrap_or(false),
            entry["min_tx_count_at_raw_limit"].as_u64().unwrap_or_default(),
            entry["estimated_upload_chunks_512b"].as_u64().unwrap_or_default(),
        ));
    }
    out.push('\n');

    if let Some(projection) = &report.projection {
        out.push_str("## Cost projection\n\n");
        out.push_str(&format!(
            "- Predicted CU: `{:.0}` feasible=`{}` budget_fraction=`{:.3}` transport_pressure=`{:.3}`\n",
            projection.score.predicted_cu,
            projection.score.feasible,
            projection.score.cu_budget_fraction,
            projection.score.proof_transport_pressure
        ));
        if let Some(core) = projection.score.verification_core_cu {
            out.push_str(&format!("- Verification core CU: `{:.0}`\n", core));
        }
        if let Some(transport) = projection.score.transport_overhead_cu {
            out.push_str(&format!("- Transport overhead CU: `{:.0}`\n", transport));
        }
        if let Some(soundness) = &projection.score.query_soundness {
            out.push_str(&format!(
                "- Query soundness lower bound: `{:.2}` bits target=`{:.2}` meets_target=`{}`\n",
                soundness.lower_bits, soundness.target_bits, soundness.meets_target
            ));
        }
        if !projection.score.feasibility_reasons.is_empty() {
            out.push_str("- Feasibility reasons:\n");
            for reason in &projection.score.feasibility_reasons {
                out.push_str(&format!("  - {}\n", reason));
            }
        }
        out.push('\n');
    }

    if report.blockers.is_empty() {
        out.push_str("## Blockers\n\nNone observed during `cargo-build-sbf`.\n");
    } else {
        out.push_str("## Blockers\n\n");
        for blocker in &report.blockers {
            out.push_str(&format!("- {}\n", blocker));
        }
    }
    out
}

fn render_gate_markdown(
    gate: &str,
    host: &HostRoundtripReport,
    solana: Option<&SolanaPlausibilityReport>,
    blockers: &[String],
) -> String {
    let mut out = String::new();
    out.push_str("# Circle spike gate\n\n");
    out.push_str(&format!("## {}\n\n", gate));
    out.push_str("### Evidence\n\n");
    out.push_str(&format!(
        "- Host roundtrip scenarios: `{}` divergences: `{}`\n",
        host.scenarios.len(),
        host.divergences.len()
    ));
    if let Some(solana) = solana {
        out.push_str(&format!(
            "- Solana compilation status: `{}`\n",
            solana.compilation_status
        ));
        if let Some(projection) = &solana.projection {
            out.push_str(&format!(
                "- Projected CU: `{:.0}` feasible=`{}`\n",
                projection.score.predicted_cu, projection.score.feasible
            ));
        }
    }
    out.push('\n');
    if blockers.is_empty() {
        out.push_str("### Blockers\n\nNone.\n");
    } else {
        out.push_str("### Blockers\n\n");
        for blocker in blockers {
            out.push_str(&format!("- {}\n", blocker));
        }
    }
    out.push('\n');
    out.push_str("### Recommendation\n\n");
    match gate {
        "GREEN" => out.push_str("Continue to a full Solana port.\n"),
        "AMBER" => out.push_str("Keep the host result, then evaluate the listed Solana blockers before committing to a full port.\n"),
        _ => out.push_str("Do not continue in this shape; treat the divergence or structural infeasibility as the finding.\n"),
    }
    out
}

fn relative(root: &PathBuf, path: &PathBuf) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn verdict(accepts: bool) -> &'static str {
    if accepts {
        "accept"
    } else {
        "reject"
    }
}
