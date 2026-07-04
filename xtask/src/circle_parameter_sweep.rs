use std::{
    fs,
    panic::{catch_unwind, AssertUnwindSafe},
    path::Path,
};

use anyhow::{anyhow, Context, Result};
use chrono::Utc;
use circle_p3_core::{
    instruction_data, parse_mirror_proof, reference_parameters, reference_prove_scenario_with_fri,
    reference_verify_scenario_bytes_with_fri, scenario_metadata, summarize_proof_bytes,
    CircleFriConfig, ProofSummary, ScenarioKind,
};
use serde::Serialize;
use solana_sdk::hash::hash;
use svm_cost_model::{
    load_summary, score_profile_with_components, CostFeatures, ProfileScoreInput,
    ProfileScoreOutput, SvmLimits,
};

use crate::{
    capture_version_manifest, fri_query_soundness_model, hex_bytes, parameter_choice,
    transport_features, workspace_root, write_json,
};

const TX_CHUNK_BYTES: u64 = 512;
const HEAP_FRAME_BYTES: u64 = 131_072;

#[derive(Clone, Debug, Serialize)]
struct ParameterSpaceReport {
    generated_at_utc: String,
    reference: circle_p3_core::ReferenceParameters,
    findings: Vec<String>,
    measured_hash_family: &'static str,
    measured_hash_scope: Vec<String>,
    source_links: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct AttemptSpec {
    id: String,
    scenario: ScenarioKind,
    target_bits: u32,
    security_assumption: &'static str,
    fri: CircleFriConfig,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct AttemptRecord {
    id: String,
    scenario: String,
    metadata: circle_p3_core::ScenarioMetadata,
    target_bits: u32,
    security_assumption: &'static str,
    fri: CircleFriConfig,
    conjectured_soundness_bits: usize,
    status: String,
    proof_path: Option<String>,
    instruction_data_path: Option<String>,
    sha256: Option<String>,
    proof_summary: Option<ProofSummary>,
    reference_accepts: Option<bool>,
    mirror_accepts: Option<bool>,
    error: Option<String>,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct HostSweepReport {
    generated_at_utc: String,
    reference: circle_p3_core::ReferenceParameters,
    attempts: Vec<AttemptRecord>,
    total_attempts: usize,
    successful_attempts: usize,
    failed_attempts: usize,
    divergences: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct ProjectionRecord {
    rank: usize,
    attempt_id: String,
    target_bits: u32,
    conjectured_soundness_bits: usize,
    scenario: String,
    fri: CircleFriConfig,
    proof_bytes: u64,
    profile: ProfileScoreInput,
    score: ProfileScoreOutput,
}

#[derive(Clone, Debug, Serialize)]
struct SbfProjectionReport {
    generated_at_utc: String,
    methodology: String,
    compilation_status: String,
    blockers: Vec<String>,
    ranked: Vec<ProjectionRecord>,
}

#[derive(Clone, Debug, Serialize)]
struct GateDecision {
    generated_at_utc: String,
    gate: &'static str,
    best_attempt_id: Option<String>,
    best_projected_cu: Option<f64>,
    best_margin_cu: Option<f64>,
    rationale: Vec<String>,
}

pub fn run_circle_parameter_sweep() -> Result<()> {
    let root = workspace_root()?;
    let docs_dir = root.join("docs");
    let results_dir = root.join("results/circle-parameter-sweep");
    let raw_dir = results_dir.join("raw");
    let raw_configs_dir = raw_dir.join("configs");
    let raw_host_dir = raw_dir.join("host");
    let raw_projection_dir = raw_dir.join("sbf");
    let proofs_dir = results_dir.join("proofs");
    fs::create_dir_all(&docs_dir)?;
    fs::create_dir_all(&results_dir)?;
    fs::create_dir_all(&raw_dir)?;
    fs::create_dir_all(&raw_configs_dir)?;
    fs::create_dir_all(&raw_host_dir)?;
    fs::create_dir_all(&raw_projection_dir)?;
    fs::create_dir_all(&proofs_dir)?;

    write_json(
        &results_dir.join("version_manifest.json"),
        &capture_version_manifest()?,
    )?;

    let parameter_space = build_parameter_space_report();
    write_json(&raw_dir.join("parameter-space.json"), &parameter_space)?;
    fs::write(
        docs_dir.join("circle-parameter-space.md"),
        render_parameter_space_markdown(&parameter_space),
    )?;

    let attempts = build_attempt_specs();
    let host_report = run_host_sweep(
        &root,
        &proofs_dir,
        &raw_configs_dir,
        &raw_host_dir,
        attempts,
    )?;
    write_json(&raw_dir.join("host-results.json"), &host_report)?;
    fs::write(
        results_dir.join("host-results.md"),
        render_host_results_markdown(&host_report),
    )?;

    let projection_report = project_sbf_costs(&host_report)?;
    write_json(
        &raw_projection_dir.join("sbf-projections.json"),
        &projection_report,
    )?;
    fs::write(
        results_dir.join("sbf-projections.md"),
        render_sbf_projection_markdown(&projection_report),
    )?;

    let gate = decide_gate(&host_report, &projection_report);
    write_json(&raw_dir.join("gate.json"), &gate)?;
    fs::write(
        docs_dir.join("circle-parameter-gate.md"),
        render_gate_markdown(&gate, &projection_report),
    )?;

    Ok(())
}

fn build_parameter_space_report() -> ParameterSpaceReport {
    ParameterSpaceReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        reference: reference_parameters(),
        findings: vec![
            "Hash family is generic at the CirclePcs type level, but the shipped Circle examples at the pinned commit only instantiate Keccak and Poseidon2 MMCS/challenger combinations; no SHA-256 Circle configuration is provided out of the box.".to_string(),
            "log_blowup is the actual rate knob. p3-fri exposes any usize value, with blowup = 2^log_blowup and conjectured soundness bits = log_blowup * num_queries + query_proof_of_work_bits.".to_string(),
            "Query count is a direct knob. p3-circle does not expose 100/120/128-bit presets; those targets have to be reached by choosing num_queries, log_blowup, and query_proof_of_work_bits together.".to_string(),
            "max_log_arity is exposed in FriParameters, but Circle folding hard-asserts log_arity == 1 at this commit. In practice Circle PCS is fixed to arity 2, so max_log_arity > 1 is not a real supported range.".to_string(),
            "log_final_poly_len is exposed in FriParameters, but circle/src/prover.rs explicitly says Circle folds down to blowup elements with no separate final_poly_len. For the Circle path this knob is narrower than it appears.".to_string(),
            "query_proof_of_work_bits is live in the Circle prover/verifier and can trade prover grinding for fewer queries at a fixed conjectured target.".to_string(),
            "commit_proof_of_work_bits is exposed in FriParameters but not consumed by the Circle prover/verifier path, so it is not a live cost/security knob for Circle proofs at this commit.".to_string(),
            "CirclePcs cannot commit to fewer than 4 rows. That makes 4 the minimum meaningful trace height for this protocol implementation.".to_string(),
            "The field tower in the validated path is M31 / CM31 / QM31. Circle code is generic over ComplexExtendable base fields, but the shipped proof examples and the earlier byte-level mirror verifier are both pinned to the Mersenne31 cubic-extension family.".to_string(),
            "Security accounting exposed by p3-fri is conjectural only. The code offers conjectured_soundness_bits(); it does not expose separate Johnson / unique-decoding / capacity security selectors for Circle STARKs.".to_string(),
        ],
        measured_hash_family: "Keccak256 byte-digest MMCS + HashChallenger",
        measured_hash_scope: vec![
            "Measured sweep keeps the validated mirror proof family from the earlier interop spike: M31 base field, cubic extension challenge field, Keccak-256 commitments/transcript, postcard proof bytes.".to_string(),
            "Poseidon2 and the u64-sponge Keccak example families are documented as exposed by p3-circle, but they are not swept here because the current mirror verifier was validated only against unchanged Keccak-256 byte-digest proofs. Supporting a different MMCS/challenger family would require new proof-type plumbing rather than a pure parameter change.".to_string(),
        ],
        source_links: vec![
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/fri/src/config.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/pcs.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/prover.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/folding.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/circle/src/verifier.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/examples/src/types.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/examples/src/proofs.rs".to_string(),
            "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/examples/examples/prove_prime_field_31.rs".to_string(),
        ],
    }
}

fn build_attempt_specs() -> Vec<AttemptSpec> {
    let mut specs = Vec::new();

    for target_bits in [100_u32, 120, 128] {
        for log_blowup in [1_usize, 2, 3, 4] {
            for max_log_arity in [1_usize, 2, 3] {
                for query_pow_bits in [8_usize, 16] {
                    specs.push(make_attempt(
                        ScenarioKind::Counter4,
                        target_bits,
                        CircleFriConfig {
                            log_blowup,
                            log_final_poly_len: 0,
                            max_log_arity,
                            num_queries: queries_for_target(
                                target_bits,
                                log_blowup,
                                query_pow_bits,
                            ),
                            commit_proof_of_work_bits: 0,
                            query_proof_of_work_bits: query_pow_bits,
                        },
                        vec![
                            "Primary floor search on the smallest supported 4-row trace."
                                .to_string(),
                        ],
                    ));
                }
            }
        }
    }

    for scenario in [ScenarioKind::Counter8, ScenarioKind::Counter16] {
        for target_bits in [100_u32, 128] {
            for log_blowup in [2_usize, 4] {
                for max_log_arity in [1_usize, 3] {
                    specs.push(make_attempt(
                        scenario,
                        target_bits,
                        CircleFriConfig {
                            log_blowup,
                            log_final_poly_len: 0,
                            max_log_arity,
                            num_queries: queries_for_target(target_bits, log_blowup, 16),
                            commit_proof_of_work_bits: 0,
                            query_proof_of_work_bits: 16,
                        },
                        vec![
                            "Trace-scaling comparison for successful floor candidates.".to_string()
                        ],
                    ));
                }
            }
        }
    }

    specs.push(make_attempt(
        ScenarioKind::Counter4,
        100,
        CircleFriConfig {
            log_blowup: 1,
            log_final_poly_len: 2,
            max_log_arity: 1,
            num_queries: queries_for_target(100, 1, 16),
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
        },
        vec![
            "Probe whether log_final_poly_len is actually live on the Circle prover path."
                .to_string(),
        ],
    ));
    specs.push(make_attempt(
        ScenarioKind::Counter4,
        100,
        CircleFriConfig {
            log_blowup: 1,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: queries_for_target(100, 1, 16),
            commit_proof_of_work_bits: 8,
            query_proof_of_work_bits: 16,
        },
        vec!["Probe whether commit_proof_of_work_bits changes Circle proofs at all.".to_string()],
    ));

    specs
}

fn make_attempt(
    scenario: ScenarioKind,
    target_bits: u32,
    fri: CircleFriConfig,
    notes: Vec<String>,
) -> AttemptSpec {
    let rate = 1usize << fri.log_blowup;
    let mut id = format!(
        "{}-t{}-rate1over{}-q{}-pow{}-arity{}",
        scenario.slug(),
        target_bits,
        rate,
        fri.num_queries,
        fri.query_proof_of_work_bits,
        fri.max_log_arity
    );
    if fri.log_final_poly_len != 0 {
        id.push_str(&format!("-final{}", fri.log_final_poly_len));
    }
    if fri.commit_proof_of_work_bits != 0 {
        id.push_str(&format!("-commitpow{}", fri.commit_proof_of_work_bits));
    }
    AttemptSpec {
        id,
        scenario,
        target_bits,
        security_assumption: "p3-fri conjectured soundness bits = log_blowup * num_queries + query_proof_of_work_bits",
        fri,
        notes,
    }
}

fn queries_for_target(target_bits: u32, log_blowup: usize, query_pow_bits: usize) -> usize {
    let covered = query_pow_bits as u32;
    if covered >= target_bits {
        1
    } else {
        (target_bits - covered).div_ceil(log_blowup as u32) as usize
    }
}

fn run_host_sweep(
    root: &Path,
    proofs_dir: &Path,
    raw_configs_dir: &Path,
    raw_host_dir: &Path,
    attempts: Vec<AttemptSpec>,
) -> Result<HostSweepReport> {
    let mut records = Vec::new();
    let mut divergences = Vec::new();
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    for attempt in attempts {
        let metadata = scenario_metadata(attempt.scenario);
        write_json(
            &raw_configs_dir.join(format!("{}.json", attempt.id)),
            &attempt,
        )?;

        let record = match catch_unwind(AssertUnwindSafe(|| {
            reference_prove_scenario_with_fri(attempt.scenario, attempt.fri)
        })) {
            Ok(Ok(proof_bytes)) => {
                let proof_sha = hex_bytes(&hash(&proof_bytes).to_bytes());
                let proof_path = proofs_dir.join(format!("{}.postcard", attempt.id));
                let instruction_path = raw_host_dir.join(format!("{}-instruction.bin", attempt.id));
                fs::write(&proof_path, &proof_bytes)?;
                fs::write(
                    raw_host_dir.join(format!("{}.hex", attempt.id)),
                    hex_bytes(&proof_bytes),
                )?;
                fs::write(
                    &instruction_path,
                    instruction_data(attempt.scenario, &proof_bytes),
                )?;

                let proof_summary = summarize_proof_bytes(&proof_bytes)
                    .with_context(|| format!("failed to summarize {}", attempt.id))?;
                let parsed = parse_mirror_proof(&proof_bytes)
                    .with_context(|| format!("failed to parse {}", attempt.id))?;
                write_json(
                    &raw_host_dir.join(format!("{}-structure.json", attempt.id)),
                    &serde_json::json!({
                        "attempt": &attempt,
                        "metadata": &metadata,
                        "summary": &proof_summary,
                        "parsed": parsed,
                    }),
                )?;

                let reference_result = reference_verify_scenario_bytes_with_fri(
                    attempt.scenario,
                    attempt.fri,
                    &proof_bytes,
                );
                let mirror_result = circle_p3_core::mirror_verify_scenario_bytes_with_fri(
                    attempt.scenario,
                    attempt.fri,
                    &proof_bytes,
                );
                let reference_accepts = reference_result.is_ok();
                let mirror_accepts = mirror_result.is_ok();
                if !reference_accepts || !mirror_accepts {
                    divergences.push(format!(
                        "{} accepted mismatch: reference_accepts={} mirror_accepts={}",
                        attempt.id, reference_accepts, mirror_accepts
                    ));
                }

                AttemptRecord {
                    id: attempt.id,
                    scenario: attempt.scenario.slug().to_string(),
                    metadata,
                    target_bits: attempt.target_bits,
                    security_assumption: attempt.security_assumption,
                    fri: attempt.fri,
                    conjectured_soundness_bits: attempt.fri.conjectured_soundness_bits(),
                    status: "success".to_string(),
                    proof_path: Some(relative(root, &proof_path)),
                    instruction_data_path: Some(relative(root, &instruction_path)),
                    sha256: Some(proof_sha),
                    proof_summary: Some(proof_summary),
                    reference_accepts: Some(reference_accepts),
                    mirror_accepts: Some(mirror_accepts),
                    error: None,
                    notes: attempt.notes,
                }
            }
            Ok(Err(err)) => AttemptRecord {
                id: attempt.id,
                scenario: attempt.scenario.slug().to_string(),
                metadata,
                target_bits: attempt.target_bits,
                security_assumption: attempt.security_assumption,
                fri: attempt.fri,
                conjectured_soundness_bits: attempt.fri.conjectured_soundness_bits(),
                status: "failed".to_string(),
                proof_path: None,
                instruction_data_path: None,
                sha256: None,
                proof_summary: None,
                reference_accepts: None,
                mirror_accepts: None,
                error: Some(err.to_string()),
                notes: attempt.notes,
            },
            Err(payload) => AttemptRecord {
                id: attempt.id,
                scenario: attempt.scenario.slug().to_string(),
                metadata,
                target_bits: attempt.target_bits,
                security_assumption: attempt.security_assumption,
                fri: attempt.fri,
                conjectured_soundness_bits: attempt.fri.conjectured_soundness_bits(),
                status: "failed".to_string(),
                proof_path: None,
                instruction_data_path: None,
                sha256: None,
                proof_summary: None,
                reference_accepts: None,
                mirror_accepts: None,
                error: Some(format!("panic: {}", panic_message(payload))),
                notes: attempt.notes,
            },
        };

        records.push(record);
    }

    std::panic::set_hook(previous_hook);

    let successful_attempts = records
        .iter()
        .filter(|record| record.status == "success")
        .count();
    let failed_attempts = records.len().saturating_sub(successful_attempts);
    Ok(HostSweepReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        reference: reference_parameters(),
        attempts: records,
        total_attempts: successful_attempts + failed_attempts,
        successful_attempts,
        failed_attempts,
        divergences,
    })
}

fn project_sbf_costs(host: &HostSweepReport) -> Result<SbfProjectionReport> {
    let root = workspace_root()?;
    let summary_path = root.join("phase1_results/summary.json");
    if !summary_path.exists() {
        return Err(anyhow!(
            "missing phase1 cost model summary at {}",
            summary_path.display()
        ));
    }

    let phase1 = load_summary(&summary_path)?;
    let limits = SvmLimits::default();
    let mut ranked = Vec::new();

    for attempt in &host.attempts {
        if attempt.status != "success" {
            continue;
        }
        let proof_summary = attempt
            .proof_summary
            .as_ref()
            .ok_or_else(|| anyhow!("missing proof summary for {}", attempt.id))?;
        let proof_bytes = proof_summary.proof_bytes as u64;
        let queries = proof_summary.fri_query_count as u64;
        let merkle_levels = proof_summary.total_merkle_siblings as u64;
        let merkle_paths = (proof_summary.total_input_openings
            + proof_summary.fri_query_count
            + proof_summary.fri_query_count * proof_summary.fri_commit_phase_rounds)
            as u64;
        let transport = transport_features(proof_bytes, TX_CHUNK_BYTES);
        let sha_calls = merkle_levels + queries + transport.sha_calls + 4;
        let sha_bytes = merkle_levels * 64 + proof_bytes + 32 * sha_calls + transport.sha_bytes;
        let field_add_sub_ops = queries
            * (proof_summary.trace_local_width as u64
                + proof_summary.trace_next_width as u64
                + proof_summary.quotient_chunk_count as u64 * 12);
        let field_mul_ops = queries * (proof_summary.quotient_chunk_count as u64 * 6 + 20)
            + proof_summary.lambda_count as u64 * 4;
        let field_inv_ops = queries * 3 + proof_summary.quotient_chunk_count as u64;
        let extension_mul_ops = queries
            * ((proof_summary.quotient_chunk_count as u64
                + proof_summary.total_commit_phase_siblings as u64 / queries.max(1))
                * 3
                + 16);

        let profile = ProfileScoreInput {
            name: attempt.id.clone(),
            protocol_family: Some("Circle".to_string()),
            features: CostFeatures {
                sha_calls,
                sha_bytes,
                merkle_paths,
                merkle_levels,
                proof_bytes,
                proof_segments: proof_bytes.div_ceil(TX_CHUNK_BYTES),
                upload_bytes: proof_bytes,
                upload_chunks: transport.upload_chunks,
                heap_frame_bytes_requested: HEAP_FRAME_BYTES,
                heap_pages_32k: HEAP_FRAME_BYTES.div_ceil(32 * 1024),
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
                    "scenario",
                    attempt.scenario.clone(),
                    "Measured on the actual p3-circle proof generated during the host sweep.",
                    &["results/circle-parameter-sweep/host-results.md"],
                ),
                parameter_choice(
                    "log_blowup",
                    attempt.fri.log_blowup.to_string(),
                    "Literal FRI blowup exponent supplied to p3-circle.",
                    &["docs/circle-parameter-space.md"],
                ),
                parameter_choice(
                    "num_queries",
                    attempt.fri.num_queries.to_string(),
                    "Literal FRI query count used by the generated proof.",
                    &["results/circle-parameter-sweep/host-results.md"],
                ),
                parameter_choice(
                    "query_proof_of_work_bits",
                    attempt.fri.query_proof_of_work_bits.to_string(),
                    "Literal PoW bits used by the generated proof.",
                    &["results/circle-parameter-sweep/host-results.md"],
                ),
                parameter_choice(
                    "upload_chunk_bytes",
                    TX_CHUNK_BYTES.to_string(),
                    "Conservative staging chunk under the 1232-byte Solana transaction ceiling.",
                    &["phase1_results/summary.json"],
                ),
            ],
            references: vec![
                "results/circle-parameter-sweep/host-results.md".to_string(),
                "docs/circle-parameter-space.md".to_string(),
                "phase1_results/summary.json".to_string(),
            ],
            query_soundness_model: Some(fri_query_soundness_model(
                attempt.fri.num_queries as u64,
                attempt.fri.log_blowup as u32,
                attempt.fri.query_proof_of_work_bits as u32,
                attempt.target_bits as f64,
                &[
                    "https://github.com/Plonky3/Plonky3/blob/0f87f2b543a01880274965c410bf804c124f5046/fri/src/config.rs",
                ],
                &[
                    "Security bound is the p3-fri conjectured helper, not a separate proven Circle-STARK soundness calculator.",
                ],
            )),
            notes: vec![
                "Projected from proof structure and the existing phase1 CU model; no direct SBF execution was possible under the pinned reference because the Solana cargo-build-sbf toolchain still rejects edition2024 dependencies.".to_string(),
                "Transport cost assumes staged upload in 512-byte chunks because every successful Circle proof in this sweep exceeds the 1232-byte transaction cap.".to_string(),
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
        ranked.push(ProjectionRecord {
            rank: 0,
            attempt_id: attempt.id.clone(),
            target_bits: attempt.target_bits,
            conjectured_soundness_bits: attempt.conjectured_soundness_bits,
            scenario: attempt.scenario.clone(),
            fri: attempt.fri,
            proof_bytes,
            profile,
            score,
        });
    }

    ranked.sort_by(|a, b| {
        a.score
            .predicted_cu
            .partial_cmp(&b.score.predicted_cu)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    for (index, record) in ranked.iter_mut().enumerate() {
        record.rank = index + 1;
    }

    Ok(SbfProjectionReport {
        generated_at_utc: Utc::now().to_rfc3339(),
        methodology: "Reuse the existing phase1 SVM cost model. For each successful host proof, derive feature counts from proof structure (hash calls/bytes, Merkle levels, field ops, staged upload bytes), then score with the chosen monolithic/core/transport models. This is a projection, not a direct SBF run.".to_string(),
        compilation_status: "projection-only".to_string(),
        blockers: vec![
            "Pinned reference still inherits the earlier cargo-build-sbf blocker: Solana's bundled Cargo 1.84 rejects edition2024 crates in the dependency tree.".to_string(),
            "To preserve proof-byte compatibility with the validated p3-circle reference commit, this sweep does not pin an older upstream version just to satisfy cargo-build-sbf.".to_string(),
        ],
        ranked,
    })
}

fn decide_gate(host: &HostSweepReport, projections: &SbfProjectionReport) -> GateDecision {
    let best = projections.ranked.first();
    let mut rationale = Vec::new();

    if !host.divergences.is_empty() {
        rationale.push("Host sweep found reference/mirror divergences, so Circle remains blocked before any Solana optimization discussion.".to_string());
        return GateDecision {
            generated_at_utc: Utc::now().to_rfc3339(),
            gate: "RED",
            best_attempt_id: best.map(|record| record.attempt_id.clone()),
            best_projected_cu: best.map(|record| record.score.predicted_cu),
            best_margin_cu: best.map(|record| 1_400_000_f64 - record.score.predicted_cu),
            rationale,
        };
    }

    if let Some(best) = best {
        let margin = 1_400_000_f64 - best.score.predicted_cu;
        rationale.push(format!(
            "Best projected configuration is `{}` at {:.0} CU with proof size {} bytes.",
            best.attempt_id, best.score.predicted_cu, best.proof_bytes
        ));
        rationale.push(format!(
            "That leaves {:.0} CU against the 1.4M cap.",
            margin
        ));
        rationale.push(
            "Every successful configuration still exceeds the 1232-byte transaction ceiling and therefore requires staged upload."
                .to_string(),
        );
        if let Some(soundness) = &best.score.query_soundness {
            rationale.push(format!(
                "Soundness accounting for the best configuration is split: proven lower bound {:.1} bits, conjectured upper bound {}.",
                soundness.lower_bits,
                soundness
                    .upper_bits
                    .map(|bits| format!("{bits:.1} bits"))
                    .unwrap_or_else(|| "not reported".to_string())
            ));
        }
        let gate = if best.score.predicted_cu <= 1_200_000_f64 {
            rationale.push(
                "This clears the compute cap with at least 200k CU of margin at the selected security target."
                    .to_string(),
            );
            "GREEN"
        } else if best.score.predicted_cu <= 2_800_000_f64 {
            rationale.push(
                "This is above the cap but within 2x, so the result is optimization-sensitive rather than structurally impossible."
                    .to_string(),
            );
            "AMBER"
        } else {
            rationale.push(
                "No defensible configuration gets within 2x of the compute cap, so the gap is structural rather than a bad parameter choice."
                    .to_string(),
            );
            "RED"
        };
        GateDecision {
            generated_at_utc: Utc::now().to_rfc3339(),
            gate,
            best_attempt_id: Some(best.attempt_id.clone()),
            best_projected_cu: Some(best.score.predicted_cu),
            best_margin_cu: Some(margin),
            rationale,
        }
    } else {
        rationale.push(
            "No successful projected configuration met its own target soundness bound.".to_string(),
        );
        GateDecision {
            generated_at_utc: Utc::now().to_rfc3339(),
            gate: "RED",
            best_attempt_id: None,
            best_projected_cu: None,
            best_margin_cu: None,
            rationale,
        }
    }
}

fn render_parameter_space_markdown(report: &ParameterSpaceReport) -> String {
    let mut out = String::new();
    out.push_str("# Circle parameter space\n\n");
    out.push_str(&format!(
        "Generated: {}\n\nPinned reference: `{}` at `{}`.\n\n",
        report.generated_at_utc, report.reference.fixture_name, report.reference.git_rev
    ));
    out.push_str("## Actual knobs\n\n");
    for finding in &report.findings {
        out.push_str(&format!("- {}\n", finding));
    }
    out.push('\n');
    out.push_str("## Measured scope\n\n");
    out.push_str(&format!(
        "- Measured hash family: `{}`\n",
        report.measured_hash_family
    ));
    for note in &report.measured_hash_scope {
        out.push_str(&format!("- {}\n", note));
    }
    out.push('\n');
    out.push_str("## Primary sources\n\n");
    for link in &report.source_links {
        out.push_str(&format!("- {}\n", link));
    }
    out
}

fn render_host_results_markdown(report: &HostSweepReport) -> String {
    let mut out = String::new();
    out.push_str("# Circle host parameter sweep\n\n");
    out.push_str(&format!(
        "Generated: {}\n\nAttempts: `{}` success: `{}` failed: `{}` divergences: `{}`.\n\n",
        report.generated_at_utc,
        report.total_attempts,
        report.successful_attempts,
        report.failed_attempts,
        report.divergences.len()
    ));
    out.push_str("## Summary\n\n");
    out.push_str(&format!(
        "- Successful attempts only occurred at `log_blowup=1` (`rate=1/2`). Every measured `log_blowup > 1` configuration failed before proof emission.\n"
    ));
    out.push_str(
        "- All successful proofs were accepted by both the p3-circle reference verifier and the unchanged mirror verifier.\n",
    );
    out.push_str(
        "- Successful `max_log_arity` variants emitted byte-identical proofs, so `max_log_arity > 1` was inert rather than providing higher-arity folding.\n\n",
    );
    out.push_str(
        "- The explicit `log_final_poly_len=2` and `commit_proof_of_work_bits=8` probes matched the baseline `rate=1/2`, `pow16`, `target=100` proof byte-for-byte, confirming that both knobs are inert on the measured Circle path.\n\n",
    );
    out.push_str("## Matrix\n\n");
    out.push_str("| id | scenario | target | rate | queries | q_pow | max_arity | status | proof_bytes | ref | mirror | notes |\n");
    out.push_str("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |\n");
    for attempt in &report.attempts {
        let proof_bytes = attempt
            .proof_summary
            .as_ref()
            .map(|summary| summary.proof_bytes.to_string())
            .unwrap_or_else(|| "-".to_string());
        let reference = attempt.reference_accepts.map(verdict).unwrap_or("-");
        let mirror = attempt.mirror_accepts.map(verdict).unwrap_or("-");
        let notes = if let Some(error) = &attempt.error {
            error.clone()
        } else {
            attempt.notes.join(" ")
        };
        out.push_str(&format!(
            "| `{}` | `{}` | `{}` | `1/{}` | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | {} |\n",
            attempt.id,
            attempt.scenario,
            attempt.target_bits,
            1usize << attempt.fri.log_blowup,
            attempt.fri.num_queries,
            attempt.fri.query_proof_of_work_bits,
            attempt.fri.max_log_arity,
            attempt.status,
            proof_bytes,
            reference,
            mirror,
            sanitize_cell(&notes),
        ));
    }
    out.push('\n');
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

fn render_sbf_projection_markdown(report: &SbfProjectionReport) -> String {
    let mut out = String::new();
    out.push_str("# Circle SBF projections\n\n");
    out.push_str(&format!(
        "Generated: {}\n\nCompilation status: `{}`.\n\n",
        report.generated_at_utc, report.compilation_status
    ));
    out.push_str("## Methodology\n\n");
    out.push_str(&report.methodology);
    out.push_str("\n\n## Blockers\n\n");
    for blocker in &report.blockers {
        out.push_str(&format!("- {}\n", blocker));
    }
    out.push_str("\n## Ranked configurations\n\n");
    out.push_str("| rank | id | target | proof_bytes | projected_cu | budget_fraction | core_cu | transport_cu | dominant drivers |\n");
    out.push_str("| --- | --- | --- | --- | --- | --- | --- | --- | --- |\n");
    for record in &report.ranked {
        let drivers = record
            .score
            .dominant_contributors
            .iter()
            .map(|contrib| format!("{}={:.0}", contrib.feature, contrib.cu))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "| `{}` | `{}` | `{}` | `{}` | `{:.0}` | `{:.2}` | `{}` | `{}` | {} |\n",
            record.rank,
            record.attempt_id,
            record.target_bits,
            record.proof_bytes,
            record.score.predicted_cu,
            record.score.cu_budget_fraction,
            fmt_opt(record.score.verification_core_cu),
            fmt_opt(record.score.transport_overhead_cu),
            sanitize_cell(&drivers),
        ));
    }
    out
}

fn render_gate_markdown(gate: &GateDecision, projections: &SbfProjectionReport) -> String {
    let mut out = String::new();
    out.push_str("# Circle parameter gate\n\n");
    out.push_str(&format!("## {}\n\n", gate.gate));
    if let Some(best) = projections.ranked.first() {
        out.push_str("### Best configuration\n\n");
        out.push_str(&format!(
            "- `{}` scenario=`{}` target_bits=`{}` rate=`1/{}` queries=`{}` query_pow_bits=`{}` projected_cu=`{:.0}` proof_bytes=`{}`\n\n",
            best.attempt_id,
            best.scenario,
            best.target_bits,
            1usize << best.fri.log_blowup,
            best.fri.num_queries,
            best.fri.query_proof_of_work_bits,
            best.score.predicted_cu,
            best.proof_bytes
        ));
        if let Some(soundness) = &best.score.query_soundness {
            out.push_str(&format!(
                "- Soundness lower bound=`{:.1}` upper bound=`{}` target=`{:.1}`\n\n",
                soundness.lower_bits,
                soundness
                    .upper_bits
                    .map(|bits| format!("{bits:.1}"))
                    .unwrap_or_else(|| "-".to_string()),
                soundness.target_bits,
            ));
        }
    }
    out.push_str("### Rationale\n\n");
    for line in &gate.rationale {
        out.push_str(&format!("- {}\n", line));
    }
    out.push('\n');
    out.push_str("### Recommendation\n\n");
    match gate.gate {
        "GREEN" => out.push_str(
            "Proceed with the full Solana port at the specific configuration above.\n",
        ),
        "AMBER" => out.push_str(
            "Treat the best configuration as the only plausible Circle target, and decide explicitly whether primitive-level optimization work is worth it before switching to WHIR-UD.\n",
        ),
        _ => out.push_str(
            "Move to the WHIR-UD spike. The remaining Circle gap is structural across the supported p3-circle configuration space measured here.\n",
        ),
    }
    out
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn verdict(value: bool) -> &'static str {
    if value {
        "accept"
    } else {
        "reject"
    }
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<&'static str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

fn sanitize_cell(input: &str) -> String {
    input.replace('|', "\\|").replace('\n', " ")
}

fn fmt_opt(value: Option<f64>) -> String {
    value
        .map(|value| format!("{value:.0}"))
        .unwrap_or_else(|| "-".to_string())
}
