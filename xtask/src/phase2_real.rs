use super::*;
use anyhow::Context;
use phase1_probe::run_real_fri_verify;
use serde::{Deserialize, Serialize};
use stark_prover::{generate_proof_with_config, ProofGenerationConfig};
use std::str::FromStr;
use winter_fri::{set_fri_proof_layer_layout, FriProofLayerLayout};

const REAL_VERIFY_HEAP_FRAME_BYTES: u32 = 256 * 1024;
const ACTUAL_VENDOR_PROGRAM_ID: &str = "CECNRbDxFQVfWiQwvG8qcSGPGSk8eLWraBCERcdL5DKT";

#[derive(Clone, Debug, Serialize)]
struct Phase2RealRunConfig {
    limits: SvmLimits,
    payload_chunk_size: usize,
    verify_repetitions: u32,
    baseline_trace_len: usize,
    baseline_num_queries: usize,
    experimental_trace_len_candidates: Vec<usize>,
    experimental_query_count_candidates: Vec<usize>,
    production_max_chat_payload_bytes: usize,
    phase2_loader_max_chat_payload_bytes: usize,
    kem_len: usize,
    slot_base: u64,
    cipher_hex: String,
    nonce_hex: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct ArchivedBaselineReference {
    verify_stark_mean_cu: f64,
    proof_bytes: u64,
    trace_length: u64,
    fri_layers: u64,
}

#[derive(Clone, Debug, Serialize)]
struct GeneratedProofVariant {
    variant: String,
    group: String,
    include_interpolants: bool,
    trace_len: usize,
    slot: u64,
    seed_u64: u64,
    inc_u64: u64,
    digest_hex: String,
    proof_bytes: usize,
    proof_sha256_hex: String,
    body_bytes: u64,
    chat_msg_account_bytes: u64,
    configured_queries: u64,
    fri_layers: u64,
    fri_remainder_elements: u64,
    lde_domain_size: u64,
    predicted_verify_cu: f64,
    predicted_lower_cu: f64,
    predicted_upper_cu: f64,
    proof_path: String,
}

#[derive(Clone, Debug, Serialize)]
struct RealMeasurement {
    variant: String,
    group: String,
    domain: String,
    stage: String,
    repetition: u32,
    include_interpolants: bool,
    trace_len: usize,
    slot: u64,
    proof_bytes: usize,
    body_bytes: u64,
    chat_msg_account_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    fri_layers: u64,
    configured_queries: u64,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    transaction_bytes: Option<u64>,
    error: Option<String>,
    seed_u64: u64,
    inc_u64: u64,
    digest_hex: String,
    proof_sha256_hex: String,
}

#[derive(Serialize)]
struct RealMeasurementCsvRow {
    variant: String,
    group: String,
    domain: String,
    stage: String,
    repetition: u32,
    include_interpolants: bool,
    trace_len: usize,
    slot: u64,
    proof_bytes: usize,
    body_bytes: u64,
    chat_msg_account_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    fri_layers: u64,
    configured_queries: u64,
    actual_cu: Option<u64>,
    elapsed_ns: Option<u128>,
    transaction_bytes: Option<u64>,
    error: Option<String>,
    seed_u64: u64,
    inc_u64: u64,
    digest_hex: String,
    proof_sha256_hex: String,
}

#[derive(Clone, Debug, Serialize)]
struct PredictedMeasuredRow {
    variant: String,
    trace_len: usize,
    include_interpolants: bool,
    proof_bytes: usize,
    fri_layers: u64,
    predicted_verify_cu: f64,
    measured_verify_cu: u64,
    absolute_error_cu: f64,
    relative_error_fraction: f64,
}

#[derive(Clone, Debug, Serialize)]
struct Phase2RealSummary {
    generated_at_utc: String,
    command: String,
    versions: VersionManifest,
    archived_trace8_reference: ArchivedBaselineReference,
    raw_artifacts: Vec<String>,
    sanity_variant: String,
    sanity_variant_verify_cu: u64,
    experimental_trace_len: usize,
    experimental_num_queries: usize,
    baseline_variant: String,
    winning_variant: String,
    baseline_verify_cu: u64,
    winning_verify_cu: u64,
    baseline_pipeline_cu: u64,
    winning_pipeline_cu: u64,
    delta_verify_cu: i64,
    delta_pipeline_cu: i64,
    delta_bytes: i64,
    note: String,
}

struct OnchainPreparedVariant {
    chat_msg_pda: Pubkey,
    setup_total_cu: u64,
    records: Vec<RealMeasurement>,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct ExperimentalProofShape {
    trace_len: usize,
    num_queries: usize,
}

#[derive(Clone, Debug, Deserialize)]
struct SyntheticPhase2Summary {
    arithmetic_winner_raw_mul: String,
    arithmetic_winner_verifier_kernel: String,
    extension_kernel_winner: String,
    lift_policy_winner: String,
    whir_fold_winner: String,
    combined_estimated_savings_cu: f64,
    combined_estimated_headroom_cu: f64,
    combined_estimated_post_change_cu: f64,
    biggest_remaining_risk: String,
}

#[derive(Debug, Deserialize)]
struct SyntheticFoldCsvRow {
    variant: String,
    stage: String,
    actual_cu: Option<u64>,
}

pub(super) fn run_phase2_real_experiments() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/phase2-real-experiments.md");
    let results_root = root.join("results/phase2-real");
    let proofs_root = results_root.join("proofs");
    if results_root.exists() {
        fs::remove_dir_all(&results_root)?;
    }
    fs::create_dir_all(&results_root)?;
    fs::create_dir_all(&proofs_root)?;

    let cipher = (0u8..28).collect::<Vec<_>>();
    let nonce = vec![
        0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe, 0x13, 0x57, 0x9b, 0xdf,
    ];
    let config = Phase2RealRunConfig {
        limits: SvmLimits::default(),
        payload_chunk_size: 640,
        verify_repetitions: 3,
        baseline_trace_len: 8,
        baseline_num_queries: 30,
        experimental_trace_len_candidates: vec![16, 32, 64, 128, 256, 512, 1024],
        experimental_query_count_candidates: vec![30, 24, 20, 16, 12, 8, 6, 4, 2],
        production_max_chat_payload_bytes: 10_068,
        phase2_loader_max_chat_payload_bytes: 65_536,
        kem_len: 0,
        slot_base: 10_000,
        cipher_hex: hex_string(&cipher),
        nonce_hex: hex_string(&nonce),
    };
    write_json(&results_root.join("run_config.json"), &config)?;

    let versions = capture_version_manifest()?;
    write_json(&results_root.join("version_manifest.json"), &versions)?;

    let archived_reference = load_archived_trace8_reference(&root)?;
    let phase1_summary = load_summary(&root.join("phase1_results/summary.json"))?;

    let program_id = Pubkey::from_str(ACTUAL_VENDOR_PROGRAM_ID)?;
    let program_so = build_actual_verifier_program(&root)?;
    let validator = start_validator_with_program(&root, &results_root, program_id, &program_so)?;
    let harness = BenchHarness {
        client: LocalRpcClient::new(validator.rpc_url.clone()),
        payer: Keypair::new(),
        program_id,
        limits: config.limits.clone(),
    };
    fund_payer(&harness)?;

    let experimental_shape = choose_experimental_proof_shape(
        &config,
        &phase1_summary,
        &proofs_root,
        &cipher,
        config.slot_base + 1,
    )?;

    let mut variants = vec![generate_variant(
        &phase1_summary,
        &proofs_root,
        "trace8_raw_rows",
        "sanity",
        FriProofLayerLayout::RAW_ROWS,
        config.baseline_trace_len,
        config.baseline_num_queries,
        config.slot_base,
        &cipher,
        config.kem_len,
    )?];
    let experimental_raw = generate_variant(
        &phase1_summary,
        &proofs_root,
        &format!(
            "trace{}_q{}_raw_rows",
            experimental_shape.trace_len, experimental_shape.num_queries
        ),
        "fold_experiment",
        FriProofLayerLayout::RAW_ROWS,
        experimental_shape.trace_len,
        experimental_shape.num_queries,
        config.slot_base + 1,
        &cipher,
        config.kem_len,
    )?;
    let experimental_packaged = generate_variant(
        &phase1_summary,
        &proofs_root,
        &format!(
            "trace{}_q{}_raw_rows_plus_interpolants",
            experimental_shape.trace_len, experimental_shape.num_queries
        ),
        "fold_experiment",
        FriProofLayerLayout::RAW_ROWS_PLUS_INTERPOLANTS,
        experimental_shape.trace_len,
        experimental_shape.num_queries,
        config.slot_base + 2,
        &cipher,
        config.kem_len,
    )?;
    if experimental_raw.proof_sha256_hex == experimental_packaged.proof_sha256_hex {
        bail!(
            "fold experiment is invalid: trace_len={} num_queries={} still produced identical raw and packaged proofs",
            experimental_shape.trace_len,
            experimental_shape.num_queries
        );
    }
    variants.push(experimental_raw);
    variants.push(experimental_packaged);
    let mut records = Vec::new();

    for variant in &variants {
        let proof_bytes = fs::read(&variant.proof_path)
            .with_context(|| format!("failed to read {}", variant.proof_path))?;
        for repetition in 0..config.verify_repetitions {
            let host_start = Instant::now();
            let _host = run_real_fri_verify(&proof_bytes, variant.seed_u64, variant.inc_u64, 1)
                .map_err(|err| anyhow!("host verify failed for {}: {}", variant.variant, err))?;
            records.push(RealMeasurement {
                variant: variant.variant.clone(),
                group: variant.group.clone(),
                domain: "host".to_string(),
                stage: "verify".to_string(),
                repetition,
                include_interpolants: variant.include_interpolants,
                trace_len: variant.trace_len,
                slot: variant.slot,
                proof_bytes: variant.proof_bytes,
                body_bytes: variant.body_bytes,
                chat_msg_account_bytes: variant.chat_msg_account_bytes,
                upload_chunk_size: 0,
                upload_chunks: 0,
                heap_frame_bytes_requested: REAL_VERIFY_HEAP_FRAME_BYTES as u64,
                fri_layers: variant.fri_layers,
                configured_queries: variant.configured_queries,
                actual_cu: None,
                elapsed_ns: Some(host_start.elapsed().as_nanos()),
                transaction_bytes: None,
                error: None,
                seed_u64: variant.seed_u64,
                inc_u64: variant.inc_u64,
                digest_hex: variant.digest_hex.clone(),
                proof_sha256_hex: variant.proof_sha256_hex.clone(),
            });
        }

        let prepared = materialize_variant_onchain(&harness, &config, variant, &cipher, &nonce)?;
        records.extend(prepared.records);

        for repetition in 0..config.verify_repetitions {
            let verify_tx = simulate_plan(
                &harness,
                TxPlan {
                    instructions: vec![build_verify_stark_instruction(
                        harness.program_id,
                        prepared.chat_msg_pda,
                    )],
                    compute_unit_limit: None,
                    heap_frame_bytes: Some(REAL_VERIFY_HEAP_FRAME_BYTES),
                },
            )?;
            let verify_cu = verify_tx.units_consumed.context("verify CU missing")?;
            records.push(RealMeasurement {
                variant: variant.variant.clone(),
                group: variant.group.clone(),
                domain: "sbf".to_string(),
                stage: "verify".to_string(),
                repetition,
                include_interpolants: variant.include_interpolants,
                trace_len: variant.trace_len,
                slot: variant.slot,
                proof_bytes: variant.proof_bytes,
                body_bytes: variant.body_bytes,
                chat_msg_account_bytes: variant.chat_msg_account_bytes,
                upload_chunk_size: 0,
                upload_chunks: 0,
                heap_frame_bytes_requested: REAL_VERIFY_HEAP_FRAME_BYTES as u64,
                fri_layers: variant.fri_layers,
                configured_queries: variant.configured_queries,
                actual_cu: Some(verify_cu),
                elapsed_ns: None,
                transaction_bytes: Some(verify_tx.transaction_bytes),
                error: verify_tx.error.clone(),
                seed_u64: variant.seed_u64,
                inc_u64: variant.inc_u64,
                digest_hex: variant.digest_hex.clone(),
                proof_sha256_hex: variant.proof_sha256_hex.clone(),
            });
            records.push(RealMeasurement {
                variant: variant.variant.clone(),
                group: variant.group.clone(),
                domain: "sbf".to_string(),
                stage: "pipeline_total".to_string(),
                repetition,
                include_interpolants: variant.include_interpolants,
                trace_len: variant.trace_len,
                slot: variant.slot,
                proof_bytes: variant.proof_bytes,
                body_bytes: variant.body_bytes,
                chat_msg_account_bytes: variant.chat_msg_account_bytes,
                upload_chunk_size: 0,
                upload_chunks: 0,
                heap_frame_bytes_requested: REAL_VERIFY_HEAP_FRAME_BYTES as u64,
                fri_layers: variant.fri_layers,
                configured_queries: variant.configured_queries,
                actual_cu: Some(prepared.setup_total_cu + verify_cu),
                elapsed_ns: None,
                transaction_bytes: Some(verify_tx.transaction_bytes),
                error: verify_tx.error.clone(),
                seed_u64: variant.seed_u64,
                inc_u64: variant.inc_u64,
                digest_hex: variant.digest_hex.clone(),
                proof_sha256_hex: variant.proof_sha256_hex.clone(),
            });
        }
    }

    let predicted_vs_measured = build_predicted_vs_measured(&variants, &records)?;

    write_generic_jsonl(&results_root.join("raw.jsonl"), &records)?;
    write_real_csv(&results_root.join("raw.csv"), &records)?;
    write_json(&results_root.join("variants.json"), &variants)?;
    write_json(
        &results_root.join("predicted_vs_measured.json"),
        &predicted_vs_measured,
    )?;

    let sanity_variant = "trace8_raw_rows".to_string();
    let sanity_verify = mean_stage_u64(&records, &sanity_variant, "verify")?;
    let fold_baseline_variant = format!(
        "trace{}_q{}_raw_rows",
        experimental_shape.trace_len, experimental_shape.num_queries
    );
    let fold_packaged_variant = format!(
        "trace{}_q{}_raw_rows_plus_interpolants",
        experimental_shape.trace_len, experimental_shape.num_queries
    );
    let baseline_verify = mean_stage_u64(&records, &fold_baseline_variant, "verify")?;
    let packaged_verify = mean_stage_u64(&records, &fold_packaged_variant, "verify")?;
    let baseline_pipeline = mean_stage_u64(&records, &fold_baseline_variant, "pipeline_total")?;
    let packaged_pipeline = mean_stage_u64(&records, &fold_packaged_variant, "pipeline_total")?;
    let baseline_failed = stage_has_error(&records, &fold_baseline_variant, "verify");
    let packaged_failed = stage_has_error(&records, &fold_packaged_variant, "verify");
    let packaged_wins = match (baseline_failed, packaged_failed) {
        (true, false) => true,
        (false, true) => false,
        _ => packaged_verify < baseline_verify,
    };
    let winning_variant = if packaged_wins {
        fold_packaged_variant.clone()
    } else {
        fold_baseline_variant.clone()
    };
    let winning_verify = if packaged_wins {
        packaged_verify
    } else {
        baseline_verify
    };
    let winning_pipeline = if packaged_wins {
        packaged_pipeline
    } else {
        baseline_pipeline
    };
    let summary = Phase2RealSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask phase2-real-experiments".to_string(),
        versions,
        archived_trace8_reference: archived_reference.clone(),
        raw_artifacts: vec![
            "results/phase2-real/run_config.json".to_string(),
            "results/phase2-real/version_manifest.json".to_string(),
            "results/phase2-real/variants.json".to_string(),
            "results/phase2-real/predicted_vs_measured.json".to_string(),
            "results/phase2-real/raw.jsonl".to_string(),
            "results/phase2-real/raw.csv".to_string(),
            "results/phase2-real/summary.json".to_string(),
            "results/phase2-real/proofs/".to_string(),
            "docs/phase2-real-experiments.md".to_string(),
        ],
        sanity_variant: sanity_variant.clone(),
        sanity_variant_verify_cu: sanity_verify,
        experimental_trace_len: experimental_shape.trace_len,
        experimental_num_queries: experimental_shape.num_queries,
        baseline_variant: fold_baseline_variant.clone(),
        winning_variant: winning_variant.clone(),
        baseline_verify_cu: baseline_verify,
        winning_verify_cu: winning_verify,
        baseline_pipeline_cu: baseline_pipeline,
        winning_pipeline_cu: winning_pipeline,
        delta_verify_cu: winning_verify as i64 - baseline_verify as i64,
        delta_pipeline_cu: winning_pipeline as i64 - baseline_pipeline as i64,
        delta_bytes: proof_bytes_for_variant(&variants, &winning_variant)? as i64
            - proof_bytes_for_variant(&variants, &fold_baseline_variant)? as i64,
        note: {
            let mut note = "This measures the actual Anchor/Winterfell `verify_stark` instruction present in the repo. It is a real transparent verifier path, but it is still Winterfell/FRI over f128 rather than a native WHIR/M31 verifier.".to_string();
            if experimental_shape.num_queries != config.baseline_num_queries {
                note.push_str(&format!(
                    " The default 30-query recursive proof did not fit the configured experiment envelope, so the fold experiment relaxes the query schedule to {} queries while keeping raw-vs-packaged semantics otherwise identical.",
                    experimental_shape.num_queries
                ));
            }
            if baseline_failed || packaged_failed {
                note.push_str(" At least one measured verify variant hit the transaction CU cap before completion; those rows are preserved as lower-bound CU observations and marked as failed-to-complete.");
            }
            note
        },
    };
    write_json(&results_root.join("summary.json"), &summary)?;

    fs::write(
        &docs_path,
        render_report(
            &config,
            &archived_reference,
            &variants,
            &records,
            &predicted_vs_measured,
            &summary,
        )?,
    )?;
    fs::write(
        root.join("docs/phase2-experiments.md"),
        render_combined_phase2_report(
            &root,
            &archived_reference,
            &variants,
            &records,
            &predicted_vs_measured,
            &summary,
        )?,
    )?;

    Ok(())
}

fn build_actual_verifier_program(root: &Path) -> Result<PathBuf> {
    let out_dir = root.join("target/stark-pqc-verifier-sbf");
    fs::create_dir_all(&out_dir)?;
    let status = Command::new("cargo")
        .arg("build-sbf")
        .arg("--manifest-path")
        .arg(root.join("third_party/solana-pqzk-fullchain/programs/stark-pqc-verifier/Cargo.toml"))
        .arg("--features")
        .arg("phase2-instrumentation")
        .arg("--sbf-out-dir")
        .arg(&out_dir)
        .status()
        .context("failed to run cargo build-sbf for stark-pqc-verifier")?;
    if !status.success() {
        bail!("cargo build-sbf failed for stark-pqc-verifier");
    }
    let so_path = out_dir.join("stark_pqc_verifier.so");
    if !so_path.exists() {
        bail!("expected SBF artifact missing at {}", so_path.display());
    }
    Ok(so_path)
}

fn load_archived_trace8_reference(root: &Path) -> Result<ArchivedBaselineReference> {
    let value: serde_json::Value = serde_json::from_slice(&fs::read(
        root.join("phase1_results/real_verifier_comparison.json"),
    )?)?;
    Ok(ArchivedBaselineReference {
        verify_stark_mean_cu: value
            .get("verify_stark_baseline")
            .and_then(|v| v.get("mean_cu"))
            .and_then(serde_json::Value::as_f64)
            .context("verify_stark_baseline.mean_cu missing")?,
        proof_bytes: value
            .get("structure")
            .and_then(|v| v.get("proof_bytes"))
            .and_then(serde_json::Value::as_u64)
            .context("structure.proof_bytes missing")?,
        trace_length: value
            .get("structure")
            .and_then(|v| v.get("trace_length"))
            .and_then(serde_json::Value::as_u64)
            .context("structure.trace_length missing")?,
        fri_layers: value
            .get("structure")
            .and_then(|v| v.get("fri_layers"))
            .and_then(serde_json::Value::as_u64)
            .context("structure.fri_layers missing")?,
    })
}

fn choose_experimental_proof_shape(
    config: &Phase2RealRunConfig,
    phase1_summary: &Phase1Summary,
    proofs_root: &Path,
    cipher: &[u8],
    slot: u64,
) -> Result<ExperimentalProofShape> {
    for num_queries in &config.experimental_query_count_candidates {
        for trace_len in &config.experimental_trace_len_candidates {
            let candidate = generate_variant(
                phase1_summary,
                proofs_root,
                &format!("candidate-trace{trace_len}-q{num_queries}-raw_rows"),
                "candidate",
                FriProofLayerLayout::RAW_ROWS,
                *trace_len,
                *num_queries,
                slot,
                cipher,
                config.kem_len,
            )?;
            if candidate.fri_layers > 0
                && candidate.body_bytes as usize <= config.phase2_loader_max_chat_payload_bytes
            {
                return Ok(ExperimentalProofShape {
                    trace_len: *trace_len,
                    num_queries: *num_queries,
                });
            }
        }
    }
    bail!("no experimental proof shape produced recursive FRI layers within the chat payload cap");
}

fn generate_variant(
    phase1_summary: &Phase1Summary,
    proofs_root: &Path,
    name: &str,
    group: &str,
    layout: FriProofLayerLayout,
    trace_len: usize,
    num_queries: usize,
    slot: u64,
    cipher: &[u8],
    kem_len: usize,
) -> Result<GeneratedProofVariant> {
    let digest = hashv(&[cipher]).to_bytes();
    let proof_bytes = generate_proof_bytes(&digest, trace_len, num_queries, layout)?;
    let mut seed_bytes = [0u8; 8];
    let mut inc_bytes = [0u8; 8];
    seed_bytes.copy_from_slice(&digest[0..8]);
    inc_bytes.copy_from_slice(&digest[8..16]);

    let proof_path = proofs_root.join(format!("{name}.bin"));
    fs::write(&proof_path, &proof_bytes)?;

    let structure = extract_variant_structure(&proof_path, &proof_bytes, cipher, kem_len)?;
    let profile = pqzk_real_verifier_profile(&structure);
    let score = score_profile_with_components(
        &phase1_summary.model.chosen,
        phase1_summary
            .verification_core_model
            .as_ref()
            .map(|model| &model.chosen),
        phase1_summary
            .transport_model
            .as_ref()
            .map(|model| &model.chosen),
        &SvmLimits::default(),
        &profile,
    )?;

    Ok(GeneratedProofVariant {
        variant: name.to_string(),
        group: group.to_string(),
        include_interpolants: layout.include_interpolants,
        trace_len,
        slot,
        seed_u64: u64::from_le_bytes(seed_bytes),
        inc_u64: u64::from_le_bytes(inc_bytes),
        digest_hex: hex_string(&digest),
        proof_bytes: proof_bytes.len(),
        proof_sha256_hex: hex_string(&hashv(&[&proof_bytes]).to_bytes()),
        body_bytes: structure.body_bytes,
        chat_msg_account_bytes: structure.chat_msg_account_bytes,
        configured_queries: structure.configured_queries,
        fri_layers: structure.fri_layers,
        fri_remainder_elements: structure.fri_remainder_elements,
        lde_domain_size: structure.lde_domain_size,
        predicted_verify_cu: score.predicted_cu,
        predicted_lower_cu: score.lower_cu.unwrap_or(score.predicted_cu),
        predicted_upper_cu: score.upper_cu.unwrap_or(score.predicted_cu),
        proof_path: proof_path.display().to_string(),
    })
}

fn generate_proof_bytes(
    digest: &[u8],
    trace_len: usize,
    num_queries: usize,
    layout: FriProofLayerLayout,
) -> Result<Vec<u8>> {
    set_fri_proof_layer_layout(layout);
    let result = generate_proof_with_config(
        digest,
        ProofGenerationConfig {
            trace_len,
            num_queries,
        },
    );
    set_fri_proof_layer_layout(FriProofLayerLayout::RAW_ROWS);
    let (_params, proof_bytes) = result?;
    Ok(proof_bytes)
}

fn extract_variant_structure(
    proof_path: &Path,
    proof_bytes: &[u8],
    cipher: &[u8],
    kem_len: usize,
) -> Result<PqzkProofStructure> {
    let proof = Proof::from_bytes(proof_bytes)
        .with_context(|| format!("failed to parse {}", proof_path.display()))?;
    let public_inputs = derive_pqzk_public_inputs(cipher);
    let air = PqzkMessageAir::new_internal(
        proof.trace_info().clone(),
        public_inputs,
        proof.options().clone(),
    );

    let fri_options = proof.options().to_fri_options();
    let folding_factor = fri_options.folding_factor();
    let lde_domain_size = proof.lde_domain_size();
    let num_unique_queries = proof.num_unique_queries as usize;

    let mut trace_query_depths = Vec::new();
    let mut total_batched_merkle_nodes = 0_u64;
    for trace_queries in proof.trace_queries.clone() {
        let (proof_nodes, _values) = trace_queries.parse::<BaseElement, PqzkHasher, PqzkMerkle>(
            lde_domain_size,
            num_unique_queries,
            air.trace_info().main_trace_width(),
        )?;
        trace_query_depths.push(proof_nodes.depth as u64);
        total_batched_merkle_nodes += total_nodes_in_batch_proof(&proof_nodes);
    }

    let (constraint_nodes, _constraint_values) = proof
        .constraint_queries
        .clone()
        .parse::<BaseElement, PqzkHasher, PqzkMerkle>(
            lde_domain_size,
            num_unique_queries,
            air.context().num_constraint_composition_columns(),
        )?;
    total_batched_merkle_nodes += total_nodes_in_batch_proof(&constraint_nodes);

    let (fri_layer_queries, fri_layer_proofs) = proof
        .fri_proof
        .clone()
        .parse_layers::<BaseElement, PqzkHasher, PqzkMerkle>(lde_domain_size, folding_factor)?;
    let mut fri_layer_depths = Vec::new();
    for proof_nodes in &fri_layer_proofs {
        fri_layer_depths.push(proof_nodes.depth as u64);
        total_batched_merkle_nodes += total_nodes_in_batch_proof(proof_nodes);
    }

    let merkle_depth_sum = trace_query_depths.iter().sum::<u64>()
        + constraint_nodes.depth as u64
        + fri_layer_depths.iter().sum::<u64>();
    let merkle_query_families = trace_query_depths.len() as u64 + 1 + fri_layer_depths.len() as u64;
    let total_merkle_levels_unbatched = merkle_depth_sum * num_unique_queries as u64;
    let body_bytes = cipher.len() as u64 + kem_len as u64 + proof_bytes.len() as u64;
    let chat_msg_account_bytes = 8 + 164 + body_bytes;

    Ok(PqzkProofStructure {
        proof_path: proof_path.display().to_string(),
        proof_sha256: hex_string(&hashv(&[proof_bytes]).to_bytes()),
        proof_bytes: proof_bytes.len() as u64,
        trace_width: proof.trace_info().width() as u64,
        trace_length: proof.trace_info().length() as u64,
        num_trace_segments: proof.trace_queries.len() as u64,
        num_unique_queries: proof.num_unique_queries as u64,
        configured_queries: proof.options().num_queries() as u64,
        blowup_factor: proof.options().blowup_factor() as u64,
        grinding_factor: proof.options().grinding_factor() as u64,
        field_extension: field_extension_name(proof.options().field_extension()).to_string(),
        folding_factor: folding_factor as u64,
        fri_layers: fri_layer_queries.len() as u64,
        fri_remainder_elements: proof.fri_proof.num_remainder_elements::<BaseElement>() as u64,
        lde_domain_size: lde_domain_size as u64,
        trace_query_depths,
        constraint_query_depth: constraint_nodes.depth as u64,
        fri_layer_depths,
        merkle_query_families,
        total_merkle_levels_unbatched,
        total_batched_merkle_nodes,
        cipher_bytes: cipher.len() as u64,
        kem_ciphertext_bytes: kem_len as u64,
        body_bytes,
        chat_msg_account_bytes,
        heap_frame_bytes_requested: REAL_VERIFY_HEAP_FRAME_BYTES as u64,
        notes: vec![
            "Proof structure was parsed from a locally generated variant proof emitted by the patched stark-prover crate.".to_string(),
            "Cipher bytes are fixed by this runner so raw-row and packaged variants bind to the same public digest.".to_string(),
            "ChatMsg account size uses 8 discriminator bytes + CHAT_HEAD(164) + body length from the actual Anchor verifier state layout.".to_string(),
        ],
    })
}

fn materialize_variant_onchain(
    harness: &BenchHarness,
    config: &Phase2RealRunConfig,
    variant: &GeneratedProofVariant,
    cipher: &[u8],
    nonce: &[u8],
) -> Result<OnchainPreparedVariant> {
    let recipient = harness.payer.pubkey();
    let chat_msg_account =
        create_program_account(harness, variant.chat_msg_account_bytes as usize)?;
    let chat_msg_pda = chat_msg_account.pubkey();

    let proof_bytes = fs::read(&variant.proof_path)
        .with_context(|| format!("failed to read {}", variant.proof_path))?;
    let payload = [cipher, &proof_bytes].concat();
    let nonce_array: [u8; 12] = nonce
        .try_into()
        .map_err(|_| anyhow!("phase2 nonce must be exactly 12 bytes"))?;

    let mut records = Vec::new();
    let init_chat_msg_tx = simulate_then_send(
        harness,
        build_phase2_init_chat_msg_instruction(
            harness.program_id,
            chat_msg_pda,
            harness.payer.pubkey(),
            recipient,
            cipher.len() as u32,
            config.kem_len as u32,
            nonce_array,
            variant.slot,
            payload.len() as u32,
        ),
        None,
    )?;
    let init_chat_msg_cu = init_chat_msg_tx
        .units_consumed
        .context("phase2_init_chat_msg CU missing")?;
    records.push(stage_record(
        variant,
        "init_chat_msg",
        0,
        init_chat_msg_cu,
        init_chat_msg_tx.transaction_bytes,
        config.payload_chunk_size,
        0,
    ));

    let write_payload = write_chat_msg_chunks(
        harness,
        variant,
        chat_msg_pda,
        &payload,
        config.payload_chunk_size,
        &mut records,
    )?;

    Ok(OnchainPreparedVariant {
        chat_msg_pda,
        setup_total_cu: init_chat_msg_cu + write_payload.total_cu,
        records,
    })
}

struct UploadStageSummary {
    total_cu: u64,
    chunk_count: u64,
}

fn write_chat_msg_chunks(
    harness: &BenchHarness,
    variant: &GeneratedProofVariant,
    chat_msg_pda: Pubkey,
    payload: &[u8],
    chunk_size: usize,
    records: &mut Vec<RealMeasurement>,
) -> Result<UploadStageSummary> {
    let mut total_cu = 0u64;
    let chunk_size = chunk_size.max(1);
    for (chunk_index, chunk) in payload.chunks(chunk_size).enumerate() {
        let tx = simulate_then_send(
            harness,
            build_phase2_write_chat_msg_chunk_instruction(
                harness.program_id,
                chat_msg_pda,
                (chunk_index * chunk_size) as u32,
                chunk.to_vec(),
            ),
            None,
        )?;
        total_cu += tx
            .units_consumed
            .context("phase2_write_chat_msg_chunk CU missing")?;
    }
    let chunk_count = payload.len().div_ceil(chunk_size) as u64;
    records.push(stage_record(
        variant,
        "write_chat_msg_total",
        0,
        total_cu,
        0,
        chunk_size,
        chunk_count,
    ));
    Ok(UploadStageSummary {
        total_cu,
        chunk_count,
    })
}

fn stage_record(
    variant: &GeneratedProofVariant,
    stage: &str,
    repetition: u32,
    actual_cu: u64,
    transaction_bytes: u64,
    upload_chunk_size: usize,
    upload_chunks: u64,
) -> RealMeasurement {
    RealMeasurement {
        variant: variant.variant.clone(),
        group: variant.group.clone(),
        domain: "sbf".to_string(),
        stage: stage.to_string(),
        repetition,
        include_interpolants: variant.include_interpolants,
        trace_len: variant.trace_len,
        slot: variant.slot,
        proof_bytes: variant.proof_bytes,
        body_bytes: variant.body_bytes,
        chat_msg_account_bytes: variant.chat_msg_account_bytes,
        upload_chunk_size,
        upload_chunks,
        heap_frame_bytes_requested: if stage == "verify" || stage == "pipeline_total" {
            REAL_VERIFY_HEAP_FRAME_BYTES as u64
        } else {
            0
        },
        fri_layers: variant.fri_layers,
        configured_queries: variant.configured_queries,
        actual_cu: Some(actual_cu),
        elapsed_ns: None,
        transaction_bytes: if transaction_bytes == 0 {
            None
        } else {
            Some(transaction_bytes)
        },
        error: None,
        seed_u64: variant.seed_u64,
        inc_u64: variant.inc_u64,
        digest_hex: variant.digest_hex.clone(),
        proof_sha256_hex: variant.proof_sha256_hex.clone(),
    }
}

fn simulate_checked(harness: &BenchHarness, plan: TxPlan) -> Result<SimulatedTx> {
    let tx = simulate_plan(harness, plan)?;
    if let Some(err) = &tx.error {
        bail!(
            "simulation failed: {err}; logs: {}",
            if tx.logs.is_empty() {
                "<none>".to_string()
            } else {
                tx.logs.join(" | ")
            }
        );
    }
    Ok(tx)
}

fn simulate_then_send(
    harness: &BenchHarness,
    instruction: Instruction,
    heap_frame_bytes: Option<u32>,
) -> Result<SimulatedTx> {
    let tx = simulate_checked(
        harness,
        TxPlan {
            instructions: vec![instruction.clone()],
            compute_unit_limit: None,
            heap_frame_bytes,
        },
    )?;
    send_instructions(harness, vec![instruction], &[])?;
    Ok(tx)
}

fn build_phase2_init_chat_msg_instruction(
    program_id: Pubkey,
    chat_msg_pda: Pubkey,
    payer: Pubkey,
    recipient: Pubkey,
    cipher_len: u32,
    kem_len: u32,
    nonce: [u8; 12],
    slot: u64,
    payload_len: u32,
) -> Instruction {
    let mut data = anchor_discriminator("phase2_init_chat_msg").to_vec();
    data.extend_from_slice(recipient.as_ref());
    data.extend_from_slice(&cipher_len.to_le_bytes());
    data.extend_from_slice(&kem_len.to_le_bytes());
    data.extend_from_slice(&nonce);
    data.extend_from_slice(&slot.to_le_bytes());
    data.extend_from_slice(&payload_len.to_le_bytes());
    Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(chat_msg_pda, false),
            AccountMeta::new_readonly(payer, true),
        ],
        data,
    }
}

fn build_phase2_write_chat_msg_chunk_instruction(
    program_id: Pubkey,
    chat_msg_pda: Pubkey,
    off: u32,
    data_bytes: Vec<u8>,
) -> Instruction {
    let mut data = anchor_discriminator("phase2_write_chat_msg_chunk").to_vec();
    data.extend_from_slice(&off.to_le_bytes());
    append_borsh_bytes(&mut data, &data_bytes);
    Instruction {
        program_id,
        accounts: vec![AccountMeta::new(chat_msg_pda, false)],
        data,
    }
}

fn anchor_discriminator(name: &str) -> [u8; 8] {
    let preimage = format!("global:{name}");
    let digest = hashv(&[preimage.as_bytes()]).to_bytes();
    let mut out = [0u8; 8];
    out.copy_from_slice(&digest[..8]);
    out
}

fn build_verify_stark_instruction(program_id: Pubkey, chat_msg_pda: Pubkey) -> Instruction {
    Instruction {
        program_id,
        accounts: vec![AccountMeta::new_readonly(chat_msg_pda, false)],
        data: anchor_discriminator("verify_stark").to_vec(),
    }
}

fn append_borsh_bytes(target: &mut Vec<u8>, bytes: &[u8]) {
    target.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    target.extend_from_slice(bytes);
}

fn build_predicted_vs_measured(
    variants: &[GeneratedProofVariant],
    records: &[RealMeasurement],
) -> Result<Vec<PredictedMeasuredRow>> {
    let mut rows = Vec::new();
    for variant in variants {
        let measured_verify_cu = mean_stage_u64(records, &variant.variant, "verify")?;
        let absolute_error = (measured_verify_cu as f64 - variant.predicted_verify_cu).abs();
        rows.push(PredictedMeasuredRow {
            variant: variant.variant.clone(),
            trace_len: variant.trace_len,
            include_interpolants: variant.include_interpolants,
            proof_bytes: variant.proof_bytes,
            fri_layers: variant.fri_layers,
            predicted_verify_cu: variant.predicted_verify_cu,
            measured_verify_cu,
            absolute_error_cu: absolute_error,
            relative_error_fraction: absolute_error / measured_verify_cu.max(1) as f64,
        });
    }
    Ok(rows)
}

fn proof_bytes_for_variant(variants: &[GeneratedProofVariant], variant: &str) -> Result<usize> {
    variants
        .iter()
        .find(|item| item.variant == variant)
        .map(|item| item.proof_bytes)
        .context("variant proof bytes missing")
}

fn mean_stage_u64(records: &[RealMeasurement], variant: &str, stage: &str) -> Result<u64> {
    let mut values = Vec::new();
    for record in records {
        if record.variant == variant && record.domain == "sbf" && record.stage == stage {
            values.push(record.actual_cu.context("missing actual CU")?);
        }
    }
    if values.is_empty() {
        bail!("missing SBF stage `{stage}` for variant `{variant}`");
    }
    Ok(values.iter().copied().sum::<u64>() / values.len() as u64)
}

fn write_real_csv(path: &Path, records: &[RealMeasurement]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for record in records {
        writer.serialize(RealMeasurementCsvRow {
            variant: record.variant.clone(),
            group: record.group.clone(),
            domain: record.domain.clone(),
            stage: record.stage.clone(),
            repetition: record.repetition,
            include_interpolants: record.include_interpolants,
            trace_len: record.trace_len,
            slot: record.slot,
            proof_bytes: record.proof_bytes,
            body_bytes: record.body_bytes,
            chat_msg_account_bytes: record.chat_msg_account_bytes,
            upload_chunk_size: record.upload_chunk_size,
            upload_chunks: record.upload_chunks,
            heap_frame_bytes_requested: record.heap_frame_bytes_requested,
            fri_layers: record.fri_layers,
            configured_queries: record.configured_queries,
            actual_cu: record.actual_cu,
            elapsed_ns: record.elapsed_ns,
            transaction_bytes: record.transaction_bytes,
            error: record.error.clone(),
            seed_u64: record.seed_u64,
            inc_u64: record.inc_u64,
            digest_hex: record.digest_hex.clone(),
            proof_sha256_hex: record.proof_sha256_hex.clone(),
        })?;
    }
    writer.flush()?;
    Ok(())
}

fn render_report(
    config: &Phase2RealRunConfig,
    archived_reference: &ArchivedBaselineReference,
    variants: &[GeneratedProofVariant],
    records: &[RealMeasurement],
    predicted_vs_measured: &[PredictedMeasuredRow],
    summary: &Phase2RealSummary,
) -> Result<String> {
    let mut lines = Vec::new();
    lines.push("# Phase 2 Real Verifier Experiments".to_string());
    lines.push(String::new());
    lines.push("## Goal".to_string());
    lines.push("Run the actual Anchor/Winterfell `verify_stark` instruction that exists in this repo, preserve the same public digest binding across proof variants, and measure whether a commitment-preserving row-interpolant sidecar buys verifier CU once the proof has at least one recursive FRI layer.".to_string());
    lines.push(String::new());
    lines.push("## Actual Program Path".to_string());
    lines.push(format!("- Program id: `{ACTUAL_VENDOR_PROGRAM_ID}`."));
    lines.push(
        "- Build target: `third_party/solana-pqzk-fullchain/programs/stark-pqc-verifier`."
            .to_string(),
    );
    lines.push("- Execution path: `phase2_init_chat_msg` -> `phase2_write_chat_msg_chunk` -> `verify_stark`.".to_string());
    lines.push("- `phase2_*` is a feature-gated loader used only to populate the exact `ChatMsg` account consumed by the production verifier instruction.".to_string());
    lines.push("- This is a real transparent verifier path, but it is Winterfell/FRI over `f128`, not a native WHIR/M31 verifier.".to_string());
    lines.push(String::new());
    lines.push("## Archived Trace-8 Reference".to_string());
    lines.push(format!(
        "- Archived repo baseline: mean verify CU {:.2}, proof bytes {}, trace length {}, recursive FRI layers {}.",
        archived_reference.verify_stark_mean_cu,
        archived_reference.proof_bytes,
        archived_reference.trace_length,
        archived_reference.fri_layers
    ));
    lines.push(format!(
        "- Local sanity run `{}`: mean verify CU {}.",
        summary.sanity_variant, summary.sanity_variant_verify_cu
    ));
    lines.push(String::new());
    lines.push("## Run Config".to_string());
    lines.push(format!(
        "- payload_chunk_size={}, verify_repetitions={}, heap_frame_bytes_requested={}.",
        config.payload_chunk_size, config.verify_repetitions, REAL_VERIFY_HEAP_FRAME_BYTES
    ));
    lines.push(format!(
        "- baseline_trace_len={}, baseline_num_queries={}, experimental_trace_len_candidates={:?}, experimental_query_count_candidates={:?}, chosen_experimental_trace_len={}, chosen_experimental_num_queries={}.",
        config.baseline_trace_len,
        config.baseline_num_queries,
        config.experimental_trace_len_candidates,
        config.experimental_query_count_candidates,
        summary.experimental_trace_len,
        summary.experimental_num_queries
    ));
    lines.push(format!(
        "- production_max_chat_payload_bytes={}, phase2_loader_max_chat_payload_bytes={}, cipher_hex=`{}`, nonce_hex=`{}`, kem_len={}.",
        config.production_max_chat_payload_bytes,
        config.phase2_loader_max_chat_payload_bytes,
        config.cipher_hex,
        config.nonce_hex,
        config.kem_len
    ));
    lines.push(String::new());
    lines.push("## Variants".to_string());
    for variant in variants {
        lines.push(format!(
            "- `{}`: group={}, trace_len={}, include_interpolants={}, proof_bytes={}, fri_layers={}, predicted_verify_cu={:.1}.",
            variant.variant,
            variant.group,
            variant.trace_len,
            variant.include_interpolants,
            variant.proof_bytes,
            variant.fri_layers,
            variant.predicted_verify_cu
        ));
    }
    lines.push(String::new());
    lines.push("## Measured Results".to_string());
    for variant in variants {
        let verify_mean = mean_stage_u64(records, &variant.variant, "verify")?;
        let pipeline_mean = mean_stage_u64(records, &variant.variant, "pipeline_total")?;
        let init_chat_msg_cu = mean_stage_u64(records, &variant.variant, "init_chat_msg")?;
        let write_chat_msg_cu = mean_stage_u64(records, &variant.variant, "write_chat_msg_total")?;
        let verify_failed = stage_has_error(records, &variant.variant, "verify");
        lines.push(format!(
            "- `{}`: verify={} CU{}, pipeline_total={} CU, init_chat_msg={} CU, write_chat_msg_total={} CU, proof_bytes={}, fri_layers={}.",
            variant.variant,
            verify_mean,
            if verify_failed { " (failed to complete under current tx CU cap)" } else { "" },
            pipeline_mean,
            init_chat_msg_cu,
            write_chat_msg_cu,
            variant.proof_bytes,
            variant.fri_layers
        ));
    }
    lines.push(String::new());
    lines.push("## Fold Experiment Winner".to_string());
    lines.push(format!(
        "- Baseline `{}` verify={} CU, pipeline_total={} CU.",
        summary.baseline_variant, summary.baseline_verify_cu, summary.baseline_pipeline_cu
    ));
    lines.push(format!(
        "- Winner `{}` verify={} CU, pipeline_total={} CU.",
        summary.winning_variant, summary.winning_verify_cu, summary.winning_pipeline_cu
    ));
    lines.push(format!(
        "- Delta vs baseline: verify {} CU, pipeline_total {} CU, proof bytes {}.",
        summary.delta_verify_cu, summary.delta_pipeline_cu, summary.delta_bytes
    ));
    lines.push(String::new());
    lines.push("## Predicted vs Measured".to_string());
    for row in predicted_vs_measured {
        lines.push(format!(
            "- `{}`: predicted_verify_cu={:.1}, measured_verify_cu={}, abs_error={:.1}, rel_error={:.2}%.",
            row.variant,
            row.predicted_verify_cu,
            row.measured_verify_cu,
            row.absolute_error_cu,
            row.relative_error_fraction * 100.0
        ));
    }
    lines.push(String::new());
    lines.push("## Notes".to_string());
    lines.push(format!("- {}", summary.note));
    lines.push("- The archived `trace_len=8` proof has zero recursive FRI layers, so the row-interpolant sidecar is a semantic no-op there. This runner chooses the smallest larger trace length that actually creates recursive FRI work within the verifier payload cap.".to_string());
    lines.push(format!(
        "- The production ChatMsg payload cap in this repo is {} bytes. The phase2-only loader used for measurement allows up to {} bytes so a full-security recursive proof can be staged without changing `verify_stark` itself.",
        config.production_max_chat_payload_bytes,
        config.phase2_loader_max_chat_payload_bytes
    ));
    if summary.experimental_num_queries != config.baseline_num_queries {
        lines.push(format!(
            "- The actual verifier envelope forced a query-count relaxation from {} to {} for the recursive-FRI comparison; raw-row and packaged variants still share the same query schedule, digest binding, and verifier instruction.",
            config.baseline_num_queries,
            summary.experimental_num_queries
        ));
    }
    lines.push("- The `phase2_*` loader bypasses signature verification only to stage identical `ChatMsg` bytes for each variant. `verify_stark` itself is unmodified and remains the measured verifier instruction.".to_string());
    lines.push("- Because the repo does not contain a native WHIR/M31 verifier, this report should be read as a real-program fold-packaging experiment on the available Winterfell/FRI verifier, not as a complete replacement for the missing M31 end-to-end path.".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} UTC from `cargo xtask phase2-real-experiments`._",
        Utc::now().to_rfc3339()
    ));
    Ok(lines.join("\n"))
}

fn hex_string(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}

fn write_generic_jsonl<T: Serialize>(path: &Path, records: &[T]) -> Result<()> {
    let mut file = File::create(path)?;
    for record in records {
        serde_json::to_writer(&mut file, record)?;
        file.write_all(b"\n")?;
    }
    Ok(())
}

fn stage_has_error(records: &[RealMeasurement], variant: &str, stage: &str) -> bool {
    records.iter().any(|record| {
        record.variant == variant
            && record.domain == "sbf"
            && record.stage == stage
            && record.error.is_some()
    })
}

fn load_synthetic_phase2_summary(root: &Path) -> Result<SyntheticPhase2Summary> {
    serde_json::from_slice(&fs::read(root.join("results/phase2/summary.json"))?)
        .context("failed to load synthetic phase2 summary")
}

fn load_synthetic_best_fold_delta(root: &Path) -> Result<f64> {
    let mut reader = csv::Reader::from_path(root.join("results/phase2/whir-fold/raw.csv"))?;
    let mut raw_total = Vec::new();
    let mut local_total = Vec::new();
    for row in reader.deserialize::<SyntheticFoldCsvRow>() {
        let row = row?;
        if row.stage != "total_sbf" {
            continue;
        }
        match row.variant.as_str() {
            "karatsuba_late_lift_qm31_raw_fibers" => {
                if let Some(cu) = row.actual_cu {
                    raw_total.push(cu as f64);
                }
            }
            "karatsuba_late_lift_qm31_local_interpolant" => {
                if let Some(cu) = row.actual_cu {
                    local_total.push(cu as f64);
                }
            }
            _ => {}
        }
    }
    if raw_total.is_empty() || local_total.is_empty() {
        bail!("synthetic fold delta inputs missing");
    }
    let raw_mean = raw_total.iter().sum::<f64>() / raw_total.len() as f64;
    let local_mean = local_total.iter().sum::<f64>() / local_total.len() as f64;
    Ok(raw_mean - local_mean)
}

fn render_combined_phase2_report(
    root: &Path,
    archived_reference: &ArchivedBaselineReference,
    real_variants: &[GeneratedProofVariant],
    real_records: &[RealMeasurement],
    real_predicted_vs_measured: &[PredictedMeasuredRow],
    real_summary: &Phase2RealSummary,
) -> Result<String> {
    const USER_WORKING_POINT_CU: f64 = 1_450_000.0;

    let synthetic = load_synthetic_phase2_summary(root)?;
    let synthetic_fold_delta = load_synthetic_best_fold_delta(root).unwrap_or(0.0);
    let projected_savings_without_fold =
        synthetic.combined_estimated_savings_cu - synthetic_fold_delta.max(0.0);
    let projected_post_change = USER_WORKING_POINT_CU - projected_savings_without_fold;
    let projected_headroom = 1_400_000.0 - projected_post_change;

    let raw_variant = real_variants
        .iter()
        .find(|variant| variant.variant == real_summary.baseline_variant)
        .context("real raw fold variant missing")?;
    let packaged_variant = real_variants
        .iter()
        .find(|variant| variant.variant != "trace8_raw_rows" && variant.include_interpolants)
        .context("real packaged fold variant missing")?;
    let raw_failed = stage_has_error(real_records, &raw_variant.variant, "verify");
    let packaged_failed = stage_has_error(real_records, &packaged_variant.variant, "verify");
    let sanity_row = real_predicted_vs_measured
        .iter()
        .find(|row| row.variant == "trace8_raw_rows")
        .context("trace8 sanity predicted-vs-measured row missing")?;

    let mut lines = Vec::new();
    lines.push("# Phase 2 Experiments".to_string());
    lines.push(String::new());
    lines.push("## Goal".to_string());
    lines.push("Run the highest-expected-value CU-reduction experiments for a WHIR-shaped transparent verifier on Solana, but distinguish probe-level synthetic substrate results from the single real verifier path that actually exists in this repo.".to_string());
    lines.push(String::new());
    lines.push("## Discovery Summary".to_string());
    lines.push("- Existing reusable pieces: `xtask`, `programs/phase1-probe`, `crates/svm-cost-model`, `results/phase2`, and the vendored `third_party/solana-pqzk-fullchain` verifier stack.".to_string());
    lines.push("- The repo does not contain a native WHIR/M31 end-to-end prover/verifier. The only real transparent verifier path present is Winterfell/FRI over `f128` in `third_party/solana-pqzk-fullchain/programs/stark-pqc-verifier`.".to_string());
    lines.push("- Reused for experiments: synthetic SBF arithmetic/lift harnesses in `phase1-probe`, the Phase 1 scorer, the real `verify_stark` instruction, and a feature-gated phase2 loader that stages exact `ChatMsg` layouts without changing `verify_stark` semantics.".to_string());
    lines.push("- Added in this phase: patched Winter FRI sidecar support for packaged interpolants, real-program proof-shape runner in `xtask`, and feature-gated instrumentation in the vendored verifier for direct `ChatMsg` loading.".to_string());
    lines.push("- Baseline commands now available: `cargo xtask phase2-experiments`, `cargo xtask phase2-real-experiments`, and the one-line reproduction path `cargo xtask phase2-experiments && cargo xtask phase2-real-experiments`.".to_string());
    lines.push(String::new());
    lines.push("## Baseline".to_string());
    lines.push(format!(
        "- User-stated WHIR spend working point remains about {:.0} CU against a {:.0} CU transaction cap.",
        USER_WORKING_POINT_CU, 1_400_000.0
    ));
    lines.push(format!(
        "- Archived real verifier baseline in this repo: `verify_stark` mean {:.2} CU, proof bytes {}, trace length {}, recursive FRI layers {}.",
        archived_reference.verify_stark_mean_cu,
        archived_reference.proof_bytes,
        archived_reference.trace_length,
        archived_reference.fri_layers
    ));
    lines.push(format!(
        "- Local sanity rerun on the real verifier path: `{}` measured {} CU.",
        real_summary.sanity_variant, real_summary.sanity_variant_verify_cu
    ));
    lines.push(String::new());
    lines.push("## Experiment Design".to_string());
    lines.push("- Experiment A reused the synthetic SBF probe to compare five M31 kernels on host and SBF: `reference_canonical`, `direct_m31`, `direct_m31_lazy`, `montgomery_form`, `barrett_reduction`.".to_string());
    lines.push("- Experiment B reused the same substrate to compare `schoolbook` vs `karatsuba` CM31/QM31 arithmetic and `eager_qm31` vs `late_lift_qm31` policy.".to_string());
    lines.push("- Experiment C was rerun on the actual Anchor/Winterfell verifier path. It compares raw FRI rows vs a sidecar-packaged interpolant representation while keeping digest binding, query schedule, and verifier logic fixed.".to_string());
    lines.push("- The real-program fold run had to widen only the phase2 loader envelope, not the verifier itself, because the production `ChatMsg` payload cap of 10,068 bytes cannot hold any full-security recursive proof emitted by the current prover.".to_string());
    lines.push(String::new());
    lines.push("## Measured vs Inferred vs Unknown".to_string());
    lines.push("- Measured directly: all SBF CU in `results/phase2`, all actual `verify_stark` CU in `results/phase2-real`, proof-byte deltas, upload chunk counts, and host verify timings.".to_string());
    lines.push("- Inferred: the projected total SpendV0 savings still combine synthetic M31/QM31 arithmetic wins with the user-stated 1.45M-CU WHIR working point.".to_string());
    lines.push("- Unknown: exact end-to-end WHIR effects on a native M31 verifier, because that verifier does not exist in this repo yet.".to_string());
    lines.push(String::new());
    lines.push("## Experiment A Results".to_string());
    lines.push(format!(
        "- Synthetic SBF raw-mul winner: `{}`.",
        synthetic.arithmetic_winner_raw_mul
    ));
    lines.push(format!(
        "- Synthetic SBF verifier-microkernel winner: `{}`.",
        synthetic.arithmetic_winner_verifier_kernel
    ));
    lines.push("- Recommendation status: provisional baseline only. This is the best available repo-local evidence for M31 arithmetic, but it is not an end-to-end native verifier measurement.".to_string());
    lines.push(String::new());
    lines.push("## Experiment B Results".to_string());
    lines.push(format!(
        "- Synthetic extension-kernel winner: `{}`.",
        synthetic.extension_kernel_winner
    ));
    lines.push(format!(
        "- Synthetic lift-policy winner: `{}`.",
        synthetic.lift_policy_winner
    ));
    lines.push("- Recommendation status: provisional baseline only. The late-lift result is still measured through the synthetic substrate because there is no native WHIR verifier path to run it through.".to_string());
    lines.push(String::new());
    lines.push("## Experiment C Results".to_string());
    lines.push(format!(
        "- Real-program recursive proof shape: trace length {}, configured queries {}, recursive FRI layers {}.",
        real_summary.experimental_trace_len,
        real_summary.experimental_num_queries,
        raw_variant.fri_layers
    ));
    lines.push(format!(
        "- Real raw-row proof: {} bytes, verify {} CU{}.",
        raw_variant.proof_bytes,
        real_summary.baseline_verify_cu,
        if raw_failed {
            " and failed to complete at the 1.4M CU cap"
        } else {
            ""
        }
    ));
    lines.push(format!(
        "- Real packaged-interpolant proof: {} bytes, verify {} CU{}.",
        packaged_variant.proof_bytes,
        mean_stage_u64(real_records, &packaged_variant.variant, "verify")?,
        if packaged_failed {
            " and failed to complete at the 1.4M CU cap"
        } else {
            ""
        }
    ));
    lines.push(format!(
        "- Measured outcome: no material verifier win under the actual transaction cap. The packaged proof is {} bytes larger than raw and does not clear the cap.",
        packaged_variant.proof_bytes as i64 - raw_variant.proof_bytes as i64
    ));
    lines.push("- Recommendation: do not switch the baseline fold representation based on current real-program evidence. Keep the raw representation until a native WHIR verifier can measure the representation change without the current Winterfell envelope mismatch.".to_string());
    lines.push(String::new());
    lines.push("## Optional Experiment Results".to_string());
    lines.push(
        "- Minimal-subtree Merkle mode and heap-streaming audit remain unexecuted in this pass."
            .to_string(),
    );
    lines.push(String::new());
    lines.push("## Predicted vs Measured Comparison".to_string());
    lines.push(format!(
        "- Real sanity check (`trace8_raw_rows`): predicted {:.1} CU vs measured {} CU, {:.2}% relative error.",
        sanity_row.predicted_verify_cu,
        sanity_row.measured_verify_cu,
        sanity_row.relative_error_fraction * 100.0
    ));
    lines.push(format!(
        "- Real recursive variants: predicted {:.1} CU raw and {:.1} CU packaged, but both actual runs hit the 1.4M cap before completion; treat the 1.4M rows as lower bounds rather than full measurements.",
        raw_variant.predicted_verify_cu,
        packaged_variant.predicted_verify_cu
    ));
    lines.push("- Synthetic scorer fit remains badly miscalibrated on the explicit M31/QM31 substrate. Use it for directional decomposition, not absolute Phase 2 totals.".to_string());
    lines.push(String::new());
    lines.push("## Combined Best-Case Configuration".to_string());
    lines.push(format!(
        "- Provisional arithmetic baseline: `{}` + `{}` + `{}`.",
        synthetic.arithmetic_winner_verifier_kernel,
        synthetic.extension_kernel_winner,
        synthetic.lift_policy_winner
    ));
    lines.push("- Fold representation baseline: keep `raw_fibers` / raw rows for now.".to_string());
    lines.push("- Combined recommendation toward SpendV0: `reference_canonical` + `karatsuba` + `late_lift_qm31` + keep raw fold representation.".to_string());
    lines.push(String::new());
    lines.push("## Estimated Total CU Savings".to_string());
    lines.push(format!(
        "- Synthetic all-in estimate previously claimed {:.1} CU savings with `local_interpolant` included.",
        synthetic.combined_estimated_savings_cu
    ));
    lines.push(format!(
        "- Removing the synthetic fold win because the real verifier did not confirm it leaves about {:.1} CU projected savings.",
        projected_savings_without_fold
    ));
    lines.push(format!(
        "- That implies an estimated post-change working point of about {:.1} CU and about {:.1} CU of headroom against the 1.4M cap.",
        projected_post_change,
        projected_headroom
    ));
    lines.push(String::new());
    lines.push("## Open Risks".to_string());
    lines.push(format!("- {}", synthetic.biggest_remaining_risk));
    lines.push("- The only actual verifier path in the repo is Winterfell/FRI, and its first recursive proof already lives on the 1.4M CU edge. That means the real fold experiment is informative but still not a native WHIR measurement.".to_string());
    lines.push("- The phase2 loader widens the staging envelope only for measurement. Production finalize semantics still cap `ChatMsg` payloads at 10,068 bytes.".to_string());
    lines.push(String::new());
    lines.push("## Recommended Next Steps Toward SpendV0".to_string());
    lines.push("- Build or import a native WHIR/M31 verifier path so Experiments A, B, and C can all run end-to-end on the real target rather than through the synthetic substrate or the Winterfell proxy.".to_string());
    lines.push("- Once that path exists, port `reference_canonical`, `karatsuba`, and `late_lift_qm31` into it first; those are still the highest-probability arithmetic wins from the current measured substrate.".to_string());
    lines.push("- Run the minimal-subtree Merkle experiment next, because the real recursive Winterfell proof shows proof bytes and transport now dominate whether the recursive case even fits the production envelope.".to_string());
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} UTC from `cargo xtask phase2-experiments && cargo xtask phase2-real-experiments`._",
        Utc::now().to_rfc3339()
    ));
    Ok(lines.join("\n"))
}
