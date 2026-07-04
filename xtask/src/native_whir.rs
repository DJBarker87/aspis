use super::*;
use anyhow::{anyhow, bail, Context, Result};
use serde::Serialize;
use whir_m31_core::{
    profile::{profile_manifest, ProfileId, WhirProfileManifest},
    proof::HEADER_BYTES as PROOF_HEADER_BYTES,
    statement::SpendV0Binding,
};
use whir_m31_host::{deterministic_witness, prove, verify};
use whir_m31_verifier::{
    build_init_upload_instruction, build_upload_chunk_instruction, build_verify_instruction,
    id as whir_program_id, UPLOAD_HEADER_BYTES,
};

#[derive(Clone, Debug, Serialize)]
struct ManifestRecord {
    id: u16,
    name: String,
    proof_version: u16,
    statement_binding_version: u16,
    log_num_rows: u8,
    fold_vars_per_round: u8,
    round_count: usize,
    query_repetitions_per_round: u8,
    query_pow_bits: u8,
    target_security_bits: u16,
    heap_frame_bytes: u32,
    upload_chunk_bytes: u16,
    max_compute_units_per_tx: u64,
    max_transaction_bytes: u64,
    min_heap_frame_bytes: u64,
    max_heap_frame_bytes: u64,
    heap_page_bytes: u64,
    stack_frame_bytes: u64,
}

#[derive(Clone, Debug, Serialize)]
struct HostRecord {
    profile: String,
    stage: String,
    success: bool,
    elapsed_ns: Option<u128>,
    proof_bytes: Option<usize>,
    error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct OnchainRecord {
    profile: String,
    stage: String,
    success: bool,
    actual_cu: Option<u64>,
    transaction_bytes: Option<u64>,
    upload_chunks: u64,
    heap_frame_bytes_requested: u64,
    error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct CorruptionRecord {
    profile: String,
    mutation: String,
    host_rejected: bool,
    onchain_rejected: bool,
    onchain_error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct ProfileSummary {
    profile: String,
    executed: bool,
    proof_bytes: Option<usize>,
    proof_path: Option<String>,
    host_prove_ns: Option<u128>,
    host_verify_ok: bool,
    onchain_verify_ok: Option<bool>,
    onchain_verify_cu: Option<u64>,
    upload_chunks: Option<u64>,
    upload_total_cu: Option<u64>,
    heap_frame_bytes_requested: u64,
    error: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct NativeWhirSummary {
    generated_at_utc: String,
    command: String,
    versions: VersionManifest,
    raw_artifacts: Vec<String>,
    proof_profiles: Vec<String>,
    dev_profile: ProfileSummary,
    target_profile: ProfileSummary,
    corruption_tests: Vec<CorruptionRecord>,
    biggest_remaining_risk: String,
    next_steps: Vec<String>,
}

#[derive(Clone)]
struct UploadOutcome {
    total_cu: u64,
    chunks: u64,
}

pub(super) fn run_native_whir_m31() -> Result<()> {
    let root = workspace_root()?;
    let docs_path = root.join("docs/native-whir-m31-v0.md");
    let results_root = root.join("results/native-whir");
    let manifests_root = results_root.join("manifests");
    let proofs_root = results_root.join("proofs");
    let host_root = results_root.join("host");
    let onchain_root = results_root.join("onchain");
    let benches_root = results_root.join("benches");

    if results_root.exists() {
        fs::remove_dir_all(&results_root)?;
    }
    fs::create_dir_all(&manifests_root)?;
    fs::create_dir_all(&proofs_root)?;
    fs::create_dir_all(&host_root)?;
    fs::create_dir_all(&onchain_root)?;
    fs::create_dir_all(&benches_root)?;

    run_checked_cargo_test(&root, &["test", "-p", "whir-m31-core"])?;
    run_checked_cargo_test(&root, &["test", "-p", "whir-m31-host"])?;
    run_checked_cargo_test(
        &root,
        &[
            "test",
            "-p",
            "whir-m31-verifier",
            "--features",
            "no-entrypoint",
        ],
    )?;

    let versions = capture_version_manifest()?;
    write_json(&results_root.join("version_manifest.json"), &versions)?;

    let dev_manifest = profile_manifest(ProfileId::WhirM31DevV0);
    let target_manifest = profile_manifest(ProfileId::WhirM31SolanaV0);
    write_json(
        &manifests_root.join("whir-m31-dev-v0.json"),
        &manifest_record(dev_manifest),
    )?;
    write_json(
        &manifests_root.join("whir-m31-solana-v0.json"),
        &manifest_record(target_manifest),
    )?;

    let program_so = build_whir_m31_program(&root)?;
    let validator =
        start_validator_with_program(&root, &results_root, whir_program_id(), &program_so)?;
    let harness = BenchHarness {
        client: LocalRpcClient::new(validator.rpc_url.clone()),
        payer: Keypair::new(),
        program_id: whir_program_id(),
        limits: SvmLimits::default(),
    };
    fund_payer(&harness)?;

    let mut host_records = Vec::new();
    let mut onchain_records = Vec::new();

    let dev_summary = run_profile(
        &harness,
        dev_manifest,
        &proofs_root,
        &mut host_records,
        &mut onchain_records,
    )?;
    let target_summary = run_profile(
        &harness,
        target_manifest,
        &proofs_root,
        &mut host_records,
        &mut onchain_records,
    )?;

    let corruption_tests = run_corruption_tests(
        &harness,
        dev_manifest,
        &proofs_root.join("whir-m31-dev-v0.bin"),
        &mut onchain_records,
    )?;

    write_jsonl_generic(&host_root.join("raw.jsonl"), &host_records)?;
    write_csv_generic(&host_root.join("raw.csv"), &host_records)?;
    write_json(&host_root.join("records.json"), &host_records)?;

    write_jsonl_generic(&onchain_root.join("raw.jsonl"), &onchain_records)?;
    write_csv_generic(&onchain_root.join("raw.csv"), &onchain_records)?;
    write_json(&onchain_root.join("records.json"), &onchain_records)?;
    write_json(&benches_root.join("corruption.json"), &corruption_tests)?;

    let summary = NativeWhirSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask native-whir-m31".to_string(),
        versions,
        raw_artifacts: vec![
            "results/native-whir/manifests/whir-m31-dev-v0.json".to_string(),
            "results/native-whir/manifests/whir-m31-solana-v0.json".to_string(),
            "results/native-whir/proofs/whir-m31-dev-v0.bin".to_string(),
            "results/native-whir/proofs/whir-m31-solana-v0.bin".to_string(),
            "results/native-whir/host/raw.jsonl".to_string(),
            "results/native-whir/host/raw.csv".to_string(),
            "results/native-whir/onchain/raw.jsonl".to_string(),
            "results/native-whir/onchain/raw.csv".to_string(),
            "results/native-whir/summary.json".to_string(),
            "docs/native-whir-m31-v0.md".to_string(),
        ],
        proof_profiles: vec![
            dev_manifest.name.to_string(),
            target_manifest.name.to_string(),
        ],
        dev_profile: dev_summary,
        target_profile: target_summary,
        corruption_tests: corruption_tests.clone(),
        biggest_remaining_risk:
            "v0 proves transcript-bound local fold consistency for a fixed committed multilinear table, but it is not yet the full WHIR paper path or a full SpendV0 arithmetic relation.".to_string(),
        next_steps: vec![
            "replace the deterministic table witness with the first real SpendV0 arithmetic/witness slice while keeping the same statement binding".to_string(),
            "measure and, if needed, tighten the target profile with a narrower Merkle proof representation once real proof bytes dominate upload cost".to_string(),
            "formalize the v0 soundness delta against the full WHIR protocol and decide which missing checks must land before SpendV0".to_string(),
        ],
    };
    write_json(&results_root.join("summary.json"), &summary)?;
    fs::write(
        &docs_path,
        render_native_whir_report(&summary, dev_manifest, target_manifest),
    )?;

    Ok(())
}

fn run_profile(
    harness: &BenchHarness,
    profile: &'static WhirProfileManifest,
    proofs_root: &Path,
    host_records: &mut Vec<HostRecord>,
    onchain_records: &mut Vec<OnchainRecord>,
) -> Result<ProfileSummary> {
    let binding = sample_binding(profile.id);
    let witness = deterministic_witness(profile, binding.digest());
    let prove_started = Instant::now();
    let prover_output = prove(profile, &binding, &witness)
        .with_context(|| format!("host prover failed for {}", profile.name))?;
    let prove_elapsed = prove_started.elapsed().as_nanos();
    let proof_path = proofs_root.join(format!("{}.bin", profile.name));
    fs::write(&proof_path, &prover_output.proof_bytes)?;
    host_records.push(HostRecord {
        profile: profile.name.to_string(),
        stage: "prove".to_string(),
        success: true,
        elapsed_ns: Some(prove_elapsed),
        proof_bytes: Some(prover_output.proof_bytes.len()),
        error: None,
    });

    let host_verify_ok = match verify(profile, &binding, &prover_output.proof_bytes) {
        Ok(_) => {
            host_records.push(HostRecord {
                profile: profile.name.to_string(),
                stage: "verify".to_string(),
                success: true,
                elapsed_ns: None,
                proof_bytes: Some(prover_output.proof_bytes.len()),
                error: None,
            });
            true
        }
        Err(error) => {
            host_records.push(HostRecord {
                profile: profile.name.to_string(),
                stage: "verify".to_string(),
                success: false,
                elapsed_ns: None,
                proof_bytes: Some(prover_output.proof_bytes.len()),
                error: Some(error.to_string()),
            });
            false
        }
    };

    let upload_account = create_program_account(
        harness,
        UPLOAD_HEADER_BYTES + prover_output.proof_bytes.len(),
    )?;
    let upload = init_and_upload_proof(
        harness,
        upload_account.pubkey(),
        profile,
        &prover_output.proof_bytes,
        onchain_records,
    )?;
    let verify_tx = simulate_then_send_simple(
        harness,
        vec![build_verify_instruction(
            harness.program_id,
            upload_account.pubkey(),
            binding,
        )],
        None,
        Some(profile.heap_frame_bytes),
        true,
    )?;
    let verify_ok = verify_tx.error.is_none();
    onchain_records.push(OnchainRecord {
        profile: profile.name.to_string(),
        stage: "verify".to_string(),
        success: verify_ok,
        actual_cu: verify_tx.units_consumed,
        transaction_bytes: Some(verify_tx.transaction_bytes),
        upload_chunks: upload.chunks,
        heap_frame_bytes_requested: profile.heap_frame_bytes as u64,
        error: verify_tx.error.clone(),
    });

    let verified_flag = harness
        .client
        .get_account_data(&upload_account.pubkey())?
        .and_then(|data| data.get(48).copied())
        .unwrap_or_default();

    Ok(ProfileSummary {
        profile: profile.name.to_string(),
        executed: true,
        proof_bytes: Some(prover_output.proof_bytes.len()),
        proof_path: Some(proof_path.display().to_string()),
        host_prove_ns: Some(prover_output.measurements.total_ns),
        host_verify_ok,
        onchain_verify_ok: Some(verify_ok && verified_flag == 1),
        onchain_verify_cu: verify_tx.units_consumed,
        upload_chunks: Some(upload.chunks),
        upload_total_cu: Some(upload.total_cu),
        heap_frame_bytes_requested: profile.heap_frame_bytes as u64,
        error: verify_tx.error,
    })
}

fn run_corruption_tests(
    harness: &BenchHarness,
    profile: &'static WhirProfileManifest,
    proof_path: &Path,
    onchain_records: &mut Vec<OnchainRecord>,
) -> Result<Vec<CorruptionRecord>> {
    let binding = sample_binding(profile.id);
    let proof_bytes = fs::read(proof_path)?;
    let mut mutations = Vec::new();
    mutations.push((
        "flip_merkle_sibling".to_string(),
        mutate_merkle_sibling(profile, &proof_bytes)?,
    ));
    mutations.push((
        "flip_fold_coefficient".to_string(),
        mutate_fold_coefficient(profile, &proof_bytes)?,
    ));
    mutations.push((
        "flip_query_opening".to_string(),
        mutate_query_opening(profile, &proof_bytes)?,
    ));
    mutations.push((
        "flip_statement_digest".to_string(),
        mutate_statement_digest(&proof_bytes),
    ));

    let mut records = Vec::new();
    for (name, bytes) in mutations {
        let host_rejected = verify(profile, &binding, &bytes).is_err();
        let upload_account = create_program_account(harness, UPLOAD_HEADER_BYTES + bytes.len())?;
        init_and_upload_proof(
            harness,
            upload_account.pubkey(),
            profile,
            &bytes,
            onchain_records,
        )?;
        let simulated = simulate_then_send_simple(
            harness,
            vec![build_verify_instruction(
                harness.program_id,
                upload_account.pubkey(),
                binding,
            )],
            None,
            Some(profile.heap_frame_bytes),
            false,
        )?;
        let onchain_rejected = simulated.error.is_some();
        onchain_records.push(OnchainRecord {
            profile: profile.name.to_string(),
            stage: format!("corruption/{name}"),
            success: false,
            actual_cu: simulated.units_consumed,
            transaction_bytes: Some(simulated.transaction_bytes),
            upload_chunks: bytes.len().div_ceil(profile.upload_chunk_bytes as usize) as u64,
            heap_frame_bytes_requested: profile.heap_frame_bytes as u64,
            error: simulated.error.clone(),
        });
        records.push(CorruptionRecord {
            profile: profile.name.to_string(),
            mutation: name,
            host_rejected,
            onchain_rejected,
            onchain_error: simulated.error,
        });
    }
    Ok(records)
}

fn init_and_upload_proof(
    harness: &BenchHarness,
    upload_account: Pubkey,
    profile: &'static WhirProfileManifest,
    proof_bytes: &[u8],
    onchain_records: &mut Vec<OnchainRecord>,
) -> Result<UploadOutcome> {
    let init_tx = simulate_then_send_simple(
        harness,
        vec![build_init_upload_instruction(
            harness.program_id,
            upload_account,
            profile.id,
            proof_bytes.len(),
        )],
        None,
        None,
        true,
    )?;
    if let Some(error) = &init_tx.error {
        bail!("init upload failed for {}: {error}", profile.name);
    }
    onchain_records.push(OnchainRecord {
        profile: profile.name.to_string(),
        stage: "init_upload".to_string(),
        success: init_tx.error.is_none(),
        actual_cu: init_tx.units_consumed,
        transaction_bytes: Some(init_tx.transaction_bytes),
        upload_chunks: 0,
        heap_frame_bytes_requested: 0,
        error: init_tx.error.clone(),
    });
    let mut total_cu = init_tx.units_consumed.unwrap_or_default();
    let mut prior_digest = [0_u8; 32];
    let mut chunk_count = 0_u64;
    for (chunk_index, chunk) in proof_bytes
        .chunks(profile.upload_chunk_bytes as usize)
        .enumerate()
    {
        let tx = simulate_then_send_simple(
            harness,
            vec![build_upload_chunk_instruction(
                harness.program_id,
                upload_account,
                chunk_index * profile.upload_chunk_bytes as usize,
                prior_digest,
                chunk.to_vec(),
            )],
            None,
            None,
            true,
        )?;
        if let Some(error) = &tx.error {
            bail!(
                "upload chunk {chunk_index} failed for {}: {error}",
                profile.name
            );
        }
        total_cu += tx.units_consumed.unwrap_or_default();
        chunk_count += 1;
        onchain_records.push(OnchainRecord {
            profile: profile.name.to_string(),
            stage: format!("upload_chunk_{chunk_index}"),
            success: tx.error.is_none(),
            actual_cu: tx.units_consumed,
            transaction_bytes: Some(tx.transaction_bytes),
            upload_chunks: 1,
            heap_frame_bytes_requested: 0,
            error: tx.error.clone(),
        });
        prior_digest = hashv(&[&prior_digest, chunk]).to_bytes();
    }
    Ok(UploadOutcome {
        total_cu,
        chunks: chunk_count,
    })
}

fn simulate_then_send_simple(
    harness: &BenchHarness,
    instructions: Vec<Instruction>,
    compute_unit_limit: Option<u32>,
    heap_frame_bytes: Option<u32>,
    send_on_success: bool,
) -> Result<SimulatedTx> {
    let plan = TxPlan {
        instructions: instructions.clone(),
        compute_unit_limit,
        heap_frame_bytes,
    };
    let tx = simulate_plan(harness, plan.clone())?;
    if tx.error.is_none() && send_on_success {
        send_plan(harness, plan, &[])?;
    }
    Ok(tx)
}

fn send_plan(harness: &BenchHarness, plan: TxPlan, additional_signers: &[&Keypair]) -> Result<()> {
    let mut instructions = Vec::new();
    instructions.push(ComputeBudgetInstruction::set_compute_unit_limit(
        plan.compute_unit_limit
            .unwrap_or(harness.limits.max_compute_units_per_tx as u32),
    ));
    if let Some(heap_frame_bytes) = plan.heap_frame_bytes {
        instructions.push(ComputeBudgetInstruction::request_heap_frame(
            heap_frame_bytes,
        ));
    }
    instructions.extend(plan.instructions);

    let recent_blockhash = harness.client.get_latest_blockhash()?;
    let mut signer_refs = vec![&harness.payer];
    signer_refs.extend_from_slice(additional_signers);
    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&harness.payer.pubkey()),
        &signer_refs,
        recent_blockhash,
    );
    harness.client.send_and_confirm_transaction(&tx)?;
    Ok(())
}

fn build_whir_m31_program(root: &Path) -> Result<PathBuf> {
    let out_dir = root.join("target/native-whir-sbf");
    fs::create_dir_all(&out_dir)?;
    let status = Command::new("cargo")
        .arg("build-sbf")
        .arg("--manifest-path")
        .arg(root.join("programs/whir-m31-verifier/Cargo.toml"))
        .arg("--features")
        .arg("instrumentation")
        .arg("--sbf-out-dir")
        .arg(&out_dir)
        .status()
        .context("failed to run cargo build-sbf for whir-m31-verifier")?;
    if !status.success() {
        bail!("cargo build-sbf failed for whir-m31-verifier");
    }
    let so_path = out_dir.join("whir_m31_verifier.so");
    if !so_path.exists() {
        bail!("expected SBF artifact missing at {}", so_path.display());
    }
    Ok(so_path)
}

fn run_checked_cargo_test(root: &Path, args: &[&str]) -> Result<()> {
    let status = Command::new("cargo")
        .args(args)
        .current_dir(root)
        .status()
        .with_context(|| format!("failed to run cargo {}", args.join(" ")))?;
    if !status.success() {
        bail!("cargo {} failed", args.join(" "));
    }
    Ok(())
}

fn manifest_record(profile: &'static WhirProfileManifest) -> ManifestRecord {
    ManifestRecord {
        id: profile.id as u16,
        name: profile.name.to_string(),
        proof_version: profile.proof_version,
        statement_binding_version: profile.statement_binding_version,
        log_num_rows: profile.log_num_rows,
        fold_vars_per_round: profile.fold_vars_per_round,
        round_count: profile.round_count(),
        query_repetitions_per_round: profile.query_repetitions_per_round,
        query_pow_bits: profile.query_pow_bits,
        target_security_bits: profile.target_security_bits,
        heap_frame_bytes: profile.heap_frame_bytes,
        upload_chunk_bytes: profile.upload_chunk_bytes,
        max_compute_units_per_tx: profile.runtime_limits.max_compute_units_per_tx,
        max_transaction_bytes: profile.runtime_limits.max_transaction_bytes,
        min_heap_frame_bytes: profile.runtime_limits.min_heap_frame_bytes,
        max_heap_frame_bytes: profile.runtime_limits.max_heap_frame_bytes,
        heap_page_bytes: profile.runtime_limits.heap_page_bytes,
        stack_frame_bytes: profile.runtime_limits.stack_frame_bytes,
    }
}

fn sample_binding(profile_id: ProfileId) -> SpendV0Binding {
    let tag = profile_id as u8;
    SpendV0Binding::new(
        [tag; 32],
        &[[tag.wrapping_add(1); 32], [tag.wrapping_add(2); 32]],
        &[[tag.wrapping_add(3); 32], [tag.wrapping_add(4); 32]],
        [tag.wrapping_add(5); 32],
        10_000 + tag as u64,
    )
}

fn mutate_merkle_sibling(
    profile: &'static WhirProfileManifest,
    proof_bytes: &[u8],
) -> Result<Vec<u8>> {
    let mut bytes = proof_bytes.to_vec();
    let sibling_offset = PROOF_HEADER_BYTES + (profile.round_count() * 32) + 16 + 16;
    let target = bytes
        .get_mut(sibling_offset)
        .ok_or_else(|| anyhow!("missing merkle sibling byte"))?;
    *target ^= 0x01;
    Ok(bytes)
}

fn mutate_fold_coefficient(
    profile: &'static WhirProfileManifest,
    proof_bytes: &[u8],
) -> Result<Vec<u8>> {
    let mut bytes = proof_bytes.to_vec();
    let offset = PROOF_HEADER_BYTES + (profile.round_count() * 32) + 16;
    let target = bytes
        .get_mut(offset)
        .ok_or_else(|| anyhow!("missing fold coefficient byte"))?;
    *target ^= 0x10;
    Ok(bytes)
}

fn mutate_query_opening(
    profile: &'static WhirProfileManifest,
    proof_bytes: &[u8],
) -> Result<Vec<u8>> {
    let mut bytes = proof_bytes.to_vec();
    let offset = PROOF_HEADER_BYTES + (profile.round_count() * 32) + 16 + 8;
    let target = bytes
        .get_mut(offset)
        .ok_or_else(|| anyhow!("missing query opening byte"))?;
    *target ^= 0x20;
    Ok(bytes)
}

fn mutate_statement_digest(proof_bytes: &[u8]) -> Vec<u8> {
    let mut bytes = proof_bytes.to_vec();
    bytes[20] ^= 0x40;
    bytes
}

fn write_jsonl_generic<T: Serialize>(path: &Path, rows: &[T]) -> Result<()> {
    let mut file = File::create(path)?;
    for row in rows {
        serde_json::to_writer(&mut file, row)?;
        file.write_all(b"\n")?;
    }
    Ok(())
}

fn write_csv_generic<T: Serialize>(path: &Path, rows: &[T]) -> Result<()> {
    let mut writer = Writer::from_path(path)?;
    for row in rows {
        writer.serialize(row)?;
    }
    writer.flush()?;
    Ok(())
}

fn render_native_whir_report(
    summary: &NativeWhirSummary,
    dev: &'static WhirProfileManifest,
    target: &'static WhirProfileManifest,
) -> String {
    let mut lines = Vec::new();
    lines.push("# Native WHIR M31 v0".to_string());
    lines.push(String::new());
    lines.push("## Goal".to_string());
    lines.push("Build a fixed-profile native multilinear opening prover/verifier slice over the M31 -> CM31 -> QM31 tower, with host proving, host verification, and an exact-profile Solana verifier using the SHA-256 syscall path.".to_string());
    lines.push(String::new());
    lines.push("## Discovery Summary".to_string());
    lines.push("- Existing reusable scaffold: `xtask`, `programs/phase1-probe`, `crates/svm-cost-model`, Phase 2 manifests/results, and the vendored `solana-pqzk-fullchain` engineering reference.".to_string());
    lines.push("- Existing reusable logic: validator orchestration, transaction simulation, staged uploads, JSON/CSV writing, and the Phase 2 M31/CM31/QM31 measurement kernels.".to_string());
    lines.push("- Replaced from the proxy path: synthetic proof envelopes, seed-derived statement binding, and synthetic WHIR record layouts.".to_string());
    lines.push(String::new());
    lines.push("## Frozen Scope".to_string());
    lines.push(format!(
        "- Dev profile: `{}` with log_rows={}, rounds={}, q={}, fold_vars={}, heap={} bytes.",
        dev.name,
        dev.log_num_rows,
        dev.round_count(),
        dev.query_repetitions_per_round,
        dev.fold_vars_per_round,
        dev.heap_frame_bytes
    ));
    lines.push(format!(
        "- Target profile: `{}` with log_rows={}, rounds={}, q={}, fold_vars={}, heap={} bytes.",
        target.name,
        target.log_num_rows,
        target.round_count(),
        target.query_repetitions_per_round,
        target.fold_vars_per_round,
        target.heap_frame_bytes
    ));
    lines.push("- Fixed hash mode: SHA-256.".to_string());
    lines.push("- Fixed fold mode: local_interpolant.".to_string());
    lines.push(
        "- Fixed statement binding: SpendV0-shaped anchor/nullifiers/outputs/asset/fee digest."
            .to_string(),
    );
    lines.push(String::new());
    lines.push("## Arithmetic Design".to_string());
    lines.push("- M31 uses direct reduction modulo 2^31 - 1.".to_string());
    lines.push(
        "- CM31 implements both schoolbook and Karatsuba multiplication over x^2 + 1.".to_string(),
    );
    lines.push("- QM31 implements the target quartic tower over u^2 - 2 - i with non-residue (2, 1) in CM31.".to_string());
    lines.push(
        "- The host and verifier default to late-lift evaluation for round-0 M31 blocks."
            .to_string(),
    );
    lines.push(String::new());
    lines.push("## Proof Format".to_string());
    lines.push(
        "- `WhirEnvelopeV1` is fixed-shape for each profile and manually parsed.".to_string(),
    );
    lines.push("- The envelope carries profile id, version fields, statement digest, per-round Merkle roots, the final QM31 value, and per-round query openings.".to_string());
    lines.push("- Merkle proofs are separate-path proofs in v0.".to_string());
    lines.push(String::new());
    lines.push("## Prover Design".to_string());
    lines.push(
        "- The prover commits one Merkle root per folding round over local-interpolant blocks."
            .to_string(),
    );
    lines.push(
        "- Fiat-Shamir transcript challenges are QM31 pairs derived after each round root."
            .to_string(),
    );
    lines.push(
        "- Query indices are derived after all round roots and the final value are absorbed."
            .to_string(),
    );
    lines.push(String::new());
    lines.push("## Verifier Design".to_string());
    lines.push("- The verifier replays the transcript, recomputes query indices, verifies Merkle paths, evaluates each opened local interpolant at the transcript challenge, and checks consistency against the next committed round or the final QM31 value.".to_string());
    lines.push("- The host verifier is the semantic oracle for the Solana verifier and uses the same parser/core verification logic.".to_string());
    lines.push(String::new());
    lines.push("## On-Chain Verifier Design".to_string());
    lines.push(
        "- The Solana program exposes `init_upload`, `upload_chunk`, and `verify` only."
            .to_string(),
    );
    lines.push(
        "- Proofs are uploaded into a fixed-layout account with a rolling SHA-256 upload digest."
            .to_string(),
    );
    lines.push("- Verification accepts only the two fixed profiles and only the exact envelope/hash/fold modes emitted by the host prover.".to_string());
    lines.push(String::new());
    lines.push("## Statement Binding Design".to_string());
    lines.push("- The public binding schema is `SpendV0Binding { anchor, nullifiers, outputs, asset_id, fee }` with a canonical byte encoding and SHA-256 statement digest.".to_string());
    lines.push(
        "- The digest is checked on host and chain before proof verification proceeds.".to_string(),
    );
    lines.push(String::new());
    lines.push("## Executed vs Implemented-Only".to_string());
    lines.push(format!(
        "- Dev profile executed: host prove={}, host verify={}, on-chain verify={:?}.",
        summary.dev_profile.proof_bytes.is_some(),
        summary.dev_profile.host_verify_ok,
        summary.dev_profile.onchain_verify_ok
    ));
    lines.push(format!(
        "- Target profile executed: host prove={}, host verify={}, on-chain verify={:?}.",
        summary.target_profile.proof_bytes.is_some(),
        summary.target_profile.host_verify_ok,
        summary.target_profile.onchain_verify_ok
    ));
    lines.push(String::new());
    lines.push("## Measurements".to_string());
    lines.push(format!(
        "- Dev proof bytes: {:?}; on-chain verify CU: {:?}; upload CU: {:?}.",
        summary.dev_profile.proof_bytes,
        summary.dev_profile.onchain_verify_cu,
        summary.dev_profile.upload_total_cu
    ));
    lines.push(format!(
        "- Target proof bytes: {:?}; on-chain verify CU: {:?}; upload CU: {:?}.",
        summary.target_profile.proof_bytes,
        summary.target_profile.onchain_verify_cu,
        summary.target_profile.upload_total_cu
    ));
    lines.push("- Previous Phase 2 proxy reference points: `whir_t100_capacity_full = 458,043 CU`, `whir_t128_capacity_full = 599,602 CU`, `whir_t128_johnson_full = 1,095,421 CU`.".to_string());
    lines.push(String::new());
    lines.push("## Corruption Tests".to_string());
    for record in &summary.corruption_tests {
        lines.push(format!(
            "- `{}`: host_rejected={}, onchain_rejected={}, onchain_error={}.",
            record.mutation,
            record.host_rejected,
            record.onchain_rejected,
            record
                .onchain_error
                .clone()
                .unwrap_or_else(|| "none".to_string())
        ));
    }
    lines.push(String::new());
    lines.push("## Biggest Remaining Gaps To SpendV0".to_string());
    lines.push(format!("- {}", summary.biggest_remaining_risk));
    lines.push(String::new());
    lines.push("## Next Steps".to_string());
    for step in &summary.next_steps {
        lines.push(format!("- {step}"));
    }
    lines.push(String::new());
    lines.push(format!(
        "_Generated {} from `{}`._",
        summary.generated_at_utc, summary.command
    ));
    lines.join("\n")
}
