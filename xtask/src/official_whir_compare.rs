use super::*;
use serde::{Deserialize, Serialize};
use whir_m31_core::profile::{profile_manifest, ProfileId, WhirProfileManifest};

const OFFICIAL_WHIR_REPO_URL: &str = "https://github.com/WizardOfMenlo/whir";
const DEFAULT_OFFICIAL_HASH: &str = "Blake3";
const DEFAULT_OFFICIAL_FIELD: &str = "Goldilocks2";
const DEFAULT_OFFICIAL_REPS: u32 = 10;
const DEFAULT_OFFICIAL_TIMEOUT_SECS: u64 = 180;

#[derive(Clone, Debug, Deserialize, Serialize)]
struct NativeWhirSummaryInput {
    generated_at_utc: String,
    command: String,
    dev_profile: NativeProfileSnapshot,
    target_profile: NativeProfileSnapshot,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct NativeProfileSnapshot {
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
struct OfficialWhirRepoSnapshot {
    repo_path: String,
    git_head: String,
    dirty: bool,
}

#[derive(Clone, Debug, Serialize)]
struct OfficialWhirInvocation {
    security_level: u16,
    pow_bits: u8,
    num_variables: u8,
    evaluations: u8,
    rate: u8,
    initial_folding_factor: u8,
    folding_factor: u8,
    field: String,
    hash: String,
    verifier_repetitions: u32,
    unique_decoding: bool,
    cli_args: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct OfficialWhirRun {
    profile: String,
    invocation: OfficialWhirInvocation,
    stdout_path: String,
    stderr_path: String,
    timeout_secs: u64,
    completed: bool,
    timed_out: bool,
    exit_success: bool,
    execution_error: Option<String>,
    proof_size_kib: Option<f64>,
    proof_size_bytes_estimate: Option<u64>,
    prover_total_ns: Option<u128>,
    verifier_ns_per_rep: Option<u128>,
    average_hashes_thousands: Option<f64>,
    security_level_bits: Option<f64>,
    security_regime: Option<String>,
    source_field_bits: Option<f64>,
    target_field_bits: Option<f64>,
    initial_stage_present: bool,
    intermediate_round_count: usize,
    final_stage_present: bool,
    cli_help_mismatch_notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct LocalManifestSnapshot {
    name: String,
    log_num_rows: u8,
    fold_vars_per_round: u8,
    round_count: usize,
    query_repetitions_per_round: u8,
    query_pow_bits: u8,
    target_security_bits: u16,
    hash_mode: String,
    fold_mode: String,
}

#[derive(Clone, Debug, Serialize)]
struct ComparisonProfileRecord {
    profile: String,
    local_manifest: LocalManifestSnapshot,
    local_summary: NativeProfileSnapshot,
    official_run: OfficialWhirRun,
    notes: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct OfficialWhirComparisonSummary {
    generated_at_utc: String,
    command: String,
    local_results_source: String,
    official_repo: OfficialWhirRepoSnapshot,
    methodology: String,
    global_notes: Vec<String>,
    profiles: Vec<ComparisonProfileRecord>,
}

pub(super) fn run_compare_official_whir() -> Result<()> {
    let root = workspace_root()?;
    let native_summary_path = root.join("results/native-whir/summary.json");
    if !native_summary_path.exists() {
        eprintln!("compare-official-whir: native-whir summary missing, running native-whir-m31");
        super::native_whir::run_native_whir_m31()?;
    }
    let local_summary: NativeWhirSummaryInput =
        serde_json::from_slice(&fs::read(&native_summary_path)?)
            .context("failed to decode results/native-whir/summary.json")?;

    let official_repo_path = resolve_official_whir_repo(&root)?;
    let official_repo = OfficialWhirRepoSnapshot {
        repo_path: official_repo_path.display().to_string(),
        git_head: run_command_capture(
            "git",
            &[
                "-C",
                official_repo_path.to_str().unwrap(),
                "rev-parse",
                "HEAD",
            ],
        )?,
        dirty: !run_command_capture(
            "git",
            &[
                "-C",
                official_repo_path.to_str().unwrap(),
                "status",
                "--porcelain",
            ],
        )?
        .is_empty(),
    };

    let results_root = root.join("results/native-whir/official-whir");
    fs::create_dir_all(&results_root)?;
    let docs_path = root.join("docs/native-whir-vs-official-whir.md");

    let dev_record = compare_profile(
        &official_repo_path,
        &results_root,
        profile_manifest(ProfileId::WhirM31DevV0),
        local_summary.dev_profile.clone(),
    )?;
    let target_record = compare_profile(
        &official_repo_path,
        &results_root,
        profile_manifest(ProfileId::WhirM31SolanaV0),
        local_summary.target_profile.clone(),
    )?;

    let summary = OfficialWhirComparisonSummary {
        generated_at_utc: Utc::now().to_rfc3339(),
        command: "cargo xtask compare-official-whir".to_string(),
        local_results_source: native_summary_path.display().to_string(),
        official_repo,
        methodology: "Nearest-comparable upstream PCS runs only. Local proofs remain M31/CM31/QM31 with SHA-256 and a fixed narrow v0 relation; official WHIR runs use the current upstream CLI over Goldilocks2 with Blake3 because upstream does not currently expose M31 or SHA-256.".to_string(),
        global_notes: vec![
            "This is a comparison harness, not a proof-equivalence oracle.".to_string(),
            "The current upstream CLI no longer exposes the README's older `--type` or `--fold_type` flags; the harness records the upstream commit and parses the real current CLI output.".to_string(),
            "Official proof size is reported from upstream stdout in KiB and converted to an estimated byte count; it is not a byte-exact serialization export.".to_string(),
            format!(
                "Official runs are bounded by a {} second timeout by default so the harness cannot hang indefinitely on one upstream profile.",
                official_timeout_secs()
            ),
        ],
        profiles: vec![dev_record, target_record],
    };

    write_json(&results_root.join("summary.json"), &summary)?;
    fs::write(&docs_path, render_official_whir_report(&summary))?;
    Ok(())
}

fn compare_profile(
    official_repo_path: &Path,
    results_root: &Path,
    manifest: &'static WhirProfileManifest,
    local_summary: NativeProfileSnapshot,
) -> Result<ComparisonProfileRecord> {
    let invocation = OfficialWhirInvocation {
        security_level: manifest.target_security_bits,
        pow_bits: manifest.query_pow_bits,
        num_variables: manifest.log_num_rows,
        evaluations: 1,
        rate: 1,
        initial_folding_factor: manifest.fold_vars_per_round,
        folding_factor: manifest.fold_vars_per_round,
        field: DEFAULT_OFFICIAL_FIELD.to_string(),
        hash: DEFAULT_OFFICIAL_HASH.to_string(),
        verifier_repetitions: DEFAULT_OFFICIAL_REPS,
        unique_decoding: false,
        cli_args: official_cli_args(manifest),
    };

    let timeout_secs = official_timeout_secs();
    let run =
        run_official_cli(official_repo_path, &invocation, timeout_secs).with_context(|| {
            format!(
                "failed to launch official WHIR comparator for {}",
                manifest.name
            )
        })?;

    let stdout = run.stdout;
    let stderr = run.stderr;
    let stdout_path = results_root.join(format!("{}.stdout.txt", manifest.name));
    let stderr_path = results_root.join(format!("{}.stderr.txt", manifest.name));
    fs::write(&stdout_path, &stdout)?;
    fs::write(&stderr_path, &stderr)?;

    let parsed = parse_official_whir_stdout(&stdout)?;
    let mut notes = vec![
        "Official run uses Goldilocks2 as the nearest upstream PCS field embedding, not M31 -> CM31 -> QM31.".to_string(),
        "Official run uses Blake3 because the current upstream CLI does not expose SHA-256.".to_string(),
        "Local verifier cost is on-chain CU; official verifier cost is host wall-clock time from the upstream binary.".to_string(),
    ];
    if !run.exit_success && !run.timed_out {
        notes.push(format!(
            "Official run exited non-zero: {}",
            run.execution_error
                .clone()
                .unwrap_or_else(|| "unknown upstream failure".to_string())
        ));
    }
    if run.timed_out {
        notes.push(format!(
            "Official run timed out after {} seconds; partial stdout/stderr were preserved.",
            timeout_secs
        ));
    }
    if parsed.intermediate_round_count + usize::from(parsed.initial_stage_present)
        != manifest.round_count()
    {
        notes.push(format!(
            "Stage-count mismatch: local fold stages={}, official reported initial+round stages={}.",
            manifest.round_count(),
            parsed.intermediate_round_count + usize::from(parsed.initial_stage_present)
        ));
    }
    if !local_summary.host_verify_ok || local_summary.onchain_verify_ok != Some(true) {
        notes.push("Local summary was not fully successful; comparison still recorded the profile's last known state.".to_string());
    }
    notes.extend(parsed.cli_help_mismatch_notes.clone());

    Ok(ComparisonProfileRecord {
        profile: manifest.name.to_string(),
        local_manifest: local_manifest_snapshot(manifest),
        local_summary,
        official_run: OfficialWhirRun {
            profile: manifest.name.to_string(),
            invocation,
            stdout_path: stdout_path.display().to_string(),
            stderr_path: stderr_path.display().to_string(),
            timeout_secs,
            completed: run.completed,
            timed_out: run.timed_out,
            exit_success: run.exit_success,
            execution_error: run.execution_error,
            proof_size_kib: parsed.proof_size_kib,
            proof_size_bytes_estimate: parsed.proof_size_bytes_estimate,
            prover_total_ns: parsed.prover_total_ns,
            verifier_ns_per_rep: parsed.verifier_ns_per_rep,
            average_hashes_thousands: parsed.average_hashes_thousands,
            security_level_bits: parsed.security_level_bits,
            security_regime: parsed.security_regime,
            source_field_bits: parsed.source_field_bits,
            target_field_bits: parsed.target_field_bits,
            initial_stage_present: parsed.initial_stage_present,
            intermediate_round_count: parsed.intermediate_round_count,
            final_stage_present: parsed.final_stage_present,
            cli_help_mismatch_notes: parsed.cli_help_mismatch_notes,
        },
        notes,
    })
}

#[derive(Debug)]
struct OfficialCliOutcome {
    stdout: String,
    stderr: String,
    completed: bool,
    timed_out: bool,
    exit_success: bool,
    execution_error: Option<String>,
}

fn run_official_cli(
    official_repo_path: &Path,
    invocation: &OfficialWhirInvocation,
    timeout_secs: u64,
) -> Result<OfficialCliOutcome> {
    let mut child = Command::new("cargo")
        .arg("run")
        .arg("--release")
        .arg("--manifest-path")
        .arg(official_repo_path.join("Cargo.toml"))
        .arg("--")
        .args(&invocation.cli_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let started = Instant::now();
    let timeout = Duration::from_secs(timeout_secs);
    let mut timed_out = false;
    loop {
        if child.try_wait()?.is_some() {
            break;
        }
        if started.elapsed() >= timeout {
            timed_out = true;
            child.kill().ok();
            break;
        }
        thread::sleep(Duration::from_millis(250));
    }
    let output = child.wait_with_output()?;
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let execution_error = if output.status.success() {
        None
    } else {
        Some(stderr.trim().to_string())
    };
    Ok(OfficialCliOutcome {
        stdout,
        stderr,
        completed: !timed_out && output.status.success(),
        timed_out,
        exit_success: output.status.success(),
        execution_error,
    })
}

fn official_timeout_secs() -> u64 {
    std::env::var("OFFICIAL_WHIR_TIMEOUT_SECS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_OFFICIAL_TIMEOUT_SECS)
}

fn local_manifest_snapshot(manifest: &'static WhirProfileManifest) -> LocalManifestSnapshot {
    LocalManifestSnapshot {
        name: manifest.name.to_string(),
        log_num_rows: manifest.log_num_rows,
        fold_vars_per_round: manifest.fold_vars_per_round,
        round_count: manifest.round_count(),
        query_repetitions_per_round: manifest.query_repetitions_per_round,
        query_pow_bits: manifest.query_pow_bits,
        target_security_bits: manifest.target_security_bits,
        hash_mode: format!("{:?}", manifest.hash_mode),
        fold_mode: format!("{:?}", manifest.fold_mode),
    }
}

fn resolve_official_whir_repo(root: &Path) -> Result<PathBuf> {
    let mut candidates = Vec::new();
    if let Ok(path) = std::env::var("OFFICIAL_WHIR_DIR") {
        candidates.push(PathBuf::from(path));
    }
    candidates.push(root.join("third_party/official-whir"));
    candidates.push(root.join("target/official-whir-ref"));
    candidates.push(PathBuf::from("/tmp/whir-ref"));

    for candidate in &candidates {
        if candidate.join("Cargo.toml").exists() {
            return Ok(candidate.clone());
        }
    }

    let clone_target = root.join("target/official-whir-ref");
    if clone_target.exists() {
        return Ok(clone_target);
    }
    let status = Command::new("git")
        .arg("clone")
        .arg("--depth")
        .arg("1")
        .arg(OFFICIAL_WHIR_REPO_URL)
        .arg(&clone_target)
        .status()
        .context("failed to clone official WHIR repository")?;
    if !status.success() {
        bail!("git clone failed for official WHIR repository");
    }
    Ok(clone_target)
}

fn official_cli_args(manifest: &'static WhirProfileManifest) -> Vec<String> {
    vec![
        "-d".to_string(),
        manifest.log_num_rows.to_string(),
        "-e".to_string(),
        "1".to_string(),
        "-l".to_string(),
        manifest.target_security_bits.to_string(),
        "-p".to_string(),
        manifest.query_pow_bits.to_string(),
        "-r".to_string(),
        "1".to_string(),
        "-i".to_string(),
        manifest.fold_vars_per_round.to_string(),
        "-k".to_string(),
        manifest.fold_vars_per_round.to_string(),
        "-f".to_string(),
        DEFAULT_OFFICIAL_FIELD.to_string(),
        "--hash".to_string(),
        DEFAULT_OFFICIAL_HASH.to_string(),
        "--reps".to_string(),
        DEFAULT_OFFICIAL_REPS.to_string(),
    ]
}

#[derive(Clone, Debug)]
struct ParsedOfficialStdout {
    proof_size_kib: Option<f64>,
    proof_size_bytes_estimate: Option<u64>,
    prover_total_ns: Option<u128>,
    verifier_ns_per_rep: Option<u128>,
    average_hashes_thousands: Option<f64>,
    security_level_bits: Option<f64>,
    security_regime: Option<String>,
    source_field_bits: Option<f64>,
    target_field_bits: Option<f64>,
    initial_stage_present: bool,
    intermediate_round_count: usize,
    final_stage_present: bool,
    cli_help_mismatch_notes: Vec<String>,
}

fn parse_official_whir_stdout(stdout: &str) -> Result<ParsedOfficialStdout> {
    let mut proof_size_kib = None;
    let mut prover_total_ns = None;
    let mut verifier_ns_per_rep = None;
    let mut average_hashes_thousands = None;
    let mut security_level_bits = None;
    let mut security_regime = None;
    let mut source_field_bits = None;
    let mut target_field_bits = None;
    let mut initial_stage_present = false;
    let mut intermediate_round_count = 0usize;
    let mut final_stage_present = false;

    for line in stdout.lines().map(str::trim) {
        if line == "Initial:" {
            initial_stage_present = true;
            continue;
        }
        if line == "Final:" {
            final_stage_present = true;
            continue;
        }
        if line.starts_with("Round ") {
            intermediate_round_count += 1;
            continue;
        }
        if let Some(rest) = line.strip_prefix("Security level: ") {
            if let Some((bits, regime)) = rest.split_once(" bits using ") {
                security_level_bits = Some(bits.trim().parse()?);
                security_regime = Some(regime.trim().to_string());
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("Source field: ") {
            if let Some((source, target)) = rest.split_once(" bits, target field: ") {
                source_field_bits = Some(source.trim().parse()?);
                target_field_bits = Some(target.trim_end_matches(" bits").trim().parse()?);
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("Proof size: ") {
            if let Some(value) = rest.strip_suffix(" KiB") {
                let kib: f64 = value.trim().parse()?;
                proof_size_kib = Some(kib);
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("Prover time: ") {
            if let Some((_, total)) = rest.rsplit_once(" = ") {
                prover_total_ns = Some(parse_duration_ns(total.trim())?);
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("Verifier time: ") {
            verifier_ns_per_rep = Some(parse_duration_ns(rest.trim())?);
            continue;
        }
        if let Some(rest) = line.strip_prefix("Average hashes: ") {
            if let Some(value) = rest.strip_suffix('k') {
                average_hashes_thousands = Some(value.trim().parse()?);
            }
        }
    }

    let mut cli_help_mismatch_notes = Vec::new();
    if !stdout.contains("Whir (PCS)") {
        cli_help_mismatch_notes
            .push("Expected `Whir (PCS)` banner missing from upstream stdout.".to_string());
    }
    if !initial_stage_present {
        cli_help_mismatch_notes
            .push("Expected `Initial:` stage missing from upstream stdout.".to_string());
    }
    if !final_stage_present {
        cli_help_mismatch_notes
            .push("Expected `Final:` stage missing from upstream stdout.".to_string());
    }

    Ok(ParsedOfficialStdout {
        proof_size_bytes_estimate: proof_size_kib.map(|kib| (kib * 1024.0).round() as u64),
        proof_size_kib,
        prover_total_ns,
        verifier_ns_per_rep,
        average_hashes_thousands,
        security_level_bits,
        security_regime,
        source_field_bits,
        target_field_bits,
        initial_stage_present,
        intermediate_round_count,
        final_stage_present,
        cli_help_mismatch_notes,
    })
}

fn parse_duration_ns(value: &str) -> Result<u128> {
    let value = value.trim();
    let (number, unit) = if let Some(stripped) = value.strip_suffix("ns") {
        (stripped, "ns")
    } else if let Some(stripped) = value.strip_suffix("µs") {
        (stripped, "us")
    } else if let Some(stripped) = value.strip_suffix("us") {
        (stripped, "us")
    } else if let Some(stripped) = value.strip_suffix("ms") {
        (stripped, "ms")
    } else if let Some(stripped) = value.strip_suffix('s') {
        (stripped, "s")
    } else {
        bail!("unknown duration unit in `{value}`");
    };
    let amount: f64 = number.trim().parse()?;
    let multiplier = match unit {
        "ns" => 1.0,
        "us" => 1_000.0,
        "ms" => 1_000_000.0,
        "s" => 1_000_000_000.0,
        _ => unreachable!(),
    };
    Ok((amount * multiplier).round() as u128)
}

fn render_official_whir_report(summary: &OfficialWhirComparisonSummary) -> String {
    let mut lines = Vec::new();
    lines.push("# Native WHIR vs Official WHIR".to_string());
    lines.push(String::new());
    lines.push("## Scope".to_string());
    lines.push(summary.methodology.clone());
    lines.push(String::new());
    lines.push("## Official Repo".to_string());
    lines.push(format!("- path: `{}`", summary.official_repo.repo_path));
    lines.push(format!("- git head: `{}`", summary.official_repo.git_head));
    lines.push(format!("- dirty: `{}`", summary.official_repo.dirty));
    lines.push(String::new());
    lines.push("## Global Notes".to_string());
    for note in &summary.global_notes {
        lines.push(format!("- {note}"));
    }
    lines.push(String::new());
    lines.push("## Profiles".to_string());
    for record in &summary.profiles {
        lines.push(format!("### {}", record.profile));
        lines.push(format!(
            "- local proof bytes: {:?}",
            record.local_summary.proof_bytes
        ));
        lines.push(format!(
            "- local host prove ns: {:?}",
            record.local_summary.host_prove_ns
        ));
        lines.push(format!(
            "- local on-chain verify CU: {:?}",
            record.local_summary.onchain_verify_cu
        ));
        lines.push(format!(
            "- official proof size: {:?} KiB (~{:?} bytes)",
            record.official_run.proof_size_kib, record.official_run.proof_size_bytes_estimate
        ));
        lines.push(format!(
            "- official completed/timed_out/exit_success: {}/{}/{}",
            record.official_run.completed,
            record.official_run.timed_out,
            record.official_run.exit_success
        ));
        lines.push(format!(
            "- official prover total ns: {:?}",
            record.official_run.prover_total_ns
        ));
        lines.push(format!(
            "- official verifier ns/rep: {:?}",
            record.official_run.verifier_ns_per_rep
        ));
        lines.push(format!(
            "- official security line: {:?} bits using {:?}",
            record.official_run.security_level_bits, record.official_run.security_regime
        ));
        lines.push(format!(
            "- local fold stages: {}, official initial+round stages: {}",
            record.local_manifest.round_count,
            record.official_run.intermediate_round_count
                + usize::from(record.official_run.initial_stage_present)
        ));
        lines.push(format!(
            "- official stdout: `{}`",
            record.official_run.stdout_path
        ));
        lines.push(format!(
            "- official stderr: `{}`",
            record.official_run.stderr_path
        ));
        for note in &record.notes {
            lines.push(format!("  - {note}"));
        }
        lines.push(String::new());
    }
    lines.push(format!(
        "_Generated {} from `{}`._",
        summary.generated_at_utc, summary.command
    ));
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_current_official_stdout_shape() {
        let sample = r#"=========================================
Whir (PCS) 🌪️
Field: Goldilocks2 and hash: Blake3
Security level: 80.06 bits using list decoding
Source field: 64.00 bits, target field: 128.00 bits
Initial:
  commit   size 1×256/4 rate 2⁻1.00 samples 187 in- 1 out-domain
  sumcheck size 256 rounds 2 pow 0.00 ℓ_zk 0
Round 0:
  commit   size 1×64/4 rate 2⁻2.00 samples 87 in- 1 out-domain
  pow      0.00 bits
  sumcheck size 64 rounds 2 pow 0.00 ℓ_zk 0
Round 1:
  commit   size 1×16/4 rate 2⁻3.00 samples 56 in- 1 out-domain
  pow      0.00 bits
  sumcheck size 16 rounds 2 pow 0.00 ℓ_zk 0
Round 2:
  commit   size 1×4/4 rate 2⁻4.00 samples 42 in- 1 out-domain
  pow      0.00 bits
  sumcheck size 4 rounds 2 pow 0.00 ℓ_zk 0
Final:
  pow      0.00bits
  sumcheck size 1 rounds 0 pow 0.00 ℓ_zk 0

Prover time: 1.3ms + 1.1ms = 2.4ms
Proof size: 19.4 KiB
Verifier time: 343.7µs
Average hashes: 0.6k"#;
        let parsed = parse_official_whir_stdout(sample).unwrap();
        assert_eq!(parsed.security_level_bits, Some(80.06));
        assert_eq!(parsed.source_field_bits, Some(64.0));
        assert_eq!(parsed.target_field_bits, Some(128.0));
        assert_eq!(parsed.intermediate_round_count, 3);
        assert_eq!(parsed.proof_size_bytes_estimate, Some(19866));
        assert_eq!(parsed.prover_total_ns, Some(2_400_000));
        assert_eq!(parsed.verifier_ns_per_rep, Some(343_700));
        assert_eq!(parsed.average_hashes_thousands, Some(0.6));
    }
}
