//! One-shot host-only V8-A compression experiment over the frozen V7 proof.
//!
//! This instantiates Construction 2.2 of Fenzi--Zhang, ePrint 2025/1446,
//! with the best observed ordinary lossless wrapper for this exact proof,
//! Brotli quality 1. It deliberately does not alter
//! the V7 proof, statement, transcript, verifier, or cryptography: the V8
//! verifier in this experiment is exactly `Decompress` followed by the
//! production V7 read-only verifier with all work checks enabled.

use std::{
    collections::BTreeMap,
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
    str::FromStr,
    time::Instant,
};

use anyhow::{anyhow, bail, ensure, Context, Result};
use aspis_core::v7_onefold::{
    V7_COMPACT_BODY_WITHOUT_FRONTIERS, V7_COMPACT_C1_BYTES_PER_QUERY,
    V7_COMPACT_C2_BYTES_PER_QUERY, V7_COMPACT_DIGEST_BYTES, V7_COMPACT_FRONTIER_CAP_PER_TREE,
    V7_COMPACT_PRIVATE_SALT_BYTES, V7_COMPACT_QUERY_BYTES,
};
use aspis_prover::HOST_HASH;
use aspis_statement::{atomic_deployment_domain, AtomicPaymentStatementV4, SpendPublic};
use aspis_verifier::v7_transaction::V7_RELEASE_BINDING;
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_sdk::pubkey::Pubkey;

const FROZEN_V7_BYTES: usize = 30_504;
const FROZEN_V7_SHA256: &str = "e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb";
const FROZEN_V7_STATEMENT_SHA256: &str =
    "7dd15bd17b8f052d540d0187caf4f1d616f4220e66a14be78b56f9c736a5a375";
const FROZEN_V7_PROFILE: &str = "V7-26C1-3C2-B10-q16-onefold-digest208-f203-fullC2";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct V7StatementSidecar {
    artifact: String,
    profile: String,
    program_id: String,
    pool: String,
    sequence: u64,
    current_anchor_hex: String,
    nullifier_hex: String,
    output_commitment_hex: String,
    output_anchor_hex: String,
    asset_id: u32,
    fee: u32,
    deployment_domain_hex: String,
    network_tag: String,
    proof_account: String,
    release_binding_hex: String,
}

#[derive(Debug, Deserialize)]
struct V7ProofMetadata {
    artifact: String,
    proof_sha256: String,
    statement_sha256: String,
    program_id: String,
    pool: String,
    proof_account: String,
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    frontier_digest_bytes: usize,
    all_work_checked: bool,
    host_full_acceptance: bool,
    release_binding_hex: String,
    proof_bytes: usize,
    work_bits: [u32; 3],
}

#[derive(Clone, Copy, Debug)]
struct ProcessTiming {
    wall_ms: u128,
    maximum_resident_set_bytes: u64,
    peak_memory_footprint_bytes: u64,
}

fn parse_arguments() -> Result<BTreeMap<String, String>> {
    const ALLOWED: [&str; 5] = [
        "--proof",
        "--statement",
        "--metadata",
        "--out-dir",
        "--brotli",
    ];
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let mut values = BTreeMap::new();
    let mut index = 0usize;
    while index < arguments.len() {
        let key = arguments.get(index).context("missing argument")?;
        ensure!(ALLOWED.contains(&key.as_str()), "unknown argument {key}");
        let value = arguments
            .get(index + 1)
            .with_context(|| format!("missing value for {key}"))?;
        ensure!(
            values.insert(key.clone(), value.clone()).is_none(),
            "duplicate {key}"
        );
        index += 2;
    }
    for required in ["--proof", "--statement", "--metadata", "--out-dir"] {
        ensure!(values.contains_key(required), "missing {required}");
    }
    Ok(values)
}

fn required_path(arguments: &BTreeMap<String, String>, key: &str) -> Result<PathBuf> {
    let path = PathBuf::from(
        arguments
            .get(key)
            .with_context(|| format!("missing {key}"))?,
    );
    ensure!(path.is_absolute(), "{key} must be absolute");
    Ok(path)
}

fn sha256(bytes: &[u8]) -> String {
    let mut hash = Sha256::new();
    hash.update(bytes);
    hash.finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn hex_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hex_32(field: &str, value: &str) -> Result<[u8; 32]> {
    ensure!(value.len() == 64, "{field} is not 32-byte hex");
    let mut decoded = [0u8; 32];
    for (index, byte) in decoded.iter_mut().enumerate() {
        let start = 2 * index;
        *byte = u8::from_str_radix(&value[start..start + 2], 16)
            .with_context(|| format!("invalid {field} hex"))?;
    }
    Ok(decoded)
}

fn statement_from_sidecar(sidecar: &V7StatementSidecar) -> Result<AtomicPaymentStatementV4> {
    ensure!(sidecar.artifact == "aspis_v7_compact_onefold_statement");
    ensure!(sidecar.profile == FROZEN_V7_PROFILE);
    ensure!(sidecar.release_binding_hex == hex_bytes(&V7_RELEASE_BINDING));
    let decode_digest = |field: &str, encoded: &str| {
        aspis_statement::decode_digest_canonical(&decode_hex_32(field, encoded)?)
            .map_err(|error| anyhow!("decode {field}: {error:?}"))
    };
    let statement = AtomicPaymentStatementV4 {
        pool: Pubkey::from_str(&sidecar.pool)
            .context("invalid V7 pool")?
            .to_bytes(),
        sequence: sidecar.sequence,
        spend: SpendPublic {
            anchor: decode_digest("current_anchor_hex", &sidecar.current_anchor_hex)?,
            nullifier: decode_digest("nullifier_hex", &sidecar.nullifier_hex)?,
            output_commitment: decode_digest(
                "output_commitment_hex",
                &sidecar.output_commitment_hex,
            )?,
            asset_id: aspis_statement::decode_asset_id_canonical(sidecar.asset_id)
                .map_err(|error| anyhow!("decode asset_id: {error:?}"))?,
            fee: sidecar.fee,
        },
        output_anchor: decode_digest("output_anchor_hex", &sidecar.output_anchor_hex)?,
        deployment_domain: decode_hex_32("deployment_domain_hex", &sidecar.deployment_domain_hex)?,
    };
    aspis_statement::encode_atomic_payment_statement_v4(&statement)
        .map_err(|error| anyhow!("noncanonical V7 statement: {error:?}"))?;
    Ok(statement)
}

fn parse_time_metric(stderr: &str, suffix: &str) -> Result<u64> {
    stderr
        .lines()
        .find_map(|line| {
            let line = line.trim();
            line.strip_suffix(suffix)
                .and_then(|prefix| prefix.trim().parse::<u64>().ok())
        })
        .with_context(|| format!("/usr/bin/time omitted {suffix}"))
}

fn finish_timed_process(
    started: Instant,
    output: Output,
    operation: &str,
) -> Result<ProcessTiming> {
    let stderr = String::from_utf8(output.stderr).context("non-UTF-8 timed process stderr")?;
    if !output.status.success() {
        bail!("{operation} failed with {}: {stderr}", output.status);
    }
    Ok(ProcessTiming {
        wall_ms: started.elapsed().as_millis(),
        maximum_resident_set_bytes: parse_time_metric(&stderr, "maximum resident set size")?,
        peak_memory_footprint_bytes: parse_time_metric(&stderr, "peak memory footprint")?,
    })
}

fn run_brotli_compress(brotli: &Path, input: &Path, output: &Path) -> Result<ProcessTiming> {
    let started = Instant::now();
    let encoded = File::create(output).context("create Brotli output")?;
    let result = Command::new("/usr/bin/time")
        .arg("-lp")
        .arg(brotli)
        .args(["-q", "1", "-c"])
        .arg(input)
        .stdout(Stdio::from(encoded))
        .output()
        .context("run Brotli compressor")?;
    finish_timed_process(started, result, "Brotli compression")
}

fn run_brotli_decompress(brotli: &Path, input: &Path, output: &Path) -> Result<ProcessTiming> {
    let started = Instant::now();
    let decoded = File::create(output).context("create Brotli round-trip output")?;
    let result = Command::new("/usr/bin/time")
        .arg("-lp")
        .arg(brotli)
        .args(["-d", "-c"])
        .arg(input)
        .stdout(Stdio::from(decoded))
        .output()
        .context("run Brotli decompressor")?;
    finish_timed_process(started, result, "Brotli decompression")
}

fn brotli_version(brotli: &Path) -> Result<String> {
    let output = Command::new(brotli)
        .arg("--version")
        .output()
        .context("run brotli --version")?;
    ensure!(output.status.success(), "brotli --version failed");
    let stdout = String::from_utf8(output.stdout)?;
    Ok(stdout.trim().to_owned())
}

fn decision_band(bytes: usize) -> &'static str {
    match bytes {
        0..=18_432 => "gold_stop_size_research",
        18_433..=18_500 => "excellent_stop_major_native_redesign",
        18_501..=18_937 => "passes_five_lifecycle_screen",
        18_938..=19_095 => "passes_five_proof_bearing_seek_lifecycle_cleanup",
        19_096..=19_375 => "passes_five_uploads_small_native_shave_needed",
        19_376..=20_500 => "near_miss_combine_with_v8_b",
        _ => "compression_alone_not_v8_route",
    }
}

fn main() -> Result<()> {
    let arguments = parse_arguments()?;
    let proof_path = required_path(&arguments, "--proof")?;
    let statement_path = required_path(&arguments, "--statement")?;
    let metadata_path = required_path(&arguments, "--metadata")?;
    let out_dir = required_path(&arguments, "--out-dir")?;
    let brotli = PathBuf::from(
        arguments
            .get("--brotli")
            .map_or("/opt/homebrew/bin/brotli", String::as_str),
    );

    for path in [&proof_path, &statement_path, &metadata_path, &brotli] {
        ensure!(path.is_file(), "missing input {}", path.display());
    }
    ensure!(
        !out_dir.exists(),
        "refusing to overwrite {}",
        out_dir.display()
    );
    fs::create_dir_all(out_dir.parent().context("output has no parent")?)?;
    fs::create_dir(&out_dir)?;

    // Pin the selected V7 wire, correcting the stale 27-byte/omitted-C2 draft.
    ensure!(V7_COMPACT_DIGEST_BYTES == 26);
    ensure!(V7_COMPACT_DIGEST_BYTES * 8 == 208);
    ensure!(V7_COMPACT_C1_BYTES_PER_QUERY == 403);
    ensure!(V7_COMPACT_C2_BYTES_PER_QUERY == 186);
    ensure!(V7_COMPACT_PRIVATE_SALT_BYTES == 32);
    ensure!(V7_COMPACT_QUERY_BYTES == 621);
    ensure!(V7_COMPACT_FRONTIER_CAP_PER_TREE == 203);
    ensure!(V7_COMPACT_BODY_WITHOUT_FRONTIERS == 19_948);

    let proof = fs::read(&proof_path)?;
    let statement_bytes = fs::read(&statement_path)?;
    let metadata_bytes = fs::read(&metadata_path)?;
    let sidecar: V7StatementSidecar = serde_json::from_slice(&statement_bytes)?;
    let metadata: V7ProofMetadata = serde_json::from_slice(&metadata_bytes)?;
    let statement = statement_from_sidecar(&sidecar)?;

    ensure!(proof.len() == FROZEN_V7_BYTES);
    ensure!(sha256(&proof) == FROZEN_V7_SHA256);
    ensure!(sha256(&statement_bytes) == FROZEN_V7_STATEMENT_SHA256);
    ensure!(metadata.artifact == "aspis_v7_compact_onefold_honest_mined_proof");
    ensure!(metadata.proof_bytes == FROZEN_V7_BYTES);
    ensure!(metadata.proof_sha256 == FROZEN_V7_SHA256);
    ensure!(metadata.statement_sha256 == FROZEN_V7_STATEMENT_SHA256);
    ensure!(metadata.program_id == sidecar.program_id);
    ensure!(metadata.pool == sidecar.pool);
    ensure!(metadata.proof_account == sidecar.proof_account);
    ensure!(metadata.release_binding_hex == hex_bytes(&V7_RELEASE_BINDING));
    ensure!(metadata.frontier_digest_bytes == 26);
    ensure!(metadata.frontier_nodes_per_tree == 203);
    ensure!(metadata.compact_counter == 4);
    ensure!(metadata.work_bits == [35, 31, 34]);
    ensure!(metadata.all_work_checked && metadata.host_full_acceptance);
    ensure!(
        proof.len()
            == V7_COMPACT_BODY_WITHOUT_FRONTIERS
                + 2 * V7_COMPACT_DIGEST_BYTES * metadata.frontier_nodes_per_tree
    );

    let program_id = Pubkey::from_str(&sidecar.program_id)?;
    let proof_account = Pubkey::from_str(&sidecar.proof_account)?;
    ensure!(program_id == aspis_verifier::id());
    ensure!(sidecar.network_tag == "devnet");
    ensure!(
        atomic_deployment_domain(HOST_HASH, &program_id.to_bytes(), b"devnet")
            == statement.deployment_domain
    );

    let compressed_path = out_dir.join("v8-a-frozen-v7.br");
    let roundtrip_path = out_dir.join("v8-a-decompressed-v7.bin");
    let evidence_path = out_dir.join("v8-a-compression-experiment.json");
    let compression_timing = run_brotli_compress(&brotli, &proof_path, &compressed_path)?;
    let decompression_timing = run_brotli_decompress(&brotli, &compressed_path, &roundtrip_path)?;

    let compressed = fs::read(&compressed_path)?;
    let roundtrip = fs::read(&roundtrip_path)?;
    ensure!(
        roundtrip == proof,
        "lossless round trip changed frozen V7 bytes"
    );
    ensure!(sha256(&roundtrip) == FROZEN_V7_SHA256);

    let verifier_started = Instant::now();
    let accepted = aspis_verifier::v7_verifier::verify_v7_read_only(
        HOST_HASH,
        &roundtrip,
        metadata.frontier_nodes_per_tree,
        &program_id,
        V7_RELEASE_BINDING,
        &proof_account,
        &statement,
        true,
    )
    .map_err(|error| anyhow!("decompressed V7 proof rejected: {error:?}"))?;
    let verifier_ms = verifier_started.elapsed().as_millis();
    ensure!(accepted.transcript.compact_counter == metadata.compact_counter);
    ensure!(accepted.transcript.frontier_nodes == metadata.frontier_nodes_per_tree);

    let compressed_bytes = compressed.len();
    let ratio = compressed_bytes as f64 / FROZEN_V7_BYTES as f64;
    let targets = [
        ("preferred_18KiB", 18_432usize),
        ("preferred_release", 18_500usize),
        ("five_total_lifecycle", 18_937usize),
        ("five_proof_bearing", 19_095usize),
        ("five_uploads_plus_verify", 19_375usize),
    ];
    let gates = targets
        .iter()
        .map(|(name, target)| {
            json!({
                "name": name,
                "target_bytes": target,
                "cleared": compressed_bytes <= *target,
                "headroom_bytes": *target as i64 - compressed_bytes as i64,
            })
        })
        .collect::<Vec<_>>();

    let compression_command = format!(
        "/usr/bin/time -lp {} -q 1 -c {} > {}",
        brotli.display(),
        proof_path.display(),
        compressed_path.display(),
    );
    let decompression_command = format!(
        "/usr/bin/time -lp {} -d -c {} > {}",
        brotli.display(),
        compressed_path.display(),
        roundtrip_path.display(),
    );
    let evidence = json!({
        "schema_version": 1,
        "artifact": "aspis_v8_a_frozen_v7_lossless_compression_kill_experiment",
        "scope": "host_only_no_cryptographic_change_no_deployment",
        "construction": {
            "name": "Fenzi-Zhang zip Construction 2.2",
            "paper": "IACR ePrint 2025/1446",
            "instantiation": "Brotli 1.2.0 quality 1, the smallest ordinary lossless output observed for this exact frozen proof",
            "v8_acceptance": "Decompress(compressed_proof) followed by exact V7 read-only verifier",
        },
        "frozen_v7": {
            "proof_path": proof_path,
            "proof_bytes": FROZEN_V7_BYTES,
            "proof_sha256": FROZEN_V7_SHA256,
            "statement_path": statement_path,
            "statement_sha256": FROZEN_V7_STATEMENT_SHA256,
            "metadata_path": metadata_path,
            "profile": FROZEN_V7_PROFILE,
            "digest_bytes": 26,
            "digest_bits": 208,
            "generic_collision_bits": 104,
            "complete_c2_disclosed": true,
            "query_bytes": 621,
            "queries": 16,
            "frontier_nodes_per_tree": 203,
            "compact_counter": metadata.compact_counter,
            "work_bits": metadata.work_bits,
        },
        "compressor": {
            "binary": brotli,
            "version": brotli_version(&brotli)?,
            "compression_command": compression_command,
            "decompression_command": decompression_command,
            "compressed_path": compressed_path,
            "compressed_bytes": compressed_bytes,
            "compressed_sha256": sha256(&compressed),
            "output_ratio": ratio,
            "reduction_bytes": FROZEN_V7_BYTES as i64 - compressed_bytes as i64,
            "reduction_fraction": 1.0 - ratio,
            "compression_wall_ms": compression_timing.wall_ms,
            "compression_maximum_resident_set_bytes": compression_timing.maximum_resident_set_bytes,
            "compression_peak_memory_footprint_bytes": compression_timing.peak_memory_footprint_bytes,
            "decompression_wall_ms": decompression_timing.wall_ms,
            "decompression_maximum_resident_set_bytes": decompression_timing.maximum_resident_set_bytes,
            "decompression_peak_memory_footprint_bytes": decompression_timing.peak_memory_footprint_bytes,
        },
        "round_trip": {
            "decompressed_path": roundtrip_path,
            "decompressed_bytes": roundtrip.len(),
            "decompressed_sha256": sha256(&roundtrip),
            "byte_identical": true,
        },
        "host_verifier": {
            "accepted": true,
            "all_work_checked": true,
            "verifier_wall_ms": verifier_ms,
            "compact_counter": accepted.transcript.compact_counter,
            "frontier_nodes": accepted.transcript.frontier_nodes,
        },
        "gates": gates,
        "decision_band": decision_band(compressed_bytes),
    });
    let mut encoded = serde_json::to_vec_pretty(&evidence)?;
    encoded.push(b'\n');
    fs::write(&evidence_path, encoded)?;

    println!(
        "V8-A Brotli-q1: {} -> {} bytes ({:.3}%); round trip exact; V7 host accepted; decision={}; evidence={}",
        FROZEN_V7_BYTES,
        compressed_bytes,
        100.0 * ratio,
        decision_band(compressed_bytes),
        evidence_path.display(),
    );
    Ok(())
}
