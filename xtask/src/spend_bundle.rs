//! `spend-bundle`: deterministically assemble the offline-verifiable
//! aspis-spend q18/g37 mainnet-beta release bundle from the source artifacts.
//!
//! The generator copies each source artifact verbatim, copies the static,
//! hand-auditable `README.md` and `verify.sh` templates, and writes a
//! `manifest.json` (object -> {bytes, sha256}) plus a `SHA256SUMS`. Every
//! embedded identity is cross-checked against the shipped evidence and the
//! frozen binaries, so the generator fails closed if the sources have drifted
//! from the finalized run. Regenerating over an existing bundle is
//! byte-identical: no wall-clock time enters the output.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, bail, Context, Result};
use serde_json::{json, Map, Value};
use sha2::{Digest, Sha256};

const RELEASE_ID: &str = "aspis-spend-q18-g37-mainnet-v1";

// Pinned identities of the finalized mainnet-beta execution.
const TAG65_SIG: &str =
    "3G1voggszvDMGi5PbGM1kuEMYKvh2TNMbH6hHHwndUdRQJNT7ehRFpQpksxLnx5tp2xkS5jGi359rVXk42sRPFcv";
const TAG65_SLOT: u64 = 433_219_840;
const TAG65_CU: u64 = 1_344_003;
const PROGRAM_ID: &str = "GQPNqfYF17Nj2dGsf6Q2AtiouyM67YxFZPh9LxBk2Ye3";
const POOL: &str = "3ZRYarQZcWJQgzNwLo1Eo7PDmier3rbW41L8ccAddCvb";
const NULLIFIER: &str = "CFJ5fYPSi4Qn6okBCZS3tXFMw7Lsz4Jy9vEAAGU5kfSU";
const DEPLOY_DOMAIN: &str = "ba43feb01d7d7f5ee3f57a6481b202066c83c6c3e76020a619c1611abbd08c8f";
const PROOF_SHA: &str = "32eb419e0c5c3ef4fa2db0d32579e88f1207547d8fb010279efeb6c05981b529";
const SBF_SHA: &str = "e289faf85fe4773880794d5d4356461bb9cb94077b68711f99348efe19707d7e";

// Static templates baked into the binary so the bundle copy is identical to
// the committed, hand-auditable source.
const VERIFY_SH: &str = include_str!("../bundle/verify.sh");
const BUNDLE_README: &str = include_str!("../bundle/README.md");

// (source path relative to workspace root, destination path relative to bundle root)
const COPIES: &[(&str, &str)] = &[
    (
        "crates/aspis-prover/fixtures/spend_q18_g37_release.bin",
        "proof/spend-q18-g37.bin",
    ),
    (
        "crates/aspis-prover/fixtures/spend_q18_g37_release.statement.json",
        "proof/statement.json",
    ),
    ("target/deploy/aspis_verifier.so", "program/aspis_verifier.so"),
    (
        "results/spend/spend_one_transaction_release.json",
        "certificates/release.json",
    ),
    (
        "results/spend/spend_d_after_g_soundness_epro.json",
        "certificates/spend_d_after_g_soundness_epro.json",
    ),
    (
        "results/spend/spend_complete_good_product.json",
        "certificates/spend_complete_good_product.json",
    ),
    (
        "results/spend/spend_computational_hvzk_closure.json",
        "certificates/spend_computational_hvzk_closure.json",
    ),
    (
        "results/spend/mainnet-evidence",
        "evidence/mainnet-execution.json",
    ),
    (
        "results/spend/mainnet-cleanup-evidence.json",
        "evidence/mainnet-cleanup.json",
    ),
    (
        "results/spend/spend_mainnet_sbf_and_instruction_reconstruction.json",
        "evidence/spend_mainnet_sbf_and_instruction_reconstruction.json",
    ),
    (
        "results/spend/spend_mainnet_independent_rpc_reconciliation.json",
        "evidence/spend_mainnet_independent_rpc_reconciliation.json",
    ),
    (
        "tools/reconstruct_spend_mainnet_sbf.py",
        "tools/reconstruct_spend_mainnet_sbf.py",
    ),
    ("paper/aspis-spend/aspis-spend.pdf", "paper/aspis-spend.pdf"),
];

/// A file that has been placed in the bundle, with its measured commitments.
struct Placed {
    rel: String,
    bytes: u64,
    sha256: String,
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hex_lower(&hasher.finalize())
}

fn hex_lower(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn write_file(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, bytes).with_context(|| format!("writing {}", path.display()))?;
    Ok(())
}

fn place(bundle_dir: &Path, rel: &str, bytes: &[u8]) -> Result<Placed> {
    let dest = bundle_dir.join(rel);
    write_file(&dest, bytes)?;
    Ok(Placed {
        rel: rel.to_string(),
        bytes: bytes.len() as u64,
        sha256: sha256_hex(bytes),
    })
}

/// Assert the shipped evidence and binaries still report the pinned finalized
/// identities. Fails closed on any drift.
fn cross_check(placed: &[Placed], evidence_bytes: &[u8], statement_bytes: &[u8]) -> Result<()> {
    let evidence: Value = serde_json::from_slice(evidence_bytes).context("parsing evidence")?;
    let statement: Value = serde_json::from_slice(statement_bytes).context("parsing statement")?;

    let ft = &evidence["final_transaction"];
    if ft["signature"].as_str() != Some(TAG65_SIG) {
        bail!("evidence final_transaction.signature != pinned tag65 signature");
    }
    if ft["finalized_slot"].as_u64() != Some(TAG65_SLOT) {
        bail!("evidence final_transaction.finalized_slot != {TAG65_SLOT}");
    }
    if ft["compute_units_consumed"].as_u64() != Some(TAG65_CU) {
        bail!("evidence final_transaction.compute_units_consumed != {TAG65_CU}");
    }
    if evidence["program_id"].as_str() != Some(PROGRAM_ID) {
        bail!("evidence program_id != {PROGRAM_ID}");
    }
    if evidence["pool_after"]["address"].as_str() != Some(POOL) {
        bail!("evidence pool_after.address != {POOL}");
    }
    if evidence["nullifier_after"]["address"].as_str() != Some(NULLIFIER) {
        bail!("evidence nullifier_after.address != {NULLIFIER}");
    }
    if statement["deployment_domain_hex"].as_str() != Some(DEPLOY_DOMAIN) {
        bail!("statement deployment_domain_hex != {DEPLOY_DOMAIN}");
    }

    let sha_of = |rel: &str| -> Option<&str> {
        placed
            .iter()
            .find(|p| p.rel == rel)
            .map(|p| p.sha256.as_str())
    };
    if sha_of("proof/spend-q18-g37.bin") != Some(PROOF_SHA) {
        bail!("copied proof sha256 != pinned release proof");
    }
    if sha_of("program/aspis_verifier.so") != Some(SBF_SHA) {
        bail!("copied SBF sha256 != pinned deployed verifier (rebuild it first)");
    }
    Ok(())
}

pub fn build(workspace_root: &Path) -> Result<PathBuf> {
    let bundle_dir = workspace_root.join("release").join(RELEASE_ID);

    // Deterministic regeneration: start from an empty bundle directory.
    if bundle_dir.exists() {
        fs::remove_dir_all(&bundle_dir)
            .with_context(|| format!("clearing {}", bundle_dir.display()))?;
    }
    fs::create_dir_all(&bundle_dir)?;

    let mut placed: Vec<Placed> = Vec::new();
    let mut evidence_bytes: Vec<u8> = Vec::new();
    let mut statement_bytes: Vec<u8> = Vec::new();

    for (src_rel, dest_rel) in COPIES {
        let src = workspace_root.join(src_rel);
        let bytes = fs::read(&src)
            .with_context(|| format!("reading source artifact {}", src.display()))?;
        if *dest_rel == "evidence/mainnet-execution.json" {
            evidence_bytes = bytes.clone();
        }
        if *dest_rel == "proof/statement.json" {
            statement_bytes = bytes.clone();
        }
        placed.push(place(&bundle_dir, dest_rel, &bytes)?);
    }

    // Static templates.
    let readme = place(&bundle_dir, "README.md", BUNDLE_README.as_bytes())?;
    placed.push(readme);
    let verify = place(&bundle_dir, "verify.sh", VERIFY_SH.as_bytes())?;
    // Make verify.sh executable.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let p = bundle_dir.join("verify.sh");
        let mut perms = fs::metadata(&p)?.permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&p, perms)?;
    }
    placed.push(verify);

    if evidence_bytes.is_empty() || statement_bytes.is_empty() {
        bail!("internal: evidence/statement not captured during copy");
    }
    cross_check(&placed, &evidence_bytes, &statement_bytes)?;

    // manifest.json objects, sorted by path for a stable ordering.
    let mut sorted = placed.iter().collect::<Vec<_>>();
    sorted.sort_by(|a, b| a.rel.cmp(&b.rel));
    let mut objects = Map::new();
    for p in &sorted {
        objects.insert(
            p.rel.clone(),
            json!({ "bytes": p.bytes, "sha256": p.sha256 }),
        );
    }

    let evidence: Value = serde_json::from_slice(&evidence_bytes)?;
    let generated_at = evidence["generated_at_utc"].as_str().unwrap_or("");
    let genesis = evidence["genesis_hash"].as_str().unwrap_or("");

    let manifest = json!({
        "schema_version": 1,
        "artifact": "aspis_spend_q18_g37_mainnet_release_bundle",
        "release_id": RELEASE_ID,
        "network": "mainnet-beta",
        "mainnet_genesis_hash": genesis,
        "generated_at_utc": generated_at,
        "finalized_transaction": {
            "signature": TAG65_SIG,
            "finalized_slot": TAG65_SLOT,
            "compute_units_consumed": TAG65_CU,
        },
        "program_id": PROGRAM_ID,
        "pool": POOL,
        "nullifier": NULLIFIER,
        "deployment_domain_hex": DEPLOY_DOMAIN,
        "proof_sha256": PROOF_SHA,
        "sbf_sha256": SBF_SHA,
        "verifier": "verify.sh",
        "objects": Value::Object(objects),
    });

    let manifest_bytes = format!("{}\n", serde_json::to_string_pretty(&manifest)?);
    write_file(&bundle_dir.join("manifest.json"), manifest_bytes.as_bytes())?;
    let manifest_placed = Placed {
        rel: "manifest.json".to_string(),
        bytes: manifest_bytes.len() as u64,
        sha256: sha256_hex(manifest_bytes.as_bytes()),
    };

    // SHA256SUMS covers every file except itself, sorted by path.
    let mut all: Vec<&Placed> = placed.iter().collect();
    all.push(&manifest_placed);
    all.sort_by(|a, b| a.rel.cmp(&b.rel));
    let mut sums = String::new();
    for p in &all {
        sums.push_str(&format!("{}  {}\n", p.sha256, p.rel));
    }
    write_file(&bundle_dir.join("SHA256SUMS"), sums.as_bytes())?;

    Ok(bundle_dir)
}

/// Entry point used by `main.rs`.
pub fn run(workspace_root: &Path) -> Result<()> {
    let workspace_root = workspace_root
        .canonicalize()
        .map_err(|e| anyhow!("resolving workspace root: {e}"))?;
    let bundle_dir = build(&workspace_root)?;
    eprintln!(
        "spend-bundle: wrote {} objects to {}; run ./verify.sh from there",
        COPIES.len() + 2,
        bundle_dir.display()
    );
    Ok(())
}
