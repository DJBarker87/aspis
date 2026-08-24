//! Local-validator measurement of the first V6 verifier slice.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{bail, ensure, Context, Result};
use serde::Serialize;
use sha2::{Digest as _, Sha256};
use solana_sdk::pubkey::Pubkey;

use aspis_core::v6_onefold::{
    binary_frontier_nodes, V6_HARD_BODY_LIMIT, V6_MAX_BODY_BYTES, V6_QUERY_COUNT,
};
use aspis_verifier::v6_cu_probe::{V6_CU_PROBE_TAG, V6_CU_PROBE_WIRE_BYTES};
use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;

use crate::spend_measure::{parse_cu_markers, simulate_readonly_program_account_instructions};

const REPEATS: usize = 3;
const MAX_FRONTIER_QUERIES: [u32; V6_QUERY_COUNT] = [
    122_108, 40_038, 180_031, 111_504, 57_828, 27_366, 58_493, 6_257, 191_948, 128_942, 244_032,
    98_351, 184_446, 150_408, 7_983, 33_159,
];

#[derive(Serialize)]
struct V6OneFoldCuSummary {
    scope: &'static str,
    profile: &'static str,
    proof_body_bytes: usize,
    hard_limit_bytes: usize,
    margin_bytes: usize,
    frontier_nodes_per_tree: usize,
    queries: [u32; V6_QUERY_COUNT],
    compute_units: u64,
    repeated_compute_units: Vec<u64>,
    deterministic_three_of_three: bool,
    phase_markers: Vec<crate::spend_measure::CuMarker>,
    sbf_path: String,
    sbf_bytes: usize,
    sbf_sha256: String,
    build_command: &'static str,
    conclusion: &'static str,
}

pub struct V6OneFoldCuOutcome {
    pub compute_units: u64,
    pub path: PathBuf,
}

fn workspace_root() -> Result<PathBuf> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .context("no workspace root")
}

fn build_sbf(root: &Path) -> Result<PathBuf> {
    let status = Command::new("cargo-build-sbf")
        .env("NO_DNA", "1")
        .arg("--manifest-path")
        .arg(root.join("programs/aspis-verifier/Cargo.toml"))
        .arg("--no-default-features")
        .arg("--features")
        .arg("v6-cu-probe")
        .status()
        .context("cargo-build-sbf not found on PATH")?;
    if !status.success() {
        bail!("V6 CU probe SBF build failed");
    }
    let built = root.join("target/deploy/aspis_verifier.so");
    ensure!(built.is_file(), "missing {}", built.display());
    let pinned = root.join("target/deploy/aspis_verifier_v6_onefold_probe.so");
    fs::copy(&built, &pinned).with_context(|| format!("pin V6 probe {}", pinned.display()))?;
    Ok(pinned)
}

fn sealed_proof_account(body: &[u8]) -> Vec<u8> {
    let mut account = vec![0u8; PROOF_ACCOUNT_HEADER_LEN + body.len()];
    account[0..4].copy_from_slice(b"ASPU");
    account[4..8].copy_from_slice(&(body.len() as u32).to_le_bytes());
    account[PROOF_ACCOUNT_HEADER_LEN..].copy_from_slice(body);
    account
}

fn instruction(frontier: usize) -> Vec<u8> {
    let mut wire = Vec::with_capacity(V6_CU_PROBE_WIRE_BYTES);
    wire.push(V6_CU_PROBE_TAG);
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    for query in MAX_FRONTIER_QUERIES {
        wire.extend_from_slice(&query.to_le_bytes());
    }
    wire
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub fn run(results_dir: &Path) -> Result<V6OneFoldCuOutcome> {
    ensure!(V6_MAX_BODY_BYTES < V6_HARD_BODY_LIMIT);
    let frontier = binary_frontier_nodes(MAX_FRONTIER_QUERIES, 18)
        .map_err(|error| anyhow::anyhow!("invalid pinned query schedule: {error:?}"))?;
    ensure!(frontier == 209, "pinned V6 schedule frontier changed");

    let root = workspace_root()?;
    let sbf = build_sbf(&root)?;
    let sbf_bytes = fs::read(&sbf).with_context(|| format!("read {}", sbf.display()))?;
    let body = vec![0u8; V6_MAX_BODY_BYTES];
    let account = sealed_proof_account(&body);
    let wires = vec![instruction(frontier); REPEATS];
    let simulations = simulate_readonly_program_account_instructions(
        &sbf,
        Pubkey::new_unique(),
        aspis_verifier::id(),
        &account,
        &wires,
    )?;
    ensure!(simulations.len() == REPEATS);
    let repeated_compute_units = simulations
        .iter()
        .map(|result| result.units)
        .collect::<Vec<_>>();
    let compute_units = repeated_compute_units[0];
    let deterministic_three_of_three = repeated_compute_units
        .iter()
        .all(|units| *units == compute_units);
    ensure!(
        deterministic_three_of_three,
        "V6 probe CU was not deterministic"
    );
    let phase_markers = parse_cu_markers(&simulations[0].logs, "aspis-v6-cu:");
    ensure!(phase_markers.len() == 5, "V6 probe omitted phase markers");

    let path = results_dir.join("v6_onefold_packed_final256_cu.json");
    let summary = V6OneFoldCuSummary {
        scope: "isolated local-validator packed parsing, q16 frontier derivation, and sixteen packed final256 evaluations; not a complete V6 verifier",
        profile: "B10, 26 M31 C1 columns + 3 QM31 C2 columns, q16, frontier cap 209",
        proof_body_bytes: V6_MAX_BODY_BYTES,
        hard_limit_bytes: V6_HARD_BODY_LIMIT,
        margin_bytes: V6_HARD_BODY_LIMIT - V6_MAX_BODY_BYTES,
        frontier_nodes_per_tree: frontier,
        queries: MAX_FRONTIER_QUERIES,
        compute_units,
        repeated_compute_units,
        deterministic_three_of_three,
        phase_markers,
        sbf_path: sbf
            .strip_prefix(&root)
            .unwrap_or(&sbf)
            .display()
            .to_string(),
        sbf_bytes: sbf_bytes.len(),
        sbf_sha256: hex(&Sha256::digest(&sbf_bytes)),
        build_command: "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v6-cu-probe",
        conclusion: "This result measures only the first exact implementation slice. Merkle authentication, transcript, relation checks, semantic terminal, and state transition must be added before applying the 1.35M-CU release gate.",
    };
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V6OneFoldCuOutcome {
        compute_units,
        path,
    })
}
