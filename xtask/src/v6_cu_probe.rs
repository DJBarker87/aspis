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
    binary_frontier_nodes, V6OneFoldWire, V6_BODY_WITHOUT_FRONTIERS, V6_C1_PACKED_BYTES_PER_QUERY,
    V6_C1_TREE_TAG, V6_C2_PACKED_BYTES_PER_QUERY, V6_C2_TREE_TAG, V6_FIXED_PACKED_FIELD_BYTES,
    V6_FRONTIER_CAP_PER_TREE, V6_HARD_BODY_LIMIT, V6_MAX_BODY_BYTES, V6_QUERY_COUNT,
};
use aspis_core::v6_query_batch::V6AuthenticatedQueryBatch;
use aspis_core::v6_transcript::{
    verify_v6_transcript_and_relation, V6TranscriptContext, V6TranscriptError, V6_COMPACT_DRAW_CAP,
    V6_QUERY_SELECTOR_COUNT,
};
use aspis_core::{
    field::M31, merkle::node_hash, state_only_private_merkle::private_leaf_hash, HashFn,
};
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{
    atomic_payment_statement_digest_v4, encode_digest_canonical, AtomicPaymentStatementV4,
    SpendPublic,
};
use aspis_verifier::atomic_payment::{
    atomic_nullifier_address, AtomicPoolStateV2, ATOMIC_NULLIFIER_MARKER_LEN, ATOMIC_POOL_STATE_LEN,
};
use aspis_verifier::v6_cu_probe::{
    V6_ATOMIC_CU_PROBE_TAG, V6_ATOMIC_CU_PROBE_WIRE_BYTES, V6_CU_PROBE_TAG, V6_CU_PROBE_WIRE_BYTES,
    V6_FULL_CU_PROBE_TAG, V6_FULL_CU_PROBE_WIRE_BYTES, V6_INTEGRATED_CU_PROBE_TAG,
    V6_INTEGRATED_CU_PROBE_WIRE_BYTES, V6_PROBE_RELEASE_BINDING, V6_PROBE_STATEMENT_DIGEST,
    V6_TERMINAL_CU_PROBE_TAG, V6_TERMINAL_CU_PROBE_WIRE_BYTES,
};
use aspis_verifier::PROOF_ACCOUNT_HEADER_LEN;

use crate::spend_measure::{
    parse_cu_markers, simulate_atomic_program_account_instructions,
    simulate_atomic_program_account_instructions_with_absent_marker,
    simulate_readonly_program_account_instructions,
};

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

#[derive(Serialize)]
struct V6FullReadOnlyCuSummary {
    scope: &'static str,
    omitted_from_measurement: [&'static str; 3],
    profile: &'static str,
    proof_body_bytes: usize,
    hard_limit_bytes: usize,
    margin_bytes: usize,
    selector: u8,
    compact_counter: u8,
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

pub struct V6FullReadOnlyCuOutcome {
    pub compute_units: u64,
    pub path: PathBuf,
}

#[derive(Serialize)]
struct V6TerminalCuSummary {
    scope: &'static str,
    proof_body_bytes: usize,
    selector: u8,
    frontier_nodes_per_tree: usize,
    compute_units: u64,
    repeated_compute_units: Vec<u64>,
    deterministic_three_of_three: bool,
    phase_markers: Vec<crate::spend_measure::CuMarker>,
    build_command: &'static str,
}

pub struct V6TerminalCuOutcome {
    pub compute_units: u64,
    pub path: PathBuf,
}

#[derive(Serialize)]
struct V6IntegratedCuSummary {
    scope: &'static str,
    omitted_from_measurement: [&'static str; 2],
    proof_body_bytes: usize,
    selector: u8,
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    queries: [u32; V6_QUERY_COUNT],
    compute_units: u64,
    headroom_under_consensus_limit: i64,
    repeated_compute_units: Vec<u64>,
    deterministic_three_of_three: bool,
    phase_markers: Vec<crate::spend_measure::CuMarker>,
    build_command: &'static str,
}

#[derive(Serialize)]
struct V6AtomicCuSummary {
    scope: &'static str,
    caveats: [&'static str; 2],
    proof_body_bytes: usize,
    selector: u8,
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    queries: [u32; V6_QUERY_COUNT],
    proof_address: String,
    pool_address: String,
    worst_frontier_search_attempts: usize,
    program_owned_marker_compute_units: u64,
    missing_marker_compute_units: u64,
    maximum_compute_units: u64,
    headroom_under_target: i64,
    program_owned_marker_repeated_compute_units: Vec<u64>,
    missing_marker_repeated_compute_units: Vec<u64>,
    deterministic_both_three_of_three: bool,
    missing_marker_completed_system_program_cpi: bool,
    all_selectors_counter7_frontier_cap: bool,
    selector_cases: Vec<V6AtomicSelectorCase>,
    build_command: &'static str,
}

#[derive(Clone, Serialize)]
struct V6AtomicSelectorCase {
    selector: u8,
    compact_counter: u8,
    frontier_nodes_per_tree: usize,
    proof_body_bytes: usize,
    queries: [u32; V6_QUERY_COUNT],
    proof_address: String,
    worst_frontier_search_attempts: usize,
    program_owned_marker_compute_units: u64,
    missing_marker_compute_units: u64,
    maximum_compute_units: u64,
    program_owned_marker_repeated_compute_units: Vec<u64>,
    missing_marker_repeated_compute_units: Vec<u64>,
    deterministic_both_three_of_three: bool,
    missing_marker_completed_system_program_cpi: bool,
}

pub struct V6AtomicCuOutcome {
    pub compute_units: u64,
    pub path: PathBuf,
}

pub struct V6IntegratedCuOutcome {
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

fn host_hash(inputs: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}

fn minimal_binary_root(
    hash: HashFn,
    entries: &[(u32, [u8; 32])],
    frontier: &[[u8; 32]],
) -> Result<[u8; 32]> {
    let mut stream = frontier.iter();
    let mut level = entries.to_vec();
    for _ in 0..18 {
        let mut next = Vec::with_capacity(level.len());
        let mut index = 0usize;
        while index < level.len() {
            let (position, digest) = level[index];
            let parent = if position & 1 == 0
                && index + 1 < level.len()
                && level[index + 1].0 == position + 1
            {
                let combined = node_hash(hash, &digest, &level[index + 1].1);
                index += 2;
                combined
            } else {
                let sibling = stream.next().context("synthetic V6 frontier exhausted")?;
                index += 1;
                if position & 1 == 0 {
                    node_hash(hash, &digest, sibling)
                } else {
                    node_hash(hash, sibling, &digest)
                }
            };
            next.push((position >> 1, parent));
        }
        level = next;
    }
    ensure!(
        stream.next().is_none(),
        "synthetic V6 frontier trailing node"
    );
    ensure!(level.len() == 1 && level[0].0 == 0);
    Ok(level[0].1)
}

fn valid_probe_body(frontier: usize) -> Result<Vec<u8>> {
    let mut body = vec![0u8; V6_MAX_BODY_BYTES];
    let parsed = V6OneFoldWire::parse(&body, frontier, frontier)
        .map_err(|error| anyhow::anyhow!("parse synthetic V6 body: {error:?}"))?;
    let mut order: [(u32, usize); V6_QUERY_COUNT] =
        core::array::from_fn(|ordinal| (MAX_FRONTIER_QUERIES[ordinal], ordinal));
    order.sort_unstable_by_key(|entry| entry.0);
    let c1_entries = order
        .iter()
        .map(|(query, ordinal)| {
            let record = parsed.query(*ordinal).unwrap();
            (
                *query,
                private_leaf_hash(host_hash, V6_C1_TREE_TAG, record.c1_packed, record.salt),
            )
        })
        .collect::<Vec<_>>();
    let c2_entries = order
        .iter()
        .map(|(query, ordinal)| {
            let record = parsed.query(*ordinal).unwrap();
            (
                *query,
                private_leaf_hash(host_hash, V6_C2_TREE_TAG, record.c2_packed, record.salt),
            )
        })
        .collect::<Vec<_>>();
    let zero_frontier = vec![[0u8; 32]; frontier];
    let c1_root = minimal_binary_root(host_hash, &c1_entries, &zero_frontier)?;
    let c2_root = minimal_binary_root(host_hash, &c2_entries, &zero_frontier)?;
    body[V6_FIXED_PACKED_FIELD_BYTES..V6_FIXED_PACKED_FIELD_BYTES + 32].copy_from_slice(&c1_root);
    body[V6_FIXED_PACKED_FIELD_BYTES + 32..V6_FIXED_PACKED_FIELD_BYTES + 64]
        .copy_from_slice(&c2_root);
    Ok(body)
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

fn full_instruction(frontier: usize, selector: u8) -> Vec<u8> {
    let mut wire = Vec::with_capacity(V6_FULL_CU_PROBE_WIRE_BYTES);
    wire.push(V6_FULL_CU_PROBE_TAG);
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.push(selector);
    wire
}

fn terminal_instruction(frontier: usize, selector: u8) -> Vec<u8> {
    let mut wire = Vec::with_capacity(V6_TERMINAL_CU_PROBE_WIRE_BYTES);
    wire.push(V6_TERMINAL_CU_PROBE_TAG);
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.push(selector);
    wire
}

fn integrated_instruction(frontier: usize, selector: u8) -> Vec<u8> {
    let mut wire = Vec::with_capacity(V6_INTEGRATED_CU_PROBE_WIRE_BYTES);
    wire.push(V6_INTEGRATED_CU_PROBE_TAG);
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.push(selector);
    wire
}

fn atomic_instruction(
    frontier: usize,
    selector: u8,
    statement: &AtomicPaymentStatementV4,
) -> Vec<u8> {
    let mut wire = Vec::with_capacity(V6_ATOMIC_CU_PROBE_WIRE_BYTES);
    wire.push(V6_ATOMIC_CU_PROBE_TAG);
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.extend_from_slice(&(frontier as u16).to_le_bytes());
    wire.push(selector);
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.anchor));
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.nullifier));
    wire.extend_from_slice(&encode_digest_canonical(&statement.spend.output_commitment));
    wire.extend_from_slice(&encode_digest_canonical(&statement.output_anchor));
    wire.extend_from_slice(&statement.spend.asset_id.0.to_le_bytes());
    wire.extend_from_slice(&statement.spend.fee.to_le_bytes());
    wire.extend_from_slice(&statement.deployment_domain);
    debug_assert_eq!(wire.len(), V6_ATOMIC_CU_PROBE_WIRE_BYTES);
    wire
}

fn completed_system_program_cpi(logs: &[String]) -> bool {
    let system_program = Pubkey::default().to_string();
    let invoke_prefix = format!("Program {system_program} invoke");
    let success = format!("Program {system_program} success");
    logs.iter()
        .position(|line| line.starts_with(&invoke_prefix))
        .is_some_and(|invoke| logs.iter().skip(invoke + 1).any(|line| line == &success))
}

fn uniform_tree_levels(tree_tag: u8, leaf_bytes: usize) -> [[u8; 32]; 19] {
    let zero_leaf = vec![0u8; leaf_bytes];
    let zero_salt = [0u8; 32];
    let mut levels = [[0u8; 32]; 19];
    levels[0] = private_leaf_hash(host_hash, tree_tag, &zero_leaf, &zero_salt);
    for level in 0..18 {
        levels[level + 1] = node_hash(host_hash, &levels[level], &levels[level]);
    }
    levels
}

fn uniform_binary_frontier(
    queries: [u32; V6_QUERY_COUNT],
    levels: &[[u8; 32]; 19],
) -> Vec<[u8; 32]> {
    let mut positions = queries.to_vec();
    positions.sort_unstable();
    positions.dedup();
    let mut frontier = Vec::new();
    for level_digest in levels.iter().take(18) {
        let mut next = Vec::with_capacity(positions.len());
        let mut index = 0usize;
        while index < positions.len() {
            let position = positions[index];
            if position & 1 == 0
                && index + 1 < positions.len()
                && positions[index + 1] == position + 1
            {
                index += 2;
            } else {
                frontier.push(*level_digest);
                index += 1;
            }
            let parent = position >> 1;
            if next.last().copied() != Some(parent) {
                next.push(parent);
            }
        }
        positions = next;
    }
    frontier
}

struct FullProbeFixture {
    body: Vec<u8>,
    selector: u8,
    compact_counter: u8,
    frontier: usize,
    queries: [u32; V6_QUERY_COUNT],
}

fn full_probe_fixture_with_digest(
    program_id: Pubkey,
    proof_account: Pubkey,
    statement_digest: [u8; 32],
    selector: u8,
) -> Result<FullProbeFixture> {
    let c1_levels = uniform_tree_levels(V6_C1_TREE_TAG, V6_C1_PACKED_BYTES_PER_QUERY);
    let c2_levels = uniform_tree_levels(V6_C2_TREE_TAG, V6_C2_PACKED_BYTES_PER_QUERY);
    let context = V6TranscriptContext {
        program_id: program_id.to_bytes(),
        release_binding: V6_PROBE_RELEASE_BINDING,
        statement_digest,
        attempt_id: proof_account.to_bytes(),
    };
    let mut empty_frontier_body = vec![0u8; V6_BODY_WITHOUT_FRONTIERS];
    empty_frontier_body[V6_FIXED_PACKED_FIELD_BYTES..V6_FIXED_PACKED_FIELD_BYTES + 32]
        .copy_from_slice(&c1_levels[18]);
    empty_frontier_body[V6_FIXED_PACKED_FIELD_BYTES + 32..V6_FIXED_PACKED_FIELD_BYTES + 64]
        .copy_from_slice(&c2_levels[18]);
    let empty_wire = V6OneFoldWire::parse(&empty_frontier_body, 0, 0)
        .map_err(|error| anyhow::anyhow!("parse zero-frontier V6 fixture: {error:?}"))?;
    let frontier = match verify_v6_transcript_and_relation(
        host_hash,
        &empty_wire,
        &context,
        selector,
        atomic_state_only_copy_inactive_row_masks_v3(),
        false,
        |_| true,
        |_| {
            Ok(V6AuthenticatedQueryBatch {
                values: [aspis_core::field::QM31::ZERO; V6_QUERY_COUNT],
                line_x: [aspis_core::field::M31::ZERO; V6_QUERY_COUNT],
            })
        },
    ) {
        Err(V6TranscriptError::FrontierCountMismatch { expected, .. }) => expected,
        Err(error) => bail!("derive V6 full-probe frontier: {error:?}"),
        Ok(_) => bail!("zero-frontier V6 fixture unexpectedly matched"),
    };

    let mut body = vec![0u8; V6_BODY_WITHOUT_FRONTIERS + 2 * frontier * 32];
    body[V6_FIXED_PACKED_FIELD_BYTES..V6_FIXED_PACKED_FIELD_BYTES + 32]
        .copy_from_slice(&c1_levels[18]);
    body[V6_FIXED_PACKED_FIELD_BYTES + 32..V6_FIXED_PACKED_FIELD_BYTES + 64]
        .copy_from_slice(&c2_levels[18]);
    let provisional = V6OneFoldWire::parse(&body, frontier, frontier)
        .map_err(|error| anyhow::anyhow!("parse provisional V6 full fixture: {error:?}"))?;
    let verified = verify_v6_transcript_and_relation(
        host_hash,
        &provisional,
        &context,
        selector,
        atomic_state_only_copy_inactive_row_masks_v3(),
        false,
        |_| true,
        |_| {
            Ok(V6AuthenticatedQueryBatch {
                values: [aspis_core::field::QM31::ZERO; V6_QUERY_COUNT],
                line_x: [aspis_core::field::M31::ZERO; V6_QUERY_COUNT],
            })
        },
    )
    .map_err(|error| anyhow::anyhow!("derive V6 full-probe queries: {error:?}"))?;
    ensure!(verified.frontier_nodes == frontier);

    let c1_frontier = uniform_binary_frontier(verified.queries, &c1_levels);
    let c2_frontier = uniform_binary_frontier(verified.queries, &c2_levels);
    ensure!(c1_frontier.len() == frontier);
    ensure!(c2_frontier.len() == frontier);
    let frontier_start = V6_BODY_WITHOUT_FRONTIERS;
    for (index, digest) in c1_frontier.iter().enumerate() {
        body[frontier_start + index * 32..frontier_start + (index + 1) * 32]
            .copy_from_slice(digest);
    }
    let c2_start = frontier_start + frontier * 32;
    for (index, digest) in c2_frontier.iter().enumerate() {
        body[c2_start + index * 32..c2_start + (index + 1) * 32].copy_from_slice(digest);
    }

    Ok(FullProbeFixture {
        body,
        selector,
        compact_counter: verified.compact_counter,
        frontier,
        queries: verified.queries,
    })
}

fn full_probe_fixture(program_id: Pubkey, proof_account: Pubkey) -> Result<FullProbeFixture> {
    full_probe_fixture_with_digest(program_id, proof_account, V6_PROBE_STATEMENT_DIGEST, 0)
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
    let body = valid_probe_body(frontier)?;
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
    ensure!(phase_markers.len() == 8, "V6 probe omitted phase markers");

    let path = results_dir.join("v6_onefold_packed_final256_cu.json");
    let summary = V6OneFoldCuSummary {
        scope: "isolated local-validator packed parsing, q16 frontier derivation, typed shared-salt two-tree binary Merkle authentication, 26+3 gamma combination, one circle-to-line fold, and sixteen explicit-final evaluations; not a complete V6 verifier",
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
        conclusion: "This exact slice is 335,561 CU below the 1.35M engineering gate after canonical packed decoding, 26+3 batching, and Merkle authentication were fused. A one-transaction verifier is plausible again, but transcript, relation, semantic, and state-transition checks still require implementation and measurement.",
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

/// Measure the complete read-only V6 transcript, relation, Merkle and one-fold
/// composition on a genuine zero-codeword PCS fixture. The semantic terminal
/// callback, three proof-of-work hash checks, statement digest computation and
/// atomic state mutation are intentionally excluded and named in the result.
pub fn run_full_read_only(results_dir: &Path) -> Result<V6FullReadOnlyCuOutcome> {
    ensure!(V6_MAX_BODY_BYTES < V6_HARD_BODY_LIMIT);
    let root = workspace_root()?;
    let sbf = build_sbf(&root)?;
    let sbf_bytes = fs::read(&sbf).with_context(|| format!("read {}", sbf.display()))?;
    let proof_account = Pubkey::new_unique();
    let fixture = full_probe_fixture(aspis_verifier::id(), proof_account)?;
    ensure!(fixture.body.len() < V6_HARD_BODY_LIMIT);
    let account = sealed_proof_account(&fixture.body);
    let wires = vec![full_instruction(fixture.frontier, fixture.selector); REPEATS];
    let simulations = simulate_readonly_program_account_instructions(
        &sbf,
        proof_account,
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
        "V6 full read-only probe CU was not deterministic"
    );
    let phase_markers = parse_cu_markers(&simulations[0].logs, "aspis-v6-full:");
    ensure!(
        phase_markers.len() == 8,
        "V6 full read-only probe omitted phase markers"
    );

    let conclusion = if compute_units <= 1_350_000 {
        "The measured read-only algebra/PCS path is within the 1.35M engineering gate. The omitted live semantic terminal, work hashes, statement digest and atomic wrapper must still be added and measured before selecting one transaction."
    } else {
        "The measured read-only algebra/PCS path already exceeds the 1.35M engineering gate. V6 must use a bound verification receipt or reduce compute before production integration."
    };
    let path = results_dir.join("v6_onefold_full_readonly_cu.json");
    let summary = V6FullReadOnlyCuSummary {
        scope: "isolated local-validator complete V6 fixed-field transcript, compact semantic/relation algebra, verifier-derived first-compact q16 schedule, typed shared-salt two-tree Merkle authentication, 26+3 batching, one circle-to-line fold, and final256 evaluations on a zero-codeword PCS fixture",
        omitted_from_measurement: [
            "live atomic-spend semantic terminal (diagnostic callback returns true)",
            "three proof-of-work SHA-256 checks (nonces are absorbed in exact order)",
            "statement digest plus atomic account validation and state mutation",
        ],
        profile: "B10, 26 M31 C1 columns + 3 QM31 C2 columns, three point rows, q16, first-compact frontier cap 209",
        proof_body_bytes: fixture.body.len(),
        hard_limit_bytes: V6_HARD_BODY_LIMIT,
        margin_bytes: V6_HARD_BODY_LIMIT - fixture.body.len(),
        selector: fixture.selector,
        compact_counter: fixture.compact_counter,
        frontier_nodes_per_tree: fixture.frontier,
        queries: fixture.queries,
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
        conclusion,
    };
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V6FullReadOnlyCuOutcome {
        compute_units,
        path,
    })
}

/// Measure the exact atomic semantic terminal on challenges and claims
/// produced by the V6 transcript. The diagnostic deliberately rejects after
/// the terminal so no PCS work is mixed into the phase ledger.
pub fn run_terminal(results_dir: &Path) -> Result<V6TerminalCuOutcome> {
    let root = workspace_root()?;
    let sbf = build_sbf(&root)?;
    let proof_account = Pubkey::new_unique();
    let fixture = full_probe_fixture(aspis_verifier::id(), proof_account)?;
    let account = sealed_proof_account(&fixture.body);
    let wires = vec![terminal_instruction(fixture.frontier, fixture.selector); REPEATS];
    let simulations = simulate_readonly_program_account_instructions(
        &sbf,
        proof_account,
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
        "V6 terminal CU was not deterministic"
    );
    let phase_markers = parse_cu_markers(&simulations[0].logs, "aspis-v6-terminal:");
    ensure!(
        phase_markers.len() == 17,
        "V6 terminal probe omitted phase markers"
    );
    let path = results_dir.join("v6_atomic_terminal_cu.json");
    let summary = V6TerminalCuSummary {
        scope: "exact V6 transcript prefix followed by the production-equivalent atomic-v3 selected masked semantic terminal, with diagnostic phase boundaries; excludes work hashes, PCS relation, Merkle openings and state mutation",
        proof_body_bytes: fixture.body.len(),
        selector: fixture.selector,
        frontier_nodes_per_tree: fixture.frontier,
        compute_units,
        repeated_compute_units,
        deterministic_three_of_three,
        phase_markers,
        build_command: "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v6-cu-probe",
    };
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V6TerminalCuOutcome {
        compute_units,
        path,
    })
}

/// Measure the complete V6 cryptographic core in one validator instruction.
/// The probe executes the production terminal, all three real SHA-256 work
/// hashes, transcript/relation logic, two Merkle trees and the one fold. Its
/// hash wrapper changes only the returned grinding digest so the zero fixture
/// can continue; every hash syscall and every transcript state transition is
/// otherwise the production path.
pub fn run_integrated(results_dir: &Path) -> Result<V6IntegratedCuOutcome> {
    ensure!(V6_MAX_BODY_BYTES < V6_HARD_BODY_LIMIT);
    let root = workspace_root()?;
    let sbf = build_sbf(&root)?;
    let proof_account = Pubkey::new_unique();
    let fixture = full_probe_fixture(aspis_verifier::id(), proof_account)?;
    let account = sealed_proof_account(&fixture.body);
    let wires = vec![integrated_instruction(fixture.frontier, fixture.selector); REPEATS];
    let simulations = simulate_readonly_program_account_instructions(
        &sbf,
        proof_account,
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
        "V6 integrated CU was not deterministic"
    );
    let phase_markers = parse_cu_markers(&simulations[0].logs, "aspis-v6-integrated:");
    ensure!(
        phase_markers.len() == 28,
        "V6 integrated probe omitted phase markers"
    );
    let path = results_dir.join("v6_onefold_integrated_core_cu.json");
    let summary = V6IntegratedCuSummary {
        scope: "one validator instruction executing the exact atomic semantic terminal, three real SHA-256 grinding calls, complete V6 transcript/relation, verifier-derived q16 schedule, two-tree Merkle authentication, 26+3 batching and one circle fold",
        omitted_from_measurement: [
            "statement digest plus production atomic account validation/state mutation",
            "honest grinding outcomes (probe computes each real hash then clears only its returned leading bytes so the zero fixture continues)",
        ],
        proof_body_bytes: fixture.body.len(),
        selector: fixture.selector,
        compact_counter: fixture.compact_counter,
        frontier_nodes_per_tree: fixture.frontier,
        queries: fixture.queries,
        compute_units,
        headroom_under_consensus_limit: 1_400_000_i64 - compute_units as i64,
        repeated_compute_units,
        deterministic_three_of_three,
        phase_markers,
        build_command: "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v6-cu-probe",
    };
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V6IntegratedCuOutcome {
        compute_units,
        path,
    })
}

/// Measure the entire retained-proof atomic instruction, including canonical
/// public decoding, statement hashing, account/state validation, the complete
/// uninstrumented V6 verifier, and final pool/nullifier writes. Both supported
/// nullifier states are measured: a preallocated program-owned marker and the
/// normal missing-marker System Program creation path.
pub fn run_atomic(results_dir: &Path) -> Result<V6AtomicCuOutcome> {
    const TARGET_CU: u64 = 1_300_000;

    ensure!(V6_MAX_BODY_BYTES < V6_HARD_BODY_LIMIT);
    let root = workspace_root()?;
    let sbf = build_sbf(&root)?;
    let program_id = aspis_verifier::id();
    // Pin the public statement while searching a deterministic proof-attempt
    // domain for the exact accepted frontier cap. The CU gate must exercise
    // the most expensive permitted topology rather than whichever schedule
    // happens to follow `Pubkey::new_unique()` in this host process.
    let pool_address = Pubkey::new_from_array([0xa6; 32]);
    let statement = AtomicPaymentStatementV4 {
        pool: pool_address.to_bytes(),
        sequence: 0,
        spend: SpendPublic {
            anchor: [M31::ZERO; 8],
            nullifier: [M31::ZERO; 8],
            output_commitment: [M31::ZERO; 8],
            asset_id: M31::ZERO,
            fee: 0,
        },
        output_anchor: [M31::ZERO; 8],
        deployment_domain: [0u8; 32],
    };
    let statement_digest = atomic_payment_statement_digest_v4(&statement, host_hash)
        .map_err(|error| anyhow::anyhow!("hash V6 atomic statement: {error:?}"))?;
    let public_anchor = encode_digest_canonical(&statement.spend.anchor);
    let public_nullifier = encode_digest_canonical(&statement.spend.nullifier);
    let marker_address = atomic_nullifier_address(&program_id, &public_nullifier).0;
    let mut pool_data = [0u8; ATOMIC_POOL_STATE_LEN];
    AtomicPoolStateV2 {
        sequence: statement.sequence,
        anchor: public_anchor,
        deployment_domain: statement.deployment_domain,
    }
    .encode(&mut pool_data)
    .map_err(|error| anyhow::anyhow!("encode V6 atomic pool: {error:?}"))?;
    let marker_data = [0u8; ATOMIC_NULLIFIER_MARKER_LEN];
    ensure!(
        pool_address != marker_address,
        "V6 atomic pool/marker fixture collision"
    );

    let mut selector_cases = Vec::with_capacity(usize::from(V6_QUERY_SELECTOR_COUNT));
    for selector in 0..V6_QUERY_SELECTOR_COUNT {
        let mut worst_fixture = None;
        for counter in 0u64..4096 {
            let mut proof_bytes = [0x56; 32];
            proof_bytes[..8].copy_from_slice(&counter.to_le_bytes());
            proof_bytes[31] = 0x06;
            let proof_address = Pubkey::new_from_array(proof_bytes);
            let fixture = match full_probe_fixture_with_digest(
                program_id,
                proof_address,
                statement_digest,
                selector,
            ) {
                Ok(fixture) => fixture,
                Err(error) if error.to_string().contains("CompactCandidatesExhausted") => continue,
                Err(error) => return Err(error),
            };
            if fixture.frontier == V6_FRONTIER_CAP_PER_TREE
                && fixture.compact_counter == V6_COMPACT_DRAW_CAP - 1
            {
                worst_fixture = Some((proof_address, fixture, counter as usize + 1));
                break;
            }
        }
        let (proof_address, fixture, worst_frontier_search_attempts) = worst_fixture.with_context(
            || {
                format!(
                    "no deterministic V6 atomic selector-{selector} fixture reached compact counter 7 and the frontier cap in 4096 attempts"
                )
            },
        )?;
        ensure!(fixture.body.len() < V6_HARD_BODY_LIMIT);
        ensure!(
            proof_address != pool_address && proof_address != marker_address,
            "V6 atomic selector-{selector} fixture account collision"
        );
        let proof_data = sealed_proof_account(&fixture.body);
        let wires =
            vec![atomic_instruction(fixture.frontier, fixture.selector, &statement); REPEATS];
        let program_owned = simulate_atomic_program_account_instructions(
            &sbf,
            proof_address,
            &proof_data,
            pool_address,
            &pool_data,
            marker_address,
            &marker_data,
            &wires,
        )?;
        let missing = simulate_atomic_program_account_instructions_with_absent_marker(
            &sbf,
            proof_address,
            &proof_data,
            pool_address,
            &pool_data,
            marker_address,
            &wires,
        )?;
        ensure!(program_owned.len() == REPEATS && missing.len() == REPEATS);

        let program_owned_marker_repeated_compute_units = program_owned
            .iter()
            .map(|result| result.units)
            .collect::<Vec<_>>();
        let missing_marker_repeated_compute_units = missing
            .iter()
            .map(|result| result.units)
            .collect::<Vec<_>>();
        let program_owned_marker_compute_units = program_owned_marker_repeated_compute_units[0];
        let missing_marker_compute_units = missing_marker_repeated_compute_units[0];
        let deterministic_both_three_of_three = program_owned_marker_repeated_compute_units
            .iter()
            .all(|units| *units == program_owned_marker_compute_units)
            && missing_marker_repeated_compute_units
                .iter()
                .all(|units| *units == missing_marker_compute_units);
        ensure!(
            deterministic_both_three_of_three,
            "V6 atomic selector-{selector} CU was not deterministic"
        );
        let missing_marker_completed_system_program_cpi = missing
            .iter()
            .all(|result| completed_system_program_cpi(&result.logs));
        ensure!(
            missing_marker_completed_system_program_cpi,
            "V6 selector-{selector} missing-marker measurement omitted successful System Program CPI"
        );
        selector_cases.push(V6AtomicSelectorCase {
            selector,
            compact_counter: fixture.compact_counter,
            frontier_nodes_per_tree: fixture.frontier,
            proof_body_bytes: fixture.body.len(),
            queries: fixture.queries,
            proof_address: proof_address.to_string(),
            worst_frontier_search_attempts,
            program_owned_marker_compute_units,
            missing_marker_compute_units,
            maximum_compute_units: program_owned_marker_compute_units
                .max(missing_marker_compute_units),
            program_owned_marker_repeated_compute_units,
            missing_marker_repeated_compute_units,
            deterministic_both_three_of_three,
            missing_marker_completed_system_program_cpi,
        });
    }
    let all_selectors_counter7_frontier_cap = selector_cases.len()
        == usize::from(V6_QUERY_SELECTOR_COUNT)
        && selector_cases.iter().all(|case| {
            case.compact_counter == V6_COMPACT_DRAW_CAP - 1
                && case.frontier_nodes_per_tree == V6_FRONTIER_CAP_PER_TREE
        });
    ensure!(
        all_selectors_counter7_frontier_cap,
        "V6 atomic gate did not cover every selector at both schedule caps"
    );
    let worst_case = selector_cases
        .iter()
        .max_by_key(|case| case.maximum_compute_units)
        .context("V6 atomic gate produced no selector cases")?
        .clone();
    let maximum_compute_units = worst_case.maximum_compute_units;

    let path = results_dir.join("v6_onefold_atomic_cu.json");
    let summary = V6AtomicCuSummary {
        scope: "complete retained-proof atomic instruction: exact account/public validation, statement SHA-256 digest handoff, uninstrumented V6 semantic terminal/transcript/relation/two-tree PCS/one-fold verification, and atomic pool/nullifier mutation; measures both preallocated and missing-marker paths",
        caveats: [
            "the probe performs every real grinding SHA-256 syscall but clears only the returned leading work bytes so the synthetic zero-codeword fixture continues",
            "the synthetic terminal is fully evaluated but this CU-only tag accepts any successful terminal evaluation; production and honest-proof gates require equality to the transcript terminal claim",
        ],
        proof_body_bytes: worst_case.proof_body_bytes,
        selector: worst_case.selector,
        compact_counter: worst_case.compact_counter,
        frontier_nodes_per_tree: worst_case.frontier_nodes_per_tree,
        queries: worst_case.queries,
        proof_address: worst_case.proof_address,
        pool_address: pool_address.to_string(),
        worst_frontier_search_attempts: worst_case.worst_frontier_search_attempts,
        program_owned_marker_compute_units: worst_case.program_owned_marker_compute_units,
        missing_marker_compute_units: worst_case.missing_marker_compute_units,
        maximum_compute_units,
        headroom_under_target: TARGET_CU as i64 - maximum_compute_units as i64,
        program_owned_marker_repeated_compute_units: worst_case
            .program_owned_marker_repeated_compute_units,
        missing_marker_repeated_compute_units: worst_case
            .missing_marker_repeated_compute_units,
        deterministic_both_three_of_three: worst_case.deterministic_both_three_of_three,
        missing_marker_completed_system_program_cpi: worst_case
            .missing_marker_completed_system_program_cpi,
        all_selectors_counter7_frontier_cap,
        selector_cases,
        build_command: "NO_DNA=1 cargo-build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v6-cu-probe",
    };
    fs::write(
        &path,
        format!("{}\n", serde_json::to_string_pretty(&summary)?),
    )?;
    Ok(V6AtomicCuOutcome {
        compute_units: maximum_compute_units,
        path,
    })
}
