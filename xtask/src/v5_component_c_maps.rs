//! Offline generation and audit of the frozen-q18 Component-C `E` map.
//!
//! This command emits only the conditioned-view map. It deliberately does
//! not construct `F`, define a legal-difference space, assert C-DEC, modify a
//! verifier wire, or include the artifact in an SBF binary.

use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::field::QM31;
use aspis_prover::v5_mask::{
    component_c::{V5ComponentCLane, V5_C_FREE_COORDINATES},
    component_c_emat::{
        build_component_c_emat_kats, validate_component_c_emat_artifact, V5ComponentCEmat,
        V5ComponentCEmatKatMetadata, V5ComponentCFrozenESchedule, V5_C_EMAT_ARTIFACT_HEADER_BYTES,
        V5_C_EMAT_COLUMNS, V5_C_EMAT_LAYER_ZERO_ROWS, V5_C_EMAT_MATRIX_BYTES, V5_C_EMAT_QM31_BYTES,
        V5_C_EMAT_ROWS,
    },
    spend_messages::{
        V5_C1_LANES, V5_C2_LANES, V5_C2_LEAF_BYTES, V5_FIBRE_SLOTS, V5_LAYER_ZERO_LEAVES,
    },
};
use serde::Serialize;
use sha2::{Digest as _, Sha256};

const COMPONENT_C_HELPER: usize = 2;
const COMPONENT_C_RELATION_LANE: usize = V5_C1_LANES + COMPONENT_C_HELPER;
const ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_emat.bin";
const MANIFEST_FILE: &str = "v5_component_c_frozen_q18_emat.json";

const _: () = assert!(COMPONENT_C_HELPER < V5_C2_LANES);
const _: () = assert!(V5_C_EMAT_COLUMNS == V5_C_FREE_COORDINATES);
const _: () = assert!(V5_C2_LEAF_BYTES == V5_C2_LANES * V5_FIBRE_SLOTS * 16);

#[derive(Clone, Debug)]
pub struct V5ComponentCMapsOutcome {
    pub artifact_path: PathBuf,
    pub manifest_path: PathBuf,
    pub artifact_bytes: usize,
    pub artifact_sha256: String,
    pub matrix_sha256: String,
    pub generation_ms: u64,
    pub total_ms: u64,
}

#[derive(Serialize)]
struct Manifest {
    schema: &'static str,
    version: u32,
    status: &'static str,
    scope: Scope,
    reproducible_command: &'static str,
    frozen_input: FrozenInput,
    matrix: MatrixMetadata,
    artifact: ArtifactMetadata,
    correspondence_kats: CorrespondenceKats,
    benchmark_policy: &'static str,
    remaining_blockers: Vec<&'static str>,
}

#[derive(Serialize)]
struct Scope {
    emitted: &'static str,
    f_matrix_emitted: bool,
    legal_difference_space_defined: bool,
    delta_defined: bool,
    c_dec_claimed: bool,
    verifier_wire_changed: bool,
    production_or_sbf_inclusion: bool,
}

#[derive(Serialize)]
struct FrozenInput {
    statement_digest: String,
    transcript_state_after_queries: String,
    roots: Vec<String>,
    query_selector: u8,
    raw_q18_queries: Vec<u32>,
    sorted_layer0_fibres: Vec<u32>,
    sorted_later_fibres: Vec<Vec<u32>>,
    pivot_row: usize,
}

#[derive(Serialize)]
struct MatrixMetadata {
    field: &'static str,
    rows: usize,
    columns: usize,
    row_order: Vec<&'static str>,
    storage_order: &'static str,
    field_element_encoding: &'static str,
    matrix_bytes: usize,
    schedule_bytes: usize,
    schedule_sha256: String,
    matrix_sha256: String,
}

#[derive(Serialize)]
struct ArtifactMetadata {
    file: &'static str,
    header_bytes: usize,
    total_bytes: usize,
    sha256: String,
}

#[derive(Serialize)]
struct CorrespondenceKats {
    all_committed_c2_values_checked: usize,
    selected_component_c_q18_values_checked: usize,
    released_claims_checked: usize,
    reconstructed_free_coordinates: usize,
    basis_columns: Vec<usize>,
    basis_column_sha256: Vec<String>,
    dense_input_sha256: String,
    dense_output_sha256: String,
    full_encoder_reference_parity_cases: usize,
    linearity_checks: usize,
    byte_lane_order: &'static str,
}

struct CorrespondenceCounts {
    all_committed_c2_values: usize,
    selected_component_c_q18_values: usize,
    released_claims: usize,
}

fn elapsed_ms(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_millis()).unwrap_or(u64::MAX)
}

fn hex(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn decode_qm31(bytes: &[u8], context: &'static str) -> Result<QM31> {
    ensure!(
        bytes.len() == V5_C_EMAT_QM31_BYTES,
        "{context}: wrong QM31 width"
    );
    QM31::from_le_bytes(bytes).ok_or_else(|| anyhow!("{context}: non-canonical QM31"))
}

fn recover_real_free_coordinates(
    schedule: &V5ComponentCFrozenESchedule,
    values: &[QM31],
) -> Result<[QM31; V5_C_EMAT_COLUMNS]> {
    ensure!(
        values.len() == V5_C_EMAT_COLUMNS + 1,
        "real Component-C message has {} rows, expected {}",
        values.len(),
        V5_C_EMAT_COLUMNS + 1
    );
    let free = core::array::from_fn(|coordinate| {
        let row = if coordinate < schedule.pivot_row {
            coordinate
        } else {
            coordinate + 1
        };
        values[row]
    });
    let reconstructed = V5ComponentCLane::encode_free_coordinates(&free);
    ensure!(
        reconstructed.values().as_slice() == values,
        "real Component-C message is not the frozen free-coordinate encoding"
    );
    Ok(free)
}

fn check_real_artifact_correspondence(
    artifact: &aspis_prover::v5_mask::real_host_proof::V5RealHostArtifact,
    schedule: &V5ComponentCFrozenESchedule,
    matrix: &V5ComponentCEmat,
) -> Result<CorrespondenceCounts> {
    ensure!(
        artifact.layer_zero.c2.encoded.len() == V5_C2_LANES,
        "real C2 encoded-lane count drift"
    );
    ensure!(
        artifact.layer_zero.c2.packed_values.len() == V5_LAYER_ZERO_LEAVES * V5_C2_LEAF_BYTES,
        "real C2 packed byte length drift"
    );

    let mut packed_checks = 0usize;
    for fibre in 0..V5_LAYER_ZERO_LEAVES {
        let leaf_start = fibre * V5_C2_LEAF_BYTES;
        for helper in 0..V5_C2_LANES {
            for slot in 0..V5_FIBRE_SLOTS {
                let packed_start =
                    leaf_start + (helper * V5_FIBRE_SLOTS + slot) * V5_C_EMAT_QM31_BYTES;
                let packed = decode_qm31(
                    &artifact.layer_zero.c2.packed_values
                        [packed_start..packed_start + V5_C_EMAT_QM31_BYTES],
                    "real C2 packed leaf",
                )?;
                let codeword_index = V5_FIBRE_SLOTS * fibre + slot;
                ensure!(
                    packed == artifact.layer_zero.c2.encoded[helper][codeword_index],
                    "real C2 byte-lane order drift at fibre {fibre}, helper {helper}, slot {slot}"
                );
                packed_checks += 1;
            }
        }
    }

    let component_c_values = &artifact.layer_zero.c2.messages[COMPONENT_C_HELPER];
    let free = recover_real_free_coordinates(schedule, component_c_values)?;
    let emitted_view = matrix.mul_vec(&free);

    let mut q18_checks = 0usize;
    for (ordinal, fibre) in schedule.layer0_fibres.iter().copied().enumerate() {
        for slot in 0..V5_FIBRE_SLOTS {
            let codeword_index = V5_FIBRE_SLOTS * fibre as usize + slot;
            let expected = artifact.layer_zero.c2.encoded[COMPONENT_C_HELPER][codeword_index];
            let row = V5_FIBRE_SLOTS * ordinal + slot;
            ensure!(
                emitted_view[row] == expected,
                "Emat/real Component-C q18 mismatch at row {row}"
            );

            let packed_start = fibre as usize * V5_C2_LEAF_BYTES
                + (COMPONENT_C_HELPER * V5_FIBRE_SLOTS + slot) * V5_C_EMAT_QM31_BYTES;
            let packed = decode_qm31(
                &artifact.layer_zero.c2.packed_values
                    [packed_start..packed_start + V5_C_EMAT_QM31_BYTES],
                "real Component-C q18 leaf",
            )?;
            ensure!(packed == expected, "Emat q18 byte correspondence drift");
            q18_checks += 1;
        }
    }
    ensure!(
        q18_checks == V5_C_EMAT_LAYER_ZERO_ROWS,
        "q18 row count drift"
    );

    for claim in 0..4 {
        ensure!(
            emitted_view[V5_C_EMAT_LAYER_ZERO_ROWS + claim]
                == artifact.relation_claims.point_major[claim][COMPONENT_C_RELATION_LANE],
            "Emat/real Component-C released-claim mismatch at claim {claim}"
        );
    }

    Ok(CorrespondenceCounts {
        all_committed_c2_values: packed_checks,
        selected_component_c_q18_values: q18_checks,
        released_claims: 4,
    })
}

fn manifest(
    schedule: &V5ComponentCFrozenESchedule,
    kats: &V5ComponentCEmatKatMetadata,
    counts: CorrespondenceCounts,
    artifact_bytes: &[u8],
    schedule_bytes: usize,
    matrix_sha256: [u8; 32],
    schedule_sha256: [u8; 32],
) -> Manifest {
    Manifest {
        schema: "aspis-v5-component-c-emat-manifest",
        version: 1,
        status: "provisional maps-only audit artifact; not a deployed Component-C hiding claim",
        scope: Scope {
            emitted: "frozen-q18 conditioned-view E matrix only",
            f_matrix_emitted: false,
            legal_difference_space_defined: false,
            delta_defined: false,
            c_dec_claimed: false,
            verifier_wire_changed: false,
            production_or_sbf_inclusion: false,
        },
        reproducible_command:
            "NO_DNA=1 cargo run -p aspis-xtask --bin aspis-xtask --release -- v5-component-c-emat",
        frozen_input: FrozenInput {
            statement_digest: hex(&schedule.statement_digest),
            transcript_state_after_queries: hex(&schedule.transcript_state_after_queries),
            roots: schedule.roots.iter().map(|root| hex(root)).collect(),
            query_selector: schedule.query_selector,
            raw_q18_queries: schedule.queries.to_vec(),
            sorted_layer0_fibres: schedule.layer0_fibres.to_vec(),
            sorted_later_fibres: schedule
                .later_fibres
                .iter()
                .map(|indices| indices.to_vec())
                .collect(),
            pivot_row: schedule.pivot_row,
        },
        matrix: MatrixMetadata {
            field: "QM31 = degree-4 tower over M31 (p = 2^31 - 1)",
            rows: V5_C_EMAT_ROWS,
            columns: V5_C_EMAT_COLUMNS,
            row_order: vec![
                "rows 0..72: sorted layer-zero q18 fibres, four codeword slots per fibre",
                "rows 72, 73, 74: MLE(z), MLE(successor(z)), MLE(xor12(z))",
                "row 75: structured terminal functional",
            ],
            storage_order: "row-major",
            field_element_encoding: "16 canonical little-endian bytes: four M31 limbs",
            matrix_bytes: V5_C_EMAT_MATRIX_BYTES,
            schedule_bytes,
            schedule_sha256: hex(&schedule_sha256),
            matrix_sha256: hex(&matrix_sha256),
        },
        artifact: ArtifactMetadata {
            file: ARTIFACT_FILE,
            header_bytes: V5_C_EMAT_ARTIFACT_HEADER_BYTES,
            total_bytes: artifact_bytes.len(),
            sha256: hex(&sha256(artifact_bytes)),
        },
        correspondence_kats: CorrespondenceKats {
            all_committed_c2_values_checked: counts.all_committed_c2_values,
            selected_component_c_q18_values_checked: counts.selected_component_c_q18_values,
            released_claims_checked: counts.released_claims,
            reconstructed_free_coordinates: V5_C_EMAT_COLUMNS,
            basis_columns: kats.basis_columns.to_vec(),
            basis_column_sha256: kats
                .basis_column_sha256
                .iter()
                .map(|hash| hex(hash))
                .collect(),
            dense_input_sha256: hex(&kats.dense_input_sha256),
            dense_output_sha256: hex(&kats.dense_output_sha256),
            full_encoder_reference_parity_cases: kats.reference_parity_cases,
            linearity_checks: kats.linearity_checks,
            byte_lane_order:
                "fibre-major, helper-major (Hcopy, B, C), then four slot-major QM31 values",
        },
        benchmark_policy: "wall-clock timings are intentionally excluded from this deterministic manifest and printed by the generator",
        remaining_blockers: vec![
            "No deployed legal-difference space or Delta map is defined.",
            "No frozen F matrix for the 256 private-view rows is emitted.",
            "No C-DEC certificate exists; this artifact cannot establish Component-C hiding.",
            "The Rust-to-Lean Emat byte/hash correspondence remains an explicit review interface.",
            "No verifier, proof serialization, SBF binary, devnet, or mainnet path consumes this artifact.",
        ],
    }
}

pub fn run(results_dir: &Path) -> Result<V5ComponentCMapsOutcome> {
    let total_start = Instant::now();

    let (_statement, real_artifact) = crate::v5_cu_probe::build_real_v5_fixture()?;

    let schedule = V5ComponentCFrozenESchedule::from_real_host_artifact(&real_artifact)
        .context("derive frozen-q18 Component-C E schedule")?;

    let phase = Instant::now();
    let matrix = V5ComponentCEmat::generate(&schedule)
        .context("generate sparse frozen-q18 Component-C E matrix")?;
    let generation_ms = elapsed_ms(phase);

    let kats = build_component_c_emat_kats(&schedule, &matrix)
        .context("run Component-C E full-encoder and linearity KATs")?;

    let correspondence = check_real_artifact_correspondence(&real_artifact, &schedule, &matrix)
        .context("bind Emat to real committed bytes and released claims")?;

    let artifact_bytes = matrix.encode_artifact(&schedule);
    let view = validate_component_c_emat_artifact(&artifact_bytes)
        .context("self-validate Component-C E artifact")?;
    ensure!(
        view.matrix_sha256 == matrix.sha256(),
        "matrix hash API drift"
    );
    ensure!(
        view.schedule_sha256 == schedule.sha256(),
        "schedule hash API drift"
    );

    fs::create_dir_all(results_dir).context("create Component-C artifact directory")?;
    let artifact_path = results_dir.join(ARTIFACT_FILE);
    let manifest_path = results_dir.join(MANIFEST_FILE);
    fs::write(&artifact_path, &artifact_bytes)
        .with_context(|| format!("write {}", artifact_path.display()))?;

    let document = manifest(
        &schedule,
        &kats,
        correspondence,
        &artifact_bytes,
        view.schedule_bytes.len(),
        view.matrix_sha256,
        view.schedule_sha256,
    );
    let encoded_manifest = format!("{}\n", serde_json::to_string_pretty(&document)?);
    fs::write(&manifest_path, encoded_manifest)
        .with_context(|| format!("write {}", manifest_path.display()))?;
    let total_ms = elapsed_ms(total_start);

    Ok(V5ComponentCMapsOutcome {
        artifact_path,
        manifest_path,
        artifact_bytes: artifact_bytes.len(),
        artifact_sha256: hex(&sha256(&artifact_bytes)),
        matrix_sha256: hex(&view.matrix_sha256),
        generation_ms,
        total_ms,
    })
}
