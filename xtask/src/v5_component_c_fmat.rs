//! Offline generation and deployed-arithmetic audit of the frozen-q18
//! Component-C intrinsic `F_sigma` map.
//!
//! The command consumes (but never rewrites) the v1 Emat artifact. It emits a
//! separate Fmat artifact and manifest. It deliberately defines no legal
//! difference space, Delta map, C-DEC certificate, verifier wire, proof bytes,
//! or SBF inclusion.

use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::field::{qm31_power_table, QM31};
use aspis_prover::{
    v5_mask::{
        component_c::{V5ComponentCLane, V5_C_FREE_COORDINATES},
        component_c_emat::{
            validate_component_c_emat_artifact, V5ComponentCFrozenESchedule,
            V5_C_EMAT_ARTIFACT_VERSION, V5_C_EMAT_SCHEDULE_BYTES,
        },
        component_c_fmat::{
            build_component_c_fmat_kats, check_gamma18_correspondence,
            evaluate_frozen_private_view_reference, relation_rows,
            validate_component_c_fmat_artifact, V5ComponentCFmat, V5ComponentCFmatKatMetadata,
            V5ComponentCFrozenFSchedule, V5_C_FMAT_ARTIFACT_HEADER_BYTES,
            V5_C_FMAT_ARTIFACT_VERSION, V5_C_FMAT_COLUMNS, V5_C_FMAT_FINAL_ROWS,
            V5_C_FMAT_GAMMA18_INCLUDED, V5_C_FMAT_LATER_ROWS, V5_C_FMAT_MATRIX_BYTES,
            V5_C_FMAT_RELATION_ROWS, V5_C_FMAT_ROWS,
        },
        real_host_proof::V5RealHostArtifact,
        spend_messages::{
            gamma_combine_v5_messages, verify_v5_pcs_openings, V5_C1_LANES, V5_C2_LANES,
            V5_FIBRE_SLOTS, V5_TOTAL_LANES,
        },
        V5_CODEWORD_LEN,
    },
    HOST_HASH,
};
use serde::Serialize;
use sha2::{Digest as _, Sha256};

const COMPONENT_C_HELPER: usize = 2;
const EMAT_ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_emat.bin";
const FMAT_ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_fmat.bin";
const FMAT_MANIFEST_FILE: &str = "v5_component_c_frozen_q18_fmat.json";

const _: () = assert!(COMPONENT_C_HELPER < V5_C2_LANES);
const _: () = assert!(V5_C_FMAT_COLUMNS == V5_C_FREE_COORDINATES);
const _: () = assert!(V5_TOTAL_LANES == V5_C1_LANES + V5_C2_LANES);
const _: () = assert!(V5_C_FMAT_ROWS == 256);
const _: () = assert!(!V5_C_FMAT_GAMMA18_INCLUDED);

#[derive(Clone, Debug)]
pub struct V5ComponentCFmatOutcome {
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
    emat_v1_compatibility: EmatCompatibility,
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
    gamma18_included: bool,
    legal_difference_space_defined: bool,
    delta_defined: bool,
    c_dec_claimed: bool,
    verifier_wire_changed: bool,
    production_or_sbf_inclusion: bool,
}

#[derive(Serialize)]
struct EmatCompatibility {
    artifact_version: u16,
    file: &'static str,
    consumed_read_only: bool,
    bytes_unchanged: bool,
    artifact_sha256: String,
    schedule_sha256: String,
    matrix_sha256: String,
    f_schedule_prefix_is_exact_emat_schedule: bool,
}

#[derive(Serialize)]
struct FrozenInput {
    statement_digest: String,
    transcript_state_after_queries: String,
    roots: Vec<String>,
    query_selector: u8,
    raw_q18_queries: Vec<u32>,
    sorted_later_fibres: Vec<Vec<u32>>,
    gamma: String,
    kappa: String,
    gamma18: String,
}

#[derive(Serialize)]
struct MatrixMetadata {
    field: &'static str,
    rows: usize,
    columns: usize,
    row_order: Vec<&'static str>,
    storage_order: &'static str,
    field_element_encoding: &'static str,
    scaling_convention: &'static str,
    gamma18_included: bool,
    matrix_bytes: usize,
    schedule_bytes: usize,
    schedule_sha256: String,
    matrix_sha256: String,
}

#[derive(Serialize)]
struct ArtifactMetadata {
    file: &'static str,
    artifact_version: u16,
    header_bytes: usize,
    total_bytes: usize,
    sha256: String,
}

#[derive(Serialize)]
struct CorrespondenceKats {
    relation_rows_checked_against_real_trace: usize,
    authenticated_later_values_checked: usize,
    final_coefficients_checked_against_real_trace: usize,
    gamma18_differential_rows_checked: usize,
    reconstructed_component_c_free_coordinates: usize,
    basis_columns: Vec<usize>,
    basis_column_sha256: Vec<String>,
    dense_input_sha256: String,
    dense_output_sha256: String,
    full_reference_parity_cases: usize,
    linearity_checks: usize,
}

struct CorrespondenceCounts {
    relation_rows: usize,
    later_values: usize,
    final_coefficients: usize,
    gamma18_rows: usize,
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

fn encode_qm31(value: QM31) -> [u8; 16] {
    let mut bytes = [0u8; 16];
    value.write_le_bytes(&mut bytes);
    bytes
}

fn decode_qm31(bytes: &[u8], context: &'static str) -> Result<QM31> {
    QM31::from_le_bytes(bytes).ok_or_else(|| anyhow!("{context}: non-canonical QM31"))
}

fn recover_real_free_coordinates(
    schedule: &V5ComponentCFrozenESchedule,
    values: &[QM31],
) -> Result<[QM31; V5_C_FMAT_COLUMNS]> {
    ensure!(
        values.len() == V5_C_FMAT_COLUMNS + 1,
        "real Component-C message length drift"
    );
    let free = core::array::from_fn(|coordinate| {
        values[if coordinate < schedule.pivot_row {
            coordinate
        } else {
            coordinate + 1
        }]
    });
    let reconstructed = V5ComponentCLane::encode_free_coordinates(&free);
    ensure!(
        reconstructed.values() == values,
        "real Component-C message is not the frozen kernel encoding"
    );
    Ok(free)
}

fn real_combined_codeword(artifact: &V5RealHostArtifact) -> Result<Vec<QM31>> {
    ensure!(
        artifact.layer_zero.c1.encoded.len() == V5_C1_LANES
            && artifact.layer_zero.c2.encoded.len() == V5_C2_LANES,
        "real encoded lane count drift"
    );
    let powers = qm31_power_table::<V5_TOTAL_LANES>(artifact.challenges.gamma);
    let mut combined = vec![QM31::ZERO; V5_CODEWORD_LEN];
    for (lane, power) in artifact
        .layer_zero
        .c1
        .encoded
        .iter()
        .zip(powers[..V5_C1_LANES].iter().copied())
    {
        ensure!(
            lane.len() == V5_CODEWORD_LEN,
            "real C1 codeword length drift"
        );
        for (output, value) in combined.iter_mut().zip(lane.iter().copied()) {
            *output = output.add(power.mul_m31(value));
        }
    }
    for (lane, power) in artifact
        .layer_zero
        .c2
        .encoded
        .iter()
        .zip(powers[V5_C1_LANES..].iter().copied())
    {
        ensure!(
            lane.len() == V5_CODEWORD_LEN,
            "real C2 codeword length drift"
        );
        for (output, value) in combined.iter_mut().zip(lane.iter().copied()) {
            *output = output.add(power.mul(value));
        }
    }
    Ok(combined)
}

fn check_real_artifact_correspondence(
    artifact: &V5RealHostArtifact,
    schedule: &V5ComponentCFrozenFSchedule,
    matrix: &V5ComponentCFmat,
) -> Result<CorrespondenceCounts> {
    let messages = artifact.layer_zero.messages();
    let combined_message = gamma_combine_v5_messages(&messages, artifact.challenges.gamma)
        .context("gamma-combine real messages")?;
    let combined_codeword = real_combined_codeword(artifact)?;
    let real_view = evaluate_frozen_private_view_reference(
        schedule,
        &combined_message,
        &combined_codeword,
        artifact.inactive_claim,
    )
    .context("evaluate full real private view")?;

    let expected_relation = relation_rows(&artifact.relation);
    ensure!(
        real_view[..V5_C_FMAT_RELATION_ROWS] == expected_relation,
        "Fmat relation rows drift from the real V5IncrementalRelation trace"
    );
    let final_start = V5_C_FMAT_RELATION_ROWS + V5_C_FMAT_LATER_ROWS;
    ensure!(
        real_view[final_start..] == artifact.relation.final_coefficients,
        "Fmat final coefficients drift from the real relation trace"
    );

    let verified = verify_v5_pcs_openings(
        HOST_HASH,
        &artifact.roots,
        &artifact.queries,
        &artifact.openings.bytes,
    )
    .context("authenticate frozen q18 private openings")?;
    ensure!(
        verified.indices == artifact.opening_indices,
        "authenticated opening schedule drift"
    );
    ensure!(
        verified.indices.later == schedule.base.later_fibres,
        "Fmat sorted later-layer schedule drift"
    );
    let mut cursor = V5_C_FMAT_RELATION_ROWS;
    let mut later_checks = 0usize;
    for layer in 0..verified.later.len() {
        ensure!(
            verified.later[layer].count == schedule.base.later_fibres[layer].len(),
            "authenticated later-layer count drift"
        );
        for ordinal in 0..verified.later[layer].count {
            let leaf = verified.later[layer]
                .value(ordinal)
                .ok_or_else(|| anyhow!("missing authenticated later-layer leaf"))?;
            ensure!(leaf.len() == V5_FIBRE_SLOTS * 16, "later leaf width drift");
            for slot in 0..V5_FIBRE_SLOTS {
                let actual = decode_qm31(
                    &leaf[slot * 16..(slot + 1) * 16],
                    "authenticated later-layer slot",
                )?;
                ensure!(
                    real_view[cursor] == actual,
                    "Fmat/real authenticated later-layer mismatch at row {cursor}"
                );
                cursor += 1;
                later_checks += 1;
            }
        }
    }
    ensure!(
        later_checks == V5_C_FMAT_LATER_ROWS && cursor == final_start,
        "later-layer row count drift"
    );

    let free = recover_real_free_coordinates(
        &schedule.base,
        &artifact.layer_zero.c2.messages[COMPONENT_C_HELPER],
    )?;
    check_gamma18_correspondence(
        schedule,
        matrix,
        &combined_message,
        &combined_codeword,
        &free,
    )
    .context("check all-row intrinsic Fmat gamma^18 differential")?;

    Ok(CorrespondenceCounts {
        relation_rows: V5_C_FMAT_RELATION_ROWS,
        later_values: later_checks,
        final_coefficients: V5_C_FMAT_FINAL_ROWS,
        gamma18_rows: V5_C_FMAT_ROWS,
    })
}

#[allow(clippy::too_many_arguments)]
fn manifest(
    schedule: &V5ComponentCFrozenFSchedule,
    kats: &V5ComponentCFmatKatMetadata,
    counts: CorrespondenceCounts,
    artifact_bytes: &[u8],
    schedule_sha256: [u8; 32],
    matrix_sha256: [u8; 32],
    emat_bytes: &[u8],
    emat_schedule_sha256: [u8; 32],
    emat_matrix_sha256: [u8; 32],
) -> Manifest {
    Manifest {
        schema: "aspis-v5-component-c-fmat-manifest",
        version: 1,
        status: "provisional maps-only audit artifact; not a deployed Component-C hiding claim",
        scope: Scope {
            emitted: "frozen-q18 intrinsic unscaled private-view F_sigma matrix only",
            gamma18_included: V5_C_FMAT_GAMMA18_INCLUDED,
            legal_difference_space_defined: false,
            delta_defined: false,
            c_dec_claimed: false,
            verifier_wire_changed: false,
            production_or_sbf_inclusion: false,
        },
        reproducible_command:
            "NO_DNA=1 cargo run -p aspis-xtask --bin aspis-xtask --release -- v5-component-c-fmat",
        emat_v1_compatibility: EmatCompatibility {
            artifact_version: V5_C_EMAT_ARTIFACT_VERSION,
            file: EMAT_ARTIFACT_FILE,
            consumed_read_only: true,
            bytes_unchanged: true,
            artifact_sha256: hex(&sha256(emat_bytes)),
            schedule_sha256: hex(&emat_schedule_sha256),
            matrix_sha256: hex(&emat_matrix_sha256),
            f_schedule_prefix_is_exact_emat_schedule: true,
        },
        frozen_input: FrozenInput {
            statement_digest: hex(&schedule.base.statement_digest),
            transcript_state_after_queries: hex(&schedule.base.transcript_state_after_queries),
            roots: schedule.base.roots.iter().map(|root| hex(root)).collect(),
            query_selector: schedule.base.query_selector,
            raw_q18_queries: schedule.base.queries.to_vec(),
            sorted_later_fibres: schedule
                .base
                .later_fibres
                .iter()
                .map(|indices| indices.to_vec())
                .collect(),
            gamma: hex(&encode_qm31(schedule.gamma)),
            kappa: hex(&encode_qm31(schedule.kappa)),
            gamma18: hex(&encode_qm31(schedule.gamma18())),
        },
        matrix: MatrixMetadata {
            field: "QM31 = degree-4 tower over M31 (p = 2^31 - 1)",
            rows: V5_C_FMAT_ROWS,
            columns: V5_C_FMAT_COLUMNS,
            row_order: vec![
                "rows 0..36: four rounds, each two OOD values then seven sumcheck coefficients",
                "rows 36..252: layers 1, 2, 3; sorted q18 fibre ordinal then slots 0,1,2,3",
                "rows 252..256: four final coefficients in natural order",
            ],
            storage_order: "row-major",
            field_element_encoding: "16 canonical little-endian bytes: four M31 limbs",
            scaling_convention:
                "intrinsic unscaled F_sigma; deployed Component-C contribution is gamma^18 * F_sigma * c",
            gamma18_included: V5_C_FMAT_GAMMA18_INCLUDED,
            matrix_bytes: V5_C_FMAT_MATRIX_BYTES,
            schedule_bytes: schedule.canonical_bytes().len(),
            schedule_sha256: hex(&schedule_sha256),
            matrix_sha256: hex(&matrix_sha256),
        },
        artifact: ArtifactMetadata {
            file: FMAT_ARTIFACT_FILE,
            artifact_version: V5_C_FMAT_ARTIFACT_VERSION,
            header_bytes: V5_C_FMAT_ARTIFACT_HEADER_BYTES,
            total_bytes: artifact_bytes.len(),
            sha256: hex(&sha256(artifact_bytes)),
        },
        correspondence_kats: CorrespondenceKats {
            relation_rows_checked_against_real_trace: counts.relation_rows,
            authenticated_later_values_checked: counts.later_values,
            final_coefficients_checked_against_real_trace: counts.final_coefficients,
            gamma18_differential_rows_checked: counts.gamma18_rows,
            reconstructed_component_c_free_coordinates: V5_C_FMAT_COLUMNS,
            basis_columns: kats.basis_columns.to_vec(),
            basis_column_sha256: kats
                .basis_column_sha256
                .iter()
                .map(|hash| hex(hash))
                .collect(),
            dense_input_sha256: hex(&kats.dense_input_sha256),
            dense_output_sha256: hex(&kats.dense_output_sha256),
            full_reference_parity_cases: kats.reference_parity_cases,
            linearity_checks: kats.linearity_checks,
        },
        benchmark_policy: "wall-clock timings are excluded from this deterministic manifest and printed by the generator",
        remaining_blockers: vec![
            "No deployed legal-difference space, Delta map, or legal-difference generator exists.",
            "No frozen C-DEC certificate exists; Emat and Fmat alone cannot establish Component-C hiding.",
            "Rust-to-Lean EMatrixFaithful and FMatrixFaithful byte/hash correspondences remain explicit review interfaces.",
            "EncoderIntertwines and DeltaImageCovered cannot be instantiated until a deployed Delta exists.",
            "No verifier, proof serialization, SBF binary, devnet, or mainnet path consumes either map artifact.",
        ],
    }
}

pub fn run(results_dir: &Path) -> Result<V5ComponentCFmatOutcome> {
    let total_start = Instant::now();

    // Emat v1 is an input compatibility anchor. This command never writes it.
    let emat_path = results_dir.join(EMAT_ARTIFACT_FILE);
    let emat_bytes = fs::read(&emat_path)
        .with_context(|| format!("read required v1 Emat artifact {}", emat_path.display()))?;
    let emat_before = sha256(&emat_bytes);
    let emat_view = validate_component_c_emat_artifact(&emat_bytes)
        .context("validate required v1 Emat artifact")?;

    let (_statement, real_artifact) = crate::v5_cu_probe::build_real_v5_fixture()?;
    let schedule = V5ComponentCFrozenFSchedule::from_real_host_artifact(&real_artifact)
        .context("derive frozen-q18 Component-C F schedule")?;
    let schedule_bytes = schedule.canonical_bytes();
    ensure!(
        &schedule_bytes[..V5_C_EMAT_SCHEDULE_BYTES] == emat_view.schedule_bytes,
        "F schedule does not extend the exact frozen Emat v1 schedule"
    );

    let phase = Instant::now();
    let matrix = V5ComponentCFmat::generate(&schedule)
        .context("generate sparse exact frozen-q18 Component-C F matrix")?;
    let generation_ms = elapsed_ms(phase);
    let kats = build_component_c_fmat_kats(&schedule, &matrix)
        .context("run Component-C F sparse/full-reference and linearity KATs")?;
    ensure!(!kats.gamma18_included, "Fmat scaling convention drift");
    let correspondence = check_real_artifact_correspondence(&real_artifact, &schedule, &matrix)
        .context("bind Fmat to real relation and authenticated openings")?;

    let artifact_bytes = matrix.encode_artifact(&schedule);
    let view = validate_component_c_fmat_artifact(&artifact_bytes)
        .context("self-validate Component-C F artifact")?;
    ensure!(
        view.matrix_sha256 == matrix.sha256(),
        "matrix hash API drift"
    );
    ensure!(
        view.schedule_sha256 == schedule.sha256(),
        "schedule hash API drift"
    );

    fs::create_dir_all(results_dir).context("create Component-C artifact directory")?;
    let artifact_path = results_dir.join(FMAT_ARTIFACT_FILE);
    let manifest_path = results_dir.join(FMAT_MANIFEST_FILE);
    fs::write(&artifact_path, &artifact_bytes)
        .with_context(|| format!("write {}", artifact_path.display()))?;
    let document = manifest(
        &schedule,
        &kats,
        correspondence,
        &artifact_bytes,
        view.schedule_sha256,
        view.matrix_sha256,
        &emat_bytes,
        emat_view.schedule_sha256,
        emat_view.matrix_sha256,
    );
    fs::write(
        &manifest_path,
        format!("{}\n", serde_json::to_string_pretty(&document)?),
    )
    .with_context(|| format!("write {}", manifest_path.display()))?;

    // Refuse accidental compatibility-artifact rewrites, including concurrent
    // ones during this command.
    let emat_after = sha256(
        &fs::read(&emat_path)
            .with_context(|| format!("re-read v1 Emat artifact {}", emat_path.display()))?,
    );
    ensure!(
        emat_before == emat_after,
        "v1 Emat artifact changed during Fmat generation"
    );

    Ok(V5ComponentCFmatOutcome {
        artifact_path,
        manifest_path,
        artifact_bytes: artifact_bytes.len(),
        artifact_sha256: hex(&sha256(&artifact_bytes)),
        matrix_sha256: hex(&view.matrix_sha256),
        generation_ms,
        total_ms: elapsed_ms(total_start),
    })
}
