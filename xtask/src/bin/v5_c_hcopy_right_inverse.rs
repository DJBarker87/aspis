//! Exact frozen-q18 diagnostic for the atomic-v3 Hcopy-padding -> Component-C
//! conditioned-view map.
//!
//! This binary is deliberately isolated from the v5 prover and verifier.  It
//! consumes the canonical **pre-public-FS-salt, pre-fresh-B-pivot** frozen-q18
//! `E` artifact, constructs the actual
//! atomic-v3 Hcopy zero-active/zero-inactive padding basis, and emits a sparse
//! exact right inverse for the 76 released `E` coordinates.  The result is
//! computational audit evidence only: it is not a Lean theorem, a sampler
//! proof, a same-statement coupling, or a deployed Component-C claim.

use std::{fs, path::Path};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::field::{P, QM31};
use aspis_prover::v5_mask::{
    component_c::{
        v5_c_inactive_functional, v5_c_pivot_row, V5ComponentCLane, V5_C_FREE_COORDINATES,
        V5_C_ROWS,
    },
    component_c_emat::{
        validate_component_c_emat_artifact, V5ComponentCEmat, V5_C_EMAT_COLUMNS,
        V5_C_EMAT_QM31_BYTES, V5_C_EMAT_ROWS,
    },
    V5_TRACE_ROWS,
};
use aspis_statement::atomic_state_only_terminal::{
    atomic_state_only_copy_active_rows_v3, atomic_state_only_copy_inactive_row_masks_v3,
    PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3,
};
use serde::Serialize;
use sha2::{Digest as _, Sha256};

const EMAT_FILE: &str = "v5_component_c_frozen_q18_emat.bin";
const FMAT_MANIFEST_FILE: &str = "v5_component_c_frozen_q18_fmat.json";
const CURRENT_CU_MANIFEST_FILE: &str = "v5_full_transaction_cu_probe.json";
const CERTIFICATE_FILE: &str =
    "v5_component_c_pre_salt_frozen_q18_hcopy_e_right_inverse_diagnostic.bin";
const MANIFEST_FILE: &str =
    "v5_component_c_pre_salt_frozen_q18_hcopy_e_right_inverse_diagnostic.json";

const PRE_SALT_EMAT_SCHEDULE_SHA256: &str =
    "aa48d48cc6767205c1209683da13ac262670c3517b8b1bd68e770c7c0d806931";

const B_PIVOT_ROW: usize = 993;
const CERTIFICATE_MAGIC: [u8; 8] = *b"AV5HRI01";
const CERTIFICATE_VERSION: u16 = 1;
const CERTIFICATE_FLAGS: u16 = 0;
const CERTIFICATE_HEADER_BYTES: usize = 320;
const PIVOT_COUNT: usize = V5_C_EMAT_ROWS;
const PIVOT_BYTES: usize = PIVOT_COUNT * 4;
const INVERSE_ENTRIES: usize = PIVOT_COUNT * PIVOT_COUNT;
const INVERSE_BYTES: usize = INVERSE_ENTRIES * V5_C_EMAT_QM31_BYTES;
const CERTIFICATE_BYTES: usize = CERTIFICATE_HEADER_BYTES + PIVOT_BYTES + INVERSE_BYTES;

const MAP_HASH_DOMAIN: &[u8] = b"aspis-v5-hcopy-scaled-e-map-v1";
const PIVOT_HASH_DOMAIN: &[u8] = b"aspis-v5-hcopy-e-right-inverse-pivots-v1";
const INVERSE_HASH_DOMAIN: &[u8] = b"aspis-v5-hcopy-e-right-inverse-values-v1";

const _: () = assert!(V5_TRACE_ROWS == V5_C_ROWS);
const _: () = assert!(V5_C_EMAT_COLUMNS == V5_C_FREE_COORDINATES);
const _: () = assert!(V5_C_EMAT_ROWS == 76);
const _: () = assert!(PIVOT_BYTES == 304);
const _: () = assert!(INVERSE_BYTES == 92_416);
const _: () = assert!(CERTIFICATE_BYTES == 93_040);

#[derive(Clone)]
struct Inputs {
    emat_raw_sha256: [u8; 32],
    emat_schedule_sha256: [u8; 32],
    emat_matrix_sha256: [u8; 32],
    fmat_manifest_sha256: [u8; 32],
    current_cu_manifest_sha256: [u8; 32],
    gamma: QM31,
    gamma16: QM31,
    gamma17: QM31,
    dependent_pivot: usize,
    direction_rows: Vec<usize>,
    scaled_map: Vec<QM31>,
    scaled_map_sha256: [u8; 32],
    emat: V5ComponentCEmat,
}

struct CertificateView {
    pivots: Vec<usize>,
    inverse: Vec<QM31>,
}

#[derive(Serialize)]
struct Manifest {
    schema: &'static str,
    version: u32,
    status: &'static str,
    scope: Scope,
    reproducible_commands: Commands,
    inputs: ManifestInputs,
    exact_result: ExactResult,
    normalization_diagnostic: NormalizationDiagnostic,
    composition_rule: CompositionRule,
    certificate: CertificateMetadata,
    remaining_obligations: Vec<&'static str>,
}

#[derive(Serialize)]
struct Scope {
    diagnostic_only: bool,
    lean_theorem_claimed: bool,
    sampler_uniformity_claimed: bool,
    same_statement_zk_claimed: bool,
    deployed_component_c_claimed: bool,
    verifier_or_wire_changed: bool,
}

#[derive(Serialize)]
struct Commands {
    generate: &'static str,
    test: &'static str,
}

#[derive(Serialize)]
struct ManifestInputs {
    field: &'static str,
    emat_file: &'static str,
    emat_artifact_sha256: String,
    emat_schedule_sha256: String,
    emat_matrix_sha256: String,
    fmat_manifest_file: &'static str,
    fmat_manifest_sha256: String,
    current_cu_manifest_file: &'static str,
    current_cu_manifest_sha256: String,
    pre_salt_schedule_differs_from_salted_cu_fixture: bool,
    gamma_le_hex: String,
    gamma16_le_hex: String,
    gamma17_le_hex: String,
    atomic_v3_active_rows_fingerprint: String,
    dependent_inactive_pivot_row: usize,
    component_b_pivot_row: usize,
}

#[derive(Serialize)]
struct ExactResult {
    map_shape: [usize; 2],
    map_rank: usize,
    inactive_rows: usize,
    hcopy_padding_directions: usize,
    canonical_pivot_columns: Vec<usize>,
    canonical_pivot_trace_rows: Vec<usize>,
    scaled_map_sha256: String,
    independent_pivot_algorithms_agree: bool,
    independent_inverse_algorithms_agree: bool,
    decoded_sparse_right_inverse_identity: &'static str,
    exact_surjectivity_statement: &'static str,
}

#[derive(Serialize)]
struct NormalizationDiagnostic {
    deterministic_cases_checked: usize,
    statement: &'static str,
    b_pivot_normalization: &'static str,
    hcopy_relations_preserved: &'static str,
    double_counting_guard: &'static str,
}

#[derive(Serialize)]
struct CompositionRule {
    statement: &'static str,
    current_matrix_provenance: &'static str,
    implication: &'static str,
}

#[derive(Serialize)]
struct CertificateMetadata {
    file: &'static str,
    format_version: u16,
    bytes: usize,
    sha256: String,
    pivot_section_sha256: String,
    inverse_section_sha256: String,
    sparse_storage: &'static str,
    mutation_tests: &'static str,
}

fn hex(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(2 * bytes.len());
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}

fn decode_hex(input: &str) -> Result<Vec<u8>> {
    ensure!(input.len().is_multiple_of(2), "odd hex length");
    input
        .as_bytes()
        .chunks_exact(2)
        .enumerate()
        .map(|(index, pair)| {
            let text = std::str::from_utf8(pair).context("non-UTF8 hex")?;
            u8::from_str_radix(text, 16)
                .with_context(|| format!("invalid hex byte at index {index}"))
        })
        .collect()
}

fn encode_qm31(value: QM31) -> [u8; V5_C_EMAT_QM31_BYTES] {
    let mut bytes = [0u8; V5_C_EMAT_QM31_BYTES];
    value.write_le_bytes(&mut bytes);
    bytes
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn domain_hash(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    hasher.finalize().into()
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16> {
    Ok(u16::from_le_bytes(
        bytes
            .get(offset..offset + 2)
            .ok_or_else(|| anyhow!("certificate truncated"))?
            .try_into()?,
    ))
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32> {
    Ok(u32::from_le_bytes(
        bytes
            .get(offset..offset + 4)
            .ok_or_else(|| anyhow!("certificate truncated"))?
            .try_into()?,
    ))
}

fn read_u64(bytes: &[u8], offset: usize) -> Result<u64> {
    Ok(u64::from_le_bytes(
        bytes
            .get(offset..offset + 8)
            .ok_or_else(|| anyhow!("certificate truncated"))?
            .try_into()?,
    ))
}

fn atomic_inactive(row: usize) -> bool {
    let masks = atomic_state_only_copy_inactive_row_masks_v3();
    masks[row >> 4] & (1 << (row & 15)) != 0
}

fn inactive_sum(values: &[QM31; V5_TRACE_ROWS]) -> QM31 {
    values
        .iter()
        .copied()
        .enumerate()
        .filter(|(row, _)| atomic_inactive(*row))
        .fold(QM31::ZERO, |sum, (_, value)| sum.add(value))
}

fn free_coordinate_for_row(row: usize, pivot: usize) -> Result<usize> {
    ensure!(
        row != pivot && row < V5_TRACE_ROWS,
        "invalid free-coordinate row"
    );
    Ok(if row < pivot { row } else { row - 1 })
}

fn decode_matrix(bytes: &[u8]) -> Result<Vec<QM31>> {
    ensure!(
        bytes.len() == V5_C_EMAT_ROWS * V5_C_EMAT_COLUMNS * V5_C_EMAT_QM31_BYTES,
        "E matrix byte length drift"
    );
    bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .enumerate()
        .map(|(index, encoded)| {
            QM31::from_le_bytes(encoded)
                .ok_or_else(|| anyhow!("non-canonical E matrix entry {index}"))
        })
        .collect()
}

fn map_entry(matrix: &[QM31], row: usize, column: usize, columns: usize) -> QM31 {
    matrix[row * columns + column]
}

fn encode_scaled_map(direction_rows: &[usize], scaled_map: &[QM31]) -> Result<Vec<u8>> {
    ensure!(
        scaled_map.len() == V5_C_EMAT_ROWS * direction_rows.len(),
        "scaled-map shape drift"
    );
    let mut bytes =
        Vec::with_capacity(4 * direction_rows.len() + V5_C_EMAT_QM31_BYTES * scaled_map.len());
    for &row in direction_rows {
        bytes.extend_from_slice(&u32::try_from(row)?.to_le_bytes());
    }
    for value in scaled_map.iter().copied() {
        bytes.extend_from_slice(&encode_qm31(value));
    }
    Ok(bytes)
}

fn load_inputs(results_dir: &Path) -> Result<Inputs> {
    let emat_path = results_dir.join(EMAT_FILE);
    let emat_bytes =
        fs::read(&emat_path).with_context(|| format!("read {}", emat_path.display()))?;
    let emat_raw_sha256 = sha256(&emat_bytes);
    let emat_view = validate_component_c_emat_artifact(&emat_bytes)
        .context("validate canonical frozen-q18 E artifact")?;
    ensure!(
        hex(&emat_view.schedule_sha256) == PRE_SALT_EMAT_SCHEDULE_SHA256,
        "E artifact is not the explicitly fenced pre-salt schedule"
    );
    let entries = decode_matrix(emat_view.matrix_bytes)?;
    let emat = V5ComponentCEmat::from_entries(entries.clone())?;

    let fmat_manifest_path = results_dir.join(FMAT_MANIFEST_FILE);
    let fmat_manifest_bytes = fs::read(&fmat_manifest_path)
        .with_context(|| format!("read {}", fmat_manifest_path.display()))?;
    let fmat_manifest_sha256 = sha256(&fmat_manifest_bytes);
    let fmat_json: serde_json::Value =
        serde_json::from_slice(&fmat_manifest_bytes).context("parse frozen-q18 F manifest")?;

    // The public FS salts changed the committed transcript and therefore the
    // q18 schedule.  Refuse to present this old E artifact as current: its
    // query vector must be observably different from the salted CU fixture.
    let current_cu_path = results_dir.join(CURRENT_CU_MANIFEST_FILE);
    let current_cu_bytes = fs::read(&current_cu_path)
        .with_context(|| format!("read {}", current_cu_path.display()))?;
    let current_cu_manifest_sha256 = sha256(&current_cu_bytes);
    let current_cu_json: serde_json::Value =
        serde_json::from_slice(&current_cu_bytes).context("parse salted CU manifest")?;
    let old_queries = fmat_json
        .pointer("/frozen_input/raw_q18_queries")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| anyhow!("pre-salt frozen queries missing from F manifest"))?;
    let current_queries = current_cu_json
        .pointer("/query_indices")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| anyhow!("salted CU queries missing from current manifest"))?;
    ensure!(
        old_queries != current_queries,
        "pre-salt and salted CU queries unexpectedly agree; regenerate and re-audit the schedule fence"
    );
    let gamma_hex = fmat_json
        .pointer("/frozen_input/gamma")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| anyhow!("frozen-q18 gamma missing from F manifest"))?;
    let gamma_bytes = decode_hex(gamma_hex)?;
    ensure!(
        gamma_bytes.len() == V5_C_EMAT_QM31_BYTES,
        "gamma byte length drift"
    );
    let gamma = QM31::from_le_bytes(&gamma_bytes).ok_or_else(|| anyhow!("non-canonical gamma"))?;
    ensure!(!gamma.is_zero(), "frozen gamma is zero");
    let gamma16 = gamma.pow(16);
    let gamma17 = gamma16.mul(gamma);
    ensure!(
        !gamma16.is_zero() && !gamma17.is_zero(),
        "gamma power is zero"
    );
    let recorded_gamma18 = fmat_json
        .pointer("/frozen_input/gamma18")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| anyhow!("frozen-q18 gamma18 missing from F manifest"))?;
    ensure!(
        decode_hex(recorded_gamma18)? == encode_qm31(gamma17.mul(gamma)),
        "gamma power chain disagrees with F manifest"
    );
    let recorded_emat_sha = fmat_json
        .pointer("/emat_v1_compatibility/artifact_sha256")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| anyhow!("E artifact binding missing from F manifest"))?;
    ensure!(
        recorded_emat_sha == hex(&emat_raw_sha256),
        "F manifest binds another E artifact"
    );

    let dependent_pivot = v5_c_pivot_row();
    let active_rows = atomic_state_only_copy_active_rows_v3();
    let mut active = [false; V5_TRACE_ROWS];
    for &row in active_rows {
        active[usize::from(row)] = true;
    }
    for row in 0..V5_TRACE_ROWS {
        ensure!(
            active[row] != atomic_inactive(row),
            "atomic-v3 active/inactive partition drift at row {row}"
        );
    }
    ensure!(
        atomic_inactive(dependent_pivot),
        "Component-C pivot is not inactive"
    );
    ensure!(
        atomic_inactive(B_PIVOT_ROW),
        "Component-B pivot is not inactive"
    );
    ensure!(
        dependent_pivot != B_PIVOT_ROW,
        "B pivot unexpectedly equals C normalization pivot"
    );

    let direction_rows = (0..V5_TRACE_ROWS)
        .filter(|&row| atomic_inactive(row) && row != dependent_pivot)
        .collect::<Vec<_>>();
    ensure!(!direction_rows.is_empty(), "empty Hcopy padding basis");

    // Construct each actual Hcopy padding direction e_row - e_pivot through
    // the deployed Component-C free-coordinate encoder.  Its E image must be
    // exactly the corresponding canonical artifact column.
    let mut scaled_map = vec![QM31::ZERO; V5_C_EMAT_ROWS * direction_rows.len()];
    for (direction, &row) in direction_rows.iter().enumerate() {
        let coordinate = free_coordinate_for_row(row, dependent_pivot)?;
        let mut free = [QM31::ZERO; V5_C_FREE_COORDINATES];
        free[coordinate] = QM31::ONE;
        let lane = V5ComponentCLane::encode_free_coordinates(&free);
        ensure!(
            lane.free_coordinates() == free,
            "Hcopy basis round trip failed"
        );
        ensure!(
            v5_c_inactive_functional(lane.values()).is_zero(),
            "Hcopy basis left ker ell"
        );
        ensure!(
            lane.values()[row] == QM31::ONE,
            "Hcopy basis row coefficient drift"
        );
        ensure!(
            lane.values()[dependent_pivot] == QM31::ONE.neg(),
            "Hcopy dependent coefficient drift"
        );
        ensure!(
            lane.values()
                .iter()
                .copied()
                .enumerate()
                .all(|(candidate, value)| {
                    candidate == row || candidate == dependent_pivot || value == QM31::ZERO
                }),
            "Hcopy basis has unexpected support"
        );
        let encoded = emat.mul_vec(&free);
        for released_row in 0..V5_C_EMAT_ROWS {
            ensure!(
                encoded[released_row] == entries[released_row * V5_C_EMAT_COLUMNS + coordinate],
                "actual Hcopy basis and E artifact column disagree"
            );
            scaled_map[released_row * direction_rows.len() + direction] =
                gamma16.mul(encoded[released_row]);
        }
    }
    let scaled_map_sha256 = domain_hash(
        MAP_HASH_DOMAIN,
        &encode_scaled_map(&direction_rows, &scaled_map)?,
    );

    Ok(Inputs {
        emat_raw_sha256,
        emat_schedule_sha256: emat_view.schedule_sha256,
        emat_matrix_sha256: emat_view.matrix_sha256,
        fmat_manifest_sha256,
        current_cu_manifest_sha256,
        gamma,
        gamma16,
        gamma17,
        dependent_pivot,
        direction_rows,
        scaled_map,
        scaled_map_sha256,
        emat,
    })
}

/// Canonical left-to-right Gaussian elimination.  The returned indices are
/// the lexicographically first independent columns.
fn exact_rank_and_pivots(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
) -> Result<(usize, Vec<usize>)> {
    ensure!(matrix.len() == rows * columns, "rank matrix shape drift");
    let mut work = matrix.to_vec();
    let mut rank = 0usize;
    let mut pivots = Vec::with_capacity(rows);
    for column in 0..columns {
        let Some(pivot_row) =
            (rank..rows).find(|&row| !map_entry(&work, row, column, columns).is_zero())
        else {
            continue;
        };
        if pivot_row != rank {
            for index in 0..columns {
                work.swap(rank * columns + index, pivot_row * columns + index);
            }
        }
        let inverse = map_entry(&work, rank, column, columns).inv();
        for row in rank + 1..rows {
            let scale = map_entry(&work, row, column, columns).mul(inverse);
            if scale.is_zero() {
                continue;
            }
            work[row * columns + column] = QM31::ZERO;
            for index in column + 1..columns {
                let position = row * columns + index;
                work[position] = work[position].sub(scale.mul(work[rank * columns + index]));
            }
        }
        pivots.push(column);
        rank += 1;
        if rank == rows {
            break;
        }
    }
    Ok((rank, pivots))
}

/// Independent column-streaming basis algorithm.  It selects a column only
/// when the exact vector is outside the span maintained so far.
fn independent_column_pivots(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
) -> Result<(usize, Vec<usize>)> {
    ensure!(matrix.len() == rows * columns, "basis matrix shape drift");
    let mut basis: Vec<(usize, Vec<QM31>)> = Vec::with_capacity(rows);
    let mut selected = Vec::with_capacity(rows);
    for column in 0..columns {
        let mut candidate = (0..rows)
            .map(|row| map_entry(matrix, row, column, columns))
            .collect::<Vec<_>>();
        for (pivot, vector) in &basis {
            let scale = candidate[*pivot];
            if scale.is_zero() {
                continue;
            }
            for row in *pivot..rows {
                candidate[row] = candidate[row].sub(scale.mul(vector[row]));
            }
        }
        let Some(pivot) = candidate.iter().position(|value| !value.is_zero()) else {
            continue;
        };
        let inverse = candidate[pivot].inv();
        for value in &mut candidate[pivot..] {
            *value = value.mul(inverse);
        }
        for (_, vector) in &mut basis {
            let scale = vector[pivot];
            if scale.is_zero() {
                continue;
            }
            for row in pivot..rows {
                vector[row] = vector[row].sub(scale.mul(candidate[row]));
            }
        }
        let insertion = basis
            .binary_search_by_key(&pivot, |(existing, _)| *existing)
            .unwrap_err();
        basis.insert(insertion, (pivot, candidate));
        selected.push(column);
        if selected.len() == rows {
            break;
        }
    }
    Ok((basis.len(), selected))
}

fn pivot_minor(matrix: &[QM31], columns: usize, pivots: &[usize]) -> Result<Vec<QM31>> {
    ensure!(pivots.len() == V5_C_EMAT_ROWS, "pivot count drift");
    ensure!(
        pivots.windows(2).all(|pair| pair[0] < pair[1]),
        "pivots not canonical"
    );
    ensure!(
        pivots.iter().all(|&pivot| pivot < columns),
        "pivot out of range"
    );
    Ok((0..V5_C_EMAT_ROWS)
        .flat_map(|row| {
            pivots
                .iter()
                .map(move |&column| map_entry(matrix, row, column, columns))
        })
        .collect())
}

fn invert_gauss_jordan(matrix: &[QM31], size: usize) -> Result<Vec<QM31>> {
    ensure!(matrix.len() == size * size, "inverse matrix shape drift");
    let mut left = matrix.to_vec();
    let mut right = vec![QM31::ZERO; size * size];
    for index in 0..size {
        right[index * size + index] = QM31::ONE;
    }
    for column in 0..size {
        let pivot = (column..size)
            .find(|&row| !left[row * size + column].is_zero())
            .ok_or_else(|| anyhow!("singular pivot minor at column {column}"))?;
        if pivot != column {
            for index in 0..size {
                left.swap(column * size + index, pivot * size + index);
                right.swap(column * size + index, pivot * size + index);
            }
        }
        let inverse = left[column * size + column].inv();
        for index in 0..size {
            left[column * size + index] = left[column * size + index].mul(inverse);
            right[column * size + index] = right[column * size + index].mul(inverse);
        }
        for row in 0..size {
            if row == column {
                continue;
            }
            let scale = left[row * size + column];
            if scale.is_zero() {
                continue;
            }
            for index in 0..size {
                left[row * size + index] =
                    left[row * size + index].sub(scale.mul(left[column * size + index]));
                right[row * size + index] =
                    right[row * size + index].sub(scale.mul(right[column * size + index]));
            }
        }
    }
    Ok(right)
}

fn solve_one(matrix: &[QM31], rhs: &[QM31], size: usize) -> Result<Vec<QM31>> {
    ensure!(
        matrix.len() == size * size && rhs.len() == size,
        "solve shape drift"
    );
    let mut left = matrix.to_vec();
    let mut out = rhs.to_vec();
    for column in 0..size {
        let pivot = (column..size)
            .find(|&row| !left[row * size + column].is_zero())
            .ok_or_else(|| anyhow!("singular solve matrix at column {column}"))?;
        if pivot != column {
            for index in 0..size {
                left.swap(column * size + index, pivot * size + index);
            }
            out.swap(column, pivot);
        }
        let inverse = left[column * size + column].inv();
        for index in column..size {
            left[column * size + index] = left[column * size + index].mul(inverse);
        }
        out[column] = out[column].mul(inverse);
        for row in column + 1..size {
            let scale = left[row * size + column];
            if scale.is_zero() {
                continue;
            }
            for index in column..size {
                left[row * size + index] =
                    left[row * size + index].sub(scale.mul(left[column * size + index]));
            }
            out[row] = out[row].sub(scale.mul(out[column]));
        }
    }
    for column in (0..size).rev() {
        for row in 0..column {
            let scale = left[row * size + column];
            if !scale.is_zero() {
                out[row] = out[row].sub(scale.mul(out[column]));
            }
        }
    }
    Ok(out)
}

fn invert_by_independent_solves(matrix: &[QM31], size: usize) -> Result<Vec<QM31>> {
    let mut inverse = vec![QM31::ZERO; size * size];
    for column in 0..size {
        let mut rhs = vec![QM31::ZERO; size];
        rhs[column] = QM31::ONE;
        let solution = solve_one(matrix, &rhs, size)?;
        for row in 0..size {
            inverse[row * size + column] = solution[row];
        }
    }
    Ok(inverse)
}

fn verify_minor_inverse(minor: &[QM31], inverse: &[QM31]) -> Result<()> {
    ensure!(
        minor.len() == INVERSE_ENTRIES && inverse.len() == INVERSE_ENTRIES,
        "minor/inverse shape drift"
    );
    for row in 0..PIVOT_COUNT {
        for column in 0..PIVOT_COUNT {
            let actual = (0..PIVOT_COUNT).fold(QM31::ZERO, |sum, inner| {
                sum.add(minor[row * PIVOT_COUNT + inner].mul(inverse[inner * PIVOT_COUNT + column]))
            });
            let expected = if row == column { QM31::ONE } else { QM31::ZERO };
            ensure!(
                actual == expected,
                "minor * inverse != I at ({row},{column})"
            );
        }
    }
    Ok(())
}

fn encode_pivots(pivots: &[usize]) -> Result<Vec<u8>> {
    ensure!(pivots.len() == PIVOT_COUNT, "pivot count drift");
    let mut bytes = Vec::with_capacity(PIVOT_BYTES);
    for &pivot in pivots {
        bytes.extend_from_slice(&u32::try_from(pivot)?.to_le_bytes());
    }
    Ok(bytes)
}

fn encode_inverse(inverse: &[QM31]) -> Result<Vec<u8>> {
    ensure!(
        inverse.len() == INVERSE_ENTRIES,
        "inverse entry count drift"
    );
    let mut bytes = Vec::with_capacity(INVERSE_BYTES);
    for value in inverse.iter().copied() {
        bytes.extend_from_slice(&encode_qm31(value));
    }
    Ok(bytes)
}

fn encode_certificate(inputs: &Inputs, pivots: &[usize], inverse: &[QM31]) -> Result<Vec<u8>> {
    let pivot_bytes = encode_pivots(pivots)?;
    let inverse_bytes = encode_inverse(inverse)?;
    let mut output = vec![0u8; CERTIFICATE_HEADER_BYTES];
    output[0..8].copy_from_slice(&CERTIFICATE_MAGIC);
    output[8..10].copy_from_slice(&CERTIFICATE_VERSION.to_le_bytes());
    output[10..12].copy_from_slice(&CERTIFICATE_FLAGS.to_le_bytes());
    output[12..16].copy_from_slice(&(CERTIFICATE_HEADER_BYTES as u32).to_le_bytes());
    output[16..20].copy_from_slice(&(V5_C_EMAT_ROWS as u32).to_le_bytes());
    output[20..24].copy_from_slice(&(inputs.direction_rows.len() as u32).to_le_bytes());
    output[24..28].copy_from_slice(&(V5_TRACE_ROWS as u32).to_le_bytes());
    output[28..32].copy_from_slice(&(inputs.dependent_pivot as u32).to_le_bytes());
    output[32..36].copy_from_slice(&(B_PIVOT_ROW as u32).to_le_bytes());
    output[36..40].copy_from_slice(&P.to_le_bytes());
    output[40..44].copy_from_slice(&(V5_C_EMAT_QM31_BYTES as u32).to_le_bytes());
    output[44..48].copy_from_slice(&(PIVOT_COUNT as u32).to_le_bytes());
    output[48..56].copy_from_slice(&(PIVOT_BYTES as u64).to_le_bytes());
    output[56..64].copy_from_slice(&(INVERSE_BYTES as u64).to_le_bytes());
    output[64..96].copy_from_slice(&inputs.emat_raw_sha256);
    output[96..128].copy_from_slice(&inputs.emat_matrix_sha256);
    output[128..160].copy_from_slice(&inputs.fmat_manifest_sha256);
    output[160..168]
        .copy_from_slice(&PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3.to_le_bytes());
    output[168..184].copy_from_slice(&encode_qm31(inputs.gamma));
    output[184..200].copy_from_slice(&encode_qm31(inputs.gamma16));
    output[200..216].copy_from_slice(&encode_qm31(inputs.gamma17));
    output[216..248].copy_from_slice(&inputs.scaled_map_sha256);
    output[248..280].copy_from_slice(&domain_hash(PIVOT_HASH_DOMAIN, &pivot_bytes));
    output[280..312].copy_from_slice(&domain_hash(INVERSE_HASH_DOMAIN, &inverse_bytes));
    ensure!(
        output[312..320].iter().all(|&byte| byte == 0),
        "reserved header drift"
    );
    output.extend_from_slice(&pivot_bytes);
    output.extend_from_slice(&inverse_bytes);
    ensure!(output.len() == CERTIFICATE_BYTES, "certificate size drift");
    Ok(output)
}

fn validate_certificate(bytes: &[u8], inputs: &Inputs) -> Result<CertificateView> {
    ensure!(bytes.len() == CERTIFICATE_BYTES, "certificate length drift");
    ensure!(bytes[0..8] == CERTIFICATE_MAGIC, "certificate magic drift");
    ensure!(
        read_u16(bytes, 8)? == CERTIFICATE_VERSION,
        "certificate version drift"
    );
    ensure!(
        read_u16(bytes, 10)? == CERTIFICATE_FLAGS,
        "certificate flags drift"
    );
    ensure!(
        read_u32(bytes, 12)? as usize == CERTIFICATE_HEADER_BYTES,
        "header size drift"
    );
    ensure!(
        read_u32(bytes, 16)? as usize == V5_C_EMAT_ROWS,
        "row count drift"
    );
    ensure!(
        read_u32(bytes, 20)? as usize == inputs.direction_rows.len(),
        "direction count drift"
    );
    ensure!(
        read_u32(bytes, 24)? as usize == V5_TRACE_ROWS,
        "trace size drift"
    );
    ensure!(
        read_u32(bytes, 28)? as usize == inputs.dependent_pivot,
        "dependent pivot drift"
    );
    ensure!(
        read_u32(bytes, 32)? as usize == B_PIVOT_ROW,
        "B pivot drift"
    );
    ensure!(read_u32(bytes, 36)? == P, "base-field modulus drift");
    ensure!(
        read_u32(bytes, 40)? as usize == V5_C_EMAT_QM31_BYTES,
        "field width drift"
    );
    ensure!(
        read_u32(bytes, 44)? as usize == PIVOT_COUNT,
        "pivot count drift"
    );
    ensure!(
        read_u64(bytes, 48)? as usize == PIVOT_BYTES,
        "pivot byte count drift"
    );
    ensure!(
        read_u64(bytes, 56)? as usize == INVERSE_BYTES,
        "inverse byte count drift"
    );
    ensure!(
        bytes[64..96] == inputs.emat_raw_sha256,
        "E artifact hash drift"
    );
    ensure!(
        bytes[96..128] == inputs.emat_matrix_sha256,
        "E matrix hash drift"
    );
    ensure!(
        bytes[128..160] == inputs.fmat_manifest_sha256,
        "F manifest hash drift"
    );
    ensure!(
        bytes[160..168] == PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3.to_le_bytes(),
        "atomic-v3 mask fingerprint drift"
    );
    ensure!(bytes[168..184] == encode_qm31(inputs.gamma), "gamma drift");
    ensure!(
        bytes[184..200] == encode_qm31(inputs.gamma16),
        "gamma16 drift"
    );
    ensure!(
        bytes[200..216] == encode_qm31(inputs.gamma17),
        "gamma17 drift"
    );
    ensure!(
        bytes[216..248] == inputs.scaled_map_sha256,
        "scaled map hash drift"
    );
    ensure!(
        bytes[312..320].iter().all(|&byte| byte == 0),
        "reserved bytes nonzero"
    );

    let pivot_bytes = &bytes[CERTIFICATE_HEADER_BYTES..CERTIFICATE_HEADER_BYTES + PIVOT_BYTES];
    let inverse_bytes = &bytes[CERTIFICATE_HEADER_BYTES + PIVOT_BYTES..];
    ensure!(
        bytes[248..280] == domain_hash(PIVOT_HASH_DOMAIN, pivot_bytes),
        "pivot section hash drift"
    );
    ensure!(
        bytes[280..312] == domain_hash(INVERSE_HASH_DOMAIN, inverse_bytes),
        "inverse section hash drift"
    );
    let pivots = pivot_bytes
        .chunks_exact(4)
        .map(|encoded| u32::from_le_bytes(encoded.try_into().unwrap()) as usize)
        .collect::<Vec<_>>();
    ensure!(
        pivots.len() == PIVOT_COUNT
            && pivots.windows(2).all(|pair| pair[0] < pair[1])
            && pivots
                .iter()
                .all(|&pivot| pivot < inputs.direction_rows.len()),
        "non-canonical pivot columns"
    );
    let inverse = inverse_bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .enumerate()
        .map(|(index, encoded)| {
            QM31::from_le_bytes(encoded)
                .ok_or_else(|| anyhow!("non-canonical inverse entry {index}"))
        })
        .collect::<Result<Vec<_>>>()?;
    ensure!(
        inverse.len() == INVERSE_ENTRIES,
        "decoded inverse shape drift"
    );
    Ok(CertificateView { pivots, inverse })
}

fn verify_certificate_against_map(view: &CertificateView, inputs: &Inputs) -> Result<()> {
    let minor = pivot_minor(
        &inputs.scaled_map,
        inputs.direction_rows.len(),
        &view.pivots,
    )?;
    verify_minor_inverse(&minor, &view.inverse)
}

fn sparse_solve(
    view: &CertificateView,
    direction_count: usize,
    target: &[QM31],
) -> Result<Vec<QM31>> {
    ensure!(target.len() == V5_C_EMAT_ROWS, "target shape drift");
    let mut coefficients = vec![QM31::ZERO; direction_count];
    for (minor_row, &direction) in view.pivots.iter().enumerate() {
        coefficients[direction] = (0..V5_C_EMAT_ROWS).fold(QM31::ZERO, |sum, column| {
            sum.add(view.inverse[minor_row * V5_C_EMAT_ROWS + column].mul(target[column]))
        });
    }
    Ok(coefficients)
}

fn apply_map(matrix: &[QM31], rows: usize, columns: usize, vector: &[QM31]) -> Result<Vec<QM31>> {
    ensure!(
        matrix.len() == rows * columns && vector.len() == columns,
        "map shape drift"
    );
    Ok((0..rows)
        .map(|row| {
            (0..columns).fold(QM31::ZERO, |sum, column| {
                sum.add(map_entry(matrix, row, column, columns).mul(vector[column]))
            })
        })
        .collect())
}

fn hcopy_message(inputs: &Inputs, coefficients: &[QM31]) -> Result<[QM31; V5_TRACE_ROWS]> {
    ensure!(
        coefficients.len() == inputs.direction_rows.len(),
        "Hcopy coefficient shape drift"
    );
    let mut message = [QM31::ZERO; V5_TRACE_ROWS];
    for (&row, coefficient) in inputs
        .direction_rows
        .iter()
        .zip(coefficients.iter().copied())
    {
        message[row] = message[row].add(coefficient);
        message[inputs.dependent_pivot] = message[inputs.dependent_pivot].sub(coefficient);
    }
    ensure!(
        inactive_sum(&message).is_zero(),
        "Hcopy correction changed inactive relation"
    );
    let active = atomic_state_only_copy_active_rows_v3();
    ensure!(
        active
            .iter()
            .all(|&row| message[usize::from(row)].is_zero()),
        "Hcopy correction touched an active row"
    );
    Ok(message)
}

fn free_from_message(
    message: &[QM31; V5_TRACE_ROWS],
    pivot: usize,
) -> [QM31; V5_C_FREE_COORDINATES] {
    core::array::from_fn(|coordinate| {
        let row = if coordinate < pivot {
            coordinate
        } else {
            coordinate + 1
        };
        message[row]
    })
}

fn q(seed: u32) -> QM31 {
    use aspis_core::field::{CM31, M31};
    QM31 {
        c0: CM31::new(M31(seed * 1_003 + 1), M31(seed * 1_009 + 3)),
        c1: CM31::new(M31(seed * 1_021 + 5), M31(seed * 1_031 + 7)),
    }
}

/// Check the exact normalization identity on deterministic arbitrary targets.
/// This is not a claim that Hcopy can be used twice: the correction's own E
/// view is deliberately checked to be nonzero for nonzero repair targets.
fn check_normalization_cases(inputs: &Inputs, view: &CertificateView, cases: usize) -> Result<()> {
    let b_coordinate = free_coordinate_for_row(B_PIVOT_ROW, inputs.dependent_pivot)?;
    let b_column = inputs.emat.column(b_coordinate);
    for case in 0..cases {
        let other_pre_c_e = (0..V5_C_EMAT_ROWS)
            .map(|row| q(50_000 + (case * V5_C_EMAT_ROWS + row) as u32))
            .collect::<Vec<_>>();
        let delta_p = q(80_000 + case as u32);
        let normalized_b_e = b_column.map(|value| delta_p.mul(value));
        let aggregate_without_hcopy = (0..V5_C_EMAT_ROWS)
            .map(|row| other_pre_c_e[row].add(inputs.gamma17.mul(normalized_b_e[row])))
            .collect::<Vec<_>>();
        ensure!(
            aggregate_without_hcopy.iter().any(|value| !value.is_zero()),
            "degenerate normalization fixture"
        );
        let repair_target = aggregate_without_hcopy
            .iter()
            .copied()
            .map(QM31::neg)
            .collect::<Vec<_>>();
        let coefficients = sparse_solve(view, inputs.direction_rows.len(), &repair_target)?;
        let scaled_hcopy_e = apply_map(
            &inputs.scaled_map,
            V5_C_EMAT_ROWS,
            inputs.direction_rows.len(),
            &coefficients,
        )?;
        ensure!(
            scaled_hcopy_e == repair_target,
            "right-inverse solve missed target"
        );

        let hcopy = hcopy_message(inputs, &coefficients)?;
        let hcopy_free = free_from_message(&hcopy, inputs.dependent_pivot);
        let hcopy_e = inputs.emat.mul_vec(&hcopy_free);
        for row in 0..V5_C_EMAT_ROWS {
            ensure!(
                inputs.gamma16.mul(hcopy_e[row]) == scaled_hcopy_e[row],
                "Hcopy message/E map correspondence failed"
            );
            ensure!(
                aggregate_without_hcopy[row]
                    .add(scaled_hcopy_e[row])
                    .is_zero(),
                "normalized pre-C E cancellation failed"
            );
        }
        ensure!(
            hcopy_e.iter().any(|value| !value.is_zero()),
            "nonzero repair unexpectedly preserved Hcopy's own E view"
        );

        // Raw B pivot change has the separately published inactive delta.
        // Subtracting that delta at the canonical dependent pivot yields the
        // exact ker(ell) representative whose E image is the artifact column.
        let mut raw_b = [QM31::ZERO; V5_TRACE_ROWS];
        raw_b[B_PIVOT_ROW] = delta_p;
        ensure!(
            inactive_sum(&raw_b) == delta_p,
            "raw B pivot relation drift"
        );
        let mut normalized_b = raw_b;
        normalized_b[inputs.dependent_pivot] = normalized_b[inputs.dependent_pivot].sub(delta_p);
        ensure!(
            inactive_sum(&normalized_b).is_zero(),
            "B normalization left ker ell"
        );
        let normalized_free = free_from_message(&normalized_b, inputs.dependent_pivot);
        let actual_normalized_e = inputs.emat.mul_vec(&normalized_free);
        ensure!(
            actual_normalized_e == normalized_b_e,
            "B normalized E column drift"
        );
    }
    Ok(())
}

/// Exact linearity check for the correct no-double-counting composition rule.
/// All eighteen pre-C lane views use the same frozen E matrix.  Consequently
/// matching each lane's own E view makes the gamma-combined pre-C E view match
/// automatically.
fn check_lane_wise_composition(inputs: &Inputs) -> Result<()> {
    const PRE_C_LANES: usize = 18;
    let lane_free: [[QM31; V5_C_FREE_COORDINATES]; PRE_C_LANES] = core::array::from_fn(|lane| {
        core::array::from_fn(|column| q(100_000 + (lane * V5_C_FREE_COORDINATES + column) as u32))
    });
    let mut combined_free = [QM31::ZERO; V5_C_FREE_COORDINATES];
    let mut combined_views = [QM31::ZERO; V5_C_EMAT_ROWS];
    let mut power = QM31::ONE;
    for free in &lane_free {
        let view = inputs.emat.mul_vec(free);
        for column in 0..V5_C_FREE_COORDINATES {
            combined_free[column] = combined_free[column].add(power.mul(free[column]));
        }
        for row in 0..V5_C_EMAT_ROWS {
            combined_views[row] = combined_views[row].add(power.mul(view[row]));
        }
        power = power.mul(inputs.gamma);
    }
    ensure!(
        inputs.emat.mul_vec(&combined_free) == combined_views,
        "E did not commute with the gamma-combined pre-C lanes"
    );

    // Build one nonzero relation-preserving Hcopy padding change in ker(E).
    // This is the only kind of Hcopy reindexing that can preserve Hcopy's own
    // E view; it also leaves the pre-C E view unchanged and cannot repair a
    // nonzero residual from another lane.
    let (_, pivots) = exact_rank_and_pivots(
        &inputs.scaled_map,
        V5_C_EMAT_ROWS,
        inputs.direction_rows.len(),
    )?;
    let nonpivot = (0..inputs.direction_rows.len())
        .find(|column| !pivots.contains(column))
        .ok_or_else(|| anyhow!("Hcopy map has no kernel direction"))?;
    let minor = pivot_minor(&inputs.scaled_map, inputs.direction_rows.len(), &pivots)?;
    let inverse = invert_gauss_jordan(&minor, V5_C_EMAT_ROWS)?;
    let mut image = vec![QM31::ZERO; V5_C_EMAT_ROWS];
    for row in 0..V5_C_EMAT_ROWS {
        image[row] = map_entry(
            &inputs.scaled_map,
            row,
            nonpivot,
            inputs.direction_rows.len(),
        );
    }
    let view = CertificateView { pivots, inverse };
    let mut kernel = sparse_solve(&view, inputs.direction_rows.len(), &image)?;
    for value in &mut kernel {
        *value = value.neg();
    }
    kernel[nonpivot] = kernel[nonpivot].add(QM31::ONE);
    ensure!(
        kernel.iter().any(|value| !value.is_zero()),
        "zero kernel witness"
    );
    ensure!(
        apply_map(
            &inputs.scaled_map,
            V5_C_EMAT_ROWS,
            inputs.direction_rows.len(),
            &kernel,
        )?
        .iter()
        .all(|value| value.is_zero()),
        "constructed Hcopy kernel witness changes E"
    );
    let message = hcopy_message(inputs, &kernel)?;
    ensure!(
        message.iter().any(|value| !value.is_zero()),
        "zero Hcopy kernel message"
    );
    Ok(())
}

fn generate(results_dir: &Path) -> Result<Manifest> {
    let inputs = load_inputs(results_dir)?;
    let (rank, pivots) = exact_rank_and_pivots(
        &inputs.scaled_map,
        V5_C_EMAT_ROWS,
        inputs.direction_rows.len(),
    )?;
    let independent = independent_column_pivots(
        &inputs.scaled_map,
        V5_C_EMAT_ROWS,
        inputs.direction_rows.len(),
    )?;
    ensure!(
        independent == (rank, pivots.clone()),
        "independent pivot algorithms disagree"
    );
    ensure!(
        rank == V5_C_EMAT_ROWS,
        "Hcopy padding map rank is {rank}, expected 76"
    );
    let minor = pivot_minor(&inputs.scaled_map, inputs.direction_rows.len(), &pivots)?;
    let inverse = invert_gauss_jordan(&minor, V5_C_EMAT_ROWS)?;
    let independent_inverse = invert_by_independent_solves(&minor, V5_C_EMAT_ROWS)?;
    ensure!(
        inverse == independent_inverse,
        "independent inverse algorithms disagree"
    );
    verify_minor_inverse(&minor, &inverse)?;

    let certificate = encode_certificate(&inputs, &pivots, &inverse)?;
    let decoded = validate_certificate(&certificate, &inputs)?;
    ensure!(
        decoded.pivots == pivots && decoded.inverse == inverse,
        "certificate round-trip drift"
    );
    verify_certificate_against_map(&decoded, &inputs)?;
    check_normalization_cases(&inputs, &decoded, 16)?;
    check_lane_wise_composition(&inputs)?;

    fs::create_dir_all(results_dir).context("create results directory")?;
    let certificate_path = results_dir.join(CERTIFICATE_FILE);
    fs::write(&certificate_path, &certificate)
        .with_context(|| format!("write {}", certificate_path.display()))?;

    let pivot_bytes = encode_pivots(&pivots)?;
    let inverse_bytes = encode_inverse(&inverse)?;
    Ok(Manifest {
        schema: "aspis-v5-component-c-pre-salt-hcopy-e-right-inverse-diagnostic",
        version: 1,
        status: "STALE-SCHEDULE / PRE-SALT ONLY: exact deterministic Rust diagnostic on the pre-public-FS-salt, pre-fresh-B-pivot frozen-q18 schedule; not current deployment evidence, a Lean theorem, sampler proof, same-statement coupling, or deployed Component-C hiding claim",
        scope: Scope {
            diagnostic_only: true,
            lean_theorem_claimed: false,
            sampler_uniformity_claimed: false,
            same_statement_zk_claimed: false,
            deployed_component_c_claimed: false,
            verifier_or_wire_changed: false,
        },
        reproducible_commands: Commands {
            generate: "NO_DNA=1 cargo run -p aspis-xtask --release --bin v5_c_hcopy_right_inverse",
            test: "NO_DNA=1 cargo test -p aspis-xtask --release --bin v5_c_hcopy_right_inverse",
        },
        inputs: ManifestInputs {
            field: "exact QM31 arithmetic over M31, p = 2^31 - 1",
            emat_file: EMAT_FILE,
            emat_artifact_sha256: hex(&inputs.emat_raw_sha256),
            emat_schedule_sha256: hex(&inputs.emat_schedule_sha256),
            emat_matrix_sha256: hex(&inputs.emat_matrix_sha256),
            fmat_manifest_file: FMAT_MANIFEST_FILE,
            fmat_manifest_sha256: hex(&inputs.fmat_manifest_sha256),
            current_cu_manifest_file: CURRENT_CU_MANIFEST_FILE,
            current_cu_manifest_sha256: hex(&inputs.current_cu_manifest_sha256),
            pre_salt_schedule_differs_from_salted_cu_fixture: true,
            gamma_le_hex: hex(&encode_qm31(inputs.gamma)),
            gamma16_le_hex: hex(&encode_qm31(inputs.gamma16)),
            gamma17_le_hex: hex(&encode_qm31(inputs.gamma17)),
            atomic_v3_active_rows_fingerprint: format!(
                "0x{:016x}",
                PINNED_ATOMIC_STATE_ONLY_COPY_ACTIVE_ROWS_FINGERPRINT_V3
            ),
            dependent_inactive_pivot_row: inputs.dependent_pivot,
            component_b_pivot_row: B_PIVOT_ROW,
        },
        exact_result: ExactResult {
            map_shape: [V5_C_EMAT_ROWS, inputs.direction_rows.len()],
            map_rank: rank,
            inactive_rows: inputs.direction_rows.len() + 1,
            hcopy_padding_directions: inputs.direction_rows.len(),
            canonical_pivot_columns: pivots.clone(),
            canonical_pivot_trace_rows: pivots
                .iter()
                .map(|&column| inputs.direction_rows[column])
                .collect(),
            scaled_map_sha256: hex(&inputs.scaled_map_sha256),
            independent_pivot_algorithms_agree: true,
            independent_inverse_algorithms_agree: true,
            decoded_sparse_right_inverse_identity: "exact multiplication of the original gamma^16-scaled 76 x N Hcopy-padding map by the decoded sparse N x 76 right inverse equals I_76",
            exact_surjectivity_statement: "on the explicitly fenced pre-salt frozen-q18 schedule, for every target in QM31^76, a zero-active and zero-inactive-sum atomic-v3 Hcopy padding translation exists whose gamma^16-scaled E view is that target",
        },
        normalization_diagnostic: NormalizationDiagnostic {
            deterministic_cases_checked: 16,
            statement: "for arbitrary target deltaE and a separately chosen B row-993 pivot delta_p, the sparse inverse solves gamma^16 E(deltaH) + deltaE + gamma^17 E(delta_p*(e_993-e_pivot)) = 0 exactly",
            b_pivot_normalization: "the raw B row-993 change has inactive claim delta_p; subtracting delta_p at the canonical dependent inactive pivot gives its ker(ell) representative without changing the separately published claim accounting",
            hcopy_relations_preserved: "every solved deltaH is zero on atomic-v3 active rows and has exact inactive sum zero",
            double_counting_guard: "a nonzero repair necessarily changes Hcopy's own E view; the same Hcopy degrees cannot both match Hcopy's released view and independently repair another lane's nonzero E residual",
        },
        composition_rule: CompositionRule {
            statement: "the valid composition is lane-wise: if every semantic/A lane, Hcopy, and B is coupled to match its own exact 76-coordinate E view under one pinned schedule and gamma, then E(preC_1-preC_2)=sum_{j<16} gamma^j E(delta_semantic_j)+gamma^16 E(delta_Hcopy)+gamma^17 E(delta_B)=0 by exact linearity",
            current_matrix_provenance: "the three existing pre-salt Component-A, Component-B, and Hcopy rank probes literally construct their observations with this same old Emat artifact and its same 72 layer-zero plus three MLE plus one structured-terminal rows; the salted+p schedule must be regenerated and rechecked",
            implication: "the Hcopy right inverse is capacity for matching Hcopy's own E view, not an additional post-composition repair budget",
        },
        certificate: CertificateMetadata {
            file: CERTIFICATE_FILE,
            format_version: CERTIFICATE_VERSION,
            bytes: certificate.len(),
            sha256: hex(&sha256(&certificate)),
            pivot_section_sha256: hex(&domain_hash(PIVOT_HASH_DOMAIN, &pivot_bytes)),
            inverse_section_sha256: hex(&domain_hash(INVERSE_HASH_DOMAIN, &inverse_bytes)),
            sparse_storage: "76 canonical direction ordinals plus row-major 76 x 76 inverse; every non-pivot row of the conceptual N x 76 right inverse is zero",
            mutation_tests: "raw section-hash mutation and rehash-consistent algebra mutation both fail closed",
        },
        remaining_obligations: vec![
            "Regenerate the real-host artifact and Emat after public FS salts and the fresh Component-B pivot pad are finalized; the current salted CU query vector already differs from this certificate's pre-salt query vector.",
            "Prove the Hcopy padding sampler/reindexing is measure-preserving and supplies the required conditional uniform law; rank and a right inverse alone do not prove this.",
            "Bind the canonical certificate bytes, atomic-v3 padding basis, gamma, and frozen Emat bytes to the corresponding Lean maps.",
            "Discharge lane-wise A, Hcopy, and B E-view matching jointly under one transcript schedule; do not reuse Hcopy's 76 degrees after matching its own view.",
            "Bind the raw B pivot claim normalization and row-993 serialization to the deployed Rust verifier transcript.",
            "This frozen-q18 result is schedule-specific and does not prove availability for every Fiat-Shamir schedule.",
            "Component C's deployed legal map, sampler, full-view correspondence, and end-to-end zero-knowledge reduction remain open.",
        ],
    })
}

fn workspace_results_dir() -> Result<std::path::PathBuf> {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .ok_or_else(|| anyhow!("xtask has no workspace parent"))?;
    Ok(workspace.join("results/spend"))
}

fn main() -> Result<()> {
    let results_dir = workspace_results_dir()?;
    let manifest = generate(&results_dir)?;
    let manifest_path = results_dir.join(MANIFEST_FILE);
    fs::write(
        &manifest_path,
        format!("{}\n", serde_json::to_string_pretty(&manifest)?),
    )
    .with_context(|| format!("write {}", manifest_path.display()))?;
    println!(
        "wrote {} and {}: rank={}, directions={}, certificate={} bytes sha256={}",
        results_dir.join(CERTIFICATE_FILE).display(),
        manifest_path.display(),
        manifest.exact_result.map_rank,
        manifest.exact_result.hcopy_padding_directions,
        manifest.certificate.bytes,
        manifest.certificate.sha256,
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certificate_recomputes_byte_for_byte_and_exact_identity_holds() {
        let results_dir = workspace_results_dir().unwrap();
        let inputs = load_inputs(&results_dir).unwrap();
        let (rank, pivots) = exact_rank_and_pivots(
            &inputs.scaled_map,
            V5_C_EMAT_ROWS,
            inputs.direction_rows.len(),
        )
        .unwrap();
        assert_eq!(rank, V5_C_EMAT_ROWS);
        assert_eq!(
            independent_column_pivots(
                &inputs.scaled_map,
                V5_C_EMAT_ROWS,
                inputs.direction_rows.len(),
            )
            .unwrap(),
            (rank, pivots.clone())
        );
        let minor = pivot_minor(&inputs.scaled_map, inputs.direction_rows.len(), &pivots).unwrap();
        let inverse = invert_gauss_jordan(&minor, V5_C_EMAT_ROWS).unwrap();
        assert_eq!(
            inverse,
            invert_by_independent_solves(&minor, V5_C_EMAT_ROWS).unwrap()
        );
        let first = encode_certificate(&inputs, &pivots, &inverse).unwrap();
        let second = encode_certificate(&inputs, &pivots, &inverse).unwrap();
        assert_eq!(first, second);
        let decoded = validate_certificate(&first, &inputs).unwrap();
        verify_certificate_against_map(&decoded, &inputs).unwrap();
    }

    #[test]
    fn raw_and_rehash_consistent_mutations_fail_closed() {
        let results_dir = workspace_results_dir().unwrap();
        let inputs = load_inputs(&results_dir).unwrap();
        let (_, pivots) = exact_rank_and_pivots(
            &inputs.scaled_map,
            V5_C_EMAT_ROWS,
            inputs.direction_rows.len(),
        )
        .unwrap();
        let minor = pivot_minor(&inputs.scaled_map, inputs.direction_rows.len(), &pivots).unwrap();
        let inverse = invert_gauss_jordan(&minor, V5_C_EMAT_ROWS).unwrap();
        let certificate = encode_certificate(&inputs, &pivots, &inverse).unwrap();

        let mut raw_mutation = certificate.clone();
        *raw_mutation.last_mut().unwrap() ^= 1;
        assert!(validate_certificate(&raw_mutation, &inputs).is_err());

        let mut algebra_mutation = certificate;
        let inverse_start = CERTIFICATE_HEADER_BYTES + PIVOT_BYTES;
        let mutated = QM31::from_le_bytes(
            &algebra_mutation[inverse_start..inverse_start + V5_C_EMAT_QM31_BYTES],
        )
        .unwrap()
        .add(QM31::ONE);
        algebra_mutation[inverse_start..inverse_start + V5_C_EMAT_QM31_BYTES]
            .copy_from_slice(&encode_qm31(mutated));
        let new_inverse_hash = domain_hash(INVERSE_HASH_DOMAIN, &algebra_mutation[inverse_start..]);
        algebra_mutation[280..312].copy_from_slice(&new_inverse_hash);
        let structurally_valid = validate_certificate(&algebra_mutation, &inputs).unwrap();
        assert!(verify_certificate_against_map(&structurally_valid, &inputs).is_err());
    }

    #[test]
    fn normalization_is_exact_but_hcopy_capacity_is_not_double_counted() {
        let results_dir = workspace_results_dir().unwrap();
        let inputs = load_inputs(&results_dir).unwrap();
        let (_, pivots) = exact_rank_and_pivots(
            &inputs.scaled_map,
            V5_C_EMAT_ROWS,
            inputs.direction_rows.len(),
        )
        .unwrap();
        let minor = pivot_minor(&inputs.scaled_map, inputs.direction_rows.len(), &pivots).unwrap();
        let inverse = invert_gauss_jordan(&minor, V5_C_EMAT_ROWS).unwrap();
        let view = CertificateView { pivots, inverse };
        check_normalization_cases(&inputs, &view, 16).unwrap();
        check_lane_wise_composition(&inputs).unwrap();
    }
}
