//! Exact offline certificate for the frozen Component-C quotient obstruction.
//!
//! The certificate identifies the 19-dimensional dual quotient
//! `im(F) / F(ker E)` without defining a legal witness-difference map.  It is
//! computational audit evidence only: no verifier, proof wire, or SBF binary
//! consumes either emitted file.

use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::field::{P, QM31};
use aspis_prover::v5_mask::{
    component_c_emat::{
        validate_component_c_emat_artifact, V5_C_EMAT_COLUMNS, V5_C_EMAT_QM31_BYTES, V5_C_EMAT_ROWS,
    },
    component_c_fmat::{validate_component_c_fmat_artifact, V5_C_FMAT_COLUMNS, V5_C_FMAT_ROWS},
};
use serde::Serialize;
use sha2::{Digest as _, Sha256};

use crate::v5_component_c_rank::{
    decode_matrix, exact_row_basis_rank_and_pivots, exact_row_rank_and_pivots, invert_square,
    verify_right_inverse_identity,
};

const EMAT_ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_emat.bin";
const FMAT_ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_fmat.bin";
const CERTIFICATE_FILE: &str = "v5_component_c_frozen_q18_quotient_obstruction.bin";
const MANIFEST_FILE: &str = "v5_component_c_frozen_q18_quotient_obstruction.json";

const E_ROWS: usize = V5_C_EMAT_ROWS;
const F_ROWS: usize = V5_C_FMAT_ROWS;
const COLUMNS: usize = V5_C_EMAT_COLUMNS;
const JOINT_ROWS: usize = E_ROWS + F_ROWS;
const F_RANK: usize = 134;
const JOINT_RANK: usize = 191;
const RESTRICTED_RANK: usize = JOINT_RANK - E_ROWS;
const LEFT_NULL_DIMENSION: usize = F_ROWS - F_RANK;
const OBSTRUCTION_DIMENSION: usize = F_RANK - RESTRICTED_RANK;

const ARTIFACT_MAGIC: [u8; 8] = *b"AV5QOC01";
const ARTIFACT_VERSION: u16 = 1;
const ARTIFACT_FLAGS: u16 = 0;
const ARTIFACT_HEADER_BYTES: usize = 640;
const SECTION_COUNT: usize = 6;
const SECTION_DESCRIPTOR_BYTES: usize = 48;
const SECTION_TABLE_OFFSET: usize = 288;

const SECTION_E_RANK: usize = 0;
const SECTION_F_RANK: usize = 1;
const SECTION_JOINT_RANK: usize = 2;
const SECTION_LEFT_NULL: usize = 3;
const SECTION_A: usize = 4;
const SECTION_Q: usize = 5;

const PAYLOAD_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-obstruction-payload-v1";
const PAIRS_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-obstruction-pairs-v1";
const SECTION_HASH_DOMAINS: [&[u8]; SECTION_COUNT] = [
    b"aspis-v5-component-c-obstruction-e-rank-v1",
    b"aspis-v5-component-c-obstruction-f-rank-v1",
    b"aspis-v5-component-c-obstruction-joint-rank-v1",
    b"aspis-v5-component-c-obstruction-left-null-v1",
    b"aspis-v5-component-c-obstruction-a-v1",
    b"aspis-v5-component-c-obstruction-q-v1",
];

const F_BLOCKS: [(&str, usize, usize); 5] = [
    ("relation OOD and sumcheck rows", 0, 36),
    ("authenticated later layer 1", 36, 108),
    ("authenticated later layer 2", 108, 180),
    ("authenticated later layer 3", 180, 252),
    ("final coefficients", 252, 256),
];

const _: () = assert!(V5_C_EMAT_COLUMNS == V5_C_FMAT_COLUMNS);
const _: () = assert!(E_ROWS == 76);
const _: () = assert!(F_ROWS == 256);
const _: () = assert!(COLUMNS == 1023);
const _: () = assert!(JOINT_ROWS == 332);
const _: () = assert!(RESTRICTED_RANK == 115);
const _: () = assert!(LEFT_NULL_DIMENSION == 122);
const _: () = assert!(OBSTRUCTION_DIMENSION == 19);
const _: () = assert!(
    SECTION_TABLE_OFFSET + SECTION_COUNT * SECTION_DESCRIPTOR_BYTES <= ARTIFACT_HEADER_BYTES
);

#[derive(Clone, Debug)]
pub struct V5ComponentCObstructionOutcome {
    pub artifact_path: PathBuf,
    pub manifest_path: PathBuf,
    pub artifact_bytes: usize,
    pub artifact_sha256: String,
    pub pair_sha256: String,
    pub total_ms: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RankCertificate {
    source_rows: usize,
    source_columns: usize,
    row_indices: Vec<usize>,
    column_indices: Vec<usize>,
    inverse: Vec<QM31>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExactCertificate {
    e_rank: RankCertificate,
    f_rank: RankCertificate,
    joint_rank: RankCertificate,
    left_null_f: Vec<QM31>,
    a: Vec<QM31>,
    q: Vec<QM31>,
    left_null_pivots: Vec<usize>,
    a_pivots: Vec<usize>,
}

#[derive(Clone, Debug)]
struct SectionDescriptor {
    offset: usize,
    length: usize,
    hash: [u8; 32],
}

#[derive(Serialize)]
struct Manifest {
    schema: &'static str,
    version: u32,
    status: &'static str,
    scope: Scope,
    reproducible_command: &'static str,
    inputs: Inputs,
    exact_dimensions: ExactDimensions,
    certificate: CertificateMetadata,
    pair_provenance: Vec<PairProvenance>,
    block_support: Vec<BlockSupport>,
    equivalence: Equivalence,
    independent_cross_checks: IndependentCrossChecks,
    remaining_blockers: Vec<&'static str>,
}

#[derive(Serialize)]
struct Scope {
    diagnostic_only: bool,
    lean_theorem_claimed: bool,
    legal_difference_or_delta_defined: bool,
    deployed_hiding_claimed: bool,
    verifier_wire_changed: bool,
    production_or_sbf_inclusion: bool,
}

#[derive(Serialize)]
struct Inputs {
    emat_file: &'static str,
    emat_artifact_sha256: String,
    emat_matrix_sha256: String,
    fmat_file: &'static str,
    fmat_artifact_sha256: String,
    fmat_matrix_sha256: String,
    field: &'static str,
}

#[derive(Serialize)]
struct ExactDimensions {
    rank_e: usize,
    rank_f: usize,
    rank_e_stacked_f: usize,
    rank_f_restricted_to_ker_e: usize,
    dimension_im_f: usize,
    dimension_f_ker_e: usize,
    quotient_dimension: usize,
    left_null_f_dimension: usize,
    raw_f_codomain_dimension: usize,
    intrinsic_f_row_relations: usize,
}

#[derive(Serialize)]
struct CertificateMetadata {
    file: &'static str,
    bytes: usize,
    sha256: String,
    pairs_sha256: String,
    format_version: u16,
    sections: Vec<SectionMetadata>,
    e_rank_rows: Vec<usize>,
    e_rank_columns: Vec<usize>,
    f_rank_rows: Vec<usize>,
    f_rank_columns: Vec<usize>,
    joint_rank_rows: Vec<usize>,
    joint_rank_columns: Vec<usize>,
    left_null_pivots: Vec<usize>,
    a_pivots: Vec<usize>,
}

#[derive(Serialize)]
struct SectionMetadata {
    name: &'static str,
    offset: usize,
    bytes: usize,
    sha256: String,
}

#[derive(Serialize)]
struct PairProvenance {
    index: usize,
    a_pivot_column: usize,
    a_nonzero_indices: Vec<usize>,
    q_nonzero_indices: Vec<usize>,
    q_nonzero_by_block: Vec<usize>,
    a_sha256: String,
    q_sha256: String,
    common_row_sha256: String,
}

#[derive(Serialize)]
struct BlockSupport {
    name: &'static str,
    f_row_range: [usize; 2],
    q_restriction_rank: usize,
    pairs_with_nonzero_support: usize,
    total_nonzero_coefficients: usize,
}

#[derive(Serialize)]
struct Equivalence {
    exact_statement: &'static str,
    annihilation_identity: &'static str,
    normalized_residual_reduction: &'static str,
    dimension_argument: &'static str,
    proof_status: &'static str,
}

#[derive(Serialize)]
struct IndependentCrossChecks {
    two_rank_algorithms_agree: bool,
    tracked_and_transpose_left_null_bases_equal: bool,
    residual_and_joint_pair_constructions_equal: bool,
    all_pair_equations_exact: bool,
    rank_minor_inverse_identities_exact: bool,
    left_null_equations_exact: bool,
    canonical_rref_and_quotient_representatives_checked: bool,
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

fn domain_hash(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    hasher.finalize().into()
}

fn encode_qm31(values: &[QM31]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len() * V5_C_EMAT_QM31_BYTES];
    for (index, value) in values.iter().copied().enumerate() {
        value.write_le_bytes(
            &mut bytes[index * V5_C_EMAT_QM31_BYTES..(index + 1) * V5_C_EMAT_QM31_BYTES],
        );
    }
    bytes
}

fn decode_qm31(bytes: &[u8], entries: usize, context: &'static str) -> Result<Vec<QM31>> {
    ensure!(
        bytes.len() == entries * V5_C_EMAT_QM31_BYTES,
        "{context}: byte length drift"
    );
    bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .enumerate()
        .map(|(index, encoded)| {
            QM31::from_le_bytes(encoded)
                .ok_or_else(|| anyhow!("{context}: non-canonical QM31 entry {index}"))
        })
        .collect()
}

fn transpose(matrix: &[QM31], rows: usize, columns: usize) -> Result<Vec<QM31>> {
    ensure!(matrix.len() == rows * columns, "transpose shape drift");
    let mut output = vec![QM31::ZERO; matrix.len()];
    for row in 0..rows {
        for column in 0..columns {
            output[column * rows + row] = matrix[row * columns + column];
        }
    }
    Ok(output)
}

fn row_times_matrix(
    row: &[QM31],
    matrix: &[QM31],
    matrix_rows: usize,
    columns: usize,
) -> Result<Vec<QM31>> {
    ensure!(row.len() == matrix_rows, "row-times-matrix row drift");
    ensure!(
        matrix.len() == matrix_rows * columns,
        "row-times-matrix shape drift"
    );
    let mut output = vec![QM31::ZERO; columns];
    for source in 0..matrix_rows {
        let scale = row[source];
        if scale.is_zero() {
            continue;
        }
        for column in 0..columns {
            output[column] = output[column].add(scale.mul(matrix[source * columns + column]));
        }
    }
    Ok(output)
}

fn matrix_product(
    left: &[QM31],
    left_rows: usize,
    inner: usize,
    right: &[QM31],
    right_columns: usize,
) -> Result<Vec<QM31>> {
    ensure!(left.len() == left_rows * inner, "left product shape drift");
    ensure!(
        right.len() == inner * right_columns,
        "right product shape drift"
    );
    let mut output = vec![QM31::ZERO; left_rows * right_columns];
    for row in 0..left_rows {
        for middle in 0..inner {
            let scale = left[row * inner + middle];
            if scale.is_zero() {
                continue;
            }
            for column in 0..right_columns {
                let position = row * right_columns + column;
                output[position] =
                    output[position].add(scale.mul(right[middle * right_columns + column]));
            }
        }
    }
    Ok(output)
}

/// Canonical Gauss-Jordan reduction. Every row operation is mirrored onto
/// the optional companion matrix.
fn rref_with_companion(
    matrix: &mut [QM31],
    rows: usize,
    columns: usize,
    mut companion: Option<(&mut [QM31], usize)>,
) -> Result<Vec<usize>> {
    ensure!(matrix.len() == rows * columns, "RREF matrix shape drift");
    if let Some((values, companion_columns)) = companion.as_ref() {
        ensure!(
            values.len() == rows * *companion_columns,
            "RREF companion shape drift"
        );
    }
    let mut rank = 0usize;
    let mut pivots = Vec::with_capacity(rows.min(columns));
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| !matrix[row * columns + column].is_zero())
        else {
            continue;
        };
        if pivot != rank {
            for index in 0..columns {
                matrix.swap(rank * columns + index, pivot * columns + index);
            }
            if let Some((values, companion_columns)) = companion.as_mut() {
                for index in 0..*companion_columns {
                    values.swap(
                        rank * *companion_columns + index,
                        pivot * *companion_columns + index,
                    );
                }
            }
        }
        let inverse = matrix[rank * columns + column].inv();
        for index in column..columns {
            matrix[rank * columns + index] = matrix[rank * columns + index].mul(inverse);
        }
        if let Some((values, companion_columns)) = companion.as_mut() {
            for index in 0..*companion_columns {
                values[rank * *companion_columns + index] =
                    values[rank * *companion_columns + index].mul(inverse);
            }
        }
        for row in 0..rows {
            if row == rank {
                continue;
            }
            let scale = matrix[row * columns + column];
            if scale.is_zero() {
                continue;
            }
            matrix[row * columns + column] = QM31::ZERO;
            for index in column + 1..columns {
                let position = row * columns + index;
                matrix[position] = matrix[position].sub(scale.mul(matrix[rank * columns + index]));
            }
            if let Some((values, companion_columns)) = companion.as_mut() {
                for index in 0..*companion_columns {
                    let position = row * *companion_columns + index;
                    values[position] =
                        values[position].sub(scale.mul(values[rank * *companion_columns + index]));
                }
            }
        }
        pivots.push(column);
        rank += 1;
        if rank == rows {
            break;
        }
    }
    Ok(pivots)
}

/// Row dependencies obtained by forward elimination while tracking the full
/// invertible row-operation matrix. The returned rows `z` satisfy `z M = 0`.
fn tracked_left_nullspace(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
) -> Result<(usize, Vec<usize>, Vec<QM31>)> {
    ensure!(
        matrix.len() == rows * columns,
        "tracked-null matrix shape drift"
    );
    let mut work = matrix.to_vec();
    let mut transform = vec![QM31::ZERO; rows * rows];
    for index in 0..rows {
        transform[index * rows + index] = QM31::ONE;
    }
    let mut rank = 0usize;
    let mut pivots = Vec::with_capacity(rows);
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| !work[row * columns + column].is_zero()) else {
            continue;
        };
        if pivot != rank {
            for index in 0..columns {
                work.swap(rank * columns + index, pivot * columns + index);
            }
            for index in 0..rows {
                transform.swap(rank * rows + index, pivot * rows + index);
            }
        }
        let inverse = work[rank * columns + column].inv();
        for row in rank + 1..rows {
            let scale = work[row * columns + column].mul(inverse);
            if scale.is_zero() {
                continue;
            }
            work[row * columns + column] = QM31::ZERO;
            for index in column + 1..columns {
                let position = row * columns + index;
                work[position] = work[position].sub(scale.mul(work[rank * columns + index]));
            }
            for index in 0..rows {
                let position = row * rows + index;
                transform[position] =
                    transform[position].sub(scale.mul(transform[rank * rows + index]));
            }
        }
        pivots.push(column);
        rank += 1;
        if rank == rows {
            break;
        }
    }
    ensure!(
        work[rank * columns..].iter().all(|value| value.is_zero()),
        "tracked-null residual rows were not zero"
    );
    let dependencies = transform[rank * rows..].to_vec();
    for (index, dependency) in dependencies.chunks_exact(rows).enumerate() {
        ensure!(
            row_times_matrix(dependency, matrix, rows, columns)?
                .iter()
                .all(|value| value.is_zero()),
            "tracked left-null relation {index} failed"
        );
    }
    Ok((rank, pivots, dependencies))
}

/// Independent left-nullspace construction: transpose and compute the
/// canonical right kernel from a full Gauss-Jordan reduction.
fn transpose_left_nullspace(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
) -> Result<(usize, Vec<QM31>)> {
    let mut transposed = transpose(matrix, rows, columns)?;
    let pivots = rref_with_companion(&mut transposed, columns, rows, None)?;
    let rank = pivots.len();
    let mut is_pivot = vec![false; rows];
    for &pivot in &pivots {
        is_pivot[pivot] = true;
    }
    let free_columns: Vec<_> = (0..rows).filter(|&column| !is_pivot[column]).collect();
    let mut kernel = vec![QM31::ZERO; free_columns.len() * rows];
    for (basis_index, free) in free_columns.into_iter().enumerate() {
        kernel[basis_index * rows + free] = QM31::ONE;
        for (pivot_row, &pivot_column) in pivots.iter().enumerate() {
            kernel[basis_index * rows + pivot_column] =
                QM31::ZERO.sub(transposed[pivot_row * rows + free]);
        }
    }
    for (index, dependency) in kernel.chunks_exact(rows).enumerate() {
        ensure!(
            row_times_matrix(dependency, matrix, rows, columns)?
                .iter()
                .all(|value| value.is_zero()),
            "transpose left-null relation {index} failed"
        );
    }
    Ok((rank, kernel))
}

fn canonical_rref(matrix: &[QM31], rows: usize, columns: usize) -> Result<(Vec<QM31>, Vec<usize>)> {
    let mut output = matrix.to_vec();
    let pivots = rref_with_companion(&mut output, rows, columns, None)?;
    ensure!(
        output[pivots.len() * columns..]
            .iter()
            .all(|value| value.is_zero()),
        "canonical RREF had nonzero tail"
    );
    output.truncate(pivots.len() * columns);
    Ok((output, pivots))
}

fn select_independent_rows(matrix: &[QM31], rows: usize, columns: usize) -> Result<Vec<usize>> {
    ensure!(
        matrix.len() == rows * columns,
        "independent-row matrix shape drift"
    );
    let mut basis: Vec<(usize, Vec<QM31>)> = Vec::with_capacity(rows);
    let mut selected = Vec::with_capacity(rows.min(columns));
    for (source_index, source) in matrix.chunks_exact(columns).enumerate() {
        let mut candidate = source.to_vec();
        for (pivot, row) in &basis {
            let scale = candidate[*pivot];
            if scale.is_zero() {
                continue;
            }
            candidate[*pivot] = QM31::ZERO;
            for column in *pivot + 1..columns {
                candidate[column] = candidate[column].sub(scale.mul(row[column]));
            }
        }
        let Some(pivot) = candidate.iter().position(|value| !value.is_zero()) else {
            continue;
        };
        let inverse = candidate[pivot].inv();
        for value in &mut candidate[pivot..] {
            *value = value.mul(inverse);
        }
        let insertion = basis
            .binary_search_by_key(&pivot, |(existing, _)| *existing)
            .unwrap_err();
        basis.insert(insertion, (pivot, candidate));
        selected.push(source_index);
    }
    Ok(selected)
}

fn build_rank_certificate(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
    expected_rank: usize,
) -> Result<RankCertificate> {
    let row_indices = select_independent_rows(matrix, rows, columns)?;
    ensure!(
        row_indices.len() == expected_rank,
        "rank-certificate row rank drift: got {}, expected {expected_rank}",
        row_indices.len()
    );
    let mut independent_rows = Vec::with_capacity(expected_rank * columns);
    for &row in &row_indices {
        independent_rows.extend_from_slice(&matrix[row * columns..(row + 1) * columns]);
    }
    let (rank, column_indices) =
        exact_row_rank_and_pivots(&independent_rows, expected_rank, columns)?;
    ensure!(rank == expected_rank, "rank-certificate column rank drift");
    let mut minor = Vec::with_capacity(expected_rank * expected_rank);
    for source_row in 0..expected_rank {
        for &column in &column_indices {
            minor.push(independent_rows[source_row * columns + column]);
        }
    }
    let inverse = invert_square(&minor, expected_rank)?;
    verify_right_inverse_identity(&minor, &inverse, expected_rank)?;
    Ok(RankCertificate {
        source_rows: rows,
        source_columns: columns,
        row_indices,
        column_indices,
        inverse,
    })
}

fn verify_rank_certificate(matrix: &[QM31], certificate: &RankCertificate) -> Result<()> {
    let rank = certificate.row_indices.len();
    ensure!(
        matrix.len() == certificate.source_rows * certificate.source_columns,
        "rank certificate source shape drift"
    );
    ensure!(
        certificate.column_indices.len() == rank && certificate.inverse.len() == rank * rank,
        "rank certificate payload shape drift"
    );
    ensure!(
        certificate
            .row_indices
            .windows(2)
            .all(|pair| pair[0] < pair[1])
            && certificate
                .row_indices
                .iter()
                .all(|&row| row < certificate.source_rows),
        "rank certificate rows are not canonical"
    );
    ensure!(
        certificate
            .column_indices
            .windows(2)
            .all(|pair| pair[0] < pair[1])
            && certificate
                .column_indices
                .iter()
                .all(|&column| column < certificate.source_columns),
        "rank certificate columns are not canonical"
    );
    let mut minor = Vec::with_capacity(rank * rank);
    for &row in &certificate.row_indices {
        for &column in &certificate.column_indices {
            minor.push(matrix[row * certificate.source_columns + column]);
        }
    }
    verify_right_inverse_identity(&minor, &certificate.inverse, rank)
}

/// Reduce F modulo the canonical row space of E. Returns `(G, C)` with
/// `F = G + C E` and every row of G zero on the E pivot columns.
fn residual_mod_e(emat: &[QM31], fmat: &[QM31]) -> Result<(Vec<QM31>, Vec<QM31>)> {
    let mut e_basis = emat.to_vec();
    let mut transform = vec![QM31::ZERO; E_ROWS * E_ROWS];
    for index in 0..E_ROWS {
        transform[index * E_ROWS + index] = QM31::ONE;
    }
    let pivots = rref_with_companion(
        &mut e_basis,
        E_ROWS,
        COLUMNS,
        Some((&mut transform, E_ROWS)),
    )?;
    ensure!(pivots.len() == E_ROWS, "E was not full row rank");
    let mut residual = fmat.to_vec();
    let mut coefficients = vec![QM31::ZERO; F_ROWS * E_ROWS];
    for f_row in 0..F_ROWS {
        for (basis_row, &pivot) in pivots.iter().enumerate() {
            let scale = residual[f_row * COLUMNS + pivot];
            if scale.is_zero() {
                continue;
            }
            for column in pivot..COLUMNS {
                let position = f_row * COLUMNS + column;
                residual[position] =
                    residual[position].sub(scale.mul(e_basis[basis_row * COLUMNS + column]));
            }
            for column in 0..E_ROWS {
                let position = f_row * E_ROWS + column;
                coefficients[position] =
                    coefficients[position].add(scale.mul(transform[basis_row * E_ROWS + column]));
            }
        }
        ensure!(
            pivots
                .iter()
                .all(|&pivot| residual[f_row * COLUMNS + pivot].is_zero()),
            "F residual retained an E pivot"
        );
    }
    let reconstructed = matrix_product(&coefficients, F_ROWS, E_ROWS, emat, COLUMNS)?;
    ensure!(
        reconstructed
            .iter()
            .zip(&residual)
            .zip(fmat)
            .all(|((&ce, &g), &f)| ce.add(g) == f),
        "F = G + C E reconstruction failed"
    );
    Ok((residual, coefficients))
}

fn canonicalize_pairs(
    a_all: &[QM31],
    q_all: &[QM31],
    relation_count: usize,
    left_null_f: &[QM31],
    left_null_pivots: &[usize],
) -> Result<(Vec<QM31>, Vec<QM31>, Vec<usize>)> {
    ensure!(
        a_all.len() == relation_count * E_ROWS
            && q_all.len() == relation_count * F_ROWS
            && left_null_f.len() == LEFT_NULL_DIMENSION * F_ROWS
            && left_null_pivots.len() == LEFT_NULL_DIMENSION,
        "pair canonicalization shape drift"
    );
    let mut a_work = a_all.to_vec();
    let mut q_work = q_all.to_vec();
    let a_pivots = rref_with_companion(
        &mut a_work,
        relation_count,
        E_ROWS,
        Some((&mut q_work, F_ROWS)),
    )?;
    ensure!(
        a_pivots.len() == OBSTRUCTION_DIMENSION,
        "obstruction rank drift: got {}, expected {OBSTRUCTION_DIMENSION}",
        a_pivots.len()
    );
    a_work.truncate(OBSTRUCTION_DIMENSION * E_ROWS);
    q_work.truncate(OBSTRUCTION_DIMENSION * F_ROWS);
    for pair in 0..OBSTRUCTION_DIMENSION {
        for (left_row, &pivot) in left_null_pivots.iter().enumerate() {
            let scale = q_work[pair * F_ROWS + pivot];
            if scale.is_zero() {
                continue;
            }
            for column in 0..F_ROWS {
                let position = pair * F_ROWS + column;
                q_work[position] =
                    q_work[position].sub(scale.mul(left_null_f[left_row * F_ROWS + column]));
            }
        }
        ensure!(
            left_null_pivots
                .iter()
                .all(|&pivot| q_work[pair * F_ROWS + pivot].is_zero()),
            "quotient representative was not reduced modulo left-null(F)"
        );
    }
    Ok((a_work, q_work, a_pivots))
}

fn pairs_from_residual(
    emat: &[QM31],
    fmat: &[QM31],
    left_null_f: &[QM31],
    left_null_pivots: &[usize],
) -> Result<(Vec<QM31>, Vec<QM31>, Vec<usize>)> {
    let (residual, coefficients) = residual_mod_e(emat, fmat)?;
    let (residual_rank, _, q_kernel) = tracked_left_nullspace(&residual, F_ROWS, COLUMNS)?;
    ensure!(
        residual_rank == RESTRICTED_RANK && q_kernel.len() == (F_ROWS - RESTRICTED_RANK) * F_ROWS,
        "residual nullity drift"
    );
    let relation_count = F_ROWS - RESTRICTED_RANK;
    let a_all = matrix_product(&q_kernel, relation_count, F_ROWS, &coefficients, E_ROWS)?;
    canonicalize_pairs(
        &a_all,
        &q_kernel,
        relation_count,
        left_null_f,
        left_null_pivots,
    )
}

fn pairs_from_joint_kernel(
    joint: &[QM31],
    left_null_f: &[QM31],
    left_null_pivots: &[usize],
) -> Result<(Vec<QM31>, Vec<QM31>, Vec<usize>)> {
    let (rank, dependencies) = transpose_left_nullspace(joint, JOINT_ROWS, COLUMNS)?;
    ensure!(rank == JOINT_RANK, "independent joint rank drift");
    let relation_count = JOINT_ROWS - JOINT_RANK;
    ensure!(
        dependencies.len() == relation_count * JOINT_ROWS,
        "joint-kernel dependency shape drift"
    );
    let mut a_all = vec![QM31::ZERO; relation_count * E_ROWS];
    let mut q_all = vec![QM31::ZERO; relation_count * F_ROWS];
    for relation in 0..relation_count {
        for column in 0..E_ROWS {
            a_all[relation * E_ROWS + column] =
                QM31::ZERO.sub(dependencies[relation * JOINT_ROWS + column]);
        }
        q_all[relation * F_ROWS..(relation + 1) * F_ROWS].copy_from_slice(
            &dependencies[relation * JOINT_ROWS + E_ROWS..(relation + 1) * JOINT_ROWS],
        );
    }
    canonicalize_pairs(
        &a_all,
        &q_all,
        relation_count,
        left_null_f,
        left_null_pivots,
    )
}

fn verify_canonical_rref(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
    expected_pivots: &[usize],
    context: &'static str,
) -> Result<()> {
    let (canonical, pivots) = canonical_rref(matrix, rows, columns)?;
    ensure!(
        canonical == matrix && pivots == expected_pivots,
        "{context}: matrix is not canonical RREF"
    );
    Ok(())
}

fn verify_exact_certificate(
    emat: &[QM31],
    fmat: &[QM31],
    joint: &[QM31],
    certificate: &ExactCertificate,
) -> Result<()> {
    ensure!(
        certificate.left_null_f.len() == LEFT_NULL_DIMENSION * F_ROWS
            && certificate.a.len() == OBSTRUCTION_DIMENSION * E_ROWS
            && certificate.q.len() == OBSTRUCTION_DIMENSION * F_ROWS,
        "exact certificate matrix shape drift"
    );
    verify_rank_certificate(emat, &certificate.e_rank)?;
    verify_rank_certificate(fmat, &certificate.f_rank)?;
    verify_rank_certificate(joint, &certificate.joint_rank)?;
    ensure!(
        certificate.e_rank.row_indices.len() == E_ROWS
            && certificate.f_rank.row_indices.len() == F_RANK
            && certificate.joint_rank.row_indices.len() == JOINT_RANK,
        "rank certificate dimensions drift"
    );
    verify_canonical_rref(
        &certificate.left_null_f,
        LEFT_NULL_DIMENSION,
        F_ROWS,
        &certificate.left_null_pivots,
        "left-null(F)",
    )?;
    verify_canonical_rref(
        &certificate.a,
        OBSTRUCTION_DIMENSION,
        E_ROWS,
        &certificate.a_pivots,
        "obstruction A",
    )?;
    for (index, relation) in certificate.left_null_f.chunks_exact(F_ROWS).enumerate() {
        ensure!(
            row_times_matrix(relation, fmat, F_ROWS, COLUMNS)?
                .iter()
                .all(|value| value.is_zero()),
            "left-null(F) relation {index} failed"
        );
    }
    for pair in 0..OBSTRUCTION_DIMENSION {
        let a = &certificate.a[pair * E_ROWS..(pair + 1) * E_ROWS];
        let q = &certificate.q[pair * F_ROWS..(pair + 1) * F_ROWS];
        let a_e = row_times_matrix(a, emat, E_ROWS, COLUMNS)?;
        let q_f = row_times_matrix(q, fmat, F_ROWS, COLUMNS)?;
        ensure!(a_e == q_f, "obstruction pair {pair}: q F != a E");
        ensure!(
            certificate
                .left_null_pivots
                .iter()
                .all(|&pivot| q[pivot].is_zero()),
            "obstruction pair {pair}: q is not the canonical quotient representative"
        );
    }
    let mut structured_joint_left_null =
        vec![QM31::ZERO; (LEFT_NULL_DIMENSION + OBSTRUCTION_DIMENSION) * JOINT_ROWS];
    for relation in 0..LEFT_NULL_DIMENSION {
        structured_joint_left_null[relation * JOINT_ROWS + E_ROWS..(relation + 1) * JOINT_ROWS]
            .copy_from_slice(&certificate.left_null_f[relation * F_ROWS..(relation + 1) * F_ROWS]);
    }
    for pair in 0..OBSTRUCTION_DIMENSION {
        let relation = LEFT_NULL_DIMENSION + pair;
        for column in 0..E_ROWS {
            structured_joint_left_null[relation * JOINT_ROWS + column] =
                QM31::ZERO.sub(certificate.a[pair * E_ROWS + column]);
        }
        structured_joint_left_null[relation * JOINT_ROWS + E_ROWS..(relation + 1) * JOINT_ROWS]
            .copy_from_slice(&certificate.q[pair * F_ROWS..(pair + 1) * F_ROWS]);
    }
    for (index, relation) in structured_joint_left_null
        .chunks_exact(JOINT_ROWS)
        .enumerate()
    {
        ensure!(
            row_times_matrix(relation, joint, JOINT_ROWS, COLUMNS)?
                .iter()
                .all(|value| value.is_zero()),
            "structured joint left-null relation {index} failed"
        );
    }
    let structured_rank_first = exact_row_rank_and_pivots(
        &structured_joint_left_null,
        LEFT_NULL_DIMENSION + OBSTRUCTION_DIMENSION,
        JOINT_ROWS,
    )?;
    let structured_rank_second = exact_row_basis_rank_and_pivots(
        &structured_joint_left_null,
        LEFT_NULL_DIMENSION + OBSTRUCTION_DIMENSION,
        JOINT_ROWS,
    )?;
    ensure!(
        structured_rank_first == structured_rank_second
            && structured_rank_first.0 == LEFT_NULL_DIMENSION + OBSTRUCTION_DIMENSION,
        "structured 141-row joint left-null certificate was not independent"
    );
    let common_rows = matrix_product(&certificate.q, OBSTRUCTION_DIMENSION, F_ROWS, fmat, COLUMNS)?;
    let common_rank_first =
        exact_row_rank_and_pivots(&common_rows, OBSTRUCTION_DIMENSION, COLUMNS)?;
    let common_rank_second =
        exact_row_basis_rank_and_pivots(&common_rows, OBSTRUCTION_DIMENSION, COLUMNS)?;
    ensure!(
        common_rank_first == common_rank_second && common_rank_first.0 == OBSTRUCTION_DIMENSION,
        "QF obstruction functionals were not independent on im(F)"
    );
    // These exact finite-dimensional facts prove the advertised equivalence:
    // E has rank 76; F has lower rank 134 and 122 independent left-null
    // relations; [E;F] has lower rank 191 and 141 independent structured
    // relations (122 from left-null(F), 19 from the full-rank A block).
    // Therefore dim F(ker E)=115.  QF=AE has rank 19, so the common kernel of
    // Q on im(F) also has dimension 115 and contains F(ker E); they are equal.
    Ok(())
}

fn build_exact_certificate(emat: &[QM31], fmat: &[QM31]) -> Result<ExactCertificate> {
    let mut joint = Vec::with_capacity(JOINT_ROWS * COLUMNS);
    joint.extend_from_slice(emat);
    joint.extend_from_slice(fmat);

    let rank_checks = [
        (emat, E_ROWS, E_ROWS, "E"),
        (fmat, F_ROWS, F_RANK, "F"),
        (&joint, JOINT_ROWS, JOINT_RANK, "[E;F]"),
    ];
    for &(matrix, rows, expected, name) in &rank_checks {
        let first = exact_row_rank_and_pivots(matrix, rows, COLUMNS)?;
        let second = exact_row_basis_rank_and_pivots(matrix, rows, COLUMNS)?;
        ensure!(
            first == second && first.0 == expected,
            "independent exact rank algorithms disagree for {name}"
        );
    }

    let (tracked_f_rank, _, left_null_tracked) = tracked_left_nullspace(fmat, F_ROWS, COLUMNS)?;
    ensure!(tracked_f_rank == F_RANK, "tracked F rank drift");
    let (mut left_null_f, left_null_pivots) =
        canonical_rref(&left_null_tracked, LEFT_NULL_DIMENSION, F_ROWS)?;
    ensure!(
        left_null_pivots.len() == LEFT_NULL_DIMENSION,
        "left-null(F) dimension drift"
    );
    let (transpose_f_rank, left_null_alt) = transpose_left_nullspace(fmat, F_ROWS, COLUMNS)?;
    ensure!(transpose_f_rank == F_RANK, "transpose F rank drift");
    let (left_null_alt, left_null_alt_pivots) =
        canonical_rref(&left_null_alt, LEFT_NULL_DIMENSION, F_ROWS)?;
    ensure!(
        left_null_f == left_null_alt && left_null_pivots == left_null_alt_pivots,
        "independent left-null(F) constructions disagree"
    );

    let primary = pairs_from_residual(emat, fmat, &left_null_f, &left_null_pivots)?;
    let secondary = pairs_from_joint_kernel(&joint, &left_null_f, &left_null_pivots)?;
    ensure!(
        primary == secondary,
        "independent obstruction-pair constructions disagree"
    );
    let (a, q, a_pivots) = primary;

    // Shrink capacity variance out of the deterministic logical value.
    left_null_f.shrink_to_fit();
    let certificate = ExactCertificate {
        e_rank: build_rank_certificate(emat, E_ROWS, COLUMNS, E_ROWS)?,
        f_rank: build_rank_certificate(fmat, F_ROWS, COLUMNS, F_RANK)?,
        joint_rank: build_rank_certificate(&joint, JOINT_ROWS, COLUMNS, JOINT_RANK)?,
        left_null_f,
        a,
        q,
        left_null_pivots,
        a_pivots,
    };
    verify_exact_certificate(emat, fmat, &joint, &certificate)?;
    Ok(certificate)
}

fn encode_rank_certificate(certificate: &RankCertificate) -> Result<Vec<u8>> {
    let rank = certificate.row_indices.len();
    ensure!(
        certificate.column_indices.len() == rank && certificate.inverse.len() == rank * rank,
        "rank certificate encode shape drift"
    );
    let mut bytes = Vec::with_capacity(16 + 8 * rank + rank * rank * V5_C_EMAT_QM31_BYTES);
    bytes.extend_from_slice(&u32::try_from(rank)?.to_le_bytes());
    bytes.extend_from_slice(&u32::try_from(certificate.source_rows)?.to_le_bytes());
    bytes.extend_from_slice(&u32::try_from(certificate.source_columns)?.to_le_bytes());
    bytes.extend_from_slice(&(V5_C_EMAT_QM31_BYTES as u32).to_le_bytes());
    for &index in &certificate.row_indices {
        bytes.extend_from_slice(&u32::try_from(index)?.to_le_bytes());
    }
    for &index in &certificate.column_indices {
        bytes.extend_from_slice(&u32::try_from(index)?.to_le_bytes());
    }
    bytes.extend_from_slice(&encode_qm31(&certificate.inverse));
    Ok(bytes)
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16> {
    Ok(u16::from_le_bytes(
        bytes
            .get(offset..offset + 2)
            .ok_or_else(|| anyhow!("u16 offset out of bounds"))?
            .try_into()
            .unwrap(),
    ))
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32> {
    Ok(u32::from_le_bytes(
        bytes
            .get(offset..offset + 4)
            .ok_or_else(|| anyhow!("u32 offset out of bounds"))?
            .try_into()
            .unwrap(),
    ))
}

fn read_u64(bytes: &[u8], offset: usize) -> Result<u64> {
    Ok(u64::from_le_bytes(
        bytes
            .get(offset..offset + 8)
            .ok_or_else(|| anyhow!("u64 offset out of bounds"))?
            .try_into()
            .unwrap(),
    ))
}

fn decode_rank_certificate(
    bytes: &[u8],
    expected_rank: usize,
    expected_rows: usize,
    expected_columns: usize,
    context: &'static str,
) -> Result<RankCertificate> {
    ensure!(bytes.len() >= 16, "{context}: rank section too short");
    let rank = read_u32(bytes, 0)? as usize;
    let source_rows = read_u32(bytes, 4)? as usize;
    let source_columns = read_u32(bytes, 8)? as usize;
    ensure!(
        rank == expected_rank
            && source_rows == expected_rows
            && source_columns == expected_columns
            && read_u32(bytes, 12)? as usize == V5_C_EMAT_QM31_BYTES,
        "{context}: rank section header drift"
    );
    let indices_bytes = rank
        .checked_mul(8)
        .ok_or_else(|| anyhow!("{context}: index length overflow"))?;
    let inverse_entries = rank
        .checked_mul(rank)
        .ok_or_else(|| anyhow!("{context}: inverse shape overflow"))?;
    let expected_len = 16usize
        .checked_add(indices_bytes)
        .and_then(|value| value.checked_add(inverse_entries.checked_mul(V5_C_EMAT_QM31_BYTES)?))
        .ok_or_else(|| anyhow!("{context}: section length overflow"))?;
    ensure!(
        bytes.len() == expected_len,
        "{context}: section length drift"
    );
    let mut row_indices = Vec::with_capacity(rank);
    let mut column_indices = Vec::with_capacity(rank);
    for index in 0..rank {
        row_indices.push(read_u32(bytes, 16 + 4 * index)? as usize);
    }
    for index in 0..rank {
        column_indices.push(read_u32(bytes, 16 + 4 * rank + 4 * index)? as usize);
    }
    let inverse_start = 16 + indices_bytes;
    let inverse = decode_qm31(&bytes[inverse_start..], inverse_entries, context)?;
    Ok(RankCertificate {
        source_rows,
        source_columns,
        row_indices,
        column_indices,
        inverse,
    })
}

fn encode_artifact(
    certificate: &ExactCertificate,
    emat_artifact_sha256: [u8; 32],
    fmat_artifact_sha256: [u8; 32],
    emat_matrix_sha256: [u8; 32],
    fmat_matrix_sha256: [u8; 32],
) -> Result<(Vec<u8>, Vec<SectionDescriptor>)> {
    let sections = vec![
        encode_rank_certificate(&certificate.e_rank)?,
        encode_rank_certificate(&certificate.f_rank)?,
        encode_rank_certificate(&certificate.joint_rank)?,
        encode_qm31(&certificate.left_null_f),
        encode_qm31(&certificate.a),
        encode_qm31(&certificate.q),
    ];
    ensure!(sections.len() == SECTION_COUNT, "section count drift");
    let payload_bytes: usize = sections.iter().map(Vec::len).sum();
    let total_bytes = ARTIFACT_HEADER_BYTES
        .checked_add(payload_bytes)
        .ok_or_else(|| anyhow!("artifact length overflow"))?;
    let mut artifact = vec![0u8; ARTIFACT_HEADER_BYTES];
    let mut descriptors = Vec::with_capacity(SECTION_COUNT);
    for (index, section) in sections.iter().enumerate() {
        let offset = artifact.len();
        artifact.extend_from_slice(section);
        descriptors.push(SectionDescriptor {
            offset,
            length: section.len(),
            hash: domain_hash(SECTION_HASH_DOMAINS[index], section),
        });
    }
    ensure!(artifact.len() == total_bytes, "artifact assembly drift");
    artifact[0..8].copy_from_slice(&ARTIFACT_MAGIC);
    artifact[8..10].copy_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    artifact[10..12].copy_from_slice(&ARTIFACT_FLAGS.to_le_bytes());
    artifact[12..16].copy_from_slice(&(ARTIFACT_HEADER_BYTES as u32).to_le_bytes());
    artifact[16..24].copy_from_slice(&(total_bytes as u64).to_le_bytes());
    artifact[24..28].copy_from_slice(&P.to_le_bytes());
    artifact[28..32].copy_from_slice(&(V5_C_EMAT_QM31_BYTES as u32).to_le_bytes());
    artifact[32..36].copy_from_slice(&(E_ROWS as u32).to_le_bytes());
    artifact[36..40].copy_from_slice(&(F_ROWS as u32).to_le_bytes());
    artifact[40..44].copy_from_slice(&(COLUMNS as u32).to_le_bytes());
    artifact[44..48].copy_from_slice(&(E_ROWS as u32).to_le_bytes());
    artifact[48..52].copy_from_slice(&(F_RANK as u32).to_le_bytes());
    artifact[52..56].copy_from_slice(&(JOINT_RANK as u32).to_le_bytes());
    artifact[56..60].copy_from_slice(&(RESTRICTED_RANK as u32).to_le_bytes());
    artifact[60..64].copy_from_slice(&(OBSTRUCTION_DIMENSION as u32).to_le_bytes());
    artifact[64..68].copy_from_slice(&(LEFT_NULL_DIMENSION as u32).to_le_bytes());
    artifact[68..72].copy_from_slice(&(SECTION_COUNT as u32).to_le_bytes());
    artifact[72..76].copy_from_slice(&(F_BLOCKS.len() as u32).to_le_bytes());
    artifact[76..80].copy_from_slice(&0u32.to_le_bytes());
    artifact[96..128].copy_from_slice(&emat_artifact_sha256);
    artifact[128..160].copy_from_slice(&fmat_artifact_sha256);
    artifact[160..192].copy_from_slice(&emat_matrix_sha256);
    artifact[192..224].copy_from_slice(&fmat_matrix_sha256);
    let payload_hash = domain_hash(PAYLOAD_HASH_DOMAIN, &artifact[ARTIFACT_HEADER_BYTES..]);
    artifact[224..256].copy_from_slice(&payload_hash);
    let mut pairs = sections[SECTION_A].clone();
    pairs.extend_from_slice(&sections[SECTION_Q]);
    artifact[256..288].copy_from_slice(&domain_hash(PAIRS_HASH_DOMAIN, &pairs));
    for (index, descriptor) in descriptors.iter().enumerate() {
        let start = SECTION_TABLE_OFFSET + index * SECTION_DESCRIPTOR_BYTES;
        artifact[start..start + 8].copy_from_slice(&(descriptor.offset as u64).to_le_bytes());
        artifact[start + 8..start + 16].copy_from_slice(&(descriptor.length as u64).to_le_bytes());
        artifact[start + 16..start + 48].copy_from_slice(&descriptor.hash);
    }
    Ok((artifact, descriptors))
}

fn parse_descriptors(bytes: &[u8]) -> Result<Vec<SectionDescriptor>> {
    let mut descriptors = Vec::with_capacity(SECTION_COUNT);
    let mut expected_offset = ARTIFACT_HEADER_BYTES;
    for index in 0..SECTION_COUNT {
        let start = SECTION_TABLE_OFFSET + index * SECTION_DESCRIPTOR_BYTES;
        let offset = usize::try_from(read_u64(bytes, start)?)?;
        let length = usize::try_from(read_u64(bytes, start + 8)?)?;
        let hash: [u8; 32] = bytes
            .get(start + 16..start + 48)
            .ok_or_else(|| anyhow!("section descriptor out of bounds"))?
            .try_into()
            .unwrap();
        ensure!(
            offset == expected_offset,
            "section {index}: non-canonical offset"
        );
        let end = offset
            .checked_add(length)
            .ok_or_else(|| anyhow!("section {index}: length overflow"))?;
        ensure!(end <= bytes.len(), "section {index}: out of bounds");
        ensure!(
            domain_hash(SECTION_HASH_DOMAINS[index], &bytes[offset..end]) == hash,
            "section {index}: hash mismatch"
        );
        descriptors.push(SectionDescriptor {
            offset,
            length,
            hash,
        });
        expected_offset = end;
    }
    ensure!(
        expected_offset == bytes.len(),
        "hidden trailing artifact bytes"
    );
    Ok(descriptors)
}

fn section<'a>(bytes: &'a [u8], descriptors: &[SectionDescriptor], index: usize) -> &'a [u8] {
    let descriptor = &descriptors[index];
    &bytes[descriptor.offset..descriptor.offset + descriptor.length]
}

fn validate_artifact(
    bytes: &[u8],
    emat_artifact_sha256: [u8; 32],
    fmat_artifact_sha256: [u8; 32],
    emat_matrix_sha256: [u8; 32],
    fmat_matrix_sha256: [u8; 32],
    emat: &[QM31],
    fmat: &[QM31],
) -> Result<ExactCertificate> {
    ensure!(bytes.len() >= ARTIFACT_HEADER_BYTES, "artifact too short");
    ensure!(bytes[0..8] == ARTIFACT_MAGIC, "artifact magic drift");
    ensure!(
        read_u16(bytes, 8)? == ARTIFACT_VERSION
            && read_u16(bytes, 10)? == ARTIFACT_FLAGS
            && read_u32(bytes, 12)? as usize == ARTIFACT_HEADER_BYTES
            && read_u64(bytes, 16)? as usize == bytes.len()
            && read_u32(bytes, 24)? == P
            && read_u32(bytes, 28)? as usize == V5_C_EMAT_QM31_BYTES
            && read_u32(bytes, 32)? as usize == E_ROWS
            && read_u32(bytes, 36)? as usize == F_ROWS
            && read_u32(bytes, 40)? as usize == COLUMNS
            && read_u32(bytes, 44)? as usize == E_ROWS
            && read_u32(bytes, 48)? as usize == F_RANK
            && read_u32(bytes, 52)? as usize == JOINT_RANK
            && read_u32(bytes, 56)? as usize == RESTRICTED_RANK
            && read_u32(bytes, 60)? as usize == OBSTRUCTION_DIMENSION
            && read_u32(bytes, 64)? as usize == LEFT_NULL_DIMENSION
            && read_u32(bytes, 68)? as usize == SECTION_COUNT
            && read_u32(bytes, 72)? as usize == F_BLOCKS.len()
            && read_u32(bytes, 76)? == 0,
        "artifact header shape drift"
    );
    ensure!(
        bytes[80..96].iter().all(|&byte| byte == 0)
            && bytes[SECTION_TABLE_OFFSET + SECTION_COUNT * SECTION_DESCRIPTOR_BYTES
                ..ARTIFACT_HEADER_BYTES]
                .iter()
                .all(|&byte| byte == 0),
        "artifact reserved bytes are not zero"
    );
    ensure!(
        bytes[96..128] == emat_artifact_sha256
            && bytes[128..160] == fmat_artifact_sha256
            && bytes[160..192] == emat_matrix_sha256
            && bytes[192..224] == fmat_matrix_sha256,
        "artifact input hash binding drift"
    );
    ensure!(
        bytes[224..256] == domain_hash(PAYLOAD_HASH_DOMAIN, &bytes[ARTIFACT_HEADER_BYTES..]),
        "artifact payload hash mismatch"
    );
    let descriptors = parse_descriptors(bytes)?;
    let mut pairs = section(bytes, &descriptors, SECTION_A).to_vec();
    pairs.extend_from_slice(section(bytes, &descriptors, SECTION_Q));
    ensure!(
        bytes[256..288] == domain_hash(PAIRS_HASH_DOMAIN, &pairs),
        "artifact pair hash mismatch"
    );
    let e_rank = decode_rank_certificate(
        section(bytes, &descriptors, SECTION_E_RANK),
        E_ROWS,
        E_ROWS,
        COLUMNS,
        "E rank",
    )?;
    let f_rank = decode_rank_certificate(
        section(bytes, &descriptors, SECTION_F_RANK),
        F_RANK,
        F_ROWS,
        COLUMNS,
        "F rank",
    )?;
    let joint_rank = decode_rank_certificate(
        section(bytes, &descriptors, SECTION_JOINT_RANK),
        JOINT_RANK,
        JOINT_ROWS,
        COLUMNS,
        "joint rank",
    )?;
    let left_null_f = decode_qm31(
        section(bytes, &descriptors, SECTION_LEFT_NULL),
        LEFT_NULL_DIMENSION * F_ROWS,
        "left-null(F)",
    )?;
    let a = decode_qm31(
        section(bytes, &descriptors, SECTION_A),
        OBSTRUCTION_DIMENSION * E_ROWS,
        "obstruction A",
    )?;
    let q = decode_qm31(
        section(bytes, &descriptors, SECTION_Q),
        OBSTRUCTION_DIMENSION * F_ROWS,
        "obstruction Q",
    )?;
    let (_, left_null_pivots) = canonical_rref(&left_null_f, LEFT_NULL_DIMENSION, F_ROWS)?;
    let (_, a_pivots) = canonical_rref(&a, OBSTRUCTION_DIMENSION, E_ROWS)?;
    let certificate = ExactCertificate {
        e_rank,
        f_rank,
        joint_rank,
        left_null_f,
        a,
        q,
        left_null_pivots,
        a_pivots,
    };
    let mut joint = Vec::with_capacity(JOINT_ROWS * COLUMNS);
    joint.extend_from_slice(emat);
    joint.extend_from_slice(fmat);
    verify_exact_certificate(emat, fmat, &joint, &certificate)?;
    Ok(certificate)
}

fn rehash_artifact(bytes: &mut [u8]) -> Result<()> {
    ensure!(
        bytes.len() >= ARTIFACT_HEADER_BYTES,
        "rehash artifact too short"
    );
    for index in 0..SECTION_COUNT {
        let descriptor_start = SECTION_TABLE_OFFSET + index * SECTION_DESCRIPTOR_BYTES;
        let offset = usize::try_from(read_u64(bytes, descriptor_start)?)?;
        let length = usize::try_from(read_u64(bytes, descriptor_start + 8)?)?;
        let end = offset
            .checked_add(length)
            .ok_or_else(|| anyhow!("rehash section length overflow"))?;
        ensure!(end <= bytes.len(), "rehash section out of bounds");
        let hash = domain_hash(SECTION_HASH_DOMAINS[index], &bytes[offset..end]);
        bytes[descriptor_start + 16..descriptor_start + 48].copy_from_slice(&hash);
    }
    let payload_hash = domain_hash(PAYLOAD_HASH_DOMAIN, &bytes[ARTIFACT_HEADER_BYTES..]);
    bytes[224..256].copy_from_slice(&payload_hash);
    let descriptors = parse_descriptors(bytes)?;
    let mut pairs = section(bytes, &descriptors, SECTION_A).to_vec();
    pairs.extend_from_slice(section(bytes, &descriptors, SECTION_Q));
    bytes[256..288].copy_from_slice(&domain_hash(PAIRS_HASH_DOMAIN, &pairs));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn artifact_teeth(
    artifact: &[u8],
    descriptors: &[SectionDescriptor],
    emat_artifact_sha256: [u8; 32],
    fmat_artifact_sha256: [u8; 32],
    emat_matrix_sha256: [u8; 32],
    fmat_matrix_sha256: [u8; 32],
    emat: &[QM31],
    fmat: &[QM31],
) -> Result<()> {
    let validate = |candidate: &[u8]| {
        validate_artifact(
            candidate,
            emat_artifact_sha256,
            fmat_artifact_sha256,
            emat_matrix_sha256,
            fmat_matrix_sha256,
            emat,
            fmat,
        )
    };

    let mut noncanonical = artifact.to_vec();
    let q_offset = descriptors[SECTION_Q].offset;
    noncanonical[q_offset..q_offset + 4].copy_from_slice(&P.to_le_bytes());
    rehash_artifact(&mut noncanonical)?;
    ensure!(
        validate(&noncanonical).is_err(),
        "non-canonical QM31 mutation was accepted"
    );

    let mut algebra = artifact.to_vec();
    let original = QM31::from_le_bytes(&algebra[q_offset..q_offset + V5_C_EMAT_QM31_BYTES])
        .ok_or_else(|| anyhow!("canonical Q entry did not decode"))?;
    original
        .add(QM31::ONE)
        .write_le_bytes(&mut algebra[q_offset..q_offset + V5_C_EMAT_QM31_BYTES]);
    rehash_artifact(&mut algebra)?;
    ensure!(
        validate(&algebra).is_err(),
        "rehash-consistent algebra mutation was accepted"
    );

    let mut reordered = artifact.to_vec();
    for &section_index in &[SECTION_A, SECTION_Q] {
        let descriptor = &descriptors[section_index];
        let row_bytes = if section_index == SECTION_A {
            E_ROWS * V5_C_EMAT_QM31_BYTES
        } else {
            F_ROWS * V5_C_EMAT_QM31_BYTES
        };
        ensure!(descriptor.length >= 2 * row_bytes, "pair section too short");
        for index in 0..row_bytes {
            reordered.swap(
                descriptor.offset + index,
                descriptor.offset + row_bytes + index,
            );
        }
    }
    rehash_artifact(&mut reordered)?;
    ensure!(
        validate(&reordered).is_err(),
        "non-canonical pair ordering was accepted"
    );

    let mut wrong_input = artifact.to_vec();
    wrong_input[96] ^= 1;
    ensure!(
        validate(&wrong_input).is_err(),
        "wrong E-artifact binding was accepted"
    );
    ensure!(
        validate(&artifact[..artifact.len() - 1]).is_err(),
        "truncated obstruction artifact was accepted"
    );
    Ok(())
}

fn pair_provenance(
    certificate: &ExactCertificate,
    emat: &[QM31],
    fmat: &[QM31],
) -> Result<Vec<PairProvenance>> {
    let mut output = Vec::with_capacity(OBSTRUCTION_DIMENSION);
    for pair in 0..OBSTRUCTION_DIMENSION {
        let a = &certificate.a[pair * E_ROWS..(pair + 1) * E_ROWS];
        let q = &certificate.q[pair * F_ROWS..(pair + 1) * F_ROWS];
        let common = row_times_matrix(q, fmat, F_ROWS, COLUMNS)?;
        ensure!(
            common == row_times_matrix(a, emat, E_ROWS, COLUMNS)?,
            "pair provenance equation drift"
        );
        output.push(PairProvenance {
            index: pair,
            a_pivot_column: certificate.a_pivots[pair],
            a_nonzero_indices: a
                .iter()
                .enumerate()
                .filter_map(|(index, value)| (!value.is_zero()).then_some(index))
                .collect(),
            q_nonzero_indices: q
                .iter()
                .enumerate()
                .filter_map(|(index, value)| (!value.is_zero()).then_some(index))
                .collect(),
            q_nonzero_by_block: F_BLOCKS
                .iter()
                .map(|(_, start, end)| {
                    q[*start..*end]
                        .iter()
                        .filter(|value| !value.is_zero())
                        .count()
                })
                .collect(),
            a_sha256: hex(&sha256(&encode_qm31(a))),
            q_sha256: hex(&sha256(&encode_qm31(q))),
            common_row_sha256: hex(&sha256(&encode_qm31(&common))),
        });
    }
    Ok(output)
}

fn block_support(certificate: &ExactCertificate) -> Result<Vec<BlockSupport>> {
    let mut output = Vec::with_capacity(F_BLOCKS.len());
    for &(name, start, end) in &F_BLOCKS {
        let width = end - start;
        let mut restricted = Vec::with_capacity(OBSTRUCTION_DIMENSION * width);
        for pair in 0..OBSTRUCTION_DIMENSION {
            restricted
                .extend_from_slice(&certificate.q[pair * F_ROWS + start..pair * F_ROWS + end]);
        }
        let (rank, _) = exact_row_rank_and_pivots(&restricted, OBSTRUCTION_DIMENSION, width)?;
        output.push(BlockSupport {
            name,
            f_row_range: [start, end],
            q_restriction_rank: rank,
            pairs_with_nonzero_support: restricted
                .chunks_exact(width)
                .filter(|row| row.iter().any(|value| !value.is_zero()))
                .count(),
            total_nonzero_coefficients: restricted.iter().filter(|value| !value.is_zero()).count(),
        });
    }
    Ok(output)
}

fn section_metadata(descriptors: &[SectionDescriptor]) -> Vec<SectionMetadata> {
    let names = [
        "E rank minor and inverse",
        "F rank minor and inverse",
        "[E;F] rank minor and inverse",
        "canonical 122x256 left-null(F) basis",
        "canonical 19x76 A coefficients",
        "canonical 19x256 Q quotient representatives",
    ];
    descriptors
        .iter()
        .zip(names)
        .map(|(descriptor, name)| SectionMetadata {
            name,
            offset: descriptor.offset,
            bytes: descriptor.length,
            sha256: hex(&descriptor.hash),
        })
        .collect()
}

pub fn run(results_dir: &Path) -> Result<V5ComponentCObstructionOutcome> {
    let total_start = Instant::now();
    let emat_path = results_dir.join(EMAT_ARTIFACT_FILE);
    let fmat_path = results_dir.join(FMAT_ARTIFACT_FILE);
    let emat_bytes =
        fs::read(&emat_path).with_context(|| format!("read {}", emat_path.display()))?;
    let fmat_bytes =
        fs::read(&fmat_path).with_context(|| format!("read {}", fmat_path.display()))?;
    let emat_artifact_sha256 = sha256(&emat_bytes);
    let fmat_artifact_sha256 = sha256(&fmat_bytes);
    let emat_view = validate_component_c_emat_artifact(&emat_bytes)
        .context("validate frozen Component-C Emat artifact")?;
    let fmat_view = validate_component_c_fmat_artifact(&fmat_bytes)
        .context("validate frozen Component-C Fmat artifact")?;
    ensure!(
        fmat_view
            .schedule_bytes
            .starts_with(emat_view.schedule_bytes),
        "E/F frozen schedules do not share the same q18 prefix"
    );
    let emat = decode_matrix(emat_view.matrix_bytes, E_ROWS, COLUMNS)?;
    let fmat = decode_matrix(fmat_view.matrix_bytes, F_ROWS, COLUMNS)?;
    let certificate = build_exact_certificate(&emat, &fmat)?;
    let (artifact, descriptors) = encode_artifact(
        &certificate,
        emat_artifact_sha256,
        fmat_artifact_sha256,
        emat_view.matrix_sha256,
        fmat_view.matrix_sha256,
    )?;
    let (second_encoding, second_descriptors) = encode_artifact(
        &certificate,
        emat_artifact_sha256,
        fmat_artifact_sha256,
        emat_view.matrix_sha256,
        fmat_view.matrix_sha256,
    )?;
    ensure!(
        artifact == second_encoding
            && descriptors
                .iter()
                .zip(&second_descriptors)
                .all(|(left, right)| {
                    left.offset == right.offset
                        && left.length == right.length
                        && left.hash == right.hash
                }),
        "obstruction certificate encoding is not deterministic"
    );
    let decoded = validate_artifact(
        &artifact,
        emat_artifact_sha256,
        fmat_artifact_sha256,
        emat_view.matrix_sha256,
        fmat_view.matrix_sha256,
        &emat,
        &fmat,
    )?;
    ensure!(
        decoded == certificate,
        "obstruction artifact round-trip drift"
    );
    artifact_teeth(
        &artifact,
        &descriptors,
        emat_artifact_sha256,
        fmat_artifact_sha256,
        emat_view.matrix_sha256,
        fmat_view.matrix_sha256,
        &emat,
        &fmat,
    )?;

    fs::create_dir_all(results_dir).context("create Component-C results directory")?;
    let artifact_path = results_dir.join(CERTIFICATE_FILE);
    fs::write(&artifact_path, &artifact)
        .with_context(|| format!("write {}", artifact_path.display()))?;
    let artifact_sha256 = sha256(&artifact);
    let pair_sha256: [u8; 32] = artifact[256..288].try_into().unwrap();
    let document = Manifest {
        schema: "aspis-v5-component-c-frozen-q18-quotient-obstruction",
        version: 1,
        status: "exact deterministic Rust certificate; not a Lean theorem or deployed Component-C hiding claim",
        scope: Scope {
            diagnostic_only: true,
            lean_theorem_claimed: false,
            legal_difference_or_delta_defined: false,
            deployed_hiding_claimed: false,
            verifier_wire_changed: false,
            production_or_sbf_inclusion: false,
        },
        reproducible_command:
            "NO_DNA=1 cargo run -p aspis-xtask --bin aspis-xtask --release -- v5-component-c-obstruction",
        inputs: Inputs {
            emat_file: EMAT_ARTIFACT_FILE,
            emat_artifact_sha256: hex(&emat_artifact_sha256),
            emat_matrix_sha256: hex(&emat_view.matrix_sha256),
            fmat_file: FMAT_ARTIFACT_FILE,
            fmat_artifact_sha256: hex(&fmat_artifact_sha256),
            fmat_matrix_sha256: hex(&fmat_view.matrix_sha256),
            field: "exact QM31 arithmetic over p = 2^31 - 1",
        },
        exact_dimensions: ExactDimensions {
            rank_e: E_ROWS,
            rank_f: F_RANK,
            rank_e_stacked_f: JOINT_RANK,
            rank_f_restricted_to_ker_e: RESTRICTED_RANK,
            dimension_im_f: F_RANK,
            dimension_f_ker_e: RESTRICTED_RANK,
            quotient_dimension: OBSTRUCTION_DIMENSION,
            left_null_f_dimension: LEFT_NULL_DIMENSION,
            raw_f_codomain_dimension: F_ROWS,
            intrinsic_f_row_relations: LEFT_NULL_DIMENSION,
        },
        certificate: CertificateMetadata {
            file: CERTIFICATE_FILE,
            bytes: artifact.len(),
            sha256: hex(&artifact_sha256),
            pairs_sha256: hex(&pair_sha256),
            format_version: ARTIFACT_VERSION,
            sections: section_metadata(&descriptors),
            e_rank_rows: certificate.e_rank.row_indices.clone(),
            e_rank_columns: certificate.e_rank.column_indices.clone(),
            f_rank_rows: certificate.f_rank.row_indices.clone(),
            f_rank_columns: certificate.f_rank.column_indices.clone(),
            joint_rank_rows: certificate.joint_rank.row_indices.clone(),
            joint_rank_columns: certificate.joint_rank.column_indices.clone(),
            left_null_pivots: certificate.left_null_pivots.clone(),
            a_pivots: certificate.a_pivots.clone(),
        },
        pair_provenance: pair_provenance(&certificate, &emat, &fmat)?,
        block_support: block_support(&certificate)?,
        equivalence: Equivalence {
            exact_statement: "For every released-view vector d in im(F), d is in F(ker E) iff q_i dot d = 0 for all i in 0..19.",
            annihilation_identity: "Each emitted pair satisfies q_i F = a_i E exactly, so every q_i annihilates F(ker E). The 19 A rows are independent and the Q rows are canonical modulo the explicit 122-row left-null(F) basis.",
            normalized_residual_reduction: "Conditional exact reduction: the 1023-coordinate C domain already parameterizes ker(ell). Therefore, if a normalized legal residual is represented by x in this same domain and also satisfies E x = 0, every obstruction vanishes automatically because q_i F x = a_i E x = 0. This certificate does not claim that the deployed residual has been defined, mapped to such an x, or proved to satisfy E x = 0.",
            dimension_argument: "Rank(E)=76, rank(F)=134, and rank([E;F])=191 give dim F(ker E)=115. QF=AE has rank 19, so ker(Q restricted to im(F)) has dimension 134-19=115. Containment plus equal dimension gives equality.",
            proof_status: "All identities, pivot-minor inverses, canonical quotient representatives, and dimension certificates are checked by exact Rust field arithmetic. A future Lean importer and Rust-to-Lean byte correspondence remain separate obligations.",
        },
        independent_cross_checks: IndependentCrossChecks {
            two_rank_algorithms_agree: true,
            tracked_and_transpose_left_null_bases_equal: true,
            residual_and_joint_pair_constructions_equal: true,
            all_pair_equations_exact: true,
            rank_minor_inverse_identities_exact: true,
            left_null_equations_exact: true,
            canonical_rref_and_quotient_representatives_checked: true,
        },
        remaining_blockers: vec![
            "No legal witness-difference or Delta map has been defined, so the certificate does not establish C-DEC or deployed hiding.",
            "The remaining protocol question is whether every genuine correlated residual difference annihilates these 19 exact quotient functionals.",
            "Rust-to-Lean E/F/certificate byte correspondences and a kernel check of the certificate remain explicit interfaces.",
            "A deployed sampler on the ultimately chosen legal mask space and its transcript/entropy binding are not implemented.",
            "No verifier, proof serialization, SBF binary, devnet, or mainnet path consumes this certificate.",
        ],
    };
    let manifest_path = results_dir.join(MANIFEST_FILE);
    fs::write(
        &manifest_path,
        format!("{}\n", serde_json::to_string_pretty(&document)?),
    )
    .with_context(|| format!("write {}", manifest_path.display()))?;
    Ok(V5ComponentCObstructionOutcome {
        artifact_path,
        manifest_path,
        artifact_bytes: artifact.len(),
        artifact_sha256: hex(&artifact_sha256),
        pair_sha256: hex(&pair_sha256),
        total_ms: elapsed_ms(total_start),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frozen_obstruction_certificate_is_exact_canonical_and_has_teeth() {
        let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../results/spend");
        let nonce = format!(
            "aspis-v5-c-obstruction-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        );
        let destination = std::env::temp_dir().join(nonce);
        if destination.exists() {
            fs::remove_dir_all(&destination).unwrap();
        }
        fs::create_dir_all(&destination).unwrap();
        for file in [EMAT_ARTIFACT_FILE, FMAT_ARTIFACT_FILE] {
            fs::copy(source.join(file), destination.join(file)).unwrap();
        }
        let first = run(&destination).unwrap();
        let first_bytes = fs::read(&first.artifact_path).unwrap();
        let second = run(&destination).unwrap();
        let second_bytes = fs::read(&second.artifact_path).unwrap();
        assert_eq!(first.artifact_sha256, second.artifact_sha256);
        assert_eq!(first.pair_sha256, second.pair_sha256);
        assert_eq!(first_bytes, second_bytes);
        fs::remove_dir_all(destination).unwrap();
    }
}
