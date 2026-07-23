//! Exact offline rank diagnostic for the frozen Component-C maps.
//!
//! This is computational audit evidence, not a Lean theorem and not a
//! deployed hiding claim. It consumes canonical Emat/Fmat artifacts and, when
//! the vertical stack has full row rank, emits a deterministic pivot-minor
//! inverse certificate. Nothing here enters a verifier, proof, or SBF binary.

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

const EMAT_ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_emat.bin";
const FMAT_ARTIFACT_FILE: &str = "v5_component_c_frozen_q18_fmat.bin";
const CERTIFICATE_FILE: &str = "v5_component_c_frozen_q18_joint_right_inverse.bin";
const MANIFEST_FILE: &str = "v5_component_c_frozen_q18_joint_rank.json";

const JOINT_ROWS: usize = V5_C_EMAT_ROWS + V5_C_FMAT_ROWS;
const JOINT_COLUMNS: usize = V5_C_EMAT_COLUMNS;
const CERTIFICATE_MAGIC: [u8; 8] = *b"AV5JRI01";
const CERTIFICATE_VERSION: u16 = 1;
const CERTIFICATE_FLAGS: u16 = 0;
const CERTIFICATE_HEADER_BYTES: usize = 192;
const PIVOT_BYTES: usize = JOINT_ROWS * 4;
const INVERSE_ENTRIES: usize = JOINT_ROWS * JOINT_ROWS;
const INVERSE_BYTES: usize = INVERSE_ENTRIES * V5_C_EMAT_QM31_BYTES;
const CERTIFICATE_BYTES: usize = CERTIFICATE_HEADER_BYTES + PIVOT_BYTES + INVERSE_BYTES;

const PIVOT_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-joint-pivots-v1";
const INVERSE_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-joint-inverse-v1";
const STACK_HASH_DOMAIN: &[u8] = b"aspis-v5-component-c-joint-matrix-v1";

const _: () = assert!(V5_C_EMAT_COLUMNS == V5_C_FMAT_COLUMNS);
const _: () = assert!(JOINT_ROWS == 332);
const _: () = assert!(JOINT_COLUMNS == 1023);
const _: () = assert!(INVERSE_ENTRIES == 110_224);
const _: () = assert!(INVERSE_BYTES == 1_763_584);
const _: () = assert!(CERTIFICATE_BYTES == 1_765_104);

#[derive(Clone, Debug)]
pub struct V5ComponentCRankOutcome {
    pub manifest_path: PathBuf,
    pub certificate_path: Option<PathBuf>,
    pub emat_rank: usize,
    pub fmat_rank: usize,
    pub joint_rank: usize,
    pub certificate_sha256: Option<String>,
    pub total_ms: u64,
}

#[derive(Serialize)]
struct RankManifest {
    schema: &'static str,
    version: u32,
    status: &'static str,
    scope: Scope,
    reproducible_command: &'static str,
    inputs: Inputs,
    exact_qm31_ranks: ExactRanks,
    exact_row_block_provenance: Vec<RowBlockRank>,
    implication: Implication,
    certificate: Option<CertificateMetadata>,
    benchmark_policy: &'static str,
    remaining_blockers: Vec<&'static str>,
}

#[derive(Serialize)]
struct Scope {
    diagnostic_only: bool,
    lean_theorem_claimed: bool,
    deployed_hiding_claimed: bool,
    delta_or_legal_difference_defined: bool,
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
    stacked_matrix_sha256: String,
    field: &'static str,
}

#[derive(Serialize)]
struct ExactRanks {
    emat_shape: [usize; 2],
    emat_rank: usize,
    emat_row_deficiency: usize,
    fmat_shape: [usize; 2],
    fmat_rank: usize,
    fmat_row_deficiency: usize,
    stacked_shape: [usize; 2],
    stacked_rank: usize,
    stacked_row_deficiency: usize,
    f_restricted_to_ker_e_rank: usize,
    f_restricted_to_ker_e_codomain_deficiency: usize,
    independent_elimination_agreement: bool,
}

#[derive(Serialize)]
struct RowBlockRank {
    name: &'static str,
    f_row_range: [usize; 2],
    block_rank: usize,
    f_prefix_rank: usize,
    f_prefix_rank_increment: usize,
    stacked_after_e_prefix_rank: usize,
    stacked_after_e_rank_increment: usize,
    row_space_intersection_with_e_dimension: usize,
}

#[derive(Serialize)]
struct Implication {
    condition_met: bool,
    statement: &'static str,
    proof_status: &'static str,
}

#[derive(Serialize)]
struct CertificateMetadata {
    file: &'static str,
    format_version: u16,
    bytes: usize,
    sha256: String,
    pivot_count: usize,
    pivot_columns_sha256: String,
    inverse_sha256: String,
    identity_checked: &'static str,
    right_inverse_storage: &'static str,
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

pub(crate) fn decode_matrix(bytes: &[u8], rows: usize, columns: usize) -> Result<Vec<QM31>> {
    let expected = rows
        .checked_mul(columns)
        .and_then(|entries| entries.checked_mul(V5_C_EMAT_QM31_BYTES))
        .ok_or_else(|| anyhow!("matrix shape overflow"))?;
    ensure!(bytes.len() == expected, "matrix byte length drift");
    bytes
        .chunks_exact(V5_C_EMAT_QM31_BYTES)
        .enumerate()
        .map(|(index, encoded)| {
            QM31::from_le_bytes(encoded)
                .ok_or_else(|| anyhow!("non-canonical matrix entry {index}"))
        })
        .collect()
}

/// Deterministic Gaussian elimination over exact QM31 arithmetic. Pivot
/// columns are returned in strictly increasing order.
pub(crate) fn exact_row_rank_and_pivots(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
) -> Result<(usize, Vec<usize>)> {
    ensure!(matrix.len() == rows * columns, "rank matrix shape drift");
    let mut work = matrix.to_vec();
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
        }
        let pivot_inverse = work[rank * columns + column].inv();
        for row in rank + 1..rows {
            let scale = work[row * columns + column].mul(pivot_inverse);
            if scale.is_zero() {
                continue;
            }
            work[row * columns + column] = QM31::ZERO;
            for index in column + 1..columns {
                let pivot_value = work[rank * columns + index];
                let position = row * columns + index;
                work[position] = work[position].sub(scale.mul(pivot_value));
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

/// Independent exact cross-check which incrementally maintains a normalized,
/// pivot-sorted basis of the row span.
pub(crate) fn exact_row_basis_rank_and_pivots(
    matrix: &[QM31],
    rows: usize,
    columns: usize,
) -> Result<(usize, Vec<usize>)> {
    ensure!(matrix.len() == rows * columns, "basis matrix shape drift");
    let mut basis: Vec<(usize, Vec<QM31>)> = Vec::with_capacity(rows);
    for source in matrix.chunks_exact(columns) {
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
    }
    Ok((
        basis.len(),
        basis.into_iter().map(|(pivot, _)| pivot).collect(),
    ))
}

fn exact_row_block_provenance(
    emat: &[QM31],
    fmat: &[QM31],
    emat_rank: usize,
) -> Result<Vec<RowBlockRank>> {
    let blocks = [
        ("relation OOD and sumcheck rows", 0usize, 36usize),
        ("authenticated later layer 1", 36, 108),
        ("authenticated later layer 2", 108, 180),
        ("authenticated later layer 3", 180, 252),
        ("final coefficients", 252, 256),
    ];
    let mut output = Vec::with_capacity(blocks.len());
    let mut previous_f_prefix = 0usize;
    let mut previous_stacked = emat_rank;
    for (name, start, end) in blocks {
        let (block_rank, _) = exact_row_rank_and_pivots(
            &fmat[start * JOINT_COLUMNS..end * JOINT_COLUMNS],
            end - start,
            JOINT_COLUMNS,
        )?;
        let (f_prefix_rank, _) =
            exact_row_rank_and_pivots(&fmat[..end * JOINT_COLUMNS], end, JOINT_COLUMNS)?;
        let mut stacked = Vec::with_capacity((V5_C_EMAT_ROWS + end) * JOINT_COLUMNS);
        stacked.extend_from_slice(emat);
        stacked.extend_from_slice(&fmat[..end * JOINT_COLUMNS]);
        let (stacked_rank, _) =
            exact_row_rank_and_pivots(&stacked, V5_C_EMAT_ROWS + end, JOINT_COLUMNS)?;
        output.push(RowBlockRank {
            name,
            f_row_range: [start, end],
            block_rank,
            f_prefix_rank,
            f_prefix_rank_increment: f_prefix_rank - previous_f_prefix,
            stacked_after_e_prefix_rank: stacked_rank,
            stacked_after_e_rank_increment: stacked_rank - previous_stacked,
            row_space_intersection_with_e_dimension: emat_rank + f_prefix_rank - stacked_rank,
        });
        previous_f_prefix = f_prefix_rank;
        previous_stacked = stacked_rank;
    }
    Ok(output)
}

fn pivot_minor(joint: &[QM31], pivot_columns: &[usize]) -> Result<Vec<QM31>> {
    ensure!(
        joint.len() == JOINT_ROWS * JOINT_COLUMNS && pivot_columns.len() == JOINT_ROWS,
        "pivot minor shape drift"
    );
    ensure!(
        pivot_columns.windows(2).all(|pair| pair[0] < pair[1])
            && pivot_columns.iter().all(|&column| column < JOINT_COLUMNS),
        "pivot columns are not canonical"
    );
    Ok((0..JOINT_ROWS)
        .flat_map(|row| {
            pivot_columns
                .iter()
                .map(move |&column| joint[row * JOINT_COLUMNS + column])
        })
        .collect())
}

pub(crate) fn invert_square(matrix: &[QM31], size: usize) -> Result<Vec<QM31>> {
    ensure!(matrix.len() == size * size, "inverse matrix shape drift");
    let mut left = matrix.to_vec();
    let mut right = vec![QM31::ZERO; size * size];
    for index in 0..size {
        right[index * size + index] = QM31::ONE;
    }
    for column in 0..size {
        let pivot = (column..size)
            .find(|&row| !left[row * size + column].is_zero())
            .ok_or_else(|| anyhow!("selected pivot minor is singular at column {column}"))?;
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
            left[row * size + column] = QM31::ZERO;
            for index in column + 1..size {
                let position = row * size + index;
                left[position] = left[position].sub(scale.mul(left[column * size + index]));
            }
            for index in 0..size {
                let position = row * size + index;
                right[position] = right[position].sub(scale.mul(right[column * size + index]));
            }
        }
    }
    Ok(right)
}

/// Independently multiply the original pivot minor by the emitted inverse.
pub(crate) fn verify_right_inverse_identity(
    minor: &[QM31],
    inverse: &[QM31],
    size: usize,
) -> Result<()> {
    ensure!(
        minor.len() == size * size && inverse.len() == size * size,
        "identity-check shape drift"
    );
    for row in 0..size {
        for column in 0..size {
            let actual = (0..size).fold(QM31::ZERO, |sum, inner| {
                sum.add(minor[row * size + inner].mul(inverse[inner * size + column]))
            });
            let expected = if row == column { QM31::ONE } else { QM31::ZERO };
            ensure!(
                actual == expected,
                "right-inverse identity failed at ({row}, {column})"
            );
        }
    }
    Ok(())
}

fn encode_pivots(pivots: &[usize]) -> Result<Vec<u8>> {
    ensure!(pivots.len() == JOINT_ROWS, "pivot count drift");
    let mut bytes = Vec::with_capacity(PIVOT_BYTES);
    for &pivot in pivots {
        bytes.extend_from_slice(
            &u32::try_from(pivot)
                .map_err(|_| anyhow!("pivot out of u32 range"))?
                .to_le_bytes(),
        );
    }
    Ok(bytes)
}

fn encode_inverse(inverse: &[QM31]) -> Result<Vec<u8>> {
    ensure!(
        inverse.len() == INVERSE_ENTRIES,
        "inverse entry count drift"
    );
    let mut bytes = vec![0u8; INVERSE_BYTES];
    for (index, value) in inverse.iter().copied().enumerate() {
        value.write_le_bytes(
            &mut bytes[index * V5_C_EMAT_QM31_BYTES..(index + 1) * V5_C_EMAT_QM31_BYTES],
        );
    }
    Ok(bytes)
}

fn encode_certificate(
    pivots: &[usize],
    inverse: &[QM31],
    emat_sha256: [u8; 32],
    fmat_sha256: [u8; 32],
) -> Result<Vec<u8>> {
    let pivot_bytes = encode_pivots(pivots)?;
    let inverse_bytes = encode_inverse(inverse)?;
    let mut output = vec![0u8; CERTIFICATE_HEADER_BYTES];
    output[0..8].copy_from_slice(&CERTIFICATE_MAGIC);
    output[8..10].copy_from_slice(&CERTIFICATE_VERSION.to_le_bytes());
    output[10..12].copy_from_slice(&CERTIFICATE_FLAGS.to_le_bytes());
    output[12..16].copy_from_slice(&(CERTIFICATE_HEADER_BYTES as u32).to_le_bytes());
    output[16..20].copy_from_slice(&(JOINT_ROWS as u32).to_le_bytes());
    output[20..24].copy_from_slice(&(JOINT_COLUMNS as u32).to_le_bytes());
    output[24..28].copy_from_slice(&(V5_C_EMAT_ROWS as u32).to_le_bytes());
    output[28..32].copy_from_slice(&(V5_C_FMAT_ROWS as u32).to_le_bytes());
    output[32..36].copy_from_slice(&(JOINT_ROWS as u32).to_le_bytes());
    output[36..40].copy_from_slice(&P.to_le_bytes());
    output[40..44].copy_from_slice(&(V5_C_EMAT_QM31_BYTES as u32).to_le_bytes());
    output[48..56].copy_from_slice(&(PIVOT_BYTES as u64).to_le_bytes());
    output[56..64].copy_from_slice(&(INVERSE_BYTES as u64).to_le_bytes());
    output[64..96].copy_from_slice(&emat_sha256);
    output[96..128].copy_from_slice(&fmat_sha256);
    output[128..160].copy_from_slice(&domain_hash(PIVOT_HASH_DOMAIN, &pivot_bytes));
    output[160..192].copy_from_slice(&domain_hash(INVERSE_HASH_DOMAIN, &inverse_bytes));
    output.extend_from_slice(&pivot_bytes);
    output.extend_from_slice(&inverse_bytes);
    debug_assert_eq!(output.len(), CERTIFICATE_BYTES);
    Ok(output)
}

struct CertificateView {
    pivots: Vec<usize>,
    inverse: Vec<QM31>,
    pivot_sha256: [u8; 32],
    inverse_sha256: [u8; 32],
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

fn validate_certificate(
    bytes: &[u8],
    emat_sha256: [u8; 32],
    fmat_sha256: [u8; 32],
) -> Result<CertificateView> {
    ensure!(
        bytes.len() == CERTIFICATE_BYTES
            && bytes.get(0..8) == Some(CERTIFICATE_MAGIC.as_slice())
            && read_u16(bytes, 8)? == CERTIFICATE_VERSION
            && read_u16(bytes, 10)? == CERTIFICATE_FLAGS
            && read_u32(bytes, 12)? as usize == CERTIFICATE_HEADER_BYTES
            && read_u32(bytes, 16)? as usize == JOINT_ROWS
            && read_u32(bytes, 20)? as usize == JOINT_COLUMNS
            && read_u32(bytes, 24)? as usize == V5_C_EMAT_ROWS
            && read_u32(bytes, 28)? as usize == V5_C_FMAT_ROWS
            && read_u32(bytes, 32)? as usize == JOINT_ROWS
            && read_u32(bytes, 36)? == P
            && read_u32(bytes, 40)? as usize == V5_C_EMAT_QM31_BYTES
            && bytes[44..48].iter().all(|&byte| byte == 0)
            && read_u64(bytes, 48)? as usize == PIVOT_BYTES
            && read_u64(bytes, 56)? as usize == INVERSE_BYTES
            && bytes[64..96] == emat_sha256
            && bytes[96..128] == fmat_sha256,
        "non-canonical rank certificate header"
    );
    let pivot_bytes = &bytes[CERTIFICATE_HEADER_BYTES..CERTIFICATE_HEADER_BYTES + PIVOT_BYTES];
    let inverse_bytes = &bytes[CERTIFICATE_HEADER_BYTES + PIVOT_BYTES..];
    let pivot_sha256: [u8; 32] = bytes[128..160].try_into()?;
    let inverse_sha256: [u8; 32] = bytes[160..192].try_into()?;
    ensure!(
        domain_hash(PIVOT_HASH_DOMAIN, pivot_bytes) == pivot_sha256
            && domain_hash(INVERSE_HASH_DOMAIN, inverse_bytes) == inverse_sha256,
        "rank certificate section hash mismatch"
    );
    let pivots = pivot_bytes
        .chunks_exact(4)
        .map(|encoded| u32::from_le_bytes(encoded.try_into().unwrap()) as usize)
        .collect::<Vec<_>>();
    ensure!(
        pivots.len() == JOINT_ROWS
            && pivots.windows(2).all(|pair| pair[0] < pair[1])
            && pivots.iter().all(|&pivot| pivot < JOINT_COLUMNS),
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
        "inverse entry count drift"
    );
    Ok(CertificateView {
        pivots,
        inverse,
        pivot_sha256,
        inverse_sha256,
    })
}

pub fn run(results_dir: &Path) -> Result<V5ComponentCRankOutcome> {
    let total_start = Instant::now();
    let emat_path = results_dir.join(EMAT_ARTIFACT_FILE);
    let fmat_path = results_dir.join(FMAT_ARTIFACT_FILE);
    let emat_bytes =
        fs::read(&emat_path).with_context(|| format!("read {}", emat_path.display()))?;
    let fmat_bytes =
        fs::read(&fmat_path).with_context(|| format!("read {}", fmat_path.display()))?;
    let emat_raw_sha256 = sha256(&emat_bytes);
    let fmat_raw_sha256 = sha256(&fmat_bytes);
    let emat_view = validate_component_c_emat_artifact(&emat_bytes)
        .context("validate canonical Emat artifact")?;
    let fmat_view = validate_component_c_fmat_artifact(&fmat_bytes)
        .context("validate canonical Fmat artifact")?;
    let emat = decode_matrix(emat_view.matrix_bytes, V5_C_EMAT_ROWS, JOINT_COLUMNS)?;
    let fmat = decode_matrix(fmat_view.matrix_bytes, V5_C_FMAT_ROWS, JOINT_COLUMNS)?;
    let mut joint = Vec::with_capacity(JOINT_ROWS * JOINT_COLUMNS);
    joint.extend_from_slice(&emat);
    joint.extend_from_slice(&fmat);

    let (emat_rank, _) = exact_row_rank_and_pivots(&emat, V5_C_EMAT_ROWS, JOINT_COLUMNS)
        .context("exact Emat QM31 rank")?;
    let (fmat_rank, _) = exact_row_rank_and_pivots(&fmat, V5_C_FMAT_ROWS, JOINT_COLUMNS)
        .context("exact Fmat QM31 rank")?;
    let (joint_rank, joint_pivots) = exact_row_rank_and_pivots(&joint, JOINT_ROWS, JOINT_COLUMNS)
        .context("exact stacked QM31 rank")?;
    let emat_reference = exact_row_basis_rank_and_pivots(&emat, V5_C_EMAT_ROWS, JOINT_COLUMNS)
        .context("independent exact Emat QM31 rank")?;
    let fmat_reference = exact_row_basis_rank_and_pivots(&fmat, V5_C_FMAT_ROWS, JOINT_COLUMNS)
        .context("independent exact Fmat QM31 rank")?;
    let joint_reference = exact_row_basis_rank_and_pivots(&joint, JOINT_ROWS, JOINT_COLUMNS)
        .context("independent exact stacked QM31 rank")?;
    ensure!(
        emat_reference.0 == emat_rank
            && fmat_reference.0 == fmat_rank
            && joint_reference.0 == joint_rank
            && joint_reference.1 == joint_pivots,
        "independent exact rank algorithms disagree"
    );
    let row_block_provenance = exact_row_block_provenance(&emat, &fmat, emat_rank)
        .context("exact Fmat row-block provenance")?;
    ensure!(
        row_block_provenance.last().is_some_and(|block| {
            block.f_prefix_rank == fmat_rank
                && block.stacked_after_e_prefix_rank == joint_rank
                && block.row_space_intersection_with_e_dimension
                    == emat_rank + fmat_rank - joint_rank
        }),
        "row-block provenance did not recover the full ranks"
    );
    let condition_met =
        emat_rank == V5_C_EMAT_ROWS && fmat_rank == V5_C_FMAT_ROWS && joint_rank == JOINT_ROWS;

    fs::create_dir_all(results_dir).context("create Component-C result directory")?;
    let certificate_path = results_dir.join(CERTIFICATE_FILE);
    let (certificate_metadata, certificate_sha256) = if condition_met {
        let minor = pivot_minor(&joint, &joint_pivots)?;
        let inverse = invert_square(&minor, JOINT_ROWS)
            .context("invert deterministic stacked pivot minor")?;
        verify_right_inverse_identity(&minor, &inverse, JOINT_ROWS)
            .context("independently verify J * sparse_right_inverse = I_332")?;
        let certificate =
            encode_certificate(&joint_pivots, &inverse, emat_raw_sha256, fmat_raw_sha256)?;
        let decoded = validate_certificate(&certificate, emat_raw_sha256, fmat_raw_sha256)
            .context("self-validate joint rank certificate")?;
        ensure!(
            decoded.pivots == joint_pivots && decoded.inverse == inverse,
            "rank certificate round-trip drift"
        );
        let decoded_minor = pivot_minor(&joint, &decoded.pivots)?;
        verify_right_inverse_identity(&decoded_minor, &decoded.inverse, JOINT_ROWS)
            .context("verify identity from decoded certificate")?;
        fs::write(&certificate_path, &certificate)
            .with_context(|| format!("write {}", certificate_path.display()))?;
        let raw_sha256 = sha256(&certificate);
        (
            Some(CertificateMetadata {
                file: CERTIFICATE_FILE,
                format_version: CERTIFICATE_VERSION,
                bytes: certificate.len(),
                sha256: hex(&raw_sha256),
                pivot_count: decoded.pivots.len(),
                pivot_columns_sha256: hex(&decoded.pivot_sha256),
                inverse_sha256: hex(&decoded.inverse_sha256),
                identity_checked: "exact QM31 multiplication of original 332x332 pivot minor by decoded inverse equals I_332",
                right_inverse_storage: "332 pivot-column indices plus row-major inverse; all 691 non-pivot rows of the conceptual 1023x332 right inverse are zero",
            }),
            Some(hex(&raw_sha256)),
        )
    } else {
        if certificate_path.exists() {
            fs::remove_file(&certificate_path).with_context(|| {
                format!(
                    "remove stale full-rank certificate {}",
                    certificate_path.display()
                )
            })?;
        }
        (None, None)
    };

    let mut stacked_bytes =
        Vec::with_capacity(emat_view.matrix_bytes.len() + fmat_view.matrix_bytes.len());
    stacked_bytes.extend_from_slice(emat_view.matrix_bytes);
    stacked_bytes.extend_from_slice(fmat_view.matrix_bytes);
    let document = RankManifest {
        schema: "aspis-v5-component-c-joint-rank-diagnostic",
        version: 1,
        status: "exact computational audit evidence; not a Lean theorem or deployed Component-C hiding claim",
        scope: Scope {
            diagnostic_only: true,
            lean_theorem_claimed: false,
            deployed_hiding_claimed: false,
            delta_or_legal_difference_defined: false,
            verifier_wire_changed: false,
            production_or_sbf_inclusion: false,
        },
        reproducible_command:
            "NO_DNA=1 cargo run -p aspis-xtask --bin aspis-xtask --release -- v5-component-c-rank",
        inputs: Inputs {
            emat_file: EMAT_ARTIFACT_FILE,
            emat_artifact_sha256: hex(&emat_raw_sha256),
            emat_matrix_sha256: hex(&emat_view.matrix_sha256),
            fmat_file: FMAT_ARTIFACT_FILE,
            fmat_artifact_sha256: hex(&fmat_raw_sha256),
            fmat_matrix_sha256: hex(&fmat_view.matrix_sha256),
            stacked_matrix_sha256: hex(&domain_hash(STACK_HASH_DOMAIN, &stacked_bytes)),
            field: "exact QM31 arithmetic over p = 2^31 - 1",
        },
        exact_qm31_ranks: ExactRanks {
            emat_shape: [V5_C_EMAT_ROWS, JOINT_COLUMNS],
            emat_rank,
            emat_row_deficiency: V5_C_EMAT_ROWS - emat_rank,
            fmat_shape: [V5_C_FMAT_ROWS, JOINT_COLUMNS],
            fmat_rank,
            fmat_row_deficiency: V5_C_FMAT_ROWS - fmat_rank,
            stacked_shape: [JOINT_ROWS, JOINT_COLUMNS],
            stacked_rank: joint_rank,
            stacked_row_deficiency: JOINT_ROWS - joint_rank,
            f_restricted_to_ker_e_rank: joint_rank - emat_rank,
            f_restricted_to_ker_e_codomain_deficiency: V5_C_FMAT_ROWS
                - (joint_rank - emat_rank),
            independent_elimination_agreement: true,
        },
        exact_row_block_provenance: row_block_provenance,
        implication: Implication {
            condition_met,
            statement: "If rank(E)=76 and rank([E;F])=332, then the intrinsic map F restricted to ker(E) is surjective onto QM31^256; this algebraic route does not require choosing a Delta parameterization.",
            proof_status: if condition_met {
                "The ranks and right-inverse identity are exact deterministic Rust computations. Importing the certificate into Lean and binding its bytes to the deployed Rust maps remain separate obligations."
            } else {
                "Two independent exact QM31 elimination implementations agree that the full-row-rank condition is false. No right-inverse certificate was emitted; these are computational audit results, not a Lean theorem."
            },
        },
        certificate: certificate_metadata,
        benchmark_policy:
            "wall-clock timings are excluded from this deterministic manifest and printed by the diagnostic",
        remaining_blockers: if condition_met {
            vec![
                "The exact rank certificate has not yet been imported and kernel-checked in Lean.",
                "Rust-to-Lean EMatrixFaithful and FMatrixFaithful byte/hash correspondences remain explicit review interfaces.",
                "A deployed sampler uniform on ker(E), and its transcript/entropy binding, are not implemented.",
                "No verifier, proof serialization, SBF binary, devnet, or mainnet path consumes these artifacts.",
            ]
        } else {
            vec![
                "Full-view surjectivity is false on this frozen schedule: F restricted to ker(E) has rank 115, not 256.",
                "A legal-difference/Delta parameterization or an explicitly reduced correlated target is still required to instantiate C-DEC; no such deployed object exists.",
                "Rust-to-Lean EMatrixFaithful and FMatrixFaithful byte/hash correspondences remain explicit review interfaces.",
                "A deployed sampler uniform on the chosen legal mask space, and its transcript/entropy binding, are not implemented.",
                "No verifier, proof serialization, SBF binary, devnet, or mainnet path consumes these artifacts.",
            ]
        },
    };
    let manifest_path = results_dir.join(MANIFEST_FILE);
    fs::write(
        &manifest_path,
        format!("{}\n", serde_json::to_string_pretty(&document)?),
    )
    .with_context(|| format!("write {}", manifest_path.display()))?;

    Ok(V5ComponentCRankOutcome {
        manifest_path,
        certificate_path: condition_met.then_some(certificate_path),
        emat_rank,
        fmat_rank,
        joint_rank,
        certificate_sha256,
        total_ms: elapsed_ms(total_start),
    })
}
