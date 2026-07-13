use aspis_core::circle::secure_ood_circle_point_from_parameter;
use aspis_core::circle_line_merkle::derive_circle_line_query_indices_for_count;
use aspis_core::circle_prefix::{CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT};
use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::state_only_hiding::{
    state_only_c1_mask_factor, state_only_explicit_g_mask_factor,
    state_only_hiding_layout_factor_fingerprint, state_only_mask_only_c1_factor,
    PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT, STATE_ONLY_HIDING_C1_RAW_M31_OBSERVATIONS,
    STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS, STATE_ONLY_HIDING_H1_GENERATOR_INDEX,
    STATE_ONLY_HIDING_QUERY_COUNT, STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS,
    STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
};
use aspis_prover::circle_candidate::{build_fold_commitments_for_domain_log, CircleEncoder};
use aspis_prover::state_only_circle_relation::StateOnlyIncrementalRelation;
use aspis_prover::HOST_HASH;
use aspis_statement::{
    binary_successor_point, build_spend_trace_v4, build_state_only_copy_helper_v4,
    derive_nullifier, derive_owner_key, merkle_root, note_commitment, output_commitment,
    project_state_only_trace_v4, state_only_copy_layout_v4, state_only_relation_free_mask_cells_v4,
    state_only_relation_free_mask_fingerprint_v4, state_only_semantic_openings_at_point,
    xor12_point, Digest, MerklePath, SpendPublic, SpendWitness, TupleLimb,
    PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT,
};

const RATE16_DOMAIN_LOG: u32 = 14;
const TRACE_ROWS: usize = 1 << STATE_ONLY_HIDING_SUMCHECK_ROUNDS;
const FIBER_SLOTS: usize = 4;
const SUMCHECK_DEGREE: usize = 27;
const SUMCHECK_COEFFICIENTS: usize = SUMCHECK_DEGREE + 1;
const EXPLICIT_G_ROWS: usize = 512;

#[derive(Clone, Copy)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545_f491_4f6c_dd1d);
        self.0
    }

    fn m31(&mut self) -> M31 {
        M31((self.next() % u64::from(P)) as u32)
    }

    fn qm31(&mut self) -> QM31 {
        QM31 {
            c0: CM31::new(self.m31(), self.m31()),
            c1: CM31::new(self.m31(), self.m31()),
        }
    }
}

fn eq_weight(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS], row: usize) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ONE, |weight, (coordinate, value)| {
            let bit = (row >> (point.len() - 1 - coordinate)) & 1;
            weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            })
        })
}

fn distinct_queries<const Q: usize>(rng: &mut Rng, domain_log: u32) -> [usize; Q] {
    let mut queries = [0usize; Q];
    let mut count = 0;
    while count < queries.len() {
        let candidate = (rng.next() as usize) & ((1usize << (domain_log - 2)) - 1);
        if !queries[..count].contains(&candidate) {
            queries[count] = candidate;
            count += 1;
        }
    }
    queries
}

fn rank_qm31(mut matrix: Vec<Vec<QM31>>) -> usize {
    let rows = matrix.len();
    let columns = matrix.first().map_or(0, Vec::len);
    let mut rank = 0;
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| matrix[row][column] != QM31::ZERO) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = matrix[rank][column].try_inv().unwrap();
        for value in &mut matrix[rank][column..] {
            *value = inverse.mul(*value);
        }
        let pivot_tail = matrix[rank][column..].to_vec();
        for row in 0..rows {
            if row == rank || matrix[row][column] == QM31::ZERO {
                continue;
            }
            let scale = matrix[row][column];
            for (value, pivot_value) in matrix[row][column..].iter_mut().zip(&pivot_tail) {
                *value = value.sub(scale.mul(*pivot_value));
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

fn rank_m31(mut matrix: Vec<Vec<M31>>) -> usize {
    let rows = matrix.len();
    let columns = matrix.first().map_or(0, Vec::len);
    let mut rank = 0;
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|&row| matrix[row][column] != M31::ZERO) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = matrix[rank][column].inv();
        for value in &mut matrix[rank][column..] {
            *value = value.mul(inverse);
        }
        let pivot_tail = matrix[rank][column..].to_vec();
        for row in 0..rows {
            if row == rank || matrix[row][column] == M31::ZERO {
                continue;
            }
            let scale = matrix[row][column];
            for (value, pivot_value) in matrix[row][column..].iter_mut().zip(&pivot_tail) {
                *value = value.sub(scale.mul(*pivot_value));
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

fn rank_m31_image_columns(images: &[Vec<M31>], outputs: usize) -> usize {
    let mut matrix = vec![vec![M31::ZERO; images.len()]; outputs];
    for (column, image) in images.iter().enumerate() {
        assert_eq!(image.len(), outputs);
        for (row, value) in image.iter().copied().enumerate() {
            matrix[row][column] = value;
        }
    }
    rank_m31(matrix)
}

fn rank_qm31_image_columns(images: &[Vec<QM31>], outputs: usize) -> usize {
    let mut matrix = vec![vec![QM31::ZERO; images.len()]; outputs];
    for (column, image) in images.iter().enumerate() {
        assert_eq!(image.len(), outputs);
        for (row, value) in image.iter().copied().enumerate() {
            matrix[row][column] = value;
        }
    }
    rank_qm31(matrix)
}

fn qm31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

fn lagrange_basis() -> [[M31; SUMCHECK_COEFFICIENTS]; SUMCHECK_COEFFICIENTS] {
    core::array::from_fn(|i| {
        let mut basis = [M31::ZERO; SUMCHECK_COEFFICIENTS];
        basis[0] = M31::ONE;
        let mut degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..SUMCHECK_COEFFICIENTS {
            if i == j {
                continue;
            }
            let root = M31(j as u32);
            let previous = basis;
            for coefficient in 0..=degree + 1 {
                let shifted = if coefficient == 0 {
                    M31::ZERO
                } else {
                    previous[coefficient - 1]
                };
                let constant = if coefficient <= degree {
                    previous[coefficient].mul(root)
                } else {
                    M31::ZERO
                };
                basis[coefficient] = shifted.sub(constant);
            }
            degree += 1;
            denominator = denominator.mul(M31(i as u32).sub(root));
        }
        let inverse = denominator.inv();
        for value in &mut basis {
            *value = value.mul(inverse);
        }
        basis
    })
}

fn interpolate(
    values: &[QM31; SUMCHECK_COEFFICIENTS],
    basis: &[[M31; SUMCHECK_COEFFICIENTS]; SUMCHECK_COEFFICIENTS],
) -> [QM31; SUMCHECK_COEFFICIENTS] {
    core::array::from_fn(|coefficient| {
        (0..SUMCHECK_COEFFICIENTS).fold(QM31::ZERO, |sum, sample| {
            sum.add(values[sample].mul_m31(basis[sample][coefficient]))
        })
    })
}

fn boundary_sum(polynomial: &[QM31; SUMCHECK_COEFFICIENTS]) -> QM31 {
    polynomial[0].add(polynomial.iter().copied().fold(QM31::ZERO, QM31::add))
}

fn evaluate(polynomial: &[QM31; SUMCHECK_COEFFICIENTS], point: QM31) -> QM31 {
    polynomial[..SUMCHECK_DEGREE]
        .iter()
        .rev()
        .copied()
        .fold(polynomial[SUMCHECK_DEGREE], |value, coefficient| {
            value.mul(point).add(coefficient)
        })
}

#[derive(Clone, Copy)]
enum FactorKind {
    C1(usize),
    ExplicitG,
    DiagnosticM31(usize),
    DiagnosticG(usize),
}

fn factor_at(kind: FactorKind, point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    match kind {
        FactorKind::C1(column) => state_only_c1_mask_factor(column, point),
        FactorKind::ExplicitG => state_only_explicit_g_mask_factor(point),
        FactorKind::DiagnosticM31(index) => state_only_mask_only_c1_factor(index, point),
        FactorKind::DiagnosticG(index) => {
            let linear = point
                .iter()
                .enumerate()
                .fold(QM31::ZERO, |sum, (variable, value)| {
                    sum.add(
                        value.mul_m31(M31((37 + 31 * index + (29 + 2 * index) * variable) as u32)),
                    )
                });
            let exponent = 16 + (index % 11);
            (0..exponent).fold(QM31::ONE, |power, _| power.mul(linear))
        }
    }
}

fn mask_sumcheck_observations(
    row: usize,
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    lagrange: &[[M31; SUMCHECK_COEFFICIENTS]; SUMCHECK_COEFFICIENTS],
    factor: FactorKind,
) -> Vec<QM31> {
    let boolean_point = core::array::from_fn(|coordinate| {
        let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
        if bit == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    });
    let mut prefix = [QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_ROUNDS];
    let mut running_claim = factor_at(factor, &boolean_point);
    let mut observations = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
    observations.push(running_claim);
    for round in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            for coordinate in round + 1..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
                let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                prefix[coordinate] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
            }
            eq_weight(&prefix, row).mul(factor_at(factor, &prefix))
        });
        let polynomial = interpolate(&samples, lagrange);
        assert_eq!(boundary_sum(&polynomial), running_claim);
        observations.push(polynomial[0]);
        observations.extend(polynomial[2..].iter().copied());
        running_claim = evaluate(&polynomial, challenges[round]);
        prefix[round] = challenges[round];
    }
    assert_eq!(
        observations.len(),
        STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
    );
    observations
}

fn encoded_query_samples<const Q: usize>(
    encoder: &CircleEncoder,
    row: usize,
    queries: &[usize; Q],
) -> Vec<M31> {
    let mut message = vec![M31::ZERO; TRACE_ROWS];
    message[row] = M31::ONE;
    let codeword = encoder.encode_c1_message(&message).unwrap();
    let mut samples = Vec::with_capacity(Q * FIBER_SLOTS);
    for &query in queries {
        for slot in 0..FIBER_SLOTS {
            samples.push(codeword[FIBER_SLOTS * query + slot]);
        }
    }
    samples
}

fn reduce_raw_view_and_collect_kernel_images(
    raw_columns: impl IntoIterator<Item = Vec<QM31>>,
    mask_columns: impl IntoIterator<Item = Vec<QM31>>,
    raw_outputs: usize,
) -> (usize, Vec<Vec<QM31>>) {
    let mut pivots: Vec<Option<(Vec<QM31>, Vec<QM31>)>> = vec![None; raw_outputs];
    let mut kernel_images = Vec::new();
    for (mut raw, mut mask) in raw_columns.into_iter().zip(mask_columns) {
        assert_eq!(raw.len(), raw_outputs);
        for pivot in 0..raw_outputs {
            if raw[pivot] == QM31::ZERO {
                continue;
            }
            if let Some((pivot_raw, pivot_mask)) = &pivots[pivot] {
                let scale = raw[pivot];
                for index in pivot..raw_outputs {
                    raw[index] = raw[index].sub(scale.mul(pivot_raw[index]));
                }
                for (value, pivot_value) in mask.iter_mut().zip(pivot_mask) {
                    *value = value.sub(scale.mul(*pivot_value));
                }
                continue;
            }
            let inverse = raw[pivot].try_inv().unwrap();
            for value in &mut raw[pivot..] {
                *value = value.mul(inverse);
            }
            for value in &mut mask {
                *value = value.mul(inverse);
            }
            pivots[pivot] = Some((core::mem::take(&mut raw), core::mem::take(&mut mask)));
            break;
        }
        if !raw.is_empty() {
            debug_assert!(raw.iter().all(|value| *value == QM31::ZERO));
            kernel_images.push(mask);
        }
    }
    (
        pivots.iter().filter(|pivot| pivot.is_some()).count(),
        kernel_images,
    )
}

fn reduce_m31_raw_view_and_collect_qm31_kernel_images(
    raw_columns: impl IntoIterator<Item = Vec<M31>>,
    mask_columns: impl IntoIterator<Item = Vec<QM31>>,
    raw_outputs: usize,
) -> (usize, Vec<Vec<QM31>>) {
    let mut pivots: Vec<Option<(Vec<M31>, Vec<QM31>)>> = vec![None; raw_outputs];
    let mut kernel_images = Vec::new();
    for (mut raw, mut mask) in raw_columns.into_iter().zip(mask_columns) {
        assert_eq!(raw.len(), raw_outputs);
        for pivot in 0..raw_outputs {
            if raw[pivot] == M31::ZERO {
                continue;
            }
            if let Some((pivot_raw, pivot_mask)) = &pivots[pivot] {
                let scale = raw[pivot];
                for index in pivot..raw_outputs {
                    raw[index] = raw[index].sub(scale.mul(pivot_raw[index]));
                }
                for (value, pivot_value) in mask.iter_mut().zip(pivot_mask) {
                    *value = value.sub(pivot_value.mul_m31(scale));
                }
                continue;
            }
            let inverse = raw[pivot].inv();
            for value in &mut raw[pivot..] {
                *value = value.mul(inverse);
            }
            for value in &mut mask {
                *value = value.mul_m31(inverse);
            }
            pivots[pivot] = Some((core::mem::take(&mut raw), core::mem::take(&mut mask)));
            break;
        }
        if !raw.is_empty() {
            debug_assert!(raw.iter().all(|value| *value == M31::ZERO));
            kernel_images.push(mask);
        }
    }
    (
        pivots.iter().filter(|pivot| pivot.is_some()).count(),
        kernel_images,
    )
}

#[test]
fn explicit_g_alone_is_not_mistaken_for_a_complete_sumcheck_mask() {
    assert_eq!(STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS, 147);
    assert_eq!(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS, 271);
    let lagrange = lagrange_basis();
    let encoder = CircleEncoder::new_for_domain_log(RATE16_DOMAIN_LOG);
    let rows = (0..EXPLICIT_G_ROWS)
        .map(|local| (local * 573 + 211) & (TRACE_ROWS - 1))
        .collect::<Vec<_>>();
    let mut rng = Rng(0x5354_4f4e_474d_4153);
    for schedule in 0..3 {
        let queries =
            distinct_queries::<STATE_ONLY_HIDING_QUERY_COUNT>(&mut rng, RATE16_DOMAIN_LOG);
        let challenges = core::array::from_fn(|_| rng.qm31());
        let z = challenges;
        let terminal_points = [z, binary_successor_point(&z), xor12_point(&z)];
        let mut raw_columns = Vec::with_capacity(rows.len());
        let mut mask_columns = Vec::with_capacity(rows.len());
        for &row in &rows {
            let mut raw = encoded_query_samples(&encoder, row, &queries)
                .into_iter()
                .map(|value| QM31::from_cm31(CM31::from_m31(value)))
                .collect::<Vec<_>>();
            for point in &terminal_points {
                raw.push(eq_weight(point, row));
            }
            raw_columns.push(raw);
            mask_columns.push(mask_sumcheck_observations(
                row,
                &challenges,
                &lagrange,
                FactorKind::ExplicitG,
            ));
        }
        let (raw_rank, kernel_images) = reduce_raw_view_and_collect_kernel_images(
            raw_columns,
            mask_columns,
            STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS,
        );
        assert_eq!(raw_rank, STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS);
        let mut conditioned = vec![
            vec![QM31::ZERO; kernel_images.len()];
            STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
        ];
        for (column, image) in kernel_images.into_iter().enumerate() {
            for (row, value) in image.into_iter().enumerate() {
                conditioned[row][column] = value;
            }
        }
        let conditioned_rank = rank_qm31(conditioned);
        std::eprintln!("explicit-G conditioned rank schedule {schedule}: {conditioned_rank}");
        assert!(
            conditioned_rank < STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS,
            "the negative one-mask guard unexpectedly passed for schedule {schedule}"
        );
    }
}

fn diagonal_ranks<const Q: usize>(
    domain_log: u32,
    schedules: usize,
    seed: u64,
    qm31_probe: bool,
) -> Vec<(Vec<usize>, Vec<usize>)> {
    // The public observation matrix is block triangular. Each C1 mask family
    // first surjects onto that column's 156-coordinate raw view. G separately
    // surjects onto its 147-QM31 raw view. We then retain only the kernels of
    // all those maps and require their combined image to cover all 1,084 M31
    // coordinates of the sumcheck view. These three checks are exactly the
    // rank of the complete concatenated raw+sumcheck observation matrix, but
    // avoid materializing its much larger zero-block structure.
    let cells = state_only_relation_free_mask_cells_v4().unwrap();
    let mut available = [[false; TRACE_ROWS]; 16];
    for cell in &cells {
        available[usize::from(cell.column)][usize::from(cell.row)] = true;
    }
    let selected_c1: [Vec<usize>; 16] = core::array::from_fn(|column| {
        (0..TRACE_ROWS)
            .filter(|row| available[column][*row])
            .collect()
    });
    assert!(selected_c1
        .iter()
        .all(|rows| rows.len() > STATE_ONLY_HIDING_C1_RAW_M31_OBSERVATIONS));

    let lagrange = lagrange_basis();
    let c1_raw_outputs = Q * FIBER_SLOTS + 4 * 3;
    let g_raw_outputs = Q * FIBER_SLOTS + 3;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let g_rows = (0..EXPLICIT_G_ROWS)
        .map(|local| (local * 573 + 211) & (TRACE_ROWS - 1))
        .collect::<Vec<_>>();
    let mut rng = Rng(seed);
    let mut schedule_ranks = Vec::with_capacity(schedules);
    for schedule in 0..schedules {
        let queries = distinct_queries::<Q>(&mut rng, domain_log);
        let challenges = core::array::from_fn(|_| rng.qm31());
        let z = challenges;
        let terminal_points = [z, binary_successor_point(&z), xor12_point(&z)];

        let mut needed = [false; TRACE_ROWS];
        for rows in &selected_c1 {
            for &row in rows {
                needed[row] = true;
            }
        }
        for &row in &g_rows {
            needed[row] = true;
        }
        // Candidate width-17 mask-only M31 column is a full-domain message.
        needed.fill(true);
        let mut encoded: [Option<Vec<M31>>; TRACE_ROWS] = core::array::from_fn(|_| None);
        for row in 0..TRACE_ROWS {
            if needed[row] {
                encoded[row] = Some(encoded_query_samples(&encoder, row, &queries));
            }
        }

        let mut m31_kernel_images = Vec::new();
        for column in 0..16usize {
            let raw_columns = selected_c1[column]
                .iter()
                .copied()
                .map(|row| {
                    let mut raw = encoded[row].as_ref().unwrap().clone();
                    for point in &terminal_points {
                        raw.extend(qm31_coordinates(eq_weight(point, row)));
                    }
                    raw
                })
                .collect::<Vec<_>>();
            let mask_columns = selected_c1[column]
                .iter()
                .copied()
                .map(|row| {
                    mask_sumcheck_observations(row, &challenges, &lagrange, FactorKind::C1(column))
                })
                .collect::<Vec<_>>();
            let (raw_rank, column_kernel) = reduce_m31_raw_view_and_collect_qm31_kernel_images(
                raw_columns,
                mask_columns,
                c1_raw_outputs,
            );
            assert_eq!(
                raw_rank, c1_raw_outputs,
                "C1 raw view deficient for schedule {schedule}, column {column}"
            );
            m31_kernel_images.extend(column_kernel.into_iter().map(|image| {
                image
                    .into_iter()
                    .flat_map(qm31_coordinates)
                    .collect::<Vec<_>>()
            }));
        }

        let mut raw_g = Vec::with_capacity(g_rows.len());
        let mut mask_g = Vec::with_capacity(g_rows.len());
        for &row in &g_rows {
            let mut raw = encoded[row]
                .as_ref()
                .unwrap()
                .iter()
                .copied()
                .map(|value| QM31::from_cm31(CM31::from_m31(value)))
                .collect::<Vec<_>>();
            for point in &terminal_points {
                raw.push(eq_weight(point, row));
            }
            raw_g.push(raw);
            mask_g.push(mask_sumcheck_observations(
                row,
                &challenges,
                &lagrange,
                FactorKind::ExplicitG,
            ));
        }
        let (g_raw_rank, g_kernel) =
            reduce_raw_view_and_collect_kernel_images(raw_g, mask_g, g_raw_outputs);
        assert_eq!(g_raw_rank, g_raw_outputs);
        for image in g_kernel {
            for coordinate in 0..4usize {
                let basis = aspis_core::state_only_hiding::state_only_mask_tower_basis(coordinate);
                m31_kernel_images.push(
                    image
                        .iter()
                        .copied()
                        .flat_map(|value| qm31_coordinates(basis.mul(value)))
                        .collect(),
                );
            }
        }

        let outputs = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
        let production_rank = rank_m31_image_columns(&m31_kernel_images, outputs);
        let mut ranks = vec![production_rank];
        let mut qm31_images = m31_kernel_images.clone();
        let mut qm31_ranks = vec![production_rank];
        for diagnostic in 0..if qm31_probe { 3 } else { 0 } {
            // One QM31 column is four independent M31 coordinate tables.
            // Give each coordinate its own public factor; a scalar L-linear
            // factor would add only four M31 ranks per oracle and is the
            // negative control this A/B is intended to avoid.
            let mut raw_extra = Vec::with_capacity(4 * TRACE_ROWS);
            let mut mask_extra = Vec::with_capacity(4 * TRACE_ROWS);
            for coordinate in 0..4usize {
                let basis = aspis_core::state_only_hiding::state_only_mask_tower_basis(coordinate);
                for row in 0..TRACE_ROWS {
                    let mut raw = encoded[row]
                        .as_ref()
                        .unwrap()
                        .iter()
                        .copied()
                        .flat_map(|value| qm31_coordinates(basis.mul_m31(value)))
                        .collect::<Vec<_>>();
                    for point in &terminal_points {
                        raw.extend(qm31_coordinates(basis.mul(eq_weight(point, row))));
                    }
                    raw_extra.push(raw);
                    mask_extra.push(mask_sumcheck_observations(
                        row,
                        &challenges,
                        &lagrange,
                        FactorKind::DiagnosticG(4 * diagnostic + coordinate),
                    ));
                }
            }
            let (extra_raw_rank, extra_kernel) = reduce_m31_raw_view_and_collect_qm31_kernel_images(
                raw_extra,
                mask_extra,
                4 * g_raw_outputs,
            );
            assert_eq!(extra_raw_rank, 4 * g_raw_outputs);
            qm31_images.extend(extra_kernel.into_iter().map(|image| {
                image
                    .into_iter()
                    .flat_map(qm31_coordinates)
                    .collect::<Vec<_>>()
            }));
            qm31_ranks.push(rank_m31_image_columns(&qm31_images, outputs));
        }

        let mut raw_m31 = Vec::with_capacity(TRACE_ROWS);
        let mut mask_m31 = Vec::with_capacity(TRACE_ROWS);
        for row in 0..TRACE_ROWS {
            let mut raw = encoded[row].as_ref().unwrap().clone();
            for point in &terminal_points {
                raw.extend(qm31_coordinates(eq_weight(point, row)));
            }
            raw_m31.push(raw);
            mask_m31.push(mask_sumcheck_observations(
                row,
                &challenges,
                &lagrange,
                FactorKind::DiagnosticM31(0),
            ));
        }
        let (m31_raw_rank, m31_kernel) =
            reduce_m31_raw_view_and_collect_qm31_kernel_images(raw_m31, mask_m31, c1_raw_outputs);
        assert_eq!(m31_raw_rank, c1_raw_outputs);
        m31_kernel_images.extend(m31_kernel.into_iter().map(|image| {
            image
                .into_iter()
                .flat_map(qm31_coordinates)
                .collect::<Vec<_>>()
        }));
        let one_m31_rank = rank_m31_image_columns(&m31_kernel_images, outputs);
        ranks.push(one_m31_rank);

        for extra_column in 1..10usize {
            let mut raw_extra = Vec::with_capacity(TRACE_ROWS);
            let mut mask_extra = Vec::with_capacity(TRACE_ROWS);
            for row in 0..TRACE_ROWS {
                let mut raw = encoded[row].as_ref().unwrap().clone();
                for point in &terminal_points {
                    raw.extend(qm31_coordinates(eq_weight(point, row)));
                }
                raw_extra.push(raw);
                mask_extra.push(mask_sumcheck_observations(
                    row,
                    &challenges,
                    &lagrange,
                    FactorKind::DiagnosticM31(extra_column),
                ));
            }
            let (extra_raw_rank, extra_kernel) = reduce_m31_raw_view_and_collect_qm31_kernel_images(
                raw_extra,
                mask_extra,
                c1_raw_outputs,
            );
            assert_eq!(extra_raw_rank, c1_raw_outputs);
            m31_kernel_images.extend(extra_kernel.into_iter().map(|image| {
                image
                    .into_iter()
                    .flat_map(qm31_coordinates)
                    .collect::<Vec<_>>()
            }));
            ranks.push(rank_m31_image_columns(&m31_kernel_images, outputs));
        }

        assert_eq!(ranks.len(), 11);
        std::eprintln!(
            "diagonal ranks q={Q} domain_log={domain_log} schedule={schedule}: m31={ranks:?} qm31={qm31_ranks:?}"
        );
        schedule_ranks.push((ranks, qm31_ranks));
    }
    schedule_ranks
}

#[test]
fn production_diagonal_has_a_rank_deficit_and_ten_extra_sources_reach_the_quotient() {
    for (schedule, (ranks, _)) in diagonal_ranks::<STATE_ONLY_HIDING_QUERY_COUNT>(
        RATE16_DOMAIN_LOG,
        3,
        0x5354_4f4e_434f_4d42,
        false,
    )
    .into_iter()
    .enumerate()
    {
        assert_eq!(ranks[0], 1_040, "schedule {schedule}");
        assert_eq!(ranks[1], 1_044, "schedule {schedule}");
        assert_eq!(ranks[9], 1_076, "schedule {schedule}");
        assert_eq!(ranks[10], 1_080, "schedule {schedule}");
    }
}

#[test]
fn rate32_q29_diagonal_finds_the_minimum_selected_extra_width() {
    for (ranks, _) in diagonal_ranks::<29>(15, 3, 0x5233_3251_3239_5a4b, false) {
        assert_eq!(ranks[10], 1_080);
    }
}

#[test]
fn coordinate_factored_qm31_packing_is_a_terminal_binding_negative_tooth() {
    for (_, qm31_ranks) in diagonal_ranks::<36>(14, 1, 0x514d_3331_5231_365a, true)
        .into_iter()
        .chain(diagonal_ranks::<29>(15, 1, 0x514d_3331_5233_325a, true))
    {
        assert_eq!(qm31_ranks.len(), 4);
        assert_eq!(qm31_ranks, [1_040, 1_068, 1_084, 1_084]);
        assert!(
            qm31_ranks[2] > 1_080,
            "a terminal-computable mask cannot exceed the one-QM31 terminal quotient"
        );
    }
}

fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31(seed + index as u32 * 17))
}

fn valid_spend(seed: u32, value: u32, path_index: u32) -> (SpendPublic, SpendWitness) {
    let nullifier_key = digest(seed + 101);
    let input_salt = digest(seed + 301);
    let output_salt = digest(seed + 501);
    let output_owner_key = digest(seed + 701);
    let asset_id = M31(17 + seed);
    let value_out = value - 1;
    let owner_key = derive_owner_key(&nullifier_key);
    let note = note_commitment(&owner_key, value, asset_id, &input_salt);
    let merkle_path = MerklePath {
        siblings: (0..20)
            .map(|level| digest(seed + 1_000 + level * 29))
            .collect(),
        index: path_index,
    };
    let public = SpendPublic {
        anchor: merkle_root(note, &merkle_path).unwrap(),
        nullifier: derive_nullifier(&nullifier_key, &input_salt),
        output_commitment: output_commitment(&output_owner_key, value_out, asset_id, &output_salt),
        asset_id,
        fee: 1,
    };
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value,
        value_out,
        merkle_path,
    };
    (public, witness)
}

#[test]
fn current_selected_masks_have_an_exact_public_h1_containment_counterexample() {
    let mask_cells = state_only_relation_free_mask_cells_v4().unwrap();
    let layout = state_only_copy_layout_v4().unwrap();

    // Structural, not sampled: the only masks which modify semantic C1 are
    // disjoint from every tuple cell used to construct h1. The ten mask-only
    // C1 columns and G are not arguments of the h1 builder at all.
    for link in &layout.links {
        for tuple in [link.producer, link.consumer] {
            for limb in tuple.limbs {
                if let TupleLimb::Cell(cell) = limb {
                    assert!(
                        !mask_cells.contains(&cell),
                        "relation-free mask unexpectedly changes copy endpoint {cell:?}"
                    );
                }
            }
        }
    }

    let (public_a, witness_a) = valid_spend(0, 1_000_000, 0x5_4321);
    let source_a = build_spend_trace_v4(&public_a, &witness_a).unwrap();
    let trace_a = project_state_only_trace_v4(&source_a).unwrap();
    let (public_b, witness_b) = valid_spend(10_000, 765_432, 0x3_210f);
    let source_b = build_spend_trace_v4(&public_b, &witness_b).unwrap();
    let trace_b = project_state_only_trace_v4(&source_b).unwrap();

    let mut rng = Rng(0x4831_434f_554e_5445);
    let lambda = rng.qm31();
    let chi = rng.qm31();
    let h1_a = build_state_only_copy_helper_v4(&trace_a, lambda, chi).unwrap();
    let h1_b = build_state_only_copy_helper_v4(&trace_b, lambda, chi).unwrap();
    assert_ne!(h1_a, h1_b, "valid witness fixtures unexpectedly share h1");

    let mut padded_a = trace_a.clone();
    for (index, cell) in mask_cells.iter().copied().enumerate() {
        let value = &mut padded_a.c1[usize::from(cell.column)][usize::from(cell.row)];
        *value = value.add(M31((index as u32 + 1) % P));
    }
    assert_eq!(
        build_state_only_copy_helper_v4(&padded_a, lambda, chi).unwrap(),
        h1_a,
        "relation-free semantic pads changed h1 despite endpoint disjointness"
    );

    // Both production geometries expose h1(z) in the three-point statement
    // block and expose h1 codeword symbols in C2 leaves. A single nonzero h1
    // projection is enough: M_mask is identically zero on this coordinate,
    // while the representative valid-fixture difference is nonzero, so
    // rank([M_mask | M_diff]) > rank(M_mask).
    for (name, schedules, seed) in [
        ("rate16-q36", 3usize, 0x4831_5231_365a_4b31u64),
        ("rate32-q29", 3usize, 0x4831_5233_325a_4b31u64),
    ] {
        let mut schedule_rng = Rng(seed);
        for schedule in 0..schedules {
            let z = core::array::from_fn(|_| schedule_rng.qm31());
            let a = state_only_semantic_openings_at_point(&trace_a, &h1_a, &z)
                .unwrap()
                .h1_z;
            let b = state_only_semantic_openings_at_point(&trace_b, &h1_b, &z)
                .unwrap()
                .h1_z;
            let difference = qm31_coordinates(a.sub(b));
            assert!(
                difference.iter().any(|value| *value != M31::ZERO),
                "zero representative h1 difference for {name} schedule {schedule}"
            );
            let empty_mask_rank = rank_m31_image_columns(&[], 4);
            let augmented_rank = rank_m31_image_columns(&[difference.to_vec()], 4);
            assert_eq!(empty_mask_rank, 0);
            assert_eq!(augmented_rank, 1);
        }
    }
}

fn copy_inactive_successor_pairs() -> Vec<(usize, usize)> {
    let layout = state_only_copy_layout_v4().unwrap();
    let mut active = [false; TRACE_ROWS];
    for link in layout.links {
        active[usize::from(link.producer_row)] = true;
        active[usize::from(link.consumer_row)] = true;
    }
    (0..TRACE_ROWS)
        .step_by(2)
        .filter(|row| !active[*row] && !active[*row + 1])
        .map(|row| (row, row + 1))
        .collect()
}

fn copy_inactive_rows() -> Vec<usize> {
    let layout = state_only_copy_layout_v4().unwrap();
    let mut active = [false; TRACE_ROWS];
    for link in layout.links {
        active[usize::from(link.producer_row)] = true;
        active[usize::from(link.consumer_row)] = true;
    }
    (0..TRACE_ROWS).filter(|row| !active[*row]).collect()
}

fn h1_pair_view_rank<const Q: usize>(domain_log: u32, seed: u64) -> usize {
    let pairs = copy_inactive_successor_pairs();
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let mut rng = Rng(seed);
    let queries = distinct_queries::<Q>(&mut rng, domain_log);
    let z = core::array::from_fn(|_| rng.qm31());
    let terminal_points = [z, binary_successor_point(&z), xor12_point(&z)];
    let outputs = Q * FIBER_SLOTS + terminal_points.len();
    let images = pairs
        .into_iter()
        .map(|(first, second)| {
            let mut message = vec![QM31::ZERO; TRACE_ROWS];
            message[first] = QM31::ONE;
            message[second] = QM31::ZERO.sub(QM31::ONE);
            let codeword = encoder.encode_c2_message(&message).unwrap();
            let mut image = Vec::with_capacity(outputs);
            for &query in &queries {
                for slot in 0..FIBER_SLOTS {
                    image.push(codeword[FIBER_SLOTS * query + slot]);
                }
            }
            for point in &terminal_points {
                image.push(eq_weight(point, first).sub(eq_weight(point, second)));
            }
            image
        })
        .collect::<Vec<_>>();
    rank_qm31_image_columns(&images, outputs)
}

#[test]
fn copy_inactive_successor_pair_masks_are_an_exact_negative_rank_tooth() {
    let pairs = copy_inactive_successor_pairs();
    assert!(pairs.windows(2).all(|pair| pair[0].1 < pair[1].0));
    assert!(pairs.len() >= STATE_ONLY_HIDING_G_RAW_QM31_OBSERVATIONS);

    for schedule in 0..3u64 {
        assert_eq!(
            h1_pair_view_rank::<36>(14, 0x4831_5041_4952_1630 ^ schedule),
            75,
            "rate16/q36 schedule {schedule}"
        );
        assert_eq!(
            h1_pair_view_rank::<29>(15, 0x4831_5041_4952_3230 ^ schedule),
            61,
            "rate32/q29 schedule {schedule}"
        );
    }
}

const H1_PADDING_MASK_START: usize = 868;

fn h1_global_padding_sum_view_rank<const Q: usize>(domain_log: u32, seed: u64) -> usize {
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let mut rng = Rng(seed);
    let queries = distinct_queries::<Q>(&mut rng, domain_log);
    let z = core::array::from_fn(|_| rng.qm31());
    let terminal_points = [z, binary_successor_point(&z), xor12_point(&z)];
    let outputs = Q * FIBER_SLOTS + terminal_points.len();
    let dependent = TRACE_ROWS - 1;
    let images = (H1_PADDING_MASK_START..dependent)
        .map(|row| {
            let mut message = vec![QM31::ZERO; TRACE_ROWS];
            message[row] = QM31::ONE;
            message[dependent] = QM31::ZERO.sub(QM31::ONE);
            let codeword = encoder.encode_c2_message(&message).unwrap();
            let mut image = Vec::with_capacity(outputs);
            for &query in &queries {
                for slot in 0..FIBER_SLOTS {
                    image.push(codeword[FIBER_SLOTS * query + slot]);
                }
            }
            for point in &terminal_points {
                image.push(eq_weight(point, row).sub(eq_weight(point, dependent)));
            }
            image
        })
        .collect::<Vec<_>>();
    rank_qm31_image_columns(&images, outputs)
}

#[derive(Clone)]
struct FullH1ViewSchedule<const Q: usize> {
    queries: [usize; Q],
    z: [QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    gamma: QM31,
    kappa: QM31,
    circle_ood: [[aspis_core::circle::SecureCirclePoint; CANDIDATE_OOD_SAMPLES]; 1],
    line_ood: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    mixes: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    alphas: [QM31; CANDIDATE_ROUND_COUNT],
}

fn full_h1_view_schedule<const Q: usize>(domain_log: u32, seed: u64) -> FullH1ViewSchedule<Q> {
    let mut rng = Rng(seed);
    let queries = distinct_queries::<Q>(&mut rng, domain_log);
    let z = core::array::from_fn(|_| rng.qm31());
    let gamma = loop {
        let candidate = rng.qm31();
        if candidate != QM31::ZERO {
            break candidate;
        }
    };
    let kappa = rng.qm31();
    let circle_ood = [core::array::from_fn(|_| loop {
        if let Ok(point) = secure_ood_circle_point_from_parameter(rng.qm31()) {
            break point;
        }
    })];
    let line_ood = core::array::from_fn(|_| core::array::from_fn(|_| rng.qm31()));
    let mixes = core::array::from_fn(|_| core::array::from_fn(|_| rng.qm31()));
    let alphas = core::array::from_fn(|_| rng.qm31());
    FullH1ViewSchedule {
        queries,
        z,
        gamma,
        kappa,
        circle_ood,
        line_ood,
        mixes,
        alphas,
    }
}

fn qm31_power(base: QM31, exponent: usize) -> QM31 {
    (0..exponent).fold(QM31::ONE, |power, _| power.mul(base))
}

fn full_h1_public_view<const Q: usize>(
    encoder: &CircleEncoder,
    domain_log: u32,
    h1: &[QM31],
    schedule: &FullH1ViewSchedule<Q>,
) -> Vec<QM31> {
    assert_eq!(h1.len(), TRACE_ROWS);
    let h1_codeword = encoder.encode_c2_message(h1).unwrap();
    let scale = qm31_power(schedule.gamma, STATE_ONLY_HIDING_H1_GENERATOR_INDEX);
    let combined_message = h1
        .iter()
        .copied()
        .map(|value| scale.mul(value))
        .collect::<Vec<_>>();
    let combined_codeword = h1_codeword
        .iter()
        .copied()
        .map(|value| scale.mul(value))
        .collect::<Vec<_>>();
    let folds = build_fold_commitments_for_domain_log(
        &combined_codeword,
        &combined_message,
        schedule.alphas,
        domain_log,
        HOST_HASH,
    )
    .unwrap();
    let terminal_points = [
        schedule.z,
        binary_successor_point(&schedule.z),
        xor12_point(&schedule.z),
    ];
    let mut relation = StateOnlyIncrementalRelation::new(
        combined_message,
        &terminal_points,
        [QM31::ONE, schedule.kappa, schedule.kappa.square()],
    )
    .unwrap();
    let mut relation_polynomials = Vec::with_capacity(CANDIDATE_ROUND_COUNT);
    for round in 0..CANDIDATE_ROUND_COUNT {
        for sample in 0..CANDIDATE_OOD_SAMPLES {
            if round == 0 {
                let point = schedule.circle_ood[0][sample];
                let value = relation.evaluate_circle_ood(point).unwrap();
                relation
                    .add_circle_ood(point, value, schedule.mixes[round][sample])
                    .unwrap();
            } else {
                let point = schedule.line_ood[round - 1][sample];
                let value = relation.evaluate_line_ood(point).unwrap();
                relation
                    .add_line_ood(point, value, schedule.mixes[round][sample])
                    .unwrap();
            }
        }
        relation_polynomials.push(relation.polynomial().unwrap());
        relation.fold(schedule.alphas[round]).unwrap();
    }
    let relation = relation.finish().unwrap();

    let query_u32 = schedule.queries.map(|query| query as u32);
    let indices = derive_circle_line_query_indices_for_count(
        &query_u32,
        encoder.codeword_len() / FIBER_SLOTS,
    )
    .unwrap();
    let mut view = Vec::new();
    for &query in &indices.layer0 {
        view.extend_from_slice(
            &h1_codeword[FIBER_SLOTS * query as usize..FIBER_SLOTS * (query as usize + 1)],
        );
    }
    for point in &terminal_points {
        view.push(
            h1.iter()
                .copied()
                .enumerate()
                .fold(QM31::ZERO, |sum, (row, value)| {
                    sum.add(eq_weight(point, row).mul(value))
                }),
        );
    }
    for layer in 0..folds.committed_evaluations.len() {
        for &query in &indices.later[layer] {
            view.extend_from_slice(
                &folds.committed_evaluations[layer]
                    [FIBER_SLOTS * query as usize..FIBER_SLOTS * (query as usize + 1)],
            );
        }
    }
    for values in relation.ood_values {
        view.extend_from_slice(&values);
    }
    for polynomial in relation_polynomials {
        view.extend_from_slice(&polynomial);
    }
    view.extend_from_slice(&relation.final_coefficients);
    view
}

fn full_h1_padding_containment<const Q: usize>(
    domain_log: u32,
    seed: u64,
    witness_difference: &[QM31],
) -> (usize, usize, usize) {
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let schedule = full_h1_view_schedule::<Q>(domain_log, seed);
    let dependent = TRACE_ROWS - 1;
    let mask_images = (H1_PADDING_MASK_START..dependent)
        .map(|row| {
            let mut message = vec![QM31::ZERO; TRACE_ROWS];
            message[row] = QM31::ONE;
            message[dependent] = QM31::ZERO.sub(QM31::ONE);
            full_h1_public_view(&encoder, domain_log, &message, &schedule)
        })
        .collect::<Vec<_>>();
    let outputs = mask_images[0].len();
    let mask_rank = rank_qm31_image_columns(&mask_images, outputs);
    let witness_image = full_h1_public_view(&encoder, domain_log, witness_difference, &schedule);
    let mut augmented = mask_images;
    augmented.push(witness_image);
    let augmented_rank = rank_qm31_image_columns(&augmented, outputs);
    (outputs, mask_rank, augmented_rank)
}

fn full_inactive_h1_padding_containment<const Q: usize>(
    domain_log: u32,
    seed: u64,
    witness_difference: &[QM31],
) -> (usize, usize, usize, usize, usize) {
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let schedule = full_h1_view_schedule::<Q>(domain_log, seed);
    let inactive = copy_inactive_rows();
    let dependent = *inactive.last().unwrap();
    let mut mask_images = Vec::with_capacity(inactive.len() - 1);
    for &row in &inactive[..inactive.len() - 1] {
        let mut message = vec![QM31::ZERO; TRACE_ROWS];
        message[row] = QM31::ONE;
        message[dependent] = QM31::ZERO.sub(QM31::ONE);
        mask_images.push(full_h1_public_view(
            &encoder, domain_log, &message, &schedule,
        ));
    }
    let outputs = mask_images[0].len();
    let mask_rank = rank_qm31_image_columns(&mask_images, outputs);
    let witness_image = full_h1_public_view(&encoder, domain_log, witness_difference, &schedule);
    let mut augmented = mask_images;
    augmented.push(witness_image);
    let augmented_rank = rank_qm31_image_columns(&augmented, outputs);
    let active = (0..TRACE_ROWS)
        .filter(|row| !inactive.contains(row))
        .collect::<Vec<_>>();
    let dependent_active = *active.last().unwrap();
    for &row in &active[..active.len() - 1] {
        let mut message = vec![QM31::ZERO; TRACE_ROWS];
        message[row] = QM31::ONE;
        message[dependent_active] = QM31::ZERO.sub(QM31::ONE);
        augmented.push(full_h1_public_view(
            &encoder, domain_log, &message, &schedule,
        ));
    }
    let universal_augmented_rank = rank_qm31_image_columns(&augmented, outputs);
    (
        inactive.len(),
        outputs,
        mask_rank,
        augmented_rank,
        universal_augmented_rank,
    )
}

#[test]
fn global_zero_sum_h1_padding_masks_span_the_complete_h1_layer0_view() {
    let layout = state_only_copy_layout_v4().unwrap();
    let max_endpoint = layout
        .links
        .iter()
        .flat_map(|link| [link.producer_row, link.consumer_row])
        .max()
        .unwrap();
    assert_eq!(max_endpoint, 866);
    assert_eq!(TRACE_ROWS - H1_PADDING_MASK_START - 1, 155);

    for schedule in 0..3u64 {
        assert_eq!(
            h1_global_padding_sum_view_rank::<36>(14, 0x4831_4753_554d_1630 ^ schedule),
            36 * FIBER_SLOTS + 3,
            "rate16/q36 schedule {schedule}"
        );
        assert_eq!(
            h1_global_padding_sum_view_rank::<29>(15, 0x4831_4753_554d_3230 ^ schedule),
            29 * FIBER_SLOTS + 3,
            "rate32/q29 schedule {schedule}"
        );
    }
}

#[test]
fn suffix_only_h1_padding_has_an_exact_full_pcs_view_counterexample() {
    let (public_a, witness_a) = valid_spend(0, 1_000_000, 0x5_4321);
    let source_a = build_spend_trace_v4(&public_a, &witness_a).unwrap();
    let trace_a = project_state_only_trace_v4(&source_a).unwrap();
    let (public_b, witness_b) = valid_spend(10_000, 765_432, 0x3_210f);
    let source_b = build_spend_trace_v4(&public_b, &witness_b).unwrap();
    let trace_b = project_state_only_trace_v4(&source_b).unwrap();
    let mut rng = Rng(0x4831_4655_4c4c_5649);
    let lambda = rng.qm31();
    let chi = rng.qm31();
    let h1_a = build_state_only_copy_helper_v4(&trace_a, lambda, chi).unwrap();
    let h1_b = build_state_only_copy_helper_v4(&trace_b, lambda, chi).unwrap();
    let difference = h1_a
        .iter()
        .copied()
        .zip(h1_b)
        .map(|(left, right)| left.sub(right))
        .collect::<Vec<_>>();

    for (name, result) in [
        (
            "rate16-q36",
            full_h1_padding_containment::<36>(14, 0x4655_4c4c_5231_365a, &difference),
        ),
        (
            "rate32-q29",
            full_h1_padding_containment::<29>(15, 0x4655_4c4c_5233_325a, &difference),
        ),
    ] {
        let (outputs, mask_rank, augmented_rank) = result;
        std::eprintln!(
            "full h1 PCS View {name}: outputs={outputs} mask-rank={mask_rank} augmented={augmented_rank}"
        );
        assert_eq!(
            augmented_rank,
            mask_rank + 1,
            "expected a one-dimensional helper-padding containment defect for {name}"
        );
    }
}

#[test]
fn all_copy_inactive_rows_contain_a_valid_witness_difference_in_the_full_pcs_view() {
    let (public_a, witness_a) = valid_spend(0, 1_000_000, 0x5_4321);
    let source_a = build_spend_trace_v4(&public_a, &witness_a).unwrap();
    let trace_a = project_state_only_trace_v4(&source_a).unwrap();
    let (public_b, witness_b) = valid_spend(10_000, 765_432, 0x3_210f);
    let source_b = build_spend_trace_v4(&public_b, &witness_b).unwrap();
    let trace_b = project_state_only_trace_v4(&source_b).unwrap();
    let mut rng = Rng(0x4831_494e_4143_5449);
    let lambda = rng.qm31();
    let chi = rng.qm31();
    let h1_a = build_state_only_copy_helper_v4(&trace_a, lambda, chi).unwrap();
    let h1_b = build_state_only_copy_helper_v4(&trace_b, lambda, chi).unwrap();
    let difference = h1_a
        .iter()
        .copied()
        .zip(h1_b)
        .map(|(left, right)| left.sub(right))
        .collect::<Vec<_>>();

    for (name, result) in [
        (
            "rate16-q36",
            full_inactive_h1_padding_containment::<36>(14, 0x494e_4143_5231_365a, &difference),
        ),
        (
            "rate32-q29",
            full_inactive_h1_padding_containment::<29>(15, 0x494e_4143_5233_325a, &difference),
        ),
    ] {
        let (inactive, outputs, mask_rank, augmented_rank, universal_augmented_rank) = result;
        std::eprintln!(
            "all-inactive h1 PCS View {name}: inactive={inactive} outputs={outputs} mask-rank={mask_rank} witness-augmented={augmented_rank} active-zero-sum-augmented={universal_augmented_rank}"
        );
        assert_eq!(augmented_rank, mask_rank, "containment defect for {name}");
        assert_eq!(
            universal_augmented_rank, mask_rank,
            "the inactive masks do not contain the complete active zero-sum helper subspace for {name}"
        );
    }
}

#[test]
fn state_only_hiding_fingerprint_binds_the_generated_semantic_layout() {
    let layout = state_only_relation_free_mask_fingerprint_v4().unwrap();
    assert_eq!(layout, PINNED_STATE_ONLY_RELATION_FREE_MASK_FINGERPRINT);
    let combined = state_only_hiding_layout_factor_fingerprint(layout);
    std::eprintln!("state-only hiding layout/factor fingerprint: {combined:#018x}");
    assert_eq!(combined, PINNED_STATE_ONLY_HIDING_LAYOUT_FACTOR_FINGERPRINT);
    assert_ne!(
        combined,
        state_only_hiding_layout_factor_fingerprint(layout ^ 1)
    );
}

#[test]
fn reusing_state_only_mask_randomness_cancels_the_pad() {
    // This is a negative privacy tooth, not a sampler: two transcripts made
    // with the same affine pad reveal their unmasked difference exactly.
    // Production must bind a fresh mask seed/nonce to every proof instance.
    let mut rng = Rng(0x5245_5553_455f_5a4b);
    let left: [QM31; 64] = core::array::from_fn(|_| rng.qm31());
    let right: [QM31; 64] = core::array::from_fn(|_| rng.qm31());
    let reused: [QM31; 64] = core::array::from_fn(|_| rng.qm31());
    let fresh: [QM31; 64] = core::array::from_fn(|_| rng.qm31());
    let masked_left = core::array::from_fn::<_, 64, _>(|index| left[index].add(reused[index]));
    let reused_right = core::array::from_fn::<_, 64, _>(|index| right[index].add(reused[index]));
    let fresh_right = core::array::from_fn::<_, 64, _>(|index| right[index].add(fresh[index]));
    for index in 0..64 {
        assert_eq!(
            masked_left[index].sub(reused_right[index]),
            left[index].sub(right[index])
        );
    }
    assert!(
        (0..64).any(|index| {
            masked_left[index].sub(fresh_right[index]) != left[index].sub(right[index])
        }),
        "fresh-mask negative control unexpectedly cancelled"
    );
}
