use aspis_core::field::{CM31, M31, P, QM31};
use aspis_core::statement_hiding::{
    payment_sparse_mask_factors, payment_sparse_mask_value, PAYMENT_SPARSE_MASK_C1_COLUMNS,
};
use aspis_core::statement_sumcheck::{
    boundary_sum, compress_polynomial, evaluate, PaymentSumcheckFullPolynomial,
    PAYMENT_SUMCHECK_DEGREE, PAYMENT_SUMCHECK_ROUNDS, PAYMENT_SUMCHECK_WIRE_COEFFICIENTS,
};
use aspis_prover::circle_candidate::CircleEncoder;
use aspis_statement::{
    direct_range_c1_mask_cells_v4, expanded_hiding_padding_cells_v4, xor11_point,
    AUX_WITNESS_ROW_START, COPY_HELPER_PADDING_ROW_START, DIRECT_RANGE_C1_COLUMN_COUNT,
    HIDING_PADDING_ROW_COUNT, HIDING_PADDING_ROW_START, STATE_AND_INTERFACE_COLUMNS, TRACE_ROWS,
};

const RATE16_DOMAIN_LOG: u32 = 14;
const QUERY_COUNT: usize = 36;
const FIBER_SLOTS: usize = 4;
const OBSERVED_BASE_SYMBOLS: usize = QUERY_COUNT * FIBER_SLOTS;
const TERMINAL_M31_COORDINATES: usize = 2 * 4;
const OBSERVATION_COUNT: usize = OBSERVED_BASE_SYMBOLS + TERMINAL_M31_COORDINATES;
const HELPER_PADDING_ROW_START: usize = COPY_HELPER_PADDING_ROW_START;
const HELPER_PADDING_ROWS: usize = TRACE_ROWS - HELPER_PADDING_ROW_START;
const HELPER_MASK_VARIABLES: usize = HELPER_PADDING_ROWS - 1;
const HELPER_OBSERVATIONS: usize = OBSERVED_BASE_SYMBOLS + 2;

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

fn qm31_coordinates(value: QM31) -> [M31; 4] {
    [value.c0.a, value.c0.b, value.c1.a, value.c1.b]
}

fn eq_weight(point: &[QM31; 10], row: usize) -> QM31 {
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

fn distinct_queries(rng: &mut Rng) -> [usize; QUERY_COUNT] {
    let mut queries = [0usize; QUERY_COUNT];
    let mut count = 0;
    while count < QUERY_COUNT {
        let candidate = (rng.next() as usize) & ((1usize << (RATE16_DOMAIN_LOG - 2)) - 1);
        if !queries[..count].contains(&candidate) {
            queries[count] = candidate;
            count += 1;
        }
    }
    queries
}

fn rank(mut matrix: Vec<Vec<M31>>) -> usize {
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

fn encoded_padding_basis(first_row: usize) -> Vec<Vec<M31>> {
    let encoder = CircleEncoder::new_for_domain_log(RATE16_DOMAIN_LOG);
    (first_row..TRACE_ROWS)
        .map(|row| {
            let mut message = vec![M31::ZERO; TRACE_ROWS];
            message[row] = M31::ONE;
            encoder.encode_c1_message(&message).unwrap()
        })
        .collect()
}

fn observation_matrix(
    encoded_basis: &[Vec<M31>],
    basis_first_row: usize,
    mask_rows: &[usize],
    queries: &[usize; QUERY_COUNT],
    z: &[QM31; 10],
) -> Vec<Vec<M31>> {
    let shifted = xor11_point(z);
    let mut matrix = vec![vec![M31::ZERO; mask_rows.len()]; OBSERVATION_COUNT];
    for (mask, &row) in mask_rows.iter().enumerate() {
        let codeword = &encoded_basis[row - basis_first_row];
        let mut output = 0;
        for &query in queries {
            for slot in 0..FIBER_SLOTS {
                matrix[output][mask] = codeword[FIBER_SLOTS * query + slot];
                output += 1;
            }
        }
        for point in [z, &shifted] {
            for coordinate in qm31_coordinates(eq_weight(point, row)) {
                matrix[output][mask] = coordinate;
                output += 1;
            }
        }
        assert_eq!(output, OBSERVATION_COUNT);
    }
    matrix
}

#[test]
fn rate16_padding_has_full_rank_for_base_openings_and_both_terminal_points() {
    assert_eq!(HIDING_PADDING_ROW_COUNT, 167);
    assert_eq!(OBSERVATION_COUNT, 152);
    let encoded_basis = encoded_padding_basis(HIDING_PADDING_ROW_START);
    let mask_rows = (HIDING_PADDING_ROW_START..TRACE_ROWS).collect::<Vec<_>>();
    let mut rng = Rng(0x4849_4449_4e47_5634);
    for schedule in 0..8 {
        let queries = distinct_queries(&mut rng);
        let z = core::array::from_fn(|_| rng.qm31());
        let matrix = observation_matrix(
            &encoded_basis,
            HIDING_PADDING_ROW_START,
            &mask_rows,
            &queries,
            &z,
        );
        assert_eq!(
            rank(matrix),
            OBSERVATION_COUNT,
            "rank-deficient padding observation map for schedule {schedule}"
        );
    }
}

#[test]
fn expanded_padding_has_full_base_and_terminal_rank_in_every_masked_column() {
    let cells = expanded_hiding_padding_cells_v4();
    let mut rows_by_column: [Vec<usize>; STATE_AND_INTERFACE_COLUMNS] =
        core::array::from_fn(|_| Vec::new());
    for cell in cells {
        rows_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    assert!(rows_by_column
        .iter()
        .all(|rows| rows.len() >= OBSERVATION_COUNT));

    let encoded_basis = encoded_padding_basis(AUX_WITNESS_ROW_START);
    let mut rng = Rng(0x4558_5041_4e44_5634);
    for schedule in 0..3 {
        let queries = distinct_queries(&mut rng);
        let z = core::array::from_fn(|_| rng.qm31());
        for (column, rows) in rows_by_column.iter().enumerate() {
            let matrix =
                observation_matrix(&encoded_basis, AUX_WITNESS_ROW_START, rows, &queries, &z);
            assert_eq!(
                rank(matrix),
                OBSERVATION_COUNT,
                "rank-deficient expanded map for schedule {schedule}, column {column}"
            );
        }
    }
}

#[test]
fn zero_sum_helper_padding_masks_q36_base_symbols_and_both_terminal_values() {
    assert_eq!(HELPER_PADDING_ROWS, 158);
    assert_eq!(HELPER_MASK_VARIABLES, 157);
    assert_eq!(HELPER_OBSERVATIONS, 146);
    let encoded_basis = encoded_padding_basis(HELPER_PADDING_ROW_START);
    let last = encoded_basis.len() - 1;
    let mut rng = Rng(0x4845_4c50_4552_5634);
    for schedule in 0..8 {
        let queries = distinct_queries(&mut rng);
        let z = core::array::from_fn(|_| rng.qm31());
        let shifted = xor11_point(&z);
        let mut matrix = vec![vec![QM31::ZERO; HELPER_MASK_VARIABLES]; HELPER_OBSERVATIONS];
        for variable in 0..HELPER_MASK_VARIABLES {
            let mut output = 0;
            for &query in &queries {
                for slot in 0..FIBER_SLOTS {
                    let coefficient = encoded_basis[variable][FIBER_SLOTS * query + slot]
                        .sub(encoded_basis[last][FIBER_SLOTS * query + slot]);
                    matrix[output][variable] = QM31::from_cm31(CM31::from_m31(coefficient));
                    output += 1;
                }
            }
            let row = HELPER_PADDING_ROW_START + variable;
            let last_row = TRACE_ROWS - 1;
            for point in [&z, &shifted] {
                matrix[output][variable] = eq_weight(point, row).sub(eq_weight(point, last_row));
                output += 1;
            }
            assert_eq!(output, HELPER_OBSERVATIONS);
        }
        assert_eq!(
            rank_qm31(matrix),
            HELPER_OBSERVATIONS,
            "rank-deficient zero-sum helper mask for schedule {schedule}"
        );
    }
}

#[test]
fn direct_range_zero_sum_c1_masks_cover_base_and_terminal_in_all_49_columns() {
    let cells = direct_range_c1_mask_cells_v4();
    let mut rows_by_column: [Vec<usize>; DIRECT_RANGE_C1_COLUMN_COUNT] =
        core::array::from_fn(|_| Vec::new());
    for cell in cells {
        let row = usize::from(cell.row);
        if row >= AUX_WITNESS_ROW_START {
            rows_by_column[usize::from(cell.column)].push(row);
        }
    }
    assert!(rows_by_column
        .iter()
        .all(|rows| rows.len() >= OBSERVATION_COUNT));
    let encoded_basis = encoded_padding_basis(AUX_WITNESS_ROW_START);
    let dependent = TRACE_ROWS - 1 - AUX_WITNESS_ROW_START;
    let mut rng = Rng(0x4449_5245_4354_5634);
    for schedule in 0..3 {
        let queries = distinct_queries(&mut rng);
        let z = core::array::from_fn(|_| rng.qm31());
        let shifted = xor11_point(&z);
        for (column, rows) in rows_by_column.iter().enumerate() {
            let mut matrix = vec![vec![M31::ZERO; rows.len()]; OBSERVATION_COUNT];
            for (variable, &row) in rows.iter().enumerate() {
                let subtract_dependent = row >= COPY_HELPER_PADDING_ROW_START;
                let codeword = &encoded_basis[row - AUX_WITNESS_ROW_START];
                let mut output = 0;
                for &query in &queries {
                    for slot in 0..FIBER_SLOTS {
                        let mut coefficient = codeword[FIBER_SLOTS * query + slot];
                        if subtract_dependent {
                            coefficient = coefficient
                                .sub(encoded_basis[dependent][FIBER_SLOTS * query + slot]);
                        }
                        matrix[output][variable] = coefficient;
                        output += 1;
                    }
                }
                for point in [&z, &shifted] {
                    let mut weight = eq_weight(point, row);
                    if subtract_dependent {
                        weight = weight.sub(eq_weight(point, TRACE_ROWS - 1));
                    }
                    for coordinate in qm31_coordinates(weight) {
                        matrix[output][variable] = coordinate;
                        output += 1;
                    }
                }
                assert_eq!(output, OBSERVATION_COUNT);
            }
            assert_eq!(
                rank(matrix),
                OBSERVATION_COUNT,
                "rank-deficient direct-range C1 map for schedule {schedule}, column {column}"
            );
        }
    }
}

#[test]
fn virtual_qm31_mask_minor_uses_only_independent_direct_range_c1_cells() {
    let cells = direct_range_c1_mask_cells_v4();
    let mut fingerprint = 0xcbf2_9ce4_8422_2325u64;
    for oracle in 0..6usize {
        for byte in (oracle as u64).to_le_bytes() {
            fingerprint ^= u64::from(byte);
            fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
        }
        let mut selected = Vec::new();
        for local in 0..1024usize {
            let row = (local * 573 + oracle * 137 + 211) & 1023;
            let available = (0..4usize).all(|basis_column| {
                let column = 4 * oracle + basis_column;
                cells
                    .iter()
                    .any(|cell| usize::from(cell.row) == row && usize::from(cell.column) == column)
            });
            if available {
                selected.push(row);
                if selected.len() == 32 {
                    break;
                }
            }
        }
        assert_eq!(selected.len(), 32, "oracle={oracle}");
        for row in selected {
            for byte in (row as u64).to_le_bytes() {
                fingerprint ^= u64::from(byte);
                fingerprint = fingerprint.wrapping_mul(0x0000_0100_0000_01b3);
            }
        }
    }
    assert_eq!(fingerprint, 0x3561_be61_14b1_1a77);
}

fn c1_mask_linear(family: usize, point: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let scalar = 3 + 22 * variable + family * (17 + 8 * variable);
            sum.add(value.mul_m31(M31(scalar as u32)))
        })
}

fn c1_mask_factor(column: usize, point: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> QM31 {
    const EXPONENTS: [[usize; 5]; 3] = [[0, 2, 4, 6, 9], [0, 2, 4, 6, 9], [9, 0, 5, 0, 0]];
    let (family, exponent) = if column == DIRECT_RANGE_C1_COLUMN_COUNT {
        (3, 9)
    } else {
        let group = column / 4;
        (group / 5, EXPONENTS[group / 5][group % 5])
    };
    let linear = c1_mask_linear(family, point);
    let power = (0..exponent).fold(QM31::ONE, |power, _| power.mul(linear));
    if column == DIRECT_RANGE_C1_COLUMN_COUNT {
        QM31::ONE.add(power)
    } else {
        power
    }
}

fn c1_mask_basis(column: usize) -> QM31 {
    match column % 4 {
        0 => QM31::ONE,
        1 => QM31 {
            c0: CM31::new(M31::ZERO, M31::ONE),
            c1: CM31::ZERO,
        },
        2 => QM31 {
            c0: CM31::ZERO,
            c1: CM31::ONE,
        },
        3 => QM31 {
            c0: CM31::ZERO,
            c1: CM31::new(M31::ZERO, M31::ONE),
        },
        _ => unreachable!(),
    }
}

#[derive(Clone, Copy)]
struct IndependentMultilinearOracle {
    at_zero: [QM31; PAYMENT_SUMCHECK_ROUNDS],
    at_one: [QM31; PAYMENT_SUMCHECK_ROUNDS],
}

impl IndependentMultilinearOracle {
    fn random(rng: &mut Rng) -> Self {
        Self {
            at_zero: core::array::from_fn(|_| rng.qm31()),
            at_one: core::array::from_fn(|_| rng.qm31()),
        }
    }

    fn evaluate(&self, point: &[QM31; PAYMENT_SUMCHECK_ROUNDS]) -> QM31 {
        (0..PAYMENT_SUMCHECK_ROUNDS).fold(QM31::ONE, |product, variable| {
            let value = self.at_zero[variable]
                .mul(QM31::ONE.sub(point[variable]))
                .add(self.at_one[variable].mul(point[variable]));
            product.mul(value)
        })
    }
}

fn deterministic_off_domain_point(rng: &mut Rng) -> [QM31; PAYMENT_SUMCHECK_ROUNDS] {
    core::array::from_fn(|_| loop {
        let value = rng.qm31();
        if value != QM31::ZERO && value != QM31::ONE {
            break value;
        }
    })
}

#[test]
fn independent_sparse_mask_identity_holds_at_50_off_domain_points_with_sz_bound() {
    const IDENTITY_POINTS: usize = 50;
    assert_eq!(PAYMENT_SPARSE_MASK_C1_COLUMNS, DIRECT_RANGE_C1_COLUMN_COUNT);

    // This reference deliberately re-encodes the family/exponent/tower-basis
    // schedule through `c1_mask_*`; it does not call the production helper to
    // derive either the expected factors or the expected H value.  With
    // arbitrary multilinear C_j and G, a nonzero difference has total degree
    // at most 9 + 10 = 19.  Thus 50 independent points sampled uniformly from
    // QM31 \ {0,1} would miss it with probability at most
    // (19 / (|QM31| - 2))^50 = (19 / (P^4 - 2))^50.  The fixed PRNG seed makes
    // those off-domain points reproducible in CI; this is a regression guard,
    // not a source of protocol soundness.
    let mut rng = Rng(0x535a_5f35_3050_5453);
    let c1_oracles: [IndependentMultilinearOracle; PAYMENT_SPARSE_MASK_C1_COLUMNS] =
        core::array::from_fn(|_| IndependentMultilinearOracle::random(&mut rng));
    let explicit_oracle = IndependentMultilinearOracle::random(&mut rng);

    for point_index in 0..IDENTITY_POINTS {
        let point = deterministic_off_domain_point(&mut rng);
        let production_factors = payment_sparse_mask_factors(&point);
        for column in 0..PAYMENT_SPARSE_MASK_C1_COLUMNS {
            let independent_factor = c1_mask_basis(column).mul(c1_mask_factor(column, &point));
            assert_eq!(
                production_factors.c1[column], independent_factor,
                "factor mismatch at off-domain point {point_index}, column {column}"
            );
        }
        let independent_explicit_factor = c1_mask_factor(PAYMENT_SPARSE_MASK_C1_COLUMNS, &point);
        assert_eq!(
            production_factors.explicit, independent_explicit_factor,
            "explicit factor mismatch at off-domain point {point_index}"
        );

        let c1_values = core::array::from_fn(|column| c1_oracles[column].evaluate(&point));
        let explicit_value = explicit_oracle.evaluate(&point);
        let independent_h = c1_values
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::ZERO, |sum, (column, value)| {
                let factor = c1_mask_basis(column).mul(c1_mask_factor(column, &point));
                sum.add(factor.mul(value))
            })
            .add(independent_explicit_factor.mul(explicit_value));
        assert_eq!(
            payment_sparse_mask_value(&c1_values, explicit_value, &point),
            independent_h,
            "H mismatch at off-domain point {point_index}"
        );
    }
}

fn interpolate_payment_samples(
    values: &[QM31; PAYMENT_SUMCHECK_DEGREE + 1],
) -> PaymentSumcheckFullPolynomial {
    let mut output = [QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
    for i in 0..=PAYMENT_SUMCHECK_DEGREE {
        let mut basis = [QM31::ZERO; PAYMENT_SUMCHECK_DEGREE + 1];
        basis[0] = QM31::ONE;
        let mut basis_degree = 0usize;
        let mut denominator = M31::ONE;
        for j in 0..=PAYMENT_SUMCHECK_DEGREE {
            if i == j {
                continue;
            }
            let root = M31(j as u32);
            let previous = basis;
            for coefficient in 0..=basis_degree + 1 {
                let shifted = if coefficient == 0 {
                    QM31::ZERO
                } else {
                    previous[coefficient - 1]
                };
                let constant = if coefficient <= basis_degree {
                    previous[coefficient].mul_m31(root)
                } else {
                    QM31::ZERO
                };
                basis[coefficient] = shifted.sub(constant);
            }
            basis_degree += 1;
            denominator = denominator.mul(M31(i as u32).sub(root));
        }
        let scale = values[i].mul_m31(denominator.inv());
        for coefficient in 0..=PAYMENT_SUMCHECK_DEGREE {
            output[coefficient] = output[coefficient].add(scale.mul(basis[coefficient]));
        }
    }
    output
}

fn c1_mask_sumcheck_observations(
    column: usize,
    row: usize,
    challenges: &[QM31; PAYMENT_SUMCHECK_ROUNDS],
) -> Vec<QM31> {
    let mut prefix = [QM31::ZERO; PAYMENT_SUMCHECK_ROUNDS];
    let boolean_point = core::array::from_fn(|coordinate| {
        let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
        if bit == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        }
    });
    let mut running_claim = c1_mask_factor(column, &boolean_point);
    let mut observations =
        Vec::with_capacity(1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS);
    observations.push(running_claim);
    for round in 0..PAYMENT_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            // On the Boolean suffix, eq(row, x) is zero for every assignment
            // except the suffix of `row`, so the apparent suffix sum has one
            // nonzero term.
            for coordinate in round + 1..PAYMENT_SUMCHECK_ROUNDS {
                let bit = (row >> (PAYMENT_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                prefix[coordinate] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
            }
            eq_weight(&prefix, row).mul(c1_mask_factor(column, &prefix))
        });
        let polynomial = interpolate_payment_samples(&samples);
        assert_eq!(boundary_sum(&polynomial), running_claim);
        observations.extend(compress_polynomial(&polynomial));
        running_claim = evaluate(&polynomial, challenges[round]);
        prefix[round] = challenges[round];
    }
    observations
}

#[test]
fn all_c1_padding_with_ten_cheap_factors_spans_the_sumcheck_view() {
    const OUTPUTS: usize = 4 * (1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS);
    const VARIABLES_PER_COLUMN: usize = 64;
    const EXPLICIT_MASK_VARIABLES: usize = 32;
    const C1_VARIABLES: usize = DIRECT_RANGE_C1_COLUMN_COUNT * VARIABLES_PER_COLUMN;
    let cells = direct_range_c1_mask_cells_v4();
    let mut available = [[false; TRACE_ROWS]; DIRECT_RANGE_C1_COLUMN_COUNT];
    for cell in cells {
        available[usize::from(cell.column)][usize::from(cell.row)] = true;
    }
    let mut rng = Rng(0x4331_4d41_534b_524b);
    let challenges = core::array::from_fn(|_| rng.qm31());
    let mut matrix = vec![vec![M31::ZERO; C1_VARIABLES + 4 * EXPLICIT_MASK_VARIABLES]; OUTPUTS];
    for column in 0..DIRECT_RANGE_C1_COLUMN_COUNT {
        let basis = c1_mask_basis(column);
        let mut selected = Vec::with_capacity(VARIABLES_PER_COLUMN);
        for local in 0..TRACE_ROWS {
            let row = (local * 573 + column * 137 + 211) & (TRACE_ROWS - 1);
            if available[column][row] {
                selected.push(row);
                if selected.len() == VARIABLES_PER_COLUMN {
                    break;
                }
            }
        }
        assert_eq!(selected.len(), VARIABLES_PER_COLUMN, "column={column}");
        for (local, row) in selected.into_iter().enumerate() {
            let mut observations = c1_mask_sumcheck_observations(column, row, &challenges);
            if row >= COPY_HELPER_PADDING_ROW_START {
                let dependent = c1_mask_sumcheck_observations(column, TRACE_ROWS - 1, &challenges);
                for (value, subtract) in observations.iter_mut().zip(dependent) {
                    *value = value.sub(subtract);
                }
            }
            let variable = column * VARIABLES_PER_COLUMN + local;
            for (field_output, value) in observations.into_iter().enumerate() {
                for (coordinate, limb) in qm31_coordinates(basis.mul(value)).into_iter().enumerate()
                {
                    matrix[4 * field_output + coordinate][variable] = limb;
                }
            }
        }
    }
    for local in 0..EXPLICIT_MASK_VARIABLES {
        let row = (local * 573 + 211) & (TRACE_ROWS - 1);
        let observations =
            c1_mask_sumcheck_observations(DIRECT_RANGE_C1_COLUMN_COUNT, row, &challenges);
        for basis_coordinate in 0..4 {
            let basis = c1_mask_basis(basis_coordinate);
            let variable = C1_VARIABLES + 4 * local + basis_coordinate;
            for (field_output, value) in observations.iter().copied().enumerate() {
                for (coordinate, limb) in qm31_coordinates(basis.mul(value)).into_iter().enumerate()
                {
                    matrix[4 * field_output + coordinate][variable] = limb;
                }
            }
        }
    }
    assert_eq!(rank(matrix), OUTPUTS);
}

fn reduce_raw_view_and_collect_kernel_images(
    raw_columns: impl IntoIterator<Item = Vec<M31>>,
    mask_columns: impl IntoIterator<Item = Vec<M31>>,
    raw_outputs: usize,
) -> (usize, Vec<Vec<M31>>) {
    let mut pivots: Vec<Option<(Vec<M31>, Vec<M31>)>> = vec![None; raw_outputs];
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
                    *value = value.sub(scale.mul(*pivot_value));
                }
                continue;
            }
            let inverse = raw[pivot].inv();
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
            debug_assert!(raw.iter().all(|value| *value == M31::ZERO));
            kernel_images.push(mask);
        }
    }
    (
        pivots.iter().filter(|pivot| pivot.is_some()).count(),
        kernel_images,
    )
}

fn mask_output_coordinates(values: Vec<QM31>, basis: QM31) -> Vec<M31> {
    values
        .into_iter()
        .flat_map(|value| qm31_coordinates(basis.mul(value)))
        .collect()
}

#[test]
fn one_explicit_mask_and_c1_padding_remain_surjective_after_all_openings() {
    const C1_RAW_OUTPUTS: usize = OBSERVED_BASE_SYMBOLS + TERMINAL_M31_COORDINATES;
    const MASK_RAW_OUTPUTS: usize = 4 * (OBSERVED_BASE_SYMBOLS + 2);
    const MASK_OUTPUTS: usize =
        4 * (1 + PAYMENT_SUMCHECK_ROUNDS * PAYMENT_SUMCHECK_WIRE_COEFFICIENTS);
    const C1_VARIABLES_PER_COLUMN: usize = 192;
    const EXPLICIT_MASK_ROWS: usize = 192;

    let cells = direct_range_c1_mask_cells_v4();
    let mut available = [[false; TRACE_ROWS]; DIRECT_RANGE_C1_COLUMN_COUNT];
    for cell in cells {
        available[usize::from(cell.column)][usize::from(cell.row)] = true;
    }
    let selected_c1: [Vec<usize>; DIRECT_RANGE_C1_COLUMN_COUNT] = core::array::from_fn(|column| {
        let mut selected = Vec::with_capacity(C1_VARIABLES_PER_COLUMN);
        for local in 0..TRACE_ROWS {
            let row = (local * 573 + column * 137 + 211) & (TRACE_ROWS - 1);
            if available[column][row] {
                selected.push(row);
                if selected.len() == C1_VARIABLES_PER_COLUMN {
                    break;
                }
            }
        }
        assert_eq!(selected.len(), C1_VARIABLES_PER_COLUMN, "column={column}");
        selected
    });
    let explicit_rows = (0..EXPLICIT_MASK_ROWS)
        .map(|local| (local * 573 + 211) & (TRACE_ROWS - 1))
        .collect::<Vec<_>>();

    let mut rng = Rng(0x4a4f_494e_545f_524b);
    for schedule in 0..3 {
        let queries = distinct_queries(&mut rng);
        let z = core::array::from_fn(|_| rng.qm31());
        let shifted = xor11_point(&z);
        let challenges = core::array::from_fn(|_| rng.qm31());

        let mut needed_rows = [false; TRACE_ROWS];
        for rows in &selected_c1 {
            for &row in rows {
                needed_rows[row] = true;
                if row >= COPY_HELPER_PADDING_ROW_START {
                    needed_rows[TRACE_ROWS - 1] = true;
                }
            }
        }
        for &row in &explicit_rows {
            needed_rows[row] = true;
        }
        let encoder = CircleEncoder::new_for_domain_log(RATE16_DOMAIN_LOG);
        let mut encoded_queries: [Option<Vec<M31>>; TRACE_ROWS] = core::array::from_fn(|_| None);
        for row in 0..TRACE_ROWS {
            if !needed_rows[row] {
                continue;
            }
            let mut message = vec![M31::ZERO; TRACE_ROWS];
            message[row] = M31::ONE;
            let codeword = encoder.encode_c1_message(&message).unwrap();
            let mut samples = Vec::with_capacity(OBSERVED_BASE_SYMBOLS);
            for query in queries {
                for slot in 0..FIBER_SLOTS {
                    samples.push(codeword[FIBER_SLOTS * query + slot]);
                }
            }
            encoded_queries[row] = Some(samples);
        }

        let mut all_kernel_images = Vec::new();
        for column in 0..DIRECT_RANGE_C1_COLUMN_COUNT {
            let basis = c1_mask_basis(column);
            let mut raw_columns = Vec::with_capacity(C1_VARIABLES_PER_COLUMN);
            let mut mask_columns = Vec::with_capacity(C1_VARIABLES_PER_COLUMN);
            for &row in &selected_c1[column] {
                let dependent = (row >= COPY_HELPER_PADDING_ROW_START).then_some(TRACE_ROWS - 1);
                let mut raw = encoded_queries[row].as_ref().unwrap().clone();
                if let Some(dependent) = dependent {
                    for (value, subtract) in raw
                        .iter_mut()
                        .zip(encoded_queries[dependent].as_ref().unwrap())
                    {
                        *value = value.sub(*subtract);
                    }
                }
                for point in [&z, &shifted] {
                    let mut terminal = eq_weight(point, row);
                    if let Some(dependent) = dependent {
                        terminal = terminal.sub(eq_weight(point, dependent));
                    }
                    raw.extend(qm31_coordinates(terminal));
                }
                raw_columns.push(raw);

                let mut observations = c1_mask_sumcheck_observations(column, row, &challenges);
                if let Some(dependent) = dependent {
                    let dependent_observations =
                        c1_mask_sumcheck_observations(column, dependent, &challenges);
                    for (value, subtract) in observations.iter_mut().zip(dependent_observations) {
                        *value = value.sub(subtract);
                    }
                }
                mask_columns.push(mask_output_coordinates(observations, basis));
            }
            let (raw_rank, kernel_images) = reduce_raw_view_and_collect_kernel_images(
                raw_columns,
                mask_columns,
                C1_RAW_OUTPUTS,
            );
            assert_eq!(
                raw_rank, C1_RAW_OUTPUTS,
                "schedule={schedule}, column={column}"
            );
            all_kernel_images.extend(kernel_images);
        }

        let mut raw_columns = Vec::with_capacity(4 * EXPLICIT_MASK_ROWS);
        let mut mask_columns = Vec::with_capacity(4 * EXPLICIT_MASK_ROWS);
        for &row in &explicit_rows {
            let observations =
                c1_mask_sumcheck_observations(DIRECT_RANGE_C1_COLUMN_COUNT, row, &challenges);
            for basis_coordinate in 0..4 {
                let basis = c1_mask_basis(basis_coordinate);
                let mut raw = Vec::with_capacity(MASK_RAW_OUTPUTS);
                for coefficient in encoded_queries[row].as_ref().unwrap() {
                    raw.extend(qm31_coordinates(basis.mul_m31(*coefficient)));
                }
                for point in [&z, &shifted] {
                    raw.extend(qm31_coordinates(basis.mul(eq_weight(point, row))));
                }
                raw_columns.push(raw);
                mask_columns.push(mask_output_coordinates(observations.clone(), basis));
            }
        }
        let (raw_rank, kernel_images) =
            reduce_raw_view_and_collect_kernel_images(raw_columns, mask_columns, MASK_RAW_OUTPUTS);
        assert_eq!(raw_rank, MASK_RAW_OUTPUTS, "schedule={schedule}");
        all_kernel_images.extend(kernel_images);

        let mut conditioned = vec![vec![M31::ZERO; all_kernel_images.len()]; MASK_OUTPUTS];
        for (column, image) in all_kernel_images.into_iter().enumerate() {
            assert_eq!(image.len(), MASK_OUTPUTS);
            for (row, value) in image.into_iter().enumerate() {
                conditioned[row][column] = value;
            }
        }
        assert_eq!(
            rank(conditioned),
            MASK_OUTPUTS,
            "conditioned mask image rank deficient for schedule {schedule}"
        );
    }
}
