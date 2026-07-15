//! Frozen nonzero witness for the joint `(q,z)` liveness route.
//!
//! This module (and its `profile22_*` file/identifier names) is live spend
//! code: the GoodSpend predicate's root-neutral polynomial-kernel rank probe
//! lives here. The historical names are retained because the rank-minor
//! block labels in this file are hashed into frozen provenance anchors that
//! the release certificates and known-answer tests pin.
//!
//! This diagnostic uses only the common natural-basis tail `896..=1023`.
//! For a distinct q16 tuple its query kernel is parameterized without
//! Gaussian denominators as `g_q(t) h(t)` in the four `{1,x,y,xy}` sectors.
//! The one inactive-sum equation leaves 63 M31 sources per lane.  The probe
//! asks whether those explicit polynomial sources already span the 324 raw
//! terminal coordinates plus the 1,080-dimensional compressed-sumcheck
//! terminal kernel at the frozen schedule.

use super::*;

const COMMON_TAIL_START: usize = 896;
const COMMON_NATURAL_BLOCKS: usize = 32;
const FULL_NATURAL_BLOCKS: usize = TRACE_ROWS / SECTORS;
const SECTORS: usize = 4;
const Q_KERNEL_DEGREE: usize = 16;
const BALANCED_SOURCES_PER_LANE: usize = SECTORS * Q_KERNEL_DEGREE - 1;
const M31_LANES: usize = STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
const RAW_TERMINAL_M31_PER_LANE: usize = 3 * 4;
const RAW_TERMINAL_M31: usize = (M31_LANES + 1) * RAW_TERMINAL_M31_PER_LANE;
const FULL_SC_M31: usize = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
const JOINT_ROWS_M31: usize = RAW_TERMINAL_M31 + FULL_SC_M31;
const EXPECTED_JOINT_RANK_M31: usize = RAW_TERMINAL_M31 + MASK_SUMCHECK_QUOTIENT_M31;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Profile22PolynomialKernelRankReport {
    pub query_count: usize,
    pub query_roots_distinct: bool,
    pub query_root_one_excluded: bool,
    pub common_tail_start: usize,
    pub common_tail_rows: usize,
    pub sectors: usize,
    pub h_degree_bound: usize,
    pub balanced_sources_per_lane_m31: usize,
    pub m31_lanes: usize,
    pub g_tower_coordinates: usize,
    pub source_columns_m31: usize,
    pub raw_terminal_rows_m31: usize,
    pub full_sumcheck_rows_m31: usize,
    pub joint_rows_m31: usize,
    pub expected_joint_rank_m31: usize,
    pub measured_joint_rank_m31: usize,
    pub complete: bool,
    pub minor: RankMinorProvenance,
    pub q_individual_degree_bound: usize,
    pub q_total_degree_bound: usize,
    pub z_total_degree_bound: usize,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Profile22MixedPolynomialKernelRankReport {
    pub query_count: usize,
    pub query_roots_distinct: bool,
    pub query_root_one_excluded: bool,
    pub semantic_lanes: usize,
    pub semantic_common_tail_sources_per_lane_m31: usize,
    pub full_domain_lanes: usize,
    pub full_domain_raw_kernel_per_lane_m31: usize,
    pub full_domain_balanced_sources_per_lane_m31: usize,
    pub potential_source_columns_m31: usize,
    pub processed_source_columns_m31: usize,
    pub raw_terminal_rows_m31: usize,
    pub full_sumcheck_rows_m31: usize,
    pub joint_rows_m31: usize,
    pub expected_joint_rank_m31: usize,
    pub measured_joint_rank_m31: usize,
    pub terminal_projection_rank_m31: usize,
    pub terminal_conditioned_sumcheck_rank_m31: usize,
    pub terminal_and_initial_projection_rank_m31: usize,
    pub initial_neutral_conditioned_sumcheck_rank_m31: usize,
    pub initial_neutral_target_rank_m31: usize,
    pub joint_complete: bool,
    pub initial_neutral_complete: bool,
    pub full_domain_balance_reference: usize,
    pub full_domain_balance_denominator_nonzero: bool,
    pub selected_semantic_columns_in_minor: usize,
    pub selected_full_domain_columns_in_minor: usize,
    pub minor: RankMinorProvenance,
    pub q_numerator_individual_degree_bound: usize,
    pub q_numerator_total_degree_bound: usize,
    pub q_denominator_individual_degree_bound: usize,
    pub q_denominator_total_degree_bound: usize,
    pub z_total_degree_bound: usize,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Profile22RootNeutralPolynomialKernelRankReport {
    pub query_count: usize,
    pub gamma_nonzero: bool,
    pub generator_order: &'static str,
    pub semantic_lanes: usize,
    pub mask_only_lanes: usize,
    pub d_tower_coordinates: usize,
    pub semantic_sources_per_lane_m31: usize,
    pub mask_only_sources_per_lane_m31: usize,
    pub d_sources_per_coordinate_m31: usize,
    pub potential_source_columns_m31: usize,
    pub processed_source_columns_m31: usize,
    pub serialized_terminal_rows_m31: usize,
    pub terminal_projection_rank_m31: usize,
    pub d_terminal_projection_rank_m31: usize,
    pub terminal_conditioned_sumcheck_rank_m31: usize,
    pub terminal_and_initial_projection_rank_m31: usize,
    pub root_neutral_conditioned_sumcheck_rank_m31: usize,
    pub root_neutral_target_rank_m31: usize,
    pub joint_rank_m31: usize,
    pub joint_target_rank_m31: usize,
    pub pointwise_root_zero_sources_checked_m31: usize,
    pub every_source_pointwise_root_zero: bool,
    pub selected_semantic_columns_by_lane: Vec<usize>,
    pub selected_mask_only_columns_by_lane: Vec<usize>,
    pub selected_d_columns: usize,
    pub selected_degree_one_q_columns: usize,
    pub selected_degree_two_q_columns: usize,
    pub minor: RankMinorProvenance,
    pub q_individual_degree_bound: usize,
    pub q_total_degree_bound: usize,
    pub gamma_inverse_norm_denominator_exponent: usize,
    pub gamma_coordinate_total_degree_bound: usize,
    pub z_total_degree_bound: usize,
    pub minimum_selector_count_for_cap16_over_100_bits: usize,
    pub complete: bool,
    pub elapsed_millis: u128,
}

fn polynomial_mul(left: &[M31], right: &[M31], capacity: usize) -> Vec<M31> {
    let mut out = vec![M31::ZERO; capacity];
    for (i, &a) in left.iter().enumerate() {
        for (j, &b) in right.iter().enumerate() {
            if i + j < capacity {
                out[i + j] = out[i + j].add(a.mul(b));
            }
        }
    }
    out
}

fn natural_t_polynomials(capacity: usize) -> Vec<Vec<M31>> {
    debug_assert!(capacity.is_power_of_two());
    let bits = capacity.trailing_zeros() as usize;
    let mut chebyshev_powers = Vec::with_capacity(bits);
    chebyshev_powers.push({
        let mut t = vec![M31::ZERO; capacity];
        t[1] = M31::ONE;
        t
    });
    for bit in 1..bits {
        let previous = &chebyshev_powers[bit - 1];
        let square = polynomial_mul(previous, previous, capacity);
        let mut next = square
            .into_iter()
            .map(|coefficient| coefficient.double())
            .collect::<Vec<_>>();
        next[0] = next[0].sub(M31::ONE);
        chebyshev_powers.push(next);
    }
    (0..capacity)
        .map(|index| {
            let mut polynomial = vec![M31::ZERO; capacity];
            polynomial[0] = M31::ONE;
            for (bit, factor) in chebyshev_powers.iter().enumerate() {
                if index & (1 << bit) != 0 {
                    polynomial = polynomial_mul(&polynomial, factor, capacity);
                }
            }
            polynomial
        })
        .collect()
}

fn ordinary_to_natural(ordinary: &[M31], natural_polynomials: &[Vec<M31>]) -> Vec<M31> {
    let capacity = natural_polynomials.len();
    let mut remainder = ordinary.to_vec();
    remainder.resize(capacity, M31::ZERO);
    let mut natural = vec![M31::ZERO; capacity];
    for degree in (0..capacity).rev() {
        let leading = natural_polynomials[degree][degree];
        debug_assert_ne!(leading, M31::ZERO);
        let coefficient = remainder[degree].mul(leading.inv());
        natural[degree] = coefficient;
        if coefficient != M31::ZERO {
            for (value, &basis) in remainder.iter_mut().zip(&natural_polynomials[degree]) {
                *value = value.sub(coefficient.mul(basis));
            }
        }
    }
    debug_assert!(remainder.iter().all(|value| *value == M31::ZERO));
    natural
}

fn query_root(
    schedule: &StateOnlyTranscriptScheduleResult,
    query: usize,
) -> Result<M31, StateOnlyHidingRankGateError> {
    let point = aspis_core::circle_fri::circle_fiber_point_for_domain_log(
        STATE_ONLY_LOG_ROWS + 9,
        schedule.queries[query] as usize,
    )
    .map_err(|_| StateOnlyHidingRankGateError::Encoding)?;
    Ok(point.x.mul(point.x).double().sub(M31::ONE))
}

fn balanced_query_kernel_sources(
    roots: &[M31],
) -> Result<Vec<Vec<M31>>, StateOnlyHidingRankGateError> {
    let query_degree = roots.len();
    if query_degree == 0 || query_degree >= COMMON_NATURAL_BLOCKS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut g = vec![M31::ONE];
    for &root in roots {
        g = polynomial_mul(&g, &[M31::ZERO.sub(root), M31::ONE], query_degree + 1);
    }
    if g.len() != query_degree + 1 || g[query_degree] != M31::ONE {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let g_at_one = g.iter().copied().fold(M31::ZERO, M31::add);
    if g_at_one == M31::ZERO {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let natural_polynomials = natural_t_polynomials(COMMON_NATURAL_BLOCKS);
    let h_degree_bound = COMMON_NATURAL_BLOCKS - query_degree;
    let h_sources = (0..SECTORS)
        .flat_map(|sector| {
            let natural_polynomials = &natural_polynomials;
            let g = &g;
            (0..h_degree_bound).map(move |degree| {
                let mut ordinary = vec![M31::ZERO; COMMON_NATURAL_BLOCKS];
                ordinary[degree..degree + g.len()].copy_from_slice(g);
                let natural = ordinary_to_natural(&ordinary, natural_polynomials);
                let mut source = vec![M31::ZERO; COMMON_NATURAL_BLOCKS * SECTORS];
                for (block, coefficient) in natural.into_iter().enumerate() {
                    source[SECTORS * block + sector] = coefficient;
                }
                source
            })
        })
        .collect::<Vec<_>>();
    if h_sources.len() != SECTORS * h_degree_bound {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let reference = h_sources
        .last()
        .ok_or(StateOnlyHidingRankGateError::Shape)?;
    let balanced = h_sources[..h_sources.len() - 1]
        .iter()
        .map(|source| {
            source
                .iter()
                .zip(reference)
                .map(|(&value, &subtract)| value.sub(subtract))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    if balanced.len() + 1 != SECTORS * h_degree_bound
        || balanced
            .iter()
            .any(|source| source.iter().copied().fold(M31::ZERO, M31::add) != M31::ZERO)
    {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    Ok(balanced)
}

fn full_domain_balanced_query_kernel_sources(
    roots: &[M31],
    active: &[bool; TRACE_ROWS],
) -> Result<(Vec<Vec<M31>>, usize, M31), StateOnlyHidingRankGateError> {
    let query_degree = roots.len();
    if query_degree == 0 || query_degree >= FULL_NATURAL_BLOCKS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let mut g = vec![M31::ONE];
    for &root in roots {
        g = polynomial_mul(&g, &[M31::ZERO.sub(root), M31::ONE], query_degree + 1);
    }
    if g.len() != query_degree + 1 || g[query_degree] != M31::ONE {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let natural_polynomials = natural_t_polynomials(FULL_NATURAL_BLOCKS);
    let h_degree_bound = FULL_NATURAL_BLOCKS - query_degree;
    let raw_kernel = (0..SECTORS)
        .flat_map(|sector| {
            let natural_polynomials = &natural_polynomials;
            let g = &g;
            (0..h_degree_bound).map(move |degree| {
                let mut ordinary = vec![M31::ZERO; FULL_NATURAL_BLOCKS];
                ordinary[degree..degree + g.len()].copy_from_slice(g);
                let natural = ordinary_to_natural(&ordinary, natural_polynomials);
                let mut source = vec![M31::ZERO; TRACE_ROWS];
                for (block, coefficient) in natural.into_iter().enumerate() {
                    source[SECTORS * block + sector] = coefficient;
                }
                source
            })
        })
        .collect::<Vec<_>>();
    let expected_raw_kernel = SECTORS * h_degree_bound;
    if raw_kernel.len() != expected_raw_kernel {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let inactive_sum = |source: &[M31]| {
        source
            .iter()
            .enumerate()
            .filter(|(row, _)| !active[*row])
            .fold(M31::ZERO, |sum, (_, &coefficient)| sum.add(coefficient))
    };
    let sums = raw_kernel
        .iter()
        .map(|source| inactive_sum(source))
        .collect::<Vec<_>>();
    // Select one nonzero inactive-sum anchor at the frozen point.  The emitted
    // frame below clears that q-dependent scalar and is polynomial, not
    // rational.  Each cleared column has degree at most two per q root.
    // Reference zero is part of the frozen polynomial-frame definition.  It
    // must not be selected adaptively from q, because that would destroy the
    // fixed-minor argument.  At the one pinned witness point it is nonzero;
    // at other q values a zero merely makes the fixed polynomial minor vanish
    // and is already covered by its degree bound.
    let reference = 0usize;
    if sums[reference] == M31::ZERO {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let denominator = sums[reference];
    let reference_source = &raw_kernel[reference];
    // Clear the common balance denominator in every column.  The resulting
    // source is exactly `s_ref*v - s_v*v_ref`: it remains in the query kernel
    // and physical inactive-sum kernel, and is polynomial of degree at most
    // two in each q root.  No rational denominator remains in the minor.
    let balanced = raw_kernel
        .iter()
        .zip(&sums)
        .enumerate()
        .filter(|(index, _)| *index != reference)
        .map(|(_, (source, &sum))| {
            source
                .iter()
                .zip(reference_source)
                .map(|(&value, &subtract)| denominator.mul(value).sub(sum.mul(subtract)))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    if balanced.len() + 1 != expected_raw_kernel
        || balanced
            .iter()
            .any(|source| inactive_sum(source) != M31::ZERO)
    {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    Ok((balanced, reference, denominator))
}

fn terminal_values(source: &[M31], terminal_rows: &[[QM31; 3]]) -> [QM31; 3] {
    let mut values = [QM31::ZERO; 3];
    for (&coefficient, row) in source.iter().zip(terminal_rows) {
        for point in 0..3 {
            values[point] = values[point].add(row[point].mul_m31(coefficient));
        }
    }
    values
}

fn combined_observations(source: &[M31], observations: &[Vec<QM31>], scale: QM31) -> Vec<QM31> {
    let mut combined = vec![QM31::ZERO; STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS];
    for (&coefficient, row) in source.iter().zip(observations) {
        if coefficient == M31::ZERO {
            continue;
        }
        let coefficient = scale.mul_m31(coefficient);
        for (value, &entry) in combined.iter_mut().zip(row) {
            *value = value.add(coefficient.mul(entry));
        }
    }
    combined
}

/// Rank the explicit denominator-free `g_q h` common-tail source frame.
///
/// A green result is a machine witness that one fixed 1,404-column minor is
/// a nonzero polynomial in the sixteen query roots and forty M31 coordinates
/// of `z`.  It is not an all-q theorem and it does not prove the later PCS
/// continuation implication used by the strong Good22 gate.
pub fn probe_profile22_common_tail_polynomial_kernel_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Profile22PolynomialKernelRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != Q_KERNEL_DEGREE {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let roots = (0..Q_KERNEL_DEGREE)
        .map(|query| query_root(schedule, query))
        .collect::<Result<Vec<_>, _>>()?;
    let mut distinct = roots.clone();
    distinct.sort_by_key(|value| value.0);
    distinct.dedup();
    let query_roots_distinct = distinct.len() == roots.len();
    let query_root_one_excluded = roots.iter().all(|root| *root != M31::ONE);
    if !query_roots_distinct || !query_root_one_excluded {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let sources = balanced_query_kernel_sources(&roots)?;
    let terminal_points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let terminal_rows = (COMMON_TAIL_START..TRACE_ROWS)
        .map(|row| core::array::from_fn(|point| eq_weight(&terminal_points[point], row)))
        .collect::<Vec<_>>();
    let lagrange = lagrange_basis();
    let factors = (0..M31_LANES)
        .map(|lane| {
            if lane < STATE_ONLY_HIDING_C1_COLUMNS {
                MaskFactor::Semantic(lane)
            } else {
                MaskFactor::MaskOnly(lane - STATE_ONLY_HIDING_C1_COLUMNS)
            }
        })
        .collect::<Vec<_>>();
    let factor_observations = factors
        .iter()
        .map(|&factor| {
            (COMMON_TAIL_START..TRACE_ROWS)
                .map(|row| {
                    mask_sumcheck_observations(
                        row,
                        &schedule.prefix.z,
                        &lagrange,
                        factor,
                        FactorSchedule::FullSharedLinear,
                        None,
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let g_observations = (COMMON_TAIL_START..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::FullSharedLinear,
                None,
            )
        })
        .collect::<Vec<_>>();

    let mut echelon = ColumnEchelon::new(JOINT_ROWS_M31);
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();
    let mut source_id = 0usize;
    let mut insert = |lane: usize, source: &[M31], observations: &[Vec<QM31>], scale: QM31| {
        let mut column = vec![M31::ZERO; JOINT_ROWS_M31];
        let terminal = terminal_values(source, &terminal_rows);
        let terminal_start = lane * RAW_TERMINAL_M31_PER_LANE;
        for (point, value) in terminal.into_iter().enumerate() {
            let value = scale.mul(value);
            column[terminal_start + 4 * point..terminal_start + 4 * point + 4]
                .copy_from_slice(&qm31_coordinates(value));
        }
        let combined = combined_observations(source, observations, scale);
        let mut sc = Vec::with_capacity(FULL_SC_M31);
        append_qm31_coordinates(&mut sc, combined);
        column[RAW_TERMINAL_M31..].copy_from_slice(&sc);
        if let Some((pivot, value)) = echelon.insert_with_pivot_value(column) {
            minor_sources.push(source_id);
            minor_rows.push(pivot);
            minor_values.push(value);
        }
        source_id += 1;
    };
    for (lane, observations) in factor_observations.iter().enumerate() {
        for source in &sources {
            insert(lane, source, observations, QM31::ONE);
        }
    }
    for coordinate in 0..4 {
        let scale = state_only_mask_tower_basis(coordinate);
        for source in &sources {
            insert(M31_LANES, source, &g_observations, scale);
        }
    }
    let expected_sources = (M31_LANES + 4) * BALANCED_SOURCES_PER_LANE;
    if source_id != expected_sources || echelon.rank > EXPECTED_JOINT_RANK_M31 {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let minor = RankMinorProvenance::from_parts(
        "profile22_common_tail_terminal324_sc1080",
        minor_sources,
        minor_rows,
        minor_values,
    );
    Ok(Profile22PolynomialKernelRankReport {
        query_count: schedule.query_count,
        query_roots_distinct,
        query_root_one_excluded,
        common_tail_start: COMMON_TAIL_START,
        common_tail_rows: TRACE_ROWS - COMMON_TAIL_START,
        sectors: SECTORS,
        h_degree_bound: Q_KERNEL_DEGREE,
        balanced_sources_per_lane_m31: BALANCED_SOURCES_PER_LANE,
        m31_lanes: M31_LANES,
        g_tower_coordinates: 4,
        source_columns_m31: source_id,
        raw_terminal_rows_m31: RAW_TERMINAL_M31,
        full_sumcheck_rows_m31: FULL_SC_M31,
        joint_rows_m31: JOINT_ROWS_M31,
        expected_joint_rank_m31: EXPECTED_JOINT_RANK_M31,
        measured_joint_rank_m31: echelon.rank,
        complete: echelon.rank == EXPECTED_JOINT_RANK_M31,
        minor,
        q_individual_degree_bound: EXPECTED_JOINT_RANK_M31,
        q_total_degree_bound: Q_KERNEL_DEGREE * EXPECTED_JOINT_RANK_M31,
        z_total_degree_bound: 41_040,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Rank the mixed structured source frame requested by the Good22 liveness
/// screen.  Semantic lanes retain the universally relation-free common tail;
/// the ten mask-only M31 lanes and four tower coordinates of G use the full
/// global `g_q(t)h(t)` raw kernel, intersected with the exact inactive-sum
/// hyperplane.
///
/// The full-domain intersection uses the explicitly cleared polynomial frame
/// `s_ref*v - s_v*v_ref`, of degree at most two in each q root.  A green
/// numeric result is still not, by itself, a Good22 continuation theorem.
pub fn probe_profile22_mixed_polynomial_kernel_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Profile22MixedPolynomialKernelRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if schedule.query_count != Q_KERNEL_DEGREE {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let roots = (0..Q_KERNEL_DEGREE)
        .map(|query| query_root(schedule, query))
        .collect::<Result<Vec<_>, _>>()?;
    let mut distinct = roots.clone();
    distinct.sort_by_key(|value| value.0);
    distinct.dedup();
    let query_roots_distinct = distinct.len() == roots.len();
    let query_root_one_excluded = roots.iter().all(|root| *root != M31::ONE);
    if !query_roots_distinct || !query_root_one_excluded {
        return Err(StateOnlyHidingRankGateError::Relation);
    }

    let common_sources = balanced_query_kernel_sources(&roots)?;
    let mut active = [false; TRACE_ROWS];
    for &row in rank_active_rows(RankLayout::AtomicV3) {
        active[usize::from(row)] = true;
    }
    let (full_sources, balance_reference, balance_denominator) =
        full_domain_balanced_query_kernel_sources(&roots, &active)?;
    let full_raw_kernel_per_lane = SECTORS * (FULL_NATURAL_BLOCKS - Q_KERNEL_DEGREE);
    if full_sources.len() + 1 != full_raw_kernel_per_lane {
        return Err(StateOnlyHidingRankGateError::Relation);
    }

    let terminal_points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let tail_terminal_rows = (COMMON_TAIL_START..TRACE_ROWS)
        .map(|row| core::array::from_fn(|point| eq_weight(&terminal_points[point], row)))
        .collect::<Vec<_>>();
    let full_terminal_rows = (0..TRACE_ROWS)
        .map(|row| core::array::from_fn(|point| eq_weight(&terminal_points[point], row)))
        .collect::<Vec<_>>();
    let lagrange = lagrange_basis();

    let mut joint = ColumnEchelon::new(JOINT_ROWS_M31);
    let mut terminal_projection = ColumnEchelon::new(RAW_TERMINAL_M31);
    let mut terminal_and_initial_projection = ColumnEchelon::new(RAW_TERMINAL_M31 + 4);
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();
    let mut selected_semantic = 0usize;
    let mut selected_full = 0usize;
    let mut source_id = 0usize;

    let mut insert = |lane: usize,
                      source: &[M31],
                      terminal_rows: &[[QM31; 3]],
                      observations: &[Vec<QM31>],
                      scale: QM31,
                      full_domain: bool| {
        let mut terminal_column = vec![M31::ZERO; RAW_TERMINAL_M31];
        let terminal = terminal_values(source, terminal_rows);
        let terminal_start = lane * RAW_TERMINAL_M31_PER_LANE;
        for (point, value) in terminal.into_iter().enumerate() {
            let value = scale.mul(value);
            terminal_column[terminal_start + 4 * point..terminal_start + 4 * point + 4]
                .copy_from_slice(&qm31_coordinates(value));
        }
        let combined = combined_observations(source, observations, scale);
        let mut sc = Vec::with_capacity(FULL_SC_M31);
        append_qm31_coordinates(&mut sc, combined);

        terminal_projection.insert(terminal_column.clone());
        let mut root_projection = terminal_column.clone();
        root_projection.extend_from_slice(&sc[..4]);
        terminal_and_initial_projection.insert(root_projection);

        let mut joint_column = terminal_column;
        joint_column.extend_from_slice(&sc);
        if let Some((pivot, value)) = joint.insert_with_pivot_value(joint_column) {
            minor_sources.push(source_id);
            minor_rows.push(pivot);
            minor_values.push(value);
            if full_domain {
                selected_full += 1;
            } else {
                selected_semantic += 1;
            }
        }
        source_id += 1;
        joint.rank == EXPECTED_JOINT_RANK_M31
            && terminal_projection.rank == RAW_TERMINAL_M31
            && terminal_and_initial_projection.rank == RAW_TERMINAL_M31 + 4
    };

    'semantic: for lane in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        let observations = (COMMON_TAIL_START..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(lane),
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        for source in &common_sources {
            if insert(
                lane,
                source,
                &tail_terminal_rows,
                &observations,
                QM31::ONE,
                false,
            ) {
                break 'semantic;
            }
        }
    }

    'full: for mask_lane in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_lane),
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let lane = STATE_ONLY_HIDING_C1_COLUMNS + mask_lane;
        for source in &full_sources {
            if insert(
                lane,
                source,
                &full_terminal_rows,
                &observations,
                QM31::ONE,
                true,
            ) {
                break 'full;
            }
        }
    }

    let observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::FullSharedLinear,
                None,
            )
        })
        .collect::<Vec<_>>();
    'g: for coordinate in 0..4 {
        let scale = state_only_mask_tower_basis(coordinate);
        for source in &full_sources {
            if insert(
                M31_LANES,
                source,
                &full_terminal_rows,
                &observations,
                scale,
                true,
            ) {
                break 'g;
            }
        }
    }
    drop(insert);

    let terminal_conditioned_sumcheck_rank = joint.rank.saturating_sub(terminal_projection.rank);
    let initial_neutral_conditioned_sumcheck_rank = joint
        .rank
        .saturating_sub(terminal_and_initial_projection.rank);
    let initial_neutral_target = MASK_SUMCHECK_QUOTIENT_M31 - 4;
    let minor = RankMinorProvenance::from_parts(
        "profile22_mixed_polynomial_kernel_terminal324_sc1080",
        minor_sources,
        minor_rows,
        minor_values,
    );
    let q_numerator_individual_degree_bound = selected_semantic + 2 * selected_full;
    Ok(Profile22MixedPolynomialKernelRankReport {
        query_count: schedule.query_count,
        query_roots_distinct,
        query_root_one_excluded,
        semantic_lanes: STATE_ONLY_HIDING_C1_COLUMNS,
        semantic_common_tail_sources_per_lane_m31: common_sources.len(),
        full_domain_lanes: STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 4,
        full_domain_raw_kernel_per_lane_m31: full_raw_kernel_per_lane,
        full_domain_balanced_sources_per_lane_m31: full_sources.len(),
        potential_source_columns_m31: STATE_ONLY_HIDING_C1_COLUMNS * common_sources.len()
            + (STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 4) * full_sources.len(),
        processed_source_columns_m31: source_id,
        raw_terminal_rows_m31: RAW_TERMINAL_M31,
        full_sumcheck_rows_m31: FULL_SC_M31,
        joint_rows_m31: JOINT_ROWS_M31,
        expected_joint_rank_m31: EXPECTED_JOINT_RANK_M31,
        measured_joint_rank_m31: joint.rank,
        terminal_projection_rank_m31: terminal_projection.rank,
        terminal_conditioned_sumcheck_rank_m31: terminal_conditioned_sumcheck_rank,
        terminal_and_initial_projection_rank_m31: terminal_and_initial_projection.rank,
        initial_neutral_conditioned_sumcheck_rank_m31: initial_neutral_conditioned_sumcheck_rank,
        initial_neutral_target_rank_m31: initial_neutral_target,
        joint_complete: joint.rank == EXPECTED_JOINT_RANK_M31,
        initial_neutral_complete: terminal_and_initial_projection.rank == RAW_TERMINAL_M31 + 4
            && initial_neutral_conditioned_sumcheck_rank == initial_neutral_target,
        full_domain_balance_reference: balance_reference,
        full_domain_balance_denominator_nonzero: balance_denominator != M31::ZERO,
        selected_semantic_columns_in_minor: selected_semantic,
        selected_full_domain_columns_in_minor: selected_full,
        minor,
        q_numerator_individual_degree_bound,
        q_numerator_total_degree_bound: Q_KERNEL_DEGREE * q_numerator_individual_degree_bound,
        q_denominator_individual_degree_bound: 0,
        q_denominator_total_degree_bound: 0,
        z_total_degree_bound: 41_040,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Frozen polynomial-kernel witness for the true D-after-G root-neutral map.
///
/// Generator indices remain `semantic 0..15`, `mask-only 16..25`, `H=26`,
/// `G=27`, and the new full-domain zero-factor QM31 lane is `D=28`.
/// Existing M31 sources are paired pointwise into G by
/// `Delta G = -gamma^(j-27) Delta C_j`; D sources use
/// `Delta G = -gamma Delta D`.  Hence the gamma-combined root message is
/// identically zero before any PCS continuation.
pub fn probe_profile22_root_neutral_polynomial_kernel_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<Profile22RootNeutralPolynomialKernelRankReport, StateOnlyHidingRankGateError> {
    const G_GENERATOR: usize = 27;
    const D_GENERATOR: usize = 28;
    const G_TERMINAL_LANE: usize = 26;
    const D_TERMINAL_LANE: usize = 27;
    const TERMINAL_LANES: usize = 28;
    const SERIALIZED_TERMINAL_M31: usize = TERMINAL_LANES * RAW_TERMINAL_M31_PER_LANE;
    const ROOT_JOINT_ROWS_M31: usize = SERIALIZED_TERMINAL_M31 + FULL_SC_M31;
    const ROOT_JOINT_TARGET_M31: usize = RAW_TERMINAL_M31 + MASK_SUMCHECK_QUOTIENT_M31;
    const ROOT_INITIAL_TARGET_M31: usize = MASK_SUMCHECK_QUOTIENT_M31 - 4;

    let started = Instant::now();
    if !matches!(schedule.query_count, 16 | 18) || schedule.prefix.gamma == QM31::ZERO {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let roots = (0..schedule.query_count)
        .map(|query| query_root(schedule, query))
        .collect::<Result<Vec<_>, _>>()?;
    let mut distinct = roots.clone();
    distinct.sort_by_key(|value| value.0);
    distinct.dedup();
    if distinct.len() != roots.len() || roots.iter().any(|root| *root == M31::ONE) {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let common_sources = balanced_query_kernel_sources(&roots)?;
    let mut active = [false; TRACE_ROWS];
    for &row in rank_active_rows(RankLayout::AtomicV3) {
        active[usize::from(row)] = true;
    }
    let (full_sources, _, balance_anchor) =
        full_domain_balanced_query_kernel_sources(&roots, &active)?;
    if balance_anchor == M31::ZERO {
        return Err(StateOnlyHidingRankGateError::Relation);
    }

    let terminal_points = [
        schedule.prefix.z,
        binary_successor_point(&schedule.prefix.z),
        xor12_point(&schedule.prefix.z),
    ];
    let tail_terminal_rows = (COMMON_TAIL_START..TRACE_ROWS)
        .map(|row| core::array::from_fn(|point| eq_weight(&terminal_points[point], row)))
        .collect::<Vec<_>>();
    let full_terminal_rows = (0..TRACE_ROWS)
        .map(|row| core::array::from_fn(|point| eq_weight(&terminal_points[point], row)))
        .collect::<Vec<_>>();
    let lagrange = lagrange_basis();
    let g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::FullSharedLinear,
                None,
            )
        })
        .collect::<Vec<_>>();

    let gamma = schedule.prefix.gamma;
    let gamma_g = gamma_power(gamma, G_GENERATOR);
    let gamma_d = gamma_power(gamma, D_GENERATOR);
    let mut joint = ColumnEchelon::new(ROOT_JOINT_ROWS_M31);
    let mut terminal_projection = ColumnEchelon::new(SERIALIZED_TERMINAL_M31);
    let mut terminal_and_initial_projection = ColumnEchelon::new(SERIALIZED_TERMINAL_M31 + 4);
    let mut d_terminal_projection = ColumnEchelon::new(RAW_TERMINAL_M31_PER_LANE);
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();
    let mut selected_semantic = vec![0usize; STATE_ONLY_HIDING_C1_COLUMNS];
    let mut selected_mask_only = vec![0usize; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS];
    let mut selected_d = 0usize;
    let mut selected_degree_one = 0usize;
    let mut selected_degree_two = 0usize;
    let mut gamma_denominator_exponent = 0usize;
    let mut gamma_degree = 0usize;
    let mut source_id = 0usize;
    let mut pointwise_checked = 0usize;
    let mut pointwise_guard = true;

    // kind: 0 semantic, 1 mask-only, 2 D.
    let mut insert = |kind: u8,
                      lane: usize,
                      primary_terminal_lane: usize,
                      primary_scale: QM31,
                      g_scale: QM31,
                      q_degree: usize,
                      gamma_inverse_exponent: usize,
                      root_zero: bool,
                      source: &[M31],
                      terminal_rows: &[[QM31; 3]],
                      observations: &[Vec<QM31>]| {
        pointwise_checked += 1;
        pointwise_guard &= root_zero;
        let terminal = terminal_values(source, terminal_rows);
        let mut terminal_column = vec![M31::ZERO; SERIALIZED_TERMINAL_M31];
        let mut d_terminal = vec![M31::ZERO; RAW_TERMINAL_M31_PER_LANE];
        for (point, value) in terminal.into_iter().enumerate() {
            let primary = primary_scale.mul(value);
            let g = g_scale.mul(value);
            terminal_column[primary_terminal_lane * RAW_TERMINAL_M31_PER_LANE + 4 * point
                ..primary_terminal_lane * RAW_TERMINAL_M31_PER_LANE + 4 * point + 4]
                .copy_from_slice(&qm31_coordinates(primary));
            terminal_column[G_TERMINAL_LANE * RAW_TERMINAL_M31_PER_LANE + 4 * point
                ..G_TERMINAL_LANE * RAW_TERMINAL_M31_PER_LANE + 4 * point + 4]
                .copy_from_slice(&qm31_coordinates(g));
            if kind == 2 {
                d_terminal[4 * point..4 * point + 4].copy_from_slice(&qm31_coordinates(primary));
            }
        }
        if kind == 2 {
            d_terminal_projection.insert(d_terminal);
        }
        let combined = combined_observations(source, observations, QM31::ONE);
        let mut sc = Vec::with_capacity(FULL_SC_M31);
        append_qm31_coordinates(&mut sc, combined);
        terminal_projection.insert(terminal_column.clone());
        let mut initial_projection = terminal_column.clone();
        initial_projection.extend_from_slice(&sc[..4]);
        terminal_and_initial_projection.insert(initial_projection);
        let mut joint_column = terminal_column;
        joint_column.extend_from_slice(&sc);
        if let Some((pivot, value)) = joint.insert_with_pivot_value(joint_column) {
            minor_sources.push(source_id);
            minor_rows.push(pivot);
            minor_values.push(value);
            match kind {
                0 => selected_semantic[lane] += 1,
                1 => selected_mask_only[lane] += 1,
                2 => selected_d += 1,
                _ => unreachable!(),
            }
            if q_degree == 1 {
                selected_degree_one += 1;
            } else if q_degree == 2 {
                selected_degree_two += 1;
            }
            gamma_denominator_exponent += gamma_inverse_exponent;
            gamma_degree += if kind == 2 {
                1
            } else {
                4 * gamma_inverse_exponent
            };
        }
        source_id += 1;
        joint.rank == ROOT_JOINT_TARGET_M31
            && terminal_projection.rank == RAW_TERMINAL_M31
            && terminal_and_initial_projection.rank == RAW_TERMINAL_M31 + 4
            && d_terminal_projection.rank == RAW_TERMINAL_M31_PER_LANE
    };

    'semantic: for lane in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        let inverse_exponent = G_GENERATOR - lane;
        let ratio = gamma_power(gamma, inverse_exponent).inv();
        let g_scale = QM31::ZERO.sub(ratio);
        let root_zero = gamma_power(gamma, lane).add(gamma_g.mul(g_scale)) == QM31::ZERO;
        let observations = (COMMON_TAIL_START..TRACE_ROWS)
            .map(|row| {
                let factor = mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(lane),
                    FactorSchedule::FullSharedLinear,
                    None,
                );
                factor
                    .into_iter()
                    .zip(&g_observations[row])
                    .map(|(value, &g)| value.add(g_scale.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for source in &common_sources {
            if insert(
                0,
                lane,
                lane,
                QM31::ONE,
                g_scale,
                1,
                inverse_exponent,
                root_zero,
                source,
                &tail_terminal_rows,
                &observations,
            ) {
                break 'semantic;
            }
        }
    }

    // q18 books the deterministic minimum-q-degree basis: all degree-one
    // semantic and D sources are offered before any degree-two full-domain
    // mask-only source. This is the standard greedy minimum-weight basis for
    // the represented column matroid. q16 retains its frozen legacy order
    // below so this q18 refinement cannot change Profile22 evidence.
    if schedule.query_count == 18 {
        'd_q18: for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            let g_scale = QM31::ZERO.sub(gamma.mul(basis));
            let d_observations = g_observations[COMMON_TAIL_START..]
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|&value| g_scale.mul(value))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let root_zero = gamma_d.mul(basis).add(gamma_g.mul(g_scale)) == QM31::ZERO;
            for source in &common_sources {
                if insert(
                    2,
                    coordinate,
                    D_TERMINAL_LANE,
                    basis,
                    g_scale,
                    1,
                    0,
                    root_zero,
                    source,
                    &tail_terminal_rows,
                    &d_observations,
                ) {
                    break 'd_q18;
                }
            }
        }
    }

    'mask_only: for mask_lane in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_lane;
        let inverse_exponent = G_GENERATOR - generator;
        let ratio = gamma_power(gamma, inverse_exponent).inv();
        let g_scale = QM31::ZERO.sub(ratio);
        let root_zero = gamma_power(gamma, generator).add(gamma_g.mul(g_scale)) == QM31::ZERO;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                let factor = mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_lane),
                    FactorSchedule::FullSharedLinear,
                    None,
                );
                factor
                    .into_iter()
                    .zip(&g_observations[row])
                    .map(|(value, &g)| value.add(g_scale.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for source in &full_sources {
            if insert(
                1,
                mask_lane,
                generator,
                QM31::ONE,
                g_scale,
                2,
                inverse_exponent,
                root_zero,
                source,
                &full_terminal_rows,
                &observations,
            ) {
                break 'mask_only;
            }
        }
    }

    // Preserve the Profile22 q16 source ordering and therefore its frozen
    // minor provenance: semantic, mask-only, then D.
    if schedule.query_count == 16 {
        'd_q16: for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            let g_scale = QM31::ZERO.sub(gamma.mul(basis));
            let d_observations = g_observations[COMMON_TAIL_START..]
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|&value| g_scale.mul(value))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let root_zero = gamma_d.mul(basis).add(gamma_g.mul(g_scale)) == QM31::ZERO;
            for source in &common_sources {
                if insert(
                    2,
                    coordinate,
                    D_TERMINAL_LANE,
                    basis,
                    g_scale,
                    1,
                    0,
                    root_zero,
                    source,
                    &tail_terminal_rows,
                    &d_observations,
                ) {
                    break 'd_q16;
                }
            }
        }
    }

    drop(insert);

    if joint.rank > ROOT_JOINT_TARGET_M31
        || terminal_projection.rank > RAW_TERMINAL_M31
        || terminal_and_initial_projection.rank > RAW_TERMINAL_M31 + 4
    {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let terminal_conditioned = joint.rank.saturating_sub(terminal_projection.rank);
    let root_neutral_conditioned = joint
        .rank
        .saturating_sub(terminal_and_initial_projection.rank);
    let q_individual_degree = selected_degree_one + 2 * selected_degree_two;
    let q_total_degree = schedule.query_count * q_individual_degree;
    let z_degree = 41_040usize;
    let rho = q_total_degree as f64 / (131_072usize - (schedule.query_count - 1)) as f64;
    let continuous = (z_degree + gamma_degree) as f64 / 2_147_483_647f64;
    let minimum_selectors = (1usize..=16)
        .find(|&selectors| {
            let beta = continuous + rho.powi(selectors as i32);
            -16.0 * beta.log2() > 100.0
        })
        .unwrap_or(17);
    let minor = RankMinorProvenance::from_parts(
        "profile22_d_after_g_root_neutral_terminal336_sc1080",
        minor_sources,
        minor_rows,
        minor_values,
    );
    Ok(Profile22RootNeutralPolynomialKernelRankReport {
        query_count: schedule.query_count,
        gamma_nonzero: true,
        generator_order: "semantic0..15,mask-only16..25,H26,G27,D28",
        semantic_lanes: STATE_ONLY_HIDING_C1_COLUMNS,
        mask_only_lanes: STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
        d_tower_coordinates: 4,
        semantic_sources_per_lane_m31: common_sources.len(),
        mask_only_sources_per_lane_m31: full_sources.len(),
        d_sources_per_coordinate_m31: common_sources.len(),
        potential_source_columns_m31: STATE_ONLY_HIDING_C1_COLUMNS * common_sources.len()
            + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS * full_sources.len()
            + 4 * common_sources.len(),
        processed_source_columns_m31: source_id,
        serialized_terminal_rows_m31: SERIALIZED_TERMINAL_M31,
        terminal_projection_rank_m31: terminal_projection.rank,
        d_terminal_projection_rank_m31: d_terminal_projection.rank,
        terminal_conditioned_sumcheck_rank_m31: terminal_conditioned,
        terminal_and_initial_projection_rank_m31: terminal_and_initial_projection.rank,
        root_neutral_conditioned_sumcheck_rank_m31: root_neutral_conditioned,
        root_neutral_target_rank_m31: ROOT_INITIAL_TARGET_M31,
        joint_rank_m31: joint.rank,
        joint_target_rank_m31: ROOT_JOINT_TARGET_M31,
        pointwise_root_zero_sources_checked_m31: pointwise_checked,
        every_source_pointwise_root_zero: pointwise_guard,
        selected_semantic_columns_by_lane: selected_semantic,
        selected_mask_only_columns_by_lane: selected_mask_only,
        selected_d_columns: selected_d,
        selected_degree_one_q_columns: selected_degree_one,
        selected_degree_two_q_columns: selected_degree_two,
        minor,
        q_individual_degree_bound: q_individual_degree,
        q_total_degree_bound: q_total_degree,
        gamma_inverse_norm_denominator_exponent: gamma_denominator_exponent,
        gamma_coordinate_total_degree_bound: gamma_degree,
        z_total_degree_bound: z_degree,
        minimum_selector_count_for_cap16_over_100_bits: minimum_selectors,
        complete: joint.rank == ROOT_JOINT_TARGET_M31
            && terminal_projection.rank == RAW_TERMINAL_M31
            && d_terminal_projection.rank == RAW_TERMINAL_M31_PER_LANE
            && terminal_and_initial_projection.rank == RAW_TERMINAL_M31 + 4
            && root_neutral_conditioned == ROOT_INITIAL_TARGET_M31
            && pointwise_guard,
        elapsed_millis: started.elapsed().as_millis(),
    })
}
