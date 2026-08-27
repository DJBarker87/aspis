//! Host-only integration-valid zero-factor C1 repair for the conditional
//! root-neutral sumcheck fiber.
//!
//! This module is live spend code: the GoodSpend predicate's raw Schur
//! probes and the complete-good product binding live here. The rank-minor
//! block labels and the complete-good-product domain separator in this file
//! are hashed into frozen provenance anchors that the release certificates
//! and known-answer tests pin; renaming them requires a full regrind.
//!
//! For a prefix of `m <= 4` new full-domain M31 C1 lanes, the exact generator
//! order is
//!
//! `semantic[0..16], mask-only[16..26], zero-factor[26..26+m], H, G`.
//!
//! Every new lane is paired pointwise into shifted G so its gamma-combined
//! root message is identically zero.  No H1 direct-sum image is suppressed.

use super::*;

pub const SPEND_ZERO_FACTOR_MAX_LANES: usize = 4;
const CONDITIONAL_SUMCHECK_TARGET_M31: usize = MASK_SUMCHECK_QUOTIENT_M31 - 4;
const SPEND_ROOT_NEUTRAL_Z_DEGREE: usize = 41_040;
const SPEND_RAW_TERMINAL_SCHUR_ROWS_M31: usize = 12;
const SPEND_RAW_TERMINAL_ENTRY_Z_DEGREE: usize = 10;
const SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE: usize =
    SPEND_RAW_TERMINAL_SCHUR_ROWS_M31 * SPEND_RAW_TERMINAL_ENTRY_Z_DEGREE;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendZeroFactorRootNeutralPrefix {
    pub added_lanes: usize,
    pub h_generator_index: usize,
    pub g_generator_index: usize,
    pub added_generator_indices: Vec<usize>,
    pub added_g_pair_exponents: Vec<isize>,
    pub baseline_existing_rank_m31: usize,
    pub conditional_rank_m31: usize,
    pub conditional_target_m31: usize,
    pub extra_raw_ranks_m31: Vec<usize>,
    pub terminal_zero_sources_checked_m31: usize,
    pub every_post_raw_source_terminal_zero: bool,
    pub conditional_minor: RankMinorProvenance,
    pub complete: bool,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendZeroFactorRootNeutralReport {
    pub query_count: usize,
    pub gamma_nonzero: bool,
    pub integration_order: &'static str,
    pub factor: &'static str,
    pub c1_leaf_bytes_before: usize,
    pub c1_leaf_delta_bytes_per_lane: usize,
    pub serialized_opening_delta_bytes_per_lane_q16: usize,
    pub generator_width_before: usize,
    pub prefixes: Vec<SpendZeroFactorRootNeutralPrefix>,
    pub minimum_complete_lanes: Option<usize>,
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendZeroFactorQm31TailRootNeutralReport {
    pub query_count: usize,
    pub gamma_nonzero: bool,
    pub production_h_generator_index: usize,
    pub production_g_generator_index: usize,
    pub tail_generator_index: usize,
    pub g_delta_from_tail: &'static str,
    pub tail_factor: &'static str,
    pub baseline_existing_rank_m31: usize,
    pub conditional_rank_m31: usize,
    pub conditional_target_m31: usize,
    pub tail_raw_rank_m31: usize,
    pub h1_inactive_padding_raw_rank_m31: usize,
    pub qm31_raw_target_m31: usize,
    pub remaining_gd_query_rank_m31: usize,
    pub remaining_gd_terminal_schur_rank_m31: usize,
    pub remaining_gd_terminal_schur_z_degree: usize,
    pub remaining_gd_terminal_schur_minor: RankMinorProvenance,
    pub h1_inactive_padding_query_rank_m31: usize,
    pub h1_inactive_padding_terminal_schur_rank_m31: usize,
    pub h1_inactive_padding_terminal_schur_z_degree: usize,
    pub h1_inactive_padding_terminal_schur_minor: RankMinorProvenance,
    pub terminal_zero_sources_checked_m31: usize,
    pub every_post_raw_source_terminal_zero: bool,
    pub conditional_minor: RankMinorProvenance,
    pub c2_leaf_bytes_before: usize,
    pub c2_leaf_delta_bytes: usize,
    pub serialized_opening_delta_bytes_q16: usize,
    pub generator_width_before: usize,
    pub generator_width_after: usize,
    pub complete: bool,
    pub elapsed_millis: u128,
}

/// Executable provenance for the complete prospective spend Good
/// polynomial.  The product is the root-neutral 1,404-row minor times the
/// two independent 12-row raw-terminal Schur minors.  The fingerprint binds
/// the three component fingerprints and every degree used by the liveness
/// ledger; it is not a production-enable flag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpendCompleteGoodProductProvenance {
    pub root_neutral_minor_fingerprint: u64,
    pub remaining_gd_terminal_schur_minor_fingerprint: u64,
    pub h1_inactive_padding_terminal_schur_minor_fingerprint: u64,
    pub root_neutral_minor_rank_m31: usize,
    pub remaining_gd_terminal_schur_rank_m31: usize,
    pub h1_inactive_padding_terminal_schur_rank_m31: usize,
    pub q_total_degree_bound: usize,
    pub root_neutral_z_degree_bound: usize,
    pub remaining_gd_terminal_schur_z_degree_bound: usize,
    pub h1_inactive_padding_terminal_schur_z_degree_bound: usize,
    pub complete_good_z_degree_bound: usize,
    pub gamma_coordinate_total_degree_bound: usize,
    pub continuous_total_degree_bound: usize,
    pub product_fingerprint: u64,
    pub complete: bool,
}

fn raw_terminal_schur_minor(
    block: &'static str,
    rows: &[RowPublicMaps],
    active: &[bool; TRACE_ROWS],
    global_dependent: usize,
    inactive_only: bool,
) -> Result<(usize, RankMinorProvenance), StateOnlyHidingRankGateError> {
    let query_rows_m31 = 4 * rows[0].layer0_m31.len();
    let mut query = CarryEchelon::new(query_rows_m31);
    let mut terminal = ColumnEchelon::new(SPEND_RAW_TERMINAL_SCHUR_ROWS_M31);
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();

    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent || (inactive_only && active[row]) {
                continue;
            }
            let source_id = coordinate * TRACE_ROWS + row;
            let subtract = if inactive_only || !active[row] {
                Some(global_dependent)
            } else {
                None
            };
            let raw = qm31_raw_difference(rows, row, subtract, basis);
            let (query_image, terminal_image) = raw.split_at(query_rows_m31);
            if let CarryReduction::Kernel(schur_image) =
                query.reduce_with_pivot(query_image.to_vec(), terminal_image.to_vec())
            {
                if let Some((pivot, value)) = terminal.insert_with_pivot_value(schur_image) {
                    minor_sources.push(source_id);
                    minor_rows.push(pivot);
                    minor_values.push(value);
                }
            }
        }
    }

    if query.rank != query_rows_m31 || terminal.rank != SPEND_RAW_TERMINAL_SCHUR_ROWS_M31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: query.rank + terminal.rank,
            want: query_rows_m31 + SPEND_RAW_TERMINAL_SCHUR_ROWS_M31,
        });
    }
    Ok((
        query.rank,
        RankMinorProvenance::from_parts(block, minor_sources, minor_rows, minor_values),
    ))
}

fn spend_complete_good_product_fingerprint(values: &[u64]) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for &byte in b"aspis/spend/complete-good-product/v1" {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    for &value in values {
        for byte in value.to_le_bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    hash
}

pub fn bind_spend_complete_good_product_provenance(
    root: &SpendRootNeutralPolynomialKernelRankReport,
    raw: &SpendZeroFactorQm31TailRootNeutralReport,
) -> Result<SpendCompleteGoodProductProvenance, StateOnlyHidingRankGateError> {
    let root_rank = root.minor.source_columns.len();
    let gd_rank = raw.remaining_gd_terminal_schur_minor.source_columns.len();
    let h1_rank = raw
        .h1_inactive_padding_terminal_schur_minor
        .source_columns
        .len();
    let shape_ok = root.complete
        && raw.complete
        && root.query_count == raw.query_count
        && root_rank == root.joint_target_rank_m31
        && gd_rank == SPEND_RAW_TERMINAL_SCHUR_ROWS_M31
        && h1_rank == SPEND_RAW_TERMINAL_SCHUR_ROWS_M31
        && raw.remaining_gd_terminal_schur_rank_m31 == gd_rank
        && raw.h1_inactive_padding_terminal_schur_rank_m31 == h1_rank
        && root.query_count == usize::from(STATE_ONLY_SPEND_QUERY_COUNT)
        && root.q_total_degree_bound == root.query_count * root.q_individual_degree_bound
        && root.q_total_degree_bound != 0
        && root.z_total_degree_bound == SPEND_ROOT_NEUTRAL_Z_DEGREE
        && root.gamma_coordinate_total_degree_bound != 0
        && raw.remaining_gd_terminal_schur_z_degree == SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE
        && raw.h1_inactive_padding_terminal_schur_z_degree == SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE;
    if !shape_ok {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let complete_good_z_degree =
        SPEND_ROOT_NEUTRAL_Z_DEGREE + 2 * SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE;
    let continuous_degree = complete_good_z_degree + root.gamma_coordinate_total_degree_bound;
    let product_fingerprint = spend_complete_good_product_fingerprint(&[
        root.minor.fingerprint,
        raw.remaining_gd_terminal_schur_minor.fingerprint,
        raw.h1_inactive_padding_terminal_schur_minor.fingerprint,
        root_rank as u64,
        gd_rank as u64,
        h1_rank as u64,
        root.q_total_degree_bound as u64,
        SPEND_ROOT_NEUTRAL_Z_DEGREE as u64,
        SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE as u64,
        SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE as u64,
        complete_good_z_degree as u64,
        root.gamma_coordinate_total_degree_bound as u64,
        continuous_degree as u64,
    ]);
    Ok(SpendCompleteGoodProductProvenance {
        root_neutral_minor_fingerprint: root.minor.fingerprint,
        remaining_gd_terminal_schur_minor_fingerprint: raw
            .remaining_gd_terminal_schur_minor
            .fingerprint,
        h1_inactive_padding_terminal_schur_minor_fingerprint: raw
            .h1_inactive_padding_terminal_schur_minor
            .fingerprint,
        root_neutral_minor_rank_m31: root_rank,
        remaining_gd_terminal_schur_rank_m31: gd_rank,
        h1_inactive_padding_terminal_schur_rank_m31: h1_rank,
        q_total_degree_bound: root.q_total_degree_bound,
        root_neutral_z_degree_bound: SPEND_ROOT_NEUTRAL_Z_DEGREE,
        remaining_gd_terminal_schur_z_degree_bound: SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE,
        h1_inactive_padding_terminal_schur_z_degree_bound: SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE,
        complete_good_z_degree_bound: complete_good_z_degree,
        gamma_coordinate_total_degree_bound: root.gamma_coordinate_total_degree_bound,
        continuous_total_degree_bound: continuous_degree,
        product_fingerprint,
        complete: true,
    })
}

fn insert_conditional_image(
    source_id: usize,
    image: Vec<QM31>,
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    initial: &mut CarryEchelon,
    conditional: &mut ColumnEchelon,
    minor_sources: &mut Vec<usize>,
    minor_rows: &mut Vec<usize>,
    minor_values: &mut Vec<M31>,
    terminal_zero_sources_checked: &mut usize,
) -> bool {
    let terminal_zero = compressed_mask_sumcheck_terminal(&image, challenges) == Some(QM31::ZERO);
    *terminal_zero_sources_checked += 1;
    if !terminal_zero {
        return false;
    }
    let mut coordinates = Vec::with_capacity(4 * image.len());
    append_qm31_coordinates(&mut coordinates, image);
    if let CarryReduction::Kernel(legal) =
        initial.reduce_with_pivot(coordinates[..4].to_vec(), coordinates[4..].to_vec())
    {
        if let Some((row, value)) = conditional.insert_with_pivot_value(legal) {
            minor_sources.push(source_id);
            minor_rows.push(row);
            minor_values.push(value);
        }
    }
    true
}

fn probe_prefix(
    schedule: &StateOnlyTranscriptScheduleResult,
    added_lanes: usize,
) -> Result<SpendZeroFactorRootNeutralPrefix, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if added_lanes > SPEND_ZERO_FACTOR_MAX_LANES
        || schedule.query_count != 16
        || schedule.query_count > schedule.queries.len()
        || schedule.prefix.gamma == QM31::ZERO
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = root_neutral_raw_rows(&encoder, schedule)?;
    let c1_raw_m31 = rows[0].layer0_m31.len() + 12;
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(RankLayout::AtomicV3);
    let mut active = [false; TRACE_ROWS];
    for &row in &active_rows {
        active[usize::from(row)] = true;
    }
    let global_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;

    let h_generator_index =
        STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + added_lanes;
    let g_generator_index = h_generator_index + 1;
    let gamma_g_inverse = gamma_power(schedule.prefix.gamma, g_generator_index).inv();
    let g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::Production,
                None,
            )
        })
        .collect::<Vec<_>>();

    let mut initial = CarryEchelon::new(4);
    // After fixing the initial claim, columns retain the remaining 1,080
    // serialized coordinates.  The independent terminal-zero guard confines
    // them to the 1,076-dimensional kernel inside that ambient space.
    let mut conditional = ColumnEchelon::new(MASK_SUMCHECK_QUOTIENT_M31);
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();
    let mut source_id = 0usize;
    let mut terminal_zero_sources_checked = 0usize;
    let mut terminal_guard = true;

    for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    FactorSchedule::Production,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let g_ratio = gamma_power(schedule.prefix.gamma, generator).mul(gamma_g_inverse);
        let effective = observations
            .iter()
            .zip(&g_observations)
            .map(|(mask, g)| {
                mask.iter()
                    .copied()
                    .zip(g)
                    .map(|(mask, &g)| mask.sub(g_ratio.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let current_source = source_id;
            source_id += 1;
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let carry = scaled_qm31_difference(
                &effective[row],
                subtract.map(|dependent| effective[dependent].as_slice()),
                QM31::ONE,
            );
            if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
                let image = kernel
                    .chunks_exact(4)
                    .map(|coordinates| qm31_from_m31_coordinates(coordinates).unwrap())
                    .collect::<Vec<_>>();
                terminal_guard &= insert_conditional_image(
                    current_source,
                    image,
                    &schedule.prefix.z,
                    &mut initial,
                    &mut conditional,
                    &mut minor_sources,
                    &mut minor_rows,
                    &mut minor_values,
                    &mut terminal_zero_sources_checked,
                );
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: mask_column,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
    }

    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(column),
                    FactorSchedule::Production,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let g_ratio = gamma_power(schedule.prefix.gamma, column).mul(gamma_g_inverse);
        let effective = observations
            .iter()
            .zip(&g_observations)
            .map(|(mask, g)| {
                mask.iter()
                    .copied()
                    .zip(g)
                    .map(|(mask, &g)| mask.sub(g_ratio.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let current_source = source_id;
            source_id += 1;
            let subtract = (!active[row]).then_some(dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let carry = scaled_qm31_difference(
                &effective[row],
                subtract.map(|dependent| effective[dependent].as_slice()),
                QM31::ONE,
            );
            if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
                let image = kernel
                    .chunks_exact(4)
                    .map(|coordinates| qm31_from_m31_coordinates(coordinates).unwrap())
                    .collect::<Vec<_>>();
                terminal_guard &= insert_conditional_image(
                    current_source,
                    image,
                    &schedule.prefix.z,
                    &mut initial,
                    &mut conditional,
                    &mut minor_sources,
                    &mut minor_rows,
                    &mut minor_values,
                    &mut terminal_zero_sources_checked,
                );
            }
        }
    }
    let baseline_existing_rank_m31 = conditional.rank;

    let mut extra_raw_ranks_m31 = Vec::with_capacity(added_lanes);
    for extra_lane in 0..added_lanes {
        let generator =
            STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + extra_lane;
        let g_ratio = gamma_power(schedule.prefix.gamma, generator).mul(gamma_g_inverse);
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let current_source = source_id;
            source_id += 1;
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            // The new C1 factor is identically zero.  Pairing its pointwise
            // source value into G contributes exactly -gamma^(j-G) F_G.
            let carry = scaled_qm31_difference(
                &g_observations[row],
                subtract.map(|dependent| g_observations[dependent].as_slice()),
                QM31::ZERO.sub(g_ratio),
            );
            if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
                let image = kernel
                    .chunks_exact(4)
                    .map(|coordinates| qm31_from_m31_coordinates(coordinates).unwrap())
                    .collect::<Vec<_>>();
                terminal_guard &= insert_conditional_image(
                    current_source,
                    image,
                    &schedule.prefix.z,
                    &mut initial,
                    &mut conditional,
                    &mut minor_sources,
                    &mut minor_rows,
                    &mut minor_values,
                    &mut terminal_zero_sources_checked,
                );
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + extra_lane,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
        extra_raw_ranks_m31.push(raw.rank);
    }

    if initial.rank != 4 || conditional.rank > CONDITIONAL_SUMCHECK_TARGET_M31 {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let conditional_minor = RankMinorProvenance::from_parts(
        "root_neutral_zero_factor_conditional_1076",
        minor_sources,
        minor_rows,
        minor_values,
    );
    Ok(SpendZeroFactorRootNeutralPrefix {
        added_lanes,
        h_generator_index,
        g_generator_index,
        added_generator_indices: (0..added_lanes)
            .map(|lane| {
                STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + lane
            })
            .collect(),
        added_g_pair_exponents: (0..added_lanes)
            .map(|lane| {
                (STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + lane)
                    as isize
                    - g_generator_index as isize
            })
            .collect(),
        baseline_existing_rank_m31,
        conditional_rank_m31: conditional.rank,
        conditional_target_m31: CONDITIONAL_SUMCHECK_TARGET_M31,
        extra_raw_ranks_m31,
        terminal_zero_sources_checked_m31: terminal_zero_sources_checked,
        every_post_raw_source_terminal_zero: terminal_guard,
        conditional_minor,
        complete: conditional.rank == CONDITIONAL_SUMCHECK_TARGET_M31 && terminal_guard,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

pub fn probe_atomic_state_only_spend_zero_factor_root_neutral_prefixes(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<SpendZeroFactorRootNeutralReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    let mut prefixes = Vec::with_capacity(SPEND_ZERO_FACTOR_MAX_LANES + 1);
    for added_lanes in 0..=SPEND_ZERO_FACTOR_MAX_LANES {
        prefixes.push(probe_prefix(schedule, added_lanes)?);
    }
    let minimum_complete_lanes = prefixes
        .iter()
        .find(|prefix| prefix.complete)
        .map(|prefix| prefix.added_lanes);
    Ok(SpendZeroFactorRootNeutralReport {
        query_count: schedule.query_count,
        gamma_nonzero: schedule.prefix.gamma != QM31::ZERO,
        integration_order: "semantic16,mask-only10,zero-factor-prefix,H,G",
        factor: "0; pointwise paired into shifted G",
        c1_leaf_bytes_before: FIBER_SLOTS
            * (STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS)
            * core::mem::size_of::<u32>(),
        c1_leaf_delta_bytes_per_lane: FIBER_SLOTS * core::mem::size_of::<u32>(),
        serialized_opening_delta_bytes_per_lane_q16: schedule.query_count
            * FIBER_SLOTS
            * core::mem::size_of::<u32>()
            + 3 * 16,
        generator_width_before: STATE_ONLY_HIDING_C1_COLUMNS
            + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
            + 2,
        prefixes,
        minimum_complete_lanes,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Exact root-message-neutral screen for one full-domain QM31 zero-factor
/// tail appended after production G.  Production C1/H/G keep generator
/// indices `0..=27`; D is generator 28 and the source restriction is
/// `delta_G = -gamma * delta_D`, hence
/// `gamma^27 delta_G + gamma^28 delta_D = 0` pointwise.
pub fn probe_atomic_state_only_spend_zero_factor_qm31_tail_root_neutral(
    schedule: &StateOnlyTranscriptScheduleResult,
) -> Result<SpendZeroFactorQm31TailRootNeutralReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    if !matches!(schedule.query_count, 16 | 18)
        || schedule.query_count > schedule.queries.len()
        || schedule.prefix.gamma == QM31::ZERO
    {
        return Err(StateOnlyHidingRankGateError::Shape);
    }
    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = root_neutral_raw_rows(&encoder, schedule)?;
    let c1_raw_m31 = rows[0].layer0_m31.len() + 12;
    let qm31_raw_m31 = 4 * (rows[0].layer0_m31.len() + 3);
    let lagrange = lagrange_basis();
    let active_rows = rank_active_rows(RankLayout::AtomicV3);
    let mut active = [false; TRACE_ROWS];
    for &row in &active_rows {
        active[usize::from(row)] = true;
    }
    let global_dependent = (0..TRACE_ROWS)
        .find(|row| !active[*row])
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let g_generator_index =
        STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 1;
    let h_generator_index = g_generator_index - 1;
    let tail_generator_index = g_generator_index + 1;
    let gamma_g_inverse = gamma_power(schedule.prefix.gamma, g_generator_index).inv();
    let g_observations = (0..TRACE_ROWS)
        .map(|row| {
            mask_sumcheck_observations(
                row,
                &schedule.prefix.z,
                &lagrange,
                MaskFactor::ExplicitG,
                FactorSchedule::Production,
                None,
            )
        })
        .collect::<Vec<_>>();

    let mut initial = CarryEchelon::new(4);
    let mut conditional = ColumnEchelon::new(MASK_SUMCHECK_QUOTIENT_M31);
    let mut minor_sources = Vec::new();
    let mut minor_rows = Vec::new();
    let mut minor_values = Vec::new();
    let mut source_id = 0usize;
    let mut terminal_zero_sources_checked = 0usize;
    let mut terminal_guard = true;

    for mask_column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::MaskOnly(mask_column),
                    FactorSchedule::Production,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let g_ratio = gamma_power(schedule.prefix.gamma, generator).mul(gamma_g_inverse);
        let effective = observations
            .iter()
            .zip(&g_observations)
            .map(|(mask, g)| {
                mask.iter()
                    .copied()
                    .zip(g)
                    .map(|(mask, &g)| mask.sub(g_ratio.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let current_source = source_id;
            source_id += 1;
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let carry = scaled_qm31_difference(
                &effective[row],
                subtract.map(|dependent| effective[dependent].as_slice()),
                QM31::ONE,
            );
            if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
                let image = kernel
                    .chunks_exact(4)
                    .map(|coordinates| qm31_from_m31_coordinates(coordinates).unwrap())
                    .collect::<Vec<_>>();
                terminal_guard &= insert_conditional_image(
                    current_source,
                    image,
                    &schedule.prefix.z,
                    &mut initial,
                    &mut conditional,
                    &mut minor_sources,
                    &mut minor_rows,
                    &mut minor_values,
                    &mut terminal_zero_sources_checked,
                );
            }
        }
        if raw.rank != c1_raw_m31 {
            return Err(StateOnlyHidingRankGateError::RawC1Rank {
                column: mask_column,
                got: raw.rank,
                want: c1_raw_m31,
            });
        }
    }

    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }
    for (column, cells) in cells_by_column.iter().enumerate() {
        let dependent = cells
            .iter()
            .copied()
            .filter(|row| !active[*row])
            .last()
            .ok_or(StateOnlyHidingRankGateError::Layout)?;
        let observations = (0..TRACE_ROWS)
            .map(|row| {
                mask_sumcheck_observations(
                    row,
                    &schedule.prefix.z,
                    &lagrange,
                    MaskFactor::Semantic(column),
                    FactorSchedule::Production,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let g_ratio = gamma_power(schedule.prefix.gamma, column).mul(gamma_g_inverse);
        let effective = observations
            .iter()
            .zip(&g_observations)
            .map(|(mask, g)| {
                mask.iter()
                    .copied()
                    .zip(g)
                    .map(|(mask, &g)| mask.sub(g_ratio.mul(g)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let current_source = source_id;
            source_id += 1;
            let subtract = (!active[row]).then_some(dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let carry = scaled_qm31_difference(
                &effective[row],
                subtract.map(|dependent| effective[dependent].as_slice()),
                QM31::ONE,
            );
            if let CarryReduction::Kernel(kernel) = raw.reduce_with_pivot(raw_image, carry) {
                let image = kernel
                    .chunks_exact(4)
                    .map(|coordinates| qm31_from_m31_coordinates(coordinates).unwrap())
                    .collect::<Vec<_>>();
                terminal_guard &= insert_conditional_image(
                    current_source,
                    image,
                    &schedule.prefix.z,
                    &mut initial,
                    &mut conditional,
                    &mut minor_sources,
                    &mut minor_rows,
                    &mut minor_values,
                    &mut terminal_zero_sources_checked,
                );
            }
        }
    }
    let baseline_existing_rank_m31 = conditional.rank;

    // Independent translation guard for the physical H1 padding source.  It
    // uses only inactive rows, balanced against the same global dependent
    // row, over all four tower coordinates.  The exact raw wire is 64 q
    // symbols plus three terminal QM31 values = 268 M31 coordinates; the old
    // idealized-H diagnostic's 304-row allocation was over-wide.
    let mut h1_inactive_raw = ColumnEchelon::new(qm31_raw_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if active[row] || row == global_dependent {
                continue;
            }
            h1_inactive_raw.insert(qm31_raw_difference(
                &rows,
                row,
                Some(global_dependent),
                basis,
            ));
        }
    }
    if h1_inactive_raw.rank != qm31_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: h1_inactive_raw.rank,
            want: qm31_raw_m31,
        });
    }
    let (h1_inactive_padding_query_rank_m31, h1_inactive_padding_terminal_schur_minor) =
        raw_terminal_schur_minor(
            "spend_h1_inactive_padding_terminal_schur_12",
            &rows,
            &active,
            global_dependent,
            true,
        )?;
    let h1_inactive_padding_terminal_schur_rank_m31 = h1_inactive_padding_terminal_schur_minor
        .source_columns
        .len();

    // One full QM31 D lane after G.  Its direct factor is zero and the exact
    // pointwise pairing delta_G=-gamma*delta_D gives carry -gamma*F_G*D.
    let mut tail_raw = CarryEchelon::new(qm31_raw_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let current_source = source_id;
            source_id += 1;
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
            let carry = scaled_qm31_difference(
                &g_observations[row],
                subtract.map(|dependent| g_observations[dependent].as_slice()),
                QM31::ZERO.sub(schedule.prefix.gamma.mul(basis)),
            );
            if let CarryReduction::Kernel(kernel) = tail_raw.reduce_with_pivot(raw_image, carry) {
                let image = kernel
                    .chunks_exact(4)
                    .map(|coordinates| qm31_from_m31_coordinates(coordinates).unwrap())
                    .collect::<Vec<_>>();
                terminal_guard &= insert_conditional_image(
                    current_source,
                    image,
                    &schedule.prefix.z,
                    &mut initial,
                    &mut conditional,
                    &mut minor_sources,
                    &mut minor_rows,
                    &mut minor_values,
                    &mut terminal_zero_sources_checked,
                );
            }
        }
    }
    if tail_raw.rank != qm31_raw_m31 {
        return Err(StateOnlyHidingRankGateError::RawGRank {
            got: tail_raw.rank,
            want: qm31_raw_m31,
        });
    }
    let (remaining_gd_query_rank_m31, remaining_gd_terminal_schur_minor) =
        raw_terminal_schur_minor(
            "spend_remaining_gd_terminal_schur_12",
            &rows,
            &active,
            global_dependent,
            false,
        )?;
    let remaining_gd_terminal_schur_rank_m31 =
        remaining_gd_terminal_schur_minor.source_columns.len();
    if initial.rank != 4 || conditional.rank > CONDITIONAL_SUMCHECK_TARGET_M31 {
        return Err(StateOnlyHidingRankGateError::Relation);
    }
    let conditional_minor = RankMinorProvenance::from_parts(
        "root_neutral_zero_factor_qm31_tail_conditional_1076",
        minor_sources,
        minor_rows,
        minor_values,
    );
    let c2_leaf_delta_bytes = FIBER_SLOTS * 16;
    let serialized_opening_delta_bytes_q16 = schedule.query_count * c2_leaf_delta_bytes + 3 * 16;
    Ok(SpendZeroFactorQm31TailRootNeutralReport {
        query_count: schedule.query_count,
        gamma_nonzero: schedule.prefix.gamma != QM31::ZERO,
        production_h_generator_index: h_generator_index,
        production_g_generator_index: g_generator_index,
        tail_generator_index,
        g_delta_from_tail: "delta_G=-gamma*delta_D",
        tail_factor: "0",
        baseline_existing_rank_m31,
        conditional_rank_m31: conditional.rank,
        conditional_target_m31: CONDITIONAL_SUMCHECK_TARGET_M31,
        tail_raw_rank_m31: tail_raw.rank,
        h1_inactive_padding_raw_rank_m31: h1_inactive_raw.rank,
        qm31_raw_target_m31: qm31_raw_m31,
        remaining_gd_query_rank_m31,
        remaining_gd_terminal_schur_rank_m31,
        remaining_gd_terminal_schur_z_degree: SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE,
        remaining_gd_terminal_schur_minor,
        h1_inactive_padding_query_rank_m31,
        h1_inactive_padding_terminal_schur_rank_m31,
        h1_inactive_padding_terminal_schur_z_degree: SPEND_RAW_TERMINAL_SCHUR_Z_DEGREE,
        h1_inactive_padding_terminal_schur_minor,
        terminal_zero_sources_checked_m31: terminal_zero_sources_checked,
        every_post_raw_source_terminal_zero: terminal_guard,
        conditional_minor,
        c2_leaf_bytes_before: FIBER_SLOTS * 2 * 16,
        c2_leaf_delta_bytes,
        serialized_opening_delta_bytes_q16,
        generator_width_before: STATE_ONLY_HIDING_C1_COLUMNS
            + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
            + 2,
        generator_width_after: STATE_ONLY_HIDING_C1_COLUMNS
            + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
            + 3,
        complete: conditional.rank == CONDITIONAL_SUMCHECK_TARGET_M31 && terminal_guard,
        elapsed_millis: started.elapsed().as_millis(),
    })
}
