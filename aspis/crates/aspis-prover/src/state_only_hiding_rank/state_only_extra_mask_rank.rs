//! Production-neutral exact-rank search for ordinary C1 repair masks.
//!
//! This child module deliberately reuses the parent's exact row maps and
//! elimination machinery while keeping all experimental factor schedules out
//! of the production wire.

use super::*;

const BASE_MASK_EXPONENTS: [usize; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
    [1, 3, 5, 7, 9, 11, 15, 17, 19, 21];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtraMaskFactorFamily {
    /// `basis(rotation) * L_0^exponent`, where `L_0` is the shared dense
    /// linear form used by the semantic and selected mask-only columns.
    Shared,
    /// `basis(rotation) * L_family^exponent` for an independently generated
    /// dense linear form.
    Dense(usize),
    /// `basis(rotation) * eq_row(point)`.  This is a multilinear selector:
    /// its degree in every sumcheck variable is one even though its total
    /// degree can be ten.  It is useful for testing whether the four-row
    /// semantic quotient can be repaired directly without a switch oracle.
    Selector(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExtraMaskFactorSpec {
    pub family: ExtraMaskFactorFamily,
    pub exponent: usize,
    pub tower_rotation: usize,
    pub add_one: bool,
}

impl ExtraMaskFactorSpec {
    fn base_mask(column: usize) -> Self {
        Self {
            family: ExtraMaskFactorFamily::Shared,
            exponent: BASE_MASK_EXPONENTS[column],
            tower_rotation: column & 3,
            add_one: false,
        }
    }

    fn base_g() -> Self {
        Self {
            family: ExtraMaskFactorFamily::Dense(16),
            exponent: 26,
            tower_rotation: 0,
            add_one: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtraMaskRankReport {
    pub candidate: String,
    pub representative_screen_only: bool,
    pub mask_only_factors: Vec<ExtraMaskFactorSpec>,
    pub explicit_g_factor: ExtraMaskFactorSpec,
    pub extra_g_factors: Vec<ExtraMaskFactorSpec>,
    pub extra_mask_only_columns: usize,
    pub extra_g_columns: usize,
    pub maximum_factor_degree: usize,
    pub maximum_masked_oracle_degree: usize,
    pub degree_27_soundness_shape_preserved: bool,
    pub c1_raw_rows_per_column_m31: usize,
    pub c1_raw_ranks_m31: Vec<usize>,
    pub g_raw_rows_m31: usize,
    pub g_raw_rank_m31: usize,
    pub extra_g_raw_ranks_m31: Vec<usize>,
    pub masked_sumcheck_rows_m31: usize,
    pub masked_sumcheck_rank_m31: usize,
    pub pre_helper_pcs_rank_m31: usize,
    pub pre_scalar_m_pcs_rank_m31: usize,
    pub pcs_rank_m31: usize,
    pub ambient_rank_m31: usize,
    pub ambient_deficit_m31: usize,
    pub conservative_semantic_augmented_rank_m31: usize,
    pub conservative_semantic_new_pivots_m31: Vec<usize>,
    pub legal_sumcheck_augmented_rank_m31: usize,
    pub legal_sumcheck_new_pivots_m31: Vec<usize>,
    pub compatibility_rank_m31: usize,
    pub post_alpha_scalar_m_probe: bool,
    pub scalar_m_variables_qm31: usize,
    pub scalar_m_observations_qm31: usize,
    pub scalar_m_observation_rank_m31: usize,
    pub scalar_m_conditioned_kernel_m31: usize,
    pub scalar_m_new_pivots_m31: Vec<usize>,
    pub scalar_m_observation_minor_fingerprint: u64,
    pub scalar_m_pcs_minor_fingerprint: u64,
    pub scalar_m_contains_conservative_semantic_superset: bool,
    pub raw_minor_fingerprint: u64,
    pub sumcheck_minor_fingerprint: u64,
    pub pcs_minor_fingerprint: u64,
    pub semantic_minor_fingerprint: u64,
    pub factor_schedule_fingerprint: u64,
    pub generator_width: usize,
    pub c1_columns: usize,
    pub c2_columns: usize,
    pub layer0_leaf_delta_bytes: usize,
    pub q16_opened_leaf_delta_bytes: usize,
    pub three_terminal_opening_delta_bytes: usize,
    pub estimated_serialized_opening_delta_bytes: usize,
    pub scalar_m_query_and_tau_delta_bytes: usize,
    pub elapsed_millis: u128,
}

fn dense_linear(family: usize, point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
    point
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (variable, value)| {
            let scalar = 3 + 22 * variable + family * (17 + 8 * variable);
            sum.add(value.mul_m31(M31(scalar as u32)))
        })
}

fn extra_factor_at(
    spec: ExtraMaskFactorSpec,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    let value = match spec.family {
        ExtraMaskFactorFamily::Shared => dense_linear(0, point).pow(spec.exponent as u64),
        ExtraMaskFactorFamily::Dense(family) => {
            dense_linear(family, point).pow(spec.exponent as u64)
        }
        ExtraMaskFactorFamily::Selector(row) => eq_weight(point, row),
    };
    let mut value = value;
    if spec.add_one {
        value = QM31::ONE.add(value);
    }
    state_only_mask_tower_basis(spec.tower_rotation & 3).mul(value)
}

fn factor_schedule_fingerprint(
    masks: &[ExtraMaskFactorSpec],
    g: ExtraMaskFactorSpec,
    extra_g: &[ExtraMaskFactorSpec],
) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    let mut absorb = |bytes: &[u8]| {
        for &byte in bytes {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    absorb(b"aspis/profile21/extra-mask-factor-search/v1");
    absorb(&(masks.len() as u64).to_le_bytes());
    for spec in masks
        .iter()
        .copied()
        .chain(core::iter::once(g))
        .chain(extra_g.iter().copied())
    {
        let family = match spec.family {
            ExtraMaskFactorFamily::Shared => 0u64,
            ExtraMaskFactorFamily::Dense(family) => 1u64 + family as u64,
            ExtraMaskFactorFamily::Selector(row) => 0x8000_0000_0000_0000u64 | row as u64,
        };
        absorb(&family.to_le_bytes());
        absorb(&(spec.exponent as u64).to_le_bytes());
        absorb(&(spec.tower_rotation as u64).to_le_bytes());
        absorb(&[u8::from(spec.add_one)]);
    }
    hash
}

fn extra_mask_sumcheck_observations(
    row: usize,
    challenges: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
    lagrange: &[[M31; MASK_SUMCHECK_COEFFICIENTS]; MASK_SUMCHECK_COEFFICIENTS],
    spec: ExtraMaskFactorSpec,
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
    let mut running_claim = extra_factor_at(spec, &boolean_point);
    let mut observations = Vec::with_capacity(STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS);
    observations.push(running_claim);
    for round in 0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        let samples = core::array::from_fn(|sample| {
            prefix[round] = QM31::from_cm31(CM31::from_m31(M31(sample as u32)));
            for coordinate in round + 1..STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
                let bit = (row >> (STATE_ONLY_HIDING_SUMCHECK_ROUNDS - 1 - coordinate)) & 1;
                prefix[coordinate] = if bit == 0 { QM31::ZERO } else { QM31::ONE };
            }
            eq_weight(&prefix, row).mul(extra_factor_at(spec, &prefix))
        });
        let polynomial = interpolate(&samples, lagrange);
        observations.push(polynomial[0]);
        observations.extend(polynomial[2..].iter().copied());
        running_claim = evaluate(&polynomial, challenges[round]);
        prefix[round] = challenges[round];
    }
    debug_assert_eq!(
        observations.len(),
        STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS
    );
    let _ = running_claim;
    observations
}

fn parse_candidate(
    candidate: &str,
) -> Result<
    (
        Vec<ExtraMaskFactorSpec>,
        ExtraMaskFactorSpec,
        Vec<ExtraMaskFactorSpec>,
    ),
    StateOnlyHidingRankGateError,
> {
    let mut masks = (0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS)
        .map(ExtraMaskFactorSpec::base_mask)
        .collect::<Vec<_>>();
    let mut g = ExtraMaskFactorSpec::base_g();
    let mut extra_g = Vec::new();
    if candidate == "baseline" {
        return Ok((masks, g, extra_g));
    }
    let parts = candidate.split('-').collect::<Vec<_>>();
    let parse_rotation = |value: &str| {
        value
            .strip_prefix('r')
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|rotation| *rotation < 4)
    };
    let family = |name: &str, value: &str| match name {
        "shared" => Some(ExtraMaskFactorFamily::Shared),
        "dense" => value
            .parse::<usize>()
            .ok()
            .map(ExtraMaskFactorFamily::Dense),
        _ => None,
    };

    match parts.as_slice() {
        ["add", "g", "shared", "pure", exponent] => {
            extra_g.push(ExtraMaskFactorSpec {
                family: ExtraMaskFactorFamily::Shared,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: 0,
                add_one: false,
            });
        }
        ["add", "g", "shared", exponent] => {
            extra_g.push(ExtraMaskFactorSpec {
                family: ExtraMaskFactorFamily::Shared,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: 0,
                add_one: true,
            });
        }
        ["add", "g", "dense", dense_family, exponent] => {
            extra_g.push(ExtraMaskFactorSpec {
                family: family("dense", dense_family).ok_or(StateOnlyHidingRankGateError::Shape)?,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: 0,
                add_one: true,
            });
        }
        ["add", "shared", exponent, rotation] => {
            masks.push(ExtraMaskFactorSpec {
                family: ExtraMaskFactorFamily::Shared,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: false,
            });
        }
        ["add", "dense", dense_family, exponent, rotation] => {
            masks.push(ExtraMaskFactorSpec {
                family: family("dense", dense_family).ok_or(StateOnlyHidingRankGateError::Shape)?,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: false,
            });
        }
        ["add", "selector", row, rotation] => {
            let row = row
                .parse::<usize>()
                .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
            if row >= TRACE_ROWS {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            masks.push(ExtraMaskFactorSpec {
                family: ExtraMaskFactorFamily::Selector(row),
                // The selector has individual degree one.  The exponent is
                // retained as one so the existing degree report stays a
                // conservative per-variable bound.
                exponent: 1,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: false,
            });
        }
        ["add", "selector4", row] => {
            let row = row
                .parse::<usize>()
                .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
            if row >= TRACE_ROWS {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            for tower_rotation in 0..4 {
                masks.push(ExtraMaskFactorSpec {
                    family: ExtraMaskFactorFamily::Selector(row),
                    exponent: 1,
                    tower_rotation,
                    add_one: false,
                });
            }
        }
        ["add", "selector20", "owner"] => {
            // Fixed, schedule-independent basis for every affine combination
            // of the five owner-key trajectory rows that support the exact
            // four-row semantic compatibility quotient.  This is a broad
            // existence screen; if it hits, a second pass must minimize the
            // selected columns before any wire is considered.
            for row in 1..=5 {
                for tower_rotation in 0..4 {
                    masks.push(ExtraMaskFactorSpec {
                        family: ExtraMaskFactorFamily::Selector(row),
                        exponent: 1,
                        tower_rotation,
                        add_one: false,
                    });
                }
            }
        }
        ["replace", "g", "shared", exponent, rotation] => {
            g = ExtraMaskFactorSpec {
                family: ExtraMaskFactorFamily::Shared,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: true,
            };
        }
        ["replace", "g", "dense", dense_family, exponent, rotation] => {
            g = ExtraMaskFactorSpec {
                family: family("dense", dense_family).ok_or(StateOnlyHidingRankGateError::Shape)?,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: true,
            };
        }
        ["replace", column, "shared", exponent, rotation] => {
            let column = column
                .parse::<usize>()
                .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
            if column >= masks.len() {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            masks[column] = ExtraMaskFactorSpec {
                family: ExtraMaskFactorFamily::Shared,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: false,
            };
        }
        ["replace", column, "dense", dense_family, exponent, rotation] => {
            let column = column
                .parse::<usize>()
                .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
            if column >= masks.len() {
                return Err(StateOnlyHidingRankGateError::Shape);
            }
            masks[column] = ExtraMaskFactorSpec {
                family: family("dense", dense_family).ok_or(StateOnlyHidingRankGateError::Shape)?,
                exponent: exponent
                    .parse()
                    .map_err(|_| StateOnlyHidingRankGateError::Shape)?,
                tower_rotation: parse_rotation(rotation)
                    .ok_or(StateOnlyHidingRankGateError::Shape)?,
                add_one: false,
            };
        }
        _ => return Err(StateOnlyHidingRankGateError::Shape),
    }
    Ok((masks, g, extra_g))
}

/// Run one exact AtomicV3/profile21 FullShared repair candidate.  Candidate
/// strings are intentionally explicit and stable, for example
/// `add-shared-23-r0`, `replace-4-shared-23-r2`, or
/// `replace-g-dense-7-26-r0`.
fn run_atomic_state_only_extra_mask_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    scalar_m_delta: QM31,
    candidate: &str,
) -> Result<ExtraMaskRankReport, StateOnlyHidingRankGateError> {
    let started = Instant::now();
    let (representative_screen_only, parsed_candidate) = candidate
        .strip_prefix("fast-")
        .map_or((false, candidate), |candidate| (true, candidate));
    let post_alpha_scalar_m_probe = parsed_candidate == "post_alpha_scalar_m";
    let parsed_factor_candidate = if post_alpha_scalar_m_probe {
        "baseline"
    } else {
        parsed_candidate
    };
    let (mask_factors, g_factor, extra_g_factors) = parse_candidate(parsed_factor_candidate)?;
    if schedule.query_count != 16 || schedule.prefix.z.len() != STATE_ONLY_HIDING_SUMCHECK_ROUNDS {
        return Err(StateOnlyHidingRankGateError::Shape);
    }

    let domain_log = STATE_ONLY_LOG_ROWS + 9;
    let encoder = CircleEncoder::new_for_domain_log(domain_log);
    let rows = row_public_maps(
        &encoder,
        domain_log,
        schedule,
        PcsSchedule::Arity4x4,
        RankLayout::AtomicV3,
    )?;
    let layer0_m31 = rows[0].layer0_m31.len();
    let c1_raw_m31 = layer0_m31 + 12;
    let g_raw_m31 = 4 * (layer0_m31 + 3);
    let pcs_tail_qm31 = rows[0].pcs_tail.len();
    let h_raw_qm31 = layer0_m31 + 3;
    let joint_pcs_m31 = 4 * (h_raw_qm31 + pcs_tail_qm31);
    let sc_m31 = 4 * STATE_ONLY_HIDING_SUMCHECK_QM31_OBSERVATIONS;
    let aux_m31 = sc_m31 + joint_pcs_m31;
    let lagrange = lagrange_basis();

    let mut active = [false; TRACE_ROWS];
    for &row in atomic_state_only_copy_active_rows_v3() {
        active[usize::from(row)] = true;
    }
    let inactive = (0..TRACE_ROWS)
        .filter(|row| !active[*row])
        .collect::<Vec<_>>();
    let global_dependent = inactive[0];

    let mask_only_columns = mask_factors.len();
    let h_generator_index = STATE_ONLY_HIDING_C1_COLUMNS + mask_only_columns;
    let g_generator_index = h_generator_index + 1;
    let last_generator_index = g_generator_index + extra_g_factors.len();
    let powers = (0..=last_generator_index)
        .map(|column| gamma_power(schedule.prefix.gamma, column))
        .collect::<Vec<_>>();

    let mut sumcheck_kernel_images = Vec::new();
    let mut sumcheck_kernel_source_ids = Vec::new();
    let mut basis_columns = 0usize;
    let mut raw_minor_sources = Vec::new();
    let mut raw_minor_rows = Vec::new();
    let mut raw_minor_values = Vec::new();
    let mut raw_block_offset = 0usize;
    let mut c1_raw_ranks = Vec::new();
    let mut semantic_raw_echelons = Vec::with_capacity(STATE_ONLY_HIDING_C1_COLUMNS);

    let cells = atomic_state_only_relation_free_mask_cells_v3()
        .map_err(|_| StateOnlyHidingRankGateError::Layout)?;
    let mut cells_by_column = vec![Vec::new(); STATE_ONLY_HIDING_C1_COLUMNS];
    for cell in cells {
        cells_by_column[usize::from(cell.column)].push(usize::from(cell.row));
    }

    // The selected semantic schedule remains bit-for-bit FullShared.
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
                    FactorSchedule::FullSharedLinear,
                    None,
                )
            })
            .collect::<Vec<_>>();
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for &row in cells {
            if row == dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[column],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            debug_assert_eq!(aux.len(), aux_m31);
            let source_id = basis_columns;
            basis_columns += 1;
            match raw.reduce_with_pivot(raw_image, aux) {
                CarryReduction::Pivot { row, value } => {
                    raw_minor_sources.push(source_id);
                    raw_minor_rows.push(raw_block_offset + row);
                    raw_minor_values.push(value);
                }
                CarryReduction::Kernel(kernel) => {
                    sumcheck_kernel_images.push(kernel);
                    sumcheck_kernel_source_ids.push(source_id);
                }
            }
        }
        c1_raw_ranks.push(raw.rank);
        semantic_raw_echelons.push(raw);
        raw_block_offset += c1_raw_m31;
    }

    // Existing and optional ordinary M31 mask-only columns.  Each is
    // conditioned on its literal q*4 M31 leaf cells plus three QM31 terminal
    // openings before its masked-sumcheck and PCS carry is retained.
    for (mask_column, &factor) in mask_factors.iter().enumerate() {
        let observations = (0..TRACE_ROWS)
            .map(|row| extra_mask_sumcheck_observations(row, &schedule.prefix.z, &lagrange, factor))
            .collect::<Vec<_>>();
        let generator = STATE_ONLY_HIDING_C1_COLUMNS + mask_column;
        let mut raw = CarryEchelon::new(c1_raw_m31);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = c1_raw_difference(&rows, row, subtract);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &observations,
                QM31::ONE,
                powers[generator],
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            let source_id = basis_columns;
            basis_columns += 1;
            match raw.reduce_with_pivot(raw_image, aux) {
                CarryReduction::Pivot { row, value } => {
                    raw_minor_sources.push(source_id);
                    raw_minor_rows.push(raw_block_offset + row);
                    raw_minor_values.push(value);
                }
                CarryReduction::Kernel(kernel) => {
                    sumcheck_kernel_images.push(kernel);
                    sumcheck_kernel_source_ids.push(source_id);
                }
            }
        }
        c1_raw_ranks.push(raw.rank);
        raw_block_offset += c1_raw_m31;
    }

    let g_observations = (0..TRACE_ROWS)
        .map(|row| extra_mask_sumcheck_observations(row, &schedule.prefix.z, &lagrange, g_factor))
        .collect::<Vec<_>>();
    let mut g_raw = CarryEchelon::new(g_raw_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row == global_dependent {
                continue;
            }
            let subtract = (!active[row]).then_some(global_dependent);
            let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
            let aux = scaled_aux_difference(
                &rows,
                row,
                subtract,
                &g_observations,
                basis,
                basis.mul(powers[g_generator_index]),
                4 * h_raw_qm31,
                joint_pcs_m31,
            );
            let source_id = basis_columns;
            basis_columns += 1;
            match g_raw.reduce_with_pivot(raw_image, aux) {
                CarryReduction::Pivot { row, value } => {
                    raw_minor_sources.push(source_id);
                    raw_minor_rows.push(raw_block_offset + row);
                    raw_minor_values.push(value);
                }
                CarryReduction::Kernel(kernel) => {
                    sumcheck_kernel_images.push(kernel);
                    sumcheck_kernel_source_ids.push(source_id);
                }
            }
        }
    }
    raw_block_offset += g_raw_m31;

    // Optional additional full-domain QM31 G-like lanes.  Unlike the
    // historical zero-coefficient tail control, every lane participates in
    // the masked zerocheck with its own nonzero public factor.
    let mut extra_g_raw_ranks = Vec::with_capacity(extra_g_factors.len());
    for (extra_index, &factor) in extra_g_factors.iter().enumerate() {
        let observations = (0..TRACE_ROWS)
            .map(|row| extra_mask_sumcheck_observations(row, &schedule.prefix.z, &lagrange, factor))
            .collect::<Vec<_>>();
        let generator = g_generator_index + 1 + extra_index;
        let mut raw = CarryEchelon::new(g_raw_m31);
        for coordinate in 0..4 {
            let basis = state_only_mask_tower_basis(coordinate);
            for row in 0..TRACE_ROWS {
                if row == global_dependent {
                    continue;
                }
                let subtract = (!active[row]).then_some(global_dependent);
                let raw_image = qm31_raw_difference(&rows, row, subtract, basis);
                let aux = scaled_aux_difference(
                    &rows,
                    row,
                    subtract,
                    &observations,
                    basis,
                    basis.mul(powers[generator]),
                    4 * h_raw_qm31,
                    joint_pcs_m31,
                );
                let source_id = basis_columns;
                basis_columns += 1;
                match raw.reduce_with_pivot(raw_image, aux) {
                    CarryReduction::Pivot { row, value } => {
                        raw_minor_sources.push(source_id);
                        raw_minor_rows.push(raw_block_offset + row);
                        raw_minor_values.push(value);
                    }
                    CarryReduction::Kernel(kernel) => {
                        sumcheck_kernel_images.push(kernel);
                        sumcheck_kernel_source_ids.push(source_id);
                    }
                }
            }
        }
        extra_g_raw_ranks.push(raw.rank);
        raw_block_offset += g_raw_m31;
    }

    let raw_minor = RankMinorProvenance::from_parts(
        "extra_mask_raw_openings",
        raw_minor_sources,
        raw_minor_rows,
        raw_minor_values,
    );

    let mut sumcheck = CarryEchelon::new(sc_m31);
    let mut pcs_kernel_images = Vec::new();
    let mut pcs_kernel_source_ids = Vec::new();
    let mut sumcheck_minor_sources = Vec::new();
    let mut sumcheck_minor_rows = Vec::new();
    let mut sumcheck_minor_values = Vec::new();
    for (&source_id, image) in sumcheck_kernel_source_ids
        .iter()
        .zip(&sumcheck_kernel_images)
    {
        let (sc, pcs) = image.split_at(sc_m31);
        match sumcheck.reduce_with_pivot(sc.to_vec(), pcs.to_vec()) {
            CarryReduction::Pivot { row, value } => {
                sumcheck_minor_sources.push(source_id);
                sumcheck_minor_rows.push(row);
                sumcheck_minor_values.push(value);
            }
            CarryReduction::Kernel(kernel) => {
                pcs_kernel_images.push(kernel);
                pcs_kernel_source_ids.push(source_id);
            }
        }
    }
    let sumcheck_minor = RankMinorProvenance::from_parts(
        "extra_mask_sumcheck",
        sumcheck_minor_sources,
        sumcheck_minor_rows,
        sumcheck_minor_values,
    );

    let mut pcs_rank = ColumnEchelon::new(joint_pcs_m31);
    let mut pcs_minor_sources = Vec::new();
    let mut pcs_minor_rows = Vec::new();
    let mut pcs_minor_values = Vec::new();
    for (source_id, image) in pcs_kernel_source_ids.into_iter().zip(pcs_kernel_images) {
        if let Some((row, value)) = pcs_rank.insert_with_pivot_value(image) {
            pcs_minor_sources.push(source_id);
            pcs_minor_rows.push(row);
            pcs_minor_values.push(value);
        }
    }
    let pre_helper_pcs_rank = pcs_rank.rank;
    let h_scale = powers[h_generator_index];
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row == global_dependent {
                continue;
            }
            let source_id = basis_columns;
            if let Some((pivot, value)) = pcs_rank.insert_with_pivot_value(h_pcs_image(
                &rows,
                row,
                global_dependent,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            )) {
                pcs_minor_sources.push(source_id);
                pcs_minor_rows.push(pivot);
                pcs_minor_values.push(value);
            }
            basis_columns += 1;
        }
    }
    let pcs_minor = RankMinorProvenance::from_parts(
        "extra_mask_post_sumcheck_pcs",
        pcs_minor_sources,
        pcs_minor_rows,
        pcs_minor_values,
    );
    let pre_scalar_m_pcs_rank = pcs_rank.rank;

    let mut scalar_m_variables_qm31 = 0usize;
    let mut scalar_m_observations_qm31 = 0usize;
    let mut scalar_m_observation_rank_m31 = 0usize;
    let mut scalar_m_conditioned_kernel_m31 = 0usize;
    let mut scalar_m_new_pivots = Vec::new();
    let mut scalar_m_observation_sources = Vec::new();
    let mut scalar_m_observation_rows = Vec::new();
    let mut scalar_m_observation_values = Vec::new();
    let mut scalar_m_pcs_sources = Vec::new();
    let mut scalar_m_pcs_values = Vec::new();
    if post_alpha_scalar_m_probe {
        if scalar_m_delta == QM31::ZERO {
            return Err(StateOnlyHidingRankGateError::Layout);
        }
        const SCALAR_M_COEFFICIENTS: usize = TRACE_ROWS / FIBER_SLOTS;
        const SCALAR_M_OBSERVATIONS_QM31: usize = 1 + 16;
        let queries = &schedule.queries[..schedule.query_count];
        let indices = derive_circle_line_query_indices_for_count(
            queries,
            encoder.codeword_len() / FIBER_SLOTS,
        )
        .map_err(|_| StateOnlyHidingRankGateError::Shape)?;
        let tails = (0..SCALAR_M_COEFFICIENTS)
            .map(|coefficient| {
                first_later_coefficient_tail(
                    &encoder,
                    domain_log,
                    coefficient,
                    schedule,
                    &indices.later,
                    RankLayout::AtomicV3,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        if tails.iter().any(|tail| tail.len() != pcs_tail_qm31) {
            return Err(StateOnlyHidingRankGateError::Shape);
        }
        let query_values = (0..SCALAR_M_COEFFICIENTS)
            .map(|coefficient| {
                first_later_coefficient_query_values(
                    &encoder,
                    domain_log,
                    coefficient,
                    schedule,
                    queries,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let weights = first_later_weights(schedule, RankLayout::AtomicV3)?;
        let observation_columns = (0..SCALAR_M_COEFFICIENTS)
            .map(|coefficient| {
                let mut column = Vec::with_capacity(SCALAR_M_OBSERVATIONS_QM31);
                column.push(weights.weight_at(coefficient as u32));
                column.extend_from_slice(&query_values[coefficient]);
                column
            })
            .collect::<Vec<_>>();
        let mut quotient = CarryEchelon::new(4 * SCALAR_M_OBSERVATIONS_QM31);
        scalar_m_variables_qm31 = SCALAR_M_COEFFICIENTS;
        scalar_m_observations_qm31 = SCALAR_M_OBSERVATIONS_QM31;
        for coefficient in 0..SCALAR_M_COEFFICIENTS {
            for tower_coordinate in 0..4 {
                let basis = state_only_mask_tower_basis(tower_coordinate);
                let mut observation = Vec::with_capacity(4 * SCALAR_M_OBSERVATIONS_QM31);
                append_qm31_coordinates(
                    &mut observation,
                    observation_columns[coefficient]
                        .iter()
                        .copied()
                        .map(|value| value.mul(basis)),
                );
                let carry = first_later_pcs_image(
                    &tails[coefficient],
                    scalar_m_delta.mul(basis),
                    h_raw_qm31,
                );
                let source_id = 4 * coefficient + tower_coordinate;
                match quotient.reduce_with_pivot(observation, carry) {
                    CarryReduction::Pivot { row, value } => {
                        scalar_m_observation_sources.push(source_id);
                        scalar_m_observation_rows.push(row);
                        scalar_m_observation_values.push(value);
                    }
                    CarryReduction::Kernel(kernel) => {
                        if let Some((pivot, value)) = pcs_rank.insert_with_pivot_value(kernel) {
                            scalar_m_pcs_sources.push(source_id);
                            scalar_m_new_pivots.push(pivot);
                            scalar_m_pcs_values.push(value);
                        }
                    }
                }
            }
        }
        scalar_m_observation_rank_m31 = quotient.rank;
        scalar_m_conditioned_kernel_m31 = 4 * SCALAR_M_COEFFICIENTS - scalar_m_observation_rank_m31;
    }
    let scalar_m_observation_minor = RankMinorProvenance::from_parts(
        "post_alpha_scalar_m_observation",
        scalar_m_observation_sources,
        scalar_m_observation_rows,
        scalar_m_observation_values,
    );
    let scalar_m_pcs_minor = RankMinorProvenance::from_parts(
        "post_alpha_scalar_m_pcs",
        scalar_m_pcs_sources,
        scalar_m_new_pivots.clone(),
        scalar_m_pcs_values,
    );
    let pcs_base_rank = pcs_rank.rank;

    let mut declared = ColumnEchelon::new(joint_pcs_m31);
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for row in 0..TRACE_ROWS {
            if row != global_dependent {
                declared.insert(combined_pcs_image(
                    &rows,
                    row,
                    basis,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &inactive {
            if row != global_dependent {
                declared.insert(h_pcs_image(
                    &rows,
                    row,
                    global_dependent,
                    basis,
                    h_scale,
                    h_raw_qm31,
                    pcs_tail_qm31,
                ));
            }
        }
    }
    let active_rows = (0..TRACE_ROWS)
        .filter(|row| active[*row])
        .collect::<Vec<_>>();
    let active_dependent = *active_rows
        .last()
        .ok_or(StateOnlyHidingRankGateError::Layout)?;
    let mut active_containment = pcs_rank.clone();
    for coordinate in 0..4 {
        let basis = state_only_mask_tower_basis(coordinate);
        for &row in &active_rows[..active_rows.len() - 1] {
            let image = h_pcs_image(
                &rows,
                row,
                active_dependent,
                basis,
                h_scale,
                h_raw_qm31,
                pcs_tail_qm31,
            );
            declared.insert(image.clone());
            active_containment.insert(image);
        }
    }
    if active_containment.rank != pcs_base_rank {
        return Err(StateOnlyHidingRankGateError::HelperContainment {
            before: pcs_base_rank,
            after: active_containment.rank,
        });
    }

    // Conservative language-independent semantic source: every M31 cell in
    // each of the 16 real semantic columns, with its exact raw and gamma PCS
    // image.  This is deliberately the 716-vs-712 repair target, not the
    // weaker language-aware quotient.
    let mut semantic_augmented = pcs_rank.clone();
    let mut compatibility = CarryEchelon::new(sc_m31);
    let mut semantic_sources = Vec::new();
    let mut semantic_rows = Vec::new();
    let mut semantic_values = Vec::new();
    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
        let rows_to_test: Box<dyn Iterator<Item = usize>> = if representative_screen_only {
            // These are the four canonical compatibility-pivot sources of
            // the frozen baseline.  A screen hit is always rerun against all
            // 16*(1024-1) legal cell directions before it is reported as a
            // repair.
            match column {
                // c0/r1..r4 establish the exact four-row compatibility
                // echelon; c0/r5 is its first uncovered PCS representative.
                0 => Box::new(1..6),
                // The next three tower-coordinate representatives.
                1..=3 => Box::new(1..2),
                _ => Box::new(0..0),
            }
        } else {
            Box::new(1..TRACE_ROWS)
        };
        for row in rows_to_test {
            // Atomic row zero is a fixed public owner-key invocation row and
            // therefore not a same-statement semantic-difference source.
            if row == 0 {
                continue;
            }
            let source_id = column * TRACE_ROWS + row;
            let raw = c1_raw_difference(&rows, row, None);
            let mut carry = vec![M31::ZERO; aux_m31];
            let pcs = scaled_qm31_difference(&rows[row].pcs_tail, None, powers[column]);
            let pcs_start = sc_m31 + 4 * h_raw_qm31;
            carry[pcs_start..pcs_start + pcs.len()].copy_from_slice(&pcs);
            let post_raw = semantic_raw_echelons[column]
                .quotient_existing(raw, carry)
                .ok_or(StateOnlyHidingRankGateError::WitnessRawQuotient { source: source_id })?;
            let (sc, pcs) = post_raw.split_at(sc_m31);
            let (sc_remainder, pcs_remainder) =
                sumcheck.remainder_existing(sc.to_vec(), pcs.to_vec());
            match compatibility.reduce_with_pivot(sc_remainder, pcs_remainder) {
                CarryReduction::Pivot { .. } => {}
                CarryReduction::Kernel(post_sumcheck) => {
                    if let Some((pivot, value)) =
                        semantic_augmented.insert_with_pivot_value(post_sumcheck)
                    {
                        semantic_sources.push(source_id);
                        semantic_rows.push(pivot);
                        semantic_values.push(value);
                    }
                }
            }
        }
    }
    let semantic_minor = RankMinorProvenance::from_parts(
        "extra_mask_conservative_semantic",
        semantic_sources,
        semantic_rows.clone(),
        semantic_values,
    );

    let mut legal_sumcheck_augmented = semantic_augmented.clone();
    let mut legal_rows = Vec::new();
    for sc_row in 4..sc_m31 {
        let mut sc = vec![M31::ZERO; sc_m31];
        sc[sc_row] = M31::ONE;
        let pcs = vec![M31::ZERO; joint_pcs_m31];
        let (sc_remainder, pcs_remainder) = sumcheck.remainder_existing(sc, pcs);
        match compatibility.reduce_with_pivot(sc_remainder, pcs_remainder) {
            CarryReduction::Pivot { .. } => {}
            CarryReduction::Kernel(post_sumcheck) => {
                if let Some(pivot) = legal_sumcheck_augmented.insert_with_pivot(post_sumcheck) {
                    legal_rows.push(pivot);
                }
            }
        }
    }

    let extra_columns = mask_only_columns - STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
    let extra_g_columns = extra_g_factors.len();
    let maximum_factor_degree = mask_factors
        .iter()
        .map(|factor| factor.exponent)
        .chain(core::iter::once(g_factor.exponent))
        .chain(extra_g_factors.iter().map(|factor| factor.exponent))
        .max()
        .unwrap_or(0);
    let maximum_masked_oracle_degree = maximum_factor_degree + 1;
    let layer0_leaf_delta_bytes = 4 * core::mem::size_of::<u32>() * extra_columns
        + 4 * 4 * core::mem::size_of::<u32>() * extra_g_columns;
    let q16_opened_leaf_delta_bytes = schedule.query_count * layer0_leaf_delta_bytes;
    let three_terminal_opening_delta_bytes = 3 * 16 * (extra_columns + extra_g_columns);
    let scalar_m_query_and_tau_delta_bytes = if post_alpha_scalar_m_probe {
        (schedule.query_count + 1) * 16
    } else {
        0
    };
    let factor_schedule_fingerprint =
        factor_schedule_fingerprint(&mask_factors, g_factor, &extra_g_factors);

    Ok(ExtraMaskRankReport {
        candidate: candidate.to_owned(),
        representative_screen_only,
        mask_only_factors: mask_factors,
        explicit_g_factor: g_factor,
        extra_g_factors,
        extra_mask_only_columns: extra_columns,
        extra_g_columns,
        maximum_factor_degree,
        maximum_masked_oracle_degree,
        degree_27_soundness_shape_preserved: maximum_masked_oracle_degree <= 27,
        c1_raw_rows_per_column_m31: c1_raw_m31,
        c1_raw_ranks_m31: c1_raw_ranks,
        g_raw_rows_m31: g_raw_m31,
        g_raw_rank_m31: g_raw.rank,
        extra_g_raw_ranks_m31: extra_g_raw_ranks,
        masked_sumcheck_rows_m31: sc_m31,
        masked_sumcheck_rank_m31: sumcheck.rank,
        pre_helper_pcs_rank_m31: pre_helper_pcs_rank,
        pre_scalar_m_pcs_rank_m31: pre_scalar_m_pcs_rank,
        pcs_rank_m31: pcs_base_rank,
        ambient_rank_m31: declared.rank,
        ambient_deficit_m31: declared.rank.saturating_sub(pcs_base_rank),
        conservative_semantic_augmented_rank_m31: semantic_augmented.rank,
        conservative_semantic_new_pivots_m31: semantic_rows,
        legal_sumcheck_augmented_rank_m31: legal_sumcheck_augmented.rank,
        legal_sumcheck_new_pivots_m31: legal_rows,
        compatibility_rank_m31: compatibility.rank,
        post_alpha_scalar_m_probe,
        scalar_m_variables_qm31,
        scalar_m_observations_qm31,
        scalar_m_observation_rank_m31,
        scalar_m_conditioned_kernel_m31,
        scalar_m_new_pivots_m31: scalar_m_new_pivots,
        scalar_m_observation_minor_fingerprint: scalar_m_observation_minor.fingerprint,
        scalar_m_pcs_minor_fingerprint: scalar_m_pcs_minor.fingerprint,
        scalar_m_contains_conservative_semantic_superset: semantic_augmented.rank == pcs_base_rank,
        raw_minor_fingerprint: raw_minor.fingerprint,
        sumcheck_minor_fingerprint: sumcheck_minor.fingerprint,
        pcs_minor_fingerprint: pcs_minor.fingerprint,
        semantic_minor_fingerprint: semantic_minor.fingerprint,
        factor_schedule_fingerprint,
        generator_width: STATE_ONLY_HIDING_C1_COLUMNS + mask_only_columns + 2 + extra_g_columns,
        c1_columns: STATE_ONLY_HIDING_C1_COLUMNS + mask_only_columns,
        c2_columns: 2 + extra_g_columns,
        layer0_leaf_delta_bytes,
        q16_opened_leaf_delta_bytes,
        three_terminal_opening_delta_bytes,
        estimated_serialized_opening_delta_bytes: q16_opened_leaf_delta_bytes
            + three_terminal_opening_delta_bytes,
        scalar_m_query_and_tau_delta_bytes,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

pub fn probe_atomic_state_only_extra_mask_rank(
    schedule: &StateOnlyTranscriptScheduleResult,
    candidate: &str,
) -> Result<ExtraMaskRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_extra_mask_rank(schedule, QM31::ONE, candidate)
}

pub fn probe_atomic_state_only_profile21_extra_mask_rank(
    schedule: &StateOnlyProfile21TranscriptScheduleResult,
    candidate: &str,
) -> Result<ExtraMaskRankReport, StateOnlyHidingRankGateError> {
    run_atomic_state_only_extra_mask_rank(&schedule.base, schedule.delta, candidate)
}
