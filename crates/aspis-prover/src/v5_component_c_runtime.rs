//! Runtime-sized Component-C downstream evaluation for the provisional v5 path.
//!
//! The offline F-matrix generator historically evaluated only the collision-free
//! `18 + 18 + 18` later-query layout.  The real host artifact instead carries
//! the sorted/deduplicated lists produced by
//! `derive_circle_line_query_indices_for_count`, so its downstream view has
//! `40 + 4 * (n1 + n2 + n3)` values.  This module is the single arithmetic
//! implementation for both shapes.  The fixed F-matrix path calls it and then
//! checks that the runtime result has 256 entries.
//!
//! This remains feature-gated candidate code.  It changes no v4 proof bytes or
//! verifier dispatch.

use std::vec::Vec;

use aspis_core::circle::SecureCirclePoint;
use aspis_core::circle_line_merkle::{
    derive_circle_line_query_indices_for_count, CIRCLE_LINE_QUERY_SHIFTS,
};
use aspis_core::circle_prefix::{
    CANDIDATE_FINAL_POLY_LEN, CANDIDATE_OOD_SAMPLES, CANDIDATE_ROUND_COUNT,
};
use aspis_core::field::{P, QM31};
use aspis_core::sumcheck::SumcheckPolynomial;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3;
use aspis_statement::{binary_successor_point, xor12_point};

use crate::circle_candidate::{
    fold_candidate_codeword_round_for_domain_log, CircleCandidateError, CircleEncoder,
};

use super::component_c::{V5ComponentCLane, V5_C_FREE_COORDINATES, V5_C_ROWS};
use super::real_host_proof::{V5RealHostArtifact, V5_REAL_HOST_QUERY_COUNT};
use super::relation_prover::{V5IncrementalRelation, V5RelationProverError};
use super::spend_messages::V5_LAYER_ZERO_LEAVES;
use super::split_layer_zero::v5_structured_terminal_covector;
use super::{V5_CODEWORD_LEN, V5_DOMAIN_LOG};

pub const V5_COMPONENT_C_RUNTIME_RELATION_ROWS: usize = 36;
pub const V5_COMPONENT_C_RUNTIME_FINAL_ROWS: usize = 4;
pub const V5_COMPONENT_C_RUNTIME_FIXED_ROWS: usize = 40;
pub const V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT: usize = 18;
const V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS: [u32; 3] = [
    (V5_LAYER_ZERO_LEAVES >> CIRCLE_LINE_QUERY_SHIFTS[0]) as u32,
    (V5_LAYER_ZERO_LEAVES >> CIRCLE_LINE_QUERY_SHIFTS[1]) as u32,
    (V5_LAYER_ZERO_LEAVES >> CIRCLE_LINE_QUERY_SHIFTS[2]) as u32,
];

const _: () = assert!(
    V5_COMPONENT_C_RUNTIME_RELATION_ROWS == CANDIDATE_ROUND_COUNT * (CANDIDATE_OOD_SAMPLES + 7)
);
const _: () = assert!(V5_COMPONENT_C_RUNTIME_FINAL_ROWS == CANDIDATE_FINAL_POLY_LEN);
const _: () = assert!(
    V5_COMPONENT_C_RUNTIME_FIXED_ROWS
        == V5_COMPONENT_C_RUNTIME_RELATION_ROWS + V5_COMPONENT_C_RUNTIME_FINAL_ROWS
);
const _: () = assert!(V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT == V5_REAL_HOST_QUERY_COUNT);
const _: () = assert!(V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS[0] == 32768);
const _: () = assert!(V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS[1] == 8192);
const _: () = assert!(V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS[2] == 2048);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5ComponentCRuntimeError {
    OpeningIndexDrift,
    PointScheduleDrift,
    TerminalCovectorShape {
        expected: usize,
        actual: usize,
    },
    TerminalCovectorDrift,
    MessageShape {
        expected: usize,
        actual: usize,
    },
    CodewordShape {
        expected: usize,
        actual: usize,
    },
    LaterIndexOutOfRange {
        layer: u8,
        index: u32,
        len: usize,
    },
    NonCanonicalRelationTable {
        round: usize,
        slot: u8,
        index: usize,
    },
    OutputLengthOverflow,
    Relation(V5RelationProverError),
    Circle(CircleCandidateError),
}

/// Public, witness-independent relation tables observed by the exact runtime
/// evaluator.  These are the concrete `ood0..3` and `poly0..3` fields of the
/// maintained Component-C schedule model, in the same round/sample order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCRuntimeRelationTables {
    pub ood: [[Vec<QM31>; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub polynomial: [Vec<QM31>; CANDIDATE_ROUND_COUNT],
}

impl V5ComponentCRuntimeRelationTables {
    fn empty() -> Self {
        Self {
            ood: [
                [Vec::new(), Vec::new()],
                [Vec::new(), Vec::new()],
                [Vec::new(), Vec::new()],
                [Vec::new(), Vec::new()],
            ],
            polynomial: [Vec::new(), Vec::new(), Vec::new(), Vec::new()],
        }
    }
}

impl From<V5RelationProverError> for V5ComponentCRuntimeError {
    fn from(error: V5RelationProverError) -> Self {
        Self::Relation(error)
    }
}

impl From<CircleCandidateError> for V5ComponentCRuntimeError {
    fn from(error: CircleCandidateError) -> Self {
        Self::Circle(error)
    }
}

/// Exact public schedule needed by the Component-C downstream linear map.
///
/// `later_fibres` retains the real sorted/deduplicated runtime order.  It is
/// deliberately not widened to `[[u32; 18]; 3]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct V5ComponentCRuntimeSchedule {
    pub points: [[QM31; 10]; 3],
    pub terminal_covector: [QM31; V5_C_ROWS],
    pub inactive_masks: [u16; 64],
    pub kappa: QM31,
    pub circle_ood_points: [SecureCirclePoint; CANDIDATE_OOD_SAMPLES],
    pub line_ood_points: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT - 1],
    pub ood_mixes: [[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    pub alphas: [QM31; CANDIDATE_ROUND_COUNT],
    pub later_fibres: [Vec<u32>; 3],
}

/// Validate the exact count and range conditions consumed by one later-layer
/// arity-four opening.  The shared query derivation already guarantees these
/// conditions for a valid 18-query host artifact; checking them at the runtime
/// schedule boundary makes that invariant executable and source-extractable.
fn validate_component_c_runtime_later_layer(
    fibres: &[u32],
    layer: u8,
    fibre_limit: u32,
) -> Result<(), V5ComponentCRuntimeError> {
    if fibres.len() > V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT {
        return Err(V5ComponentCRuntimeError::OutputLengthOverflow);
    }
    let mut ordinal = 0usize;
    while ordinal < fibres.len() {
        let fibre = fibres[ordinal];
        if fibre >= fibre_limit {
            return Err(V5ComponentCRuntimeError::LaterIndexOutOfRange {
                layer,
                index: fibre,
                len: 4 * fibre_limit as usize,
            });
        }
        ordinal += 1;
    }
    Ok(())
}

/// Validate one public relation-weight table before it enters the maintained
/// Component-C schedule. Slots 0 and 1 are the two OOD tables; slot 2 is the
/// polynomial table. The check is representation-only and does not alter any
/// field arithmetic or serialized value.
fn validate_component_c_runtime_relation_table(
    table: &[QM31],
    round: usize,
    slot: u8,
) -> Result<(), V5ComponentCRuntimeError> {
    let mut index = 0usize;
    while index < table.len() {
        let value = table[index];
        if value.c0.a.0 >= P || value.c0.b.0 >= P || value.c1.a.0 >= P || value.c1.b.0 >= P {
            return Err(V5ComponentCRuntimeError::NonCanonicalRelationTable { round, slot, index });
        }
        index += 1;
    }
    Ok(())
}

impl V5ComponentCRuntimeSchedule {
    /// Reconstruct the schedule from the real host artifact and rederive every
    /// query list through the shared core routine.  No query index is accepted
    /// from proof bytes.
    pub fn from_real_host_artifact(
        artifact: &V5RealHostArtifact,
    ) -> Result<Self, V5ComponentCRuntimeError> {
        let indices =
            derive_circle_line_query_indices_for_count(&artifact.queries, V5_LAYER_ZERO_LEAVES)
                .map_err(|_| V5ComponentCRuntimeError::OpeningIndexDrift)?;
        if indices != artifact.opening_indices {
            return Err(V5ComponentCRuntimeError::OpeningIndexDrift);
        }
        validate_component_c_runtime_later_layer(
            &indices.later[0],
            1,
            V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS[0],
        )?;
        validate_component_c_runtime_later_layer(
            &indices.later[1],
            2,
            V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS[1],
        )?;
        validate_component_c_runtime_later_layer(
            &indices.later[2],
            3,
            V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS[2],
        )?;

        let z = artifact.semantic_sumcheck.challenges;
        let points = [z, binary_successor_point(&z), xor12_point(&z)];
        if artifact.relation_claims.points != points {
            return Err(V5ComponentCRuntimeError::PointScheduleDrift);
        }
        let expected_terminal = v5_structured_terminal_covector(&z);
        if artifact.relation_claims.terminal_covector.len() != V5_C_ROWS {
            return Err(V5ComponentCRuntimeError::TerminalCovectorShape {
                expected: V5_C_ROWS,
                actual: artifact.relation_claims.terminal_covector.len(),
            });
        }
        if artifact.relation_claims.terminal_covector != expected_terminal {
            return Err(V5ComponentCRuntimeError::TerminalCovectorDrift);
        }
        let terminal_covector = expected_terminal.try_into().map_err(|values: Vec<QM31>| {
            V5ComponentCRuntimeError::TerminalCovectorShape {
                expected: V5_C_ROWS,
                actual: values.len(),
            }
        })?;

        Ok(Self {
            points,
            terminal_covector,
            inactive_masks: atomic_state_only_copy_inactive_row_masks_v3(),
            kappa: artifact.challenges.kappa,
            circle_ood_points: artifact.ood_points_circle[0],
            line_ood_points: artifact.ood_points_line,
            ood_mixes: artifact.ood_mixes,
            alphas: artifact.alphas,
            later_fibres: indices.later,
        })
    }

    pub fn later_counts(&self) -> [usize; 3] {
        [
            self.later_fibres[0].len(),
            self.later_fibres[1].len(),
            self.later_fibres[2].len(),
        ]
    }
}

pub fn component_c_runtime_downstream_rows(later_counts: [usize; 3]) -> Option<usize> {
    if later_counts[0] > V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT
        || later_counts[1] > V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT
        || later_counts[2] > V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT
    {
        return None;
    }
    Some(
        V5_COMPONENT_C_RUNTIME_FIXED_ROWS
            + 4 * (later_counts[0] + later_counts[1] + later_counts[2]),
    )
}

/// One canonical row tag in the runtime-sized downstream view.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5ComponentCRuntimeRow {
    /// One of the four `2 OOD || 7 polynomial` relation blocks.
    Relation { round: u8, slot: u8 },
    /// One scalar from a flattened arity-four later-opening block.
    Later { layer: u8, index: usize },
    /// One of the four final coefficients.
    Final { coefficient: u8 },
}

/// Decode one flat row into the canonical runtime tag.
///
/// `later_value_counts` counts scalar values, not fibres, so a layer with `n`
/// deduplicated fibres contributes exactly `4*n` consecutive rows.
pub fn component_c_runtime_downstream_row(
    later_value_counts: [usize; 3],
    row: usize,
) -> Option<V5ComponentCRuntimeRow> {
    if row < 36 {
        return Some(V5ComponentCRuntimeRow::Relation {
            round: (row / 9) as u8,
            slot: (row % 9) as u8,
        });
    }

    let mut tail = row - 36;
    if tail < later_value_counts[0] {
        return Some(V5ComponentCRuntimeRow::Later {
            layer: 0,
            index: tail,
        });
    }
    tail -= later_value_counts[0];
    if tail < later_value_counts[1] {
        return Some(V5ComponentCRuntimeRow::Later {
            layer: 1,
            index: tail,
        });
    }
    tail -= later_value_counts[1];
    if tail < later_value_counts[2] {
        return Some(V5ComponentCRuntimeRow::Later {
            layer: 2,
            index: tail,
        });
    }
    tail -= later_value_counts[2];
    if tail < 4 {
        return Some(V5ComponentCRuntimeRow::Final {
            coefficient: tail as u8,
        });
    }
    None
}

/// Return one value from the canonical runtime downstream row order.
///
/// This accessor is shared with the packer so the production branch structure
/// is the same structure proved by the Rust-to-Lean correspondence.  The six
/// segments are `36 relation || later-1 || later-2 || later-3 || 4 final`, with
/// each relation round internally ordered as `2 OOD || 7 polynomial`.
pub fn component_c_runtime_downstream_value_at(
    ood_values: &[[QM31; 2]; 4],
    polynomials: &[SumcheckPolynomial; 4],
    later: &[Vec<QM31>; 3],
    final_coefficients: &[QM31; 4],
    row: usize,
) -> Option<QM31> {
    let tag =
        component_c_runtime_downstream_row([later[0].len(), later[1].len(), later[2].len()], row);
    match tag {
        None => None,
        Some(V5ComponentCRuntimeRow::Relation { round, slot }) => {
            let round = usize::from(round);
            let slot = usize::from(slot);
            if slot < 2 {
                Some(ood_values[round][slot])
            } else {
                Some(polynomials[round][slot - 2])
            }
        }
        Some(V5ComponentCRuntimeRow::Later { layer, index }) => {
            Some(later[usize::from(layer)][index])
        }
        Some(V5ComponentCRuntimeRow::Final { coefficient }) => {
            Some(final_coefficients[usize::from(coefficient)])
        }
    }
}

/// Canonical runtime row packer: four repetitions of `2 OOD || 7 polynomial`,
/// the three deduplicated later layers in their supplied order, then four final
/// coefficients.
pub fn pack_component_c_runtime_downstream(
    ood_values: &[[QM31; CANDIDATE_OOD_SAMPLES]; CANDIDATE_ROUND_COUNT],
    polynomials: &[SumcheckPolynomial; CANDIDATE_ROUND_COUNT],
    later: &[Vec<QM31>; 3],
    final_coefficients: &[QM31; CANDIDATE_FINAL_POLY_LEN],
) -> Result<Vec<QM31>, V5ComponentCRuntimeError> {
    let counts = [later[0].len() / 4, later[1].len() / 4, later[2].len() / 4];
    if later[0].len() % 4 != 0 || later[1].len() % 4 != 0 || later[2].len() % 4 != 0 {
        return Err(V5ComponentCRuntimeError::OutputLengthOverflow);
    }
    let rows = match component_c_runtime_downstream_rows(counts) {
        Some(rows) => rows,
        None => return Err(V5ComponentCRuntimeError::OutputLengthOverflow),
    };
    let mut output = Vec::with_capacity(rows);

    let mut row = 0usize;
    while row < rows {
        let Some(value) = component_c_runtime_downstream_value_at(
            ood_values,
            polynomials,
            later,
            final_coefficients,
            row,
        ) else {
            return Err(V5ComponentCRuntimeError::OutputLengthOverflow);
        };
        output.push(value);
        row += 1;
    }
    debug_assert_eq!(output.len(), rows);
    Ok(output)
}

fn evaluate_component_c_runtime_relation_sample(
    schedule: &V5ComponentCRuntimeSchedule,
    relation: &mut V5IncrementalRelation,
    tables: &mut V5ComponentCRuntimeRelationTables,
    round: usize,
    sample: usize,
) -> Result<(), V5ComponentCRuntimeError> {
    if round == 0 {
        let point = schedule.circle_ood_points[sample];
        let (value, table) = relation.evaluate_circle_ood_with_table(point)?;
        validate_component_c_runtime_relation_table(&table, round, sample as u8)?;
        tables.ood[round][sample] = table;
        relation.add_circle_ood(point, value, schedule.ood_mixes[round][sample])?;
    } else {
        let point = schedule.line_ood_points[round - 1][sample];
        let (value, table) = relation.evaluate_line_ood_with_table(point)?;
        validate_component_c_runtime_relation_table(&table, round, sample as u8)?;
        tables.ood[round][sample] = table;
        relation.add_line_ood(point, value, schedule.ood_mixes[round][sample])?;
    }
    Ok(())
}

fn evaluate_component_c_runtime_relation_round(
    schedule: &V5ComponentCRuntimeSchedule,
    relation: &mut V5IncrementalRelation,
    tables: &mut V5ComponentCRuntimeRelationTables,
    round: usize,
) -> Result<(), V5ComponentCRuntimeError> {
    evaluate_component_c_runtime_relation_sample(schedule, relation, tables, round, 0)?;
    evaluate_component_c_runtime_relation_sample(schedule, relation, tables, round, 1)?;
    let (_, table) = relation.polynomial_with_table()?;
    validate_component_c_runtime_relation_table(&table, round, 2)?;
    tables.polynomial[round] = table;
    relation.fold(schedule.alphas[round])?;
    Ok(())
}

fn append_component_c_runtime_later_fibre(
    folded_codeword: &[QM31],
    target: &mut Vec<QM31>,
    layer: usize,
    fibre: u32,
) -> Result<(), V5ComponentCRuntimeError> {
    let start = 4usize.checked_mul(fibre as usize).ok_or(
        V5ComponentCRuntimeError::LaterIndexOutOfRange {
            layer: layer as u8 + 1,
            index: fibre,
            len: folded_codeword.len(),
        },
    )?;
    let end = start
        .checked_add(4)
        .ok_or(V5ComponentCRuntimeError::LaterIndexOutOfRange {
            layer: layer as u8 + 1,
            index: fibre,
            len: folded_codeword.len(),
        })?;
    if end > folded_codeword.len() {
        return Err(V5ComponentCRuntimeError::LaterIndexOutOfRange {
            layer: layer as u8 + 1,
            index: fibre,
            len: folded_codeword.len(),
        });
    }
    let mut slot = 0usize;
    while slot < 4 {
        target.push(folded_codeword[start + slot]);
        slot += 1;
    }
    Ok(())
}

fn evaluate_component_c_runtime_round(
    schedule: &V5ComponentCRuntimeSchedule,
    relation: &mut V5IncrementalRelation,
    folded_codeword: &mut Vec<QM31>,
    later: &mut [Vec<QM31>; 3],
    tables: &mut V5ComponentCRuntimeRelationTables,
    round: usize,
) -> Result<(), V5ComponentCRuntimeError> {
    evaluate_component_c_runtime_relation_round(schedule, relation, tables, round)?;
    *folded_codeword = fold_candidate_codeword_round_for_domain_log(
        folded_codeword,
        schedule.alphas[round],
        round,
        V5_DOMAIN_LOG,
    )?;

    if round < 3 {
        let mut ordinal = 0usize;
        let mut error = None;
        while ordinal < schedule.later_fibres[round].len() && error.is_none() {
            let fibre = schedule.later_fibres[round][ordinal];
            error = append_component_c_runtime_later_fibre(
                folded_codeword,
                &mut later[round],
                round,
                fibre,
            )
            .err();
            ordinal += 1;
        }
        if let Some(error) = error {
            return Err(error);
        }
    }
    Ok(())
}

/// Evaluate the exact runtime-sized downstream map through the shared relation
/// and circle/line fold implementations.
pub fn evaluate_component_c_runtime_private_view(
    schedule: &V5ComponentCRuntimeSchedule,
    coefficients: &[QM31],
    codeword: &[QM31],
    expected_inactive_claim: QM31,
) -> Result<Vec<QM31>, V5ComponentCRuntimeError> {
    if coefficients.len() != V5_C_ROWS {
        return Err(V5ComponentCRuntimeError::MessageShape {
            expected: V5_C_ROWS,
            actual: coefficients.len(),
        });
    }
    if codeword.len() != V5_CODEWORD_LEN {
        return Err(V5ComponentCRuntimeError::CodewordShape {
            expected: V5_CODEWORD_LEN,
            actual: codeword.len(),
        });
    }
    let (view, _) = evaluate_component_c_runtime_private_view_with_tables(
        schedule,
        coefficients,
        codeword,
        expected_inactive_claim,
    )?;
    Ok(view)
}

fn evaluate_component_c_runtime_private_view_with_tables(
    schedule: &V5ComponentCRuntimeSchedule,
    coefficients: &[QM31],
    codeword: &[QM31],
    expected_inactive_claim: QM31,
) -> Result<(Vec<QM31>, V5ComponentCRuntimeRelationTables), V5ComponentCRuntimeError> {
    if coefficients.len() != V5_C_ROWS {
        return Err(V5ComponentCRuntimeError::MessageShape {
            expected: V5_C_ROWS,
            actual: coefficients.len(),
        });
    }
    if codeword.len() != V5_CODEWORD_LEN {
        return Err(V5ComponentCRuntimeError::CodewordShape {
            expected: V5_CODEWORD_LEN,
            actual: codeword.len(),
        });
    }

    let kappa2 = schedule.kappa.square();
    let kappa3 = kappa2.mul(schedule.kappa);
    let mut relation = V5IncrementalRelation::new(
        coefficients.to_vec(),
        &schedule.points,
        [QM31::ONE, schedule.kappa, kappa2],
        schedule.inactive_masks,
        expected_inactive_claim,
        &schedule.terminal_covector,
        kappa3,
    )?;
    let mut folded_codeword = codeword.to_vec();
    let mut later = [
        Vec::with_capacity(4 * schedule.later_fibres[0].len()),
        Vec::with_capacity(4 * schedule.later_fibres[1].len()),
        Vec::with_capacity(4 * schedule.later_fibres[2].len()),
    ];
    let mut tables = V5ComponentCRuntimeRelationTables::empty();

    evaluate_component_c_runtime_round(
        schedule,
        &mut relation,
        &mut folded_codeword,
        &mut later,
        &mut tables,
        0,
    )?;
    evaluate_component_c_runtime_round(
        schedule,
        &mut relation,
        &mut folded_codeword,
        &mut later,
        &mut tables,
        1,
    )?;
    evaluate_component_c_runtime_round(
        schedule,
        &mut relation,
        &mut folded_codeword,
        &mut later,
        &mut tables,
        2,
    )?;
    evaluate_component_c_runtime_round(
        schedule,
        &mut relation,
        &mut folded_codeword,
        &mut later,
        &mut tables,
        3,
    )?;

    let trace = relation.finish()?;
    let view = pack_component_c_runtime_downstream(
        &trace.ood_values,
        &trace.sumchecks,
        &later,
        &trace.final_coefficients,
    )?;
    Ok((view, tables))
}

/// Public correspondence entrypoint for the real Component-C encoder and the
/// runtime schedule decoded from an accepted host artifact.
pub fn evaluate_component_c_runtime_downstream_correspondence(
    artifact: &V5RealHostArtifact,
    free: &[QM31; V5_C_FREE_COORDINATES],
) -> Result<Vec<QM31>, V5ComponentCRuntimeError> {
    let schedule = V5ComponentCRuntimeSchedule::from_real_host_artifact(artifact)?;
    let lane = V5ComponentCLane::encode_free_coordinates(free);
    let encoder = CircleEncoder::new_for_domain_log(V5_DOMAIN_LOG);
    let codeword = encoder.encode_c2_message(lane.values())?;
    evaluate_component_c_runtime_private_view(&schedule, lane.values(), &codeword, QM31::ZERO)
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31, P};

    fn q(value: u32) -> QM31 {
        QM31::from_cm31(CM31::from_m31(M31(value)))
    }

    #[test]
    fn runtime_row_count_is_exact_and_bounded_by_q18() {
        assert_eq!(component_c_runtime_downstream_rows([18, 18, 18]), Some(256));
        assert_eq!(component_c_runtime_downstream_rows([4, 3, 2]), Some(76));
        assert_eq!(component_c_runtime_downstream_rows([19, 0, 0]), None);
    }

    #[test]
    fn runtime_schedule_layer_validator_enforces_exact_count_and_ranges() {
        for (layer_index, fibre_limit) in V5_COMPONENT_C_RUNTIME_LATER_FIBRE_LIMITS
            .iter()
            .copied()
            .enumerate()
        {
            assert_eq!(
                validate_component_c_runtime_later_layer(
                    &[0, fibre_limit - 1],
                    layer_index as u8 + 1,
                    fibre_limit,
                ),
                Ok(())
            );
            assert_eq!(
                validate_component_c_runtime_later_layer(
                    &[fibre_limit],
                    layer_index as u8 + 1,
                    fibre_limit,
                ),
                Err(V5ComponentCRuntimeError::LaterIndexOutOfRange {
                    layer: layer_index as u8 + 1,
                    index: fibre_limit,
                    len: 4 * fibre_limit as usize,
                })
            );
        }

        let too_many = vec![0; V5_COMPONENT_C_RUNTIME_MAX_LATER_COUNT + 1];
        assert_eq!(
            validate_component_c_runtime_later_layer(&too_many, 1, 32768),
            Err(V5ComponentCRuntimeError::OutputLengthOverflow)
        );
    }

    #[test]
    fn runtime_relation_table_validator_preserves_canonical_values() {
        let table = vec![QM31::ZERO, QM31::ONE, q(P - 1)];
        let before = table.clone();
        assert_eq!(
            validate_component_c_runtime_relation_table(&table, 3, 2),
            Ok(())
        );
        assert_eq!(table, before);
    }

    #[test]
    fn runtime_relation_table_validator_rejects_each_noncanonical_limb() {
        let raw = |limbs: [u32; 4]| QM31 {
            c0: CM31 {
                a: M31(limbs[0]),
                b: M31(limbs[1]),
            },
            c1: CM31 {
                a: M31(limbs[2]),
                b: M31(limbs[3]),
            },
        };
        for limb in 0..4 {
            let mut limbs = [0u32; 4];
            limbs[limb] = P;
            let table = [QM31::ZERO, raw(limbs)];
            assert_eq!(
                validate_component_c_runtime_relation_table(&table, 1, 0),
                Err(V5ComponentCRuntimeError::NonCanonicalRelationTable {
                    round: 1,
                    slot: 0,
                    index: 1,
                })
            );
        }
    }

    #[test]
    fn runtime_packer_preserves_every_segment_and_dynamic_order() {
        let ood_values = core::array::from_fn(|round| {
            core::array::from_fn(|sample| q((10 * round + sample) as u32))
        });
        let polynomials = core::array::from_fn(|round| {
            core::array::from_fn(|degree| q((100 + 10 * round + degree) as u32))
        });
        let later = [
            (0..16).map(|row| q(200 + row)).collect::<Vec<_>>(),
            (0..12).map(|row| q(300 + row)).collect::<Vec<_>>(),
            (0..8).map(|row| q(400 + row)).collect::<Vec<_>>(),
        ];
        let final_coefficients = core::array::from_fn(|index| q(500 + index as u32));
        let output = pack_component_c_runtime_downstream(
            &ood_values,
            &polynomials,
            &later,
            &final_coefficients,
        )
        .unwrap();

        assert_eq!(output.len(), 76);
        for round in 0..4 {
            let base = 9 * round;
            assert_eq!(&output[base..base + 2], &ood_values[round]);
            assert_eq!(&output[base + 2..base + 9], &polynomials[round]);
        }
        assert_eq!(&output[36..52], later[0].as_slice());
        assert_eq!(&output[52..64], later[1].as_slice());
        assert_eq!(&output[64..72], later[2].as_slice());
        assert_eq!(&output[72..76], &final_coefficients);
    }

    #[test]
    fn swapping_a_deduplicated_fibre_slot_changes_the_runtime_view() {
        let ood_values = [[QM31::ZERO; 2]; 4];
        let polynomials = [[QM31::ZERO; 7]; 4];
        let later = [vec![q(1), q(4), q(9), q(16)], Vec::new(), Vec::new()];
        let mut swapped = later.clone();
        swapped[0].swap(1, 2);
        let final_coefficients = [QM31::ZERO; 4];
        let honest = pack_component_c_runtime_downstream(
            &ood_values,
            &polynomials,
            &later,
            &final_coefficients,
        )
        .unwrap();
        let mutated = pack_component_c_runtime_downstream(
            &ood_values,
            &polynomials,
            &swapped,
            &final_coefficients,
        )
        .unwrap();
        assert_ne!(honest, mutated);
        assert_eq!(honest[37], q(4));
        assert_eq!(mutated[37], q(9));
    }
}
