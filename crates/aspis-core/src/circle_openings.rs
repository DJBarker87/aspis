//! Authenticated opening composition for the fixed M31 circle candidate.
//!
//! This module joins the separately tested layer-zero and later-line Merkle
//! sections to the separately tested per-query arithmetic chain. It still
//! does not derive transcript challenges, verify the OOD/sumcheck relation,
//! enable tag 24, or accept a complete proof.

use crate::circle_fri::{
    CircleFriError, FIXED_ARITY4_ROUNDS, FIXED_CIRCLE_INV_2X, FIXED_CIRCLE_INV_2Y, FIXED_FINAL_X,
    FIXED_LINE1_INV, FIXED_LINE2_INV, FIXED_LINE3_INV, RATE16_CIRCLE_INV_2X, RATE16_CIRCLE_INV_2Y,
    RATE16_FINAL_X, RATE16_LINE1_INV, RATE16_LINE2_INV, RATE16_LINE3_INV, RATE32_CIRCLE_INV_2X,
    RATE32_CIRCLE_INV_2Y, RATE32_FINAL_X, RATE32_LINE1_INV, RATE32_LINE2_INV, RATE32_LINE3_INV,
    RATE512_CIRCLE_INV_2X, RATE512_CIRCLE_INV_2Y, RATE512_FINAL_X, RATE512_LINE1_INV,
    RATE512_LINE2_INV, RATE512_LINE3_INV,
};
use crate::circle_hiding_query::PaymentHidingQueryPowers;
use crate::circle_line_merkle::{
    derive_circle_line_query_indices, derive_circle_line_query_indices_for_count,
    verify_circle_line_openings_deferred_canonical_for_geometry_with_indices,
    verify_circle_line_openings_for_geometry_with_indices, CircleLineMerkleError,
    CircleOpeningGeometry, VerifiedCircleLineOpenings, CIRCLE_LINE_LAYER_COUNT,
    FIXED_CIRCLE_OPENING_GEOMETRY,
};
use crate::circle_merkle::{
    verify_circle_layer0_opening_from_proof,
    verify_circle_layer0_opening_from_proof_deferred_canonical_for_depth_and_leaf_bytes,
    CircleLayer0Opening, CircleMerkleError, CIRCLE_C2_LEAF_BYTES,
};
use crate::circle_prefix::{CandidatePrefix, CANDIDATE_FINAL_POLY_LEN, CANDIDATE_QUERY_COUNT};
use crate::circle_query::{
    check_fixed_circle_query, check_fixed_layer0_transition_prepared,
    check_fixed_line_transition_prepared, check_fixed_line_transition_prepared_polynomial,
    check_fixed_terminal_transition_prepared, check_fixed_terminal_transition_prepared_polynomial,
    check_layer0_transition_prepared_for_fiber_count, CircleQueryCheck, CircleQueryError,
    CircleQueryGammaPowers, CIRCLE_QUERY_LATER_LAYERS,
};
use crate::field::{PreparedQm31Multiplier, M31, QM31};
use crate::state_only_query::{
    check_state_only_layer0_transition_prepared_polynomial_for_fiber_count, StateOnlyQueryPowers,
    STATE_ONLY_C1_LEAF_BYTES, STATE_ONLY_C2_LEAF_BYTES,
};
use crate::HashFn;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleOpeningsError {
    Layer0(CircleMerkleError),
    Later(CircleLineMerkleError),
    Query(CircleQueryError),
    QueryCountMismatch {
        expected: usize,
        actual: usize,
    },
    QueryRange {
        start: usize,
        end: usize,
        available: usize,
    },
    PrefixShape,
}

/// Measurement-only partition of the exact all-query arithmetic. The
/// Johnson diagnostic executes these partitions against one authenticated
/// opening so a total above Solana's transaction ceiling can be reconciled
/// without adding overlapping verifier phases.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleQuerySegment {
    PreparedBase,
    Layer0Range { start: usize, end: usize },
    LaterAll,
    Full,
}

impl From<CircleMerkleError> for CircleOpeningsError {
    fn from(error: CircleMerkleError) -> Self {
        Self::Layer0(error)
    }
}

impl From<CircleLineMerkleError> for CircleOpeningsError {
    fn from(error: CircleLineMerkleError) -> Self {
        Self::Later(error)
    }
}

impl From<CircleQueryError> for CircleOpeningsError {
    fn from(error: CircleQueryError) -> Self {
        Self::Query(error)
    }
}

impl From<CircleFriError> for CircleOpeningsError {
    fn from(error: CircleFriError) -> Self {
        Self::Query(CircleQueryError::Fold(error))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AuthenticatedCircleQueryLeaves<'a> {
    pub query: u32,
    pub c1: &'a [u8],
    pub c2: &'a [u8],
    pub later: [&'a [u8]; CIRCLE_QUERY_LATER_LAYERS],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedCircleOpenings<'a> {
    pub layer0: CircleLayer0Opening<'a>,
    pub later: VerifiedCircleLineOpenings<'a>,
}

fn advance_monotone_ordinal(
    indices: &[u32],
    ordinal: &mut usize,
    target: u32,
    layer: u8,
) -> Result<usize, CircleOpeningsError> {
    loop {
        match indices.get(*ordinal).copied() {
            Some(index) if index < target => *ordinal += 1,
            Some(index) if index == target => return Ok(*ordinal),
            _ => {
                return Err(CircleLineMerkleError::LeafIndexNotFound {
                    layer,
                    index: target,
                }
                .into())
            }
        }
    }
}

impl<'a> VerifiedCircleOpenings<'a> {
    fn layer0_transition_leaves(
        &self,
        layer0_ordinal: usize,
        layer1_ordinal: usize,
        query: u32,
    ) -> Result<(&'a [u8], &'a [u8], &'a [u8]), CircleOpeningsError> {
        if self.later.indices.layer0.get(layer0_ordinal) != Some(&query) {
            return Err(CircleLineMerkleError::QueryNotOpened { query }.into());
        }
        let layer1_index = query >> 2;
        if self.later.indices.later[0].get(layer1_ordinal) != Some(&layer1_index) {
            return Err(CircleLineMerkleError::LeafIndexNotFound {
                layer: 1,
                index: layer1_index,
            }
            .into());
        }
        let c1 = self.layer0.c1_leaf(layer0_ordinal).ok_or(
            CircleLineMerkleError::LeafIndexNotFound {
                layer: 0,
                index: query,
            },
        )?;
        let c2 = self.layer0.c2_leaf(layer0_ordinal).ok_or(
            CircleLineMerkleError::LeafIndexNotFound {
                layer: 0,
                index: query,
            },
        )?;
        let layer1 = self.later.openings.layers[0].leaf(layer1_ordinal).ok_or(
            CircleLineMerkleError::LeafIndexNotFound {
                layer: 1,
                index: layer1_index,
            },
        )?;
        Ok((c1, c2, layer1.as_slice()))
    }

    /// Return the exact authenticated leaves selected by one original query.
    pub fn query_leaves(
        &self,
        query: u32,
    ) -> Result<AuthenticatedCircleQueryLeaves<'a>, CircleOpeningsError> {
        let ordinal = self
            .later
            .indices
            .layer0
            .binary_search(&query)
            .map_err(|_| CircleLineMerkleError::QueryNotOpened { query })?;
        let c1 = self
            .layer0
            .c1_leaf(ordinal)
            .ok_or(CircleLineMerkleError::LeafIndexNotFound {
                layer: 0,
                index: query,
            })?;
        let c2 = self
            .layer0
            .c2_leaf(ordinal)
            .ok_or(CircleLineMerkleError::LeafIndexNotFound {
                layer: 0,
                index: query,
            })?;
        let slots = [
            self.later.query_leaf_slot(query, 1)?,
            self.later.query_leaf_slot(query, 2)?,
            self.later.query_leaf_slot(query, 3)?,
        ];
        Ok(AuthenticatedCircleQueryLeaves {
            query,
            c1,
            c2,
            later: slots.map(|slot| slot.leaf.as_slice()),
        })
    }

    /// Check the arithmetic chain for one already-authenticated query.
    pub fn check_query(
        &self,
        query: u32,
        gamma: QM31,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
    ) -> Result<CircleQueryCheck, CircleOpeningsError> {
        let leaves = self.query_leaves(query)?;
        Ok(check_fixed_circle_query(
            leaves.c1,
            leaves.c2,
            leaves.later,
            query as usize,
            gamma,
            alphas,
            final_natural,
        )?)
    }

    /// Check every unique layer-zero query committed by the opening suffix.
    pub fn check_all_queries(
        &self,
        gamma: QM31,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
    ) -> Result<(), CircleOpeningsError> {
        self.check_all_queries_with_trace(gamma, alphas, final_natural, None)
    }

    pub fn check_all_queries_with_trace(
        &self,
        gamma: QM31,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        trace: Option<fn(usize)>,
    ) -> Result<(), CircleOpeningsError> {
        let powers = CircleQueryGammaPowers::new(gamma);
        self.check_all_queries_with_trace_prepared(&powers, alphas, final_natural, trace)
    }

    pub fn check_all_queries_with_trace_prepared(
        &self,
        powers: &CircleQueryGammaPowers,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        trace: Option<fn(usize)>,
    ) -> Result<(), CircleOpeningsError> {
        let alpha_squares = alphas.map(QM31::square);
        let alpha_multipliers = alphas.map(PreparedQm31Multiplier::new);
        let alpha_square_multipliers = alpha_squares.map(PreparedQm31Multiplier::new);
        if let Some(trace) = trace {
            trace(0);
        }
        let mut layer1_ordinal = 0usize;
        for (ordinal, &query) in self.later.indices.layer0.iter().enumerate() {
            let layer1_index = query >> 2;
            advance_monotone_ordinal(
                &self.later.indices.later[0],
                &mut layer1_ordinal,
                layer1_index,
                1,
            )?;
            let (c1, c2, layer1) = self.layer0_transition_leaves(ordinal, layer1_ordinal, query)?;
            check_fixed_layer0_transition_prepared(
                c1,
                c2,
                layer1,
                query as usize,
                powers,
                [
                    M31(FIXED_CIRCLE_INV_2X[query as usize]),
                    M31(FIXED_CIRCLE_INV_2Y[query as usize]),
                ],
                alpha_multipliers[0],
                alpha_square_multipliers[0],
            )?;
            if let Some(trace) = trace {
                if (ordinal + 1) % 8 == 0 || ordinal + 1 == self.later.indices.layer0.len() {
                    trace(ordinal + 1);
                }
            }
        }
        let line_tables = [&FIXED_LINE1_INV[..], &FIXED_LINE2_INV, &FIXED_LINE3_INV];
        for layer in 0..CIRCLE_QUERY_LATER_LAYERS {
            let mut outgoing_ordinal = 0usize;
            for (ordinal, &index) in self.later.indices.later[layer].iter().enumerate() {
                let incoming = self.later.openings.layers[layer].leaf(ordinal).unwrap();
                let offset = index as usize * 3;
                let inverses = [
                    M31(line_tables[layer][offset]),
                    M31(line_tables[layer][offset + 1]),
                    M31(line_tables[layer][offset + 2]),
                ];
                if layer + 1 < CIRCLE_QUERY_LATER_LAYERS {
                    let outgoing_index = index >> 2;
                    advance_monotone_ordinal(
                        &self.later.indices.later[layer + 1],
                        &mut outgoing_ordinal,
                        outgoing_index,
                        layer as u8 + 2,
                    )?;
                    let outgoing = self.later.openings.layers[layer + 1]
                        .leaf(outgoing_ordinal)
                        .unwrap();
                    check_fixed_line_transition_prepared(
                        incoming,
                        outgoing,
                        index as usize,
                        layer as u8 + 1,
                        inverses,
                        alpha_multipliers[layer + 1],
                        alpha_square_multipliers[layer + 1],
                    )?;
                } else {
                    check_fixed_terminal_transition_prepared(
                        incoming,
                        final_natural,
                        index as usize,
                        inverses,
                        M31(FIXED_FINAL_X[index as usize]),
                        alpha_multipliers[3],
                        alpha_square_multipliers[3],
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Execute one exact partition of the optimized query checker. Challenge
    /// powers and fold multipliers are prepared unconditionally in every
    /// mode. `PreparedBase` keeps that setup observable so the measurement
    /// ledger can subtract repeated setup together with the shared prefix,
    /// relation, and Merkle work.
    #[inline(never)]
    pub fn check_query_segment(
        &self,
        gamma: QM31,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        segment: CircleQuerySegment,
    ) -> Result<(), CircleOpeningsError> {
        self.check_query_segment_for_geometry(
            gamma,
            alphas,
            final_natural,
            segment,
            FIXED_CIRCLE_OPENING_GEOMETRY,
        )
    }

    #[inline(never)]
    pub fn check_query_segment_for_geometry(
        &self,
        gamma: QM31,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        segment: CircleQuerySegment,
        geometry: CircleOpeningGeometry,
    ) -> Result<(), CircleOpeningsError> {
        let powers = CircleQueryGammaPowers::new(gamma);
        self.check_query_segment_prepared_for_geometry(
            &powers,
            alphas,
            final_natural,
            segment,
            geometry,
        )
    }

    /// Prepared-power form of [`Self::check_query_segment_for_geometry`].
    /// Callers which already expanded the same 51-term gamma generator for
    /// the OOD relation can reuse it here instead of paying for a second power
    /// table. The checked query equations are otherwise identical.
    #[inline(never)]
    pub fn check_query_segment_prepared_for_geometry(
        &self,
        powers: &CircleQueryGammaPowers,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        segment: CircleQuerySegment,
        geometry: CircleOpeningGeometry,
    ) -> Result<(), CircleOpeningsError> {
        let alpha_squares = alphas.map(QM31::square);
        let alpha_multipliers = alphas.map(PreparedQm31Multiplier::new);
        let alpha_square_multipliers = alpha_squares.map(PreparedQm31Multiplier::new);

        // Keep setup in the base row even when no leaf is visited. The same
        // barrier executes in every segment and is therefore retained once
        // by the overlap-subtracted total.
        core::hint::black_box((&powers, &alpha_multipliers, &alpha_square_multipliers));

        let (circle_inv_2x, circle_inv_2y, line_tables, final_x): (
            &[u32],
            &[u32],
            [&[u32]; 3],
            &[u32],
        ) = match geometry.layer0_binary_depth {
            10 => (
                &FIXED_CIRCLE_INV_2X,
                &FIXED_CIRCLE_INV_2Y,
                [&FIXED_LINE1_INV, &FIXED_LINE2_INV, &FIXED_LINE3_INV],
                &FIXED_FINAL_X,
            ),
            12 => (
                &RATE16_CIRCLE_INV_2X,
                &RATE16_CIRCLE_INV_2Y,
                [&RATE16_LINE1_INV, &RATE16_LINE2_INV, &RATE16_LINE3_INV],
                &RATE16_FINAL_X,
            ),
            13 => (
                &RATE32_CIRCLE_INV_2X,
                &RATE32_CIRCLE_INV_2Y,
                [&RATE32_LINE1_INV, &RATE32_LINE2_INV, &RATE32_LINE3_INV],
                &RATE32_FINAL_X,
            ),
            17 => (
                &RATE512_CIRCLE_INV_2X,
                &RATE512_CIRCLE_INV_2Y,
                [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV],
                &RATE512_FINAL_X,
            ),
            _ => return Err(CircleOpeningsError::PrefixShape),
        };
        let fiber_count = 1usize << geometry.layer0_binary_depth;

        let layer0_range = match segment {
            CircleQuerySegment::PreparedBase | CircleQuerySegment::LaterAll => None,
            CircleQuerySegment::Layer0Range { start, end } => Some((start, end)),
            CircleQuerySegment::Full => Some((0, self.later.indices.layer0.len())),
        };
        if let Some((start, end)) = layer0_range {
            let available = self.later.indices.layer0.len();
            if start > end || end > available {
                return Err(CircleOpeningsError::QueryRange {
                    start,
                    end,
                    available,
                });
            }
            let mut layer1_ordinal = if start < end {
                let layer1_index = self.later.indices.layer0[start] >> 2;
                self.later.indices.later[0]
                    .binary_search(&layer1_index)
                    .map_err(|_| CircleLineMerkleError::LeafIndexNotFound {
                        layer: 1,
                        index: layer1_index,
                    })?
            } else {
                0
            };
            for ordinal in start..end {
                let query = self.later.indices.layer0[ordinal];
                let layer1_index = query >> 2;
                advance_monotone_ordinal(
                    &self.later.indices.later[0],
                    &mut layer1_ordinal,
                    layer1_index,
                    1,
                )?;
                let (c1, c2, layer1) =
                    self.layer0_transition_leaves(ordinal, layer1_ordinal, query)?;
                check_layer0_transition_prepared_for_fiber_count(
                    c1,
                    c2,
                    layer1,
                    query as usize,
                    fiber_count,
                    powers,
                    [
                        M31(circle_inv_2x[query as usize]),
                        M31(circle_inv_2y[query as usize]),
                    ],
                    alpha_multipliers[0],
                    alpha_square_multipliers[0],
                )?;
            }
        }

        if matches!(
            segment,
            CircleQuerySegment::LaterAll | CircleQuerySegment::Full
        ) {
            for layer in 0..CIRCLE_QUERY_LATER_LAYERS {
                let mut outgoing_ordinal = 0usize;
                for (ordinal, &index) in self.later.indices.later[layer].iter().enumerate() {
                    let incoming = self.later.openings.layers[layer].leaf(ordinal).unwrap();
                    let offset = index as usize * 3;
                    let inverses = [
                        M31(line_tables[layer][offset]),
                        M31(line_tables[layer][offset + 1]),
                        M31(line_tables[layer][offset + 2]),
                    ];
                    if layer + 1 < CIRCLE_QUERY_LATER_LAYERS {
                        let outgoing_index = index >> 2;
                        advance_monotone_ordinal(
                            &self.later.indices.later[layer + 1],
                            &mut outgoing_ordinal,
                            outgoing_index,
                            layer as u8 + 2,
                        )?;
                        let outgoing = self.later.openings.layers[layer + 1]
                            .leaf(outgoing_ordinal)
                            .unwrap();
                        check_fixed_line_transition_prepared(
                            incoming,
                            outgoing,
                            index as usize,
                            layer as u8 + 1,
                            inverses,
                            alpha_multipliers[layer + 1],
                            alpha_square_multipliers[layer + 1],
                        )?;
                    } else {
                        check_fixed_terminal_transition_prepared(
                            incoming,
                            final_natural,
                            index as usize,
                            inverses,
                            M31(final_x[index as usize]),
                            alpha_multipliers[3],
                            alpha_square_multipliers[3],
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Width-18 state-only form of the optimized query checker. Only the
    /// layer-zero generator changes; all authenticated later layers and fold
    /// equations are identical to the ordinary candidate.
    #[inline(never)]
    pub fn check_state_only_query_segment_prepared_for_geometry(
        &self,
        powers: &StateOnlyQueryPowers,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        segment: CircleQuerySegment,
        geometry: CircleOpeningGeometry,
    ) -> Result<(), CircleOpeningsError> {
        let alpha_squares = alphas.map(QM31::square);
        let alpha_cubes: [QM31; FIXED_ARITY4_ROUNDS as usize] =
            core::array::from_fn(|round| alpha_squares[round].mul(alphas[round]));
        let alpha_multipliers = alphas.map(PreparedQm31Multiplier::new);
        let alpha_square_multipliers = alpha_squares.map(PreparedQm31Multiplier::new);
        let alpha_cube_multipliers = alpha_cubes.map(PreparedQm31Multiplier::new);
        core::hint::black_box((
            &powers,
            &alpha_multipliers,
            &alpha_square_multipliers,
            &alpha_cube_multipliers,
        ));

        let (circle_inv_2x, circle_inv_2y, line_tables, final_x): (
            &[u32],
            &[u32],
            [&[u32]; 3],
            &[u32],
        ) = match geometry.layer0_binary_depth {
            10 => (
                &FIXED_CIRCLE_INV_2X,
                &FIXED_CIRCLE_INV_2Y,
                [&FIXED_LINE1_INV, &FIXED_LINE2_INV, &FIXED_LINE3_INV],
                &FIXED_FINAL_X,
            ),
            12 => (
                &RATE16_CIRCLE_INV_2X,
                &RATE16_CIRCLE_INV_2Y,
                [&RATE16_LINE1_INV, &RATE16_LINE2_INV, &RATE16_LINE3_INV],
                &RATE16_FINAL_X,
            ),
            13 => (
                &RATE32_CIRCLE_INV_2X,
                &RATE32_CIRCLE_INV_2Y,
                [&RATE32_LINE1_INV, &RATE32_LINE2_INV, &RATE32_LINE3_INV],
                &RATE32_FINAL_X,
            ),
            17 => (
                &RATE512_CIRCLE_INV_2X,
                &RATE512_CIRCLE_INV_2Y,
                [&RATE512_LINE1_INV, &RATE512_LINE2_INV, &RATE512_LINE3_INV],
                &RATE512_FINAL_X,
            ),
            _ => return Err(CircleOpeningsError::PrefixShape),
        };
        let fiber_count = 1usize << geometry.layer0_binary_depth;

        let layer0_range = match segment {
            CircleQuerySegment::PreparedBase | CircleQuerySegment::LaterAll => None,
            CircleQuerySegment::Layer0Range { start, end } => Some((start, end)),
            CircleQuerySegment::Full => Some((0, self.later.indices.layer0.len())),
        };
        if let Some((start, end)) = layer0_range {
            let available = self.later.indices.layer0.len();
            if start > end || end > available {
                return Err(CircleOpeningsError::QueryRange {
                    start,
                    end,
                    available,
                });
            }
            let mut layer1_ordinal = if start < end {
                let layer1_index = self.later.indices.layer0[start] >> 2;
                self.later.indices.later[0]
                    .binary_search(&layer1_index)
                    .map_err(|_| CircleLineMerkleError::LeafIndexNotFound {
                        layer: 1,
                        index: layer1_index,
                    })?
            } else {
                0
            };
            for ordinal in start..end {
                let query = self.later.indices.layer0[ordinal];
                let layer1_index = query >> 2;
                advance_monotone_ordinal(
                    &self.later.indices.later[0],
                    &mut layer1_ordinal,
                    layer1_index,
                    1,
                )?;
                let (c1, c2, layer1) =
                    self.layer0_transition_leaves(ordinal, layer1_ordinal, query)?;
                check_state_only_layer0_transition_prepared_polynomial_for_fiber_count(
                    c1,
                    c2,
                    layer1,
                    query as usize,
                    fiber_count,
                    powers,
                    [
                        M31(circle_inv_2x[query as usize]),
                        M31(circle_inv_2y[query as usize]),
                    ],
                    alpha_multipliers[0],
                    alpha_square_multipliers[0],
                    alpha_cube_multipliers[0],
                )?;
            }
        }

        if matches!(
            segment,
            CircleQuerySegment::LaterAll | CircleQuerySegment::Full
        ) {
            for layer in 0..CIRCLE_QUERY_LATER_LAYERS {
                let mut outgoing_ordinal = 0usize;
                for (ordinal, &index) in self.later.indices.later[layer].iter().enumerate() {
                    let incoming = self.later.openings.layers[layer].leaf(ordinal).unwrap();
                    let offset = index as usize * 3;
                    let inverses = [
                        M31(line_tables[layer][offset]),
                        M31(line_tables[layer][offset + 1]),
                        M31(line_tables[layer][offset + 2]),
                    ];
                    if layer + 1 < CIRCLE_QUERY_LATER_LAYERS {
                        let outgoing_index = index >> 2;
                        advance_monotone_ordinal(
                            &self.later.indices.later[layer + 1],
                            &mut outgoing_ordinal,
                            outgoing_index,
                            layer as u8 + 2,
                        )?;
                        let outgoing = self.later.openings.layers[layer + 1]
                            .leaf(outgoing_ordinal)
                            .unwrap();
                        check_fixed_line_transition_prepared_polynomial(
                            incoming,
                            outgoing,
                            index as usize,
                            layer as u8 + 1,
                            inverses,
                            alpha_multipliers[layer + 1],
                            alpha_square_multipliers[layer + 1],
                            alpha_cube_multipliers[layer + 1],
                        )?;
                    } else {
                        check_fixed_terminal_transition_prepared_polynomial(
                            incoming,
                            final_natural,
                            index as usize,
                            inverses,
                            M31(final_x[index as usize]),
                            alpha_multipliers[3],
                            alpha_square_multipliers[3],
                            alpha_cube_multipliers[3],
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Hiding-profile alias of the ordinary 51-column checker. C2 is exactly
    /// `(h1,G)`, so no special layer-zero arithmetic remains.
    #[inline(never)]
    pub fn check_payment_hiding_query_segment_for_geometry(
        &self,
        gamma: QM31,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        segment: CircleQuerySegment,
        geometry: CircleOpeningGeometry,
    ) -> Result<(), CircleOpeningsError> {
        self.check_query_segment_for_geometry(gamma, alphas, final_natural, segment, geometry)
    }

    /// One-mask hiding-profile alias which reuses an already expanded standard
    /// 51-column generator. C2 is exactly `(h1,G)`, so this is the same checker
    /// as [`Self::check_query_segment_prepared_for_geometry`].
    #[inline(never)]
    pub fn check_payment_hiding_query_segment_prepared_for_geometry(
        &self,
        powers: &PaymentHidingQueryPowers,
        alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
        final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
        segment: CircleQuerySegment,
        geometry: CircleOpeningGeometry,
    ) -> Result<(), CircleOpeningsError> {
        self.check_query_segment_prepared_for_geometry(
            powers,
            alphas,
            final_natural,
            segment,
            geometry,
        )
    }
}

/// Authenticate the complete layer0||layer1||layer2||layer3 opening suffix.
pub fn verify_circle_openings<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    let indices = derive_circle_line_query_indices(layer0_queries)?;
    let (layer0, remainder) = verify_circle_layer0_opening_from_proof(
        hash,
        c1_root,
        c2_root,
        &indices.layer0,
        proof_bytes,
    )?;
    let later = verify_circle_line_openings_for_geometry_with_indices(
        hash,
        later_roots,
        indices,
        remainder,
        FIXED_CIRCLE_OPENING_GEOMETRY,
    )?;
    Ok(VerifiedCircleOpenings { layer0, later })
}

/// Authenticate all fixed openings while deferring canonical decoding to the
/// immediately following all-query check. Every opened leaf is visited by
/// that check, so the composed acceptance predicate is unchanged.
pub(crate) fn verify_circle_openings_deferred_canonical<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    verify_circle_openings_deferred_canonical_for_geometry(
        hash,
        c1_root,
        c2_root,
        later_roots,
        layer0_queries,
        proof_bytes,
        FIXED_CIRCLE_OPENING_GEOMETRY,
    )
}

pub(crate) fn verify_circle_openings_deferred_canonical_for_geometry<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    verify_circle_openings_deferred_canonical_for_geometry_and_c2_leaf_bytes(
        hash,
        c1_root,
        c2_root,
        later_roots,
        layer0_queries,
        proof_bytes,
        geometry,
        CIRCLE_C2_LEAF_BYTES,
    )
}

pub(crate) fn verify_circle_openings_deferred_canonical_for_geometry_and_c2_leaf_bytes<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
    c2_leaf_bytes: usize,
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    verify_circle_openings_deferred_canonical_for_geometry_and_leaf_bytes(
        hash,
        c1_root,
        c2_root,
        later_roots,
        layer0_queries,
        proof_bytes,
        geometry,
        crate::circle_merkle::CIRCLE_C1_LEAF_BYTES,
        c2_leaf_bytes,
    )
}

pub(crate) fn verify_circle_openings_deferred_canonical_for_geometry_and_leaf_bytes<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
    c1_leaf_bytes: usize,
    c2_leaf_bytes: usize,
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    let indices = if geometry == FIXED_CIRCLE_OPENING_GEOMETRY {
        derive_circle_line_query_indices(layer0_queries)?
    } else {
        derive_circle_line_query_indices_for_count(
            layer0_queries,
            1usize << geometry.layer0_binary_depth,
        )?
    };
    let (layer0, remainder) =
        verify_circle_layer0_opening_from_proof_deferred_canonical_for_depth_and_leaf_bytes(
            hash,
            c1_root,
            c2_root,
            &indices.layer0,
            proof_bytes,
            geometry.layer0_binary_depth,
            c1_leaf_bytes,
            c2_leaf_bytes,
        )?;
    let later = verify_circle_line_openings_deferred_canonical_for_geometry_with_indices(
        hash,
        later_roots,
        indices,
        remainder,
        geometry,
    )?;
    Ok(VerifiedCircleOpenings { layer0, later })
}

/// Authenticate roots from the fixed prefix, then check every derived query
/// against explicit transcript challenges and the prefix's natural final4.
/// Challenge derivation and relation verification remain outside this helper.
pub fn verify_and_check_circle_openings_for_prefix<'a>(
    hash: HashFn,
    prefix: &CandidatePrefix<'_>,
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    gamma: QM31,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    let expected_query_count = usize::from(CANDIDATE_QUERY_COUNT);
    if layer0_queries.len() != expected_query_count {
        return Err(CircleOpeningsError::QueryCountMismatch {
            expected: expected_query_count,
            actual: layer0_queries.len(),
        });
    }
    let mut later_roots = [[0u8; 32]; CIRCLE_LINE_LAYER_COUNT];
    for (layer, root) in later_roots.iter_mut().enumerate() {
        *root = prefix.rounds[layer + 1]
            .root
            .copied()
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let mut final_natural = [QM31::ZERO; CANDIDATE_FINAL_POLY_LEN];
    for (coefficient, value) in final_natural.iter_mut().enumerate() {
        *value = prefix
            .final_coefficient(coefficient)
            .ok_or(CircleOpeningsError::PrefixShape)?;
    }
    let verified = verify_circle_openings(
        hash,
        prefix.c1_root,
        prefix.c2_root,
        &later_roots,
        layer0_queries,
        proof_bytes,
    )?;
    verified.check_all_queries(gamma, alphas, final_natural)?;
    Ok(verified)
}

/// Authenticate and check one complete opening suffix for an explicitly
/// selected rate geometry. This is the composed acceptance boundary used by
/// rate-1/32 tests and future profiles: canonical decoding is deferred only
/// until the immediately following all-query arithmetic, which visits every
/// opened leaf.
pub fn verify_and_check_circle_openings_for_geometry<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    gamma: QM31,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    let verified = verify_circle_openings_deferred_canonical_for_geometry(
        hash,
        c1_root,
        c2_root,
        later_roots,
        layer0_queries,
        proof_bytes,
        geometry,
    )?;
    verified.check_query_segment_for_geometry(
        gamma,
        alphas,
        final_natural,
        CircleQuerySegment::Full,
        geometry,
    )?;
    Ok(verified)
}

/// Composed Merkle-plus-query acceptance boundary for the width-18
/// state-only profile. Both leaf widths are fixed here so a profile cannot
/// authenticate one byte layout and decode another.
pub fn verify_and_check_state_only_circle_openings_for_geometry<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    powers: &StateOnlyQueryPowers,
    alphas: [QM31; FIXED_ARITY4_ROUNDS as usize],
    final_natural: [QM31; CANDIDATE_FINAL_POLY_LEN],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    let verified = verify_state_only_circle_openings_for_geometry(
        hash,
        c1_root,
        c2_root,
        later_roots,
        layer0_queries,
        proof_bytes,
        geometry,
    )?;
    verified.check_state_only_query_segment_prepared_for_geometry(
        powers,
        alphas,
        final_natural,
        CircleQuerySegment::Full,
        geometry,
    )?;
    Ok(verified)
}

/// Authenticate and parse the complete state-only opening suffix without yet
/// running the query arithmetic. This split is acceptance-neutral: callers
/// must immediately invoke
/// [`VerifiedCircleOpenings::check_state_only_query_segment_prepared_for_geometry`]
/// with `CircleQuerySegment::Full`. It exists so an on-chain measurement can
/// name the Merkle/opening cost separately from the all-query recombination.
pub fn verify_state_only_circle_openings_for_geometry<'a>(
    hash: HashFn,
    c1_root: &[u8; 32],
    c2_root: &[u8; 32],
    later_roots: &[[u8; 32]; CIRCLE_LINE_LAYER_COUNT],
    layer0_queries: &[u32],
    proof_bytes: &'a [u8],
    geometry: CircleOpeningGeometry,
) -> Result<VerifiedCircleOpenings<'a>, CircleOpeningsError> {
    verify_circle_openings_deferred_canonical_for_geometry_and_leaf_bytes(
        hash,
        c1_root,
        c2_root,
        later_roots,
        layer0_queries,
        proof_bytes,
        geometry,
        STATE_ONLY_C1_LEAF_BYTES,
        STATE_ONLY_C2_LEAF_BYTES,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    #[test]
    fn monotone_routing_matches_binary_search_for_random_nested_query_sets() {
        let mut state = 0x4d4f_4e4f_544f_4e45u64;
        for schedule in 0..64 {
            let depth = if schedule & 1 == 0 { 10 } else { 12 };
            let bound = 1u32 << depth;
            let mut queries = Vec::with_capacity(36);
            for _ in 0..36 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                queries.push(((state >> 32) as u32) & (bound - 1));
            }
            let indices =
                derive_circle_line_query_indices_for_count(&queries, bound as usize).unwrap();

            let mut layer1_ordinal = 0usize;
            for &query in &indices.layer0 {
                let target = query >> 2;
                let expected = indices.later[0].binary_search(&target).unwrap();
                assert_eq!(
                    advance_monotone_ordinal(&indices.later[0], &mut layer1_ordinal, target, 1,)
                        .unwrap(),
                    expected,
                );
            }

            for layer in 0..2 {
                let mut outgoing_ordinal = 0usize;
                for &index in &indices.later[layer] {
                    let target = index >> 2;
                    let expected = indices.later[layer + 1].binary_search(&target).unwrap();
                    assert_eq!(
                        advance_monotone_ordinal(
                            &indices.later[layer + 1],
                            &mut outgoing_ordinal,
                            target,
                            layer as u8 + 2,
                        )
                        .unwrap(),
                        expected,
                    );
                }
            }
        }

        let mut ordinal = 0;
        assert_eq!(
            advance_monotone_ordinal(&[1, 3, 7], &mut ordinal, 2, 1),
            Err(CircleOpeningsError::Later(
                CircleLineMerkleError::LeafIndexNotFound { layer: 1, index: 2 }
            )),
        );
    }
}
