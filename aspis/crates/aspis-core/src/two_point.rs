//! Neutral two-point MLE batching diagnostic.
//!
//! This module prices four explicitly unselected relation shapes over one
//! deterministic log10 fixture. It does not define a production transcript,
//! proof format, soundness term, or payment rule.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::{CM31, M31, QM31};
#[cfg(test)]
use crate::sumcheck::polynomial_for_extension;
use crate::sumcheck::{
    boundary_sum, evaluate, SumcheckPolynomial, TensorWeightError, WeightAccumulator,
    SUMCHECK_BYTES,
};
use crate::transcript::{label, ChallengeSampleExhausted, HashFn, Transcript};

pub const TWO_POINT_LOG_ROWS: u32 = 10;
pub const TWO_POINT_ROUNDS: u32 = 4;
pub const TWO_POINT_STATEMENT_VALUES: usize = 102;
pub const TWO_POINT_COORDINATES: usize = 10;
pub const TWO_POINT_VALUES_BYTES: usize = TWO_POINT_STATEMENT_VALUES * 16;
pub const TWO_POINT_POINTS_BYTES: usize = 2 * TWO_POINT_COORDINATES * 16;

const TWO_POINT_VALUES_LABEL: u8 = 11;
const MODE_MARKERS: [u32; 4] = [101, 211, 307, 401];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TwoPointBatchingMode {
    OnePointBaseline,
    FreshKappaSingleLane,
    TwoIndependentRelationLanes,
    DisjointGamma51SingleLane,
}

impl TwoPointBatchingMode {
    pub const ALL: [Self; 4] = [
        Self::OnePointBaseline,
        Self::FreshKappaSingleLane,
        Self::TwoIndependentRelationLanes,
        Self::DisjointGamma51SingleLane,
    ];

    pub const fn index(self) -> usize {
        match self {
            Self::OnePointBaseline => 0,
            Self::FreshKappaSingleLane => 1,
            Self::TwoIndependentRelationLanes => 2,
            Self::DisjointGamma51SingleLane => 3,
        }
    }

    pub const fn relation_lanes(self) -> u8 {
        match self {
            Self::TwoIndependentRelationLanes => 2,
            _ => 1,
        }
    }

    pub const fn point_components(self) -> u8 {
        match self {
            Self::OnePointBaseline => 1,
            _ => 2,
        }
    }

    pub const fn relation_proof_bytes(self) -> u32 {
        self.relation_lanes() as u32 * TWO_POINT_ROUNDS * SUMCHECK_BYTES as u32
    }

    /// Exact no-retry SHA-256 backend calls made by the diagnostic transcript:
    /// five common pre-gamma absorbs, gamma's squeeze+advance, each relation
    /// polynomial absorb, and each round challenge's squeeze+advance. Only
    /// fresh-kappa adds another squeeze+advance.
    pub const fn transcript_hash_calls_no_retry(self) -> u32 {
        let common_prefix_and_gamma = 5 + 2;
        let kappa = match self {
            Self::FreshKappaSingleLane => 2,
            _ => 0,
        };
        common_prefix_and_gamma + kappa + TWO_POINT_ROUNDS * (self.relation_lanes() as u32 + 2)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TwoPointBatchingProbeError {
    ChallengeSampleExhausted,
    WeightShape,
    FixtureDecode,
    BoundaryMismatch,
    TerminalMismatch,
}

impl From<ChallengeSampleExhausted> for TwoPointBatchingProbeError {
    fn from(_: ChallengeSampleExhausted) -> Self {
        Self::ChallengeSampleExhausted
    }
}

impl From<TensorWeightError> for TwoPointBatchingProbeError {
    fn from(_: TensorWeightError) -> Self {
        Self::WeightShape
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TwoPointBatchingProbeResult {
    pub sink: QM31,
    pub gamma: QM31,
    pub kappa: Option<QM31>,
    pub relation_lanes: u8,
    pub point_components: u8,
    pub relation_polynomials: u8,
    pub relation_proof_bytes: u32,
    pub transcript_hash_calls_no_retry: u32,
}

// Filled from the deterministic host fixture and asserted on both host and
// SBF. Re-pin only for a named change to this diagnostic kernel.
pub const TWO_POINT_BATCHING_EXPECTED_SINKS: [[u8; 16]; 4] = [
    [
        222, 251, 66, 82, 231, 180, 205, 96, 143, 65, 236, 104, 78, 27, 63, 83,
    ],
    [
        7, 54, 249, 40, 55, 217, 139, 71, 105, 186, 34, 73, 70, 221, 145, 96,
    ],
    [
        150, 225, 124, 31, 196, 45, 115, 104, 225, 253, 42, 25, 165, 37, 19, 12,
    ],
    [
        84, 129, 131, 73, 145, 24, 194, 19, 221, 240, 51, 32, 183, 52, 83, 124,
    ],
];

fn sample(index: u32, lane: u32) -> QM31 {
    let limb = |offset: u32| {
        M31(1 + index
            .wrapping_mul(131)
            .wrapping_add(lane * 977 + offset * 17)
            % 1_000_003)
    };
    QM31 {
        c0: CM31::new(limb(0), limb(1)),
        c1: CM31::new(limb(2), limb(3)),
    }
}

fn encode_qm31(values: &[QM31]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len() * 16];
    for (value, chunk) in values.iter().zip(bytes.chunks_exact_mut(16)) {
        value.write_le_bytes(chunk);
    }
    bytes
}

fn fixture_points() -> (Vec<QM31>, Vec<QM31>) {
    let first = (0..TWO_POINT_COORDINATES)
        .map(|coordinate| sample(coordinate as u32, 1))
        .collect::<Vec<_>>();
    let mut second = first.clone();
    for coordinate in &mut second[TWO_POINT_COORDINATES - 2..] {
        *coordinate = QM31::ONE.sub(*coordinate);
    }
    (first, second)
}

fn fixture_values() -> Vec<QM31> {
    (0..TWO_POINT_STATEMENT_VALUES)
        .map(|index| sample(index as u32, 2))
        .collect()
}

#[cfg(test)]
fn fixture_coefficients() -> Vec<QM31> {
    (0..1u32 << TWO_POINT_LOG_ROWS)
        .map(|index| sample(index, 3))
        .collect()
}

fn absorb_common_prefix(
    transcript: &mut Transcript,
    first: &[QM31],
    second: &[QM31],
    values: &[QM31],
) {
    transcript.absorb(label::PROFILE, b"aspis:two-point-batching-probe:v0");
    transcript.absorb(label::STATEMENT, &[0x5a; 32]);
    transcript.absorb(label::CLAIM, &encode_qm31(first));
    transcript.absorb(label::CLAIM, &encode_qm31(second));
    transcript.absorb(TWO_POINT_VALUES_LABEL, &encode_qm31(values));
}

#[cfg(test)]
fn fold_coefficients(coefficients: &[QM31], alpha: QM31) -> Vec<QM31> {
    let alpha2 = alpha.square();
    let alpha3 = alpha2.mul(alpha);
    coefficients
        .chunks_exact(4)
        .map(|chunk| {
            chunk[0]
                .add(alpha.mul(chunk[1]))
                .add(alpha2.mul(chunk[2]))
                .add(alpha3.mul(chunk[3]))
        })
        .collect()
}

fn fixture_blob(mode: TwoPointBatchingMode) -> &'static [u8] {
    match mode {
        TwoPointBatchingMode::OnePointBaseline => &crate::two_point_fixtures::ONE_POINT_BASELINE,
        TwoPointBatchingMode::FreshKappaSingleLane => {
            &crate::two_point_fixtures::FRESH_KAPPA_SINGLE_LANE
        }
        TwoPointBatchingMode::TwoIndependentRelationLanes => {
            &crate::two_point_fixtures::TWO_INDEPENDENT_RELATION_LANES
        }
        TwoPointBatchingMode::DisjointGamma51SingleLane => {
            &crate::two_point_fixtures::DISJOINT_GAMMA51_SINGLE_LANE
        }
    }
}

fn take_qm31(bytes: &[u8], cursor: &mut usize) -> Result<QM31, TwoPointBatchingProbeError> {
    let end = cursor
        .checked_add(16)
        .ok_or(TwoPointBatchingProbeError::FixtureDecode)?;
    let value = QM31::from_le_bytes(
        bytes
            .get(*cursor..end)
            .ok_or(TwoPointBatchingProbeError::FixtureDecode)?,
    )
    .ok_or(TwoPointBatchingProbeError::FixtureDecode)?;
    *cursor = end;
    Ok(value)
}

fn take_polynomial(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<SumcheckPolynomial, TwoPointBatchingProbeError> {
    let mut polynomial = [QM31::ZERO; crate::sumcheck::SUMCHECK_COEFFICIENTS];
    for coefficient in &mut polynomial {
        *coefficient = take_qm31(bytes, cursor)?;
    }
    Ok(polynomial)
}

fn build_lanes(
    mode: TwoPointBatchingMode,
    first: Vec<QM31>,
    second: Vec<QM31>,
    gamma: QM31,
    kappa: Option<QM31>,
) -> Result<Vec<WeightAccumulator>, TwoPointBatchingProbeError> {
    let mut lanes = Vec::with_capacity(mode.relation_lanes() as usize);
    match mode {
        TwoPointBatchingMode::OnePointBaseline => {
            let mut weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
            weights.add_multilinear(QM31::ONE, first)?;
            lanes.push(weights);
        }
        TwoPointBatchingMode::FreshKappaSingleLane => {
            let mut weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
            weights.add_multilinear(QM31::ONE, first)?;
            weights.add_multilinear(
                kappa.ok_or(TwoPointBatchingProbeError::FixtureDecode)?,
                second,
            )?;
            lanes.push(weights);
        }
        TwoPointBatchingMode::TwoIndependentRelationLanes => {
            let mut first_weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
            first_weights.add_multilinear(QM31::ONE, first)?;
            lanes.push(first_weights);
            let mut second_weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
            second_weights.add_multilinear(QM31::ONE, second)?;
            lanes.push(second_weights);
        }
        TwoPointBatchingMode::DisjointGamma51SingleLane => {
            let mut weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
            weights.add_multilinear(QM31::ONE, first)?;
            weights.add_multilinear(gamma.pow(51), second)?;
            lanes.push(weights);
        }
    }
    Ok(lanes)
}

fn absorb_polynomial(transcript: &mut Transcript, polynomial: &SumcheckPolynomial) {
    let mut bytes = [0u8; SUMCHECK_BYTES];
    for (coefficient, chunk) in polynomial.iter().zip(bytes.chunks_exact_mut(16)) {
        coefficient.write_le_bytes(chunk);
    }
    transcript.absorb(label::SUMCHECK_POLY, &bytes);
}

fn marker(value: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(value)))
}

pub fn two_point_batching_probe(
    hash: HashFn,
    mode: TwoPointBatchingMode,
) -> Result<TwoPointBatchingProbeResult, TwoPointBatchingProbeError> {
    let (first, second) = fixture_points();
    let values = fixture_values();
    let mut transcript = Transcript::new(hash);
    absorb_common_prefix(&mut transcript, &first, &second, &values);
    let gamma = transcript.challenge_qm31()?;
    let kappa = if mode == TwoPointBatchingMode::FreshKappaSingleLane {
        Some(transcript.challenge_qm31()?)
    } else {
        None
    };

    let mut lanes = build_lanes(mode, first, second, gamma, kappa)?;
    let blob = fixture_blob(mode);
    let expected_blob_len =
        mode.relation_lanes() as usize * 16 + mode.relation_proof_bytes() as usize + 4 * 16;
    if blob.len() != expected_blob_len {
        return Err(TwoPointBatchingProbeError::FixtureDecode);
    }
    let mut cursor = 0usize;
    let mut running_claims = Vec::with_capacity(lanes.len());
    for _ in 0..lanes.len() {
        running_claims.push(take_qm31(blob, &mut cursor)?);
    }
    let mut sink = marker(MODE_MARKERS[mode.index()]).add(gamma.mul(marker(17)));
    if let Some(kappa) = kappa {
        sink = sink.add(kappa.mul(marker(19)));
    }

    for round in 0..TWO_POINT_ROUNDS {
        let mut polynomials = Vec::with_capacity(lanes.len());
        for (lane, running_claim) in running_claims.iter().copied().enumerate() {
            let polynomial = take_polynomial(blob, &mut cursor)?;
            let boundary = boundary_sum(&polynomial);
            if boundary != running_claim {
                return Err(TwoPointBatchingProbeError::BoundaryMismatch);
            }
            absorb_polynomial(&mut transcript, &polynomial);
            for (degree, coefficient) in polynomial.iter().enumerate() {
                let scale = marker(31 + round * 29 + lane as u32 * 11 + degree as u32);
                sink = sink.add(coefficient.mul(scale));
            }
            polynomials.push(polynomial);
        }

        let alpha = transcript.challenge_qm31()?;
        sink = sink.add(alpha.mul(marker(43 + round)));
        for (lane, polynomial) in polynomials.iter().enumerate() {
            running_claims[lane] = evaluate(polynomial, alpha);
            sink = sink.add(running_claims[lane].mul(marker(53 + lane as u32 + round * 7)));
            lanes[lane].fold(alpha);
        }
    }

    let mut terminal_coefficients = [QM31::ZERO; 4];
    for coefficient in &mut terminal_coefficients {
        *coefficient = take_qm31(blob, &mut cursor)?;
    }
    if cursor != blob.len() {
        return Err(TwoPointBatchingProbeError::FixtureDecode);
    }
    for (lane, weights) in lanes.iter().enumerate() {
        let terminal = weights.dot(&terminal_coefficients);
        if terminal != running_claims[lane] {
            return Err(TwoPointBatchingProbeError::TerminalMismatch);
        }
        sink = sink.add(terminal.mul(marker(89 + lane as u32 * 13)));
    }

    Ok(TwoPointBatchingProbeResult {
        sink,
        gamma,
        kappa,
        relation_lanes: mode.relation_lanes(),
        point_components: mode.point_components(),
        relation_polynomials: mode.relation_lanes() * TWO_POINT_ROUNDS as u8,
        relation_proof_bytes: mode.relation_proof_bytes(),
        transcript_hash_calls_no_retry: mode.transcript_hash_calls_no_retry(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicU32, Ordering};

    static HASH_CALLS: AtomicU32 = AtomicU32::new(0);

    fn sha_hash(inputs: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};

        let mut hasher = Sha256::new();
        for input in inputs {
            hasher.update(input);
        }
        hasher.finalize().into()
    }

    fn counting_hash(inputs: &[&[u8]]) -> [u8; 32] {
        HASH_CALLS.fetch_add(1, Ordering::Relaxed);
        sha_hash(inputs)
    }

    fn encode(value: QM31) -> [u8; 16] {
        let mut bytes = [0u8; 16];
        value.write_le_bytes(&mut bytes);
        bytes
    }

    fn generated_fixture_blob(
        hash: HashFn,
        mode: TwoPointBatchingMode,
    ) -> Result<Vec<u8>, TwoPointBatchingProbeError> {
        let (first, second) = fixture_points();
        let values = fixture_values();
        let mut transcript = Transcript::new(hash);
        absorb_common_prefix(&mut transcript, &first, &second, &values);
        let gamma = transcript.challenge_qm31()?;
        let kappa = if mode == TwoPointBatchingMode::FreshKappaSingleLane {
            Some(transcript.challenge_qm31()?)
        } else {
            None
        };

        let mut lanes = Vec::with_capacity(mode.relation_lanes() as usize);
        match mode {
            TwoPointBatchingMode::OnePointBaseline => {
                let mut weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
                weights.add_multilinear(QM31::ONE, first)?;
                lanes.push(weights);
            }
            TwoPointBatchingMode::FreshKappaSingleLane => {
                let mut weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
                weights.add_multilinear(QM31::ONE, first)?;
                weights.add_multilinear(kappa.unwrap(), second)?;
                lanes.push(weights);
            }
            TwoPointBatchingMode::TwoIndependentRelationLanes => {
                let mut first_weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
                first_weights.add_multilinear(QM31::ONE, first)?;
                lanes.push(first_weights);
                let mut second_weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
                second_weights.add_multilinear(QM31::ONE, second)?;
                lanes.push(second_weights);
            }
            TwoPointBatchingMode::DisjointGamma51SingleLane => {
                let mut weights = WeightAccumulator::empty(TWO_POINT_LOG_ROWS);
                weights.add_multilinear(QM31::ONE, first)?;
                weights.add_multilinear(gamma.pow(51), second)?;
                lanes.push(weights);
            }
        }

        let mut coefficients = fixture_coefficients();
        let mut running_claims = lanes
            .iter()
            .map(|weights| weights.dot(&coefficients))
            .collect::<Vec<_>>();
        let mut blob = encode_qm31(&running_claims);
        for _ in 0..TWO_POINT_ROUNDS {
            let mut polynomials = Vec::with_capacity(lanes.len());
            for weights in &lanes {
                let polynomial = polynomial_for_extension(&coefficients, weights);
                absorb_polynomial(&mut transcript, &polynomial);
                blob.extend_from_slice(&encode_qm31(&polynomial));
                polynomials.push(polynomial);
            }
            let alpha = transcript.challenge_qm31()?;
            for (lane, polynomial) in polynomials.iter().enumerate() {
                running_claims[lane] = evaluate(polynomial, alpha);
                lanes[lane].fold(alpha);
            }
            coefficients = fold_coefficients(&coefficients, alpha);
        }
        blob.extend_from_slice(&encode_qm31(&coefficients));
        Ok(blob)
    }

    fn canonical_kappa_challenges(hash: HashFn) -> (QM31, QM31) {
        let (first, second) = fixture_points();
        let values = fixture_values();
        let mut transcript = Transcript::new(hash);
        absorb_common_prefix(&mut transcript, &first, &second, &values);
        let gamma = transcript.challenge_qm31().unwrap();
        let kappa = transcript.challenge_qm31().unwrap();
        (gamma, kappa)
    }

    fn weakened_kappa_before_values_challenges(hash: HashFn) -> (QM31, QM31) {
        let (first, second) = fixture_points();
        let values = fixture_values();
        let mut transcript = Transcript::new(hash);
        transcript.absorb(label::PROFILE, b"aspis:two-point-batching-probe:v0");
        transcript.absorb(label::STATEMENT, &[0x5a; 32]);
        transcript.absorb(label::CLAIM, &encode_qm31(&first));
        transcript.absorb(label::CLAIM, &encode_qm31(&second));
        let kappa = transcript.challenge_qm31().unwrap();
        transcript.absorb(TWO_POINT_VALUES_LABEL, &encode_qm31(&values));
        let gamma = transcript.challenge_qm31().unwrap();
        (gamma, kappa)
    }

    fn weakened_one_point_accepts(error_0: QM31, _error_1: QM31) -> bool {
        error_0 == QM31::ZERO
    }

    fn canonical_two_lanes_accept(error_0: QM31, error_1: QM31) -> bool {
        error_0 == QM31::ZERO && error_1 == QM31::ZERO
    }

    fn canonical_kappa_accepts(kappa: QM31, error_0: QM31, error_1: QM31) -> bool {
        error_0.add(kappa.mul(error_1)) == QM31::ZERO
    }

    fn weakened_fixed_scale_accepts(error_0: QM31, error_1: QM31) -> bool {
        error_0.add(error_1) == QM31::ZERO
    }

    fn weakened_swapped_kappa_accepts(kappa: QM31, error_0: QM31, error_1: QM31) -> bool {
        kappa.mul(error_0).add(error_1) == QM31::ZERO
    }

    fn canonical_kappa_schedule_accepts(hash: HashFn, candidate: (QM31, QM31)) -> bool {
        canonical_kappa_challenges(hash) == candidate
    }

    fn weakened_early_kappa_schedule_accepts(hash: HashFn, candidate: (QM31, QM31)) -> bool {
        weakened_kappa_before_values_challenges(hash) == candidate
    }

    fn canonical_gamma51_accepts(gamma: QM31, error_0: QM31, error_1: QM31) -> bool {
        error_0.add(gamma.pow(51).mul(error_1)) == QM31::ZERO
    }

    fn weakened_omitted_shift_accepts(error_0: QM31, error_1: QM31) -> bool {
        error_0.add(error_1) == QM31::ZERO
    }

    fn weakened_gamma50_accepts(gamma: QM31, error_0: QM31, error_1: QM31) -> bool {
        error_0.add(gamma.pow(50).mul(error_1)) == QM31::ZERO
    }

    #[test]
    fn deterministic_modes_pin_sinks_and_exact_hash_counts() {
        let mut actual_sinks = [[0u8; 16]; 4];
        for mode in TwoPointBatchingMode::ALL {
            HASH_CALLS.store(0, Ordering::Relaxed);
            let result = two_point_batching_probe(counting_hash, mode).unwrap();
            assert_eq!(
                generated_fixture_blob(sha_hash, mode).unwrap(),
                fixture_blob(mode),
                "embedded verifier fixture drifted from host generator for {mode:?}"
            );
            assert_eq!(
                HASH_CALLS.load(Ordering::Relaxed),
                result.transcript_hash_calls_no_retry
            );
            actual_sinks[mode.index()] = encode(result.sink);
            assert_eq!(
                result.relation_proof_bytes,
                u32::from(result.relation_polynomials) * SUMCHECK_BYTES as u32
            );
        }
        assert_eq!(
            actual_sinks, TWO_POINT_BATCHING_EXPECTED_SINKS,
            "two-point batching diagnostic sinks drifted"
        );
    }

    #[test]
    fn one_point_baseline_exposes_cross_point_cancellation() {
        let error_0 = QM31::ZERO;
        let error_1 = sample(7, 9);
        assert!(weakened_one_point_accepts(error_0, error_1));
        assert!(!canonical_two_lanes_accept(error_0, error_1));
    }

    #[test]
    fn fresh_kappa_cancellation_scale_swap_and_order_have_teeth() {
        let (_, kappa) = canonical_kappa_challenges(sha_hash);
        let delta = sample(11, 10);

        // Fixed scale one accepts opposite errors; canonical fresh kappa does
        // not, except at its ledgered field-probability event.
        let error_0 = delta;
        let error_1 = delta.neg();
        assert!(weakened_fixed_scale_accepts(error_0, error_1));
        assert!(!canonical_kappa_accepts(kappa, error_0, error_1));

        // Swapping scales accepts its paired vector while canonical order
        // rejects it.
        let error_0 = delta;
        let error_1 = kappa.mul(delta).neg();
        assert!(weakened_swapped_kappa_accepts(kappa, error_0, error_1));
        assert!(!canonical_kappa_accepts(kappa, error_0, error_1));

        let candidate = weakened_kappa_before_values_challenges(sha_hash);
        assert!(weakened_early_kappa_schedule_accepts(sha_hash, candidate));
        assert!(!canonical_kappa_schedule_accepts(sha_hash, candidate));
    }

    #[test]
    fn two_independent_lanes_reject_an_omitted_second_lane() {
        let error_0 = QM31::ZERO;
        let error_1 = sample(13, 11);
        assert!(weakened_one_point_accepts(error_0, error_1));
        assert!(!canonical_two_lanes_accept(error_0, error_1));
    }

    #[test]
    fn disjoint_gamma_shift_omission_and_off_by_one_have_teeth() {
        let (gamma, _) = canonical_kappa_challenges(sha_hash);
        let delta = sample(17, 12);

        let error_1 = delta;
        let omitted_error_0 = delta.neg();
        assert!(weakened_omitted_shift_accepts(omitted_error_0, error_1));
        assert!(!canonical_gamma51_accepts(gamma, omitted_error_0, error_1));

        let off_by_one_error_0 = gamma.pow(50).mul(delta).neg();
        assert!(weakened_gamma50_accepts(gamma, off_by_one_error_0, error_1));
        assert!(!canonical_gamma51_accepts(
            gamma,
            off_by_one_error_0,
            error_1
        ));
    }
}
