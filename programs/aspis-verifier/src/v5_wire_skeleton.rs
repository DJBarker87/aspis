//! Fail-closed executable grammar for the proposed v5 Spend prefix.
//!
//! This module deliberately stops at the first missing cryptographic seam.
//! It pins byte order, lane roles, dimensions, the ten degree-27 sumcheck
//! messages, the 19-by-4 opening table, and the component-B terminal identity.
//! The trailing lane-digest table is synthetic test data, not a circle-PCS
//! proof.  [`verify_v5_wire_for_production`] therefore rejects every value
//! accepted by [`verify_synthetic_v5_wire`].  Replacing that rejection requires
//! a real opening proof authenticating all 76 claims against the pre-eta root.

use aspis_core::field::{CM31, M31, P, QM31};

pub const V5_WIRE_MAGIC: [u8; 8] = *b"AV5PFX01";
pub const V5_WIRE_VERSION: u8 = 1;
pub const V5_WIRE_SYNTHETIC_PCS_FLAG: u8 = 1;

pub const V5_WIRE_C1_LANES: usize = 16;
pub const V5_WIRE_AUX_LANES: usize = 3;
pub const V5_WIRE_LANES: usize = V5_WIRE_C1_LANES + V5_WIRE_AUX_LANES;
pub const V5_WIRE_HCOPY_LANE: usize = 16;
pub const V5_WIRE_COMPONENT_B_LANE: usize = 17;
pub const V5_WIRE_COMPONENT_C_LANE: usize = 18;

pub const V5_WIRE_C1_VALUE_BYTES: usize = 256;
pub const V5_WIRE_C2_VALUE_BYTES: usize = 192;
pub const V5_WIRE_CLAIMS_PER_LANE: usize = 4;
pub const V5_WIRE_OPENING_CLAIMS: usize = V5_WIRE_LANES * V5_WIRE_CLAIMS_PER_LANE;
pub const V5_WIRE_ROUNDS: usize = 10;
pub const V5_WIRE_SUMCHECK_DEGREE: usize = 27;
pub const V5_WIRE_ROUND_COEFFICIENTS: usize = V5_WIRE_SUMCHECK_DEGREE + 1;

const QM31_BYTES: usize = 16;
const DIGEST_BYTES: usize = 32;
const POINT_MAJOR_CLAIM_LAYOUT: u8 = 0;
const AUX_ROLE_HCOPY: u8 = 1;
const AUX_ROLE_COMPONENT_B: u8 = 2;
const AUX_ROLE_COMPONENT_C: u8 = 3;
pub const V5_WIRE_AUX_ROLES: [u8; V5_WIRE_AUX_LANES] =
    [AUX_ROLE_HCOPY, AUX_ROLE_COMPONENT_B, AUX_ROLE_COMPONENT_C];

/// Fixed header through the point-major layout tag.  The transcript root is
/// the next field; the synthetic lane table lives after the transcript fields
/// and is not absorbed as a challenge after the fact.
pub const V5_WIRE_HEADER_BYTES: usize = 23;
pub const V5_WIRE_ROOT_OFFSET: usize = V5_WIRE_HEADER_BYTES;
pub const V5_WIRE_INITIAL_CLAIM_OFFSET: usize = V5_WIRE_ROOT_OFFSET + DIGEST_BYTES;
pub const V5_WIRE_ROUNDS_OFFSET: usize = V5_WIRE_INITIAL_CLAIM_OFFSET + QM31_BYTES;
pub const V5_WIRE_ROUND_MESSAGE_BYTES: usize = V5_WIRE_ROUND_COEFFICIENTS * QM31_BYTES;
pub const V5_WIRE_ROUND_RECORD_BYTES: usize = V5_WIRE_ROUND_MESSAGE_BYTES;
pub const V5_WIRE_OPENINGS_OFFSET: usize =
    V5_WIRE_ROUNDS_OFFSET + V5_WIRE_ROUNDS * V5_WIRE_ROUND_RECORD_BYTES;
pub const V5_WIRE_TERMINALS_OFFSET: usize =
    V5_WIRE_OPENINGS_OFFSET + V5_WIRE_OPENING_CLAIMS * QM31_BYTES;
pub const V5_WIRE_SYNTHETIC_LANES_OFFSET: usize = V5_WIRE_TERMINALS_OFFSET + 3 * QM31_BYTES;
pub const V5_WIRE_PREFIX_BYTES: usize =
    V5_WIRE_SYNTHETIC_LANES_OFFSET + V5_WIRE_LANES * DIGEST_BYTES;

const SYNTHETIC_ROOT_DOMAIN: &[u8] = b"aspis-v5-wire-synthetic-root-v1";
const SYNTHETIC_LANE_DOMAIN: &[u8] = b"aspis-v5-wire-synthetic-lane-v1";
const SYNTHETIC_B_LANE_DOMAIN: &[u8] = b"aspis-v5-wire-synthetic-b-state-v1";
const SYNTHETIC_TRANSCRIPT_DOMAIN: &[u8] = b"aspis-v5-wire-transcript-v1";
const SYNTHETIC_ROUND_DOMAIN: &[u8] = b"aspis-v5-wire-round-v1";
const SYNTHETIC_KAPPA_DOMAIN: &[u8] = b"aspis-v5-wire-kappa-v1";

pub type Hashv = fn(&[&[u8]]) -> [u8; DIGEST_BYTES];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5WireError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    UnsupportedFlags,
    WrongWidths,
    WrongLaneShape,
    WrongAuxRoles,
    WrongRoundShape,
    WrongClaimShape,
    NonCanonicalField,
    ZeroTranscriptChallenge,
    SyntheticRootMismatch,
    SumcheckBoundaryMismatch,
    SumcheckTerminalMismatch,
    ComponentBOpeningMismatch,
    TerminalIdentityMismatch,
    EmptySyntheticLaneDigest,
    /// The exact blocker at the edge of the executable skeleton: no real PCS
    /// opening proof authenticates the 76 released claims against the root.
    SyntheticPcsAuthenticationForbidden,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5AuxLaneRole {
    Hcopy,
    ComponentB,
    ComponentC,
}

#[derive(Clone, Copy)]
pub struct ParsedV5Wire<'a> {
    bytes: &'a [u8],
}

impl ParsedV5Wire<'_> {
    pub fn root(&self) -> &[u8; DIGEST_BYTES] {
        self.bytes[V5_WIRE_ROOT_OFFSET..V5_WIRE_INITIAL_CLAIM_OFFSET]
            .try_into()
            .expect("fixed root bounds")
    }

    pub fn initial_claim(&self) -> Result<QM31, V5WireError> {
        decode_qm31(self.bytes, V5_WIRE_INITIAL_CLAIM_OFFSET)
    }

    pub fn round_message(&self, round: usize) -> &[u8] {
        let start = V5_WIRE_ROUNDS_OFFSET + round * V5_WIRE_ROUND_RECORD_BYTES;
        &self.bytes[start..start + V5_WIRE_ROUND_MESSAGE_BYTES]
    }

    /// Claims are serialized point-major: `point * 19 + lane`.
    pub fn opening_claim(&self, point: usize, lane: usize) -> Result<QM31, V5WireError> {
        if point >= V5_WIRE_CLAIMS_PER_LANE || lane >= V5_WIRE_LANES {
            return Err(V5WireError::WrongClaimShape);
        }
        decode_qm31(
            self.bytes,
            V5_WIRE_OPENINGS_OFFSET + (point * V5_WIRE_LANES + lane) * QM31_BYTES,
        )
    }

    pub fn terminal_real(&self) -> Result<QM31, V5WireError> {
        decode_qm31(self.bytes, V5_WIRE_TERMINALS_OFFSET)
    }

    pub fn terminal_mask(&self) -> Result<QM31, V5WireError> {
        decode_qm31(self.bytes, V5_WIRE_TERMINALS_OFFSET + QM31_BYTES)
    }

    pub fn terminal_masked(&self) -> Result<QM31, V5WireError> {
        decode_qm31(self.bytes, V5_WIRE_TERMINALS_OFFSET + 2 * QM31_BYTES)
    }

    pub fn synthetic_lane_digest(&self, lane: usize) -> Result<&[u8; DIGEST_BYTES], V5WireError> {
        if lane >= V5_WIRE_LANES {
            return Err(V5WireError::WrongLaneShape);
        }
        let start = V5_WIRE_SYNTHETIC_LANES_OFFSET + lane * DIGEST_BYTES;
        Ok(self.bytes[start..start + DIGEST_BYTES]
            .try_into()
            .expect("fixed lane digest bounds"))
    }

    pub const fn aux_role(lane: usize) -> Option<V5AuxLaneRole> {
        match lane {
            V5_WIRE_HCOPY_LANE => Some(V5AuxLaneRole::Hcopy),
            V5_WIRE_COMPONENT_B_LANE => Some(V5AuxLaneRole::ComponentB),
            V5_WIRE_COMPONENT_C_LANE => Some(V5AuxLaneRole::ComponentC),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedSyntheticV5Wire {
    pub eta: QM31,
    pub round_challenges: [QM31; V5_WIRE_ROUNDS],
    pub kappa: QM31,
    pub terminal_real: QM31,
    pub terminal_mask: QM31,
    pub terminal_masked: QM31,
}

pub fn parse_v5_wire(bytes: &[u8]) -> Result<ParsedV5Wire<'_>, V5WireError> {
    if bytes.len() != V5_WIRE_PREFIX_BYTES {
        return Err(V5WireError::WrongLength);
    }
    if bytes[..V5_WIRE_MAGIC.len()] != V5_WIRE_MAGIC {
        return Err(V5WireError::WrongMagic);
    }
    if bytes[8] != V5_WIRE_VERSION {
        return Err(V5WireError::WrongVersion);
    }
    if bytes[9] != V5_WIRE_SYNTHETIC_PCS_FLAG {
        return Err(V5WireError::UnsupportedFlags);
    }
    if u16::from_le_bytes(bytes[10..12].try_into().unwrap()) != V5_WIRE_C1_VALUE_BYTES as u16
        || u16::from_le_bytes(bytes[12..14].try_into().unwrap()) != V5_WIRE_C2_VALUE_BYTES as u16
    {
        return Err(V5WireError::WrongWidths);
    }
    if usize::from(bytes[14]) != V5_WIRE_C1_LANES || usize::from(bytes[15]) != V5_WIRE_AUX_LANES {
        return Err(V5WireError::WrongLaneShape);
    }
    if bytes[16..19] != V5_WIRE_AUX_ROLES {
        return Err(V5WireError::WrongAuxRoles);
    }
    if usize::from(bytes[19]) != V5_WIRE_ROUNDS || usize::from(bytes[20]) != V5_WIRE_SUMCHECK_DEGREE
    {
        return Err(V5WireError::WrongRoundShape);
    }
    if usize::from(bytes[21]) != V5_WIRE_CLAIMS_PER_LANE {
        return Err(V5WireError::WrongClaimShape);
    }
    if bytes[22] != POINT_MAJOR_CLAIM_LAYOUT {
        return Err(V5WireError::WrongClaimShape);
    }
    Ok(ParsedV5Wire { bytes })
}

fn decode_qm31(bytes: &[u8], offset: usize) -> Result<QM31, V5WireError> {
    QM31::from_le_bytes(
        bytes
            .get(offset..offset + QM31_BYTES)
            .ok_or(V5WireError::WrongLength)?,
    )
    .ok_or(V5WireError::NonCanonicalField)
}

fn digest_to_synthetic_qm31(digest: [u8; DIGEST_BYTES]) -> QM31 {
    let limb = |index: usize| {
        let word = u32::from_le_bytes(
            digest[index * 4..index * 4 + 4]
                .try_into()
                .expect("digest limb bounds"),
        ) & P;
        M31(if word == P { 0 } else { word })
    };
    QM31 {
        c0: CM31::new(limb(0), limb(1)),
        c1: CM31::new(limb(2), limb(3)),
    }
}

fn synthetic_root(parsed: ParsedV5Wire<'_>, hashv: Hashv) -> [u8; DIGEST_BYTES] {
    hashv(&[
        SYNTHETIC_ROOT_DOMAIN,
        &parsed.bytes[..V5_WIRE_ROOT_OFFSET],
        &parsed.bytes[V5_WIRE_SYNTHETIC_LANES_OFFSET..],
    ])
}

fn round_coefficients(
    parsed: ParsedV5Wire<'_>,
    round: usize,
) -> Result<[QM31; V5_WIRE_ROUND_COEFFICIENTS], V5WireError> {
    let message = parsed.round_message(round);
    let mut coefficients = [QM31::ZERO; V5_WIRE_ROUND_COEFFICIENTS];
    for (index, coefficient) in coefficients.iter_mut().enumerate() {
        *coefficient = decode_qm31(message, index * QM31_BYTES)?;
    }
    Ok(coefficients)
}

fn polynomial_evaluation(coefficients: &[QM31; V5_WIRE_ROUND_COEFFICIENTS], point: QM31) -> QM31 {
    coefficients
        .iter()
        .rev()
        .copied()
        .fold(QM31::ZERO, |value, coefficient| {
            value.mul(point).add(coefficient)
        })
}

pub fn verify_synthetic_v5_wire(
    bytes: &[u8],
    hashv: Hashv,
) -> Result<VerifiedSyntheticV5Wire, V5WireError> {
    let parsed = parse_v5_wire(bytes)?;
    for lane in 0..V5_WIRE_LANES {
        if parsed
            .synthetic_lane_digest(lane)?
            .iter()
            .all(|byte| *byte == 0)
        {
            return Err(V5WireError::EmptySyntheticLaneDigest);
        }
    }
    let root = synthetic_root(parsed, hashv);
    if &root != parsed.root() {
        return Err(V5WireError::SyntheticRootMismatch);
    }
    let eta = digest_to_synthetic_qm31(hashv(&[SYNTHETIC_TRANSCRIPT_DOMAIN, parsed.root()]));
    if eta.is_zero() {
        return Err(V5WireError::ZeroTranscriptChallenge);
    }

    let mut incoming_claim = parsed.initial_claim()?;
    let mut eta_bytes = [0u8; QM31_BYTES];
    eta.write_le_bytes(&mut eta_bytes);
    let mut transcript_state = hashv(&[
        SYNTHETIC_TRANSCRIPT_DOMAIN,
        parsed.root(),
        &eta_bytes,
        &bytes[V5_WIRE_INITIAL_CLAIM_OFFSET..V5_WIRE_ROUNDS_OFFSET],
    ]);
    let mut round_challenges = [QM31::ZERO; V5_WIRE_ROUNDS];
    for round in 0..V5_WIRE_ROUNDS {
        let coefficients = round_coefficients(parsed, round)?;
        let at_zero = coefficients[0];
        let at_one = coefficients.iter().copied().fold(QM31::ZERO, QM31::add);
        if at_zero.add(at_one) != incoming_claim {
            return Err(V5WireError::SumcheckBoundaryMismatch);
        }

        let round_byte = [round as u8];
        transcript_state = hashv(&[
            SYNTHETIC_ROUND_DOMAIN,
            &transcript_state,
            &round_byte,
            parsed.round_message(round),
        ]);
        let challenge = digest_to_synthetic_qm31(transcript_state);
        round_challenges[round] = challenge;
        incoming_claim = polynomial_evaluation(&coefficients, challenge);
    }

    // Decode every released coordinate even though only B's fourth claim is
    // used by the terminal equation.  This pins the canonical 19-by-4 wire.
    for point in 0..V5_WIRE_CLAIMS_PER_LANE {
        for lane in 0..V5_WIRE_LANES {
            parsed.opening_claim(point, lane)?;
        }
    }
    let terminal_real = parsed.terminal_real()?;
    let terminal_mask = parsed.terminal_mask()?;
    let terminal_masked = parsed.terminal_masked()?;
    if terminal_masked != incoming_claim {
        return Err(V5WireError::SumcheckTerminalMismatch);
    }
    if parsed.opening_claim(V5_WIRE_CLAIMS_PER_LANE - 1, V5_WIRE_COMPONENT_B_LANE)? != terminal_mask
    {
        return Err(V5WireError::ComponentBOpeningMismatch);
    }
    if terminal_mask.add(eta.mul(terminal_real)) != terminal_masked {
        return Err(V5WireError::TerminalIdentityMismatch);
    }
    // Functional batching is sampled only after the verifier has absorbed
    // every one of the 76 claims and the terminal tuple.  Kappa is not proof
    // data and cannot be selected by the prover.
    let kappa = digest_to_synthetic_qm31(hashv(&[
        SYNTHETIC_KAPPA_DOMAIN,
        &transcript_state,
        &bytes[V5_WIRE_OPENINGS_OFFSET..V5_WIRE_TERMINALS_OFFSET],
        &bytes[V5_WIRE_TERMINALS_OFFSET..V5_WIRE_SYNTHETIC_LANES_OFFSET],
    ]));
    if kappa.is_zero() {
        return Err(V5WireError::ZeroTranscriptChallenge);
    }

    Ok(VerifiedSyntheticV5Wire {
        eta,
        round_challenges,
        kappa,
        terminal_real,
        terminal_mask,
        terminal_masked,
    })
}

/// Deliberately fail closed until the synthetic lane table is replaced by a
/// real, pre-eta circle-PCS root plus opening authentication for all 76 claims.
pub fn verify_v5_wire_for_production(bytes: &[u8]) -> Result<(), V5WireError> {
    let _ = parse_v5_wire(bytes)?;
    Err(V5WireError::SyntheticPcsAuthenticationForbidden)
}

#[cfg(not(target_os = "solana"))]
fn next_m31(state: &mut u64) -> M31 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    M31((*state % u64::from(P)) as u32)
}

#[cfg(not(target_os = "solana"))]
fn next_qm31(state: &mut u64) -> QM31 {
    QM31 {
        c0: CM31::new(next_m31(state), next_m31(state)),
        c1: CM31::new(next_m31(state), next_m31(state)),
    }
}

#[cfg(not(target_os = "solana"))]
fn write_qm31(output: &mut [u8], offset: usize, value: QM31) {
    value.write_le_bytes(&mut output[offset..offset + QM31_BYTES]);
}

#[cfg(not(target_os = "solana"))]
fn synthetic_b_terminal(
    initial: QM31,
    tails: &[[QM31; V5_WIRE_SUMCHECK_DEGREE]; V5_WIRE_ROUNDS],
    point: &[QM31; V5_WIRE_ROUNDS],
) -> QM31 {
    let half = QM31::ONE.half();
    let mut state = initial;
    for round in 0..V5_WIRE_ROUNDS {
        let mut power = point[round];
        let contribution = tails[round]
            .iter()
            .copied()
            .fold(QM31::ZERO, |sum, coefficient| {
                let next = sum.add(coefficient.mul(power.sub(half)));
                power = power.mul(point[round]);
                next
            });
        state = state.half().add(contribution);
    }
    state
}

/// Deterministic host/KAT prover for the fail-closed grammar.  The component-B
/// lane digest commits (by a plain SHA-256 test hash) to one initial state and
/// 270 tail coordinates; its fourth opening is their exact compact terminal
/// functional.  No PCS authentication path is emitted, hence production
/// verification still rejects the result.
#[cfg(not(target_os = "solana"))]
pub fn build_deterministic_synthetic_v5_wire(hashv: Hashv) -> Vec<u8> {
    let mut random = 0x7055_19c2_27b0_0041u64;
    let mut output = vec![0u8; V5_WIRE_PREFIX_BYTES];
    output[..8].copy_from_slice(&V5_WIRE_MAGIC);
    output[8] = V5_WIRE_VERSION;
    output[9] = V5_WIRE_SYNTHETIC_PCS_FLAG;
    output[10..12].copy_from_slice(&(V5_WIRE_C1_VALUE_BYTES as u16).to_le_bytes());
    output[12..14].copy_from_slice(&(V5_WIRE_C2_VALUE_BYTES as u16).to_le_bytes());
    output[14] = V5_WIRE_C1_LANES as u8;
    output[15] = V5_WIRE_AUX_LANES as u8;
    output[16..19].copy_from_slice(&V5_WIRE_AUX_ROLES);
    output[19] = V5_WIRE_ROUNDS as u8;
    output[20] = V5_WIRE_SUMCHECK_DEGREE as u8;
    output[21] = V5_WIRE_CLAIMS_PER_LANE as u8;
    output[22] = POINT_MAJOR_CLAIM_LAYOUT;

    let b_initial = next_qm31(&mut random);
    let b_tails: [[QM31; V5_WIRE_SUMCHECK_DEGREE]; V5_WIRE_ROUNDS] =
        core::array::from_fn(|_| core::array::from_fn(|_| next_qm31(&mut random)));
    let mut b_state_bytes = vec![0u8; (1 + V5_WIRE_ROUNDS * V5_WIRE_SUMCHECK_DEGREE) * QM31_BYTES];
    write_qm31(&mut b_state_bytes, 0, b_initial);
    for (round, tails) in b_tails.iter().enumerate() {
        for (coefficient, value) in tails.iter().copied().enumerate() {
            write_qm31(
                &mut b_state_bytes,
                (1 + round * V5_WIRE_SUMCHECK_DEGREE + coefficient) * QM31_BYTES,
                value,
            );
        }
    }

    for lane in 0..V5_WIRE_LANES {
        let start = V5_WIRE_SYNTHETIC_LANES_OFFSET + lane * DIGEST_BYTES;
        let lane_byte = [lane as u8];
        let digest = if lane == V5_WIRE_COMPONENT_B_LANE {
            hashv(&[SYNTHETIC_B_LANE_DOMAIN, &lane_byte, &b_state_bytes])
        } else {
            let seed = next_qm31(&mut random);
            let mut seed_bytes = [0u8; QM31_BYTES];
            seed.write_le_bytes(&mut seed_bytes);
            hashv(&[SYNTHETIC_LANE_DOMAIN, &lane_byte, &seed_bytes])
        };
        output[start..start + DIGEST_BYTES].copy_from_slice(&digest);
    }
    let parsed = parse_v5_wire(&output).expect("builder writes the pinned header");
    let root = synthetic_root(parsed, hashv);
    output[V5_WIRE_ROOT_OFFSET..V5_WIRE_INITIAL_CLAIM_OFFSET].copy_from_slice(&root);
    let eta = digest_to_synthetic_qm31(hashv(&[SYNTHETIC_TRANSCRIPT_DOMAIN, &root]));
    assert!(!eta.is_zero(), "pinned synthetic eta must remain nonzero");

    let mut incoming_claim = next_qm31(&mut random);
    write_qm31(&mut output, V5_WIRE_INITIAL_CLAIM_OFFSET, incoming_claim);
    let mut eta_bytes = [0u8; QM31_BYTES];
    eta.write_le_bytes(&mut eta_bytes);
    let mut transcript_state = hashv(&[
        SYNTHETIC_TRANSCRIPT_DOMAIN,
        &root,
        &eta_bytes,
        &output[V5_WIRE_INITIAL_CLAIM_OFFSET..V5_WIRE_ROUNDS_OFFSET],
    ]);
    let mut point = [QM31::ZERO; V5_WIRE_ROUNDS];
    for round in 0..V5_WIRE_ROUNDS {
        let start = V5_WIRE_ROUNDS_OFFSET + round * V5_WIRE_ROUND_RECORD_BYTES;
        let mut coefficients = [QM31::ZERO; V5_WIRE_ROUND_COEFFICIENTS];
        let mut tail_sum = QM31::ZERO;
        for coefficient in coefficients.iter_mut().skip(1) {
            *coefficient = next_qm31(&mut random);
            tail_sum = tail_sum.add(*coefficient);
        }
        coefficients[0] = incoming_claim.sub(tail_sum).half();
        for (index, coefficient) in coefficients.iter().copied().enumerate() {
            write_qm31(&mut output, start + index * QM31_BYTES, coefficient);
        }
        let round_byte = [round as u8];
        transcript_state = hashv(&[
            SYNTHETIC_ROUND_DOMAIN,
            &transcript_state,
            &round_byte,
            &output[start..start + V5_WIRE_ROUND_MESSAGE_BYTES],
        ]);
        let challenge = digest_to_synthetic_qm31(transcript_state);
        point[round] = challenge;
        incoming_claim = polynomial_evaluation(&coefficients, challenge);
    }

    for claim in 0..V5_WIRE_OPENING_CLAIMS {
        write_qm31(
            &mut output,
            V5_WIRE_OPENINGS_OFFSET + claim * QM31_BYTES,
            next_qm31(&mut random),
        );
    }
    let terminal_mask = synthetic_b_terminal(b_initial, &b_tails, &point);
    let component_b_fourth = V5_WIRE_OPENINGS_OFFSET
        + ((V5_WIRE_CLAIMS_PER_LANE - 1) * V5_WIRE_LANES + V5_WIRE_COMPONENT_B_LANE) * QM31_BYTES;
    write_qm31(&mut output, component_b_fourth, terminal_mask);
    let terminal_real = incoming_claim.sub(terminal_mask).mul(eta.inv());
    write_qm31(&mut output, V5_WIRE_TERMINALS_OFFSET, terminal_real);
    write_qm31(
        &mut output,
        V5_WIRE_TERMINALS_OFFSET + QM31_BYTES,
        terminal_mask,
    );
    write_qm31(
        &mut output,
        V5_WIRE_TERMINALS_OFFSET + 2 * QM31_BYTES,
        incoming_claim,
    );

    verify_synthetic_v5_wire(&output, hashv).expect("synthetic builder must round-trip");
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hashv(inputs: &[&[u8]]) -> [u8; 32] {
        solana_program::hash::hashv(inputs).to_bytes()
    }

    #[test]
    fn deterministic_serializer_parser_verifier_round_trip() {
        let bytes = build_deterministic_synthetic_v5_wire(hashv);
        let verified = verify_synthetic_v5_wire(&bytes, hashv).unwrap();
        let parsed = parse_v5_wire(&bytes).unwrap();
        assert_eq!(bytes.len(), V5_WIRE_PREFIX_BYTES);
        assert_eq!(V5_WIRE_LANES, 19);
        assert_eq!(V5_WIRE_OPENING_CLAIMS, 76);
        assert_eq!(ParsedV5Wire::aux_role(16), Some(V5AuxLaneRole::Hcopy));
        assert_eq!(ParsedV5Wire::aux_role(17), Some(V5AuxLaneRole::ComponentB));
        assert_eq!(ParsedV5Wire::aux_role(18), Some(V5AuxLaneRole::ComponentC));
        assert_eq!(
            parsed.opening_claim(3, V5_WIRE_COMPONENT_B_LANE).unwrap(),
            verified.terminal_mask
        );
        assert_eq!(
            verified
                .terminal_mask
                .add(verified.eta.mul(verified.terminal_real)),
            verified.terminal_masked
        );
        assert_eq!(
            verify_v5_wire_for_production(&bytes),
            Err(V5WireError::SyntheticPcsAuthenticationForbidden)
        );
    }

    #[test]
    fn every_placeholder_mutation_fails_closed() {
        let bytes = build_deterministic_synthetic_v5_wire(hashv);
        let mut mutation = bytes.clone();
        mutation[9] = 0;
        assert!(matches!(
            parse_v5_wire(&mutation),
            Err(V5WireError::UnsupportedFlags)
        ));

        mutation = bytes.clone();
        mutation[V5_WIRE_SYNTHETIC_LANES_OFFSET] ^= 1;
        assert_eq!(
            verify_synthetic_v5_wire(&mutation, hashv),
            Err(V5WireError::SyntheticRootMismatch)
        );

        mutation = bytes.clone();
        mutation[V5_WIRE_ROUNDS_OFFSET] ^= 1;
        assert!(verify_synthetic_v5_wire(&mutation, hashv).is_err());

        mutation = bytes.clone();
        let b_fourth = V5_WIRE_OPENINGS_OFFSET
            + ((V5_WIRE_CLAIMS_PER_LANE - 1) * V5_WIRE_LANES + V5_WIRE_COMPONENT_B_LANE)
                * QM31_BYTES;
        mutation[b_fourth] ^= 1;
        assert_eq!(
            verify_synthetic_v5_wire(&mutation, hashv),
            Err(V5WireError::ComponentBOpeningMismatch)
        );
    }

    #[test]
    fn offsets_and_exact_size_are_pinned() {
        assert_eq!(V5_WIRE_HEADER_BYTES, 23);
        assert_eq!(V5_WIRE_ROOT_OFFSET, 23);
        assert_eq!(V5_WIRE_INITIAL_CLAIM_OFFSET, 55);
        assert_eq!(V5_WIRE_ROUNDS_OFFSET, 71);
        assert_eq!(V5_WIRE_OPENINGS_OFFSET, 4_551);
        assert_eq!(V5_WIRE_TERMINALS_OFFSET, 5_767);
        assert_eq!(V5_WIRE_SYNTHETIC_LANES_OFFSET, 5_815);
        assert_eq!(V5_WIRE_PREFIX_BYTES, 6_423);
    }
}
