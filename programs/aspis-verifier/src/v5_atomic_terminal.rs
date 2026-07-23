//! V5-only adapter for the unchanged atomic-v3 semantic terminal.
//!
//! The atomic evaluator's historical input is three rows of 28 claims:
//! sixteen semantic C1 lanes, ten v4 mask-only lanes, Hcopy, and G.  V5 keeps
//! the sixteen semantic lanes and Hcopy, but removes the ten mask-only lanes
//! and G.  This module therefore calls the *unmasked* atomic evaluator after
//! embedding the authenticated v5 point claims into the historical shape.
//! Component B's authenticated fourth opening supplies the new mask term:
//!
//! `terminal_masked = terminal_mask + eta * terminal_real`.
//!
//! Component C is a PCS-view mask and is not a semantic-terminal input.

use aspis_core::field::QM31;
use aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_unmasked_terminal_value_compiled_v3;
use aspis_statement::state_only_poseidon::{successor_point, xor12_point};
use aspis_statement::{
    decode_asset_id_canonical, decode_digest_canonical, encode_atomic_payment_statement_v4,
    AtomicPaymentStatementV4, AtomicStatementError, SpendPublic, StateOnlyTerminalError,
    ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES, ATOMIC_PAYMENT_STATEMENT_VERSION,
    ATOMIC_PAYMENT_TREE_DEPTH,
};

pub const V5_ATOMIC_TERMINAL_SEMANTIC_LANES: usize = 16;
pub const V5_ATOMIC_TERMINAL_HCOPY_LANE: usize = 16;
pub const V5_ATOMIC_TERMINAL_COMPONENT_B_LANE: usize = 17;
pub const V5_ATOMIC_TERMINAL_COMPONENT_C_LANE: usize = 18;
pub const V5_ATOMIC_TERMINAL_LANES: usize = 19;
pub const V5_ATOMIC_TERMINAL_POINT_CLAIMS: usize = 3;
pub const V5_ATOMIC_TERMINAL_CLAIMS_PER_LANE: usize = 4;
pub const V5_ATOMIC_TERMINAL_POINT_COORDINATES: usize = 10;
pub const V5_ATOMIC_TERMINAL_POINT_BYTES: usize =
    V5_ATOMIC_TERMINAL_POINT_CLAIMS * V5_ATOMIC_TERMINAL_POINT_COORDINATES * 16;
pub const V5_ATOMIC_TERMINAL_CLAIM_BYTES: usize =
    V5_ATOMIC_TERMINAL_CLAIMS_PER_LANE * V5_ATOMIC_TERMINAL_LANES * 16;
pub const V5_ATOMIC_TERMINAL_STATEMENT_OFFSET: usize = 0;
pub const V5_ATOMIC_TERMINAL_LAMBDA_OFFSET: usize = ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES;
pub const V5_ATOMIC_TERMINAL_CHI_OFFSET: usize = V5_ATOMIC_TERMINAL_LAMBDA_OFFSET + 16;
pub const V5_ATOMIC_TERMINAL_THETA_OFFSET: usize = V5_ATOMIC_TERMINAL_CHI_OFFSET + 16;
pub const V5_ATOMIC_TERMINAL_ZEROCHECK_OFFSET: usize = V5_ATOMIC_TERMINAL_THETA_OFFSET + 16;
pub const V5_ATOMIC_TERMINAL_MU_OFFSET: usize =
    V5_ATOMIC_TERMINAL_ZEROCHECK_OFFSET + V5_ATOMIC_TERMINAL_POINT_COORDINATES * 16;
/// Additional fixed account material needed beyond the already-present v5
/// point table, claim table, eta, and terminal tuple.
pub const V5_ATOMIC_TERMINAL_CONTEXT_BYTES: usize = V5_ATOMIC_TERMINAL_MU_OFFSET + 16;

const LEGACY_COLUMNS: usize = 28;
const LEGACY_CLAIMS: usize = V5_ATOMIC_TERMINAL_POINT_CLAIMS * LEGACY_COLUMNS;
const LEGACY_MASK_ONLY_START: usize = 16;
const LEGACY_HCOPY_COLUMN: usize = 26;
const LEGACY_G_COLUMN: usize = 27;

const _: () = assert!(V5_ATOMIC_TERMINAL_LANES == 16 + 3);
const _: () = assert!(V5_ATOMIC_TERMINAL_POINT_BYTES == 480);
const _: () = assert!(V5_ATOMIC_TERMINAL_CLAIM_BYTES == 1_216);
const _: () = assert!(V5_ATOMIC_TERMINAL_CONTEXT_BYTES == 440);
const _: () = assert!(LEGACY_CLAIMS == 84);
const _: () = assert!(LEGACY_MASK_ONLY_START + 10 == LEGACY_HCOPY_COLUMN);
const _: () = assert!(LEGACY_HCOPY_COLUMN + 1 == LEGACY_G_COLUMN);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5AtomicTerminalChallenges {
    pub lambda: QM31,
    pub chi: QM31,
    pub theta: QM31,
    pub zerocheck_point: [QM31; V5_ATOMIC_TERMINAL_POINT_COORDINATES],
    pub mu: QM31,
    pub eta: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V5AtomicTerminalClaims {
    pub real: QM31,
    pub mask: QM31,
    pub masked: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedV5AtomicTerminal {
    pub real: QM31,
    pub mask: QM31,
    pub masked: QM31,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum V5AtomicTerminalError {
    WrongContextBytes { expected: usize, actual: usize },
    InvalidStatement,
    NonCanonicalContextField { field: usize },
    WrongPointBytes { expected: usize, actual: usize },
    WrongClaimBytes { expected: usize, actual: usize },
    NonCanonicalPoint { point: usize, coordinate: usize },
    NonCanonicalClaim { point: usize, lane: usize },
    OpeningPointMismatch { point: usize },
    Semantic(StateOnlyTerminalError),
    RealMismatch,
    MaskMismatch,
    MaskedMismatch,
}

impl From<StateOnlyTerminalError> for V5AtomicTerminalError {
    fn from(error: StateOnlyTerminalError) -> Self {
        Self::Semantic(error)
    }
}

fn decode_statement(bytes: &[u8]) -> Result<AtomicPaymentStatementV4, V5AtomicTerminalError> {
    if bytes.len() != ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES
        || bytes[0] != ATOMIC_PAYMENT_STATEMENT_VERSION
        || usize::from(bytes[1]) != ATOMIC_PAYMENT_TREE_DEPTH
        || bytes[2..8] != [0u8; 6]
    {
        return Err(V5AtomicTerminalError::InvalidStatement);
    }
    let digest = |start: usize| {
        decode_digest_canonical(bytes[start..start + 32].try_into().unwrap())
            .map_err(|_| V5AtomicTerminalError::InvalidStatement)
    };
    let statement = AtomicPaymentStatementV4 {
        pool: bytes[8..40].try_into().unwrap(),
        sequence: u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
        spend: SpendPublic {
            anchor: digest(48)?,
            nullifier: digest(80)?,
            output_commitment: digest(112)?,
            asset_id: decode_asset_id_canonical(u32::from_le_bytes(
                bytes[176..180].try_into().unwrap(),
            ))
            .map_err(|_| V5AtomicTerminalError::InvalidStatement)?,
            fee: u32::from_le_bytes(bytes[180..184].try_into().unwrap()),
        },
        output_anchor: digest(144)?,
        deployment_domain: bytes[184..216].try_into().unwrap(),
    };
    let encoded = encode_atomic_payment_statement_v4(&statement)
        .map_err(|_| V5AtomicTerminalError::InvalidStatement)?;
    if encoded.as_slice() != bytes {
        return Err(V5AtomicTerminalError::InvalidStatement);
    }
    Ok(statement)
}

fn decode_context_qm31(
    bytes: &[u8],
    offset: usize,
    field: usize,
) -> Result<QM31, V5AtomicTerminalError> {
    QM31::from_le_bytes(&bytes[offset..offset + 16])
        .ok_or(V5AtomicTerminalError::NonCanonicalContextField { field })
}

/// Decode the canonical atomic statement and the transcript-derived terminal
/// challenges carried by the isolated CU stress account. Production must
/// derive these challenges from the transcript; this decoder merely makes
/// the stress account byte-exact and canonical.
pub fn decode_v5_atomic_terminal_context(
    bytes: &[u8],
    eta: QM31,
) -> Result<(AtomicPaymentStatementV4, V5AtomicTerminalChallenges), V5AtomicTerminalError> {
    if bytes.len() != V5_ATOMIC_TERMINAL_CONTEXT_BYTES {
        return Err(V5AtomicTerminalError::WrongContextBytes {
            expected: V5_ATOMIC_TERMINAL_CONTEXT_BYTES,
            actual: bytes.len(),
        });
    }
    let statement = decode_statement(
        &bytes[V5_ATOMIC_TERMINAL_STATEMENT_OFFSET..V5_ATOMIC_TERMINAL_LAMBDA_OFFSET],
    )?;
    let lambda = decode_context_qm31(bytes, V5_ATOMIC_TERMINAL_LAMBDA_OFFSET, 0)?;
    let chi = decode_context_qm31(bytes, V5_ATOMIC_TERMINAL_CHI_OFFSET, 1)?;
    let theta = decode_context_qm31(bytes, V5_ATOMIC_TERMINAL_THETA_OFFSET, 2)?;
    let mut zerocheck_point = [QM31::ZERO; V5_ATOMIC_TERMINAL_POINT_COORDINATES];
    for (coordinate, output) in zerocheck_point.iter_mut().enumerate() {
        *output = decode_context_qm31(
            bytes,
            V5_ATOMIC_TERMINAL_ZEROCHECK_OFFSET + coordinate * 16,
            3 + coordinate,
        )?;
    }
    let mu = decode_context_qm31(bytes, V5_ATOMIC_TERMINAL_MU_OFFSET, 13)?;
    Ok((
        statement,
        V5AtomicTerminalChallenges {
            lambda,
            chi,
            theta,
            zerocheck_point,
            mu,
            eta,
        },
    ))
}

/// Host serializer for the canonical 440-byte terminal context.
#[cfg(not(target_os = "solana"))]
pub fn encode_v5_atomic_terminal_context(
    statement: &AtomicPaymentStatementV4,
    challenges: &V5AtomicTerminalChallenges,
) -> Result<[u8; V5_ATOMIC_TERMINAL_CONTEXT_BYTES], AtomicStatementError> {
    let mut bytes = [0u8; V5_ATOMIC_TERMINAL_CONTEXT_BYTES];
    bytes[..ATOMIC_PAYMENT_STATEMENT_PAYLOAD_BYTES]
        .copy_from_slice(&encode_atomic_payment_statement_v4(statement)?);
    challenges.lambda.write_le_bytes(
        &mut bytes[V5_ATOMIC_TERMINAL_LAMBDA_OFFSET..V5_ATOMIC_TERMINAL_CHI_OFFSET],
    );
    challenges
        .chi
        .write_le_bytes(&mut bytes[V5_ATOMIC_TERMINAL_CHI_OFFSET..V5_ATOMIC_TERMINAL_THETA_OFFSET]);
    challenges.theta.write_le_bytes(
        &mut bytes[V5_ATOMIC_TERMINAL_THETA_OFFSET..V5_ATOMIC_TERMINAL_ZEROCHECK_OFFSET],
    );
    for (coordinate, value) in challenges.zerocheck_point.iter().copied().enumerate() {
        let start = V5_ATOMIC_TERMINAL_ZEROCHECK_OFFSET + coordinate * 16;
        value.write_le_bytes(&mut bytes[start..start + 16]);
    }
    challenges
        .mu
        .write_le_bytes(&mut bytes[V5_ATOMIC_TERMINAL_MU_OFFSET..V5_ATOMIC_TERMINAL_CONTEXT_BYTES]);
    Ok(bytes)
}

fn decode_points(
    bytes: &[u8],
) -> Result<
    [[QM31; V5_ATOMIC_TERMINAL_POINT_COORDINATES]; V5_ATOMIC_TERMINAL_POINT_CLAIMS],
    V5AtomicTerminalError,
> {
    if bytes.len() != V5_ATOMIC_TERMINAL_POINT_BYTES {
        return Err(V5AtomicTerminalError::WrongPointBytes {
            expected: V5_ATOMIC_TERMINAL_POINT_BYTES,
            actual: bytes.len(),
        });
    }
    let mut points =
        [[QM31::ZERO; V5_ATOMIC_TERMINAL_POINT_COORDINATES]; V5_ATOMIC_TERMINAL_POINT_CLAIMS];
    for (point, coordinates) in points.iter_mut().enumerate() {
        for (coordinate, output) in coordinates.iter_mut().enumerate() {
            let value = point * V5_ATOMIC_TERMINAL_POINT_COORDINATES + coordinate;
            let start = value * 16;
            *output = QM31::from_le_bytes(&bytes[start..start + 16])
                .ok_or(V5AtomicTerminalError::NonCanonicalPoint { point, coordinate })?;
        }
    }
    Ok(points)
}

fn claim(bytes: &[u8], point: usize, lane: usize) -> Result<QM31, V5AtomicTerminalError> {
    let value = point * V5_ATOMIC_TERMINAL_LANES + lane;
    let start = value * 16;
    QM31::from_le_bytes(&bytes[start..start + 16])
        .ok_or(V5AtomicTerminalError::NonCanonicalClaim { point, lane })
}

/// Verify the unchanged atomic semantics against the authenticated v5 view.
///
/// `opening_point_bytes` is exactly the three point-major coordinate rows
/// `(z, successor(z), xor12(z))`. `point_major_claim_bytes` is exactly the
/// four-by-nineteen PCS table. The fourth Component-B claim is the terminal
/// mask opening already committed before `eta` by the surrounding protocol.
/// This function checks values, not commitment ordering; the caller remains
/// responsible for authenticating the table and deriving every challenge.
#[allow(clippy::too_many_arguments)]
pub fn verify_v5_atomic_terminal_from_bytes(
    statement: &AtomicPaymentStatementV4,
    opening_point_bytes: &[u8],
    point_major_claim_bytes: &[u8],
    challenges: &V5AtomicTerminalChallenges,
    claimed: V5AtomicTerminalClaims,
) -> Result<VerifiedV5AtomicTerminal, V5AtomicTerminalError> {
    if point_major_claim_bytes.len() != V5_ATOMIC_TERMINAL_CLAIM_BYTES {
        return Err(V5AtomicTerminalError::WrongClaimBytes {
            expected: V5_ATOMIC_TERMINAL_CLAIM_BYTES,
            actual: point_major_claim_bytes.len(),
        });
    }

    let points = decode_points(opening_point_bytes)?;
    if points[1] != successor_point(&points[0]) {
        return Err(V5AtomicTerminalError::OpeningPointMismatch { point: 1 });
    }
    if points[2] != xor12_point(&points[0]) {
        return Err(V5AtomicTerminalError::OpeningPointMismatch { point: 2 });
    }

    // The old mask-only and G slots stay zero and are deliberately consumed
    // only by the historical function's unused return values. Calling the
    // masked atomic-v3 wrapper here would silently reintroduce H/G/D-era
    // semantics and is therefore forbidden by construction.
    let mut legacy = [QM31::ZERO; LEGACY_CLAIMS];
    for point in 0..V5_ATOMIC_TERMINAL_POINT_CLAIMS {
        let legacy_base = point * LEGACY_COLUMNS;
        for lane in 0..V5_ATOMIC_TERMINAL_SEMANTIC_LANES {
            legacy[legacy_base + lane] = claim(point_major_claim_bytes, point, lane)?;
        }
        legacy[legacy_base + LEGACY_HCOPY_COLUMN] = claim(
            point_major_claim_bytes,
            point,
            V5_ATOMIC_TERMINAL_HCOPY_LANE,
        )?;
    }

    let real = atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
        statement,
        &legacy,
        &points[0],
        challenges.lambda,
        challenges.chi,
        challenges.theta,
        &challenges.zerocheck_point,
        challenges.mu,
    )?;
    if real != claimed.real {
        return Err(V5AtomicTerminalError::RealMismatch);
    }

    let mask = claim(
        point_major_claim_bytes,
        V5_ATOMIC_TERMINAL_CLAIMS_PER_LANE - 1,
        V5_ATOMIC_TERMINAL_COMPONENT_B_LANE,
    )?;
    if mask != claimed.mask {
        return Err(V5AtomicTerminalError::MaskMismatch);
    }
    let masked = mask.add(challenges.eta.mul(real));
    if masked != claimed.masked {
        return Err(V5AtomicTerminalError::MaskedMismatch);
    }

    Ok(VerifiedV5AtomicTerminal { real, mask, masked })
}

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::field::{CM31, M31, P};
    use aspis_statement::atomic_state_only_registry::build_atomic_state_only_copy_helper_v3;
    use aspis_statement::atomic_state_only_trace::{
        atomic_merkle_root_v3, build_atomic_state_only_trace_v3,
    };
    use aspis_statement::{
        derive_nullifier, derive_owner_key, multilinear_evaluate, multilinear_evaluate_qm31,
        note_commitment, output_commitment, Digest, MerklePath, SpendPublic, SpendWitness,
    };

    fn q(seed: u32) -> QM31 {
        let limb = |offset: u32| {
            M31(((u64::from(seed) * 1_003 + u64::from(offset)) % u64::from(P)) as u32)
        };
        QM31 {
            c0: CM31::new(limb(1), limb(3)),
            c1: CM31::new(limb(5), limb(7)),
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 17 * index as u32))
    }

    fn fixture() -> (AtomicPaymentStatementV4, SpendWitness) {
        let nullifier_key = digest(101);
        let input_salt = digest(301);
        let output_salt = digest(501);
        let output_owner_key = digest(701);
        let asset_id = M31(17);
        let merkle_path = MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        };
        let witness = SpendWitness {
            nullifier_key,
            input_salt,
            output_salt,
            output_owner_key,
            input_asset_id: asset_id,
            value: 1_000_000,
            value_out: 999_999,
            merkle_path,
        };
        let input = note_commitment(
            &derive_owner_key(&nullifier_key),
            witness.value,
            asset_id,
            &input_salt,
        );
        let output =
            output_commitment(&output_owner_key, witness.value_out, asset_id, &output_salt);
        let statement = AtomicPaymentStatementV4 {
            pool: [0x5a; 32],
            sequence: 73,
            spend: SpendPublic {
                anchor: atomic_merkle_root_v3(input, &witness.merkle_path).unwrap(),
                nullifier: derive_nullifier(&nullifier_key, &input_salt),
                output_commitment: output,
                asset_id,
                fee: 1,
            },
            output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path).unwrap(),
            deployment_domain: [0x5d; 32],
        };
        (statement, witness)
    }

    fn encode_points(
        points: &[[QM31; V5_ATOMIC_TERMINAL_POINT_COORDINATES]; V5_ATOMIC_TERMINAL_POINT_CLAIMS],
    ) -> [u8; V5_ATOMIC_TERMINAL_POINT_BYTES] {
        let mut bytes = [0u8; V5_ATOMIC_TERMINAL_POINT_BYTES];
        for (value, point) in points.iter().flatten().copied().enumerate() {
            point.write_le_bytes(&mut bytes[value * 16..value * 16 + 16]);
        }
        bytes
    }

    fn encode_claims(
        claims: &[[QM31; V5_ATOMIC_TERMINAL_LANES]; V5_ATOMIC_TERMINAL_CLAIMS_PER_LANE],
    ) -> [u8; V5_ATOMIC_TERMINAL_CLAIM_BYTES] {
        let mut bytes = [0u8; V5_ATOMIC_TERMINAL_CLAIM_BYTES];
        for (value, claim) in claims.iter().flatten().copied().enumerate() {
            claim.write_le_bytes(&mut bytes[value * 16..value * 16 + 16]);
        }
        bytes
    }

    #[test]
    fn honest_atomic_trace_zero_mask_specialisation_closes_v5_identity() {
        let (statement, witness) = fixture();
        let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
        let lambda = q(40_001);
        let chi = q(40_002);
        let hcopy = build_atomic_state_only_copy_helper_v3(&atomic.trace, lambda, chi).unwrap();
        let z = core::array::from_fn(|coordinate| q(41_000 + coordinate as u32));
        let points = [z, successor_point(&z), xor12_point(&z)];
        let mut claims =
            [[QM31::ZERO; V5_ATOMIC_TERMINAL_LANES]; V5_ATOMIC_TERMINAL_CLAIMS_PER_LANE];
        for (point, evaluation_point) in points.iter().enumerate() {
            for lane in 0..V5_ATOMIC_TERMINAL_SEMANTIC_LANES {
                claims[point][lane] =
                    multilinear_evaluate(&atomic.trace.c1[lane], evaluation_point).unwrap();
            }
            claims[point][V5_ATOMIC_TERMINAL_HCOPY_LANE] =
                multilinear_evaluate_qm31(&hcopy, evaluation_point).unwrap();
        }

        // Zero Component A/B/C masks are the algebraically honest v5 message
        // specialisation. They are intentionally not a hiding distribution.
        let challenges = V5AtomicTerminalChallenges {
            lambda,
            chi,
            theta: q(40_003),
            zerocheck_point: core::array::from_fn(|coordinate| q(42_000 + coordinate as u32)),
            mu: q(40_004),
            eta: q(40_005),
        };
        let point_bytes = encode_points(&points);
        let claim_bytes = encode_claims(&claims);

        let mut legacy = [QM31::ZERO; LEGACY_CLAIMS];
        for point in 0..V5_ATOMIC_TERMINAL_POINT_CLAIMS {
            for lane in 0..V5_ATOMIC_TERMINAL_SEMANTIC_LANES {
                legacy[point * LEGACY_COLUMNS + lane] = claims[point][lane];
            }
            legacy[point * LEGACY_COLUMNS + LEGACY_HCOPY_COLUMN] =
                claims[point][V5_ATOMIC_TERMINAL_HCOPY_LANE];
        }
        let real = atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
            &statement,
            &legacy,
            &z,
            challenges.lambda,
            challenges.chi,
            challenges.theta,
            &challenges.zerocheck_point,
            challenges.mu,
        )
        .unwrap();
        let mask = QM31::ZERO;
        let masked = mask.add(challenges.eta.mul(real));
        let verified = verify_v5_atomic_terminal_from_bytes(
            &statement,
            &point_bytes,
            &claim_bytes,
            &challenges,
            V5AtomicTerminalClaims { real, mask, masked },
        )
        .unwrap();
        assert_eq!(verified, VerifiedV5AtomicTerminal { real, mask, masked });
    }

    #[test]
    fn terminal_adapter_has_point_real_mask_and_masked_teeth() {
        let (statement, witness) = fixture();
        let atomic = build_atomic_state_only_trace_v3(&statement, &witness).unwrap();
        let lambda = q(50_001);
        let chi = q(50_002);
        let hcopy = build_atomic_state_only_copy_helper_v3(&atomic.trace, lambda, chi).unwrap();
        let z = core::array::from_fn(|coordinate| q(51_000 + coordinate as u32));
        let points = [z, successor_point(&z), xor12_point(&z)];
        let mut claims =
            [[QM31::ZERO; V5_ATOMIC_TERMINAL_LANES]; V5_ATOMIC_TERMINAL_CLAIMS_PER_LANE];
        for (point, evaluation_point) in points.iter().enumerate() {
            for lane in 0..V5_ATOMIC_TERMINAL_SEMANTIC_LANES {
                claims[point][lane] =
                    multilinear_evaluate(&atomic.trace.c1[lane], evaluation_point).unwrap();
            }
            claims[point][V5_ATOMIC_TERMINAL_HCOPY_LANE] =
                multilinear_evaluate_qm31(&hcopy, evaluation_point).unwrap();
        }
        claims[3][V5_ATOMIC_TERMINAL_COMPONENT_B_LANE] = q(50_006);
        claims[3][V5_ATOMIC_TERMINAL_COMPONENT_C_LANE] = q(50_007);
        let challenges = V5AtomicTerminalChallenges {
            lambda,
            chi,
            theta: q(50_003),
            zerocheck_point: core::array::from_fn(|coordinate| q(52_000 + coordinate as u32)),
            mu: q(50_004),
            eta: q(50_005),
        };
        let point_bytes = encode_points(&points);
        let claim_bytes = encode_claims(&claims);

        let mut legacy = [QM31::ZERO; LEGACY_CLAIMS];
        for point in 0..V5_ATOMIC_TERMINAL_POINT_CLAIMS {
            for lane in 0..V5_ATOMIC_TERMINAL_SEMANTIC_LANES {
                legacy[point * LEGACY_COLUMNS + lane] = claims[point][lane];
            }
            legacy[point * LEGACY_COLUMNS + LEGACY_HCOPY_COLUMN] =
                claims[point][V5_ATOMIC_TERMINAL_HCOPY_LANE];
        }
        let real = atomic_state_only_selected_unmasked_terminal_value_compiled_v3(
            &statement,
            &legacy,
            &z,
            challenges.lambda,
            challenges.chi,
            challenges.theta,
            &challenges.zerocheck_point,
            challenges.mu,
        )
        .unwrap();
        let mask = claims[3][V5_ATOMIC_TERMINAL_COMPONENT_B_LANE];
        let masked = mask.add(challenges.eta.mul(real));
        let claimed = V5AtomicTerminalClaims { real, mask, masked };
        verify_v5_atomic_terminal_from_bytes(
            &statement,
            &point_bytes,
            &claim_bytes,
            &challenges,
            claimed,
        )
        .unwrap();

        let mut bad_points = points;
        bad_points[1][0] = bad_points[1][0].add(QM31::ONE);
        assert_eq!(
            verify_v5_atomic_terminal_from_bytes(
                &statement,
                &encode_points(&bad_points),
                &claim_bytes,
                &challenges,
                claimed,
            ),
            Err(V5AtomicTerminalError::OpeningPointMismatch { point: 1 })
        );
        assert_eq!(
            verify_v5_atomic_terminal_from_bytes(
                &statement,
                &point_bytes,
                &claim_bytes,
                &challenges,
                V5AtomicTerminalClaims {
                    real: real.add(QM31::ONE),
                    ..claimed
                },
            ),
            Err(V5AtomicTerminalError::RealMismatch)
        );
        assert_eq!(
            verify_v5_atomic_terminal_from_bytes(
                &statement,
                &point_bytes,
                &claim_bytes,
                &challenges,
                V5AtomicTerminalClaims {
                    mask: mask.add(QM31::ONE),
                    ..claimed
                },
            ),
            Err(V5AtomicTerminalError::MaskMismatch)
        );
        assert_eq!(
            verify_v5_atomic_terminal_from_bytes(
                &statement,
                &point_bytes,
                &claim_bytes,
                &challenges,
                V5AtomicTerminalClaims {
                    masked: masked.add(QM31::ONE),
                    ..claimed
                },
            ),
            Err(V5AtomicTerminalError::MaskedMismatch)
        );
    }
}
