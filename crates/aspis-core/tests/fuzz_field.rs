//! Fuzz-style harness for field/encoding invariants (canonical M31/QM31
//! decoding and degenerate circle-point handling).
//!
//! Approach: proptest on the pinned stable toolchain, same rationale as
//! `fuzz_parser.rs` (cargo-fuzz would require nightly + libFuzzer).
//!
//! Invariants exercised:
//!  * `M31::from_le_bytes` accepts a 4-byte word iff it is canonical (`< P`),
//!    rejects every non-canonical word (`>= P`, including the exact modulus),
//!    and canonical decodes round-trip through `to_le_bytes`.
//!  * `CM31`/`QM31` decoding accepts a wire encoding iff *every* limb is
//!    canonical, and round-trips.
//!  * The circle-point maps never panic on arbitrary parameters, land on the
//!    unit circle when they succeed, and the OOD map rejects the whole CM31
//!    parameter subfield and the singular parameter with the defined errors.

use aspis_core::circle::{
    secure_circle_point_from_parameter, secure_ood_circle_point_from_parameter, CirclePointError,
};
use aspis_core::field::{CM31, M31, P, QM31};
use proptest::prelude::*;

fn cm31(a: u32, b: u32) -> CM31 {
    CM31::new(M31(a % P), M31(b % P))
}

fn qm31(limbs: [u32; 4]) -> QM31 {
    QM31 {
        c0: cm31(limbs[0], limbs[1]),
        c1: cm31(limbs[2], limbs[3]),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// M31 decoding is exactly canonical: Some iff value < P, and round-trips.
    #[test]
    fn m31_decode_is_canonical(value in any::<u32>()) {
        let bytes = value.to_le_bytes();
        match M31::from_le_bytes(bytes) {
            Some(elem) => {
                prop_assert!(value < P, "accepted a non-canonical M31 word {value:#x}");
                prop_assert_eq!(elem.to_le_bytes(), bytes, "canonical M31 did not round-trip");
            }
            None => {
                prop_assert!(value >= P, "rejected a canonical M31 word {value:#x}");
            }
        }
    }

    /// The exact modulus and everything above it is non-canonical.
    #[test]
    fn m31_rejects_non_canonical(excess in 0u32..=(u32::MAX - P)) {
        let value = P.wrapping_add(excess);
        prop_assert!(M31::from_le_bytes(value.to_le_bytes()).is_none());
    }

    /// CM31 accepts iff both limbs are canonical; round-trips when accepted.
    #[test]
    fn cm31_decode_is_canonical(a in any::<u32>(), b in any::<u32>()) {
        let mut bytes = [0u8; 8];
        bytes[0..4].copy_from_slice(&a.to_le_bytes());
        bytes[4..8].copy_from_slice(&b.to_le_bytes());
        match CM31::from_le_bytes(&bytes) {
            Some(elem) => {
                prop_assert!(a < P && b < P);
                let mut out = [0u8; 8];
                elem.write_le_bytes(&mut out);
                prop_assert_eq!(out, bytes);
            }
            None => prop_assert!(a >= P || b >= P),
        }
    }

    /// QM31 accepts iff all four limbs are canonical; round-trips when accepted.
    #[test]
    fn qm31_decode_is_canonical(limbs in any::<[u32; 4]>()) {
        let mut bytes = [0u8; 16];
        for (i, limb) in limbs.iter().enumerate() {
            bytes[i * 4..i * 4 + 4].copy_from_slice(&limb.to_le_bytes());
        }
        match QM31::from_le_bytes(&bytes) {
            Some(elem) => {
                prop_assert!(limbs.iter().all(|&l| l < P));
                let mut out = [0u8; 16];
                elem.write_le_bytes(&mut out);
                prop_assert_eq!(out, bytes);
            }
            None => prop_assert!(limbs.iter().any(|&l| l >= P)),
        }
    }

    /// Poison one QM31 limb to exactly P: decoding must reject.
    #[test]
    fn qm31_rejects_single_non_canonical_limb(
        mut limbs in any::<[u32; 4]>(),
        poison in 0usize..4,
    ) {
        for l in limbs.iter_mut() {
            *l %= P;
        }
        limbs[poison] = P; // exactly the modulus: non-canonical
        let mut bytes = [0u8; 16];
        for (i, limb) in limbs.iter().enumerate() {
            bytes[i * 4..i * 4 + 4].copy_from_slice(&limb.to_le_bytes());
        }
        prop_assert!(QM31::from_le_bytes(&bytes).is_none());
    }

    /// The circle parameterization never panics and lands on the unit circle.
    #[test]
    fn circle_point_is_non_panicking_and_on_circle(limbs in any::<[u32; 4]>()) {
        let parameter = qm31(limbs);
        if let Ok(point) = secure_circle_point_from_parameter(parameter) {
            prop_assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
        }
        // The OOD variant never panics and agrees with the plain map on success.
        if let Ok(point) = secure_ood_circle_point_from_parameter(parameter) {
            prop_assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
        }
    }

    /// Degenerate circle points: any parameter drawn from the CM31 subfield
    /// (c1 == 0) is rejected canonically by the OOD policy — either as the
    /// singular parameter (t = ±i) or as a CM31-subfield parameter.
    #[test]
    fn ood_rejects_cm31_subfield_parameters(a in any::<u32>(), b in any::<u32>()) {
        let parameter = QM31::from_cm31(cm31(a, b));
        match secure_ood_circle_point_from_parameter(parameter) {
            Err(CirclePointError::ParameterInCm31Subfield)
            | Err(CirclePointError::SingularParameter) => {}
            other => prop_assert!(
                false,
                "CM31-subfield parameter was not rejected canonically: {other:?}"
            ),
        }
    }
}

/// The two circle singularities `t = ±i` are reported as the defined singular
/// error rather than panicking through the inverse.
#[test]
fn circle_singularities_are_defined_errors() {
    let plus_i = QM31::from_cm31(CM31::new(M31::ZERO, M31::ONE));
    let minus_i = QM31::from_cm31(CM31::new(M31::ZERO, M31(P - 1)));
    for singular in [plus_i, minus_i] {
        assert_eq!(
            secure_circle_point_from_parameter(singular),
            Err(CirclePointError::SingularParameter)
        );
        assert_eq!(
            secure_ood_circle_point_from_parameter(singular),
            Err(CirclePointError::SingularParameter)
        );
    }
}
