//! Secure-field circle-point math for the candidate M31 circle PCS.
//!
//! This module is arithmetic and sampling policy only. It does not select a
//! proof version, alter the production transcript schedule, or close the
//! circle-FRI soundness transport.

use crate::field::{CM31, QM31};

/// A point `(x, y)` on `x^2 + y^2 = 1` over QM31.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SecureCirclePoint {
    pub x: QM31,
    pub y: QM31,
}

/// Rejection reasons for the rational parameterization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CirclePointError {
    /// `1 + t^2 = 0`, so the rational map has no finite value.
    SingularParameter,
    /// OOD policy rejects the whole CM31 parameter subfield. This is stronger
    /// than merely excluding the M31 circle domain and matches the existing
    /// line-point policy of sampling from `QM31 \ CM31`.
    ParameterInCm31Subfield,
}

/// Apply the rational circle parameterization
///
/// `x = (1 - t^2)/(1 + t^2), y = 2t/(1 + t^2)`.
///
/// This pure algebra helper accepts parameters from any subfield, but returns
/// an explicit error when the denominator is zero. It never calls the
/// panicking inverse API.
pub fn secure_circle_point_from_parameter(
    parameter: QM31,
) -> Result<SecureCirclePoint, CirclePointError> {
    let square = parameter.square();
    let inverse_denominator = QM31::ONE
        .add(square)
        .try_inv()
        .ok_or(CirclePointError::SingularParameter)?;
    Ok(SecureCirclePoint {
        x: QM31::ONE.sub(square).mul(inverse_denominator),
        y: parameter.add(parameter).mul(inverse_denominator),
    })
}

/// Apply the same rational map under Aspis's layer-zero OOD policy.
///
/// The finite rational map is injective with inverse `t = y/(1+x)` and never
/// reaches `x = -1`. Rejecting `t in CM31` therefore guarantees that the
/// resulting point cannot have both coordinates in CM31. In particular it is
/// outside the M31 circle evaluation domain. Later line layers do not use
/// this map; they retain the exact-uniform `QM31 \ CM31` scalar sampler.
pub fn secure_ood_circle_point_from_parameter(
    parameter: QM31,
) -> Result<SecureCirclePoint, CirclePointError> {
    // Check the singularity first so `t = ±i` has the precise algebraic error
    // even though those two roots also lie in CM31.
    let point = secure_circle_point_from_parameter(parameter)?;
    if parameter.c1 == CM31::ZERO {
        return Err(CirclePointError::ParameterInCm31Subfield);
    }
    Ok(point)
}

/// Circle/line basis map `pi(x) = 2x^2 - 1`.
#[inline(always)]
pub fn double_x(x: QM31) -> QM31 {
    let square = x.square();
    square.add(square).sub(QM31::ONE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{M31, P};

    fn q(values: [u32; 4]) -> QM31 {
        QM31 {
            c0: CM31::new(M31(values[0]), M31(values[1])),
            c1: CM31::new(M31(values[2]), M31(values[3])),
        }
    }

    #[test]
    fn rational_map_is_on_circle_and_non_panicking() {
        for seed in 1..=32u32 {
            let parameter = q([seed * 17 % P, seed * 31 % P, seed * 43 % P, seed * 71 % P]);
            let point = secure_circle_point_from_parameter(parameter).unwrap();
            assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
        }
    }

    #[test]
    fn singular_denominator_is_an_explicit_error() {
        let i = QM31::from_cm31(CM31::new(M31::ZERO, M31::ONE));
        assert_eq!(
            secure_circle_point_from_parameter(i),
            Err(CirclePointError::SingularParameter)
        );
        assert_eq!(
            secure_ood_circle_point_from_parameter(i),
            Err(CirclePointError::SingularParameter)
        );
    }

    #[test]
    fn ood_policy_rejects_cm31_and_accepts_secure_parameters() {
        let cm31_parameter = QM31::from_cm31(CM31::new(M31(17), M31(29)));
        assert_eq!(
            secure_ood_circle_point_from_parameter(cm31_parameter),
            Err(CirclePointError::ParameterInCm31Subfield)
        );

        let point = secure_ood_circle_point_from_parameter(q([17, 29, 43, 71])).unwrap();
        assert!(point.x.c1 != CM31::ZERO || point.y.c1 != CM31::ZERO);
        assert_eq!(point.x.square().add(point.y.square()), QM31::ONE);
    }
}
