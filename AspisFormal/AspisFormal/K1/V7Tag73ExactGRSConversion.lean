import AspisFormal.K1.V7Tag73ExactOneFoldEncoderBinding

/-!
# Exact V7 circle/line to generalized Reed--Solomon conversion

This file discharges the coding-theoretic conversion boundary for the two
released Tag-73 one-fold encoders.  It uses the exact QM31 tower, the exact
bit-reversed log-20 circle order, and the exact bit-reversed log-18 line order.
No decoding theorem is assumed here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactGRSConversion

open Polynomial
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5FriCircleEncoderDistance
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV7ExactOneFoldDomains

noncomputable section

private theorem qm31Exact_two_ne_zero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact 0 := by
    simpa only [map_ofNat, map_zero] using equalZero
  have baseEqual :=
    FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31Exact_two_ne_zero⟩

/-! ## Final `256 -> 2^18` line code -/

/-- The exact released final line encoder is a dimension-256 GRS code on the
stored bit-reversed log-18 points, with all column multipliers equal to one. -/
noncomputable def exactFinalGRSConversion :
    ExactGRSConversion 256 255 exactFinalEncoder where
  messageCoordinates := Equiv.refl _
  points := fun index =>
    algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
      (storedFirstLineX18 index)
  multipliers := fun _ => 1
  messagePolynomial := naturalCoefficientPolynomial
  points_injective := by
    intro left right equal
    apply storedFirstLineX18_injective
    exact FaithfulSMul.algebraMap_injective
      (ZMod AspisCircleGroupOrder.P) QM31Exact equal
  multipliers_ne_zero := fun _ => one_ne_zero
  messagePolynomial_injective := naturalCoefficientPolynomial_injective
  messagePolynomial_degree_le := by
    intro message
    exact naturalCoefficientPolynomial_natDegree_le (by norm_num) message
  coordinate_identity := by
    intro message index
    simp only [exactFinalEncoder, exactFinalLinear_apply,
      generalizedReedSolomonEncode, one_mul]

theorem exactFinalEncoder_eq_grs (message : FinalMessage QM31Exact) :
    exactFinalEncoder message = exactFinalGRSConversion.grsEncoder message :=
  exactFinalGRSConversion.releasedEncoder_eq_grsEncoder message

theorem exactFinalAgreementCount_eq_grs
    (received : FinalWord QM31Exact) (message : FinalMessage QM31Exact) :
    agreementCount received (exactFinalEncoder message) =
      agreementCount received (exactFinalGRSConversion.grsEncoder message) :=
  exactFinalGRSConversion.agreementCount_eq received message

theorem exactFinalThreshold_transport
    (received : FinalWord QM31Exact) (message : FinalMessage QM31Exact) :
    closeAtLeast finalAgreementThreshold exactFinalEncoder received message ↔
      closeAtLeast finalAgreementThreshold exactFinalGRSConversion.grsEncoder
        received message :=
  exactFinalGRSConversion.closeAtLeast_iff finalAgreementThreshold received
    message

/-- The final natural-basis map covers every polynomial of degree at most
255, so this instance is the full dimension-256 GRS code, not merely a
subcode. -/
theorem exactFinalMessagePolynomial_complete
    (polynomial : QM31Exact[X]) (degree : polynomial.natDegree ≤ 255) :
    ∃ message : FinalMessage QM31Exact,
      exactFinalGRSConversion.messagePolynomial message = polynomial := by
  exact naturalCoefficientPolynomial_complete (by norm_num) polynomial
    (by simpa using degree)

theorem exactFinal9558_transport
    (received : FinalWord QM31Exact) (message : FinalMessage QM31Exact) :
    closeAtLeast 9558 exactFinalEncoder received message ↔
      closeAtLeast 9558 exactFinalGRSConversion.grsEncoder received message := by
  simpa only [finalAgreementThreshold] using
    exactFinalThreshold_transport received message

/-! ## Initial `1024 -> 2^20` circle code -/

/-- The release-specific stereographic numerator from the existing exact
circle realization.  It clears 512 powers of `1+t²`, has degree at most
1024, and is injective on the released 1024-dimensional message subspace. -/
noncomputable def exactCircleGRSPolynomial
    (message : InitialMessage QM31Exact) : QM31Exact[X] :=
  circleNumerator
    (exactInitialEncoderCircleRealization.p0 message)
    (exactInitialEncoderCircleRealization.p1 message)

/-- Exact stereographic evaluation point in the deployed stored log-20
coordinate order. -/
def exactCircleGRSPoint (index : Fin 1048576) : QM31Exact :=
  algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
    ((exactInitialEncoderCircleRealization.point index).1.2 /
      (1 + AspisCircleGroupOrder.X
        (exactInitialEncoderCircleRealization.point index)))

@[simp] theorem exactCircleGRSPolynomial_eq_released
    (message : InitialMessage QM31Exact) :
    exactCircleGRSPolynomial message =
      circleNumerator (initialP0 message) (initialP1 message) := rfl

@[simp] theorem exactCircleGRSPoint_eq_stored (index : Fin 1048576) :
    exactCircleGRSPoint index =
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        ((storedInitialCirclePoint20 index).1.2 /
          (1 + AspisCircleGroupOrder.X
            (storedInitialCirclePoint20 index))) := rfl

/-- Nonzero GRS column multiplier obtained by undoing the 512 cleared
stereographic denominator powers. -/
def exactCircleGRSMultiplier (index : Fin 1048576) : QM31Exact :=
  ((1 + exactCircleGRSPoint index ^ 2) ^ 512)⁻¹

theorem exactCircleGRSPoint_injective :
    Function.Injective exactCircleGRSPoint :=
  exactInitialEncoderCircleRealization.parameter_injective

private theorem exactCircleDenominator_ne_zero (index : Fin 1048576) :
    1 + exactCircleGRSPoint index ^ 2 ≠ 0 := by
  let parameter : M31Exact :=
    (exactInitialEncoderCircleRealization.point index).1.2 /
      (1 + AspisCircleGroupOrder.X
        (exactInitialEncoderCircleRealization.point index))
  have pointEq : exactCircleGRSPoint index =
      algebraMap M31Exact QM31Exact parameter := by
    rfl
  rw [pointEq]
  intro zero
  apply m31_neg_one_not_isSquare
  refine ⟨parameter, ?_⟩
  have mapped : algebraMap M31Exact QM31Exact (1 + parameter ^ 2) = 0 := by
    simpa only [map_add, map_one, map_pow, map_zero] using zero
  have base : 1 + parameter ^ 2 = 0 :=
    FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  have square : parameter ^ 2 = -1 := by
    linear_combination base
  simpa only [pow_two] using square.symm

theorem exactCircleGRSMultiplier_ne_zero (index : Fin 1048576) :
    exactCircleGRSMultiplier index ≠ 0 := by
  unfold exactCircleGRSMultiplier
  exact inv_ne_zero (pow_ne_zero 512 (exactCircleDenominator_ne_zero index))

theorem exactCircleGRSPolynomial_degree_le
    (message : InitialMessage QM31Exact) :
    (exactCircleGRSPolynomial message).natDegree ≤ 1024 := by
  exact circleNumerator_natDegree_le _ _

theorem exactCircleGRSPolynomial_injective :
    Function.Injective exactCircleGRSPolynomial :=
  exactInitialEncoderCircleRealization.numerator_injective

theorem exactInitialEncoder_coordinate_grs
    (message : InitialMessage QM31Exact) (index : Fin 1048576) :
    exactInitialEncoder message index =
      generalizedReedSolomonEncode exactCircleGRSPoint
        exactCircleGRSMultiplier (exactCircleGRSPolynomial message) index := by
  unfold generalizedReedSolomonEncode exactCircleGRSMultiplier
  unfold exactCircleGRSPolynomial exactCircleGRSPoint
  have denominatorPowerNonzero :
      (1 +
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact)
            ((exactInitialEncoderCircleRealization.point index).1.2 /
              (1 + AspisCircleGroupOrder.X
                (exactInitialEncoderCircleRealization.point index))) ^ 2) ^
        512 ≠ 0 := by
    simpa only [exactCircleGRSPoint] using
      pow_ne_zero 512 (exactCircleDenominator_ne_zero index)
  rw [exactInitialEncoderCircleRealization.encoder_numerator_eval]
  rw [← mul_assoc, inv_mul_cancel₀ denominatorPowerNonzero, one_mul]

/-- The exact released initial circle encoder is a 1024-dimensional subcode
of the degree-at-most-1024 ambient GRS code after the explicit stereographic
message transform and nonzero coordinate multipliers above.  Its GRS
coordinates remain in the released bit-reversed order, so the coordinate
permutation is the identity. -/
noncomputable def exactInitialGRSConversion :
    ExactGRSConversion 1024 1024 exactInitialEncoder where
  messageCoordinates := Equiv.refl _
  points := exactCircleGRSPoint
  multipliers := exactCircleGRSMultiplier
  messagePolynomial := exactCircleGRSPolynomial
  points_injective := exactCircleGRSPoint_injective
  multipliers_ne_zero := exactCircleGRSMultiplier_ne_zero
  messagePolynomial_injective := exactCircleGRSPolynomial_injective
  messagePolynomial_degree_le := exactCircleGRSPolynomial_degree_le
  coordinate_identity := exactInitialEncoder_coordinate_grs

theorem exactInitialEncoder_eq_grs (message : InitialMessage QM31Exact) :
    exactInitialEncoder message =
      exactInitialGRSConversion.grsEncoder message :=
  exactInitialGRSConversion.releasedEncoder_eq_grsEncoder message

theorem exactInitialAgreementCount_eq_grs
    (received : InitialWord QM31Exact) (message : InitialMessage QM31Exact) :
    agreementCount received (exactInitialEncoder message) =
      agreementCount received (exactInitialGRSConversion.grsEncoder message) :=
  exactInitialGRSConversion.agreementCount_eq received message

theorem exactInitialThreshold_transport
    (received : InitialWord QM31Exact) (message : InitialMessage QM31Exact) :
    closeAtLeast initialAgreementThreshold exactInitialEncoder received message ↔
      closeAtLeast initialAgreementThreshold
        exactInitialGRSConversion.grsEncoder received message :=
  exactInitialGRSConversion.closeAtLeast_iff initialAgreementThreshold received
    message

theorem exactInitial38230_transport
    (received : InitialWord QM31Exact) (message : InitialMessage QM31Exact) :
    closeAtLeast 38230 exactInitialEncoder received message ↔
      closeAtLeast 38230 exactInitialGRSConversion.grsEncoder received
        message := by
  simpa only [initialAgreementThreshold] using
    exactInitialThreshold_transport received message

#print axioms exactFinalGRSConversion
#print axioms exactFinalEncoder_eq_grs
#print axioms exactFinalAgreementCount_eq_grs
#print axioms exactFinalThreshold_transport
#print axioms exactFinalMessagePolynomial_complete
#print axioms exactFinal9558_transport
#print axioms exactCircleGRSPoint_injective
#print axioms exactCircleGRSMultiplier_ne_zero
#print axioms exactCircleGRSPolynomial_degree_le
#print axioms exactCircleGRSPolynomial_injective
#print axioms exactInitialEncoder_coordinate_grs
#print axioms exactInitialGRSConversion
#print axioms exactInitialEncoder_eq_grs
#print axioms exactInitialAgreementCount_eq_grs
#print axioms exactInitialThreshold_transport
#print axioms exactInitial38230_transport

end

end AspisK1.V7Tag73ExactGRSConversion
