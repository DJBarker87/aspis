import AspisFormal.K1.V7ExactCorrelatedAgreementInterpolation
import AspisFormal.V6PublishedTheoremInterfaces

/-!
# Exact V7 correlated agreement

This module closes the coding-theory correlated-agreement boundary for the
two exact released V7 encoders.  The released initial code is handled as its
actual 1024-dimensional linear subcode of the ambient maximum-degree-1024
GRS code; it is never enlarged to the full ambient polynomial space.
-/

set_option autoImplicit false

namespace AspisK1.V7ExactCorrelatedAgreement

open scoped BigOperators
open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7Tag73ExactMultiplicityThreeGS
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV6Width29CorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6PublishedTheoremInterfaces

noncomputable section

private theorem qm31ExactTwoNeZero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact 0 := by
    simpa only [map_ofNat, map_zero] using equalZero
  have baseEqual :=
    FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31ExactTwoNeZero⟩

/-! ## Exact released-code linear closure -/

private theorem naturalCoefficientPolynomial_eval_add
    {n : Nat} (positive : 0 < n) (left right : Fin n → QM31Exact)
    (x : QM31Exact) :
    (naturalCoefficientPolynomial (left + right)).eval x =
      (naturalCoefficientPolynomial left).eval x +
        (naturalCoefficientPolynomial right).eval x := by
  rw [naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem naturalCoefficientPolynomial_eval_smul
    {n : Nat} (positive : 0 < n) (scalar : QM31Exact)
    (coefficients : Fin n → QM31Exact) (x : QM31Exact) :
    (naturalCoefficientPolynomial (scalar • coefficients)).eval x =
      scalar * (naturalCoefficientPolynomial coefficients).eval x := by
  rw [naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem initialP0_eval_add
    (left right : InitialMessage QM31Exact) (x : QM31Exact) :
    (initialP0 (left + right)).eval x =
      (initialP0 left).eval x + (initialP0 right).eval x := by
  unfold initialP0
  have coordinates :
      evenCoefficients (n := 512) (left + right) =
        evenCoefficients (n := 512) left +
          evenCoefficients (n := 512) right := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_add (by norm_num) _ _ x

private theorem initialP1_eval_add
    (left right : InitialMessage QM31Exact) (x : QM31Exact) :
    (initialP1 (left + right)).eval x =
      (initialP1 left).eval x + (initialP1 right).eval x := by
  unfold initialP1
  have coordinates :
      oddCoefficients (n := 512) (left + right) =
        oddCoefficients (n := 512) left +
          oddCoefficients (n := 512) right := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_add (by norm_num) _ _ x

private theorem initialP0_eval_smul
    (scalar : QM31Exact) (message : InitialMessage QM31Exact)
    (x : QM31Exact) :
    (initialP0 (scalar • message)).eval x =
      scalar * (initialP0 message).eval x := by
  unfold initialP0
  have coordinates :
      evenCoefficients (n := 512) (scalar • message) =
        scalar • evenCoefficients (n := 512) message := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_smul (by norm_num) scalar _ x

private theorem initialP1_eval_smul
    (scalar : QM31Exact) (message : InitialMessage QM31Exact)
    (x : QM31Exact) :
    (initialP1 (scalar • message)).eval x =
      scalar * (initialP1 message).eval x := by
  unfold initialP1
  have coordinates :
      oddCoefficients (n := 512) (scalar • message) =
        scalar • oddCoefficients (n := 512) message := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_smul (by norm_num) scalar _ x

/-- The exact released initial circle encoder, packaged as a QM31-linear map.
This proves closure of the actual 1024-coordinate message image, not of the
larger ambient degree-at-most-1024 polynomial space. -/
noncomputable def exactInitialLinear :
    InitialMessage QM31Exact →ₗ[QM31Exact] InitialWord QM31Exact where
  toFun := exactInitialEncoder
  map_add' := by
    intro left right
    funext index
    simp only [exactInitialEncoder]
    rw [initialP0_eval_add, initialP1_eval_add]
    simp only [Pi.add_apply, exactInitialEncoder]
    ring
  map_smul' := by
    intro scalar message
    funext index
    simp only [exactInitialEncoder]
    rw [initialP0_eval_smul, initialP1_eval_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      exactInitialEncoder]
    ring

@[simp] theorem exactInitialLinear_apply
    (message : InitialMessage QM31Exact) :
    exactInitialLinear message = exactInitialEncoder message := rfl

theorem exactInitialEncoder_add
    (left right : InitialMessage QM31Exact) :
    exactInitialEncoder (left + right) =
      exactInitialEncoder left + exactInitialEncoder right :=
  exactInitialLinear.map_add left right

theorem exactInitialEncoder_smul
    (scalar : QM31Exact) (message : InitialMessage QM31Exact) :
    exactInitialEncoder (scalar • message) =
      scalar • exactInitialEncoder message :=
  exactInitialLinear.map_smul scalar message

/-- The final released line encoder already is the existing exact linear map. -/
theorem exactFinalEncoder_add
    (left right : FinalMessage QM31Exact) :
    exactFinalEncoder (left + right) =
      exactFinalEncoder left + exactFinalEncoder right :=
  exactFinalLinear.map_add left right

theorem exactFinalEncoder_smul
    (scalar : QM31Exact) (message : FinalMessage QM31Exact) :
    exactFinalEncoder (scalar • message) =
      scalar • exactFinalEncoder message :=
  exactFinalLinear.map_smul scalar message

/-! ## Scalar-power curves remain in the exact released images -/

/-- The actual initial message on the scalar-power curve.  This is a message
of the released `Fin 1024 -> QM31Exact` type, not an ambient GRS polynomial. -/
def exactInitialMessageCurve
    (components : Fin 29 → InitialMessage QM31Exact) (gamma : QM31Exact) :
    InitialMessage QM31Exact :=
  ∑ lane, gamma ^ lane.1 • components lane

/-- The actual final message on the degree-three scalar-power curve. -/
def exactFinalMessageCurve
    (components : Fin 4 → FinalMessage QM31Exact) (z : QM31Exact) :
    FinalMessage QM31Exact :=
  ∑ lane, z ^ lane.1 • components lane

@[simp] theorem exactInitialMessageCurve_apply
    (components : Fin 29 → InitialMessage QM31Exact) (gamma : QM31Exact)
    (coefficient : Fin 1024) :
    exactInitialMessageCurve components gamma coefficient =
      width29Batch (fun lane => components lane coefficient) gamma := by
  simp only [exactInitialMessageCurve, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, width29Batch]
  apply Finset.sum_congr rfl
  intro lane _
  ring

@[simp] theorem exactFinalMessageCurve_apply
    (components : Fin 4 → FinalMessage QM31Exact) (z : QM31Exact)
    (coefficient : Fin 256) :
    exactFinalMessageCurve components z coefficient =
      AspisV5FunctionalBatching.batchedDiscrepancy
        (fun lane => components lane coefficient) z := by
  rw [exactFinalMessageCurve, Finset.sum_apply, Fin.sum_univ_four]
  simp only [Pi.smul_apply, smul_eq_mul,
    AspisV5FunctionalBatching.batchedDiscrepancy]
  norm_num
  ring

/-- Exact initial closure: encoding the released message curve is pointwise
the width-29 curve through the encoded released component messages. -/
theorem exactInitialEncoder_messageCurve
    (components : Fin 29 → InitialMessage QM31Exact) (gamma : QM31Exact) :
    exactInitialEncoder (exactInitialMessageCurve components gamma) =
      fun index => width29CurveValue
        (fun lane => exactInitialEncoder (components lane)) gamma index := by
  change exactInitialLinear (exactInitialMessageCurve components gamma) = _
  rw [exactInitialMessageCurve, map_sum]
  simp_rw [map_smul]
  funext index
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    width29CurveValue, width29Batch,
    exactInitialLinear_apply]
  apply Finset.sum_congr rfl
  intro lane _
  ring

/-- Exact final closure for the released degree-three message curve. -/
theorem exactFinalEncoder_messageCurve
    (components : Fin 4 → FinalMessage QM31Exact) (z : QM31Exact) :
    exactFinalEncoder (exactFinalMessageCurve components z) =
      fun index => curveValue
        (fun lane => exactFinalEncoder (components lane)) z index := by
  change exactFinalLinear (exactFinalMessageCurve components z) = _
  rw [exactFinalMessageCurve, map_sum]
  simp_rw [map_smul]
  funext index
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    curveValue,
    AspisV5FunctionalBatching.batchedDiscrepancy, Fin.sum_univ_four,
    exactFinalEncoder]
  norm_num
  ring

/-! ## Exact symbolic curve interpolants -/

/-- Divide every initial received lane by the exact nonzero GRS column
multiplier.  This is the lane-wise form of `exactInitialNormalizedReceived`;
it keeps the trivariate interpolation problem in ordinary polynomial-
evaluation coordinates. -/
def exactInitialNormalizedLanes
    (lanes : Fin 29 → InitialWord QM31Exact) :
    Fin 29 → Fin 1048576 → QM31Exact := fun lane index =>
  (exactInitialGRSConversion.multipliers index)⁻¹ * lanes lane index

@[simp] theorem exactInitialNormalizedLanes_curve
    (lanes : Fin 29 → InitialWord QM31Exact) (gamma : QM31Exact)
    (index : Fin 1048576) :
    (receivedCurvePolynomial (exactInitialNormalizedLanes lanes) index).eval
        gamma =
      exactInitialNormalizedReceived
        (fun coordinate => width29CurveValue lanes gamma coordinate) index := by
  simp only [receivedCurvePolynomial_eval, exactInitialNormalizedLanes,
    exactInitialNormalizedReceived, width29CurveValue, width29Batch]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lane _
  ring

@[simp] theorem exactFinalLanes_curve
    (lanes : Fin 4 → FinalWord QM31Exact) (z : QM31Exact)
    (index : Fin 262144) :
    (receivedCurvePolynomial lanes index).eval z =
      curveValue lanes z index := by
  rw [receivedCurvePolynomial_eval, Fin.sum_univ_four]
  simp only [curveValue,
    AspisV5FunctionalBatching.batchedDiscrepancy]
  norm_num

/-- The exact initial width-29 family has a nonzero symbolic
multiplicity-three interpolant.  Candidate messages have not been fixed here:
the six Hasse constraints hold identically in the challenge variable. -/
theorem exists_exactInitialCurveInterpolation
    (lanes : Fin 29 → InitialWord QM31Exact) :
    ∃ coefficients :
        CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
          initialCurveZBound → QM31Exact,
      coefficients ≠ 0 ∧
        curveInterpolationMap exactInitialGRSConversion.points
          (exactInitialNormalizedLanes lanes) coefficients = 0 := by
  apply exists_nonzero_curveInterpolationKernel
  exact exactInitialCurveInterpolationBudget.2.2

/-- The exact final degree-three family has a nonzero symbolic
multiplicity-three interpolant over the released `2^18` line domain. -/
theorem exists_exactFinalCurveInterpolation
    (lanes : Fin 4 → FinalWord QM31Exact) :
    ∃ coefficients :
        CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
          finalCurveZBound → QM31Exact,
      coefficients ≠ 0 ∧
        curveInterpolationMap exactFinalGRSConversion.points lanes
          coefficients = 0 := by
  apply exists_nonzero_curveInterpolationKernel
  exact exactFinalCurveInterpolationBudget.2.2

/-! ## Every challenge-dependent close candidate is a specialized root -/

-- Large dependent `Fin` indices make elaboration of the exact specialization
-- substantially more expensive than the underlying symbolic proof.
set_option maxHeartbeats 1000000 in
/- A final candidate selected independently at challenge `z` is a root of
the one symbolic interpolant specialized at `z`.  The proof uses only that
challenge's support; no candidate is fixed before `z`. -/
theorem exactFinalValidCandidate_substitute_eq_zero
    (lanes : Fin 4 → FinalWord QM31Exact)
    (strategy : ProximateStrategy QM31Exact (Fin 262144)
      (FinalMessage QM31Exact))
    (coefficients :
      CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
        finalCurveZBound → QM31Exact)
    (kernel : curveInterpolationMap exactFinalGRSConversion.points lanes
      coefficients = 0)
    (z : QM31Exact)
    (valid : ValidResponse exactFinalEncoder 9557 lanes strategy z) :
    interpolationSubstitute
        (specializeCurveCoefficients (by norm_num [finalCurveXBound,
          finalCurveYRows]) coefficients z)
        (exactFinalGRSConversion.messagePolynomial
          (strategy.candidate z)) = 0 := by
  let specialized := specializeCurveCoefficients (by
    norm_num [finalCurveXBound, finalCurveYRows]) coefficients z
  have specializedKernel :
      interpolationMap exactFinalGRSConversion.points
        (fun index => curveValue lanes z index) specialized = 0 := by
    have symbolic := specializeCurveCoefficients_mem_kernel
      (by norm_num [finalCurveZBound])
      (by norm_num [finalCurveXBound, finalCurveYRows])
      exactFinalGRSConversion.points lanes coefficients kernel z
    simpa only [exactFinalLanes_curve] using symbolic
  apply interpolationSubstitute_eq_zero_of_agreement (threshold := 9558)
    exactFinalGRSConversion.points (fun index => curveValue lanes z index)
    exactFinalGRSConversion.points_injective specialized specializedKernel
    (by norm_num [finalCurveXBound, finalCurveYRows])
    (by norm_num [finalCurveXBound])
    (exactFinalGRSConversion.messagePolynomial (strategy.candidate z))
    (exactFinalGRSConversion.messagePolynomial_degree_le
      (strategy.candidate z))
  have supportSubset : strategy.support z ⊆
      polynomialAgreementSet exactFinalGRSConversion.points
        (fun index => curveValue lanes z index)
        (exactFinalGRSConversion.messagePolynomial
          (strategy.candidate z)) := by
    intro index indexMem
    rw [mem_polynomialAgreementSet]
    have response := valid.2 index indexMem
    have encoded := congrFun
      (exactFinalEncoder_eq_grs (strategy.candidate z)) index
    unfold ExactGRSConversion.grsEncoder generalizedReedSolomonEncode at encoded
    simpa only [exactFinalGRSConversion, one_mul] using
      encoded.symm.trans response.symm
  have supportCard := Finset.card_le_card supportSubset
  have threshold := valid.1
  omega

-- The width-29 dependent interpolation index requires the same elaboration
-- allowance as the exact final specialization above.
set_option maxHeartbeats 1000000 in
/- The analogous exact statement for the initial width-29 circle code.
The received curve is divided by the proved nonzero GRS multiplier, while the
candidate remains an actual released `Fin 1024 → QM31Exact` message. -/
theorem exactInitialValidCandidate_substitute_eq_zero
    (lanes : Fin 29 → InitialWord QM31Exact)
    (strategy : Width29ProximateStrategy QM31Exact (Fin 1048576)
      (InitialMessage QM31Exact))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → QM31Exact)
    (kernel : curveInterpolationMap exactInitialGRSConversion.points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (gamma : QM31Exact)
    (valid : Width29ValidResponse exactInitialEncoder 38229 lanes strategy
      gamma) :
    interpolationSubstitute
        (specializeCurveCoefficients (by norm_num [initialCurveXBound,
          initialCurveYRows]) coefficients gamma)
        (exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma)) = 0 := by
  let specialized := specializeCurveCoefficients (by
    norm_num [initialCurveXBound, initialCurveYRows]) coefficients gamma
  have specializedKernel :
      interpolationMap exactInitialGRSConversion.points
        (exactInitialNormalizedReceived
          (fun index => width29CurveValue lanes gamma index))
        specialized = 0 := by
    have symbolic := specializeCurveCoefficients_mem_kernel
      (by norm_num [initialCurveZBound])
      (by norm_num [initialCurveXBound, initialCurveYRows])
      exactInitialGRSConversion.points (exactInitialNormalizedLanes lanes)
      coefficients kernel gamma
    simpa only [exactInitialNormalizedLanes_curve] using symbolic
  apply interpolationSubstitute_eq_zero_of_agreement (threshold := 38230)
    exactInitialGRSConversion.points
    (exactInitialNormalizedReceived
      (fun index => width29CurveValue lanes gamma index))
    exactInitialGRSConversion.points_injective specialized specializedKernel
    (by norm_num [initialCurveXBound, initialCurveYRows])
    (by norm_num [initialCurveXBound])
    (exactInitialGRSConversion.messagePolynomial (strategy.candidate gamma))
    (exactInitialGRSConversion.messagePolynomial_degree_le
      (strategy.candidate gamma))
  have supportSubset : strategy.support gamma ⊆
      polynomialAgreementSet exactInitialGRSConversion.points
        (exactInitialNormalizedReceived
          (fun index => width29CurveValue lanes gamma index))
        (exactInitialGRSConversion.messagePolynomial
          (strategy.candidate gamma)) := by
    intro index indexMem
    rw [mem_polynomialAgreementSet]
    have response := valid.2 index indexMem
    rw [exactInitialNormalizedReceived, response,
      exactInitialEncoder_coordinate_grs]
    unfold generalizedReedSolomonEncode
    have multiplierNeZero :=
      exactInitialGRSConversion.multipliers_ne_zero index
    field_simp
    simp only [exactInitialGRSConversion]
    ring
  have supportCard := Finset.card_le_card supportSubset
  have threshold := valid.1
  omega

/-! The curve-decodability reconstruction and exact V7 instantiations follow
after the released-code closure layer above. -/

#print axioms exactInitialLinear
#print axioms exactInitialEncoder_add
#print axioms exactInitialEncoder_smul
#print axioms exactFinalEncoder_add
#print axioms exactFinalEncoder_smul
#print axioms exactInitialEncoder_messageCurve
#print axioms exactFinalEncoder_messageCurve
#print axioms exists_exactInitialCurveInterpolation
#print axioms exists_exactFinalCurveInterpolation
#print axioms exactFinalValidCandidate_substitute_eq_zero
#print axioms exactInitialValidCandidate_substitute_eq_zero

end

end AspisK1.V7ExactCorrelatedAgreement
