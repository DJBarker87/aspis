import AspisFormal.K1.V7Tag73ExactOneFoldRestorationStrategy
import AspisFormal.V7ExactOneFoldDomains

/-!
# Concrete deployed encoder binding for the Tag-73 one-fold reduction

This module instantiates the algebraic structure consumed by the restoration-
wide one-fold theorem.  It defines the exact bit-reversed log-18 natural-line
encoder, proves that the exact stored log-20 circle evaluator is its radix-four
circle lift, proves final-encoder injectivity, and packages the literal inverse
table equations needed by the normalized fold.

The only remaining source-facing inputs are ordinary equalities identifying a
decoder's two encoder functions and the parsed inverse arrays with these exact
mathematical objects.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactOneFoldEncoderBinding

open AspisCircleGroupOrder
open AspisCircleTensorBinding
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriInitialCircleEncoderIdentity
open AspisV6OneFoldCandidateExtraction
open AspisV7ExactOneFoldDomains

noncomputable section

private theorem qm31ExactTwoNeZero : (2 : QM31Exact) ≠ 0 := by
  intro equalZero
  have mapped :
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact (2 : M31Exact) =
        algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact (0 : M31Exact) := by
    calc
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact (2 : M31Exact) =
          (2 : QM31Exact) := map_ofNat _ 2
      _ = 0 := equalZero
      _ = algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (0 : M31Exact) := (map_zero _).symm
  have baseEqual := FaithfulSMul.algebraMap_injective M31Exact QM31Exact mapped
  exact AspisCircleGroupOrder.two_ne_zero_ZModP baseEqual

local instance qm31ExactNeZeroTwo : NeZero (2 : QM31Exact) :=
  ⟨qm31ExactTwoNeZero⟩

/-- Exact log-18 natural-line encoder as a QM31-linear map. -/
noncomputable def exactFinalLinear :
    (AspisV6OneFoldCandidateExtraction.FinalCoefficients QM31Exact) →ₗ[QM31Exact]
      (AspisV6OneFoldCandidateExtraction.FinalWord QM31Exact) where
  toFun := fun coefficients index =>
    (naturalCoefficientPolynomial coefficients).eval
      (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (storedFirstLineX18 index))
  map_add' := by
    intro left right
    funext index
    change
      (naturalCoefficientPolynomial (left + right)).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
            (storedFirstLineX18 index)) =
        (naturalCoefficientPolynomial left).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
              (storedFirstLineX18 index)) +
          (naturalCoefficientPolynomial right).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
              (storedFirstLineX18 index))
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar coefficients
    funext index
    change
      (naturalCoefficientPolynomial (scalar • coefficients)).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
            (storedFirstLineX18 index)) =
        scalar * (naturalCoefficientPolynomial coefficients).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
            (storedFirstLineX18 index))
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def exactFinalEncoder :
    AspisV6OneFoldCandidateExtraction.FinalCoefficients QM31Exact →
      AspisV6OneFoldCandidateExtraction.FinalWord QM31Exact :=
  exactFinalLinear

@[simp] theorem exactFinalLinear_apply
    (coefficients : AspisV6OneFoldCandidateExtraction.FinalCoefficients
      QM31Exact) (index : Fin 262144) :
    exactFinalLinear coefficients index =
      (naturalCoefficientPolynomial coefficients).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
          (storedFirstLineX18 index)) := rfl

/-- Exact line-evaluation identity used both for distance and decoder
applicability. -/
noncomputable def exactFinalEvaluationIdentity :
    NaturalLineEvaluationIdentity exactFinalEncoder where
  points := fun index =>
    algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
      (storedFirstLineX18 index)
  points_injective := by
    intro left right equal
    apply storedFirstLineX18_injective
    exact FaithfulSMul.algebraMap_injective M31Exact QM31Exact equal
  encoder_eq_eval := by
    intro message index
    rfl

theorem exactFinalEncoder_overlap_cap
    (left right : AspisV6OneFoldCandidateExtraction.FinalCoefficients
      QM31Exact) (different : left ≠ right) :
    (AspisV5FriCoherentCandidateExtraction.agreementSet
      (exactFinalEncoder left) (exactFinalEncoder right)).card ≤
      255 := by
  exact agreementSet_card_le_of_polynomialEvaluation exactFinalEncoder 255
    (naturalLinePolynomialRealization (K := QM31Exact)
      (n := 256) (m := 262144) (by norm_num)
      exactFinalEncoder exactFinalEvaluationIdentity)
    left right different

theorem exactFinalEncoder_injective : Function.Injective exactFinalEncoder := by
  intro left right codeEqual
  by_contra different
  have cap := exactFinalEncoder_overlap_cap left right different
  have full : AspisV5FriCoherentCandidateExtraction.agreementSet
      (exactFinalEncoder left) (exactFinalEncoder right) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro index
    simp only [AspisV5FriCoherentCandidateExtraction.agreementSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrFun codeEqual index
  rw [full] at cap
  norm_num at cap

/-- Embedded slot-zero circle x-coordinate for each stored fibre. -/
def exactCircleX (index : Fin 262144) : QM31Exact :=
  algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
    (X (storedInitialFibrePoint20 index))

/-- Embedded slot-zero circle y-coordinate for each stored fibre. -/
def exactCircleY (index : Fin 262144) : QM31Exact :=
  algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
    (storedInitialFibrePoint20 index).1.2

/-- The exact stored circle evaluator is pointwise the radix-four lift of the
exact line encoder. -/
theorem exactInitialEncoder_eq_circleLift :
    exactInitialEncoder = fun message =>
      circleLiftEncoder exactFinalLinear exactCircleX exactCircleY message := by
  funext message storedIndex
  suffices childEquality : ∀ (index : Fin 262144) (slot : Fin 4),
      exactInitialEncoder message (childIndex index slot) =
        circleLiftEncoder exactFinalLinear exactCircleX exactCircleY message
          (childIndex index slot) by
    have selected := childEquality (parentIndex (n := 262144) storedIndex)
      (slotIndex (n := 262144) storedIndex)
    rw [childIndex_parentIndex_slotIndex (n := 262144) storedIndex] at selected
    exact selected
  intro index slot
  rw [show circleLiftEncoder exactFinalLinear exactCircleX exactCircleY message
      (childIndex index slot) =
      radix4Evaluate (exactCircleY index) (-exactCircleY index)
        (exactCircleX index)
        (fun lane => exactFinalLinear
          (coefficientLane 256 lane message) index) slot by
      unfold circleLiftEncoder
      simpa only [Pi.neg_apply] using
        (radix4LiftEncoder_apply_child exactFinalLinear exactCircleY
          (-exactCircleY) exactCircleX message index slot)]
  simp only [exactFinalLinear_apply, exactInitialEncoder]
  have lineNode := storedFirstLineX18_eq_doubled_algebraMap
    (K := QM31Exact) index
  have fibrePoint :
      storedInitialFibrePoint20 index =
        g ^ AspisV6EncoderDistance.initialCircleExponent
          (2 * (AspisV5FriBitReverse.reverseFin 18 index).val) := by
    simpa only [storedInitialFibrePoint20_eq_zpow,
      storedInitialNaturalIndex20_child_zero]
  have negativeNode :
      doubledFactor
          (-(algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
            (X (storedInitialFibrePoint20 index)))) 1 =
        doubledFactor
          (algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
            (X (storedInitialFibrePoint20 index))) 1 := by
    simp only [doubledFactor]
    ring
  rw [storedInitialCirclePoint20_x_slots,
    storedInitialCirclePoint20_y_slots]
  have fourCases (selectedSlot : Fin 4) :
      selectedSlot = 0 ∨ selectedSlot = 1 ∨
        selectedSlot = 2 ∨ selectedSlot = 3 := by
    fin_cases selectedSlot <;> simp
  rcases fourCases slot with hs | hs | hs | hs
  all_goals subst slot
  all_goals
    simp [storedCircleSlotX20, storedCircleSlotY20, exactCircleX,
      exactCircleY, radix4Evaluate, map_neg]
  all_goals
    rw [← fibrePoint]
  all_goals
    rw [initialP0_eval_lanes, initialP1_eval_lanes]
    try rw [negativeNode]
    rw [← lineNode]
  all_goals ring

/-- Literal inverse-table equations required by the one-fold algebraic
binding.  They are source/public-parameter facts, not coding-theorem fields. -/
def ExactOneFoldInverseTables
    (schedule : OneFoldSchedule M31Exact QM31Exact) : Prop :=
  (∀ index,
    2 * exactCircleX index *
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (schedule.circleInv2x index) = 1) ∧
  (∀ index,
    2 * exactCircleY index *
      algebraMap (ZMod AspisCircleGroupOrder.P) QM31Exact
        (schedule.circleInv2y index) = 1)

/-- Package the concrete mathematical encoders into the generic restoration
theorem's algebraic interface. -/
noncomputable def exactOneFoldAlgebraBinding
    (schedule : OneFoldSchedule M31Exact QM31Exact)
    (encoders : AspisV6OneFoldCandidateExtraction.CodeEncoders QM31Exact)
    (initialEncoderEq : encoders.initial = exactInitialEncoder)
    (finalEncoderEq : encoders.final = exactFinalEncoder)
    (inverseTables : ExactOneFoldInverseTables schedule) :
    OneFoldAlgebraBinding schedule encoders where
  finalLinear := exactFinalLinear
  circleX := exactCircleX
  circleY := exactCircleY
  initialEncoderEq := initialEncoderEq.trans exactInitialEncoder_eq_circleLift
  finalEncoderEq := finalEncoderEq
  inverse2x := inverseTables.1
  inverse2y := inverseTables.2
  finalInjective := exactFinalEncoder_injective

#print axioms exactFinalLinear_apply
#print axioms exactFinalEncoder_overlap_cap
#print axioms exactFinalEncoder_injective
#print axioms exactInitialEncoder_eq_circleLift
#print axioms exactOneFoldAlgebraBinding

end

end AspisK1.V7Tag73ExactOneFoldEncoderBinding
