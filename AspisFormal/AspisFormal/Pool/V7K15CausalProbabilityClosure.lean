import AspisFormal.Pool.V7K15IndependentRootCertificates

/-!
# Complete causal V7 K1.5 ideal probability closure

This file composes the three causal pieces proved separately:

* the fixed width-29 semantic family (`30,500 / |QM31|`);
* the fixed C1 copy family (`365,900 / |QM31|`);
* the five independent terminal categories (`30 / |QM31|`).

Their sum is the exact corrected K1.5 numerator `396,430`.  This is the
algebraic probability closure; the production transcript/source coupling is
kept as a separate explicit bridge.
-/

set_option autoImplicit false

namespace AspisPool.V7K15CausalProbabilityClosure

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7FixedC1CopyCollisionSecurity
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7K15IndependentRootCertificates
open AspisV5ComponentCQM31TowerExact
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5SequentialTerminalChallengeBound
open AspisV6TranscriptRelationGrammar
open AspisPool.V7Width29ComponentExtraction

/-- The complete ideal K1.5 mass, preserving the two-stage copy experiment
and the fixed-family semantic experiment rather than replacing either by an
informal root count. -/
noncomputable def causalK15IdealSubtotal
    (decoder : ExactDecoderInstantiation QM31Exact)
    (width29Lanes : Width29InitialWords QM31Exact)
    (c1Lanes : C1InitialWords)
    (terminal : FixedWidth29TupleCandidate decoder width29Lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder width29Lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (copySource : FixedC1TupleCandidate decoder c1Lanes →
      PackedDeployedCopySource) : Rat :=
  fixedWidth29CombinedIdealSemanticSubtotal decoder width29Lanes terminal
      sumcheck +
    fixedFamilyCopyCollisionProbability copySource +
    independentK15IdealSubtotal

/-- Exact composition of all thirteen failure branches, grouped into the
eight causal categories of `FixedFamilyK15Failure`. -/
theorem causalK15IdealSubtotal_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (width29Lanes : Width29InitialWords QM31Exact)
    (c1Lanes : C1InitialWords)
    (terminal : FixedWidth29TupleCandidate decoder width29Lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder width29Lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (copySource : FixedC1TupleCandidate decoder c1Lanes →
      PackedDeployedCopySource) :
    causalK15IdealSubtotal decoder width29Lanes c1Lanes terminal sumcheck
        copySource ≤
      (396430 : Rat) / Fintype.card QM31Exact := by
  unfold causalK15IdealSubtotal
  calc
    fixedWidth29CombinedIdealSemanticSubtotal decoder width29Lanes terminal
          sumcheck +
        fixedFamilyCopyCollisionProbability copySource +
        independentK15IdealSubtotal ≤
      (30500 : Rat) / Fintype.card QM31Exact +
        (365900 : Rat) / Fintype.card QM31Exact +
        (30 : Rat) / Fintype.card QM31Exact := by
      gcongr
      · exact fixedWidth29CombinedIdealSemanticSubtotal_le decoder
          width29Lanes terminal sumcheck
      · exact fixedC1CopyCollisionProbability_le decoder c1Lanes copySource
      · exact le_of_eq independentK15IdealSubtotal_eq
    _ = (396430 : Rat) / Fintype.card QM31Exact := by ring

/-- The complete corrected causal K1.5 algebraic error is below `2^-105`
before any grinding/work normalization. -/
theorem causal_k15_ideal_subtotal_le_two_pow_neg_105 :
    (396430 : Real) / Fintype.card QM31Exact ≤
      (1 : Real) / 2 ^ 105 := by
  rw [qm31Exact_card]
  norm_num [P]

#print axioms causalK15IdealSubtotal_le
#print axioms causal_k15_ideal_subtotal_le_two_pow_neg_105

end AspisPool.V7K15CausalProbabilityClosure
