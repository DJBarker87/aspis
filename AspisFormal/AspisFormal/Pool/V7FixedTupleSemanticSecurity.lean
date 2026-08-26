import AspisFormal.Pool.V7FixedWidth29TupleList
import AspisFormal.V5CandidateTerminalSecurity

/-!
# Causal semantic accounting over the fixed V7 tuple family

For one trace fixed before `theta`, the existing checked experiment charges
`35 / |K|` for theta, the ten-coordinate zerocheck point, and helper `mu`,
plus `270 / |K|` for the ten adaptive degree-27 sumcheck rounds.  A V7 trace
may be selected only after those challenges, so the one-trace `305 / |K|`
bound cannot be used directly.

`V7FixedWidth29TupleList` proves that every successful K1.4 trace belongs to
one decoder-backed family, fixed by the received lanes, with at most 100
members.  This file instantiates the existing fixed-candidate experiment and
obtains the exact conservative subtotal `30,500 / |QM31|`.
-/

set_option autoImplicit false

namespace AspisPool.V7FixedTupleSemanticSecurity

open AspisFormal.ArithmetizationCore
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CandidateTerminalSecurity
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisV5SumcheckTranscriptBinding

/-! ## Deterministic accepted-trace coverage -/

/-- The three non-sumcheck terminal failures for one fixed plan. -/
def FixedTerminalAlgebraFailure
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (plan : FixedTerminalAlgebraPlan K)
    (theta : K) (point : Fin 10 → K) (mu : K) : Prop :=
  HelperCancellation plan.basis plan.constraintRows theta point mu
      plan.helper ∨
    ZerocheckEvaluationCollision plan.basis plan.constraintRows theta point ∨
    ThetaLaneCollision plan.basis plan.constraintRows theta

/-- Corresponding membership in the three exact finite bad sets. -/
def FixedTerminalAlgebraBad
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (plan : FixedTerminalAlgebraPlan K)
    (theta : K) (point : Fin 10 → K) (mu : K) : Prop :=
  theta ∈ plan.thetaBad ∨
    point ∈ plan.pointBad theta ∨
    mu ∈ plan.muBad theta point

set_option maxRecDepth 1000000 in
theorem fixedTerminalAlgebraFailure_implies_bad
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]
    (plan : FixedTerminalAlgebraPlan K)
    (theta : K) (point : Fin 10 → K) (mu : K)
    (failure : FixedTerminalAlgebraFailure plan theta point mu) :
    FixedTerminalAlgebraBad plan theta point mu := by
  rcases failure with helper | zerocheck | thetaCollision
  · exact Or.inr (Or.inr
      ((plan.helperCancellation_iff theta point mu).mp helper))
  · exact Or.inr (Or.inl
      ((plan.zerocheckCollision_iff theta point).mp zerocheck))
  · exact Or.inl ((plan.thetaCollision_iff theta).mp thetaCollision)

/-- The four candidate-dependent semantic failures, unioned over the one
width-29 family fixed before `theta` and the ten sumcheck challenges. -/
def FixedWidth29SemanticFailure
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (theta : QM31Exact) (zerocheckPoint sumcheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact) : Prop :=
  ∃ candidate,
    FixedTerminalAlgebraBad (terminal candidate) theta zerocheckPoint mu ∨
      ∃ round,
        sumcheckPoint round ∈ (sumcheck candidate).badAt
          (challengeHistory sumcheckPoint round)

/-- Exact source data needed to place one accepted semantic trace inside the
fixed-family event. `causal` states that each pair of degree-27 messages is
fixed by the preceding challenges. `terminalCovered` records the deterministic
finite-root characterization of the terminal algebra. -/
structure SelectedFixedWidth29SemanticSource
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (selected : FixedWidth29TupleCandidate decoder lanes)
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → QM31Exact}
    (reference : FixedOracleTenRoundTrace table wire.transcript.point) : Prop where
  causal : WireUsesAdaptiveDegree27Plan wire reference (sumcheck selected)
  terminalCovered : ∀ theta point mu,
    FixedTerminalAlgebraFailure (terminal selected) theta point mu →
      FixedTerminalAlgebraBad (terminal selected) theta point mu

set_option maxRecDepth 1000000 in
/-- Build the selected-trace source record from its only protocol-specific
premise: causal construction of the ten sumcheck messages.  Terminal coverage
is discharged by the exact root-set characterizations already proved for a
fixed terminal plan. -/
theorem selectedFixedWidth29SemanticSourceOfCausal
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (selected : FixedWidth29TupleCandidate decoder lanes)
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → QM31Exact}
    (reference : FixedOracleTenRoundTrace table wire.transcript.point)
    (causal : WireUsesAdaptiveDegree27Plan wire reference
      (sumcheck selected)) :
    SelectedFixedWidth29SemanticSource decoder lanes terminal sumcheck
      selected wire reference where
  causal := causal
  terminalCovered := fun theta point mu failure =>
    fixedTerminalAlgebraFailure_implies_bad
      (terminal selected) theta point mu failure

/- Every candidate-dependent semantic failure of the selected accepted trace
is covered by the fixed pre-challenge width-29 family. -/
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 200000 in
theorem selected_semantic_failure_mem_fixedWidth29_family
    {Public Root : Type*}
    {scheme : FiatShamirSchedule Public Root QM31Exact}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (selected : FixedWidth29TupleCandidate decoder lanes)
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → QM31Exact}
    (reference : FixedOracleTenRoundTrace table wire.transcript.point)
    (source : SelectedFixedWidth29SemanticSource decoder lanes terminal sumcheck
      selected wire reference)
    (theta : QM31Exact)
    (zerocheckPoint : Fin 10 → QM31Exact)
    (mu : QM31Exact)
    (failure : TenRoundRepair wire reference ∨
      FixedTerminalAlgebraFailure (terminal selected) theta
        zerocheckPoint mu) :
    FixedWidth29SemanticFailure decoder lanes terminal sumcheck theta
      zerocheckPoint wire.transcript.point mu := by
  rcases failure with repair | terminalFailure
  · have hit := tenRoundRepair_hits_adaptive_badSet wire reference
      (sumcheck selected) source.causal repair
    exact ⟨selected, Or.inr hit⟩
  · exact ⟨selected, Or.inl
      (source.terminalCovered theta zerocheckPoint mu terminalFailure)⟩

/-- The exact ideal subtotal over the one fixed width-29 tuple family. -/
noncomputable def fixedWidth29CombinedIdealSemanticSubtotal
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact) : Rat :=
  candidateCombinedIdealTerminalSubtotal
    (FixedWidth29TupleCandidate decoder lanes) terminal sumcheck

/-- At most 100 fixed candidates, each costing 305 roots, gives exactly the
`30,500 / |QM31|` causal semantic subtotal. -/
theorem fixedWidth29CombinedIdealSemanticSubtotal_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact) :
    fixedWidth29CombinedIdealSemanticSubtotal decoder lanes terminal sumcheck ≤
      (30500 : Rat) / Fintype.card QM31Exact := by
  unfold fixedWidth29CombinedIdealSemanticSubtotal
  calc
    candidateCombinedIdealTerminalSubtotal
        (FixedWidth29TupleCandidate decoder lanes) terminal sumcheck ≤
        Fintype.card (FixedWidth29TupleCandidate decoder lanes) *
          ((305 : Rat) / Fintype.card QM31Exact) :=
      candidateCombinedIdealTerminalSubtotal_le_card_mul
        (FixedWidth29TupleCandidate decoder lanes) terminal sumcheck
    _ ≤ (100 : Rat) *
        ((305 : Rat) / Fintype.card QM31Exact) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast fixedWidth29TupleCandidate_card_le_100 decoder lanes
      · positivity
    _ = (30500 : Rat) / Fintype.card QM31Exact := by ring

/-- Concrete field arithmetic: the corrected fixed-family semantic subtotal
is still at most `2^-109` before any work normalization. -/
theorem fixed_width29_semantic_subtotal_le_two_pow_neg_109 :
    (30500 : Real) / Fintype.card QM31Exact ≤
      (1 : Real) / 2 ^ 109 := by
  rw [qm31Exact_card]
  norm_num [P]

/-- Production comparison specialized to the causal V7 family.  Its one gap
field remains the explicit source/ROM/sampling bridge; no such claim is hidden
inside the ideal list union. -/
theorem production_fixedWidth29SemanticFailureProbability_le
    {Coins : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (productionFailure : Finset Coins)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact)
    (candidateSelectionHashAndSourceGap : Rat)
    (connection : ProductionCandidateTerminalConnection Coins
      (FixedWidth29TupleCandidate decoder lanes) productionFailure terminal
      sumcheck candidateSelectionHashAndSourceGap) :
    AspisV5FriFixedFamilyExperiment.finiteUniformEventProbability
        productionFailure ≤
      (30500 : Rat) / Fintype.card QM31Exact +
        candidateSelectionHashAndSourceGap := by
  exact connection.production_le_candidate_subtotal_plus_gap.trans
    (add_le_add
      (fixedWidth29CombinedIdealSemanticSubtotal_le decoder lanes terminal
        sumcheck)
      le_rfl)

#print axioms fixedWidth29CombinedIdealSemanticSubtotal_le
#print axioms fixedTerminalAlgebraFailure_implies_bad
#print axioms selectedFixedWidth29SemanticSourceOfCausal
#print axioms selected_semantic_failure_mem_fixedWidth29_family
#print axioms fixed_width29_semantic_subtotal_le_two_pow_neg_109
#print axioms production_fixedWidth29SemanticFailureProbability_le

end AspisPool.V7FixedTupleSemanticSecurity
