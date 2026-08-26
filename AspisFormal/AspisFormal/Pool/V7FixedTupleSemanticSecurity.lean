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

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CandidateTerminalSecurity
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

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
#print axioms fixed_width29_semantic_subtotal_le_two_pow_neg_109
#print axioms production_fixedWidth29SemanticFailureProbability_le

end AspisPool.V7FixedTupleSemanticSecurity
