import AspisFormal.V5ForwardAcceptedFalseRawAccounting
import AspisFormal.V5TerminalFixedInitialListSecurity

/-!
# Candidate timing in the accepted-false experiment

`CompatibilityFriExperiment.CandidateAt coins` is written using the complete
transcript at one outcome, which can make the candidate type look as though it
depends on later challenges.  It does not: the initial decoder list reads only
the layer-zero word, and every transcript in the causal family has the same
layer-zero word.

This file proves the exact list equality and subtype equivalence.  It also
derives the stronger 222-candidate bound directly from the released circle
encoder distance theorem, then specializes the terminal subtotal to the
candidate type used by the accepted-false accounting.
-/

namespace AspisV5CompatibilityCandidateTimingBridge

open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CandidateTerminalSecurity
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriInitialListBound
open AspisV5FriReleasedLineGeometry
open AspisV5SequentialTerminalChallengeBound
open AspisV5Tag67FixedCandidateTiming
open AspisV5TerminalFixedInitialListSecurity

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]

set_option maxRecDepth 100000

/-- The outcome-indexed presentation of the initial list is exactly the one
fixed by the causal family's layer-zero word. -/
theorem CompatibilityFriExperiment.initialCandidateList_eq_fixed_family
    {Coins : Type*} (experiment : CompatibilityFriExperiment Coins K)
    (coins : Coins) :
    initialCandidateList
        (concreteCodeEncoders experiment.base releasedEvaluationPoints)
        (experiment.transcriptAt coins) =
      fixedInitialCandidateList
        (concreteCodeEncoders experiment.base releasedEvaluationPoints)
        experiment.family.layer0 := by
  rw [initialCandidateList_eq_fixedInitialCandidateList]
  rfl

/-- Exact equivalence between the candidate subtype used in accepted-false
accounting and the pre-challenge fixed-list subtype. -/
noncomputable def CompatibilityFriExperiment.candidateAtEquivFixedFamily
    {Coins : Type*} (experiment : CompatibilityFriExperiment Coins K)
    (coins : Coins) :
    experiment.CandidateAt coins ≃
      FixedInitialCandidate
        (concreteCodeEncoders experiment.base releasedEvaluationPoints)
        experiment.family.layer0 where
  toFun candidate := ⟨candidate.1, by
    rw [← initialCandidateList_eq_fixed_family experiment coins]
    exact candidate.2⟩
  invFun candidate := ⟨candidate.1, by
    rw [initialCandidateList_eq_fixed_family experiment coins]
    exact candidate.2⟩
  left_inv candidate := by cases candidate; rfl
  right_inv candidate := by cases candidate; rfl

/-- The exact accepted-false candidate type has at most 222 elements.  The
older 240 field is therefore conservative. -/
theorem CompatibilityFriExperiment.candidateAt_card_le_222
    {Coins : Type*} (experiment : CompatibilityFriExperiment Coins K)
    (coins : Coins) :
    Fintype.card (experiment.CandidateAt coins) ≤ 222 := by
  rw [Fintype.card_congr
    (candidateAtEquivFixedFamily experiment coins)]
  exact fixedInitialCandidate_fintype_card_le_222
    (concreteCodeEncoders experiment.base releasedEvaluationPoints)
    experiment.family.layer0
    (releasedInitialEncoderDistance experiment.base experiment.finalDomain)

/-- The per-outcome candidate type in the accepted-false experiment inherits
the tighter `222 * 305 / |K|` terminal subtotal.  The preceding equivalence is
the timing fact; this numeric theorem uses its derived cardinality bound. -/
theorem CompatibilityFriExperiment.candidateAt_terminalSubtotal_le_222
    {Coins : Type*} (experiment : CompatibilityFriExperiment Coins K)
    (coins : Coins)
    (terminal : experiment.CandidateAt coins → FixedTerminalAlgebraPlan K)
    (sumcheck : experiment.CandidateAt coins →
      AdaptiveDegree27MessagePlan K) :
    candidateCombinedIdealTerminalSubtotal
        (experiment.CandidateAt coins) terminal sumcheck ≤
      (67710 : Rat) / Fintype.card K := by
  calc
    candidateCombinedIdealTerminalSubtotal
        (experiment.CandidateAt coins) terminal sumcheck ≤
      Fintype.card (experiment.CandidateAt coins) *
        ((305 : Rat) / Fintype.card K) :=
      candidateCombinedIdealTerminalSubtotal_le_card_mul
        (experiment.CandidateAt coins) terminal sumcheck
    _ ≤ (222 : Rat) * ((305 : Rat) / Fintype.card K) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast candidateAt_card_le_222 experiment coins
    _ = (67710 : Rat) / Fintype.card K := by ring

#print axioms CompatibilityFriExperiment.initialCandidateList_eq_fixed_family
#print axioms CompatibilityFriExperiment.candidateAtEquivFixedFamily
#print axioms CompatibilityFriExperiment.candidateAt_card_le_222
#print axioms CompatibilityFriExperiment.candidateAt_terminalSubtotal_le_222

end AspisV5CompatibilityCandidateTimingBridge
