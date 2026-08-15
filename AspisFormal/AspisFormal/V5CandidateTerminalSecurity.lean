import AspisFormal.V5CombinedTerminalSecurity

/-!
# Terminal challenge accounting across the released candidate list

`V5CombinedTerminalSecurity` proves `305 / |K|` for one trace fixed before
its challenges.  An accepted false proof may instead be witnessed by one
member of the decoder's initial list.  That list has at most 240 members, so
using the one-trace number directly would undercount the event.

This file performs the conservative union accounting.  It sums one combined
terminal experiment per candidate and proves the released cap

`240 * 305 / |K| = 73200 / |K|`.

At the released QM31 cardinality that subtotal is at most `2^-107`.  This is
still an ideal arithmetic subtotal, not a deployed theft-resistance claim.
The production theorem retains one explicit comparison containing candidate
selection, source correspondence, commitment timing, SHA-256 behavior, and
field sampling.
-/

namespace AspisV5CandidateTerminalSecurity

open scoped BigOperators
open AspisFormal.ArithmetizationCore
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CombinedTerminalSecurity
open AspisV5FriFixedFamilyExperiment
open AspisV5SequentialTerminalChallengeBound

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]

/-- Sum of the one-trace ideal terminal probabilities over one fixed finite
candidate family.  This definition counts each candidate once. -/
noncomputable def candidateCombinedIdealTerminalSubtotal
    (Candidate : Type*) [Fintype Candidate]
    (terminal : Candidate → FixedTerminalAlgebraPlan K)
    (sumcheck : Candidate → AdaptiveDegree27MessagePlan K) : Rat :=
  ∑ candidate,
    combinedIdealTerminalFailureProbability (terminal candidate)
      (sumcheck candidate)

/-- Union-bound subtotal for an arbitrary finite candidate family. -/
theorem candidateCombinedIdealTerminalSubtotal_le_card_mul
    (Candidate : Type*) [Fintype Candidate]
    (terminal : Candidate → FixedTerminalAlgebraPlan K)
    (sumcheck : Candidate → AdaptiveDegree27MessagePlan K) :
    candidateCombinedIdealTerminalSubtotal Candidate terminal sumcheck ≤
      Fintype.card Candidate * ((305 : Rat) / Fintype.card K) := by
  unfold candidateCombinedIdealTerminalSubtotal
  calc
    (∑ candidate,
        combinedIdealTerminalFailureProbability (terminal candidate)
          (sumcheck candidate)) ≤
        ∑ _candidate : Candidate,
          ((305 : Rat) / Fintype.card K) := by
      apply Finset.sum_le_sum
      intro candidate _
      exact combinedIdealTerminalFailureProbability_le
        (terminal candidate) (sumcheck candidate)
    _ = Fintype.card Candidate *
        ((305 : Rat) / Fintype.card K) := by simp

/-- The released list cap turns the per-candidate `305` root count into
`73200`. -/
theorem candidateCombinedIdealTerminalSubtotal_le_240
    (Candidate : Type*) [Fintype Candidate]
    (terminal : Candidate → FixedTerminalAlgebraPlan K)
    (sumcheck : Candidate → AdaptiveDegree27MessagePlan K)
    (candidateCap : Fintype.card Candidate ≤ 240) :
    candidateCombinedIdealTerminalSubtotal Candidate terminal sumcheck ≤
      (73200 : Rat) / Fintype.card K := by
  calc
    candidateCombinedIdealTerminalSubtotal Candidate terminal sumcheck ≤
        Fintype.card Candidate *
          ((305 : Rat) / Fintype.card K) :=
      candidateCombinedIdealTerminalSubtotal_le_card_mul
        Candidate terminal sumcheck
    _ ≤ (240 : Rat) * ((305 : Rat) / Fintype.card K) := by
      apply mul_le_mul_of_nonneg_right _
      · positivity
      · exact_mod_cast candidateCap
    _ = (73200 : Rat) / Fintype.card K := by ring

/-- Concrete released-field arithmetic for the cap-240 subtotal. -/
theorem qm31_candidate_terminal_subtotal_le_two_pow_neg_107 :
    (73200 : Real) / AspisSoundnessLedger.FIELD ≤
      (1 : Real) / 2 ^ 107 := by
  unfold AspisSoundnessLedger.FIELD
  norm_num

/-- Exact remaining production comparison for the cap-240 candidate event.
No hash, sampling, commitment, or source claim is inferred here. -/
structure ProductionCandidateTerminalConnection
    (Coins Candidate : Type*)
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Fintype Candidate]
    (productionFailure : Finset Coins)
    (terminal : Candidate → FixedTerminalAlgebraPlan K)
    (sumcheck : Candidate → AdaptiveDegree27MessagePlan K)
    (candidateSelectionHashAndSourceGap : Rat) : Prop where
  gapNonnegative : 0 ≤ candidateSelectionHashAndSourceGap
  production_le_candidate_subtotal_plus_gap :
    finiteUniformEventProbability productionFailure ≤
      candidateCombinedIdealTerminalSubtotal Candidate terminal sumcheck +
        candidateSelectionHashAndSourceGap

/-- A concrete production event inherits the cap-240 terminal bound only
after the explicit comparison above has been supplied. -/
theorem productionCandidateTerminalFailureProbability_le
    {Coins Candidate : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Fintype Candidate]
    (productionFailure : Finset Coins)
    (terminal : Candidate → FixedTerminalAlgebraPlan K)
    (sumcheck : Candidate → AdaptiveDegree27MessagePlan K)
    (candidateSelectionHashAndSourceGap : Rat)
    (candidateCap : Fintype.card Candidate ≤ 240)
    (connection : ProductionCandidateTerminalConnection Coins Candidate
      productionFailure terminal sumcheck
      candidateSelectionHashAndSourceGap) :
    finiteUniformEventProbability productionFailure ≤
      (73200 : Rat) / Fintype.card K +
        candidateSelectionHashAndSourceGap := by
  exact connection.production_le_candidate_subtotal_plus_gap.trans
    (add_le_add
      (candidateCombinedIdealTerminalSubtotal_le_240 Candidate terminal
        sumcheck candidateCap)
      le_rfl)

#print axioms candidateCombinedIdealTerminalSubtotal_le_card_mul
#print axioms candidateCombinedIdealTerminalSubtotal_le_240
#print axioms qm31_candidate_terminal_subtotal_le_two_pow_neg_107
#print axioms productionCandidateTerminalFailureProbability_le

end AspisV5CandidateTerminalSecurity
