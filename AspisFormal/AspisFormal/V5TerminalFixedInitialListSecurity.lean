import AspisFormal.V5PrefixDependentCandidateSecurity
import AspisFormal.V5Tag67FixedCandidateTiming

/-!
# Terminal bound for the decoder list fixed before the challenges

The terminal algebra bound may only union over candidates fixed before
`theta` and the later sumcheck challenges.  The initial FRI decoder list has
exactly that property: it is a function of the layer-zero word alone.  Later
FRI data may choose a member of the list, but cannot change the list.

This file specializes the generic candidate accounting to that exact list.
The proved Johnson bound is 222 candidates, giving the tighter ideal subtotal
`67710 / |K|`; the release's cap-240 subtotal remains a conservative upper
bound.

Merkle binding and the Fiat--Shamir conditional-distribution comparison are
still external to this finite-field result.
-/

namespace AspisV5TerminalFixedInitialListSecurity

open AspisFormal.ArithmetizationCore
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5CandidateTerminalSecurity
open AspisV5CombinedTerminalSecurity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriInitialListBound
open AspisV5PrefixDependentCandidateSecurity
open AspisV5SequentialTerminalChallengeBound
open AspisV5Tag67FixedCandidateTiming

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]

set_option maxRecDepth 100000

/-- The exact fixed-list subtype inherits the stronger 222-member Johnson
bound, not merely the release cap of 240. -/
theorem fixedInitialCandidate_fintype_card_le_222
    (encoders : CodeEncoders K) (layer0 : Word0 K)
    (hdistance : InitialEncoderDistance encoders) :
    Fintype.card (FixedInitialCandidate encoders layer0) ≤ 222 := by
  change Fintype.card
    {candidate : Coeff0 K // candidate ∈
      fixedInitialCandidateList encoders layer0} ≤ 222
  rw [Fintype.card_coe]
  exact fixedInitialCandidateList_card_le_222 encoders layer0 hdistance

/-- For one layer-zero word fixed before the terminal challenges, summing the
checked terminal failure probabilities over every possible decoder candidate
costs at most `222 * 305 / |K|`. -/
theorem fixedInitialCandidate_terminalSubtotal_le_222
    (encoders : CodeEncoders K) (layer0 : Word0 K)
    (hdistance : InitialEncoderDistance encoders)
    (terminal : FixedInitialCandidate encoders layer0 →
      FixedTerminalAlgebraPlan K)
    (sumcheck : FixedInitialCandidate encoders layer0 →
      AdaptiveDegree27MessagePlan K) :
    candidateCombinedIdealTerminalSubtotal
        (FixedInitialCandidate encoders layer0) terminal sumcheck ≤
      (67710 : Rat) / Fintype.card K := by
  calc
    candidateCombinedIdealTerminalSubtotal
        (FixedInitialCandidate encoders layer0) terminal sumcheck ≤
      Fintype.card (FixedInitialCandidate encoders layer0) *
        ((305 : Rat) / Fintype.card K) :=
      candidateCombinedIdealTerminalSubtotal_le_card_mul
        (FixedInitialCandidate encoders layer0) terminal sumcheck
    _ ≤ (222 : Rat) * ((305 : Rat) / Fintype.card K) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast
        fixedInitialCandidate_fintype_card_le_222 encoders layer0 hdistance
    _ = (67710 : Rat) / Fintype.card K := by ring

/-- The same result averaged over any finite family of committed prefixes.
The prefix may determine the layer-zero word arbitrarily; no factor for the
number of prefixes appears. -/
theorem prefixAveragedFixedInitialCandidate_terminalSubtotal_le_222
    (Prefix : Type*) [Fintype Prefix] [Nonempty Prefix]
    (encoders : CodeEncoders K)
    (layer0Of : Prefix → Word0 K)
    (hdistance : InitialEncoderDistance encoders)
    (terminal : ∀ p, FixedInitialCandidate encoders (layer0Of p) →
      FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p, FixedInitialCandidate encoders (layer0Of p) →
      AdaptiveDegree27MessagePlan K) :
    prefixAveragedCandidateTerminalSubtotal Prefix
        (fun p ↦ FixedInitialCandidate encoders (layer0Of p)) terminal
        sumcheck ≤
      (67710 : Rat) / Fintype.card K := by
  unfold prefixAveragedCandidateTerminalSubtotal
  exact finiteSubsetAverage_le (Finset.univ : Finset Prefix)
    (fun p ↦ candidateCombinedIdealTerminalSubtotal
      (FixedInitialCandidate encoders (layer0Of p)) (terminal p) (sumcheck p))
    ((67710 : Rat) / Fintype.card K) (by positivity)
    (fun p _ ↦ fixedInitialCandidate_terminalSubtotal_le_222 encoders
      (layer0Of p) hdistance (terminal p) (sumcheck p))

/-- The exact-list 222 result implies the release's conservative cap-240
subtotal without any further coding-theory premise. -/
theorem prefixAveragedFixedInitialCandidate_terminalSubtotal_le_240
    (Prefix : Type*) [Fintype Prefix] [Nonempty Prefix]
    (encoders : CodeEncoders K)
    (layer0Of : Prefix → Word0 K)
    (hdistance : InitialEncoderDistance encoders)
    (terminal : ∀ p, FixedInitialCandidate encoders (layer0Of p) →
      FixedTerminalAlgebraPlan K)
    (sumcheck : ∀ p, FixedInitialCandidate encoders (layer0Of p) →
      AdaptiveDegree27MessagePlan K) :
    prefixAveragedCandidateTerminalSubtotal Prefix
        (fun p ↦ FixedInitialCandidate encoders (layer0Of p)) terminal
        sumcheck ≤
      (73200 : Rat) / Fintype.card K := by
  exact (prefixAveragedFixedInitialCandidate_terminalSubtotal_le_222 Prefix
    encoders layer0Of hdistance terminal sumcheck).trans (by
      have hcard : (0 : Rat) < Fintype.card K := by
        exact_mod_cast Fintype.card_pos
      rw [div_le_div_iff_of_pos_right hcard]
      norm_num)

#print axioms fixedInitialCandidate_fintype_card_le_222
#print axioms fixedInitialCandidate_terminalSubtotal_le_222
#print axioms prefixAveragedFixedInitialCandidate_terminalSubtotal_le_222
#print axioms prefixAveragedFixedInitialCandidate_terminalSubtotal_le_240

end AspisV5TerminalFixedInitialListSecurity
