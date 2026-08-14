import AspisFormal.V5FiatShamirAdaptiveQueryBudget
import AspisFormal.V5FriForwardDoomSoundness

/-!
# Adaptive query accounting for the forward FRI event

`V5FriForwardDoomSoundness` replaces the backwards suffix-conditioned event
with four bad sets fixed at the real transcript checkpoints.  This file puts
that forward event into the generic adaptive fresh-oracle experiment.

The adversary may choose a different causal transcript family after every
earlier completed attempt.  It may not choose the current attempt's family
after seeing that attempt's fresh four-challenge answer.  Under that timing
condition, `attempts` trials cost at most `attempts` times the raw one-trial
bound.

The final production theorem deliberately retains one explicit connection.
It must account for SHA-256, Fiat--Shamir programmability, repeated queries,
rejection sampling, interleaving, and the map from a Rust accepting run to
completed fresh attempts.  Proof of work is not used to divide the raw bound.
-/

namespace AspisV5FriForwardAdaptiveQueryBudget

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FiatShamirAdaptiveQueryBudget
open AspisV5FriAdaptiveUnmatched
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriFixedFamilyExperiment
open AspisV5FriForwardDoomSoundness
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5FriRoundByRoundSoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- At each completed-attempt history, choose the causal family for the next
attempt before its fresh four-challenge answer is sampled. -/
structure ForwardAdaptiveFriAttemptPlan (K : Type*) where
  familyAt : List (FourChallenges K) → CausalTranscriptFamily K

/-- The actual prefix-timed bad challenge tuples selected at each adaptive
attempt. -/
noncomputable def ForwardAdaptiveFriAttemptPlan.toFreshOraclePlan
    (plan : ForwardAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    AdaptiveFreshOraclePlan (FourChallenges K) where
  badAt history :=
    prefixBadChallengeTuples
      (releasedForwardBadSets base (plan.familyAt history) hfinal htables
        hpublished)

/-- Every forward event chosen at a transcript checkpoint has the released
raw one-attempt bound. -/
theorem forwardAdaptiveFriPlan_everyFreshBadSetBounded
    (plan : ForwardAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    EveryFreshBadSetBounded
      (plan.toFreshOraclePlan base hfinal htables hpublished)
      (releasedFriRawPerAttemptBound (K := K)) := by
  intro history
  have h := releasedForwardBadProbability_le base (plan.familyAt history)
    hfinal htables hpublished
  change
    ((prefixBadChallengeTuples
      (releasedForwardBadSets base (plan.familyAt history) hfinal htables
        hpublished)).card : Rat) /
        Fintype.card (FourChallenges K) ≤
      releasedFriRawPerAttemptBound (K := K)
  rw [show Fintype.card (FourChallenges K) = Fintype.card K ^ 4 by
    simp [FourChallenges, pow_succ]]
  exact h

/-- Raw adaptive bound for the forward, prefix-timed released FRI event. -/
theorem adaptiveForwardReleasedFriFailureProbability_le_attempts_mul
    (plan : ForwardAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (attempts : Nat) :
    adaptiveFailureProbabilityFromStart
        (plan.toFreshOraclePlan base hfinal htables hpublished) attempts ≤
      (attempts : Rat) * releasedFriRawPerAttemptBound (K := K) := by
  exact adaptiveFailureProbabilityFromStart_le_attempts_mul _ _
    releasedFriRawPerAttemptBound_nonnegative
    (forwardAdaptiveFriPlan_everyFreshBadSetBounded plan base hfinal htables
      hpublished) attempts

/-- The same theorem using a proved upper bound on completed fresh attempts. -/
theorem adaptiveForwardReleasedFriFailureProbability_le_queryBudget_mul
    (plan : ForwardAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (attempts freshQueryBudget : Nat)
    (hattempts : attempts ≤ freshQueryBudget) :
    adaptiveFailureProbabilityFromStart
        (plan.toFreshOraclePlan base hfinal htables hpublished) attempts ≤
      (freshQueryBudget : Rat) * releasedFriRawPerAttemptBound (K := K) := by
  exact adaptiveFailureProbabilityFromStart_le_queryBudget_mul _ _
    releasedFriRawPerAttemptBound_nonnegative
    (forwardAdaptiveFriPlan_everyFreshBadSetBounded plan base hfinal htables
      hpublished) attempts freshQueryBudget hattempts

/-- Production endpoint for the forward event.  All pure FRI counting and
adaptive bad-set timing are discharged; `connection` is exactly the remaining
SHA-256/Fiat--Shamir and Rust-execution reduction. -/
theorem productionForwardReleasedFriFailureProbability_le_queryBudget_mul_add_gap
    {Coins : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (productionFailure : Finset Coins)
    (plan : ForwardAdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (completedAttempts freshQueryBudget : Nat)
    (hashAndSamplingGap : Rat)
    (connection : ProductionAdaptiveFreshOracleConnection Coins
      (FourChallenges K) productionFailure
      (plan.toFreshOraclePlan base hfinal htables hpublished)
      completedAttempts freshQueryBudget hashAndSamplingGap) :
    finiteUniformEventProbability productionFailure ≤
      (freshQueryBudget : Rat) * releasedFriRawPerAttemptBound (K := K) +
        hashAndSamplingGap := by
  exact productionFailureProbability_le_queryBudget_mul_add_gap
    productionFailure
    (plan.toFreshOraclePlan base hfinal htables hpublished)
    completedAttempts freshQueryBudget
    (releasedFriRawPerAttemptBound (K := K)) hashAndSamplingGap
    releasedFriRawPerAttemptBound_nonnegative
    (forwardAdaptiveFriPlan_everyFreshBadSetBounded plan base hfinal htables
      hpublished)
    connection

#print axioms forwardAdaptiveFriPlan_everyFreshBadSetBounded
#print axioms adaptiveForwardReleasedFriFailureProbability_le_attempts_mul
#print axioms adaptiveForwardReleasedFriFailureProbability_le_queryBudget_mul
#print axioms
  productionForwardReleasedFriFailureProbability_le_queryBudget_mul_add_gap

end AspisV5FriForwardAdaptiveQueryBudget
