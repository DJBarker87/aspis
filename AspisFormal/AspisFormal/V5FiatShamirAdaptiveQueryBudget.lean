import AspisFormal.V5FriFixedFamilyExperiment

/-!
# Adaptive Fiat--Shamir query accounting

The fixed-family FRI count applies after one causal response family has been
chosen and before its four fresh challenges are sampled.  A malicious prover
does not have to use the same family on every attempt: it may choose the next
family after seeing every earlier random-oracle answer.

This file models that adaptivity directly.  At each node, `badAt history` is
fixed before the next fresh answer is drawn; after that answer, the next node
may depend on the entire enlarged history.  The exact recursive probability
of ever hitting a bad set is at most

```
number of fresh attempts * per-attempt bad probability.
```

No independence between different attempts is assumed.  The timing condition
is the essential one: the current bad set may depend on earlier answers but
not on the current fresh answer.

The released-FRI specialization lets each attempt choose an arbitrary
`CausalTranscriptFamily` from the preceding challenge tuples.  Thus it covers
adaptive choice across attempts and the already-modelled causal choice within
each four-round FRI attempt.

This is an ideal fresh-oracle theorem.  The final section gives an explicit
production boundary.  Connecting SHA-256 calls, rejection sampling, repeated
queries, domain separation, interleaved attempts, and the accepted Rust run to
this ideal experiment remains a computational reduction premise.  The bound
here is a raw success probability and is never divided by proof-of-work.
-/

namespace AspisV5FiatShamirAdaptiveQueryBudget

open AspisCircleGroupOrder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAdaptiveUnmatched
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriFixedFamilyExperiment
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry

/-! ## A generic adaptive fresh-oracle experiment -/

/-- An adaptive strategy for choosing the bad set tested by the next fresh
oracle answer.  The complete list of *earlier* answers is available.  The
fresh answer itself is not an argument to `badAt`, which records the timing
condition needed by the counting proof. -/
structure AdaptiveFreshOraclePlan (Answer : Type*) where
  badAt : List Answer -> Finset Answer

/-- Exact failure probability for `attempts` remaining independent uniform
fresh answers, conditional on `history`.

If the current answer is bad, the run has failed.  Otherwise the experiment
continues and the plan may adapt to that answer. -/
noncomputable def adaptiveFailureProbability
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (plan : AdaptiveFreshOraclePlan Answer) : Nat -> List Answer -> Rat
  | 0, _ => 0
  | attempts + 1, history =>
      let bad := plan.badAt history
      (bad.card : Rat) / Fintype.card Answer +
        (Finset.univ.filter (fun answer => answer ∉ bad)).sum
            (fun answer =>
              adaptiveFailureProbability plan attempts (history ++ [answer])) /
          Fintype.card Answer

/-- The same experiment from the empty oracle history. -/
noncomputable def adaptiveFailureProbabilityFromStart
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer]
    (plan : AdaptiveFreshOraclePlan Answer) (attempts : Nat) : Rat :=
  adaptiveFailureProbability plan attempts []

/-- Every adaptively selected bad set has probability at most `epsilon` under
one fresh uniform answer.  This is a node-by-node condition over every
possible prior history, not an independence claim about the eventual run. -/
def EveryFreshBadSetBounded
    {Answer : Type*} [Fintype Answer]
    (plan : AdaptiveFreshOraclePlan Answer) (epsilon : Rat) : Prop :=
  forall history,
    ((plan.badAt history).card : Rat) / Fintype.card Answer <= epsilon

theorem adaptiveFailureProbability_nonnegative
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]
    (plan : AdaptiveFreshOraclePlan Answer) :
    forall attempts history,
      0 <= adaptiveFailureProbability plan attempts history := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      simp [adaptiveFailureProbability]
  | succ attempts ih =>
      intro history
      rw [adaptiveFailureProbability]
      have hcard : (0 : Rat) < Fintype.card Answer := by
        exact_mod_cast Fintype.card_pos
      have hbad : (0 : Rat) <=
          ((plan.badAt history).card : Rat) / Fintype.card Answer := by
        positivity
      have hsum : (0 : Rat) <=
          (Finset.univ.filter
              (fun answer => answer ∉ plan.badAt history)).sum
            (fun answer => adaptiveFailureProbability plan attempts
              (history ++ [answer])) := by
        exact Finset.sum_nonneg fun answer _ => ih (history ++ [answer])
      exact add_nonneg hbad (div_nonneg hsum hcard.le)

/-- **Adaptive fresh-query union bound.**  The bad set at every attempt may be
an arbitrary function of all earlier answers.  If every such set has fresh
probability at most `epsilon`, then `attempts` adaptive attempts fail with
probability at most `attempts * epsilon`.

There is no independence assumption between the adaptively selected bad sets.
Independence is used only for the next fresh uniform answer represented by the
recursive average in `adaptiveFailureProbability`. -/
theorem adaptiveFailureProbability_le_attempts_mul
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]
    (plan : AdaptiveFreshOraclePlan Answer) (epsilon : Rat)
    (hepsilon : 0 <= epsilon)
    (hnodes : EveryFreshBadSetBounded plan epsilon) :
    forall attempts history,
      adaptiveFailureProbability plan attempts history <=
        (attempts : Rat) * epsilon := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      simp [adaptiveFailureProbability]
  | succ attempts ih =>
      intro history
      rw [adaptiveFailureProbability]
      let good : Finset Answer :=
        Finset.univ.filter (fun answer => answer ∉ plan.badAt history)
      have hanswerCard : (0 : Rat) < Fintype.card Answer := by
        exact_mod_cast Fintype.card_pos
      have hchildren :
          good.sum (fun answer => adaptiveFailureProbability plan attempts
            (history ++ [answer])) <=
            good.sum (fun _ => (attempts : Rat) * epsilon) := by
        exact Finset.sum_le_sum fun answer _ => ih (history ++ [answer])
      have hgoodCardNat : good.card <= Fintype.card Answer :=
        Finset.card_le_univ good
      have hgoodCard : (good.card : Rat) <= Fintype.card Answer := by
        exact_mod_cast hgoodCardNat
      have hmulNonnegative : 0 <= (attempts : Rat) * epsilon :=
        mul_nonneg (by positivity) hepsilon
      have hsum :
          good.sum (fun answer => adaptiveFailureProbability plan attempts
            (history ++ [answer])) <=
            (Fintype.card Answer : Rat) * ((attempts : Rat) * epsilon) := by
        calc
          good.sum (fun answer => adaptiveFailureProbability plan attempts
              (history ++ [answer]))
              <= good.sum (fun _ => (attempts : Rat) * epsilon) := hchildren
          _ = (good.card : Rat) * ((attempts : Rat) * epsilon) := by simp
          _ <= (Fintype.card Answer : Rat) *
              ((attempts : Rat) * epsilon) :=
            mul_le_mul_of_nonneg_right hgoodCard hmulNonnegative
      have haverage :
          good.sum (fun answer => adaptiveFailureProbability plan attempts
              (history ++ [answer])) / Fintype.card Answer <=
            (attempts : Rat) * epsilon := by
        rw [div_le_iff₀ hanswerCard]
        calc
          good.sum (fun answer => adaptiveFailureProbability plan attempts
              (history ++ [answer]))
              <= (Fintype.card Answer : Rat) *
                  ((attempts : Rat) * epsilon) := hsum
          _ = ((attempts : Rat) * epsilon) * Fintype.card Answer := by ring
      calc
        ((plan.badAt history).card : Rat) / Fintype.card Answer +
              good.sum (fun answer => adaptiveFailureProbability plan attempts
                (history ++ [answer])) / Fintype.card Answer
            <= epsilon + (attempts : Rat) * epsilon :=
          add_le_add (hnodes history) haverage
        _ = (Nat.succ attempts : Rat) * epsilon := by
          push_cast
          ring

/-- Starting from no prior queries, the same adaptive bound holds. -/
theorem adaptiveFailureProbabilityFromStart_le_attempts_mul
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]
    (plan : AdaptiveFreshOraclePlan Answer) (epsilon : Rat)
    (hepsilon : 0 <= epsilon)
    (hnodes : EveryFreshBadSetBounded plan epsilon)
    (attempts : Nat) :
    adaptiveFailureProbabilityFromStart plan attempts <=
      (attempts : Rat) * epsilon :=
  adaptiveFailureProbability_le_attempts_mul plan epsilon hepsilon hnodes
    attempts []

/-- A stated upper bound on the number of completed fresh attempts can replace
the actual attempt count. -/
theorem adaptiveFailureProbabilityFromStart_le_queryBudget_mul
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]
    (plan : AdaptiveFreshOraclePlan Answer) (epsilon : Rat)
    (hepsilon : 0 <= epsilon)
    (hnodes : EveryFreshBadSetBounded plan epsilon)
    (attempts freshQueryBudget : Nat)
    (hattempts : attempts <= freshQueryBudget) :
    adaptiveFailureProbabilityFromStart plan attempts <=
      (freshQueryBudget : Rat) * epsilon := by
  refine (adaptiveFailureProbabilityFromStart_le_attempts_mul plan epsilon
    hepsilon hnodes attempts).trans ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hattempts) hepsilon

/-! ## Why post-selection after the current answer is not covered -/

/-- If a prover is allowed to choose its alleged size-one bad set *after*
seeing the current answer, it can choose the singleton containing that answer. -/
def postselectedSingleton
    {Answer : Type*} [DecidableEq Answer] (answer : Answer) : Finset Answer :=
  {answer}

@[simp] theorem postselectedSingleton_card
    {Answer : Type*} [DecidableEq Answer] (answer : Answer) :
    (postselectedSingleton answer).card = 1 := by
  simp [postselectedSingleton]

@[simp] theorem answer_mem_postselectedSingleton
    {Answer : Type*} [DecidableEq Answer] (answer : Answer) :
    answer ∈ postselectedSingleton answer := by
  simp [postselectedSingleton]

/-- Despite every post-selected set having cardinality one, the response is in
its post-selected set for every possible response.  Therefore a fixed-set
count cannot be applied when the proof/bad set is selected after the same
challenge being counted. -/
theorem postselectedSingleton_success_set_is_univ
    {Answer : Type*} [Fintype Answer] [DecidableEq Answer] :
    Finset.univ.filter (fun answer => answer ∈ postselectedSingleton answer) =
      (Finset.univ : Finset Answer) := by
  ext answer
  simp

/-! ## Released FRI specialization -/

section ReleasedFri

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- Across completed FRI attempts, the adversary may choose a different
causal transcript family as an arbitrary function of all earlier four-tuples.
The current four-tuple is not available when `familyAt` is evaluated. -/
structure AdaptiveFriAttemptPlan (K : Type*) where
  familyAt : List (FourChallenges K) -> CausalTranscriptFamily K

/-- The exact released fixed-family bad set selected at each adaptive attempt. -/
noncomputable def AdaptiveFriAttemptPlan.toFreshOraclePlan
    (plan : AdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    AdaptiveFreshOraclePlan (FourChallenges K) where
  badAt history :=
    fixedFamilyBadChallengeTuples base (plan.familyAt history) hfinal htables
      hpublished

/-- Raw one-attempt FRI fibre bound.  There is deliberately no grinding/work
divisor in this definition. -/
noncomputable def releasedFriRawPerAttemptBound : Rat :=
  (releasedChallengeCap 0 + releasedChallengeCap 1 +
    releasedChallengeCap 2 + releasedChallengeCap 3 : Rat) /
      Fintype.card K

theorem releasedFriRawPerAttemptBound_nonnegative :
    (0 : Rat) <= releasedFriRawPerAttemptBound (K := K) := by
  unfold releasedFriRawPerAttemptBound
  positivity

/-- Every adaptively selected released FRI family satisfies the already
proved exact four-fibre bound at the moment it is selected. -/
theorem adaptiveFriPlan_everyFreshBadSetBounded
    (plan : AdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)) :
    EveryFreshBadSetBounded
      (plan.toFreshOraclePlan base hfinal htables hpublished)
      (releasedFriRawPerAttemptBound (K := K)) := by
  intro history
  have h := fixedFamilyUniformBadProbability_le base
    (plan.familyAt history) hfinal htables hpublished
  change
    ((fixedFamilyBadChallengeTuples base (plan.familyAt history) hfinal htables
        hpublished).card : Rat) /
        Fintype.card (FourChallenges K) <=
      releasedFriRawPerAttemptBound (K := K)
  rw [show Fintype.card (FourChallenges K) = Fintype.card K ^ 4 by
    simp [FourChallenges, pow_succ]]
  exact h

/-- **Raw adaptive released-FRI bound.**  The prover may change its causal FRI
family after every preceding attempt.  For `attempts` fresh independent
four-challenge tuples, its chance of ever hitting the counted FRI fibre is at
most `attempts` times the raw one-attempt bound. -/
theorem adaptiveReleasedFriFailureProbability_le_attempts_mul
    (plan : AdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (attempts : Nat) :
    adaptiveFailureProbabilityFromStart
        (plan.toFreshOraclePlan base hfinal htables hpublished) attempts <=
      (attempts : Rat) * releasedFriRawPerAttemptBound (K := K) := by
  exact adaptiveFailureProbabilityFromStart_le_attempts_mul _ _
    releasedFriRawPerAttemptBound_nonnegative
    (adaptiveFriPlan_everyFreshBadSetBounded plan base hfinal htables
      hpublished) attempts

/-- The same raw bound stated with an external budget on completed fresh
four-challenge attempts.  A SHA-256 query budget may safely be used only after
a separate production reduction proves that each modeled attempt consumes a
fresh, correctly domain-separated oracle query (and handles repeats and
rejection sampling). -/
theorem adaptiveReleasedFriFailureProbability_le_queryBudget_mul
    (plan : AdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (attempts freshQueryBudget : Nat)
    (hattempts : attempts <= freshQueryBudget) :
    adaptiveFailureProbabilityFromStart
        (plan.toFreshOraclePlan base hfinal htables hpublished) attempts <=
      (freshQueryBudget : Rat) * releasedFriRawPerAttemptBound (K := K) := by
  exact adaptiveFailureProbabilityFromStart_le_queryBudget_mul _ _
    releasedFriRawPerAttemptBound_nonnegative
    (adaptiveFriPlan_everyFreshBadSetBounded plan base hfinal htables
      hpublished) attempts freshQueryBudget hattempts

end ReleasedFri

/-! ## Explicit production/SHA-256 boundary -/

/-- What a real SHA-256/Fiat--Shamir reduction must establish before the ideal
adaptive query theorem can be applied to a production event.

`hashAndSamplingGap` may include SHA-256/random-oracle distinguishing,
implementation/specification divergence, rejection-sampling effects not
captured by the ideal answer type, repeated-query handling, and any loss in
mapping an interleaved production transcript to completed fresh attempts.

The crucial probability comparison is a field, not a theorem in this file.
Consequently this interface does not claim that the deployed verifier already
has a proved Fiat--Shamir reduction. -/
structure ProductionAdaptiveFreshOracleConnection
    (Coins Answer : Type*)
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]
    (productionFailure : Finset Coins)
    (plan : AdaptiveFreshOraclePlan Answer)
    (completedAttempts freshQueryBudget : Nat)
    (hashAndSamplingGap : Rat) : Prop where
  completedAttempts_le_budget : completedAttempts <= freshQueryBudget
  hashAndSamplingGap_nonnegative : 0 <= hashAndSamplingGap
  productionFailure_le_ideal_plus_gap :
    finiteUniformEventProbability productionFailure <=
      adaptiveFailureProbabilityFromStart plan completedAttempts +
        hashAndSamplingGap

/-- Once the explicit production reduction is supplied, a bounded adaptive
attacker inherits `queryBudget * epsilon`, plus the named hash/sampling gap.
This is raw probability accounting; there is no proof-of-work divisor. -/
theorem productionFailureProbability_le_queryBudget_mul_add_gap
    {Coins Answer : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]
    (productionFailure : Finset Coins)
    (plan : AdaptiveFreshOraclePlan Answer)
    (completedAttempts freshQueryBudget : Nat)
    (epsilon hashAndSamplingGap : Rat)
    (hepsilon : 0 <= epsilon)
    (hnodes : EveryFreshBadSetBounded plan epsilon)
    (connection : ProductionAdaptiveFreshOracleConnection Coins Answer
      productionFailure plan completedAttempts freshQueryBudget
      hashAndSamplingGap) :
    finiteUniformEventProbability productionFailure <=
      (freshQueryBudget : Rat) * epsilon + hashAndSamplingGap := by
  calc
    finiteUniformEventProbability productionFailure
        <= adaptiveFailureProbabilityFromStart plan completedAttempts +
            hashAndSamplingGap :=
      connection.productionFailure_le_ideal_plus_gap
    _ <= (freshQueryBudget : Rat) * epsilon + hashAndSamplingGap := by
      exact add_le_add_left
        (adaptiveFailureProbabilityFromStart_le_queryBudget_mul plan epsilon
          hepsilon hnodes completedAttempts freshQueryBudget
          connection.completedAttempts_le_budget)
        hashAndSamplingGap

/-- Released-FRI form of the production boundary.  The mathematical part of
the premise is discharged by the fixed-family count; the remaining
`connection` is precisely the SHA-256/Fiat--Shamir reduction still required
for a deployed claim. -/
theorem productionReleasedFriFailureProbability_le_queryBudget_mul_add_gap
    {Coins K : Type*}
    [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (productionFailure : Finset Coins)
    (friPlan : AdaptiveFriAttemptPlan K)
    (base : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain base)
    (htables : InverseTablesMatch base releasedEvaluationPoints)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (completedAttempts freshQueryBudget : Nat)
    (hashAndSamplingGap : Rat)
    (connection : ProductionAdaptiveFreshOracleConnection Coins
      (FourChallenges K) productionFailure
      (friPlan.toFreshOraclePlan base hfinal htables hpublished)
      completedAttempts freshQueryBudget hashAndSamplingGap) :
    finiteUniformEventProbability productionFailure <=
      (freshQueryBudget : Rat) * releasedFriRawPerAttemptBound (K := K) +
        hashAndSamplingGap := by
  exact productionFailureProbability_le_queryBudget_mul_add_gap
    productionFailure
    (friPlan.toFreshOraclePlan base hfinal htables hpublished)
    completedAttempts freshQueryBudget
    (releasedFriRawPerAttemptBound (K := K)) hashAndSamplingGap
    releasedFriRawPerAttemptBound_nonnegative
    (adaptiveFriPlan_everyFreshBadSetBounded friPlan base hfinal htables
      hpublished)
    connection

#print axioms adaptiveFailureProbability_nonnegative
#print axioms adaptiveFailureProbability_le_attempts_mul
#print axioms adaptiveFailureProbabilityFromStart_le_queryBudget_mul
#print axioms postselectedSingleton_success_set_is_univ
#print axioms adaptiveFriPlan_everyFreshBadSetBounded
#print axioms adaptiveReleasedFriFailureProbability_le_attempts_mul
#print axioms adaptiveReleasedFriFailureProbability_le_queryBudget_mul
#print axioms productionFailureProbability_le_queryBudget_mul_add_gap
#print axioms productionReleasedFriFailureProbability_le_queryBudget_mul_add_gap

end AspisV5FiatShamirAdaptiveQueryBudget
