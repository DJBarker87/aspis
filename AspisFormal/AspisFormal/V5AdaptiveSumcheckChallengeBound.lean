import AspisFormal.V5AcceptedSumcheckSourceBridge
import AspisFormal.V5FiatShamirAdaptiveQueryBudget

/-!
# Adaptive bound for the ten sumcheck challenges

The accepted-sumcheck proof shows that a wrong initial claim repaired by the
final opening must make two distinct degree-at-most-27 messages agree at one
of ten challenges. A malicious prover may choose each new message after
seeing all earlier challenges. This file proves the corresponding adaptive
count directly.

At a transcript prefix, the claimed and reference messages are fixed before
the next answer. If they differ, their equality set contains at most 27 field
elements; if they agree, that prefix contributes no repair event. The generic
fresh-oracle theorem therefore gives a total bound of `270 / |K|` for ten
rounds, without assuming that the ten bad sets are independent.

The last theorem keeps the production boundary explicit. Applying this
finite-field result to SHA-256 still requires a reduction showing that the ten
source challenges behave as fresh, domain-separated uniform field answers,
apart from a separately measured hash/sampling gap.
-/

namespace AspisV5AdaptiveSumcheckChallengeBound

open AspisSumcheckMasking
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5FiatShamirAdaptiveQueryBudget

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The two degree-27 messages selected at each prefix. Both may depend on
all earlier field answers; neither receives the current fresh answer. -/
structure AdaptiveDegree27MessagePlan (K : Type*) where
  claimedAt : List K → Degree27Message K
  referenceAt : List K → Degree27Message K

/-- The repair set fixed at one prefix. Equal messages cannot witness a
nonzero-polynomial repair, so that branch is the empty set. -/
noncomputable def AdaptiveDegree27MessagePlan.badAt
    (plan : AdaptiveDegree27MessagePlan K) (history : List K) : Finset K := by
  classical
  exact if plan.claimedAt history = plan.referenceAt history then ∅
    else degree27CollisionSet (plan.claimedAt history)
      (plan.referenceAt history)

/-- View the ten-round strategy as the generic fresh-oracle experiment. -/
noncomputable def AdaptiveDegree27MessagePlan.toFreshOraclePlan
    (plan : AdaptiveDegree27MessagePlan K) : AdaptiveFreshOraclePlan K where
  badAt := plan.badAt

/-- Distinct prefix-fixed messages that agree at the current answer place that
answer in the plan's bad set. -/
theorem AdaptiveDegree27MessagePlan.mem_badAt_of_evaluations_equal
    (plan : AdaptiveDegree27MessagePlan K) (history : List K) (answer : K)
    (different : plan.claimedAt history ≠ plan.referenceAt history)
    (evaluationsEqual :
      coeffEval (plan.claimedAt history) answer =
        coeffEval (plan.referenceAt history) answer) :
    answer ∈ plan.badAt history := by
  classical
  simp [AdaptiveDegree27MessagePlan.badAt, different,
    degree27CollisionSet, evaluationsEqual]

/-- Every prefix-fixed bad set has fresh mass at most `27 / |K|`. -/
theorem AdaptiveDegree27MessagePlan.everyFreshBadSetBounded
    (plan : AdaptiveDegree27MessagePlan K) :
    EveryFreshBadSetBounded plan.toFreshOraclePlan
      ((27 : Rat) / Fintype.card K) := by
  intro history
  classical
  by_cases equal : plan.claimedAt history = plan.referenceAt history
  · change ((plan.badAt history).card : Rat) / Fintype.card K ≤
        (27 : Rat) / Fintype.card K
    rw [AdaptiveDegree27MessagePlan.badAt, if_pos equal]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity
  · simpa [AdaptiveDegree27MessagePlan.toFreshOraclePlan,
      AdaptiveDegree27MessagePlan.badAt, equal,
      uniformDegree27CollisionProbability] using
      (uniformDegree27CollisionProbability_le
        (plan.claimedAt history) (plan.referenceAt history) equal)

/-- Exact ideal probability of hitting one of the adaptively selected repair
sets during the ten rounds. -/
noncomputable def adaptiveTenRoundRepairProbability
    (plan : AdaptiveDegree27MessagePlan K) : Rat :=
  adaptiveFailureProbabilityFromStart plan.toFreshOraclePlan 10

/-- Ten adaptive degree-27 rounds cost at most `270 / |K|`. Later bad sets
may depend arbitrarily on all previous answers. -/
theorem adaptiveTenRoundRepairProbability_le
    (plan : AdaptiveDegree27MessagePlan K) :
    adaptiveTenRoundRepairProbability plan ≤
      (270 : Rat) / Fintype.card K := by
  have nonnegative : (0 : Rat) ≤
      (27 : Rat) / Fintype.card K := by positivity
  calc
    adaptiveTenRoundRepairProbability plan ≤
        (10 : Rat) * ((27 : Rat) / Fintype.card K) :=
      adaptiveFailureProbabilityFromStart_le_attempts_mul
        plan.toFreshOraclePlan ((27 : Rat) / Fintype.card K)
        nonnegative plan.everyFreshBadSetBounded 10
    _ = (270 : Rat) / Fintype.card K := by ring

/-! ## Connecting one accepted wire to a causal message plan -/

/-- The challenges strictly before `round`, in source order. -/
def challengeHistory (point : Fin 10 → K) (round : Fin 10) : List K :=
  List.ofFn fun earlier : Fin round.val ↦
    point ⟨earlier.val, lt_trans earlier.isLt round.isLt⟩

omit [Field K] [Fintype K] [DecidableEq K] in
@[simp] theorem challengeHistory_length
    (point : Fin 10 → K) (round : Fin 10) :
    (challengeHistory point round).length = round.val := by
  simp [challengeHistory]

/-- The exact causality obligation for using the adaptive count on one
accepted wire and one fixed-oracle reference trace. It says that each pair
of messages is determined by the earlier challenges, before the current
challenge is sampled. -/
structure WireUsesAdaptiveDegree27Plan
    {Public Root : Type*}
    {scheme : AspisV5SumcheckTranscriptBinding.FiatShamirSchedule Public Root K}
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (reference : FixedOracleTenRoundTrace table wire.transcript.point)
    (plan : AdaptiveDegree27MessagePlan K) : Prop where
  claimedAt : ∀ round,
    plan.claimedAt (challengeHistory wire.transcript.point round) =
      wire.transcript.messages round
  referenceAt : ∀ round,
    plan.referenceAt (challengeHistory wire.transcript.point round) =
      reference.messages round

/-- A repair in a concrete accepted round hits the bad set chosen from the
strictly earlier challenge prefix. -/
theorem roundRepair_hits_adaptive_badSet
    {Public Root : Type*}
    {scheme : AspisV5SumcheckTranscriptBinding.FiatShamirSchedule Public Root K}
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (reference : FixedOracleTenRoundTrace table wire.transcript.point)
    (plan : AdaptiveDegree27MessagePlan K)
    (causal : WireUsesAdaptiveDegree27Plan wire reference plan)
    (round : Fin 10) (repair : RoundRepair wire reference round) :
    wire.transcript.point round ∈
      plan.badAt (challengeHistory wire.transcript.point round) := by
  apply plan.mem_badAt_of_evaluations_equal
  · rw [causal.claimedAt round, causal.referenceAt round]
    exact roundRepair_messages_different wire reference round repair
  · rw [causal.claimedAt round, causal.referenceAt round]
    have collision := roundRepair_mem_degree27CollisionSet
      wire reference round repair
    exact (Finset.mem_filter.mp collision).2

/-- The complete ten-round repair event therefore hits one of the ten
prefix-selected bad sets. -/
theorem tenRoundRepair_hits_adaptive_badSet
    {Public Root : Type*}
    {scheme : AspisV5SumcheckTranscriptBinding.FiatShamirSchedule Public Root K}
    (wire : AcceptedProductionTenRoundWire scheme)
    {table : Fin 1024 → K}
    (reference : FixedOracleTenRoundTrace table wire.transcript.point)
    (plan : AdaptiveDegree27MessagePlan K)
    (causal : WireUsesAdaptiveDegree27Plan wire reference plan)
    (repair : TenRoundRepair wire reference) :
    ∃ round : Fin 10, wire.transcript.point round ∈
      plan.badAt (challengeHistory wire.transcript.point round) := by
  rcases repair with ⟨round, repaired⟩
  exact ⟨round,
    roundRepair_hits_adaptive_badSet wire reference plan causal round repaired⟩

/-! ## Explicit production-to-fresh-oracle boundary -/

/-- What remains to transfer a concrete finite production event to the ideal
ten-answer experiment. Its probability comparison includes the complete
SHA-256, field-sampling, freshness, and source-correspondence loss. -/
abbrev ProductionTenRoundRepairConnection
    (Coins : Type*) [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (productionFailure : Finset Coins)
    (plan : AdaptiveDegree27MessagePlan K)
    (hashAndSamplingGap : Rat) : Prop :=
  ProductionAdaptiveFreshOracleConnection Coins K productionFailure
    plan.toFreshOraclePlan 10 10 hashAndSamplingGap

/-- Once that explicit production reduction is supplied, the concrete repair
event costs at most `270 / |K|` plus the stated hash/sampling gap. -/
theorem productionTenRoundRepairProbability_le
    {Coins : Type*} [Fintype Coins] [DecidableEq Coins] [Nonempty Coins]
    (productionFailure : Finset Coins)
    (plan : AdaptiveDegree27MessagePlan K)
    (hashAndSamplingGap : Rat)
    (connection : ProductionTenRoundRepairConnection Coins
      productionFailure plan hashAndSamplingGap) :
    AspisV5FriFixedFamilyExperiment.finiteUniformEventProbability
        productionFailure ≤
      (270 : Rat) / Fintype.card K + hashAndSamplingGap := by
  have nonnegative : (0 : Rat) ≤
      (27 : Rat) / Fintype.card K := by positivity
  calc
    AspisV5FriFixedFamilyExperiment.finiteUniformEventProbability
        productionFailure ≤
        (10 : Rat) * ((27 : Rat) / Fintype.card K) +
          hashAndSamplingGap :=
      productionFailureProbability_le_queryBudget_mul_add_gap
        productionFailure plan.toFreshOraclePlan 10 10
        ((27 : Rat) / Fintype.card K) hashAndSamplingGap nonnegative
        plan.everyFreshBadSetBounded connection
    _ = (270 : Rat) / Fintype.card K + hashAndSamplingGap := by ring

#print axioms AdaptiveDegree27MessagePlan.mem_badAt_of_evaluations_equal
#print axioms AdaptiveDegree27MessagePlan.everyFreshBadSetBounded
#print axioms adaptiveTenRoundRepairProbability_le
#print axioms roundRepair_hits_adaptive_badSet
#print axioms tenRoundRepair_hits_adaptive_badSet
#print axioms productionTenRoundRepairProbability_le

end AspisV5AdaptiveSumcheckChallengeBound
