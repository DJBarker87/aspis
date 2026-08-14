import AspisFormal.V5AcceptedExecutionReleasedSecurity
import AspisFormal.V5FinalSecurityAccounting

/-!
# Final accounting for the released accepted-execution theorem

`V5AcceptedExecutionReleasedSecurity` removes four cases from the general
accepted-execution result: the two released-table predicates, failure to
construct one causal backwards strategy, and absence of the published
decoding theorem.  This file connects exactly the fourteen remaining cases
to `V5FinalSecurityAccounting`.

The counted FRI case is deliberately not an arbitrary predicate and does not
quantify over a response strategy.  It is the bad-set event for
`constructedAdaptiveStrategies`, with one fixed released schedule and one
fixed causal transcript family.  The final four FRI probability bounds remain
the explicit assumptions already recorded by `AssumedFinalSecurityBounds`;
this file neither changes nor instantiates those assumptions.
-/

namespace AspisV5AcceptedExecutionReleasedFinalAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FinalSecurityAccounting
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry

/-! ## The exact constructed-strategy FRI event -/

/-- One fixed released FRI experiment inside a larger security experiment.

The four challenge projections may read the experiment's coins.  The schedule
and causal transcript family are fixed, and the response strategy is not a
field: `ConstructedFriExperiment.event` below always uses the strategy
constructed in Lean. -/
structure ConstructedFriExperiment
    (Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] where
  base : FixedSchedule (ZMod P) K
  family : CausalTranscriptFamily K
  finalDomain : FinalXMatchesReleasedDomain base
  inverseTables : InverseTablesMatch base releasedEvaluationPoints
  publishedDecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)
  round0Challenge : Coins -> K
  round1Challenge : Coins -> K
  round2Challenge : Coins -> K
  round3Challenge : Coins -> K

/-- The exact counted FRI event for the single globally constructed strategy.
There is intentionally no strategy argument or existential quantifier here. -/
def ConstructedFriExperiment.event
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : ConstructedFriExperiment Coins K) : Set Coins :=
  {coins |
    (adaptiveBadSets experiment.base experiment.family
      experiment.finalDomain experiment.inverseTables
      experiment.publishedDecoding
      (constructedAdaptiveStrategies experiment.base experiment.family)).Occurs
        (experiment.round0Challenge coins)
        (experiment.round1Challenge coins)
        (experiment.round2Challenge coins)
        (experiment.round3Challenge coins)}

/-- The proof witnesses packaged by the released accepted-execution theorem
identify the same fixed event.  Only proofs of the released table and decoding
facts are existentially packaged there; the response strategy itself is still
the single `constructedAdaptiveStrategies` value. -/
theorem ConstructedFriExperiment.mem_event_of_exists_evidence
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (experiment : ConstructedFriExperiment Coins K) (coins : Coins)
    (occurs :
      ∃ (hfinal : FinalXMatchesReleasedDomain experiment.base)
          (htables : InverseTablesMatch experiment.base
            releasedEvaluationPoints)
          (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
        (adaptiveBadSets experiment.base experiment.family hfinal htables
          hpublished
          (constructedAdaptiveStrategies experiment.base
            experiment.family)).Occurs
          (experiment.round0Challenge coins)
          (experiment.round1Challenge coins)
          (experiment.round2Challenge coins)
          (experiment.round3Challenge coins)) :
    coins ∈ experiment.event := by
  rcases occurs with ⟨hfinal, htables, hpublished, occurs⟩
  simpa only [ConstructedFriExperiment.event, Set.mem_setOf_eq] using occurs

/-! ## The fourteen released predicates -/

/-- The thirteen freely supplied predicates and the one exact constructed FRI
experiment returned by the released accepted-execution reduction. -/
structure ReleasedAcceptedExecutionFailurePredicates
    (Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] where
  sourceRelationProjection : Coins -> Prop
  familyProjection : Coins -> Prop
  transcriptProjection : Coins -> Prop
  workProjection : Coins -> Prop
  referenceForest : Coins -> Prop
  rustOpeningCorrespondence : Coins -> Prop
  merkleHashCollision : Coins -> Prop
  workCheck : Coins -> Prop
  friArithmetic : Coins -> Prop
  queryPhase : Coins -> Prop
  countedFri : ConstructedFriExperiment Coins K
  candidateTrace : Coins -> Prop
  relationRepair : Coins -> Prop
  poseidon : Coins -> Prop

/-- A coin outcome reaches one of the fourteen cases in
`ReleasedAcceptedExecutionSecurityEvent`. -/
def ReleasedAcceptedExecutionFailurePredicates.Occurs
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (failure : ReleasedAcceptedExecutionFailurePredicates Coins K)
    (coins : Coins) : Prop :=
  ReleasedAcceptedExecutionSecurityEvent
    (failure.sourceRelationProjection coins)
    (failure.familyProjection coins)
    (failure.transcriptProjection coins)
    (failure.workProjection coins)
    (failure.referenceForest coins)
    (failure.rustOpeningCorrespondence coins)
    (failure.merkleHashCollision coins)
    (failure.workCheck coins)
    (failure.friArithmetic coins)
    (failure.queryPhase coins)
    (coins ∈ failure.countedFri.event)
    (failure.candidateTrace coins)
    (failure.relationRepair coins)
    (failure.poseidon coins)

/-! ## Exact containment obligations -/

/-- Each of the fourteen released outcomes is assigned to an existing final
ledger event.  The exact constructed-strategy FRI event is assigned to the
union of the four already budgeted round events; it does not add a fifth FRI
term. -/
structure ReleasedAcceptedExecutionFailureCoverage
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : FinalSecurityEvents Coins)
    (failure : ReleasedAcceptedExecutionFailurePredicates Coins K) : Prop where
  sourceRelationProjection :
    {coins | failure.sourceRelationProjection coins} ⊆
      events.acceptedRunRelationBridge
  familyProjection :
    {coins | failure.familyProjection coins} ⊆
      events.acceptedRunRelationBridge
  transcriptProjection :
    {coins | failure.transcriptProjection coins} ⊆
      events.transcriptAndPrimitives.event .rustToLean
  workProjection :
    {coins | failure.workProjection coins} ⊆
      events.transcriptAndPrimitives.event .rustToLean
  referenceForest :
    {coins | failure.referenceForest coins} ⊆
      events.proofMerkleOpeningBridge
  rustOpeningCorrespondence :
    {coins | failure.rustOpeningCorrespondence coins} ⊆
      events.proofMerkleOpeningBridge
  merkleHashCollision :
    {coins | failure.merkleHashCollision coins} ⊆
      events.transcriptAndPrimitives.event .sha256Collision
  workCheck :
    {coins | failure.workCheck coins} ⊆
      events.acceptedRunRelationBridge
  friArithmetic :
    {coins | failure.friArithmetic coins} ⊆
      events.acceptedRunRelationBridge
  queryPhase :
    {coins | failure.queryPhase coins} ⊆ events.queryAndFinalWorkMiss
  countedFri :
    failure.countedFri.event ⊆
      events.friRound0 ∪ events.friRound1 ∪
        events.friRound2 ∪ events.friRound3
  candidateTrace :
    {coins | failure.candidateTrace coins} ⊆
      events.acceptedRunRelationBridge
  relationRepair :
    {coins | failure.relationRepair coins} ⊆ events.relationRepair
  poseidon :
    {coins | failure.poseidon coins} ⊆
      events.transcriptAndPrimitives.event .poseidon2ImplementationDivergence

/-! ## Deterministic and probability composition -/

/-- Every outcome of the fourteen-way released reduction lies in the final
ledger, provided the exact event-containment obligations above hold. -/
theorem released_accepted_execution_failure_subset_total
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (events : FinalSecurityEvents Coins)
    (failure : ReleasedAcceptedExecutionFailurePredicates Coins K)
    (coverage : ReleasedAcceptedExecutionFailureCoverage events failure) :
    {coins | failure.Occurs coins} ⊆ totalFinalFailure events := by
  intro coins occurs
  cases occurs with
  | sourceRelationProjection event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.sourceRelationProjection event)
  | familyProjection event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.familyProjection event)
  | transcriptProjection event =>
      exact one_final_failure_is_in_total events .transcriptRustToLean
        (coverage.transcriptProjection event)
  | workProjection event =>
      exact one_final_failure_is_in_total events .transcriptRustToLean
        (coverage.workProjection event)
  | releasedFinalDomain event => exact event.elim
  | releasedInverseTable event => exact event.elim
  | referenceForest event =>
      exact one_final_failure_is_in_total events .proofMerkleOpeningBridge
        (coverage.referenceForest event)
  | globalCausalSelection event => exact event.elim
  | rustOpeningCorrespondence event =>
      exact one_final_failure_is_in_total events .proofMerkleOpeningBridge
        (coverage.rustOpeningCorrespondence event)
  | merkleHashCollision event =>
      exact one_final_failure_is_in_total events .sha256Collision
        (coverage.merkleHashCollision event)
  | workCheck event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.workCheck event)
  | friArithmetic event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.friArithmetic event)
  | queryPhase event =>
      exact one_final_failure_is_in_total events .queryAndFinalWorkMiss
        (coverage.queryPhase event)
  | friFibre event =>
      have covered := coverage.countedFri event
      simp only [Set.mem_union] at covered
      rcases covered with ((event0 | event1) | event2) | event3
      · exact one_final_failure_is_in_total events .friRound0 event0
      · exact one_final_failure_is_in_total events .friRound1 event1
      · exact one_final_failure_is_in_total events .friRound2 event2
      · exact one_final_failure_is_in_total events .friRound3 event3
  | candidateTrace event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.candidateTrace event)
  | relationRepairEvent event =>
      exact one_final_failure_is_in_total events .relationRepair
        (coverage.relationRepair event)
  | poseidon event =>
      exact one_final_failure_is_in_total events
        .poseidon2ImplementationDivergence (coverage.poseidon event)
  | publishedDecoding event => exact event.elim

/-- Any attack already reduced to the fourteen-way released event inherits
the existing final bound.  The `2^-108` term is only the released arithmetic
subtotal; every external bridge, primitive, and runtime term remains in
`budget.total` and still requires `AssumedFinalSecurityBounds`. -/
theorem released_attack_probability_le_final_budget
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (failure : ReleasedAcceptedExecutionFailurePredicates Coins K)
    (attack : Set Coins)
    (attackReduces : attack ⊆ {coins | failure.Occurs coins})
    (coverage : ReleasedAcceptedExecutionFailureCoverage events failure)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget) :
    measure.real attack ≤ (1 : Real) / 2 ^ 108 + budget.total := by
  have covered : attack ⊆ totalFinalFailure events :=
    Set.Subset.trans attackReduces
      (released_accepted_execution_failure_subset_total events failure
        coverage)
  exact (MeasureTheory.measureReal_mono covered).trans
    (total_final_failure_probability_le_released_subtotal_plus_external
      measure events budget assumed)

#print axioms ConstructedFriExperiment.mem_event_of_exists_evidence
#print axioms released_accepted_execution_failure_subset_total
#print axioms released_attack_probability_le_final_budget

end AspisV5AcceptedExecutionReleasedFinalAccounting
