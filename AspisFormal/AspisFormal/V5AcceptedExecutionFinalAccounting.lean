import AspisFormal.V5AcceptedExecutionSecurityBridge
import AspisFormal.V5FinalSecurityAccounting

/-!
# Connecting accepted-execution failures to the final probability ledger

`V5AcceptedExecutionSecurityBridge` gives a deterministic eighteen-way result
for one false accepted source-shaped execution.  `V5FinalSecurityAccounting`
gives the non-duplicated probability ledger.  This file states the exact
containment obligations needed to connect those two results.

No containment is inferred merely from similar names.  In particular, the
query, four FRI, transcript, Merkle, Poseidon2, and relation-repair events must
be shown to be the same events used by the final experiment.  The remaining
source/model failures share the single accepted-run bridge budget.
-/

namespace AspisV5AcceptedExecutionFinalAccounting

open MeasureTheory
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5CryptographicAssumptions
open AspisV5FinalSecurityAccounting

/-! ## Pointwise failures returned by the deterministic theorem -/

/-- The eighteen propositions returned by the accepted-execution theorem,
made into predicates on the coins of one security experiment. -/
structure AcceptedExecutionFailurePredicates (Coins : Type*) where
  sourceRelationProjection : Coins -> Prop
  familyProjection : Coins -> Prop
  transcriptProjection : Coins -> Prop
  workProjection : Coins -> Prop
  releasedFinalDomain : Coins -> Prop
  releasedInverseTable : Coins -> Prop
  referenceForest : Coins -> Prop
  globalCausalSelection : Coins -> Prop
  rustOpeningCorrespondence : Coins -> Prop
  merkleHashCollision : Coins -> Prop
  workCheck : Coins -> Prop
  friArithmetic : Coins -> Prop
  queryPhase : Coins -> Prop
  countedFriFibre : Coins -> Prop
  candidateTrace : Coins -> Prop
  relationRepair : Coins -> Prop
  poseidon : Coins -> Prop
  publishedDecoding : Coins -> Prop

/-- A coin outcome reaches one constructor of the deterministic
accepted-execution result. -/
def AcceptedExecutionFailurePredicates.Occurs
    {Coins : Type*} (failure : AcceptedExecutionFailurePredicates Coins)
    (coins : Coins) : Prop :=
  AcceptedExecutionSecurityEvent
    (failure.sourceRelationProjection coins)
    (failure.familyProjection coins)
    (failure.transcriptProjection coins)
    (failure.workProjection coins)
    (failure.releasedFinalDomain coins)
    (failure.releasedInverseTable coins)
    (failure.referenceForest coins)
    (failure.globalCausalSelection coins)
    (failure.rustOpeningCorrespondence coins)
    (failure.merkleHashCollision coins)
    (failure.workCheck coins)
    (failure.friArithmetic coins)
    (failure.queryPhase coins)
    (failure.countedFriFibre coins)
    (failure.candidateTrace coins)
    (failure.relationRepair coins)
    (failure.poseidon coins)
    (failure.publishedDecoding coins)

/-! ## Exact containment obligations -/

/-- Every constructor is assigned to an already counted final event.

The four adaptive FRI events are one union because the deterministic theorem
returns the occurrence of the four-round bad-set family.  A concrete
experiment may prove a sharper disjoint or round-indexed containment, but the
union below is sufficient and does not add a fifth FRI budget.
-/
structure AcceptedExecutionFailureCoverage
    {Coins : Type*}
    (events : FinalSecurityEvents Coins)
    (failure : AcceptedExecutionFailurePredicates Coins) : Prop where
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
  releasedFinalDomain :
    {coins | failure.releasedFinalDomain coins} ⊆
      events.acceptedRunRelationBridge
  releasedInverseTable :
    {coins | failure.releasedInverseTable coins} ⊆
      events.acceptedRunRelationBridge
  referenceForest :
    {coins | failure.referenceForest coins} ⊆
      events.proofMerkleOpeningBridge
  globalCausalSelection :
    {coins | failure.globalCausalSelection coins} ⊆
      events.acceptedRunRelationBridge
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
  countedFriFibre :
    {coins | failure.countedFriFibre coins} ⊆
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
  publishedDecoding :
    {coins | failure.publishedDecoding coins} ⊆
      events.acceptedRunRelationBridge

/-! ## Deterministic and probability composition -/

/-- The eighteen-way accepted-execution result lands in the one final ledger
when every exact event-containment obligation above is supplied. -/
theorem accepted_execution_failure_subset_total
    {Coins : Type*}
    (events : FinalSecurityEvents Coins)
    (failure : AcceptedExecutionFailurePredicates Coins)
    (coverage : AcceptedExecutionFailureCoverage events failure) :
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
  | releasedFinalDomain event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.releasedFinalDomain event)
  | releasedInverseTable event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.releasedInverseTable event)
  | referenceForest event =>
      exact one_final_failure_is_in_total events .proofMerkleOpeningBridge
        (coverage.referenceForest event)
  | globalCausalSelection event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.globalCausalSelection event)
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
      have covered := coverage.countedFriFibre event
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
  | publishedDecoding event =>
      exact one_final_failure_is_in_total events .acceptedRunRelationBridge
        (coverage.publishedDecoding event)

/-- Any real attack already reduced pointwise to the deterministic
accepted-execution result inherits the explicit final budget.  This theorem
does not construct that reduction or any of the containment premises. -/
theorem attack_probability_le_final_budget
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Coins)
    (failure : AcceptedExecutionFailurePredicates Coins)
    (attack : Set Coins)
    (attackReduces : attack ⊆ {coins | failure.Occurs coins})
    (coverage : AcceptedExecutionFailureCoverage events failure)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget) :
    measure.real attack ≤ (1 : Real) / 2 ^ 108 + budget.total := by
  have covered : attack ⊆ totalFinalFailure events :=
    Set.Subset.trans attackReduces
      (accepted_execution_failure_subset_total events failure coverage)
  exact (MeasureTheory.measureReal_mono covered).trans
    (total_final_failure_probability_le_released_subtotal_plus_external
      measure events budget assumed)

#print axioms accepted_execution_failure_subset_total
#print axioms attack_probability_le_final_budget

end AspisV5AcceptedExecutionFinalAccounting
