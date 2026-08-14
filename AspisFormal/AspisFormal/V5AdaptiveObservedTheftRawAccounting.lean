import AspisFormal.V5AdaptiveObservedTheftGame
import AspisFormal.V5RawFinalSecurityAccounting

/-!
# Raw accounting for theft after observing other proofs

`V5AdaptiveObservedTheftGame` proves the deterministic case split for a first
fraudulent spend chosen after any finite ordered history of other public
proofs.  This file combines that case split with the raw one-proof accounting.

The result does not turn a per-proof probability into an unlimited-attempt
claim.  `AssumedRawFinalSecurityBounds` must hold for the induced adaptive
experiment, including its history-dependent extractor and transcript
distribution.  A caller modelling several final attempts must separately
bound their number or prove the corresponding state-restoration theorem.
-/

namespace AspisV5AdaptiveObservedTheftRawAccounting

open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5AdaptiveObservedTheftGame
open AspisV5FinalSecurityAccounting
open AspisV5FixedVictimTheftGame
open AspisV5RawFinalSecurityAccounting
open AspisV5TheftStateTransitionReduction

/-- Exact raw-core endpoint for the first fraudulent spend selected after an
arbitrary finite public history.  The independently named victim-setup event
is added rather than hidden in a cryptographic or runtime budget. -/
theorem deployed_adaptive_first_fraudulent_spend_probability_le_raw_budget
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    [MeasurableSpace Sample]
    (measure : Measure Sample)
    [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Sample)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget)
    (deployedFirstFraudulentSpend : Sample → Prop)
    (chain : AdaptiveChainFailures Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      events.runtime chain deployedOwner deployedNote
      deployedNullifier deployedNode Accepts Commits victim experiment
      extractAfter)
    (coverage : AdaptiveHistoryFailureCoverage events
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | CredentialRecoveryAfterObservationEvent Accepts victim
        experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
      (rawCoreSubtotal + budget.total) +
        measure.real {sample | chain.victimSetup sample} := by
  have subset :=
    deployed_adaptive_first_fraudulent_spend_subset_final_or_setup events
      deployedFirstFraudulentSpend chain deployedOwner
      deployedNote deployedNullifier deployedNode Accepts Commits victim
      experiment extractAfter connection coverage
  calc
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
        measure.real
          (totalFinalFailure events ∪ {sample | chain.victimSetup sample}) :=
      MeasureTheory.measureReal_mono subset
    _ ≤ measure.real (totalFinalFailure events) +
          measure.real {sample | chain.victimSetup sample} :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (rawCoreSubtotal + budget.total) +
          measure.real {sample | chain.victimSetup sample} := by
      gcongr
      exact total_final_failure_probability_le_raw_core_plus_external
        measure events budget assumed

/-- Conservative 75-bit endpoint for the raw ideal core.  Every production,
primitive, extraction, credential, runtime, and victim-setup term remains
visible in the statement. -/
theorem deployed_adaptive_first_fraudulent_spend_probability_le_two_pow_neg_75
    {Sample AdversaryCoins PublicArtifact Execution : Type*}
    [MeasurableSpace Sample]
    (measure : Measure Sample)
    [IsProbabilityMeasure measure]
    (events : FinalSecurityEvents Sample)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedRawFinalSecurityBounds measure events budget)
    (deployedFirstFraudulentSpend : Sample → Prop)
    (chain : AdaptiveChainFailures Sample)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      events.runtime chain deployedOwner deployedNote
      deployedNullifier deployedNode Accepts Commits victim experiment
      extractAfter)
    (coverage : AdaptiveHistoryFailureCoverage events
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | CredentialRecoveryAfterObservationEvent Accepts victim
        experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
      ((1 : Real) / 2 ^ 75 + budget.total) +
        measure.real {sample | chain.victimSetup sample} := by
  have exactBound :=
    deployed_adaptive_first_fraudulent_spend_probability_le_raw_budget
      measure events budget assumed deployedFirstFraudulentSpend chain
      deployedOwner deployedNote deployedNullifier deployedNode Accepts Commits
      victim experiment extractAfter connection coverage
  calc
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
        (rawCoreSubtotal + budget.total) +
          measure.real {sample | chain.victimSetup sample} := exactBound
    _ ≤ ((1 : Real) / 2 ^ 75 + budget.total) +
          measure.real {sample | chain.victimSetup sample} := by
      gcongr
      exact raw_core_subtotal_le_two_pow_neg_75

#print axioms
  deployed_adaptive_first_fraudulent_spend_probability_le_raw_budget
#print axioms
  deployed_adaptive_first_fraudulent_spend_probability_le_two_pow_neg_75

end AspisV5AdaptiveObservedTheftRawAccounting
