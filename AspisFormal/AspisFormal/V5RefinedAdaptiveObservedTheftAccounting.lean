import AspisFormal.V5AdaptiveObservedTheftGame
import AspisFormal.V5TerminalCandidateEventBridge

/-!
# Adaptive theft accounting with the exact terminal event

This file carries the refined one-proof result into the game where an attacker
may first observe any finite public history and then choose the first
fraudulent spend.

The proof avoids counting the same hash failure twice.  An extractor failure
for the chosen spend is first sent through the production-to-ideal connection.
The three alternative-opening collision cases are sent to that same
transcript-and-hash failure union.  Credential recovery, the seven named
implementation/runtime failures, and an invalid victim setup remain separate.

The resulting theorem is deliberately conditional.  Its `2^-75` term is the
proved ideal finite-field subtotal for one selected proof.  Every remaining
source, authentication, cryptographic, runtime, and setup term is displayed
in the conclusion.
-/

namespace AspisV5RefinedAdaptiveObservedTheftAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5AdaptiveObservedTheftGame
open AspisV5CryptographicAssumptions
open AspisV5FixedVictimTheftGame
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5MaskedBoundaryFailureAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5RefinedAcceptedFalseAccounting
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open AspisV5TerminalCandidateEventBridge
open AspisV5TheftStateTransitionReduction

/-! ## A non-duplicated failure union -/

/-- The five top-level events used below: an ideal accepted false spend, one
shared hash/transcript failure union, credential recovery, a named runtime
failure, and invalid victim setup. -/
def refinedAdaptiveFailureUnion
    {Sample : Type*}
    (acceptedFalse hashOrTranscript credential runtime setup : Set Sample) :
    Set Sample :=
  ((((acceptedFalse ∪ hashOrTranscript) ∪ credential) ∪ runtime) ∪ setup)

theorem measureReal_refinedAdaptiveFailureUnion_le
    {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample)
    (acceptedFalse hashOrTranscript credential runtime setup : Set Sample) :
    measure.real (refinedAdaptiveFailureUnion acceptedFalse hashOrTranscript
      credential runtime setup) ≤
      (((measure.real acceptedFalse + measure.real hashOrTranscript) +
        measure.real credential) + measure.real runtime) +
        measure.real setup := by
  unfold refinedAdaptiveFailureUnion
  calc
    measure.real ((((acceptedFalse ∪ hashOrTranscript) ∪ credential) ∪
        runtime) ∪ setup) ≤
        measure.real (((acceptedFalse ∪ hashOrTranscript) ∪ credential) ∪
          runtime) + measure.real setup :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (measure.real ((acceptedFalse ∪ hashOrTranscript) ∪ credential) +
          measure.real runtime) + measure.real setup := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((measure.real (acceptedFalse ∪ hashOrTranscript) +
          measure.real credential) + measure.real runtime) +
          measure.real setup := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ (((measure.real acceptedFalse + measure.real hashOrTranscript) +
          measure.real credential) + measure.real runtime) +
          measure.real setup := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _

/-! ## The adaptive-history connection -/

/-- Exact coverage required to connect the adaptive theft classification to
the refined production false-spend experiment.  The extractor-after-history
event must be a production false spend.  The three alternative-opening cases
must enter the same hash failure union already used by the production
connection, so that union is counted only once. -/
structure RefinedAdaptiveHistoryCoverage
    {Sample K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Sample K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (extractorAfterObservation nullifierSecondPreimage noteSecondPreimage
      victimTreeCollision : Set Sample) : Prop where
  extractorAfterObservation :
    extractorAfterObservation ⊆ production.productionFalseSpend
  nullifierSecondPreimage : nullifierSecondPreimage ⊆
    totalFailure production.transcriptAndHashFailures
  noteSecondPreimage : noteSecondPreimage ⊆
    totalFailure production.transcriptAndHashFailures
  victimTreeCollision : victimTreeCollision ⊆
    totalFailure production.transcriptAndHashFailures

/-- A deployed first fraudulent spend, even when selected after observing an
arbitrary finite public history, lands in the exact five-event union above.
The production-to-ideal connection is used here, so its transcript/hash union
also covers the three alternative-opening collision cases without duplicate
accounting. -/
theorem deployed_adaptive_first_fraudulent_spend_subset_refined_union
    {Sample AdversaryCoins PublicArtifact Execution K : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Sample K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (deployedFirstFraudulentSpend : Sample → Prop)
    (runtime : RuntimeFailurePredicates Sample)
    (chain : AdaptiveChainFailures Sample)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      runtime chain deployedOwner deployedNote deployedNullifier deployedNode
      Accepts Commits victim experiment extractAfter)
    (coverage : RefinedAdaptiveHistoryCoverage production
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    {sample | deployedFirstFraudulentSpend sample} ⊆
      refinedAdaptiveFailureUnion data.base.acceptedFalse
        (totalFailure production.transcriptAndHashFailures)
        {sample | CredentialRecoveryAfterObservationEvent Accepts victim
          experiment extractAfter sample}
        {sample | NamedRuntimeFailureEvent runtime sample}
        {sample | chain.victimSetup sample} := by
  intro sample attack
  rcases connection sample attack with modeled | runtimeFailure | setupFailure
  · have classified :=
      adaptive_first_fraudulent_spend_implies_mathematical_failure
        deployedOwner deployedNote deployedNullifier deployedNode Accepts
        Commits victim experiment extractAfter sample modeled
    rcases classified with extraction | credential | nullifier | note | tree
    · have productionFailure := coverage.extractorAfterObservation extraction
      rcases production.production_subset_ideal_or_hash productionFailure with
        ideal | hashFailure
      · exact Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_left _ (Set.mem_union_left _ ideal)))
      · exact Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_left _ (Set.mem_union_right _ hashFailure)))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ credential))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _
          (Set.mem_union_right _ (coverage.nullifierSecondPreimage nullifier))))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _
          (Set.mem_union_right _ (coverage.noteSecondPreimage note))))
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _
          (Set.mem_union_right _ (coverage.victimTreeCollision tree))))
  · exact Set.mem_union_left _ (Set.mem_union_right _ runtimeFailure)
  · exact Set.mem_union_right _ setupFailure

/-! ## Probability accounting -/

/-- The exact terminal candidate event is now part of the adaptive theft
bound.  Only the ideal finite-field part receives the `2^-75` number; every
remaining probability stays visible. -/
theorem deployed_adaptive_first_fraudulent_spend_probability_le_refined
    {Run Sample AdversaryCoins PublicArtifact Execution K Public Root : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Sample]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Sample K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (projection : StatementBindingProjectionData Run Sample K data)
    (boundary : MaskedBoundaryProjectionData Run Sample K Public Root
      (scheme := scheme) projection)
    (plans : TerminalCandidatePlanProjection Run Sample K Public Root boundary)
    (terminalBound :
      measure.real (exactTerminalCandidateFailureSet plans) ≤
        AspisV5RefinedRawCoreAccounting.rawCandidateTerminalBound)
    (deployedFirstFraudulentSpend : Sample → Prop)
    (runtime : RuntimeFailurePredicates Sample)
    (chain : AdaptiveChainFailures Sample)
    (Accepts Commits : V5PublicStatement → Execution → Prop)
    (victim : FixedVictim)
    (experiment : AdaptiveObservationExperiment Sample AdversaryCoins
      PublicArtifact Execution)
    (extractAfter : ExtractAfterObservation PublicArtifact Execution)
    (connection : DeployedAdaptiveAttackConnection deployedFirstFraudulentSpend
      runtime chain deployedOwner deployedNote deployedNullifier deployedNode
      Accepts Commits victim experiment extractAfter)
    (coverage : RefinedAdaptiveHistoryCoverage production
      {sample | ExtractorAfterObservationFailureEvent deployedOwner deployedNote
        deployedNullifier deployedNode Accepts experiment extractAfter sample}
      {sample | NullifierSecondPreimageAfterObservationEvent deployedNullifier
        victim experiment extractAfter sample}
      {sample | NoteSecondPreimageAfterObservationEvent deployedOwner
        deployedNote victim experiment extractAfter sample}
      {sample | VictimTreeCollisionAfterObservationEvent deployedOwner
        deployedNote deployedNode victim experiment extractAfter sample}) :
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
      (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.arithmeticResidualFailure +
        measure.real data.hashMerkleResidualFailure +
        measure.real (totalFailure production.transcriptAndHashFailures) +
        measure.real {sample | CredentialRecoveryAfterObservationEvent Accepts
          victim experiment extractAfter sample} +
        measure.real {sample | NamedRuntimeFailureEvent runtime sample} +
        measure.real {sample | chain.victimSetup sample} := by
  let credential : Set Sample :=
    {sample | CredentialRecoveryAfterObservationEvent Accepts victim
      experiment extractAfter sample}
  let runtimeFailure : Set Sample :=
    {sample | NamedRuntimeFailureEvent runtime sample}
  let setup : Set Sample := {sample | chain.victimSetup sample}
  have subset :=
    deployed_adaptive_first_fraudulent_spend_subset_refined_union data
      production deployedFirstFraudulentSpend runtime chain Accepts Commits
      victim experiment extractAfter connection coverage
  have unionBound := measureReal_refinedAdaptiveFailureUnion_le measure
    data.base.acceptedFalse
    (totalFailure production.transcriptAndHashFailures)
    credential runtimeFailure setup
  have acceptedBound := acceptedFalse_probability_le_with_exact_terminal_event
    measure data connections projection boundary plans terminalBound
  calc
    measure.real {sample | deployedFirstFraudulentSpend sample} ≤
        measure.real (refinedAdaptiveFailureUnion data.base.acceptedFalse
          (totalFailure production.transcriptAndHashFailures)
          credential runtimeFailure setup) :=
      MeasureTheory.measureReal_mono subset
    _ ≤ (((measure.real data.base.acceptedFalse +
          measure.real (totalFailure production.transcriptAndHashFailures)) +
          measure.real credential) + measure.real runtimeFailure) +
          measure.real setup := unionBound
    _ ≤ (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
          nonterminalStatementFailureProbabilitySum measure boundary +
          measure.real data.arithmeticResidualFailure +
          measure.real data.hashMerkleResidualFailure +
          measure.real (totalFailure production.transcriptAndHashFailures) +
          measure.real credential + measure.real runtimeFailure +
          measure.real setup := by
      gcongr

#print axioms measureReal_refinedAdaptiveFailureUnion_le
#print axioms deployed_adaptive_first_fraudulent_spend_subset_refined_union
#print axioms deployed_adaptive_first_fraudulent_spend_probability_le_refined

end AspisV5RefinedAdaptiveObservedTheftAccounting
