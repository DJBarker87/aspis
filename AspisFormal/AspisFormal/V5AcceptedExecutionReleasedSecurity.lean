import AspisFormal.V5AcceptedExecutionReleasedSchedule

/-!
# Accepted false executions with the released FRI schedule

This file combines the accepted-execution theorem with the facts proved for
the released FRI tables.

Four branches in the general event are impossible here:

* the released final-domain table is wrong;
* a released inverse table is wrong;
* no single causal backwards strategy exists; and
* the published decoding theorem is unavailable.

The first two are removed from an explicit
`ProductionUsesReleasedFriTables` correspondence.  The third is already
constructed in Lean by `V5FriGlobalCausalStrategy`.  The fourth is removed
only when `PublishedOrdinaryPolynomialCurveDecoding` is supplied.  All real
source, authentication, transcript, primitive, query, FRI, and relation
failures remain visible.  The theorem is pointwise for one supplied causal
transcript family.  Connecting a production Fiat--Shamir execution to one
family fixed across counterfactual challenge tuples remains a separate
experiment boundary.
-/

namespace AspisV5AcceptedExecutionReleasedSecurity

open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- The accepted-execution event after removing the four branches proved
impossible for the released schedule.  The fourteen remaining propositions
are kept in the same order as the general event. -/
abbrev ReleasedAcceptedExecutionSecurityEvent
    (sourceRelationProjectionFailure : Prop)
    (familyProjectionFailure : Prop)
    (transcriptProjectionFailure : Prop)
    (workProjectionFailure : Prop)
    (referenceForestFailure : Prop)
    (rustOpeningCorrespondenceFailure : Prop)
    (hashCollision : Prop)
    (workFailure : Prop)
    (friArithmeticFailure : Prop)
    (queryMiss : Prop)
    (countedFriFibre : Prop)
    (candidateTraceFailure : Prop)
    (relationRepair : Prop)
    (poseidonFailure : Prop) : Prop :=
  AcceptedExecutionSecurityEvent
    sourceRelationProjectionFailure familyProjectionFailure
    transcriptProjectionFailure workProjectionFailure
    False False referenceForestFailure False
    rustOpeningCorrespondenceFailure hashCollision workFailure
    friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
    relationRepair poseidonFailure False

/-- Convert the general accepted-execution result to the released-schedule
event.  This small lemma makes the exact four eliminated positions easy to
audit independently of the larger source-execution theorem. -/
theorem released_event_of_accepted_event
    {schedule : FixedSchedule (ZMod P) K}
    (hproduction : ProductionUsesReleasedFriTables schedule)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (event : AcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      (¬ FinalXMatchesReleasedDomain schedule)
      (¬ InverseTablesMatch schedule releasedEvaluationPoints)
      referenceForestFailure False rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure
      (¬ PublishedOrdinaryPolynomialCurveDecoding (K := K))) :
    ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure := by
  exact accepted_event_with_released_tables hproduction hpublished event

/-- A successful false source-shaped execution using the released FRI tables
reaches one of the fourteen remaining events.

`hproduction` is the explicit source-to-table correspondence.  This theorem
does not prove it from the Rust source.  Likewise, `hpublished` remains the
external ordinary-polynomial curve-decoding theorem.  The counted FRI event
uses the single constructed strategy, not an outcome-dependent existential
strategy. -/
theorem accepted_false_source_execution_event_with_released_tables
    {RustInput MerkleDigest PointValue State : Type*}
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.F ->
      AspisFormal.ArithmetizationCore.F ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest ->
      AspisFormal.ArithmetizationCore.Digest}
    (hashing : MerkleHashing MerkleDigest)
    (rustAcceptsOpening : RustInput -> Prop)
    (rootsOf : RustInput -> V5PrivateRoots MerkleDigest)
    (querySetOf : RustInput -> Finset V5Query)
    (rustInput : RustInput)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (causalFamily : CausalTranscriptFamily K)
    (input : SourceRelationInput K)
    (relationFamily : CoherentCandidateFamily K
      (AcceptedCandidate base causalFamily input))
    (records : CandidateRecords (AcceptedCandidate base causalFamily input) K)
    (statement : V5PublicStatement)
    (queries : QuerySchedule 18 131072)
    (decoder : OpeningFibreDecoder K)
    (expectedC2 : V5Query -> Fin 4 -> K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (workFunctions : ExecutableWorkFunctions State
      (SqueezeResult K PointValue))
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue))
    (hsource : ∃ output, runSourceRelationVerifier input = some output)
    (hrustOpening : rustAcceptsOpening rustInput)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    ReleasedAcceptedExecutionSecurityEvent
    (¬ SourceRelationInputMatchesFamily input relationFamily)
    (¬ FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily input) relationFamily input.challenges)
    (¬ TranscriptExecutionProjection input transcriptInput derived
      driverResult (querySetOf rustInput) queries)
    (¬ WorkExecutionProjection transcriptInput derived workInputs)
    (¬ ∃ reference : AcceptedV5Forest hashing (rootsOf rustInput)
        (querySetOf rustInput),
      ForestProjectsToTranscript decoder hashing reference
        (acceptedTranscript causalFamily input) expectedC2)
    (¬ RustAcceptedOpeningYieldsForest hashing rustAcceptsOpening rootsOf
      querySetOf)
    (HashCollision hashing)
    (¬ ExecutableWorkAcceptance workFunctions workInputs)
    (∃ forest : AcceptedV5Forest hashing (rootsOf rustInput)
        (querySetOf rustInput),
      ¬ ForestFriChecks decoder hashing forest (acceptedSchedule base input)
        (acceptedTranscript causalFamily input) queries)
    (QueryPhaseFailure (acceptedSchedule base input)
      (acceptedTranscript causalFamily input) queries)
    (∃ (hfinal : FinalXMatchesReleasedDomain base)
        (htables : InverseTablesMatch base releasedEvaluationPoints)
        (hdecoding : PublishedOrdinaryPolynomialCurveDecoding (K := K)),
      (adaptiveBadSets base causalFamily hfinal htables hdecoding
        (constructedAdaptiveStrategies base causalFamily)).Occurs
        input.round0.alpha input.round1.alpha input.round2.alpha
          input.round3.alpha)
    (∃ candidate : AcceptedCandidate base causalFamily input,
      CandidateEarlierFailure rc (relationFamily.execution candidate)
        input.challenges statement (records candidate))
    (Fintype.card (AcceptedCandidate base causalFamily input) ≤ 240 ∧
      input.challenges ∈ boundedCandidateRepairEvent
        (fun candidate => (relationFamily.execution candidate).adaptiveData))
    (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
      deployedNode) := by
  apply released_event_of_accepted_event hproduction hpublished
  exact accepted_false_source_execution_event rc hashing rustAcceptsOpening
    rootsOf querySetOf rustInput base causalFamily input relationFamily records
    statement queries decoder expectedC2 transcriptInput derived driverResult
    workFunctions workInputs hsource hrustOpening noWitness

#print axioms released_event_of_accepted_event
#print axioms accepted_false_source_execution_event_with_released_tables

end AspisV5AcceptedExecutionReleasedSecurity
