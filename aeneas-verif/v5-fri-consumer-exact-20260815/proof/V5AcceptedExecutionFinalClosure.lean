import V5FriAcceptedForestChecks
import AspisFormal.V5AcceptedExecutionDeterministicClosure
import AspisFormal.V5SourceCandidateFamily
import AspisFormal.V5TerminalCandidateEventBridge

/-!
# Final deterministic closure for one accepted V5 execution

This file joins the already proved source, transcript, work, Merkle, and FRI
facts.  It removes their failure branches from the released accepted-false
event.  A SHA-256 collision and the genuine probabilistic or cryptographic
events remain visible.
-/

set_option autoImplicit false

namespace AspisV5AcceptedExecutionFinalClosure

open AspisCircleGroupOrder
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionDeterministicClosure
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedExecutionDerivedQueries
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAcceptedForestChecks
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67RelationListInclusion
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness
open AspisV5SourceCandidateFamily

/-- Once the positive transcript, work, and authenticated FRI facts have been
proved, the released accepted-false theorem has only genuine security events
left.  A different accepted Merkle forest is handled by the explicit
SHA-256-collision branch, rather than being assumed equal to the reference
forest. -/
theorem accepted_execution_leaves_only_security_events
    {Digest : Type*}
    (decoder : Decoder)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest}
    {querySet : Finset V5Query}
    (reference : AcceptedV5Forest hashing roots querySet)
    (schedule : FixedSchedule (ZMod P) K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (referenceChecks : ForestFriChecks decoder hashing reference schedule
      transcript queries)
    {transcriptProjectionFailure workProjectionFailure
      referenceForestFailure workFailure queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure : Prop}
    (transcriptConnected : ¬ transcriptProjectionFailure)
    (workProjectionConnected : ¬ workProjectionFailure)
    (referenceFailureIsCollision :
      referenceForestFailure → HashCollision hashing)
    (workAccepted : ¬ workFailure)
    (event : ReleasedAcceptedExecutionSecurityEvent
      False False transcriptProjectionFailure workProjectionFailure
      referenceForestFailure False (HashCollision hashing) workFailure
      (∃ forest : AcceptedV5Forest hashing roots querySet,
        ¬ ForestFriChecks decoder hashing forest schedule transcript queries)
      queryMiss countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      False False False False False False (HashCollision hashing) False False
      queryMiss countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure := by
  have withoutFriFailure :=
    remove_released_fri_arithmetic_failure_into_collision decoder hashing
      reference schedule transcript queries referenceChecks event
  exact remove_proved_implementation_failures
    (by simp) (by simp) transcriptConnected workProjectionConnected
    referenceFailureIsCollision (by simp) workAccepted (by simp)
    withoutFriFailure

/-!
## One complete deterministic composition

The theorem above removes implementation branches from an event which has
already been constructed.  The theorem below performs the preceding step as
well: it uses the candidate family built from the accepted relation caller,
then removes the exact transcript, work, Merkle, and FRI branches.  Its
conclusion contains only the explicit hash, sampling, algebraic, and
Poseidon2 security events.
-/

theorem accepted_false_constructed_execution_leaves_only_security_events
    {PointValue State : Type*}
    (rc : RoundConstants)
    {deployedOwner : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNote : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNullifier : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    {deployedNode : AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest →
      AspisFormal.ArithmetizationCore.Digest}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte →
      AspisV5MerkleRustBridge.Digest32)
    (rustObservation : V5ProductionCall → Option OpeningAndFriObservation)
    (rustCall : V5ProductionCall)
    (observation : OpeningAndFriObservation)
    (hconsumer : ExactRustV5OpeningAndFriConsumerEquality sha256
      rustObservation)
    (hobservation : rustObservation rustCall = some observation)
    (base : FixedSchedule (ZMod P) K)
    (hproduction : ProductionUsesReleasedFriTables base)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K)
    (records : CandidateRecords
      (AcceptedCandidate base causalFamily (sourceMode9RelationInput data)) K)
    (statement : V5PublicStatement)
    (decoder : OpeningFibreDecoder K)
    (expectedC2 : V5Query → Fin 4 → K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues K PointValue)
    (driverResult : V5TranscriptDriverResult K PointValue)
    (queryBlocks : List (FixedBytes 32))
    (hdecode : derive18Queries queryBlocks = some derived.queries)
    (workFunctions : ExecutableWorkFunctions State
      (SqueezeResult K PointValue))
    (workInputs : PositionedWorkInputs State (SqueezeResult K PointValue))
    {terminalClaim : K}
    (hcaller : runSourceMode9RelationCaller data
      (acceptedTranscript causalFamily
        (sourceMode9RelationInput data)).publishedFinal = some terminalClaim)
    (transcriptConnected : TranscriptExecutionProjection
      (sourceMode9RelationInput data) transcriptInput derived driverResult
      rustCall.queries
      (decodedQuerySchedule queryBlocks derived.queries hdecode))
    (workProjectionConnected : WorkExecutionProjection transcriptInput derived
      workInputs)
    (workAccepted : ExecutableWorkAcceptance workFunctions workInputs)
    (reference : AcceptedV5Forest (sha256MerkleHashing sha256)
      rustCall.roots rustCall.queries)
    (referenceProjection : ForestProjectsToTranscript decoder
      (sha256MerkleHashing sha256) reference
      (acceptedTranscript causalFamily (sourceMode9RelationInput data))
      expectedC2)
    (referenceChecks : ForestFriChecks decoder (sha256MerkleHashing sha256)
      reference (acceptedSchedule base (sourceMode9RelationInput data))
      (acceptedTranscript causalFamily (sourceMode9RelationInput data))
      (decodedQuerySchedule queryBlocks derived.queries hdecode))
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    let input := sourceMode9RelationInput data
    let relationFamily := releasedSourceCandidateFamily base causalFamily data
    let queries := decodedQuerySchedule queryBlocks derived.queries hdecode
    ReleasedAcceptedExecutionSecurityEvent
      False False False False False False
      (HashCollision (sha256MerkleHashing sha256)) False False
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
  dsimp only
  have event :=
    accepted_false_source_observation_with_constructed_family rc sha256
      rustObservation rustCall observation hconsumer hobservation base
      hproduction hpublished causalFamily data records statement decoder
      expectedC2 transcriptInput derived driverResult queryBlocks hdecode
      workFunctions workInputs hcaller noWitness
  exact accepted_execution_leaves_only_security_events decoder
    (sha256MerkleHashing sha256) reference
    (acceptedSchedule base (sourceMode9RelationInput data))
    (acceptedTranscript causalFamily (sourceMode9RelationInput data))
    (decodedQuerySchedule queryBlocks derived.queries hdecode) referenceChecks
    (by simpa using transcriptConnected)
    (by simpa using workProjectionConnected)
    (fun failure =>
      (failure ⟨reference, by simpa using referenceProjection⟩).elim)
    (by simpa using workAccepted) event

#print axioms accepted_execution_leaves_only_security_events
#print axioms
  accepted_false_constructed_execution_leaves_only_security_events

end AspisV5AcceptedExecutionFinalClosure
