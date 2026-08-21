import AspisFormal.V5AcceptedExecutionDerivedQueries
import AspisFormal.V5ReleasedFailureReduction

/-!
# The candidate family determined by one decoded V5 proof

The accepted-execution theorem previously received a coherent candidate
family as an independent argument.  This file constructs the family directly
from the decoded relation data and the one initial FRI decoder list.

The construction is deliberately simple.  A fixed decoded proof supplies the
same initial weights, claimed values, claimed polynomials, and final
coefficients for every possible decoder candidate.  Only the candidate's
initial coefficient vector varies.  Later coefficient vectors are already
the deterministic folds in `CoherentCandidateFamily.execution`.

This removes two avoidable pointwise failures:

* the source relation input not matching the selected family; and
* the selected family not using the initial FRI list and final polynomial of
  the accepted transcript.

It does not prove the Fiat--Shamir probability comparison for an adaptive
prover.  That remains the separately stated random-oracle boundary.
-/

namespace AspisV5SourceCandidateFamily

open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5AcceptedExecutionDerivedQueries
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5CompactTerminal
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriGlobalCausalStrategy
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5RelationStressSourceBridge
open AspisV5ReleasedFailureReduction
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge
open AspisV5NonceWorkAuthentication
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- The coherent relation family determined by one decoded proof body.
Only `initialValues` depends on the decoder candidate. -/
noncomputable def sourceFixedBodyCandidateFamily
    {Candidate : Type*}
    (initialValues : Candidate → Fin 1024 → K)
    (data : SourceMode9CallerData K) :
    CoherentCandidateFamily K Candidate where
  initialValues := initialValues
  initialWeights := fun index =>
    data.mainWeights.initial index +
      terminalWeights data.componentBPoint (data.kappa ^ 3) index
  initialClaim := sourceCallerInitialClaim data.inactiveClaim data.kappa
    data.gamma data.pointMajorClaims
  round0 := {
    firstWeights := fun _ => data.mainWeights.round0First
    secondWeights := fun _ => data.mainWeights.round0Second
    claimedFirst := fun _ => data.relationTail.oodValues 0 0
    claimedSecond := fun _ _ => data.relationTail.oodValues 0 1
    claimedPolynomial := fun _ _ =>
      data.relationTail.polynomialCoefficients 0
  }
  round1 := {
    firstWeights := fun _ => data.mainWeights.round1First
    secondWeights := fun _ => data.mainWeights.round1Second
    claimedFirst := fun _ => data.relationTail.oodValues 1 0
    claimedSecond := fun _ _ => data.relationTail.oodValues 1 1
    claimedPolynomial := fun _ _ =>
      data.relationTail.polynomialCoefficients 1
  }
  round2 := {
    firstWeights := fun _ => data.mainWeights.round2First
    secondWeights := fun _ => data.mainWeights.round2Second
    claimedFirst := fun _ => data.relationTail.oodValues 2 0
    claimedSecond := fun _ _ => data.relationTail.oodValues 2 1
    claimedPolynomial := fun _ _ =>
      data.relationTail.polynomialCoefficients 2
  }
  round3 := {
    firstWeights := fun _ => data.mainWeights.round3First
    secondWeights := fun _ => data.mainWeights.round3Second
    claimedFirst := fun _ => data.relationTail.oodValues 3 0
    claimedSecond := fun _ _ => data.relationTail.oodValues 3 1
    claimedPolynomial := fun _ _ =>
      data.relationTail.polynomialCoefficients 3
  }
  publishedFinal := fun _ => data.relationTail.finalCoefficients

/-- Every field of the source caller agrees definitionally with the family
constructed from that caller. -/
theorem sourceFixedBodyCandidateFamily_matches_caller
    {Candidate : Type*}
    (initialValues : Candidate → Fin 1024 → K)
    (data : SourceMode9CallerData K) :
    SourceMode9CallerMatchesFamily data
      (sourceFixedBodyCandidateFamily initialValues data) := by
  refine { claims := ?_, weights := ?_ }
  · constructor <;> rfl
  · constructor <;> rfl

/-- Specialize the fixed-body family to the exact initial decoder list of the
accepted root-defined transcript. -/
noncomputable def releasedSourceCandidateFamily
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K) :
    CoherentCandidateFamily K
      (AcceptedCandidate base causalFamily (sourceMode9RelationInput data)) :=
  sourceFixedBodyCandidateFamily (fun candidate => candidate.1) data

/-- The decoded scalar relation input matches the family constructed from the
same decoded caller data, for every initial decoder candidate. -/
theorem released_source_relation_input_matches_family
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K) :
    SourceRelationInputMatchesFamily (sourceMode9RelationInput data)
      (releasedSourceCandidateFamily base causalFamily data) := by
  exact sourceMode9RelationInput_matches_family (NeZero.ne (2 : K)) data
    (releasedSourceCandidateFamily base causalFamily data)
    (sourceFixedBodyCandidateFamily_matches_caller
      (fun candidate : AcceptedCandidate base causalFamily
        (sourceMode9RelationInput data) => candidate.1) data)

/-- If the relation caller's four final coefficients equal the FRI final
polynomial, the constructed family uses exactly the initial decoder list and
final polynomial of the accepted transcript. -/
theorem released_source_family_matches_fri_transcript
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K)
    (hfinal : data.relationTail.finalCoefficients =
      (acceptedTranscript causalFamily
        (sourceMode9RelationInput data)).publishedFinal) :
    FamilyMatchesFriTranscript
      (concreteCodeEncoders base releasedEvaluationPoints)
      (acceptedTranscript causalFamily (sourceMode9RelationInput data))
      (releasedSourceCandidateFamily base causalFamily data)
      (sourceMode9RelationInput data).challenges := by
  constructor
  · intro candidate
    rfl
  · exact hfinal

/-- Both pointwise relation/family projections are therefore derived from the
decoded data and one final-polynomial equality. -/
theorem released_source_relation_and_family_projections
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K)
    (hfinal : data.relationTail.finalCoefficients =
      (acceptedTranscript causalFamily
        (sourceMode9RelationInput data)).publishedFinal) :
    SourceRelationInputMatchesFamily (sourceMode9RelationInput data)
        (releasedSourceCandidateFamily base causalFamily data) ∧
      FamilyMatchesFriTranscript
        (concreteCodeEncoders base releasedEvaluationPoints)
        (acceptedTranscript causalFamily (sourceMode9RelationInput data))
        (releasedSourceCandidateFamily base causalFamily data)
        (sourceMode9RelationInput data).challenges := by
  exact ⟨released_source_relation_input_matches_family base causalFamily data,
    released_source_family_matches_fri_transcript base causalFamily data
      hfinal⟩

/-- A successful source caller already checks the required equality against
the FRI final polynomial, so callers need not supply it separately. -/
theorem released_source_relation_and_family_projections_of_caller_success
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K)
    {terminalClaim : K}
    (success : runSourceMode9RelationCaller data
      (acceptedTranscript causalFamily
        (sourceMode9RelationInput data)).publishedFinal =
        some terminalClaim) :
    SourceRelationInputMatchesFamily (sourceMode9RelationInput data)
        (releasedSourceCandidateFamily base causalFamily data) ∧
      FamilyMatchesFriTranscript
        (concreteCodeEncoders base releasedEvaluationPoints)
        (acceptedTranscript causalFamily (sourceMode9RelationInput data))
        (releasedSourceCandidateFamily base causalFamily data)
        (sourceMode9RelationInput data).challenges := by
  apply released_source_relation_and_family_projections base causalFamily data
  exact sourceCaller_success_implies_final_coefficients_equal_fri data
    (acceptedTranscript causalFamily
      (sourceMode9RelationInput data)).publishedFinal success

/-- Insert the constructed family into the released accepted-false event.
The two pointwise relation/family mismatch branches become literally
`False`; every other branch is preserved unchanged. -/
theorem caller_success_removes_source_and_family_failures
    (base : FixedSchedule (ZMod P) K)
    (causalFamily : CausalTranscriptFamily K)
    (data : SourceMode9CallerData K)
    {terminalClaim : K}
    (success : runSourceMode9RelationCaller data
      (acceptedTranscript causalFamily
        (sourceMode9RelationInput data)).publishedFinal =
        some terminalClaim)
    {transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (event : ReleasedAcceptedExecutionSecurityEvent
      (¬ SourceRelationInputMatchesFamily (sourceMode9RelationInput data)
        (releasedSourceCandidateFamily base causalFamily data))
      (¬ FamilyMatchesFriTranscript
        (concreteCodeEncoders base releasedEvaluationPoints)
        (acceptedTranscript causalFamily (sourceMode9RelationInput data))
        (releasedSourceCandidateFamily base causalFamily data)
        (sourceMode9RelationInput data).challenges)
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      False False transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure hashCollision
      workFailure friArithmeticFailure queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure := by
  have projections :=
    released_source_relation_and_family_projections_of_caller_success
      base causalFamily data success
  exact remove_released_source_and_family_failures
    (fun failure => failure projections.1)
    (fun failure => failure projections.2) event

/-- The released accepted-false endpoint specialized to the relation input
and candidate family constructed from one decoded source caller.  Successful
caller execution supplies the source-verifier success and proves both
relation/family projections, so those two failure branches are `False` in the
result rather than caller-supplied probability events. -/
theorem accepted_false_source_observation_with_constructed_family
    {PointValue State : Type*}
    (rc : RoundConstants)
    {deployedOwner : Digest -> Digest}
    {deployedNote : Digest -> F -> F -> Digest -> Digest}
    {deployedNullifier : Digest -> Digest -> Digest}
    {deployedNode : Digest -> Digest -> Digest}
    (sha256 : List Byte -> AspisV5MerkleRustBridge.Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
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
    (expectedC2 : V5Query -> Fin 4 -> K)
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
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    let input := sourceMode9RelationInput data
    let relationFamily := releasedSourceCandidateFamily base causalFamily data
    let queries := decodedQuerySchedule queryBlocks derived.queries hdecode
    ReleasedAcceptedExecutionSecurityEvent
      False False
      (¬ TranscriptExecutionProjection input transcriptInput derived
        driverResult rustCall.queries queries)
      (¬ WorkExecutionProjection transcriptInput derived workInputs)
      (¬ ∃ reference : AcceptedV5Forest
          (sha256MerkleHashing sha256) rustCall.roots rustCall.queries,
        ForestProjectsToTranscript decoder (sha256MerkleHashing sha256)
          reference (acceptedTranscript causalFamily input) expectedC2)
      False
      (HashCollision (sha256MerkleHashing sha256))
      (¬ ExecutableWorkAcceptance workFunctions workInputs)
      (∃ forest : AcceptedV5Forest (sha256MerkleHashing sha256)
          rustCall.roots rustCall.queries,
        ¬ ForestFriChecks decoder (sha256MerkleHashing sha256) forest
          (acceptedSchedule base input)
          (acceptedTranscript causalFamily input) queries)
      (QueryPhaseFailure (acceptedSchedule base input)
        (acceptedTranscript causalFamily input) queries)
      (∃ hfinal : FinalXMatchesReleasedDomain base,
        ∃ htables : InverseTablesMatch base releasedEvaluationPoints,
          ∃ hdecoding :
              PublishedOrdinaryPolynomialCurveDecoding (K := K),
            (adaptiveBadSets base causalFamily hfinal htables hdecoding
              (constructedAdaptiveStrategies base causalFamily)).Occurs
              input.round0.alpha input.round1.alpha input.round2.alpha
                input.round3.alpha)
      (∃ candidate : AcceptedCandidate base causalFamily input,
        CandidateEarlierFailure rc (relationFamily.execution candidate)
          input.challenges statement (records candidate))
      (Fintype.card (AcceptedCandidate base causalFamily input) <= 240 /\
        input.challenges ∈ boundedCandidateRepairEvent
          (fun candidate => (relationFamily.execution candidate).adaptiveData))
      (¬ Poseidon2Faithful rc deployedOwner deployedNote deployedNullifier
        deployedNode) := by
  dsimp only
  have hsource := sourceCaller_success_implies_relation_success data
    (acceptedTranscript causalFamily
      (sourceMode9RelationInput data)).publishedFinal hcaller
  have event :=
    accepted_false_source_observation_event_with_derived_queries rc sha256
      rustObservation rustCall observation hconsumer hobservation base
      hproduction hpublished causalFamily (sourceMode9RelationInput data)
      (releasedSourceCandidateFamily base causalFamily data) records statement
      decoder expectedC2 transcriptInput derived driverResult queryBlocks
      hdecode workFunctions workInputs hsource noWitness
  exact caller_success_removes_source_and_family_failures base causalFamily
    data hcaller event

#print axioms sourceFixedBodyCandidateFamily_matches_caller
#print axioms released_source_relation_input_matches_family
#print axioms released_source_family_matches_fri_transcript
#print axioms released_source_relation_and_family_projections
#print axioms
  released_source_relation_and_family_projections_of_caller_success
#print axioms caller_success_removes_source_and_family_failures
#print axioms accepted_false_source_observation_with_constructed_family

end AspisV5SourceCandidateFamily
