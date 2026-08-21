import V5FriAcceptedForestChecks
import V5FriTransparentHelperEquality
import ConsumerShapeClosure

/-!
# Accepted production call to authenticated FRI checks

This file removes an otherwise free `ForestFriChecks` input from the final
security composition.  The reference forest and its four accepted arithmetic
checks are obtained from the same successful production observation and the
same translated `check_v5_fri_queries` execution.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedProductionFriClosure

open AspisV5AcceptedExecutionSecurityBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAcceptedForestChecks
open AspisV5FriConsumerCoordinateBridge
open AspisV5FriConsumerExactProof
open AspisV5FriConsumerObservationBridge
open AspisV5FriDecoderReferenceSemantics
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge
open AspisV5RelationStressSourceBridge
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness
open V5FriConsumerExact

/-- One concrete accepted FRI call supplies the exact authenticated run and
all four FRI comparisons used by the security theorem.  The remaining two
arguments are the model binding for the accepted transcript values and the
coordinate-source equality; they are kept visible until their source bridges
are joined in the final wrapper. -/
theorem accepted_call_yields_authenticated_released_fri_checks
    {PointValue : Type*}
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (rustObservation : V5ProductionCall → Option OpeningAndFriObservation)
    (rustCall : V5ProductionCall)
    (acceptedCall : AcceptedFriCall)
    (hconsumer : ExactRustV5OpeningAndFriConsumerEquality sha256
      rustObservation)
    (hobservation : rustObservation rustCall =
      some acceptedCall.observation)
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P)
      AspisV5FriAcceptedForestChecks.K)
    (transcript : IdealTranscript AspisV5FriAcceptedForestChecks.K)
    (queries : QuerySchedule 18 131072)
    (relationInput : SourceRelationInput
      AspisV5FriAcceptedForestChecks.K)
    (transcriptInput : V5TranscriptInputs)
    (derived : V5DerivedValues AspisV5FriAcceptedForestChecks.K PointValue)
    (driverResult : V5TranscriptDriverResult
      AspisV5FriAcceptedForestChecks.K PointValue)
    (projection : TranscriptExecutionProjection relationInput transcriptInput
      derived driverResult rustCall.queries queries)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hBinding : ∀ execution : AcceptedProductionFriExecution
        acceptedCall.openings acceptedCall.prepared
        acceptedCall.finalPolynomial acceptedCall.sink,
      AcceptedFriModelInputBinding acceptedCall.prepared
        execution.sourceAlphas acceptedCall.finalPolynomial
        (exactReleasedFriTables base) transcript)
    (hCoordinate : ∀ execution : AcceptedProductionFriExecution
        acceptedCall.openings acceptedCall.prepared
        acceptedCall.finalPolynomial acceptedCall.sink,
      AcceptedExecutionCoordinateSourceCertificate execution) :
    ∃ run : ExactV5Run sha256 rustCall.roots rustCall.queries,
      run.proofBytes = rustCall.proofBytes ∧
      ForestFriChecks (productionOpeningFibreDecoder acceptedCall.prepared)
        (sha256MerkleHashing sha256) run.forest
        (exactReleasedFriTables base) transcript queries := by
  obtain ⟨run, hbytes, hobservationExact⟩ :=
    hconsumer rustCall acceptedCall.observation hobservation
  have hdriver : generatedDriverOutput acceptedCall.openings =
      driverOutputOfRun run [] := by
    have h := congrArg OpeningAndFriObservation.driver hobservationExact
    simpa [AcceptedFriCall.observation, observationOfRun] using h
  obtain ⟨execution⟩ :=
    unchanged_source_acceptance_yields_complete_fri_execution
      acceptedCall.openings acceptedCall.prepared acceptedCall.alphas
      acceptedCall.finalPolynomial acceptedCall.inverse acceptedCall.sink
      acceptedCall.accepted
  have hchecks :=
    accepted_production_execution_yields_released_forest_fri_checks run
      acceptedCall.openings acceptedCall.prepared acceptedCall.finalPolynomial
      acceptedCall.sink execution hdriver base transcript queries relationInput
      transcriptInput derived driverResult projection
      AspisV5FriTransparentHelperEquality.transparentFriHelperCallEquality
      hDecoder
      (hBinding execution) V5ShapeValidationProof.validationSuccessPreservesShape
      (hCoordinate execution)
  exact ⟨run, hbytes, hchecks⟩

#print axioms accepted_call_yields_authenticated_released_fri_checks

end AspisV5AcceptedProductionFriClosure
