import V5FriAcceptedForestChecks
import AspisFormal.V5AcceptedExecutionDeterministicClosure

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
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriAcceptedForestChecks
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5WithoutReplacementQuerySoundness

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

#print axioms accepted_execution_leaves_only_security_events

end AspisV5AcceptedExecutionFinalClosure
