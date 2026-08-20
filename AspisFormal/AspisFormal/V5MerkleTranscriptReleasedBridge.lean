import AspisFormal.V5MerkleTranscriptProjection
import AspisFormal.V5AcceptedExecutionReleasedSecurity

/-!
# Remove the released reference-forest failure

`V5MerkleTranscriptProjection` constructs the complete FRI words directly
from a causal family of Merkle roots.  This file feeds that result into the
released accepted-execution event.  If a successful exact production
observation somehow lacked the required forest projection, then the Merkle
hash collision event already occurred.  Consequently the old independent
reference-forest branch can be removed rather than renamed.
-/

namespace AspisV5MerkleTranscriptReleasedBridge

open AspisCircleGroupOrder
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge
open AspisV5MerkleTranscriptProjection

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- The exact private-opening call made at one causal challenge prefix. -/
def causalProductionCall
    (roots : CausalMerkleRoots K Digest32) (z0 z1 z2 : K)
    (queries : Finset V5Query) (proofBytes : List Byte) : V5ProductionCall where
  roots := roots.at z0 z1 z2
  queries := queries
  proofBytes := proofBytes

/-- For a successful exact observation, failure of the root-defined causal
projection implies the already explicit Merkle collision event.  There is no
reference forest, transcript equality, or source-correspondence premise in
this implication. -/
theorem committedCausal_reference_failure_implies_collision
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
    (hconsumer : ExactRustV5OpeningAndFriConsumerEquality sha256
      rustObservation)
    (decoder : OpeningFibreDecoder K)
    (roots : CausalMerkleRoots K Digest32) (z0 z1 z2 z3 : K)
    (queries : Finset V5Query) (proofBytes : List Byte)
    (observation : OpeningAndFriObservation)
    (hobservation : rustObservation
      (causalProductionCall roots z0 z1 z2 queries proofBytes) =
        some observation)
    (failure : ¬ (∃ reference : AcceptedV5Forest
        (sha256MerkleHashing sha256) (roots.at z0 z1 z2) queries,
      ForestProjectsToTranscript decoder (sha256MerkleHashing sha256)
        reference
        (fullTranscript (committedCausalFamily decoder
          (sha256MerkleHashing sha256) roots) z0 z1 z2 z3)
        (committedC2 decoder (sha256MerkleHashing sha256)
          (roots.at z0 z1 z2)))) :
    HashCollision (sha256MerkleHashing sha256) := by
  by_contra hcollision
  obtain ⟨run, _hbytes, _hobservation⟩ := hconsumer
    (causalProductionCall roots z0 z1 z2 queries proofBytes)
    observation hobservation
  apply failure
  refine ⟨run.forest, ?_⟩
  exact forest_projects_to_committedCausalFamily decoder
    (sha256MerkleHashing sha256) hcollision roots z0 z1 z2 z3 run.forest

/-- Generic event transformer: merge the obsolete reference-forest branch
into the Merkle-collision branch while preserving every other event exactly. -/
theorem remove_released_reference_failure_into_collision
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (href : referenceForestFailure -> hashCollision)
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      False rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure := by
  cases event with
  | sourceRelationProjection failure => exact .sourceRelationProjection failure
  | familyProjection failure => exact .familyProjection failure
  | transcriptProjection failure => exact .transcriptProjection failure
  | workProjection failure => exact .workProjection failure
  | releasedFinalDomain failure => exact failure.elim
  | releasedInverseTable failure => exact failure.elim
  | referenceForest failure => exact .merkleHashCollision (href failure)
  | globalCausalSelection failure => exact failure.elim
  | rustOpeningCorrespondence failure =>
      exact .rustOpeningCorrespondence failure
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact .workCheck failure
  | friArithmetic failure => exact .friArithmetic failure
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact failure.elim

/-- Specialized released-event rewrite for the exact observed parser/FRI
consumer and the causal root-defined transcript. -/
theorem remove_committedCausal_reference_failure
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
    (hconsumer : ExactRustV5OpeningAndFriConsumerEquality sha256
      rustObservation)
    (decoder : OpeningFibreDecoder K)
    (roots : CausalMerkleRoots K Digest32) (z0 z1 z2 z3 : K)
    (queries : Finset V5Query) (proofBytes : List Byte)
    (observation : OpeningAndFriObservation)
    (hobservation : rustObservation
      (causalProductionCall roots z0 z1 z2 queries proofBytes) =
        some observation)
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      rustOpeningCorrespondenceFailure workFailure friArithmeticFailure
      queryMiss countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      (¬ (∃ reference : AcceptedV5Forest
          (sha256MerkleHashing sha256) (roots.at z0 z1 z2) queries,
        ForestProjectsToTranscript decoder (sha256MerkleHashing sha256)
          reference
          (fullTranscript (committedCausalFamily decoder
            (sha256MerkleHashing sha256) roots) z0 z1 z2 z3)
          (committedC2 decoder (sha256MerkleHashing sha256)
            (roots.at z0 z1 z2))))
      rustOpeningCorrespondenceFailure
      (HashCollision (sha256MerkleHashing sha256))
      workFailure friArithmeticFailure queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      False rustOpeningCorrespondenceFailure
      (HashCollision (sha256MerkleHashing sha256))
      workFailure friArithmeticFailure queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure := by
  apply remove_released_reference_failure_into_collision (event := event)
  exact committedCausal_reference_failure_implies_collision sha256
    rustObservation hconsumer decoder roots z0 z1 z2 z3 queries proofBytes
    observation hobservation

#print axioms committedCausal_reference_failure_implies_collision
#print axioms remove_released_reference_failure_into_collision
#print axioms remove_committedCausal_reference_failure

end AspisV5MerkleTranscriptReleasedBridge
