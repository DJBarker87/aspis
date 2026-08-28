import AspisFormal.K1.V7Tag73ExactCompilerQ16InitialDigestMap
import AspisFormal.K1.V7Tag73OperationalQ16ForestHandoff

/-!
# Exact compiler q16 decoder-to-forest handoff

Strict source refinement exposes the exact consumed decoder prefix at every
counter through the selected counter.  This module packages those prefixes in
the pointwise form consumed by the already-proved operational q16 forest law.
The sole remaining router obligation is literal per-block equality with the
online-routed forest; no decoder, first-success, or probability conclusion is
assumed there.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerQ16ForestHandoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73ActualQ16DecoderExtraction
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SamplerDecoder

noncomputable section

/-- Canonical source decoder prefix for every scanned candidate. -/
noncomputable def exactOperationalQ16CandidateBlocks
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Fin 64 → List Digest256 := fun counter =>
  if beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val then
    Classical.choose
      (strict_checked_refinement_exposes_exact_q16_decoder_prefixes
        (exactOperationalTable input) (exactOperationalTape input)
        (exactOperationalRawTrace input)
        input.package.root.fixedRoot.base.strictRefinement counter
        beforeSelected)
  else
    []

theorem exact_operational_q16_candidate_blocks_length
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    (exactOperationalQ16CandidateBlocks input counter).length =
      ((exactOperationalTape input).search.outcome counter).blocksUsed := by
  rw [exactOperationalQ16CandidateBlocks, dif_pos beforeSelected]
  exact (Classical.choose_spec
    (strict_checked_refinement_exposes_exact_q16_decoder_prefixes
      (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement counter
      beforeSelected)).1

theorem exact_operational_q16_candidate_blocks_decode
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    decodeCandidateOutcome counter
        (exactOperationalQ16CandidateBlocks input counter) =
      some ((exactOperationalTape input).search.outcome counter) := by
  rw [exactOperationalQ16CandidateBlocks, dif_pos beforeSelected]
  exact (Classical.choose_spec
    (strict_checked_refinement_exposes_exact_q16_decoder_prefixes
      (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement counter
      beforeSelected)).2

/-- Exact pointwise operational realization.  Only the online router's literal
answer equality and the already-authenticated frontier recurrence remain as
arguments. -/
def exactOperationalQ16PointwiseFacts
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (forest : Q16CandidateDigestForest)
    (routedBytesExact : ∀ counter
      (beforeSelected : counter.val ≤
        (exactOperationalTape input).search.selectedCounter.val)
      (index : Nat)
      (inBlocks : index <
        (exactOperationalQ16CandidateBlocks input counter).length),
      (exactOperationalQ16CandidateBlocks input counter)[index] =
        forest counter
          ⟨index, by
            rw [exact_operational_q16_candidate_blocks_length input counter
              beforeSelected] at inBlocks
            exact Nat.lt_of_lt_of_le inBlocks
              (candidate_outcome_blocks_cap
                ((exactOperationalTape input).search.outcome counter))⟩)
    (frontierExact : ∀ counter schedule,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      (exactOperationalTape input).search.outcome counter = .schedule schedule →
      semanticFrontierNodes (semanticScheduleOfOperational schedule) =
        (exactOperationalTape input).frontierNodes schedule) :
    OperationalQ16DigestPointwiseFacts
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search forest where
  candidateBlocks := exactOperationalQ16CandidateBlocks input
  candidateLengthCap counter beforeSelected := by
    rw [exact_operational_q16_candidate_blocks_length input counter
      beforeSelected]
    exact candidate_outcome_blocks_cap
      ((exactOperationalTape input).search.outcome counter)
  candidateBlockExact := routedBytesExact
  outcomeDecoded counter beforeSelected :=
    exact_operational_q16_candidate_blocks_decode input counter beforeSelected
  frontierExact := frontierExact

theorem exact_operational_q16_pointwise_implies_successful_forest
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (forest : Q16CandidateDigestForest)
    (routedBytesExact : ∀ counter
      (beforeSelected : counter.val ≤
        (exactOperationalTape input).search.selectedCounter.val)
      (index : Nat)
      (inBlocks : index <
        (exactOperationalQ16CandidateBlocks input counter).length),
      (exactOperationalQ16CandidateBlocks input counter)[index] =
        forest counter
          ⟨index, by
            rw [exact_operational_q16_candidate_blocks_length input counter
              beforeSelected] at inBlocks
            exact Nat.lt_of_lt_of_le inBlocks
              (candidate_outcome_blocks_cap
                ((exactOperationalTape input).search.outcome counter))⟩)
    (frontierExact : ∀ counter schedule,
      counter.val ≤ (exactOperationalTape input).search.selectedCounter.val →
      (exactOperationalTape input).search.outcome counter = .schedule schedule →
      semanticFrontierNodes (semanticScheduleOfOperational schedule) =
        (exactOperationalTape input).frontierNodes schedule) :
    q16DigestForestSucceeds forest := by
  exact operational_realization_implies_q16_digest_forest_succeeds
    (operationalQ16ForestRealizationOfDigestPointwise
      (exactOperationalQ16PointwiseFacts input forest routedBytesExact
        frontierExact))

#print axioms exact_operational_q16_candidate_blocks_length
#print axioms exact_operational_q16_candidate_blocks_decode
#print axioms exactOperationalQ16PointwiseFacts
#print axioms exact_operational_q16_pointwise_implies_successful_forest

end

end AspisK1.V7Tag73ExactCompilerQ16ForestHandoff
