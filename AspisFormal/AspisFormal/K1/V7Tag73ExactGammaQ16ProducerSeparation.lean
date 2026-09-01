import AspisFormal.K1.V7Tag73ExactGammaPrefixBoundaryOrigin
import AspisFormal.K1.V7Tag73ExactAlphaQ16ProducerSeparation

/-!
# Gamma-chain separation from q16 producers

The gamma sampler is causally rooted at the literal batch-nonce absorption.
That 42-byte source grammar is disjoint from both q16 candidate absorbs and
q16 duplex advances.  Clean-root answer uniqueness therefore prevents any
gamma state digest from aliasing a q16 producer digest, including when the
adversary first queried either coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactGammaQ16ProducerSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactAlphaQ16ProducerSeparation
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagProducerRecordProvenance
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactGammaPrefixBoundaryOrigin
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The canonical batch-nonce absorption cannot be a source coordinate for
any q16 producer.  Candidate inputs have 35 bytes and recursive advances have
33, whereas the deployed batch-nonce input has 42. -/
theorem gamma_boundary_avoids_q16_producer_sources
    (messages : Messages) (beforeBatchDigest base : Digest256)
    (producers : List Q16DagProducer)
    (inventory : Q16DagProducerInventoryValid base producers) :
    ∀ producer ∈ producers,
      bytes beforeBatchDigest ++ [domAbsorb, batchWorkNonceLabel] ++
          bytes messages.batchGrinding.selected ≠ producer.sourceInput := by
  intro producer producerMember equal
  rcases inventory producer producerMember with candidate | advanced
  · rw [candidate.2] at equal
    have lengths := congrArg List.length equal
    simp at lengths
  · obtain ⟨parent, _parentMember, _counterExact, _blockExact,
      sourceExact⟩ := advanced
    rw [sourceExact] at equal
    have lengths := congrArg List.length equal
    simp at lengths

/-- The production gamma sampler's complete consumed state chain avoids the
full q16 producer inventory reconstructed from the same accepted root. -/
theorem exact_operational_gamma_chain_avoids_full_dag_producers
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters) :
    ∃ (producerInput : ShaInput) (initialDigest : Digest256)
        (outputs advances : List Digest256),
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
          advances ∧
      outputs.length =
          ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed ∧
      advances.length = outputs.length ∧
      ChainStatesAvoidQ16Producers
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (exactFixedRootRecords input.package.root)
          (exactDagCandidateInitialState input)).memory.producers
        initialDigest advances := by
  obtain ⟨producerInput, initialDigest, outputs, advances, _producerLookup,
      ⟨beforeBatch, producerInputExact⟩, chain, outputsLength,
      advancesLength⟩ :=
    exact_operational_batch_nonce_and_gamma_chain transitionRoom input
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial)
    (exactFixedRootRecords input.package.root)
    (exactDagCandidateInitialState input)
  have invariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached] using exact_dag_candidate_root_producer_invariant input trial
  have avoids : ChainStatesAvoidQ16Producers reached.memory.producers
      initialDigest advances := by
    cases baseExact : reached.memory.q16Base with
    | none =>
        have empty := invariant.noBaseHasNoProducers baseExact
        simp [empty, ChainStatesAvoidQ16Producers]
    | some base =>
        have inventory : Q16DagProducerInventoryValid base
            reached.memory.producers :=
          invariant.inventoryValid base baseExact
        have provenance : ∀ producer ∈ reached.memory.producers,
            ∃ actor,
              (.machineFresh actor producer.sourceInput producer.digest :
                  UnifiedExposureRecord) ∈
                exactFixedRootRecords input.package.root := by
          intro producer producerMember
          apply exact_dag_prefix_producer_has_literal_record input trial
            (exactFixedRootRecords input.package.root) [] (by simp) producer
          simpa [reached] using producerMember
        apply exact_root_ordered_chain_avoids_q16_producers input base
          reached.memory.producers inventory provenance chain
        intro producer producerMember
        rw [producerInputExact]
        apply gamma_boundary_avoids_q16_producer_sources
          (exactOperationalTape input).messages beforeBatch.digest base
          reached.memory.producers inventory producer producerMember
  exact ⟨producerInput, initialDigest, outputs, advances, chain, outputsLength,
    advancesLength, by simpa [reached] using avoids⟩

#print axioms gamma_boundary_avoids_q16_producer_sources
#print axioms exact_operational_gamma_chain_avoids_full_dag_producers

end

end AspisK1.V7Tag73ExactGammaQ16ProducerSeparation
