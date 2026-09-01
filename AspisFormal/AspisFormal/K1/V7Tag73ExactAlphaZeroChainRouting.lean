import AspisFormal.K1.V7Tag73ExactAlphaZeroControllerAlignment

/-!
# Recursive accepted-source routing of the four alpha-zero blocks

The exact q16 sampler certificate is a recursive duplex chain.  This file
folds that certificate through the source-aligned alpha controller: every
output block is assigned its pre-answer `Fin 4` label, while every advance
answer installs the producer used by the next block.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaZeroChainRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Obtain the alpha duplex chain and its block-zero producer installation
from one accepted-source witness.  Keeping these facts in one existential
prevents an illicit uniqueness join between separately chosen witnesses. -/
theorem exact_compiler_alpha_zero_chain_and_initial_installation
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
      fixedInstance sample) :
    ∃ boundaryIndex producer outputs advances,
      producer.block = (0 : Fin 4) ∧
      ExactRootOrderedQ16Chain input producer.sourceInput producer.digest
        outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse (.alpha 0)).blocksUsed ∧
      ExactAlphaZeroProducerInstalled input boundaryIndex producer := by
  obtain ⟨producerInput, _final256Input, beforeAlpha, _afterAlpha,
      _afterBlocks, _afterFinal256, outputs, advances, _exactValue,
      _workAnswer, _q16Base, producerLookup,
      ⟨producerDigest, producerInputExact⟩, ordered, outputsLength,
      _outputsPositive, _advancesLength, _terminalExact, _afterAlphaExact,
      _final256InputExact, _final256Lookup, _workLookup, _workAccepted,
      _finalNonceLookup, _q16BaseExact, _acceptedParameter, _exactDecode,
      _operationalExact⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom input
  obtain ⟨actor, rootMember⟩ :=
    exact_final_table_lookup_has_root_record input producerInput
      beforeAlpha.digest producerLookup
  obtain ⟨prior, later, rootExact⟩ := (List.mem_iff_append).mp rootMember
  let boundaryIndex := prior.length
  let producer : AlphaZeroProducer :=
    { digest := beforeAlpha.digest, block := 0, sourceInput := producerInput }
  let selected : UnifiedExposureRecord :=
    .machineFresh actor producerInput beforeAlpha.digest
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let reached := indexedStateAfterRecords transitionFuel controller prior
    (exactAlphaZeroInitialState input)
  have selectedAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      beforeAlpha.digest = selected := by
    exact exact_root_records_aligned_for_alpha_zero_controller input
      boundaryIndex prior selected later (by simpa [selected] using rootExact)
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some producerInput :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      producerInput beforeAlpha.digest (by simpa [selected] using selectedAligned)
  have reachedIndex : reached.exposureIndex = boundaryIndex := by
    simpa [reached, boundaryIndex, exactAlphaZeroInitialState] using
      indexed_state_after_records_exposure_index transitionFuel controller
        prior (exactAlphaZeroInitialState input)
  have boundary : isAlphaZeroBoundaryInput producerInput = true := by
    rw [producerInputExact]
    simp [isAlphaZeroBoundaryInput, alphaZeroBoundaryPayload,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
  have installedMemory :
      (alphaZeroAfterMemory transitionFuel boundaryIndex reached
        beforeAlpha.digest).producers = [producer] := by
    have raw := alpha_zero_after_boundary_has_block_zero_producer transitionFuel
      boundaryIndex reached producerInput beforeAlpha.digest inputExact
        reachedIndex boundary
    simpa [producer] using raw
  have installed : ExactAlphaZeroProducerInstalled input boundaryIndex
      producer := by
    intro arbitraryPrior arbitraryLater arbitraryActor arbitraryExact
    have prefixExact : prior = arbitraryPrior := by
      apply alpha_mapped_nodup_selected_prefix_eq UnifiedExposureRecord.answer
        (exactFixedRootRecords input.package.root) prior later arbitraryPrior
          arbitraryLater selected
          (.machineFresh arbitraryActor producer.sourceInput producer.digest :
            UnifiedExposureRecord)
          (exact_root_record_answers_nodup input)
          (by simpa [selected] using rootExact) arbitraryExact
      rfl
    subst arbitraryPrior
    refine ⟨by omega, ?_⟩
    rw [indexed_state_after_records_append,
      indexed_state_after_records_cons, indexed_state_after_records_nil]
    change producer ∈
      ((alphaZeroCausalController transitionFuel boundaryIndex).afterAnswer
        transitionFuel reached beforeAlpha.digest).memory.producers
    change producer ∈
      (alphaZeroAfterMemory transitionFuel boundaryIndex reached
        beforeAlpha.digest).producers
    rw [installedMemory]
    simp
  exact ⟨boundaryIndex, producer, outputs, advances, rfl, by
    simpa [producer] using ordered, outputsLength, installed⟩

/-- Recursive exact-root fold.  Every consumed alpha-zero output has its
literal accepted-root decomposition and the corresponding pre-answer label.
The theorem is independent of which actor first exposed each SHA coordinate.
-/
theorem exact_ordered_alpha_zero_chain_has_preferred_slots
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
    (boundaryIndex : Nat) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 4)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (lengthCap : block.val + outputs.length ≤ 4)
      (installed : ExactAlphaZeroProducerInstalled input boundaryIndex
        (AlphaZeroProducer.mk digest block producerInput)),
      ∀ index (inOutputs : index < outputs.length),
        ∃ outputPrefix later outputActor outputInput,
          exactFixedRootRecords input.package.root =
            outputPrefix ++
              (.machineFresh outputActor outputInput outputs[index] :
                UnifiedExposureRecord) :: later ∧
          alphaZeroPreferredSlot transitionFuel
            (indexedStateAfterRecords transitionFuel
              (alphaZeroCausalController transitionFuel boundaryIndex)
              outputPrefix (exactAlphaZeroInitialState input)) =
                some
                  ⟨block.val + index,
                    (Nat.add_lt_add_left inOutputs block.val).trans_le
                      lengthCap⟩ := by
  intro producerInput digest outputs advances block chain lengthCap installed
  induction chain generalizing block with
  | done producerInput digest producerFound =>
      intro index inOutputs
      simp at inOutputs
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail ih =>
      intro index inOutputs
      let producer := AlphaZeroProducer.mk digest block producerInput
      have headPreferred :=
        exact_alpha_installed_producer_output_has_preferred_slot input
          boundaryIndex producer output (by simpa [producer] using installed)
          (by simpa [producer, gammaOutputInput] using producerBeforeOutput)
      cases index with
      | zero =>
          obtain ⟨outputPrefix, later, outputActor, decomposition,
              preferred⟩ := headPreferred
          exact ⟨outputPrefix, later, outputActor,
            gammaOutputInput producer.digest, by
              simpa [producer] using decomposition, by
              simpa [producer] using preferred⟩
      | succ index =>
          have indexInTail : index < outputs.length := by
            simpa using inOutputs
          have nextBound : block.val + 1 < 4 := by
            have positive : 0 < outputs.length := Nat.zero_lt_of_lt indexInTail
            simp only [List.length_cons] at lengthCap
            omega
          let nextBlock : Fin 4 := ⟨block.val + 1, nextBound⟩
          let nextProducer := AlphaZeroProducer.mk advanced nextBlock
            (gammaAdvanceInput digest)
          have nextInstalled : ExactAlphaZeroProducerInstalled input
              boundaryIndex nextProducer := by
            have installedRaw := exact_alpha_advance_installs_next_producer
              input boundaryIndex producer advanced nextBound
                (by simpa [producer] using installed)
                (by simpa [producer, gammaAdvanceInput] using
                  producerBeforeAdvance)
            simpa [producer, nextProducer, nextBlock] using installedRaw
          have tailLengthCap : nextBlock.val + outputs.length ≤ 4 := by
            simp [nextBlock]
            simp only [List.length_cons] at lengthCap
            omega
          have tailPreferred := ih nextBlock tailLengthCap nextInstalled index
            indexInTail
          let goalBlock : Fin 4 :=
            ⟨block.val + (index + 1),
              (Nat.add_lt_add_left inOutputs block.val).trans_le lengthCap⟩
          let tailBlock : Fin 4 :=
            ⟨nextBlock.val + index,
              (Nat.add_lt_add_left indexInTail nextBlock.val).trans_le
                tailLengthCap⟩
          have blockExact : goalBlock = tailBlock := by
            apply Fin.ext
            simp only [goalBlock, tailBlock, nextBlock]
            omega
          have outputExact : (output :: outputs)[index + 1] = outputs[index] :=
            rfl
          simpa [nextProducer, goalBlock, tailBlock, blockExact, outputExact]
            using tailPreferred

/-- Accepted-source operational closure for alpha zero: every output block
actually consumed by the deployed bounded decoder has a literal root record
and the exact `Fin 4` pre-answer label.  Unused cap slots remain padding in
the total 517-coordinate router. -/
theorem exact_compiler_alpha_zero_consumed_outputs_have_preferred_slots
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
      fixedInstance sample) :
    ∃ boundaryIndex producer outputs advances,
      producer.block = (0 : Fin 4) ∧
      ExactRootOrderedQ16Chain input producer.sourceInput producer.digest
        outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse (.alpha 0)).blocksUsed ∧
      ExactAlphaZeroProducerInstalled input boundaryIndex producer ∧
      ∃ lengthCap : producer.block.val + outputs.length ≤ 4,
        ∀ index (inOutputs : index < outputs.length),
          ∃ outputPrefix later outputActor outputInput,
            exactFixedRootRecords input.package.root =
              outputPrefix ++
                (.machineFresh outputActor outputInput outputs[index] :
                  UnifiedExposureRecord) :: later ∧
            alphaZeroPreferredSlot transitionFuel
              (indexedStateAfterRecords transitionFuel
                (alphaZeroCausalController transitionFuel boundaryIndex)
                outputPrefix (exactAlphaZeroInitialState input)) =
                  some
                    ⟨producer.block.val + index,
                      (Nat.add_lt_add_left inOutputs producer.block.val).trans_le
                        lengthCap⟩ := by
  obtain ⟨boundaryIndex, producer, outputs, advances, blockZero, chain,
      outputsLength, installed⟩ :=
    exact_compiler_alpha_zero_chain_and_initial_installation transitionRoom input
  have lengthCap : producer.block.val + outputs.length ≤ 4 := by
    have blockValue : producer.block.val = 0 := by
      simpa using congrArg Fin.val blockZero
    rw [blockValue, Nat.zero_add, outputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        (.alpha 0)).withinDeployedCap
  refine ⟨boundaryIndex, producer, outputs, advances, blockZero, chain,
    outputsLength, installed, lengthCap, ?_⟩
  exact exact_ordered_alpha_zero_chain_has_preferred_slots input boundaryIndex
    producer.block chain lengthCap installed

#print axioms exact_ordered_alpha_zero_chain_has_preferred_slots
#print axioms exact_compiler_alpha_zero_chain_and_initial_installation
#print axioms exact_compiler_alpha_zero_consumed_outputs_have_preferred_slots

end

end AspisK1.V7Tag73ExactAlphaZeroChainRouting
