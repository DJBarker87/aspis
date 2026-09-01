import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73ExactAlphaZeroRootOrder
import AspisFormal.K1.V7Tag73ExactDagCandidateLabeledRootRouting

/-!
# Exact accepted-source alignment of the alpha-zero controller

The pre-answer alpha controller is useful only if its boundary index is the
literal fold-nonce absorption in the accepted compiler execution.  This file
locates that exact root record, replays its strict prefix through the same
unified scheduler cursor used by the causal router, and proves that consuming
the boundary answer installs block zero's producer.

No raw-input role classifier is used.  An adversary may have queried the
fold-nonce input first; the chosen root record retains whichever actor made
the unique fresh exposure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaZeroControllerAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactAlphaZeroRootOrder
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Canonical initial state of the accepted run's alpha-zero controller. -/
def exactAlphaZeroInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      AlphaZeroControllerMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := inactiveAlphaZeroMemory }

/-- The complete accepted root prefix is cursor-aligned with the alpha
controller for any fixed boundary ordinal. -/
theorem exact_root_records_aligned_for_alpha_zero_controller
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
    IndexedRecordsAligned transitionFuel
      (alphaZeroCausalController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel boundaryIndex)
      (exactAlphaZeroInitialState input)
      (exactFixedRootRecords input.package.root) := by
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let rootTape := operationalTapeCoordinates
    (globalFull256OracleCallCap parameters) 1
    (unifiedFull256ExposureCap parameters)
    (exactCompilerOperationalIndexedTape parameters sample.2)
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase rootTape =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa [rootTape, exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  have fullAligned := indexed_records_aligned_of_trace transitionFuel
    controller (exactAlphaZeroInitialState input) rootTape
      (runExactPlainRom transitionFuel configuration sample).trace traceExact
  have fullSplit :
      (runExactPlainRom transitionFuel configuration sample).trace =
        [] ++ exactFixedRootRecords input.package.root ++
          (exactFixedComputedClientTailRun transitionFuel configuration sample
            input.package.root).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    rfl
  have rootAligned := indexed_records_aligned_segment transitionFuel controller
    (exactAlphaZeroInitialState input)
    (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil] using rootAligned

/-- The exact fold-nonce root record fixes a boundary ordinal at which the
returned digest is installed as alpha block zero's producer.  The statement
retains the literal actor-tagged trace decomposition and the exact replayed
post-record memory. -/
theorem exact_compiler_alpha_zero_boundary_installs_block_zero
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
    ∃ boundaryIndex prior later actor producerInput beforeAlphaDigest,
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh actor producerInput beforeAlphaDigest :
            UnifiedExposureRecord) :: later ∧
      boundaryIndex = prior.length ∧
      isAlphaZeroBoundaryInput producerInput = true ∧
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          transitionFuel boundaryIndex)
        (prior ++
          [(.machineFresh actor producerInput beforeAlphaDigest :
            UnifiedExposureRecord)])
        (exactAlphaZeroInitialState input)).memory.producers =
          [{ digest := beforeAlphaDigest, block := ⟨0, by omega⟩ }] := by
  obtain ⟨producerInput, _final256Input, beforeAlpha, _afterAlpha,
      _afterBlocks, _afterFinal256, _outputs, _advances, _exactValue,
      _workAnswer, _q16Base, producerLookup,
      ⟨producerDigest, producerInputExact⟩, _ordered, _outputsLength,
      _outputsPositive, _advancesLength, _terminalExact, _afterAlphaExact,
      _final256InputExact, _final256Lookup, _workLookup, _workAccepted,
      _finalNonceLookup, _q16BaseExact, _exactDecode, _operationalExact⟩ :=
    exact_compiler_alpha_zero_chain_has_root_order transitionRoom input
  obtain ⟨actor, rootMember⟩ :=
    exact_final_table_lookup_has_root_record input producerInput
      beforeAlpha.digest producerLookup
  obtain ⟨prior, later, rootExact⟩ := (List.mem_iff_append).mp rootMember
  let boundaryIndex := prior.length
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
  have installed :
      (alphaZeroAfterMemory transitionFuel boundaryIndex reached
        beforeAlpha.digest).producers =
        [{ digest := beforeAlpha.digest, block := ⟨0, by omega⟩ }] :=
    alpha_zero_after_boundary_has_block_zero_producer transitionFuel
      boundaryIndex reached producerInput beforeAlpha.digest inputExact
      reachedIndex boundary
  refine ⟨boundaryIndex, prior, later, actor, producerInput,
    beforeAlpha.digest, by simpa [selected] using rootExact, rfl, boundary, ?_⟩
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change
    (alphaZeroAfterMemory transitionFuel boundaryIndex reached
      beforeAlpha.digest).producers =
        [{ digest := beforeAlpha.digest, block := ⟨0, by omega⟩ }]
  exact installed

#print axioms exactAlphaZeroInitialState
#print axioms exact_root_records_aligned_for_alpha_zero_controller
#print axioms exact_compiler_alpha_zero_boundary_installs_block_zero

end

end AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
