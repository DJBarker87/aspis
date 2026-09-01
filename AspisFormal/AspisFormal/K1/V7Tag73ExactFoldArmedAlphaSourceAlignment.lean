import AspisFormal.K1.V7Tag73FoldArmedAlphaZeroController
import AspisFormal.K1.V7Tag73ExactAcceptedFoldTrialPackage

/-!
# Exact-source alignment for the fold-armed alpha controller

This module connects the answer-independent controller to the literal accepted
root.  Replaying the exact root prefix reaches the selected fold-work record;
the record's pre-answer input then arms precisely the deployed fold-nonce
absorption.  The result closes the boundary-ordinal mismatch without fixing a
tape-dependent ordinal in the probability router.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The exact accepted root is cursor-aligned with the fold-armed controller.
This is controller-independent scheduler replay specialized to the new
memory. -/
theorem exact_root_records_aligned_for_fold_armed_controller
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) :
    IndexedRecordsAligned transitionFuel
      (foldArmedCompleteController transitionFuel foldTrial.val finalTrial.val)
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
      (exactFixedRootRecords input.package.root) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
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
    controller initial rootTape
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
    initial (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil, controller, initial] using
    rootAligned

/-- At the exact selected fold-work record, the complete controller arms the
literal fold-nonce absorption input. -/
theorem exact_accepted_fold_record_arms_alpha_boundary
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
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reached := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    (controller.afterMemory reached fold.answer).2.1.expectedBoundary =
      some (bytes fold.digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reached.cursor fold.answer =
        (.machineFresh fold.actor
          (bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          fold.answer : UnifiedExposureRecord) := by
    exact aligned fold.prior _ fold.later fold.rootDecomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor
      fold.actor _ fold.answer selectedAligned
  have atFold : reached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simpa [reached, initial, foldArmedInitialState, fold.trialExact] using count
  exact fold_armed_complete_literal_fold_step_arms_boundary transitionFuel
    fold.trial.val finalTrial.val reached fold.digest fold.answer
    (exactOperationalTape input).messages.foldGrinding.selected atFold inputExact

#print axioms exact_root_records_aligned_for_fold_armed_controller
#print axioms exact_accepted_fold_record_arms_alpha_boundary

end

end AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
