import AspisFormal.K1.V7Tag73ExactFoldArmedRootRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaSourceAlignment
import AspisFormal.K1.V7Tag73ExactFoldAlphaQ16OperationalRealization
import AspisFormal.K1.V7Tag73FoldArmedPreFinalPrefix

/-!
# Accepted fold and final-work routing for the fold-armed controller

The fold coordinate is selected at its exact exposure ordinal.  At the later
41-byte final-work input, the alpha controller cannot have a 33-byte squeeze
preference, so the established DAG preference lifts through the fold-armed
product and outer controller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactFoldArmedRootRouting
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedCompleteLabelsNodup
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem fold_armed_dag_state_after_records
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalWorkAnchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedCompleteMemory),
      foldArmedPreFinalDagState
          (indexedStateAfterRecords transitionFuel
            (foldArmedCompleteController transitionFuel foldExposureIndex
              finalWorkAnchorIndex) records state) =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            finalWorkAnchorIndex) records (foldArmedPreFinalDagState state) := by
  intro records
  induction records with
  | nil => intro state; rfl
  | cons record records ih =>
      intro state
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      rw [ih]
      rfl

theorem exact_fold_armed_accepted_fold_is_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters) :
    causalRoutedAnswer? none
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        fold.trial.val finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some fold.answer := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller fold.prior
    initial
  have coherentInitial : FoldArmedOuterCoherent fold.trial.val initial := by
    simp [FoldArmedOuterCoherent, initial, foldArmedInitialState]
  have coherentReached : FoldArmedOuterCoherent fold.trial.val reached := by
    exact fold_armed_outer_coherent_after_records transitionFuel fold.trial.val
      finalTrial.val fold.prior initial coherentInitial
  have atFold : reached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller fold.prior initial
    simpa [reached, initial, foldArmedInitialState, fold.trialExact] using count
  have unused : reached.memory.1 = false := by
    unfold FoldArmedOuterCoherent at coherentReached
    rw [atFold] at coherentReached
    simpa using coherentReached
  have preferred : controller.preferredSlot reached = some none := by
    simpa [controller] using
      fold_armed_complete_preferred_at_fold transitionFuel fold.trial.val
        finalTrial.val reached unused atFold
  exact exact_fold_armed_root_answer_is_routed programmedCover input fold.trial
    finalTrial fold.prior fold.later fold.actor
      (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected)
      fold.answer none fold.rootDecomposition (by
        simpa [controller, initial, reached] using preferred)

/-- The DAG state inside the fold-armed initial state is exactly the standard
inactive DAG initial state used by accepted-source routing. -/
theorem fold_armed_initial_dag_state_eq
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    foldArmedPreFinalDagState
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase) =
      exactDagCandidateInitialState input := by
  rfl

/-- A literal 41-byte final-work request cannot simultaneously be an alpha
squeeze output, whose exact input width is 33 bytes. -/
theorem fold_armed_alpha_preferred_none_at_final_work
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (key : RawFinalWorkKey) (answer : Digest256)
    (digestLength : key.digest.length = 32)
    (nonceLength : key.nonce.length = 8)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor key.workInput answer :
        UnifiedExposureRecord) :: later) :
    alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState
        (foldArmedAlphaState
          (indexedStateAfterRecords transitionFuel
            (foldArmedCompleteController transitionFuel foldTrial.val
              finalTrial.val) prior
            (foldArmedInitialState
              (exactPlainRomCursor configuration sample.1).erase)))) = none := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    foldTrial finalTrial
  have selectedAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      answer = (.machineFresh actor key.workInput answer :
        UnifiedExposureRecord) := by
    exact aligned prior _ later decomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some key.workInput :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      key.workInput answer selectedAligned
  cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState (foldArmedAlphaState reached)) with
  | none =>
      simpa using alphaPreferred
  | some alphaSlot =>
      exfalso
      obtain ⟨selectedInput, producer, selectedInputExact, _producerMember,
          selectedIsOutput, _blockExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel
          (foldArmedAlphaIndexedState (foldArmedAlphaState reached)) alphaSlot
          alphaPreferred
      have selectedInputEq : selectedInput = key.workInput :=
        Option.some.inj (selectedInputExact.symm.trans (by
          exact inputExact))
      have alphaLength : key.workInput.length = 33 := by
        rw [← selectedInputEq, selectedIsOutput]
        simp
      have workLength : key.workInput.length = 41 := by
        simp [RawFinalWorkKey.workInput, digestLength, nonceLength]
      omega

theorem exact_fold_armed_final_work_is_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactAcceptedDagInstallation input) :
    causalRoutedAnswer? (some (Sum.inr none))
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        fold.trial.val source.finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some source.workAnswer := by
  obtain ⟨workPrior, workLater, workActor, workDecomposition,
      workDagPreferred⟩ := source.workLabeled
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val source.finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller workPrior
    initial
  have dagProjection : foldArmedPreFinalDagState reached =
      indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel source.finalTrial) workPrior
        (exactDagCandidateInitialState input) := by
    rw [show foldArmedPreFinalDagState reached =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
            transitionFuel source.finalTrial.val) workPrior
          (foldArmedPreFinalDagState initial) by
      exact fold_armed_dag_state_after_records transitionFuel fold.trial.val
        source.finalTrial.val workPrior initial]
    rw [fold_armed_initial_dag_state_eq input]
    rfl
  have dagPreferred :
      (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
        transitionFuel source.finalTrial.val).preferredSlot
        (foldArmedPreFinalDagState reached) = some none := by
    rw [dagProjection]
    simpa [exactDagTrialController] using workDagPreferred
  have alphaNone := fold_armed_alpha_preferred_none_at_final_work input
    fold.trial source.finalTrial workPrior workLater workActor
      (literalFinalWorkKey source.digest
        (exactOperationalTape input).messages.finalGrinding.selected)
      source.workAnswer (by simp [literalFinalWorkKey, bytes_length])
      (by simp [literalFinalWorkKey, bytes_length]) workDecomposition
  have underlyingPreferred :
      (alphaFinalWorkQ16DagController transitionFuel source.finalTrial.val
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState reached) = some (Sum.inr none) := by
    apply alpha_final_work_q16_preferred_of_dag
    · simpa [foldArmedAlphaZeroController, foldArmedAlphaState] using alphaNone
    · simpa [foldArmedPreFinalDagState] using dagPreferred
  have workDistinct : workPrior.length ≠ fold.trial.val := by
    symm
    exact exact_accepted_fold_trial_ne_final_work_record input fold source.digest
      source.workAnswer source.prefinal workPrior workLater workActor
        workDecomposition
  have reachedIndex : reached.exposureIndex = workPrior.length := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller workPrior initial
    simpa [reached, initial, foldArmedInitialState] using count
  have notFold : reached.exposureIndex ≠ fold.trial.val := by
    simpa [reachedIndex] using workDistinct
  have preferred : controller.preferredSlot reached =
      some (some (Sum.inr none)) := by
    simp [controller, foldArmedCompleteController, notFold,
      underlyingPreferred]
  exact exact_fold_armed_root_answer_is_routed programmedCover input fold.trial
    source.finalTrial workPrior workLater workActor
      (literalFinalWorkKey source.digest
        (exactOperationalTape input).messages.finalGrinding.selected).workInput
      source.workAnswer (some (Sum.inr none)) workDecomposition (by
        simpa [controller, initial, reached] using preferred)

#print axioms exact_fold_armed_accepted_fold_is_routed
#print axioms fold_armed_alpha_preferred_none_at_final_work
#print axioms exact_fold_armed_final_work_is_routed

end

end AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting
