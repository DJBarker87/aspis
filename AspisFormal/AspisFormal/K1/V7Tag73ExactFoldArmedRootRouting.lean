import AspisFormal.K1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73FoldArmedCompleteLabelsNodup

/-!
# Accepted-root routing for the fold-armed 518-slot controller

This is the source/tape wrapper needed by the K1.3 probability router.  It
does not assume a tape-dependent alpha-boundary ordinal: labels are produced
online by the fold-armed controller and routed from the literal accepted root
prefix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedCompleteLabelsNodup
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactFoldArmedRootLabels
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
    List (Option FoldAlphaFinalWorkQ16DigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (foldArmedCompleteController transitionFuel foldTrial.val finalTrial.val)
    (foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase)
    (exactFixedRootRecords input.package.root)

theorem exact_fold_armed_root_labels_form_trace
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
    MachineLabeledTrace
      ((foldArmedCompleteController transitionFuel foldTrial.val
        finalTrial.val).machine transitionFuel)
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
      (exactFoldArmedRootLabels input foldTrial finalTrial)
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldTrial.val finalTrial.val)
        (exactFixedRootRecords input.package.root)
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel _ _ _

theorem exact_fold_armed_root_named_slots_nodup
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
    (namedTraceSlots
      (exactFoldArmedRootLabels input foldTrial finalTrial)).Nodup := by
  apply fold_armed_complete_labeled_records_named_slots_nodup transitionFuel
    foldTrial.val finalTrial.val
  simp [FoldArmedOuterCoherent, foldArmedInitialState]

theorem exact_fold_armed_root_labels_tape_prefix
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
    freshAnswerTapeToList
        (foldAlphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      (exactFoldArmedRootLabels input foldTrial finalTrial).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold foldAlphaFinalWorkQ16NamedSlotInputTape
    exactCompilerFoldAlphaFinalWorkQ16InputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]
  unfold exactFoldArmedRootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  have base := exact_causal_router_tape_has_literal_root_prefix input
  unfold finalWorkQ16NamedSlotInputTape exactCompilerFinalWorkQ16InputTape at base
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast] at base
  exact base

theorem exact_fold_armed_root_residual_enough
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
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps (exactFoldArmedRootLabels input foldTrial finalTrial) ≤
      (exactCompilerTargetCaps parameters).length - 518 := by
  let records := exactFixedRootRecords input.package.root
  let labels := exactFoldArmedRootLabels input foldTrial finalTrial
  have labelsLength : labels.length = records.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (foldArmedCompleteController transitionFuel foldTrial.val
          finalTrial.val)
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase) records)
    simpa [labels, exactFoldArmedRootLabels, records] using answers
  have residualLe : residualTraceSteps labels ≤ labels.length := by
    have split := labeled_trace_length_split labels
    omega
  have projectedLength (actor : QueryActor) :
      ∀ queries : List (ShaInput × Digest256),
        (projectedMachineFreshRecords actor queries).length = queries.length := by
    intro queries
    induction queries with
    | nil => rfl
    | cons query queries ih =>
        rcases query with ⟨queryInput, answer⟩
        simp [projectedMachineFreshRecords, ih]
  have recordsCount : records.length = machineFreshCoordinateCount records := by
    unfold records exactFixedRootRecords fullProjectedRootRecords
    simp [projectedLength]
  have recordsMachineLe : records.length ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [recordsCount,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [records]
  have recordsLengthLe : records.length ≤ full256MachineFreshCap parameters :=
    recordsMachineLe.trans input.package.root.traceCaps.1
  have capLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 518 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLe.trans
    (labelsLength.le.trans (recordsLengthLe.trans capLe))

/-- Any online preference at a literal accepted-root record is routed to its
named coordinate in the fold-armed 518-coordinate router. -/
theorem exact_fold_armed_root_answer_is_routed
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (preferred :
      (foldArmedCompleteController transitionFuel foldTrial.val
        finalTrial.val).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldTrial.val
            finalTrial.val) prior
          (foldArmedInitialState
            (exactPlainRomCursor configuration sample.1).erase)) = some slot) :
    causalRoutedAnswer? slot
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some answer := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition :
      exactFoldArmedRootLabels input foldTrial finalTrial =
        priorLabels ++ (some slot, answer) :: laterLabels := by
    unfold exactFoldArmedRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_fold_armed_root_labels_form_trace input foldTrial finalTrial)
    (exact_fold_armed_root_named_slots_nodup input foldTrial finalTrial)
    (fun target _ => Finset.mem_univ target)
    (exact_fold_armed_root_residual_enough input foldTrial finalTrial
      programmedCover)
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_fold_armed_root_labels_tape_prefix input foldTrial finalTrial)
    priorLabels laterLabels slot answer labelsDecomposition

#print axioms exact_fold_armed_root_named_slots_nodup
#print axioms exact_fold_armed_root_labels_tape_prefix
#print axioms exact_fold_armed_root_residual_enough
#print axioms exact_fold_armed_root_answer_is_routed

end

end AspisK1.V7Tag73ExactFoldArmedRootRouting
