import AspisFormal.K1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73ExactFoldWorkExposureTrial
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup

/-!
# Accepted-root routing for the complete 518-slot controller

The literal accepted fold-work record is selected at its concrete compiler
exposure index and routed from the same master tape as the established
alpha/final-work/q16 controller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerFoldWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldWorkExposureTrial
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactCompilerFoldAlphaFinalWorkQ16InputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      (518 + ((exactCompilerTargetCaps parameters).length - 518)) :=
  castFreshAnswerTape (by
    have enough :=
      exact_compiler_tape_has_fold_alpha_final_work_q16_capacity parameters
    omega) tape

def foldAlphaFinalWorkQ16NamedSlotInputTape
    {residual : Nat}
    (tape : FreshAnswerTape Digest256 (518 + residual)) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset FoldAlphaFinalWorkQ16DigestSlot).card + residual) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ, fold_alpha_final_work_q16_digest_slot_card]) tape

def exactFoldAlphaFinalWorkQ16InitialState
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
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory := (false, (inactiveAlphaZeroMemory, inactiveDagMemory)) }

def exactFoldAlphaFinalWorkQ16RootLabels
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
    (boundaryIndex : Nat) :
    List (Option FoldAlphaFinalWorkQ16DigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (foldAlphaFinalWorkQ16Controller foldTrial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex)))
    (exactFoldAlphaFinalWorkQ16InitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_fold_alpha_final_work_q16_root_labels_form_trace
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
    (boundaryIndex : Nat) :
    MachineLabeledTrace
      ((foldAlphaFinalWorkQ16Controller foldTrial.val
        (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
          (alphaZeroCausalController transitionFuel boundaryIndex))).machine
            transitionFuel)
      (exactFoldAlphaFinalWorkQ16InitialState input)
      (exactFoldAlphaFinalWorkQ16RootLabels input foldTrial finalTrial
        boundaryIndex)
      (indexedStateAfterRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)))
        (exactFixedRootRecords input.package.root)
        (exactFoldAlphaFinalWorkQ16InitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel _ _ _

theorem exact_fold_alpha_final_work_q16_root_named_slots_nodup
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
    (boundaryIndex : Nat) :
    (namedTraceSlots
      (exactFoldAlphaFinalWorkQ16RootLabels input foldTrial finalTrial
        boundaryIndex)).Nodup := by
  exact fold_alpha_final_work_q16_labeled_records_named_slots_nodup
    transitionFuel foldTrial.val finalTrial.val boundaryIndex
      (exactFixedRootRecords input.package.root)
      (exactFoldAlphaFinalWorkQ16InitialState input)

theorem exact_fold_alpha_final_work_q16_root_labels_tape_prefix
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
    (boundaryIndex : Nat) :
    freshAnswerTapeToList
        (foldAlphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      (exactFoldAlphaFinalWorkQ16RootLabels input foldTrial finalTrial
        boundaryIndex).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold foldAlphaFinalWorkQ16NamedSlotInputTape
    exactCompilerFoldAlphaFinalWorkQ16InputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]
  unfold exactFoldAlphaFinalWorkQ16RootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  have base := exact_causal_router_tape_has_literal_root_prefix input
  unfold finalWorkQ16NamedSlotInputTape exactCompilerFinalWorkQ16InputTape at base
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast] at base
  exact base

theorem exact_fold_alpha_final_work_q16_root_residual_enough
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
    (boundaryIndex : Nat)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
        (exactFoldAlphaFinalWorkQ16RootLabels input foldTrial finalTrial
          boundaryIndex) ≤
      (exactCompilerTargetCaps parameters).length - 518 := by
  let records := exactFixedRootRecords input.package.root
  let labels := exactFoldAlphaFinalWorkQ16RootLabels input foldTrial finalTrial
    boundaryIndex
  have labelsLength : labels.length = records.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (foldAlphaFinalWorkQ16Controller foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)))
        (exactFoldAlphaFinalWorkQ16InitialState input) records)
    simpa [labels, exactFoldAlphaFinalWorkQ16RootLabels, records] using answers
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
  have recordsMachineLe : machineFreshCoordinateCount records ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [records]
  have recordsLengthLe : records.length ≤ full256MachineFreshCap parameters := by
    rw [recordsCount]
    exact recordsMachineLe.trans input.package.root.traceCaps.1
  have capLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 518 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLe.trans
    (labelsLength.le.trans (recordsLengthLe.trans capLe))

theorem exact_fold_work_preferred_at_exposure_trial
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
    (boundaryIndex : Nat) (prior : List UnifiedExposureRecord)
    (trialExact : foldTrial.val = prior.length) :
    (foldAlphaFinalWorkQ16Controller foldTrial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))) prior
        (exactFoldAlphaFinalWorkQ16InitialState input)) = some none := by
  let underlying : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      AlphaFinalWorkQ16DigestSlot
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory) :=
    alphaFinalWorkQ16DagController transitionFuel finalTrial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :=
    foldAlphaFinalWorkQ16Controller foldTrial.val underlying
  let reached := indexedStateAfterRecords transitionFuel controller prior
    (exactFoldAlphaFinalWorkQ16InitialState input)
  have unused : reached.memory.1 = false := by
    apply fold_controller_unused_before_index transitionFuel foldTrial.val
      underlying prior (exactFoldAlphaFinalWorkQ16InitialState input)
    · rfl
    · simp [exactFoldAlphaFinalWorkQ16InitialState, trialExact]
  have atIndex : reached.exposureIndex = foldTrial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller prior (exactFoldAlphaFinalWorkQ16InitialState input)
    simpa [reached, exactFoldAlphaFinalWorkQ16InitialState, trialExact] using
      count
  exact fold_controller_preferred_at_fresh_index foldTrial.val underlying
    reached unused atIndex

theorem exact_compiler_accepted_fold_work_is_routed_by_518_router
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    ∃ foldTrial : ExactCompilerExposureTrial parameters,
      ∃ workAnswer : Digest256,
        FoldWork31Accepted workAnswer ∧
        causalRoutedAnswer? none
          (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
            foldTrial.val
            (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
              (alphaZeroCausalController transitionFuel boundaryIndex))
            (inactiveAlphaZeroMemory, inactiveDagMemory)
            (exactPlainRomCursor configuration sample.1).erase)
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
          some workAnswer := by
  obtain ⟨digest, workAnswer, foldTrial, prior, later, actor, accepted,
      decomposition, trialExact⟩ :=
    exact_compiler_accepted_fold_work_has_exposure_trial input
  have preferred := exact_fold_work_preferred_at_exposure_trial input foldTrial
    finalTrial boundaryIndex prior trialExact
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :=
    foldAlphaFinalWorkQ16Controller foldTrial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))
  let initial := exactFoldAlphaFinalWorkQ16InitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached workAnswer) later
  have labelsDecomposition :
      exactFoldAlphaFinalWorkQ16RootLabels input foldTrial finalTrial
          boundaryIndex =
        priorLabels ++ (some none, workAnswer) :: laterLabels := by
    unfold exactFoldAlphaFinalWorkQ16RootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  refine ⟨foldTrial, workAnswer, accepted, ?_⟩
  exact machine_labeled_trace_routes_named_answer
    (exact_fold_alpha_final_work_q16_root_labels_form_trace input foldTrial
      finalTrial boundaryIndex)
    (exact_fold_alpha_final_work_q16_root_named_slots_nodup input foldTrial
      finalTrial boundaryIndex)
    (fun slot _ => Finset.mem_univ slot)
    (exact_fold_alpha_final_work_q16_root_residual_enough input foldTrial
      finalTrial boundaryIndex programmedCover)
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_fold_alpha_final_work_q16_root_labels_tape_prefix input foldTrial
      finalTrial boundaryIndex)
    priorLabels laterLabels none workAnswer labelsDecomposition

#print axioms exactCompilerFoldAlphaFinalWorkQ16InputTape
#print axioms foldAlphaFinalWorkQ16NamedSlotInputTape
#print axioms exactFoldAlphaFinalWorkQ16InitialState
#print axioms exactFoldAlphaFinalWorkQ16RootLabels
#print axioms exact_fold_alpha_final_work_q16_root_labels_form_trace
#print axioms exact_fold_alpha_final_work_q16_root_named_slots_nodup
#print axioms exact_fold_alpha_final_work_q16_root_labels_tape_prefix
#print axioms exact_fold_alpha_final_work_q16_root_residual_enough
#print axioms exact_fold_work_preferred_at_exposure_trial
#print axioms exact_compiler_accepted_fold_work_is_routed_by_518_router

end

end AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
