import AspisFormal.K1.V7Tag73ExactFoldArmedRootRouting
import AspisFormal.K1.V7Tag73CausalResidualCoordinatePrefix

/-!
# Fold-armed complete-controller prefix before final work

Before the selected final-work exposure the DAG component is inactive, so an
online fold-armed label can only be the outer fold coordinate or one of the
four alpha coordinates.  This makes equality of the residual/alpha/fold
conditioning coordinates sufficient to replay the literal accepted prefix
while leaving final work and q16 unconstrained.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73FoldArmedPreFinalPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldArmedRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev FoldArmedPreFinalMemory := FoldArmedCompleteMemory

def foldArmedPreFinalDagState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedPreFinalMemory) :
    IndexedUnifiedExposureState globalOracleCalls FinalWorkQ16DagMemory :=
  finalWorkQ16IndexedState (foldArmedUnderlyingState state)

@[simp] theorem fold_armed_pre_final_dag_state_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedPreFinalMemory)
    (answer : Digest256) :
    foldArmedPreFinalDagState
        ((foldArmedCompleteController transitionFuel foldExposureIndex
          finalExposureIndex).afterAnswer transitionFuel state answer) =
      (finalWorkQ16DagController globalOracleCalls transitionFuel
        finalExposureIndex).afterAnswer transitionFuel
          (foldArmedPreFinalDagState state) answer := by
  rfl

theorem fold_armed_pre_final_dag_memory_stays_inactive_one_step
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedPreFinalMemory)
    (answer : Digest256)
    (beforeFinal : state.exposureIndex ≠ finalExposureIndex)
    (inactive : (foldArmedPreFinalDagState state).memory = inactiveDagMemory) :
    (foldArmedPreFinalDagState
      ((foldArmedCompleteController transitionFuel foldExposureIndex
        finalExposureIndex).afterAnswer transitionFuel state answer)).memory =
      inactiveDagMemory := by
  have dagBefore :
      (foldArmedPreFinalDagState state).exposureIndex ≠ finalExposureIndex :=
    beforeFinal
  rw [fold_armed_pre_final_dag_state_after_answer]
  simp only [finalWorkQ16DagController,
    IndexedUnifiedExposureController.afterAnswer]
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel
      (foldArmedPreFinalDagState state).cursor <;>
    simp [dagCandidateAfterMemory, inputExact, inactive, dagBefore,
      inactiveDagMemory, dagMemoryAfterInput, dagCoreMemoryAfterInput,
      dagPreferredSlotForInput, dagRawPreferredSlot]

/-- Strictly before final work, the inactive DAG cannot emit a final/q16
label.  Dynamic alpha arming changes producers but not this label shape. -/
theorem fold_armed_pre_final_named_slots_only_fold_or_alpha
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        FoldArmedPreFinalMemory),
      state.exposureIndex + records.length = finalExposureIndex →
      (foldArmedPreFinalDagState state).memory = inactiveDagMemory →
      ∀ slot ∈ namedTraceSlots
        (indexedControllerLabeledRecords transitionFuel
          (foldArmedCompleteController transitionFuel foldExposureIndex
            finalExposureIndex) state records),
        slot = none ∨ ∃ alpha : Fin 4, slot = some (Sum.inl alpha) := by
  intro records
  induction records with
  | nil =>
      intro state _finalExact _inactive slot member
      simp at member
  | cons record records ih =>
      intro state finalExact inactive slot member
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalExposureIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have beforeFinal : state.exposureIndex ≠ finalExposureIndex := by
        intro equal
        rw [equal] at finalExact
        simp only [List.length_cons] at finalExact
        omega
      have dagPreferredNone :
          dagCandidatePreferredSlot transitionFuel finalExposureIndex
            (foldArmedPreFinalDagState state) = none := by
        have dagBefore :
            (foldArmedPreFinalDagState state).exposureIndex ≠
              finalExposureIndex := beforeFinal
        unfold dagCandidatePreferredSlot
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel
            (foldArmedPreFinalDagState state).cursor <;>
          simp [inputExact, dagPreferredSlotForInput, dagRawPreferredSlot,
            inactive, dagBefore, inactiveDagMemory]
      have currentShape : controller.preferredSlot state = none ∨
          controller.preferredSlot state = some none ∨
          ∃ alpha : Fin 4,
            controller.preferredSlot state = some (some (Sum.inl alpha)) := by
        by_cases atFold : state.memory.1 = false ∧
            state.exposureIndex = foldExposureIndex
        · exact Or.inr (Or.inl (by
            simpa [controller] using
              fold_armed_complete_preferred_at_fold transitionFuel
                foldExposureIndex finalExposureIndex state atFold.1 atFold.2))
        · have outerUnderlying : controller.preferredSlot state =
              ((alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
                (foldArmedAlphaZeroController transitionFuel)).preferredSlot
                  (foldArmedUnderlyingState state)).map some := by
            simp [controller, foldArmedCompleteController, atFold]
          rw [outerUnderlying]
          cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
              (foldArmedAlphaIndexedState
                (alphaIndexedState (foldArmedUnderlyingState state))) with
          | some alpha =>
              exact Or.inr (Or.inr ⟨alpha, by
                have underlying := alpha_final_work_q16_preferred_of_alpha
                  transitionFuel finalExposureIndex
                    (foldArmedAlphaZeroController transitionFuel)
                    (foldArmedUnderlyingState state) alpha (by
                      simpa [foldArmedAlphaZeroController] using alphaPreferred)
                simp [underlying]⟩)
          | none =>
              have alphaNone :
                  (foldArmedAlphaZeroController transitionFuel).preferredSlot
                      (alphaIndexedState (foldArmedUnderlyingState state)) =
                    none := by
                simpa [foldArmedAlphaZeroController] using alphaPreferred
              have dagNone :
                  (finalWorkQ16DagController globalOracleCalls transitionFuel
                    finalExposureIndex).preferredSlot
                      (finalWorkQ16IndexedState
                        (foldArmedUnderlyingState state)) = none := by
                change dagCandidatePreferredSlot transitionFuel
                  finalExposureIndex (foldArmedPreFinalDagState state) = none
                exact dagPreferredNone
              exact Or.inl (by
                simp [alphaFinalWorkQ16DagController, alphaPreferred,
                  dagNone])
      simp only [indexed_controller_labeled_records_cons] at member
      rcases currentShape with currentNone | currentFold | currentAlpha
      · rw [currentNone] at member
        simp only [named_trace_slots_none_cons] at member
        apply ih next
        · simp only [next, controller, indexed_after_answer_exposure_index,
            List.length_cons] at finalExact ⊢
          omega
        · exact fold_armed_pre_final_dag_memory_stays_inactive_one_step
            transitionFuel foldExposureIndex finalExposureIndex state
              record.answer beforeFinal inactive
        · exact member
      · rw [currentFold] at member
        simp only [named_trace_slots_some_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact Or.inl rfl
        · apply ih next
          · simp only [next, controller, indexed_after_answer_exposure_index,
              List.length_cons] at finalExact ⊢
            omega
          · exact fold_armed_pre_final_dag_memory_stays_inactive_one_step
              transitionFuel foldExposureIndex finalExposureIndex state
                record.answer beforeFinal inactive
          · exact member
      · obtain ⟨alpha, currentAlpha⟩ := currentAlpha
        rw [currentAlpha] at member
        simp only [named_trace_slots_some_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact Or.inr ⟨alpha, rfl⟩
        · apply ih next
          · simp only [next, controller, indexed_after_answer_exposure_index,
              List.length_cons] at finalExact ⊢
            omega
          · exact fold_armed_pre_final_dag_memory_stays_inactive_one_step
              transitionFuel foldExposureIndex finalExposureIndex state
                record.answer beforeFinal inactive
          · exact member

theorem exact_fold_armed_coordinates_force_pre_final_tape_prefix
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
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (finalTrialExact : finalTrial.val = prior.length)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (contextExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
          transitionFuel foldTrial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase) sample.2).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
          transitionFuel foldTrial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase) right).1)
    (foldExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
          transitionFuel foldTrial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase) sample.2).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
          transitionFuel foldTrial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase) right).2.1) :
    ∃ rightRemaining,
      freshAnswerTapeToList
        (foldAlphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters right)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller prior initial) later
  have labelsExact : exactFoldArmedRootLabels input foldTrial finalTrial =
      prefixLabels ++ suffixLabels := by
    unfold exactFoldArmedRootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  obtain ⟨prefixState, prefixTrace⟩ : ∃ prefixState,
      MachineLabeledTrace (controller.machine transitionFuel) initial
        prefixLabels prefixState := by
    have rootTrace := exact_fold_armed_root_labels_form_trace input foldTrial
      finalTrial
    have splitTrace : MachineLabeledTrace (controller.machine transitionFuel)
        initial (prefixLabels ++ suffixLabels)
        (indexedStateAfterRecords transitionFuel controller
          (exactFixedRootRecords input.package.root) initial) := by
      simpa only [controller, initial, labelsExact] using rootTrace
    obtain ⟨middle, prefixPart, _suffixPart⟩ :=
      machine_labeled_trace_append_split prefixLabels suffixLabels splitTrace
    exact ⟨middle, prefixPart⟩
  have namedNodup : (namedTraceSlots prefixLabels).Nodup := by
    have full := exact_fold_armed_root_named_slots_nodup input foldTrial
      finalTrial
    rw [labelsExact, named_trace_slots_append] at full
    exact List.Nodup.of_append_left full
  have residualEnough : residualTraceSteps prefixLabels ≤
      (exactCompilerTargetCaps parameters).length - 518 := by
    have full := exact_fold_armed_root_residual_enough input foldTrial
      finalTrial programmedCover
    rw [labelsExact, residual_trace_steps_append] at full
    omega
  have leftPrefix : freshAnswerTapeToList
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (suffixLabels.map Prod.snd ++
          input.package.root.full.projection.rootPrefixes.verifier.remaining) := by
    rw [exact_fold_armed_root_labels_tape_prefix input foldTrial finalTrial,
      labelsExact, List.map_append, List.append_assoc]
  have leftTraceExact : freshAnswerTapeToList
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (freshAnswerTapeToList
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)
          )).drop prefixLabels.length := by
    rw [leftPrefix]
    have prefixLength : (prefixLabels.map Prod.snd).length =
        prefixLabels.length := by simp
    rw [← prefixLength, List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration sample.1).erase
  let leftTape := foldAlphaFinalWorkQ16NamedSlotInputTape
    (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)
  let rightTape := foldAlphaFinalWorkQ16NamedSlotInputTape
    (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters right)
  have residualExact : (router.coordinateEquiv leftTape).2 =
      (router.coordinateEquiv rightTape).2 := by
    have residualPart := congrArg Prod.fst contextExact
    change (router.coordinateEquiv leftTape).2 =
      (router.coordinateEquiv rightTape).2
    exact residualPart
  have alphaExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        sample.2).1.2 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1.2 := congrArg Prod.snd contextExact
  have namedShape : ∀ slot ∈ namedTraceSlots prefixLabels,
      slot = none ∨ ∃ alpha : Fin 4, slot = some (Sum.inl alpha) := by
    apply fold_armed_pre_final_named_slots_only_fold_or_alpha transitionFuel
      foldTrial.val finalTrial.val prior initial
    · simpa [initial, foldArmedInitialState, finalTrialExact]
    · rfl
  have namedExact : ∀ current : ↥(Finset.univ :
      Finset FoldAlphaFinalWorkQ16DigestSlot),
      current.1 ∈ namedTraceSlots prefixLabels →
        (router.coordinateEquiv leftTape).1 current =
          (router.coordinateEquiv rightTape).1 current := by
    intro current used
    rcases namedShape current.1 used with foldSlot | ⟨alpha, alphaSlot⟩
    · have currentExact : current =
          ⟨none, Finset.mem_univ none⟩ := Subtype.ext foldSlot
      subst current
      change
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          sample.2).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1
      exact foldExact
    · have currentExact : current =
          ⟨some (Sum.inl alpha), Finset.mem_univ _⟩ := Subtype.ext alphaSlot
      subst current
      change
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          sample.2).1.2 alpha =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1.2 alpha
      exact congrFun alphaExact alpha
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    trace_forces_right_prefix_of_used_coordinate_agreement prefixTrace
      namedNodup (fun slot _ => Finset.mem_univ slot) residualEnough leftTape
      rightTape (by
        change freshAnswerTapeToList leftTape =
          prefixLabels.map Prod.snd ++
            (freshAnswerTapeToList leftTape).drop prefixLabels.length
        exact leftTraceExact) residualExact namedExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer := by
    exact indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  refine ⟨rightRemaining, ?_⟩
  rw [prefixAnswers] at rightPrefix
  exact rightPrefix

#print axioms fold_armed_pre_final_named_slots_only_fold_or_alpha
#print axioms exact_fold_armed_coordinates_force_pre_final_tape_prefix

end

end AspisK1.V7Tag73FoldArmedPreFinalPrefix
