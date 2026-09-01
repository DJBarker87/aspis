import AspisFormal.K1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73CausalResidualCoordinatePrefix

/-!
# Complete-controller prefix before final work

Before the selected final-work exposure, the underlying causal-DAG controller
is inactive.  Consequently the complete 518-slot controller can use only its
outer fold coordinate or one of the four alpha-zero coordinates on that
prefix.  This is the exact shape needed to replay the prefix while leaving the
later q16 forest unconstrained.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73FoldAlphaPreFinalPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev CompletePreFinalMemory :=
  FoldAlphaFinalWorkQ16ControllerMemory
    (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)

def completePreFinalDagState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      CompletePreFinalMemory) :
    IndexedUnifiedExposureState globalOracleCalls FinalWorkQ16DagMemory :=
  finalWorkQ16IndexedState (underlyingIndexedState state)

@[simp] theorem complete_pre_final_dag_state_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      CompletePreFinalMemory)
    (answer : Digest256) :
    completePreFinalDagState
        ((foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
            (alphaZeroCausalController transitionFuel boundaryIndex))).afterAnswer
              transitionFuel state answer) =
      (finalWorkQ16DagController globalOracleCalls transitionFuel
        finalExposureIndex).afterAnswer transitionFuel
          (completePreFinalDagState state) answer := by
  rfl

theorem complete_pre_final_dag_memory_stays_inactive_one_step
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      CompletePreFinalMemory)
    (answer : Digest256)
    (beforeFinal : state.exposureIndex ≠ finalExposureIndex)
    (inactive : (completePreFinalDagState state).memory = inactiveDagMemory) :
    (completePreFinalDagState
      ((foldAlphaFinalWorkQ16Controller foldExposureIndex
        (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
          (alphaZeroCausalController transitionFuel boundaryIndex))).afterAnswer
            transitionFuel state answer)).memory = inactiveDagMemory := by
  have dagBefore :
      (completePreFinalDagState state).exposureIndex ≠ finalExposureIndex :=
    beforeFinal
  rw [complete_pre_final_dag_state_after_answer]
  simp only [finalWorkQ16DagController,
    IndexedUnifiedExposureController.afterAnswer]
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel
      (completePreFinalDagState state).cursor <;>
    simp [dagCandidateAfterMemory, inputExact, inactive, dagBefore,
      inactiveDagMemory, dagMemoryAfterInput, dagCoreMemoryAfterInput,
      dagPreferredSlotForInput, dagRawPreferredSlot]

/-- Every named coordinate strictly before the final-work exposure is either
the outer fold coordinate or an alpha-zero coordinate. -/
theorem complete_pre_final_named_slots_only_fold_or_alpha
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        CompletePreFinalMemory),
      state.exposureIndex + records.length = finalExposureIndex →
      (completePreFinalDagState state).memory = inactiveDagMemory →
      ∀ slot ∈ namedTraceSlots
        (indexedControllerLabeledRecords transitionFuel
          (foldAlphaFinalWorkQ16Controller foldExposureIndex
            (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
              (alphaZeroCausalController transitionFuel boundaryIndex)))
          state records),
        slot = none ∨ ∃ alpha : Fin 4, slot = some (Sum.inl alpha) := by
  intro records
  induction records with
  | nil =>
      intro state _finalExact _inactive slot member
      simp at member
  | cons record records ih =>
      intro state finalExact inactive slot member
      let underlying : IndexedUnifiedExposureController globalOracleCalls
          Digest256 AlphaFinalWorkQ16DigestSlot
          (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory) :=
        alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
          (alphaZeroCausalController transitionFuel boundaryIndex)
      let controller : IndexedUnifiedExposureController globalOracleCalls
          Digest256 FoldAlphaFinalWorkQ16DigestSlot CompletePreFinalMemory :=
        foldAlphaFinalWorkQ16Controller foldExposureIndex underlying
      let next := controller.afterAnswer transitionFuel state record.answer
      have beforeFinal : state.exposureIndex ≠ finalExposureIndex := by
        intro equal
        rw [equal] at finalExact
        simp only [List.length_cons] at finalExact
        omega
      have dagPreferredNone :
          (finalWorkQ16DagController globalOracleCalls transitionFuel
            finalExposureIndex).preferredSlot
              (completePreFinalDagState state) = none := by
        have dagBefore :
            (completePreFinalDagState state).exposureIndex ≠
              finalExposureIndex := beforeFinal
        unfold finalWorkQ16DagController
        unfold dagCandidatePreferredSlot
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel
            (completePreFinalDagState state).cursor <;>
          simp [inputExact, dagPreferredSlotForInput, dagRawPreferredSlot,
            inactive, dagBefore, inactiveDagMemory]
      have currentShape : controller.preferredSlot state = none ∨
          controller.preferredSlot state = some none ∨
          ∃ alpha : Fin 4,
            controller.preferredSlot state = some (some (Sum.inl alpha)) := by
        by_cases foldHere : state.exposureIndex = foldExposureIndex
        · by_cases foldUsed : state.memory.1 = false
          · exact Or.inr (Or.inl
              (fold_controller_preferred_at_fresh_index foldExposureIndex
                underlying state foldUsed foldHere))
          · have foldUsed' : state.memory.1 = true := Bool.eq_true_of_not_eq_false
              foldUsed
            rw [show controller.preferredSlot state =
                (underlying.preferredSlot (underlyingIndexedState state)).map
                  some by
              simp [controller, foldAlphaFinalWorkQ16Controller, foldHere,
                foldUsed']]
            cases alphaPreferred :
                (alphaZeroCausalController transitionFuel boundaryIndex
                  ).preferredSlot
                    (alphaIndexedState (underlyingIndexedState state)) with
            | none =>
                change alphaZeroPreferredSlot transitionFuel
                    (alphaIndexedState (underlyingIndexedState state)) = none
                  at alphaPreferred
                have dagNone :
                    (finalWorkQ16DagController globalOracleCalls transitionFuel
                      finalExposureIndex).preferredSlot
                        (finalWorkQ16IndexedState
                          (underlyingIndexedState state)) = none := by
                  exact dagPreferredNone
                simp [underlying, alphaFinalWorkQ16DagController,
                  alphaPreferred, dagNone]
            | some alpha =>
                change alphaZeroPreferredSlot transitionFuel
                    (alphaIndexedState (underlyingIndexedState state)) =
                      some alpha at alphaPreferred
                exact Or.inr (Or.inr ⟨alpha, by
                  simp [underlying, alphaFinalWorkQ16DagController,
                    alphaPreferred]⟩)
        · rw [show controller.preferredSlot state =
              (underlying.preferredSlot (underlyingIndexedState state)).map
                some by
            simp [controller, foldAlphaFinalWorkQ16Controller, foldHere]]
          cases alphaPreferred :
              (alphaZeroCausalController transitionFuel boundaryIndex
                ).preferredSlot
                  (alphaIndexedState (underlyingIndexedState state)) with
          | none =>
              change alphaZeroPreferredSlot transitionFuel
                  (alphaIndexedState (underlyingIndexedState state)) = none
                at alphaPreferred
              have dagNone :
                  (finalWorkQ16DagController globalOracleCalls transitionFuel
                    finalExposureIndex).preferredSlot
                      (finalWorkQ16IndexedState
                        (underlyingIndexedState state)) = none := by
                exact dagPreferredNone
              simp [underlying, alphaFinalWorkQ16DagController,
                alphaPreferred, dagNone]
          | some alpha =>
              change alphaZeroPreferredSlot transitionFuel
                  (alphaIndexedState (underlyingIndexedState state)) =
                    some alpha at alphaPreferred
              exact Or.inr (Or.inr ⟨alpha, by
                simp [underlying, alphaFinalWorkQ16DagController,
                  alphaPreferred]⟩)
      simp only [indexed_controller_labeled_records_cons] at member
      rcases currentShape with currentNone | currentFold | currentAlpha
      · rw [currentNone] at member
        simp only [named_trace_slots_none_cons] at member
        apply ih next
        · simp only [next, controller, indexed_after_answer_exposure_index,
            List.length_cons] at finalExact ⊢
          omega
        · exact complete_pre_final_dag_memory_stays_inactive_one_step
            transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
              state record.answer beforeFinal inactive
        · exact member
      · rw [currentFold] at member
        simp only [named_trace_slots_some_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact Or.inl rfl
        · apply ih next
          · simp only [next, controller, indexed_after_answer_exposure_index,
              List.length_cons] at finalExact ⊢
            omega
          · exact complete_pre_final_dag_memory_stays_inactive_one_step
              transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
                state record.answer beforeFinal inactive
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
          · exact complete_pre_final_dag_memory_stays_inactive_one_step
              transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
                state record.answer beforeFinal inactive
          · exact member

/-- Equality of the complete residual/alpha context and fold coordinate
replays the literal root prefix strictly before final work.  The final-work
answer and the entire q16 forest remain free. -/
theorem exact_fold_alpha_coordinates_force_pre_final_tape_prefix
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
    (prior later : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (finalTrialExact : finalTrial.val = prior.length)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (contextExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
          foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))
          (inactiveAlphaZeroMemory, inactiveDagMemory)
          (exactPlainRomCursor configuration sample.1).erase) sample.2).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
          foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))
          (inactiveAlphaZeroMemory, inactiveDagMemory)
          (exactPlainRomCursor configuration sample.1).erase) right).1)
    (foldExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
          foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))
          (inactiveAlphaZeroMemory, inactiveDagMemory)
          (exactPlainRomCursor configuration sample.1).erase) sample.2).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
          foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))
          (inactiveAlphaZeroMemory, inactiveDagMemory)
          (exactPlainRomCursor configuration sample.1).erase) right).2.1) :
    ∃ rightRemaining,
      freshAnswerTapeToList
        (foldAlphaFinalWorkQ16NamedSlotInputTape
          (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters right)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let underlying : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      AlphaFinalWorkQ16DigestSlot
      (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory) :=
    alphaFinalWorkQ16DagController transitionFuel finalTrial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompletePreFinalMemory :=
    foldAlphaFinalWorkQ16Controller foldTrial.val underlying
  let initial := exactFoldAlphaFinalWorkQ16InitialState input
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller prior initial) later
  have labelsExact : exactFoldAlphaFinalWorkQ16RootLabels input foldTrial
      finalTrial boundaryIndex = prefixLabels ++ suffixLabels := by
    unfold exactFoldAlphaFinalWorkQ16RootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  obtain ⟨prefixState, prefixTrace⟩ : ∃ prefixState,
      MachineLabeledTrace (controller.machine transitionFuel) initial
        prefixLabels prefixState := by
    have rootTrace := exact_fold_alpha_final_work_q16_root_labels_form_trace
      input foldTrial finalTrial boundaryIndex
    have splitTrace : MachineLabeledTrace (controller.machine transitionFuel)
        initial (prefixLabels ++ suffixLabels)
        (indexedStateAfterRecords transitionFuel controller
          (exactFixedRootRecords input.package.root) initial) := by
      simpa only [controller, initial, labelsExact] using rootTrace
    obtain ⟨middle, prefixPart, _suffixPart⟩ :=
      machine_labeled_trace_append_split prefixLabels suffixLabels splitTrace
    exact ⟨middle, prefixPart⟩
  have namedNodup : (namedTraceSlots prefixLabels).Nodup := by
    have full := exact_fold_alpha_final_work_q16_root_named_slots_nodup input
      foldTrial finalTrial boundaryIndex
    rw [labelsExact, named_trace_slots_append] at full
    exact List.Nodup.of_append_left full
  have residualEnough : residualTraceSteps prefixLabels ≤
      (exactCompilerTargetCaps parameters).length - 518 := by
    have full := exact_fold_alpha_final_work_q16_root_residual_enough input
      foldTrial finalTrial boundaryIndex programmedCover
    rw [labelsExact, residual_trace_steps_append] at full
    omega
  have leftPrefix : freshAnswerTapeToList
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      prefixLabels.map Prod.snd ++
        (suffixLabels.map Prod.snd ++
          input.package.root.full.projection.rootPrefixes.verifier.remaining) := by
    rw [exact_fold_alpha_final_work_q16_root_labels_tape_prefix input foldTrial
      finalTrial boundaryIndex, labelsExact, List.map_append, List.append_assoc]
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
  let router := exactCompilerFoldAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val underlying
      (inactiveAlphaZeroMemory, inactiveDagMemory)
      (exactPlainRomCursor configuration sample.1).erase
  let leftTape := foldAlphaFinalWorkQ16NamedSlotInputTape
    (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)
  let rightTape := foldAlphaFinalWorkQ16NamedSlotInputTape
    (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters right)
  have residualExact :
      (router.coordinateEquiv leftTape).2 =
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
    apply complete_pre_final_named_slots_only_fold_or_alpha transitionFuel
      foldTrial.val finalTrial.val boundaryIndex prior initial
    · simpa [initial, exactFoldAlphaFinalWorkQ16InitialState,
        finalTrialExact]
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
    AspisK1.V7Tag73CausalResidualCoordinatePrefix.trace_forces_right_prefix_of_used_coordinate_agreement prefixTrace
      namedNodup (fun slot _ => Finset.mem_univ slot) residualEnough leftTape
      rightTape (by
        change freshAnswerTapeToList leftTape =
          prefixLabels.map Prod.snd ++
            (freshAnswerTapeToList leftTape).drop prefixLabels.length
        exact leftTraceExact) residualExact
      namedExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer := by
    exact indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  refine ⟨rightRemaining, ?_⟩
  rw [prefixAnswers] at rightPrefix
  exact rightPrefix

#print axioms complete_pre_final_named_slots_only_fold_or_alpha
#print axioms exact_fold_alpha_coordinates_force_pre_final_tape_prefix

end

end AspisK1.V7Tag73FoldAlphaPreFinalPrefix
