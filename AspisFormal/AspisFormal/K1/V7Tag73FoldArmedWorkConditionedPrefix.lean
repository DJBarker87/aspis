import AspisFormal.K1.V7Tag73FoldArmedPreFinalPrefix

/-!
# Fold-armed prefix replay conditioned on both work coordinates

The K1.3 one-forest argument fixes the residual/alpha context, the selected
fold-work answer, and the selected final-work answer before varying the q16
forest.  Consequently a source prefix that has used no q16 named slot is
fully determined even when a malicious adversary exposed final work early.

This is the exact mixed residual/named transport lemma for that cut.  It does
not assume a protocol role from raw SHA bytes: the caller supplies the label
inventory obtained from the executable causal controller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73FoldArmedWorkConditionedPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
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

/-- Equal context/fold/work coordinates replay an exact root prefix whose
causal labels contain no q16 candidate slot.  The allowed labels are residual,
fold work, one of the four alpha blocks, and final work. -/
theorem exact_fold_armed_coordinates_force_work_conditioned_prefix
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
          (exactPlainRomCursor configuration sample.1).erase) right).2.1)
    (workExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
          transitionFuel foldTrial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase) sample.2).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
        (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
          transitionFuel foldTrial.val finalTrial.val
          (exactPlainRomCursor configuration sample.1).erase) right).2.2.1)
    (noQ16 :
      let controller := foldArmedCompleteController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel foldTrial.val finalTrial.val
      let initial := foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase
      ∀ slot ∈ namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller initial
            prior),
        slot = none ∨
          (∃ alpha : Fin 4, slot = some (Sum.inl alpha)) ∨
          slot = some (Sum.inr none)) :
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
    exact congrArg Prod.fst contextExact
  have alphaExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        sample.2).1.2 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1.2 := congrArg Prod.snd contextExact
  have namedExact : ∀ current : ↥(Finset.univ :
      Finset FoldAlphaFinalWorkQ16DigestSlot),
      current.1 ∈ namedTraceSlots prefixLabels →
        (router.coordinateEquiv leftTape).1 current =
          (router.coordinateEquiv rightTape).1 current := by
    intro current used
    rcases noQ16 current.1 used with foldSlot | alphaOrWork
    · have currentExact : current =
          ⟨none, Finset.mem_univ none⟩ := Subtype.ext foldSlot
      subst current
      change
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          sample.2).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1
      exact foldExact
    · rcases alphaOrWork with ⟨alpha, alphaSlot⟩ | workSlot
      · have currentExact : current =
            ⟨some (Sum.inl alpha), Finset.mem_univ _⟩ :=
          Subtype.ext alphaSlot
        subst current
        change
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            sample.2).1.2 alpha =
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            right).1.2 alpha
        exact congrFun alphaExact alpha
      · have currentExact : current =
            ⟨some (Sum.inr none), Finset.mem_univ _⟩ :=
          Subtype.ext workSlot
        subst current
        change
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            sample.2).2.2.1 =
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            right).2.2.1
        exact workExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    trace_forces_right_prefix_of_used_coordinate_agreement prefixTrace
      namedNodup (fun slot _ => Finset.mem_univ slot) residualEnough leftTape
      rightTape (by
        exact leftTraceExact) residualExact namedExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer := by
    exact indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  refine ⟨rightRemaining, ?_⟩
  rw [prefixAnswers] at rightPrefix
  exact rightPrefix

#print axioms exact_fold_armed_coordinates_force_work_conditioned_prefix

end

end AspisK1.V7Tag73FoldArmedWorkConditionedPrefix
