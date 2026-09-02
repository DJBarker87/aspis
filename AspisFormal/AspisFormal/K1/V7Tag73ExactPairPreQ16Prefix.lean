import AspisFormal.K1.V7Tag73ExactPairFoldQ16Dichotomy

/-!
# Common prefix before the first pre-fold q16 exposure

The selected fold-work check may be delayed until after the prover has already
queried q16.  This file handles that honest adversarial ordering directly.  It
splits the literal fold prefix at its first q16-labelled record and replays the
strictly preceding records from the equal non-q16 conditioning coordinates.

No q16 answer is compared, no transcript role is inferred from raw SHA bytes,
and no ordering convention is imposed on the adversary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairPreQ16Prefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairFoldQ16Dichotomy
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedWorkConditionedPrefix
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Every non-q16 fold-armed slot has exactly one of the residual, alpha, or
work shapes accepted by the prefix replay theorem. -/
theorem fold_slot_shape_of_not_q16
    (slot : FoldAlphaFinalWorkQ16DigestSlot)
    (notQ16 : ¬ ∃ query : Fin 64 × Fin 8,
      slot = some (Sum.inr (some query))) :
    slot = none ∨
      (∃ alpha : Fin 4, slot = some (Sum.inl alpha)) ∨
      slot = some (Sum.inr none) := by
  rcases slot with _ | alphaOrWork
  · exact Or.inl rfl
  · rcases alphaOrWork with alpha | workOrQ16
    · exact Or.inr (Or.inl ⟨alpha, rfl⟩)
    · rcases workOrQ16 with _ | query
      · exact Or.inr (Or.inr rfl)
      · exact (notQ16 ⟨query, rfl⟩).elim

/-- A labelled trace containing q16 has a first q16 record, and every named
slot before it has a non-q16 shape.  The statement is on the actual labelled
records, so chronological answers are retained. -/
theorem labeled_records_split_before_first_q16
    (records : List
      (Option FoldAlphaFinalWorkQ16DigestSlot × Digest256))
    (contains : ∃ slot ∈ namedTraceSlots records,
      ∃ query : Fin 64 × Fin 8,
        slot = some (Sum.inr (some query))) :
    ∃ before query answer after,
      records = before ++
        (some (some (Sum.inr (some query))), answer) :: after ∧
      ∀ slot ∈ namedTraceSlots before,
        slot = none ∨
          (∃ alpha : Fin 4, slot = some (Sum.inl alpha)) ∨
          slot = some (Sum.inr none) := by
  induction records with
  | nil => simp [namedTraceSlots] at contains
  | cons head tail ih =>
      rcases head with ⟨label, answer⟩
      cases label with
      | none =>
          simp only [named_trace_slots_none_cons] at contains
          obtain ⟨before, query, targetAnswer, after, exactRecords,
              beforeClean⟩ := ih contains
          refine ⟨(none, answer) :: before, query, targetAnswer, after, ?_, ?_⟩
          · simp [exactRecords]
          · simpa only [named_trace_slots_none_cons] using beforeClean
      | some slot =>
          by_cases currentQ16 : ∃ query : Fin 64 × Fin 8,
              slot = some (Sum.inr (some query))
          · obtain ⟨query, slotExact⟩ := currentQ16
            refine ⟨[], query, answer, tail, ?_, by simp [namedTraceSlots]⟩
            simp [slotExact]
          · have tailContains : ∃ target ∈ namedTraceSlots tail,
                ∃ query : Fin 64 × Fin 8,
                  target = some (Sum.inr (some query)) := by
              rcases contains with ⟨target, targetMember, query, targetExact⟩
              simp only [named_trace_slots_some_cons, List.mem_cons] at targetMember
              rcases targetMember with targetHead | targetTail
              · exact (currentQ16
                  ⟨query, targetHead.symm.trans targetExact⟩).elim
              · exact ⟨target, targetTail, query, targetExact⟩
            obtain ⟨before, query, targetAnswer, after, exactRecords,
                beforeClean⟩ := ih tailContains
            refine ⟨(some slot, answer) :: before, query, targetAnswer,
              after, ?_, ?_⟩
            · simp [exactRecords]
            · intro target targetMember
              simp only [named_trace_slots_some_cons, List.mem_cons] at targetMember
              rcases targetMember with targetHead | targetMember
              · rw [targetHead]
                exact fold_slot_shape_of_not_q16 slot currentQ16
              · exact beforeClean target targetMember

/-- In the delayed-fold branch, the records strictly before the first q16
exposure form one literal answer prefix on both tapes.  This is the exact
source object needed to prove that K1.2 words, gamma, and alpha zero were fixed
before any q16 answer used by the fibre argument. -/
theorem exact_fixed_clean_pair_k13_prior_q16_has_common_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (_rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1)
    (workExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.2.1)
    (priorQ16 :
      let leftFold := exactAcceptedFoldTrial leftWitness.joint.input
      ∃ slot ∈ namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel
            (foldArmedCompleteController
              (globalOracleCalls := globalFull256OracleCallCap parameters)
              transitionFuel foldTrial.val finalTrial.val)
            (foldArmedInitialState
              (exactPlainRomCursor configuration hidden).erase)
            leftFold.prior),
        ∃ query : Fin 64 × Fin 8,
          slot = some (Sum.inr (some query))) :
    ∃ before rootRemaining rightRemaining query answer labelAfter,
      exactFixedRootRecords leftWitness.joint.input.package.root =
          before ++ rootRemaining ∧
      freshAnswerTapeToList
          (foldAlphaFinalWorkQ16NamedSlotInputTape
            (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters right)) =
        before.map UnifiedExposureRecord.answer ++ rightRemaining ∧
      indexedControllerLabeledRecords transitionFuel
          (foldArmedCompleteController
            (globalOracleCalls := globalFull256OracleCallCap parameters)
            transitionFuel foldTrial.val finalTrial.val)
          (foldArmedInitialState
            (exactPlainRomCursor configuration hidden).erase)
          (exactAcceptedFoldTrial leftWitness.joint.input).prior =
        indexedControllerLabeledRecords transitionFuel
            (foldArmedCompleteController
              (globalOracleCalls := globalFull256OracleCallCap parameters)
              transitionFuel foldTrial.val finalTrial.val)
            (foldArmedInitialState
              (exactPlainRomCursor configuration hidden).erase)
            before ++
          (some (some (Sum.inr (some query))), answer) :: labelAfter := by
  let leftFold := exactAcceptedFoldTrial leftWitness.joint.input
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration hidden).erase
  let labels := indexedControllerLabeledRecords transitionFuel controller
    initial leftFold.prior
  obtain ⟨labelBefore, query, answer, labelAfter, labelsExact, beforeClean⟩ :=
    labeled_records_split_before_first_q16 labels (by
      simpa [labels, controller, initial, leftFold] using priorQ16)
  let before := leftFold.prior.take labelBefore.length
  let after := leftFold.prior.drop labelBefore.length
  have foldSplit : leftFold.prior = before ++ after := by
    exact (List.take_append_drop labelBefore.length leftFold.prior).symm
  have labelAppend : labels =
      indexedControllerLabeledRecords transitionFuel controller initial before ++
        indexedControllerLabeledRecords transitionFuel controller
          (indexedStateAfterRecords transitionFuel controller before initial)
          after := by
    dsimp only [labels]
    rw [foldSplit, indexed_controller_labeled_records_append]
  have beforeLabelsLength :
      (indexedControllerLabeledRecords transitionFuel controller initial before).length =
        before.length := by
    have answers := indexed_controller_labeled_records_answers transitionFuel
      controller initial before
    simpa using congrArg List.length answers
  have labelsLength : labels.length = leftFold.prior.length := by
    have answers := indexed_controller_labeled_records_answers transitionFuel
      controller initial leftFold.prior
    simpa [labels] using congrArg List.length answers
  have labelBeforeBound : labelBefore.length ≤ leftFold.prior.length := by
    have strict : labelBefore.length < labels.length := by
      rw [labelsExact]
      simp
    omega
  have beforeLength : before.length = labelBefore.length := by
    simp [before, labelBeforeBound]
  have beforeLabelsExact :
      indexedControllerLabeledRecords transitionFuel controller initial before =
        labelBefore := by
    have leftTake : labels.take labelBefore.length =
        indexedControllerLabeledRecords transitionFuel controller initial before := by
      rw [labelAppend]
      simp [beforeLabelsLength, beforeLength]
    have rightTake : labels.take labelBefore.length = labelBefore := by
      rw [labelsExact]
      simp
    exact leftTake.symm.trans rightTake
  have noQ16Before : ∀ slot ∈ namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel controller initial before),
      slot = none ∨
        (∃ alpha : Fin 4, slot = some (Sum.inl alpha)) ∨
        slot = some (Sum.inr none) := by
    simpa [beforeLabelsExact] using beforeClean
  have rootExact : exactFixedRootRecords leftWitness.joint.input.package.root =
      before ++
        (after ++
          (.machineFresh leftFold.actor
            (bytes leftFold.digest ++ [domGrind] ++
              bytes (exactOperationalTape leftWitness.joint.input).messages.foldGrinding.selected)
            leftFold.answer : UnifiedExposureRecord) :: leftFold.later) := by
    rw [leftFold.rootDecomposition, foldSplit]
    simp only [List.append_assoc]
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_fold_armed_coordinates_force_work_conditioned_prefix
      leftWitness.joint.input foldTrial finalTrial before
        (after ++
          (.machineFresh leftFold.actor
            (bytes leftFold.digest ++ [domGrind] ++
              bytes (exactOperationalTape leftWitness.joint.input).messages.foldGrinding.selected)
            leftFold.answer : UnifiedExposureRecord) :: leftFold.later)
        rootExact programmedCover right contextExact foldExact workExact (by
          simpa [controller, initial] using noQ16Before)
  exact ⟨before,
    after ++
      (.machineFresh leftFold.actor
        (bytes leftFold.digest ++ [domGrind] ++
          bytes (exactOperationalTape leftWitness.joint.input).messages.foldGrinding.selected)
        leftFold.answer : UnifiedExposureRecord) :: leftFold.later,
    rightRemaining, query, answer, labelAfter, rootExact, rightPrefix, by
      simpa [labels, controller, initial, leftFold, beforeLabelsExact] using
        labelsExact⟩

#print axioms fold_slot_shape_of_not_q16
#print axioms labeled_records_split_before_first_q16
#print axioms exact_fixed_clean_pair_k13_prior_q16_has_common_prefix

end

end AspisK1.V7Tag73ExactPairPreQ16Prefix
