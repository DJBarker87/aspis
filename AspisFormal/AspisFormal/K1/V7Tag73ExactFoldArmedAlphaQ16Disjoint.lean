import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
import AspisFormal.K1.V7Tag73ExactAlphaQ16InventoryDisjoint

/-!
# Exact fold-armed alpha/q16 inventory disjointness

At every accepted post-fold prefix, the dynamically armed alpha inventory has
the same recursive validity and literal-root provenance needed by the frozen
alpha/q16 grammar theorem.  Equal digests would therefore identify two literal
machine records by the clean-root answer uniqueness theorem and force equal
source inputs, contradicting the structural grammar.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedAlphaQ16Disjoint

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaQ16InventoryDisjoint
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaQ16InventoryDisjoint
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagProducerRecordProvenance
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem selected_prefix_split_of_lt
    {A : Type} (root firstPrefix secondPrefix : List A)
    (first second : A) (firstSuffix secondSuffix : List A)
    (firstExact : root = firstPrefix ++ first :: firstSuffix)
    (secondExact : root = secondPrefix ++ second :: secondSuffix)
    (before : firstPrefix.length < secondPrefix.length) :
    ∃ middle,
      secondPrefix = firstPrefix ++ first :: middle ∧
      firstSuffix = middle ++ second :: secondSuffix := by
  let consumed := firstPrefix ++ [first]
  have consumedLength : consumed.length ≤ secondPrefix.length := by
    simp [consumed]
    omega
  have consumedPrefix : consumed <+: secondPrefix := by
    rw [List.prefix_iff_eq_take]
    have rootFirst : root.take consumed.length = consumed := by
      rw [firstExact]
      rw [show firstPrefix ++ first :: firstSuffix =
        consumed ++ firstSuffix by simp [consumed, List.append_assoc]]
      exact List.take_append_length
    have rootSecond : root.take consumed.length =
        secondPrefix.take consumed.length := by
      rw [secondExact, List.take_append_of_le_length consumedLength]
    exact rootFirst.symm.trans rootSecond
  obtain ⟨middle, secondPrefixExact⟩ := consumedPrefix
  refine ⟨middle, ?_, ?_⟩
  · simpa [consumed, List.append_assoc] using secondPrefixExact.symm
  · have equal : firstPrefix ++ first :: firstSuffix =
        secondPrefix ++ second :: secondSuffix := firstExact.symm.trans
          secondExact
    rw [← secondPrefixExact] at equal
    have cancelled : consumed ++ firstSuffix =
        consumed ++ (middle ++ second :: secondSuffix) := by
      simpa [consumed, List.append_assoc] using equal
    exact (List.append_right_inj consumed).mp cancelled

theorem exact_fold_armed_alpha_q16_post_fold_prefix_digests_disjoint
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
    (trial : ExactCompilerExposureTrial parameters)
    (segment rest : List UnifiedExposureRecord)
    (laterExact : fold.later = segment ++ rest) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val trial.val
    let initial := foldArmedInitialState
      (exactPlainRomCursor configuration sample.1).erase
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let selected : UnifiedExposureRecord := .machineFresh fold.actor
      (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected)
      fold.answer
    let afterFold := controller.afterAnswer transitionFuel reachedFold
      fold.answer
    let prior := fold.prior ++ [selected] ++ segment
    let alphaState := indexedStateAfterRecords transitionFuel controller
      segment afterFold
    let dagState := indexedStateAfterRecords transitionFuel
      (exactDagTrialController transitionFuel trial) prior
      (exactDagCandidateInitialState input)
    ∀ alpha ∈ alphaState.memory.2.1.alpha.producers,
      ∀ q16 ∈ dagState.memory.producers,
        alpha.digest ≠ q16.digest := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val trial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reachedFold := indexedStateAfterRecords transitionFuel controller
    fold.prior initial
  let selected : UnifiedExposureRecord := .machineFresh fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer
  let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
  let consumed := fold.prior ++ [selected]
  let prior := consumed ++ segment
  let alphaState := indexedStateAfterRecords transitionFuel controller segment
    afterFold
  let dagState := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) prior
    (exactDagCandidateInitialState input)
  have alphaInvariant := exact_fold_armed_post_fold_prefix_invariant input fold
    trial segment rest laterExact
  change FoldArmedAlphaPrefixInvariant prior alphaState.memory.2.1 at alphaInvariant
  have decomposition : exactFixedRootRecords input.package.root = prior ++ rest := by
    rw [fold.rootDecomposition, laterExact]
    simp [prior, consumed, selected, List.append_assoc]
  have dagInvariant : Q16DagMemoryProducerInvariant dagState.memory := by
    simpa [dagState] using exact_dag_candidate_prefix_producer_invariant input
      trial prior rest decomposition
  dsimp only
  intro alpha alphaMember q16 q16Member
  obtain ⟨key, base, workSeen, anchorExact, baseExact⟩ :=
    producer_member_implies_tracks_some_base dagState.memory q16 dagInvariant
      q16Member
  have q16Valid : Q16DagProducerInventoryValid base
      dagState.memory.producers := dagInvariant.inventoryValid base baseExact
  apply alpha_q16_producer_digests_disjoint
    alphaState.memory.2.1.alpha.producers dagState.memory.producers base
      alphaInvariant.core.producer.inventoryValid
      alphaInvariant.core.blockZeroBoundary q16Valid
  · intro candidate candidateMember dagProducer dagProducerMember digestEqual
    obtain ⟨alphaActor, alphaRecord⟩ :=
      alphaInvariant.sourcesLiteral candidate candidateMember
    obtain ⟨dagActor, dagRecord⟩ :=
      exact_dag_prefix_producer_has_literal_record input trial prior rest
        decomposition dagProducer (by simpa [dagState] using dagProducerMember)
    have alphaRoot :
        (.machineFresh alphaActor candidate.sourceInput candidate.digest :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [decomposition, List.mem_append]
      exact Or.inl alphaRecord
    have dagRoot :
        (.machineFresh dagActor dagProducer.sourceInput dagProducer.digest :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [decomposition, List.mem_append]
      exact Or.inl dagRecord
    have recordExact :
        (.machineFresh alphaActor candidate.sourceInput candidate.digest :
          UnifiedExposureRecord) =
        (.machineFresh dagActor dagProducer.sourceInput dagProducer.digest :
          UnifiedExposureRecord) :=
      List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
        alphaRoot dagRoot digestEqual
    injection recordExact
  · simpa [alphaState] using alphaMember
  · simpa [dagState, prior, consumed, selected] using q16Member

/-- At any literal accepted q16 output record, q16 priority is preserved by
the fold-armed composition.  Before fold the alpha inventory is empty; at the
fold ordinal the 33-byte q16 input cannot be the 41-byte fold input; after
fold, the exact cross-inventory disjointness theorem applies. -/
theorem exact_fold_armed_alpha_preferred_none_of_q16_preferred
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
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : Fin 64 × Fin 8)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (dagPreferred :
      (exactDagTrialController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial) prior
          (exactDagCandidateInitialState input)) = some (some slot)) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val trial.val
    let reached := indexedStateAfterRecords transitionFuel controller prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
    alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState (foldArmedAlphaState reached)) = none := by
  dsimp only
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val trial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let dagState := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) prior
    (exactDagCandidateInitialState input)
  have rootAligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial trial
  have selectedAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      answer = (.machineFresh actor queryInput answer : UnifiedExposureRecord) :=
    rootAligned prior _ later decomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some queryInput := aligned_machine_record_has_exact_input transitionFuel
        reached.cursor actor queryInput answer selectedAligned
  have dagPreferredInput : dagPreferredSlotForInput trial.val
      dagState.exposureIndex dagState.memory queryInput = some (some slot) := by
    change dagCandidatePreferredSlot transitionFuel trial.val dagState =
      some (some slot) at dagPreferred
    unfold dagCandidatePreferredSlot at dagPreferred
    have dagAligned := exact_root_records_aligned_for_dag_controller input
      trial.val prior (.machineFresh actor queryInput answer) later decomposition
    have dagInputExact : unifiedInputBeforeAnswer? transitionFuel
        dagState.cursor = some queryInput :=
      aligned_machine_record_has_exact_input transitionFuel dagState.cursor
        actor queryInput answer (by simpa [dagState,
          exactDagTrialController, UnifiedExposureRecord.answer] using dagAligned)
    rw [dagInputExact] at dagPreferred
    exact dagPreferred
  obtain ⟨q16Producer, q16ProducerMember, q16InputIsOutput,
      _q16SlotExact⟩ :=
    dag_preferred_q16_slot_has_producer trial.val dagState.exposureIndex
      dagState.memory queryInput slot dagPreferredInput
  rcases Nat.lt_trichotomy prior.length fold.trial.val with before | equal | after
  · have empty := fold_armed_alpha_empty_before_selected_fold transitionFuel
      fold.trial.val trial.val prior initial (by
        simpa [initial, foldArmedInitialState] using before.le)
        (by rfl) (by rfl)
    change reached.memory.2.1.expectedBoundary = none ∧
      reached.memory.2.1.alpha.producers = [] at empty
    unfold alphaZeroPreferredSlot
    have projectedInput : unifiedInputBeforeAnswer? transitionFuel
        (foldArmedAlphaIndexedState (foldArmedAlphaState reached)).cursor =
          some queryInput := by
      change unifiedInputBeforeAnswer? transitionFuel reached.cursor =
        some queryInput
      exact inputExact
    rw [projectedInput]
    rw [show (foldArmedAlphaIndexedState
      (foldArmedAlphaState reached)).memory.producers = [] by exact empty.2]
    simp [alphaZeroOutputSlot?]
  · exfalso
    have distinct := exact_accepted_fold_trial_ne_root_record_of_input_length
      input fold prior later actor queryInput answer decomposition (by
        rw [q16InputIsOutput]
        simp)
    exact distinct (by simpa [fold.trialExact] using equal.symm)
  · obtain ⟨segment, priorExact, laterExact⟩ := selected_prefix_split_of_lt
      (exactFixedRootRecords input.package.root) fold.prior prior
      (.machineFresh fold.actor
        (bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        fold.answer)
      (.machineFresh actor queryInput answer) fold.later later
      fold.rootDecomposition decomposition (by
        simpa [fold.trialExact] using after)
    let selected : UnifiedExposureRecord := .machineFresh fold.actor
      (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected)
      fold.answer
    let reachedFold := indexedStateAfterRecords transitionFuel controller
      fold.prior initial
    let afterFold := controller.afterAnswer transitionFuel reachedFold fold.answer
    let postState := indexedStateAfterRecords transitionFuel controller segment
      afterFold
    have consumedState : indexedStateAfterRecords transitionFuel controller
        (fold.prior ++ [selected]) initial = afterFold := by
      rw [indexed_state_after_records_append]
      simp [selected, afterFold, reachedFold, UnifiedExposureRecord.answer]
    have reachedExact : reached = postState := by
      simp only [reached, postState]
      rw [show prior = (fold.prior ++ [selected]) ++ segment by
        simpa [selected, List.append_assoc] using priorExact]
      rw [indexed_state_after_records_append, consumedState]
    have disjoint :=
      exact_fold_armed_alpha_q16_post_fold_prefix_digests_disjoint input fold
        trial segment
          ((.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
            later)
          (by simpa [selected, List.append_assoc] using laterExact)
    cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
        (foldArmedAlphaIndexedState (foldArmedAlphaState reached)) with
    | none => simpa using alphaPreferred
    | some alphaSlot =>
        exfalso
        obtain ⟨selectedInput, alphaProducer, selectedInputExact,
            alphaProducerMember, selectedIsOutput, _blockExact⟩ :=
          alpha_zero_preferred_slot_has_producer transitionFuel
            (foldArmedAlphaIndexedState (foldArmedAlphaState reached))
            alphaSlot alphaPreferred
        have selectedInputEq : selectedInput = queryInput :=
          Option.some.inj (selectedInputExact.symm.trans (by
            change unifiedInputBeforeAnswer? transitionFuel reached.cursor =
              some queryInput
            exact inputExact))
        have outputInputsEqual :
            bytes alphaProducer.digest ++ [domSqueeze] =
              bytes q16Producer.digest ++ [domSqueeze] := by
          rw [← selectedIsOutput, selectedInputEq, q16InputIsOutput]
        have digestEqual : alphaProducer.digest = q16Producer.digest :=
          output_input_eq_implies_state_eq alphaProducer.digest
            q16Producer.digest outputInputsEqual
        have forbidden := disjoint alphaProducer (by
          have raw : alphaProducer ∈ reached.memory.2.1.alpha.producers :=
            alphaProducerMember
          rw [reachedExact] at raw
          simpa [postState] using raw)
          q16Producer (by
            simpa [dagState, priorExact, selected, List.append_assoc] using
              q16ProducerMember)
        exact forbidden digestEqual

#print axioms exact_fold_armed_alpha_q16_post_fold_prefix_digests_disjoint
#print axioms exact_fold_armed_alpha_preferred_none_of_q16_preferred

end

end AspisK1.V7Tag73ExactFoldArmedAlphaQ16Disjoint
