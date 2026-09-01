import AspisFormal.K1.V7Tag73ExactAlphaQ16InventoryDisjoint

/-!
# Preserve final-work/q16 labels in the composed 517-slot controller

At an exact accepted-root prefix, a final-work or q16 label cannot also be an
alpha-zero label.  Final work is excluded by fixed input width; q16 is excluded
by the proved disjointness of the two causal producer inventories.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAlphaDagPrioritySeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactAlphaQ16InventoryDisjoint
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem dag_preferred_final_work_input_length
    (anchorIndex exposureIndex : Nat) (memory : FinalWorkQ16DagMemory)
    (input : ShaInput)
    (wellFormed : Q16DagAnchorWellFormed memory.anchor)
    (preferred : dagPreferredSlotForInput anchorIndex exposureIndex memory input =
      some none) :
    input.length = 41 := by
  unfold dagPreferredSlotForInput at preferred
  cases raw : dagRawPreferredSlot anchorIndex exposureIndex memory input with
  | none => simp [raw] at preferred
  | some slot =>
      by_cases used : slot ∈ memory.usedSlots
      · simp [raw, used] at preferred
      · simp only [raw, used, if_false] at preferred
        have slotExact : slot = none := Option.some.inj preferred
        subst slot
        cases anchorExact : memory.anchor with
        | inactive =>
            unfold dagRawPreferredSlot at raw
            rw [anchorExact] at raw
            split at raw <;> try contradiction
            cases parsed : rawFinalWorkKeyOfWorkInput? input with
            | none => simp [parsed] at raw
            | some key =>
                unfold rawFinalWorkKeyOfWorkInput? at parsed
                split at parsed <;> try contradiction
                rename_i lengthExact
                exact lengthExact
        | tracked key workSeen =>
            have keyLengths : key.digest.length = 32 ∧ key.nonce.length = 8 := by
              simpa [anchorExact, Q16DagAnchorWellFormed] using wellFormed
            unfold dagRawPreferredSlot at raw
            rw [anchorExact] at raw
            by_cases selected : workSeen = false ∧ input = key.workInput
            · have inputExact : input = key.workInput := selected.2
              rw [inputExact]
              simp [RawFinalWorkKey.workInput, keyLengths.1, keyLengths.2]
            · simp [selected] at raw

theorem exact_alpha_preferred_none_of_dag_preferred
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
    (trial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : FinalWorkQ16DigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (dagPreferred :
      (exactDagTrialController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial) prior
          (exactDagCandidateInitialState input)) = some slot) :
    alphaZeroPreferredSlot transitionFuel
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)) = none := by
  let alphaState := indexedStateAfterRecords transitionFuel
    (alphaZeroCausalController transitionFuel boundaryIndex) prior
    (exactAlphaZeroInitialState input)
  let dagState := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) prior
    (exactDagCandidateInitialState input)
  have alphaAligned : unifiedRecordAtAnswer transitionFuel alphaState.cursor answer =
      UnifiedExposureRecord.machineFresh actor queryInput answer := by
    have aligned := exact_root_records_aligned_for_alpha_zero_controller input
      boundaryIndex prior (.machineFresh actor queryInput answer) later
        decomposition
    simpa [alphaState, UnifiedExposureRecord.answer] using aligned
  have alphaInputExact : unifiedInputBeforeAnswer? transitionFuel
      alphaState.cursor = some queryInput :=
    aligned_machine_record_has_exact_input transitionFuel alphaState.cursor actor
      queryInput answer alphaAligned
  have dagAligned : unifiedRecordAtAnswer transitionFuel dagState.cursor answer =
      UnifiedExposureRecord.machineFresh actor queryInput answer := by
    have aligned := exact_root_records_aligned_for_dag_controller input trial.val
      prior (.machineFresh actor queryInput answer) later decomposition
    simpa [dagState, exactDagTrialController,
      UnifiedExposureRecord.answer] using aligned
  have dagInputExact : unifiedInputBeforeAnswer? transitionFuel dagState.cursor =
      some queryInput :=
    aligned_machine_record_has_exact_input transitionFuel dagState.cursor actor
      queryInput answer dagAligned
  have dagPreferredInput : dagPreferredSlotForInput trial.val
      dagState.exposureIndex dagState.memory queryInput = some slot := by
    change dagCandidatePreferredSlot transitionFuel trial.val dagState =
      some slot at dagPreferred
    unfold dagCandidatePreferredSlot at dagPreferred
    rw [dagInputExact] at dagPreferred
    exact dagPreferred
  cases alphaPreferred : alphaZeroPreferredSlot transitionFuel alphaState with
  | none => simpa [alphaState] using alphaPreferred
  | some alphaSlot =>
      exfalso
      obtain ⟨selectedInput, alphaProducer, selectedInputExact,
          alphaProducerMember, selectedIsOutput, _blockExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel alphaState
          alphaSlot alphaPreferred
      have selectedInputEq : selectedInput = queryInput :=
        Option.some.inj (selectedInputExact.symm.trans alphaInputExact)
      have alphaInputIsOutput : queryInput =
          bytes alphaProducer.digest ++ [domSqueeze] := by
        rw [← selectedInputEq]
        exact selectedIsOutput
      cases slot with
      | none =>
          have anchorWellFormed : Q16DagAnchorWellFormed dagState.memory.anchor := by
            simpa [dagState] using
              exact_dag_candidate_prefix_anchor_well_formed input trial prior
          have finalLength := dag_preferred_final_work_input_length trial.val
            dagState.exposureIndex dagState.memory queryInput anchorWellFormed
              dagPreferredInput
          have alphaLength : queryInput.length = 33 := by
            rw [alphaInputIsOutput]
            simp
          omega
      | some q16Slot =>
          obtain ⟨q16Producer, q16ProducerMember, q16InputIsOutput,
              _q16SlotExact⟩ :=
            dag_preferred_q16_slot_has_producer trial.val dagState.exposureIndex
              dagState.memory queryInput q16Slot dagPreferredInput
          have outputInputsEqual :
              bytes alphaProducer.digest ++ [domSqueeze] =
                bytes q16Producer.digest ++ [domSqueeze] := by
            rw [← alphaInputIsOutput, ← q16InputIsOutput]
          have digestEqual : alphaProducer.digest = q16Producer.digest :=
            output_input_eq_implies_state_eq alphaProducer.digest
              q16Producer.digest outputInputsEqual
          have disjoint := exact_alpha_q16_prefix_producer_digests_disjoint
            input trial boundaryIndex prior
              ((.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
                later)
              (by simpa only [List.append_assoc] using decomposition)
              alphaProducer (by simpa [alphaState] using alphaProducerMember)
              q16Producer (by simpa [dagState] using q16ProducerMember)
          exact disjoint digestEqual

#print axioms dag_preferred_final_work_input_length
#print axioms exact_alpha_preferred_none_of_dag_preferred

end

end AspisK1.V7Tag73ExactAlphaDagPrioritySeparation
