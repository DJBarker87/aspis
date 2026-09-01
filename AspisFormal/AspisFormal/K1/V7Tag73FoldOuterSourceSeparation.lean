import AspisFormal.K1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73ExactFoldWorkExposureTrial

/-!
# Literal source separation for the outer fold-work coordinate

The fold-work query has the deployed 41-byte grinding grammar.  Therefore no
33-byte squeeze/advance answer used by alpha or q16 can occupy the same root
exposure.  The remaining 41-byte final-work case is deliberately not decided
here; it must be discharged by the clean transcript-collision accounting.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldOuterSourceSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldWorkExposureTrial
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem selected_record_eq_of_equal_prefix_length
    {records priorLeft laterLeft priorRight laterRight :
      List UnifiedExposureRecord}
    {left right : UnifiedExposureRecord}
    (leftExact : records = priorLeft ++ left :: laterLeft)
    (rightExact : records = priorRight ++ right :: laterRight)
    (sameIndex : priorLeft.length = priorRight.length) :
    left = right := by
  have leftAt : records[priorLeft.length]? = some left := by
    rw [leftExact]
    simp
  have rightAt : records[priorRight.length]? = some right := by
    rw [rightExact]
    simp
  rw [sameIndex, rightAt] at leftAt
  exact Option.some.inj leftAt.symm

theorem machine_fresh_prefix_lengths_ne_of_input_lengths_ne
    {records priorLeft laterLeft priorRight laterRight :
      List UnifiedExposureRecord}
    {leftActor rightActor : QueryActor}
    {leftInput rightInput : ShaInput}
    {leftAnswer rightAnswer : Digest256}
    (leftExact : records = priorLeft ++
      (.machineFresh leftActor leftInput leftAnswer : UnifiedExposureRecord) ::
        laterLeft)
    (rightExact : records = priorRight ++
      (.machineFresh rightActor rightInput rightAnswer : UnifiedExposureRecord) ::
        laterRight)
    (differentLengths : leftInput.length ≠ rightInput.length) :
    priorLeft.length ≠ priorRight.length := by
  intro sameIndex
  have recordExact := selected_record_eq_of_equal_prefix_length leftExact
    rightExact sameIndex
  have inputExact : leftInput = rightInput := by
    injection recordExact
  exact differentLengths (congrArg List.length inputExact)

@[simp] theorem literal_fold_work_input_length
    (digest : Digest256) (nonce : NonceBytes) :
    (bytes digest ++ [domGrind] ++ bytes nonce).length = 41 := by
  simp [bytes_length]

/-- Any literal 33-byte root coordinate is at a different compiler exposure
from the accepted fold-work coordinate. -/
theorem exact_33_byte_root_prefix_ne_fold_trial
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
    (foldTrial : ExactCompilerExposureTrial parameters)
    (foldDigest foldAnswer : Digest256)
    (foldActor : QueryActor) (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root =
      foldPrior ++
        (.machineFresh foldActor
          (bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          foldAnswer : UnifiedExposureRecord) :: foldLater)
    (trialExact : foldTrial.val = foldPrior.length)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (inputLength : queryInput.length = 33) :
    prior.length ≠ foldTrial.val := by
  rw [trialExact]
  apply machine_fresh_prefix_lengths_ne_of_input_lengths_ne decomposition
    foldExact
  rw [inputLength, literal_fold_work_input_length]
  decide

/-- Every non-final-work label of the established 517-slot controller is a
literal 33-byte alpha/q16 squeeze answer.  This statement follows the exact
accepted root cursor; it does not classify arbitrary adversary inputs. -/
theorem exact_underlying_nonfinal_preferred_input_length
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
    (slot : AlphaFinalWorkQ16DigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (notFinalWork : slot ≠ Sum.inr none)
    (preferred :
      (alphaFinalWorkQ16DagController transitionFuel trial.val
        (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (alphaFinalWorkQ16DagController transitionFuel trial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)) prior
          (exactAlphaFinalWorkQ16InitialState input)) = some slot) :
    queryInput.length = 33 := by
  let alphaState := indexedStateAfterRecords transitionFuel
    (alphaZeroCausalController transitionFuel boundaryIndex) prior
    (exactAlphaZeroInitialState input)
  let dagState := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial) prior
    (exactDagCandidateInitialState input)
  let combinedState := indexedStateAfterRecords transitionFuel
    (alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)) prior
    (exactAlphaFinalWorkQ16InitialState input)
  have alphaProjection : alphaIndexedState combinedState = alphaState := by
    rw [alpha_indexed_state_after_composed_records]
    rfl
  have dagProjection : finalWorkQ16IndexedState combinedState = dagState := by
    rw [final_work_q16_indexed_state_after_composed_records]
    rfl
  have alphaAligned : unifiedRecordAtAnswer transitionFuel alphaState.cursor
      answer = (UnifiedExposureRecord.machineFresh actor queryInput answer) := by
    have aligned := exact_root_records_aligned_for_alpha_zero_controller input
      boundaryIndex prior (.machineFresh actor queryInput answer) later
        decomposition
    simpa [alphaState, UnifiedExposureRecord.answer] using aligned
  have alphaInputExact : unifiedInputBeforeAnswer? transitionFuel
      alphaState.cursor = some queryInput :=
    aligned_machine_record_has_exact_input transitionFuel alphaState.cursor actor
      queryInput answer alphaAligned
  have dagAligned : unifiedRecordAtAnswer transitionFuel dagState.cursor answer =
      (UnifiedExposureRecord.machineFresh actor queryInput answer) := by
    have aligned := exact_root_records_aligned_for_dag_controller input trial.val
      prior (.machineFresh actor queryInput answer) later decomposition
    simpa [dagState, exactDagTrialController,
      UnifiedExposureRecord.answer] using aligned
  have dagInputExact : unifiedInputBeforeAnswer? transitionFuel dagState.cursor =
      some queryInput :=
    aligned_machine_record_has_exact_input transitionFuel dagState.cursor actor
      queryInput answer dagAligned
  change
    (match alphaZeroPreferredSlot transitionFuel
        (alphaIndexedState combinedState) with
      | some alphaSlot => some (Sum.inl alphaSlot)
      | none =>
          (dagCandidatePreferredSlot transitionFuel trial.val
            (finalWorkQ16IndexedState combinedState)).map Sum.inr) =
      some slot at preferred
  rw [alphaProjection, dagProjection] at preferred
  cases alphaPreferred : alphaZeroPreferredSlot transitionFuel alphaState with
  | some alphaSlot =>
      rw [alphaPreferred] at preferred
      have slotExact : slot = Sum.inl alphaSlot := by
        exact (Option.some.inj preferred).symm
      subst slot
      obtain ⟨selectedInput, producer, selectedInputExact, _producerMember,
          selectedIsOutput, _slotExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel alphaState
          alphaSlot alphaPreferred
      have selectedInputEq : selectedInput = queryInput :=
        Option.some.inj (selectedInputExact.symm.trans alphaInputExact)
      rw [← selectedInputEq, selectedIsOutput]
      simp
  | none =>
      rw [alphaPreferred] at preferred
      cases dagPreferred : dagCandidatePreferredSlot transitionFuel trial.val
          dagState with
      | none => simp [dagPreferred] at preferred
      | some dagSlot =>
          rw [dagPreferred] at preferred
          have slotExact : slot = Sum.inr dagSlot := by
            exact (Option.some.inj preferred).symm
          subst slot
          cases dagSlot with
          | none => exact (notFinalWork rfl).elim
          | some q16Slot =>
              have dagPreferredInput : dagPreferredSlotForInput trial.val
                  dagState.exposureIndex dagState.memory queryInput =
                  some (some q16Slot) := by
                change dagCandidatePreferredSlot transitionFuel trial.val
                    dagState = some (some q16Slot) at dagPreferred
                unfold dagCandidatePreferredSlot at dagPreferred
                rw [dagInputExact] at dagPreferred
                exact dagPreferred
              obtain ⟨producer, _producerMember, sourceIsOutput,
                  _slotExact⟩ :=
                dag_preferred_q16_slot_has_producer trial.val
                  dagState.exposureIndex dagState.memory queryInput q16Slot
                    dagPreferredInput
              rw [sourceIsOutput]
              simp

/-- Consequently every alpha/q16 source record is separated from the fold
exposure automatically; only the final-work label needs the clean-collision
bridge. -/
theorem exact_underlying_nonfinal_prefix_ne_fold_trial
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
    (foldDigest foldAnswer : Digest256) (foldActor : QueryActor)
    (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root =
      foldPrior ++
        (.machineFresh foldActor
          (bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          foldAnswer : UnifiedExposureRecord) :: foldLater)
    (foldTrialExact : foldTrial.val = foldPrior.length)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : AlphaFinalWorkQ16DigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (notFinalWork : slot ≠ Sum.inr none)
    (preferred :
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)) prior
          (exactAlphaFinalWorkQ16InitialState input)) = some slot) :
    prior.length ≠ foldTrial.val := by
  apply exact_33_byte_root_prefix_ne_fold_trial input foldTrial foldDigest
    foldAnswer foldActor foldPrior foldLater foldExact foldTrialExact actor
      queryInput answer prior later decomposition
  exact exact_underlying_nonfinal_preferred_input_length input finalTrial
    boundaryIndex prior later actor queryInput answer slot decomposition
      notFinalWork preferred

#print axioms selected_record_eq_of_equal_prefix_length
#print axioms machine_fresh_prefix_lengths_ne_of_input_lengths_ne
#print axioms literal_fold_work_input_length
#print axioms exact_33_byte_root_prefix_ne_fold_trial
#print axioms exact_underlying_nonfinal_preferred_input_length
#print axioms exact_underlying_nonfinal_prefix_ne_fold_trial

end

end AspisK1.V7Tag73FoldOuterSourceSeparation
