import AspisFormal.K1.V7Tag73FoldFinalWorkSourceSeparation
import AspisFormal.K1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting

/-!
# Proof-relevant accepted fold trial package

This package retains the one literal accepted fold-work first-creation record,
its exact compiler trial, and the preceding relation-round origin.  Downstream
K1.3 coverage can therefore use the same fold trial for source separation and
for the 518-slot router, rather than choosing two propositionally unrelated
existential witnesses.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactAcceptedFoldTrialPackage

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73FinalWorkEarliestExposure
open AspisK1.V7Tag73ExactFoldWorkExposureTrial
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldFinalWorkSourceSeparation
open AspisK1.V7Tag73FoldOuterSourceSeparation
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

structure ExactAcceptedFoldTrial
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  beforeRelation : EvalState
  digest : Digest256
  answer : Digest256
  boundaryAnswer : Digest256
  trial : ExactCompilerExposureTrial parameters
  prior : List UnifiedExposureRecord
  later : List UnifiedExposureRecord
  actor : QueryActor
  accepted : FoldWork31Accepted answer
  relationLookup :
    tableLookup (exactOperationalTable input)
        (bytes beforeRelation.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              ((exactOperationalTape input).messages.relationSent 0)).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)).data) =
      some digest
  workLookup :
    tableLookup (exactOperationalTable input)
        (bytes digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) =
      some answer
  boundaryLookup :
    tableLookup (exactOperationalTable input)
        (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) =
      some boundaryAnswer
  rootDecomposition :
    exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor
          (bytes digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          answer : UnifiedExposureRecord) :: later
  trialExact : trial.val = prior.length

theorem exact_accepted_fold_trial_exists
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
    Nonempty (ExactAcceptedFoldTrial input) := by
  obtain ⟨beforeRelation, digest, answer, boundaryAnswer, relationLookup,
      workLookup, accepted, boundaryLookup⟩ :=
    exact_operational_relation_zero_and_fold_work_lookups input
  obtain ⟨actor, member⟩ :=
    exact_final_table_lookup_has_root_record input _ answer workLookup
  obtain ⟨prior, later, decomposition⟩ := (List.mem_iff_append).mp member
  have priorLtRoot : prior.length <
      (exactFixedRootRecords input.package.root).length := by
    rw [decomposition]
    simp
  have priorLtCap : prior.length < unifiedFull256ExposureCap parameters := by
    rw [← exact_compiler_full_trace_length transitionFuel configuration sample]
    apply priorLtRoot.trans_le
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp
  let trial : ExactCompilerExposureTrial parameters := ⟨prior.length, priorLtCap⟩
  exact ⟨
    { beforeRelation := beforeRelation
      digest := digest
      answer := answer
      boundaryAnswer := boundaryAnswer
      trial := trial
      prior := prior
      later := later
      actor := actor
      accepted := accepted
      relationLookup := relationLookup
      workLookup := workLookup
      boundaryLookup := boundaryLookup
      rootDecomposition := decomposition
      trialExact := rfl }⟩

noncomputable def exactAcceptedFoldTrial
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : ExactAcceptedFoldTrial input :=
  Classical.choice (exact_accepted_fold_trial_exists input)

/-- The retained fold record is routed at the leftmost slot of the complete
518-coordinate router. -/
theorem exact_accepted_fold_trial_is_routed
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    causalRoutedAnswer? none
      (exactCompilerFoldAlphaFinalWorkQ16Router parameters transitionFuel
        fold.trial.val
        (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
          (alphaZeroCausalController transitionFuel boundaryIndex))
        (inactiveAlphaZeroMemory, inactiveDagMemory)
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaFinalWorkQ16NamedSlotInputTape
        (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2)) =
      some fold.answer := by
  have preferred := exact_fold_work_preferred_at_exposure_trial input
    fold.trial finalTrial boundaryIndex fold.prior fold.trialExact
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot
      (FoldAlphaFinalWorkQ16ControllerMemory
        (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)) :=
    foldAlphaFinalWorkQ16Controller fold.trial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))
  let initial := exactFoldAlphaFinalWorkQ16InitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial fold.prior
  let reached := indexedStateAfterRecords transitionFuel controller fold.prior
    initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached fold.answer) fold.later
  have labelsDecomposition :
      exactFoldAlphaFinalWorkQ16RootLabels input fold.trial finalTrial
          boundaryIndex =
        priorLabels ++ (some none, fold.answer) :: laterLabels := by
    unfold exactFoldAlphaFinalWorkQ16RootLabels
    rw [fold.rootDecomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_fold_alpha_final_work_q16_root_labels_form_trace input fold.trial
      finalTrial boundaryIndex)
    (exact_fold_alpha_final_work_q16_root_named_slots_nodup input fold.trial
      finalTrial boundaryIndex)
    (fun slot _ => Finset.mem_univ slot)
    (exact_fold_alpha_final_work_q16_root_residual_enough input fold.trial
      finalTrial boundaryIndex programmedCover)
    (foldAlphaFinalWorkQ16NamedSlotInputTape
      (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_fold_alpha_final_work_q16_root_labels_tape_prefix input fold.trial
      finalTrial boundaryIndex)
    priorLabels laterLabels none fold.answer labelsDecomposition

/-- The retained fold record and either chronological ordering of the literal
final-work pair occupy different exposure trials. -/
theorem exact_accepted_fold_trial_ne_final_pair_trial
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (finalDigest finalAnswer base : Digest256)
    (prefinal : ExactOperationalPrefinalDigest input finalDigest)
    (pairLabeled : ExactDagFinalWorkPairLabeled input finalTrial
      (literalFinalWorkKey finalDigest
        (exactOperationalTape input).messages.finalGrinding.selected)
      finalAnswer base) :
    fold.trial.val ≠ finalTrial.val := by
  have digestDifferent : fold.digest ≠ finalDigest :=
    exact_relation_fold_digest_ne_operational_prefinal input
      fold.beforeRelation fold.digest finalDigest fold.relationLookup prefinal
  have workInputsDifferent :
      bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected ≠
        (literalFinalWorkKey finalDigest
          (exactOperationalTape input).messages.finalGrinding.selected).workInput := by
    intro equal
    apply digestDifferent
    have prefixEqual := congrArg (List.take 32) equal
    have foldTake : List.take 32
        (bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected) =
        bytes fold.digest := by
      simpa [bytes_length] using
        (List.take_append_length
          (l₁ := bytes fold.digest)
          (l₂ := [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected))
    have finalTake : List.take 32
        (literalFinalWorkKey finalDigest
          (exactOperationalTape input).messages.finalGrinding.selected).workInput =
        bytes finalDigest := by
      simp [RawFinalWorkKey.workInput, literalFinalWorkKey, bytes_length]
    rw [foldTake, finalTake] at prefixEqual
    exact List.ofFn_injective prefixEqual
  intro trialEqual
  rcases pairLabeled with
      ⟨finalPrior, middle, later, workActor, absorbActor, recordsExact,
        finalTrialExact⟩ |
      ⟨finalPrior, middle, later, workActor, absorbActor, recordsExact,
        finalTrialExact⟩
  · have prefixLengthEqual : fold.prior.length = finalPrior.length := by
      rw [← fold.trialExact, trialEqual, finalTrialExact]
    have finalDecomposition :
        exactFixedRootRecords input.package.root =
          finalPrior ++
            (.machineFresh workActor
              (literalFinalWorkKey finalDigest
                (exactOperationalTape input).messages.finalGrinding.selected).workInput
              finalAnswer : UnifiedExposureRecord) ::
            (middle ++
              (.machineFresh absorbActor
                (literalFinalWorkKey finalDigest
                  (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
                base : UnifiedExposureRecord) :: later) := by
      simpa only [List.cons_append, List.append_assoc] using recordsExact
    have recordExact := selected_record_eq_of_equal_prefix_length
      fold.rootDecomposition finalDecomposition prefixLengthEqual
    have inputExact :
        bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected =
          (literalFinalWorkKey finalDigest
            (exactOperationalTape input).messages.finalGrinding.selected).workInput := by
      injection recordExact
    exact workInputsDifferent inputExact
  · have prefixLengthEqual : fold.prior.length = finalPrior.length := by
      rw [← fold.trialExact, trialEqual, finalTrialExact]
    have finalDecomposition :
        exactFixedRootRecords input.package.root =
          finalPrior ++
            (.machineFresh absorbActor
              (literalFinalWorkKey finalDigest
                (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
              base : UnifiedExposureRecord) ::
            (middle ++
              (.machineFresh workActor
                (literalFinalWorkKey finalDigest
                  (exactOperationalTape input).messages.finalGrinding.selected).workInput
                finalAnswer : UnifiedExposureRecord) :: later) := by
      simpa only [List.cons_append, List.append_assoc] using recordsExact
    have recordExact := selected_record_eq_of_equal_prefix_length
      fold.rootDecomposition finalDecomposition prefixLengthEqual
    have inputExact :
        bytes fold.digest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected =
          (literalFinalWorkKey finalDigest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput := by
      injection recordExact
    have lengthExact := congrArg List.length inputExact
    have impossible : (41 : Nat) = 42 := by
      simpa [RawFinalWorkKey.absorbInput, literalFinalWorkKey, bytes_length]
        using lengthExact
    omega

/-- Any root record whose SHA input is not 41 bytes occupies a different
exposure from the retained fold-work query. -/
theorem exact_accepted_fold_trial_ne_root_record_of_input_length
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
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (lengthDifferent : queryInput.length ≠ 41) :
    fold.trial.val ≠ prior.length := by
  intro trialEqual
  have prefixLengthEqual : fold.prior.length = prior.length := by
    rw [← fold.trialExact, trialEqual]
  have recordExact := selected_record_eq_of_equal_prefix_length
    fold.rootDecomposition decomposition prefixLengthEqual
  have inputExact :
      bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected =
        queryInput := by
    injection recordExact
  apply lengthDifferent
  rw [← inputExact]
  simp [bytes_length]

/-- Distinct literal SHA inputs select distinct first-creation records in the
exact root and therefore distinct exposure indices. -/
theorem exact_accepted_fold_trial_ne_root_record_of_input_ne
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
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (inputDifferent :
      bytes fold.digest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected ≠
        queryInput) :
    fold.trial.val ≠ prior.length := by
  intro trialEqual
  have prefixLengthEqual : fold.prior.length = prior.length := by
    rw [← fold.trialExact, trialEqual]
  have recordExact := selected_record_eq_of_equal_prefix_length
    fold.rootDecomposition decomposition prefixLengthEqual
  apply inputDifferent
  injection recordExact

/-- In particular, a final-work record whose digest came from the exact
`final256` absorption cannot occupy the retained fold trial. -/
theorem exact_accepted_fold_trial_ne_final_work_record
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
    (finalDigest answer : Digest256)
    (prefinal : ExactOperationalPrefinalDigest input finalDigest)
    (prior later : List UnifiedExposureRecord) (actor : QueryActor)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor
          (literalFinalWorkKey finalDigest
            (exactOperationalTape input).messages.finalGrinding.selected).workInput
          answer : UnifiedExposureRecord) :: later) :
    fold.trial.val ≠ prior.length := by
  apply exact_accepted_fold_trial_ne_root_record_of_input_ne input fold prior
    later actor _ answer decomposition
  have digestDifferent : fold.digest ≠ finalDigest :=
    exact_relation_fold_digest_ne_operational_prefinal input
      fold.beforeRelation fold.digest finalDigest fold.relationLookup prefinal
  intro inputEqual
  apply digestDifferent
  have prefixEqual := congrArg (List.take 32) inputEqual
  have foldTake : List.take 32
      (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected) =
      bytes fold.digest := by
    simpa [bytes_length] using
      (List.take_append_length
        (l₁ := bytes fold.digest)
        (l₂ := [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected))
  have finalTake : List.take 32
      (literalFinalWorkKey finalDigest
        (exactOperationalTape input).messages.finalGrinding.selected).workInput =
      bytes finalDigest := by
    simp [RawFinalWorkKey.workInput, literalFinalWorkKey, bytes_length]
  rw [foldTake, finalTake] at prefixEqual
  exact List.ofFn_injective prefixEqual

/-- The retained fold trial cannot be the proof-relevant final-work/q16 trial
from the same accepted execution. -/
theorem exact_accepted_fold_trial_ne_actual_final_trial
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (finalTrial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input finalTrial) :
    fold.trial.val ≠ finalTrial.val := by
  obtain ⟨finalDigest, finalAnswer, base, _accepted, prefinal, _baseExact,
      pairLabeled, _workLabeled, _workCoordinate, _realized⟩ := actual
  exact exact_accepted_fold_trial_ne_final_pair_trial input fold finalTrial
    finalDigest finalAnswer base prefinal pairLabeled

#print axioms ExactAcceptedFoldTrial
#print axioms exact_accepted_fold_trial_exists
#print axioms exactAcceptedFoldTrial
#print axioms exact_accepted_fold_trial_is_routed
#print axioms exact_accepted_fold_trial_ne_final_pair_trial
#print axioms exact_accepted_fold_trial_ne_root_record_of_input_length
#print axioms exact_accepted_fold_trial_ne_root_record_of_input_ne
#print axioms exact_accepted_fold_trial_ne_final_work_record
#print axioms exact_accepted_fold_trial_ne_actual_final_trial

end

end AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
