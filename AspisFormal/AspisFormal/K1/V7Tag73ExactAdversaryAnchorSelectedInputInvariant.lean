import AspisFormal.K1.V7Tag73ExactAdversaryAnchorPrefinalChronology
import AspisFormal.K1.V7Tag73ExactDagPreAnchorResidualPrefix

/-!
# Selected-input invariance at an adversary-owned K1.3 anchor

Equal residual coordinates replay the exact answer prefix before the selected
final-work pair.  Because the production root traces are aligned with the
same scheduler cursor, equality of those answers fixes the emitted records,
not only their answer projection.  This module packages that deterministic
fact and applies it to the two accepted K1.3 trials.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73ExactAdversaryAnchorPrefinalChronology
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagPreAnchorResidualPrefix
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Two aligned record prefixes emitted from the same indexed state are equal
when their chronological answer projections agree.  Inputs and actor labels
are recovered from the pre-answer cursor, so this does not assume an answer
classifier. -/
theorem indexed_records_aligned_eq_of_answer_maps_eq
    {globalOracleCalls : Nat} {Memory : Type}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 FinalWorkQ16DigestSlot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory) :
    ∀ left right,
      IndexedRecordsAligned transitionFuel controller state left →
      IndexedRecordsAligned transitionFuel controller state right →
      left.map UnifiedExposureRecord.answer =
        right.map UnifiedExposureRecord.answer →
      left = right := by
  intro left
  induction left generalizing state with
  | nil =>
      intro right _leftAligned _rightAligned answersExact
      cases right with
      | nil => rfl
      | cons head tail => simp at answersExact
  | cons leftHead leftTail ih =>
      intro right leftAligned rightAligned answersExact
      cases right with
      | nil => simp at answersExact
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at answersExact
          have leftHeadExact := leftAligned [] leftHead leftTail (by simp)
          have rightHeadExact := rightAligned [] rightHead rightTail (by simp)
          simp only [indexed_state_after_records_nil] at leftHeadExact
          simp only [indexed_state_after_records_nil] at rightHeadExact
          have headExact : leftHead = rightHead := by
            rw [answersExact.1] at leftHeadExact
            exact leftHeadExact.symm.trans rightHeadExact
          subst rightHead
          have leftTailAligned : IndexedRecordsAligned transitionFuel controller
              (controller.afterAnswer transitionFuel state leftHead.answer)
              leftTail := by
            simpa only [indexed_state_after_records_cons,
              indexed_state_after_records_nil] using
              indexed_records_aligned_segment transitionFuel controller state
                (leftHead :: leftTail) [leftHead] leftTail [] leftAligned (by
                  simp)
          have rightTailAligned : IndexedRecordsAligned transitionFuel controller
              (controller.afterAnswer transitionFuel state leftHead.answer)
              rightTail := by
            simpa only [indexed_state_after_records_cons,
              indexed_state_after_records_nil] using
              indexed_records_aligned_segment transitionFuel controller state
                (leftHead :: rightTail) [leftHead] rightTail [] rightAligned (by
                  simp)
          have tailExact := ih
            (controller.afterAnswer transitionFuel state leftHead.answer)
            rightTail leftTailAligned rightTailAligned answersExact.2
          rw [tailExact]

/-- The fixed-width transcript block encoder is injective. -/
theorem encode_blocks_injective (width : Nat) :
    ∀ count : Nat,
      Function.Injective
        (encodeBlocks : (Fin count → Bytes width) → ByteString) := by
  intro count
  induction count with
  | zero =>
      intro left right _exact
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      intro left right exact
      have splitExact :
          bytes (left 0) ++
              encodeBlocks (fun (index : Fin count) => left index.succ) =
            bytes (right 0) ++
              encodeBlocks (fun (index : Fin count) => right index.succ) := by
        simpa [encodeBlocks, List.ofFn_succ] using exact
      obtain ⟨headExact, tailExact⟩ := List.append_inj splitExact (by simp)
      have headValueExact : left 0 = right 0 :=
        List.ofFn_injective headExact
      have tailValueExact :
          (fun (index : Fin count) => left index.succ) =
            (fun (index : Fin count) => right index.succ) := ih tailExact
      funext index
      refine Fin.cases headValueExact (fun tailIndex => ?_) index
      exact congrFun tailValueExact tailIndex

/-- Every proof-relevant actual K1.3 trial exposes the earlier member of its
literal final-work pair.  The selected input carries the exact source-bound
pre-final digest, irrespective of which actor first queried it. -/
theorem exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
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
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial) :
    ∃ prior later actor target answer digest base absorbActor,
      exactFixedRootRecords input.package.root =
        prior ++ (.machineFresh actor target answer : UnifiedExposureRecord) ::
          later ∧
      trial.val = prior.length ∧
      HasLiteralStatePrefix digest target ∧
      ExactOperationalPrefinalDigest input digest ∧
      base = (exactOperationalRawTrace input).q16BaseDigest ∧
      (.machineFresh absorbActor
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
        base : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
  obtain ⟨digest, workAnswer, base, _workAccepted, prefinalOrigin,
      baseExact, pairLabeled, _workLabeled, _workCoordinate, _realized⟩ :=
    actual
  rcases pairLabeled with
      ⟨prior, middle, later, workActor, absorbActor, pairExact, trialExact⟩ |
      ⟨prior, middle, later, workActor, absorbActor, pairExact, trialExact⟩
  · have absorbMember :
        (.machineFresh absorbActor
          (literalFinalWorkKey digest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
          base : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
      rw [pairExact]
      simp
    refine ⟨prior,
      middle ++ (.machineFresh absorbActor
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
        base : UnifiedExposureRecord) :: later,
      workActor,
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected).workInput,
      workAnswer, digest, base, absorbActor, ?_, trialExact, ?_,
      prefinalOrigin, baseExact, absorbMember⟩
    · simpa only [List.cons_append, List.append_assoc] using pairExact
    · simp [HasLiteralStatePrefix, RawFinalWorkKey.workInput,
        literalFinalWorkKey]
  · have absorbMember :
        (.machineFresh absorbActor
          (literalFinalWorkKey digest
            (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
          base : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
      rw [pairExact]
      simp
    refine ⟨prior,
      middle ++ (.machineFresh workActor
        (literalFinalWorkKey digest
          (exactOperationalTape input).messages.finalGrinding.selected).workInput
        workAnswer : UnifiedExposureRecord) :: later,
      absorbActor,
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected).absorbInput,
      base, digest, base, absorbActor, ?_, trialExact, ?_, prefinalOrigin,
      baseExact, absorbMember⟩
    · simpa only [List.cons_append, List.append_assoc] using pairExact
    · simp [HasLiteralStatePrefix, RawFinalWorkKey.absorbInput,
        literalFinalWorkKey]

/-- The master tape starts with the answers of any literal exact-root prefix.
This is the uncast source form used to compare two accepted trials. -/
theorem exact_master_tape_has_root_record_prefix
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
    (prior later : List UnifiedExposureRecord)
    (selected : UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ selected :: later) :
    ∃ remaining,
      freshAnswerTapeToList sample.2 =
        prior.map UnifiedExposureRecord.answer ++ remaining := by
  have tapeExact := exact_causal_router_tape_has_literal_root_prefix input
  rw [final_work_q16_named_slot_tape_preserves_master_list] at tapeExact
  rw [← exact_fixed_root_records_map_answer input] at tapeExact
  rw [rootExact, List.map_append, List.map_cons] at tapeExact
  exact ⟨selected.answer ::
    (later.map UnifiedExposureRecord.answer ++
      input.package.root.full.projection.rootPrefixes.verifier.remaining),
    by simpa only [List.cons_append, List.append_assoc] using tapeExact⟩

/-- Equal residual coordinates identify the complete exact-root record prefix
before two proof-relevant selected anchors at the same trial index. -/
theorem exact_fixed_clean_k13_equal_residual_selected_root_priors_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (hidden, left))
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (hidden, right))
    (leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord)
    (leftActor rightActor : QueryActor)
    (leftTarget rightTarget : ShaInput)
    (leftAnswer rightAnswer : Digest256)
    (leftRootExact : exactFixedRootRecords leftInput.package.root =
      leftPrior ++ (.machineFresh leftActor leftTarget leftAnswer :
        UnifiedExposureRecord) :: leftLater)
    (rightRootExact : exactFixedRootRecords rightInput.package.root =
      rightPrior ++ (.machineFresh rightActor rightTarget rightAnswer :
        UnifiedExposureRecord) :: rightLater)
    (leftTrialExact : trial.val = leftPrior.length)
    (rightTrialExact : trial.val = rightPrior.length)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    leftPrior = rightPrior := by
  obtain ⟨_rightRemaining, rightTapeFromLeft⟩ :=
    exact_dag_residual_coordinate_forces_pre_anchor_tape_prefix
      leftInput trial leftPrior
      ((.machineFresh leftActor leftTarget leftAnswer :
        UnifiedExposureRecord) :: leftLater)
      (by simpa only [List.cons_append] using leftRootExact)
      leftTrialExact programmedCover right (by
        change
          ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
            (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
              (finalWorkQ16NamedSlotInputTape
                (exactCompilerFinalWorkQ16InputTape parameters left))).2 =
          ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
            (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
              (finalWorkQ16NamedSlotInputTape
                (exactCompilerFinalWorkQ16InputTape parameters right))).2
        exact coordinateExact)
  rw [final_work_q16_named_slot_tape_preserves_master_list] at rightTapeFromLeft
  obtain ⟨_rightSourceRemaining, rightTapeFromRight⟩ :=
    exact_master_tape_has_root_record_prefix rightInput rightPrior rightLater
      (.machineFresh rightActor rightTarget rightAnswer) rightRootExact
  have leftLength : (leftPrior.map UnifiedExposureRecord.answer).length =
      trial.val := by simp [leftTrialExact]
  have rightLength : (rightPrior.map UnifiedExposureRecord.answer).length =
      trial.val := by simp [rightTrialExact]
  have priorAnswersExact :
      leftPrior.map UnifiedExposureRecord.answer =
        rightPrior.map UnifiedExposureRecord.answer := by
    have leftTake : List.take trial.val (freshAnswerTapeToList right) =
        leftPrior.map UnifiedExposureRecord.answer := by
      rw [rightTapeFromLeft, ← leftLength]
      simp
    have rightTake : List.take trial.val (freshAnswerTapeToList right) =
        rightPrior.map UnifiedExposureRecord.answer := by
      rw [rightTapeFromRight, ← rightLength]
      simp
    exact leftTake.symm.trans rightTake
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState leftInput
  have leftAlignedRaw := exact_root_records_aligned_for_dag_controller
    leftInput trial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightInput trial.val
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftInput.package.root) := by
    simpa [controller, initial, exactDagTrialController] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightInput.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftPriorAligned : IndexedRecordsAligned transitionFuel controller initial
      leftPrior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords leftInput.package.root) [] leftPrior
      ((.machineFresh leftActor leftTarget leftAnswer :
        UnifiedExposureRecord) :: leftLater)
    · exact leftAligned
    · simpa only [List.nil_append, List.cons_append] using leftRootExact
  have rightPriorAligned : IndexedRecordsAligned transitionFuel controller initial
      rightPrior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords rightInput.package.root) [] rightPrior
      ((.machineFresh rightActor rightTarget rightAnswer :
        UnifiedExposureRecord) :: rightLater)
    · exact rightAligned
    · simpa only [List.nil_append, List.cons_append] using rightRootExact
  exact indexed_records_aligned_eq_of_answer_maps_eq transitionFuel controller
    initial leftPrior rightPrior leftPriorAligned rightPriorAligned
      priorAnswersExact

/-- At equal residual coordinates, an adversary-owned selected anchor and the
proof-relevant selected anchor of the comparison execution have the identical
literal SHA input and therefore the identical source-bound pre-final digest.
No cross-execution hash injectivity is used. -/
theorem exact_fixed_clean_k13_adversary_anchor_selected_input_and_digest_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ selectedInput leftDigest rightDigest leftBase rightBase
        leftAbsorbActor rightAbsorbActor,
      HasLiteralStatePrefix leftDigest selectedInput ∧
      HasLiteralStatePrefix rightDigest selectedInput ∧
      leftDigest = rightDigest ∧
      ExactOperationalPrefinalDigest leftWitness.input leftDigest ∧
      ExactOperationalPrefinalDigest rightWitness.input rightDigest ∧
      leftBase =
        (exactOperationalRawTrace leftWitness.input).q16BaseDigest ∧
      rightBase =
        (exactOperationalRawTrace rightWitness.input).q16BaseDigest ∧
      (.machineFresh leftAbsorbActor
        (literalFinalWorkKey leftDigest
          (exactOperationalTape leftWitness.input).messages.finalGrinding.selected).absorbInput
        leftBase : UnifiedExposureRecord) ∈
        exactFixedRootRecords leftWitness.input.package.root ∧
      (.machineFresh rightAbsorbActor
        (literalFinalWorkKey rightDigest
          (exactOperationalTape rightWitness.input).messages.finalGrinding.selected).absorbInput
        rightBase : UnifiedExposureRecord) ∈
        exactFixedRootRecords rightWitness.input.package.root := by
  obtain ⟨leftPrior, leftLater, leftInput, leftAnswer, leftDigest, leftBase,
      leftAbsorbActor, leftRootExact, leftTrialExact, leftPrefix, leftOrigin,
      _leftKind, leftBaseExact, leftAbsorbMember⟩ :=
    exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix trial
      leftWitness anchor
  obtain ⟨rightPrior, rightLater, rightActor, rightInput, rightAnswer,
      rightDigest, rightBase, rightAbsorbActor, rightRootExact,
      rightTrialExact, rightPrefix, rightOrigin, rightBaseExact,
      rightAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.input trial rightWitness.actualTrial
  obtain ⟨rightRemaining, rightTapeFromLeft⟩ :=
    exact_dag_residual_coordinate_forces_pre_anchor_tape_prefix
      leftWitness.input trial leftPrior
      ((.machineFresh .adversary leftInput leftAnswer :
        UnifiedExposureRecord) :: leftLater)
      (by simpa only [List.cons_append] using leftRootExact)
      leftTrialExact programmedCover right (by
        change
          ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
            (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
              (finalWorkQ16NamedSlotInputTape
                (exactCompilerFinalWorkQ16InputTape parameters left))).2 =
          ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
            (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
              (finalWorkQ16NamedSlotInputTape
                (exactCompilerFinalWorkQ16InputTape parameters right))).2
        exact coordinateExact)
  rw [final_work_q16_named_slot_tape_preserves_master_list] at rightTapeFromLeft
  obtain ⟨rightSourceRemaining, rightTapeFromRight⟩ :=
    exact_master_tape_has_root_record_prefix rightWitness.input rightPrior
      rightLater (.machineFresh rightActor rightInput rightAnswer)
      rightRootExact
  have leftLength : (leftPrior.map UnifiedExposureRecord.answer).length =
      trial.val := by simp [leftTrialExact]
  have rightLength : (rightPrior.map UnifiedExposureRecord.answer).length =
      trial.val := by simp [rightTrialExact]
  have priorAnswersExact :
      leftPrior.map UnifiedExposureRecord.answer =
        rightPrior.map UnifiedExposureRecord.answer := by
    have leftTake : List.take trial.val (freshAnswerTapeToList right) =
        leftPrior.map UnifiedExposureRecord.answer := by
      rw [rightTapeFromLeft, ← leftLength]
      simp
    have rightTake : List.take trial.val (freshAnswerTapeToList right) =
        rightPrior.map UnifiedExposureRecord.answer := by
      rw [rightTapeFromRight, ← rightLength]
      simp
    exact leftTake.symm.trans rightTake
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState leftWitness.input
  have leftAligned := exact_root_records_aligned_for_dag_controller
    leftWitness.input trial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightWitness.input trial.val
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightWitness.input.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftPriorAligned : IndexedRecordsAligned transitionFuel controller initial
      leftPrior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords leftWitness.input.package.root) [] leftPrior
      ((.machineFresh .adversary leftInput leftAnswer :
        UnifiedExposureRecord) :: leftLater)
    · simpa [controller, initial, exactDagTrialController] using leftAligned
    · simpa only [List.nil_append, List.cons_append] using leftRootExact
  have rightPriorAligned : IndexedRecordsAligned transitionFuel controller initial
      rightPrior := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords rightWitness.input.package.root) [] rightPrior
      ((.machineFresh rightActor rightInput rightAnswer :
        UnifiedExposureRecord) :: rightLater)
    · exact rightAligned
    · simpa only [List.nil_append, List.cons_append] using rightRootExact
  have priorExact : leftPrior = rightPrior :=
    indexed_records_aligned_eq_of_answer_maps_eq transitionFuel controller
      initial leftPrior rightPrior leftPriorAligned rightPriorAligned
        priorAnswersExact
  have leftSelectedAligned := leftAligned leftPrior
    (.machineFresh .adversary leftInput leftAnswer)
    leftLater leftRootExact
  have rightSelectedAligned := rightAligned rightPrior
    (.machineFresh rightActor rightInput rightAnswer)
    rightLater rightRootExact
  have leftInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    .adversary leftInput leftAnswer leftSelectedAligned
  have rightInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller rightPrior initial).cursor
    rightActor rightInput rightAnswer rightSelectedAligned
  have selectedInputExact : leftInput = rightInput := by
    rw [priorExact] at leftInputExact
    exact Option.some.inj (leftInputExact.symm.trans rightInputExact)
  have digestExact : leftDigest = rightDigest := by
    apply digest_bytes_injective
    calc
      bytes leftDigest = leftInput.take 32 := leftPrefix
      _ = rightInput.take 32 := by rw [selectedInputExact]
      _ = bytes rightDigest := rightPrefix.symm
  refine ⟨leftInput, leftDigest, rightDigest, leftBase, rightBase,
    leftAbsorbActor, rightAbsorbActor, leftPrefix, ?_, digestExact,
    leftOrigin, rightOrigin, leftBaseExact, rightBaseExact, leftAbsorbMember,
    rightAbsorbMember⟩
  simpa [selectedInputExact] using rightPrefix

/-- Equal residual fibres have the identical canonical `final256` producer
input.  The proof transports the already-created producer record across the
aligned pre-anchor root prefix and uses per-execution answer uniqueness; it
does not assume that SHA-256 is injective. -/
theorem exact_fixed_clean_k13_adversary_anchor_final256_input_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ (leftBefore rightBefore : EvalState) (digest : Digest256),
      (bytes leftBefore.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape leftWitness.input).messages.finalValues).data) =
        (bytes rightBefore.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape rightWitness.input).messages.finalValues).data) ∧
      tableLookup (exactOperationalTable leftWitness.input)
          (bytes leftBefore.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.input).messages.finalValues).data) =
        some digest ∧
      tableLookup (exactOperationalTable rightWitness.input)
          (bytes rightBefore.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.input).messages.finalValues).data) =
        some digest := by
  obtain ⟨leftRootPrior, leftRootMiddle, leftRootLater, leftProducerInput,
      leftAnchorInput, leftAnchorAnswer, leftDigest, leftRootExact,
      leftTrialExact, _leftProducerLookup, leftAnchorPrefix, leftOrigin⟩ :=
    exact_fixed_k13_adversary_anchor_has_earlier_final256_root_record
      transitionRoom trial leftWitness anchor
  obtain ⟨rightPrior, rightLater, rightActor, rightAnchorInput,
      rightAnchorAnswer, rightDigest, _rightBase, _rightAbsorbActor,
      rightRootExact, rightTrialExact, rightAnchorPrefix, rightOrigin,
      _rightBaseExact, _rightAbsorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
      rightWitness.input trial rightWitness.actualTrial
  let leftPrior : List UnifiedExposureRecord :=
    leftRootPrior ++
      (.machineFresh .adversary leftProducerInput leftDigest :
        UnifiedExposureRecord) :: leftRootMiddle
  have leftSelectedExact :
      exactFixedRootRecords leftWitness.input.package.root =
        leftPrior ++
          (.machineFresh .adversary leftAnchorInput leftAnchorAnswer :
            UnifiedExposureRecord) :: leftRootLater := by
    simpa [leftPrior, List.append_assoc] using leftRootExact
  have leftTrialExact' : trial.val = leftPrior.length := by
    simpa [leftPrior] using leftTrialExact
  have priorExact : leftPrior = rightPrior :=
    exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial hidden
      left right leftWitness.input rightWitness.input leftPrior leftRootLater
      rightPrior rightLater .adversary rightActor leftAnchorInput
      rightAnchorInput leftAnchorAnswer rightAnchorAnswer leftSelectedExact
      rightRootExact leftTrialExact' rightTrialExact programmedCover
      coordinateExact
  let controller := exactDagTrialController transitionFuel trial
  let initial := exactDagCandidateInitialState leftWitness.input
  have leftAlignedRaw := exact_root_records_aligned_for_dag_controller
    leftWitness.input trial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightWitness.input trial.val
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftWitness.input.package.root) := by
    simpa [controller, initial, exactDagTrialController] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightWitness.input.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftSelectedAligned := leftAligned leftPrior
    (.machineFresh .adversary leftAnchorInput leftAnchorAnswer)
    leftRootLater leftSelectedExact
  have rightSelectedAligned := rightAligned rightPrior
    (.machineFresh rightActor rightAnchorInput rightAnchorAnswer)
    rightLater rightRootExact
  have leftInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    .adversary leftAnchorInput leftAnchorAnswer leftSelectedAligned
  have rightInputExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller rightPrior initial).cursor
    rightActor rightAnchorInput rightAnchorAnswer rightSelectedAligned
  have anchorInputExact : leftAnchorInput = rightAnchorInput := by
    rw [priorExact] at leftInputExact
    exact Option.some.inj (leftInputExact.symm.trans rightInputExact)
  have digestExact : leftDigest = rightDigest := by
    apply digest_bytes_injective
    calc
      bytes leftDigest = leftAnchorInput.take 32 := leftAnchorPrefix
      _ = rightAnchorInput.take 32 := by rw [anchorInputExact]
      _ = bytes rightDigest := rightAnchorPrefix.symm
  obtain ⟨leftBefore, leftLookup⟩ := leftOrigin
  obtain ⟨rightBefore, rightLookup⟩ := rightOrigin
  let leftCanonicalInput : ShaInput :=
    bytes leftBefore.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.input).messages.finalValues).data
  let rightCanonicalInput : ShaInput :=
    bytes rightBefore.digest ++
      [domAbsorb,
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.input).messages.finalValues).data
  obtain ⟨leftCanonicalActor, leftCanonicalMember⟩ :=
    exact_final_table_lookup_has_root_record leftWitness.input
      leftCanonicalInput leftDigest (by
        simpa [leftCanonicalInput] using leftLookup)
  have leftProducerMember :
      (.machineFresh .adversary leftProducerInput leftDigest :
          UnifiedExposureRecord) ∈
        exactFixedRootRecords leftWitness.input.package.root := by
    rw [leftRootExact]
    simp
  have leftCanonicalRecordExact :
      (.machineFresh .adversary leftProducerInput leftDigest :
          UnifiedExposureRecord) =
        (.machineFresh leftCanonicalActor leftCanonicalInput leftDigest :
          UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup leftWitness.input)
      leftProducerMember leftCanonicalMember rfl
  have leftProducerCanonical : leftProducerInput = leftCanonicalInput := by
    injection leftCanonicalRecordExact
  obtain ⟨rightCanonicalActor, rightCanonicalMemberRaw⟩ :=
    exact_final_table_lookup_has_root_record rightWitness.input
      rightCanonicalInput rightDigest (by
        simpa [rightCanonicalInput] using rightLookup)
  have transportedProducerMember :
      (.machineFresh .adversary leftProducerInput leftDigest :
          UnifiedExposureRecord) ∈
        exactFixedRootRecords rightWitness.input.package.root := by
    rw [rightRootExact, ← priorExact]
    simp [leftPrior]
  have rightCanonicalMember :
      (.machineFresh rightCanonicalActor rightCanonicalInput leftDigest :
          UnifiedExposureRecord) ∈
        exactFixedRootRecords rightWitness.input.package.root := by
    simpa [digestExact] using rightCanonicalMemberRaw
  have rightCanonicalRecordExact :
      (.machineFresh .adversary leftProducerInput leftDigest :
          UnifiedExposureRecord) =
        (.machineFresh rightCanonicalActor rightCanonicalInput leftDigest :
          UnifiedExposureRecord) :=
    List.inj_on_of_nodup_map
      (exact_root_record_answers_nodup rightWitness.input)
      transportedProducerMember rightCanonicalMember rfl
  have producerInputExact : leftProducerInput = rightCanonicalInput := by
    injection rightCanonicalRecordExact
  refine ⟨leftBefore, rightBefore, leftDigest, ?_, ?_, ?_⟩
  · exact leftProducerCanonical.symm.trans producerInputExact
  · simpa [leftCanonicalInput] using leftLookup
  · simpa [rightCanonicalInput, digestExact] using rightLookup

/-- Equal canonical `final256` producer inputs also fix the exact transcript
state immediately before that absorption.  This is a serialization result,
not an inversion of SHA-256. -/
theorem exact_fixed_clean_k13_adversary_anchor_before_final256_digest_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ leftBefore rightBefore : EvalState,
      leftBefore.digest = rightBefore.digest := by
  obtain ⟨leftBefore, rightBefore, _digest, inputExact, _leftLookup,
      _rightLookup⟩ :=
    exact_fixed_clean_k13_adversary_anchor_final256_input_eq transitionRoom
      trial hidden left right leftWitness rightWitness anchor programmedCover
      coordinateExact
  refine ⟨leftBefore, rightBefore, ?_⟩
  apply digest_bytes_injective
  have prefixExact := congrArg (List.take 32) inputExact
  simpa using prefixExact

/-- The canonical final-256 producer equality fixes every serialized prover
field block before q16. -/
theorem exact_fixed_clean_k13_adversary_anchor_final_values_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    (exactOperationalTape leftWitness.input).messages.finalValues =
      (exactOperationalTape rightWitness.input).messages.finalValues := by
  obtain ⟨leftBefore, rightBefore, digest, inputExact, _leftLookup,
      _rightLookup⟩ :=
    exact_fixed_clean_k13_adversary_anchor_final256_input_eq transitionRoom
      trial hidden left right leftWitness rightWitness anchor programmedCover
      coordinateExact
  have leftDrop :
      List.drop 34
          (bytes leftBefore.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.input).messages.finalValues).data) =
        encodeBlocks
          (exactOperationalTape leftWitness.input).messages.finalValues := by
    simp only [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
    convert (List.drop_append_length
      (l₁ := bytes leftBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape leftWitness.input).messages.finalValues)) using 1 <;>
      simp
  have rightDrop :
      List.drop 34
          (bytes rightBefore.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.input).messages.finalValues).data) =
        encodeBlocks
          (exactOperationalTape rightWitness.input).messages.finalValues := by
    simp only [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
    convert (List.drop_append_length
      (l₁ := bytes rightBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape rightWitness.input).messages.finalValues)) using 1 <;>
      simp
  have finalBytesExact :
      encodeBlocks
          (exactOperationalTape leftWitness.input).messages.finalValues =
        encodeBlocks
          (exactOperationalTape rightWitness.input).messages.finalValues := by
    calc
      _ = List.drop 34
          (bytes leftBefore.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape leftWitness.input).messages.finalValues).data) :=
        leftDrop.symm
      _ = List.drop 34
          (bytes rightBefore.digest ++
            [domAbsorb,
              (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
                (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape rightWitness.input).messages.finalValues).data) := by
        rw [inputExact]
      _ = _ := rightDrop
  exact encode_blocks_injective 16 256 finalBytesExact

#print axioms indexed_records_aligned_eq_of_answer_maps_eq
#print axioms encode_blocks_injective
#print axioms exact_fixed_k13_actual_trial_has_selected_prefinal_prefix
#print axioms exact_master_tape_has_root_record_prefix
#print axioms exact_fixed_clean_k13_equal_residual_selected_root_priors_eq
#print axioms
  exact_fixed_clean_k13_adversary_anchor_selected_input_and_digest_eq
#print axioms
  exact_fixed_clean_k13_adversary_anchor_final256_input_eq
#print axioms
  exact_fixed_clean_k13_adversary_anchor_before_final256_digest_eq
#print axioms
  exact_fixed_clean_k13_adversary_anchor_final_values_eq

end

end AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
