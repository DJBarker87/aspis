import AspisFormal.K1.V7Tag73K13CorrectedPairTrialProbability
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier
import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant
import AspisFormal.K1.V7Tag73ExactPairRootAbsorbChainClosure
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity
import AspisFormal.K1.V7Tag73ExactFixedQ16ScheduleFunctional
import AspisFormal.K1.V7Tag73ExactFoldArmedFinalPairPrefix
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73SchedulerTraceFactorization
import AspisFormal.K1.V7Tag73K13PreQ16RootInvariant

/-!
# Semantic profile for corrected pre-q16 pair trials

The corrected bad set depends on five and only five execution-facing values:
the chronological record prefix, the two Merkle roots, the parsed schedule,
gamma, and the disclosed final vector.  This file records that dependency as
an exact congruence theorem and connects the resulting semantic invariant to
the joint alpha/fold/final-work coordinate probability wrapper.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CorrectedPairProfileInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairRootAbsorbChainClosure
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFoldArmedFinalPairPrefix
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73K13PreQ16RootInvariant
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The corrected witness retains the same literal accepted final-work pair as
the deployed execution. Equal non-q16 coordinates therefore expose a common
answer prefix through the final nonce absorb, without using the obsolete
q16-dependent consistency set. -/
theorem exact_preQ16_clean_pair_has_common_final_absorb_tape_prefix
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
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
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
          right).2.2.1) :
    ∃ completed rootRemaining tapeRemaining,
      exactFixedRootRecords leftWitness.joint.input.package.root =
          completed ++ rootRemaining ∧
        freshAnswerTapeToList right =
          completed.map UnifiedExposureRecord.answer ++ tapeRemaining := by
  obtain ⟨digest, workAnswer, base, _workAccepted, _prefinal, _baseExact,
      pairLabeled, _workLabeled, _workCoordinate, _forest⟩ :=
    leftWitness.joint.actualTrial
  exact exact_fold_armed_coordinates_force_final_pair_tape_prefix
    leftWitness.joint.input foldTrial finalTrial digest workAnswer base
      (exactOperationalTape leftWitness.joint.input).messages.finalGrinding.selected
      pairLabeled programmedCover right contextExact foldExact workExact

/-- The common answer prefix is also a common native scheduler trace prefix.
This supplies the corrected causal bridge used by alpha and gamma replay. -/
theorem exact_preQ16_clean_pair_has_common_final_absorb_trace_prefix
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
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
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
          right).2.2.1) :
    ∃ completed leftRootRemaining rightTraceRemaining,
      exactFixedRootRecords leftWitness.joint.input.package.root =
          completed ++ leftRootRemaining ∧
        (runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration hidden)
          (freshAnswerTapeToList right)).trace =
            completed ++ rightTraceRemaining := by
  obtain ⟨completed, leftRootRemaining, rightTapeRemaining, rootExact,
      rightTapeExact⟩ :=
    exact_preQ16_clean_pair_has_common_final_absorb_tape_prefix foldTrial
      finalTrial hidden left right leftWitness programmedCover contextExact
        foldExact workExact
  let leftTail := exactFixedComputedClientTailRun transitionFuel configuration
    (hidden, left) leftWitness.joint.input.package.root
  have leftTraceExact :
      (runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration hidden)
        (freshAnswerTapeToList left)).trace =
          completed ++ (leftRootRemaining ++ leftTail.trace) := by
    have fullExact := congrArg (fun run => run.trace)
      leftWitness.joint.input.package.factorization.fullRunExact
    change
      (runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration hidden)
        (freshAnswerTapeToList left)).trace =
          (exactFixedRootRecords leftWitness.joint.input.package.root ++
            leftTail.trace) at fullExact
    rw [rootExact] at fullExact
    simpa only [List.append_assoc] using fullExact
  have nativePrefix :
      schedulerNativePrefixRecords transitionFuel
          (exactPlainRomCursor configuration hidden)
          (completed.map UnifiedExposureRecord.answer) = completed :=
    scheduler_native_prefix_records_eq_of_run_trace_prefix transitionFuel
      (exactPlainRomCursor configuration hidden)
      (freshAnswerTapeToList left) completed
        (leftRootRemaining ++ leftTail.trace) leftTraceExact
  obtain ⟨records, finalCursor, traversal⟩ :=
    scheduler_native_prefix_traversal_exists transitionFuel
      (exactPlainRomCursor configuration hidden)
      (completed.map UnifiedExposureRecord.answer)
  have recordsExact :=
    scheduler_native_prefix_traversal_records_exact traversal
  have rightTrace :=
    scheduler_native_prefix_traversal_trace_factorization traversal
      rightTapeRemaining
  rw [← recordsExact, nativePrefix] at rightTrace
  rw [← rightTapeExact] at rightTrace
  exact ⟨completed, leftRootRemaining,
    (runSchedulerNativeListRunFrom transitionFuel transitionFuel finalCursor
      rightTapeRemaining).trace, rootExact, rightTrace⟩

/-- Pure congruence for the corrected consistency set.  No execution,
probability, hash, or source premise is hidden here. -/
theorem exact_preQ16_k13_bad_congr_of_semantic_fields
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftPrior rightPrior : List UnifiedExposureRecord)
    (priorExact : leftPrior = rightPrior)
    (rootsExact : exactK12Roots left = exactK12Roots right)
    (scheduleExact : (exactK13ParsedProof left).schedule =
      (exactK13ParsedProof right).schedule)
    (gammaExact : (exactK13ParsedProof left).gamma =
      (exactK13ParsedProof right).gamma)
    (finalExact : (exactK13ParsedProof left).disclosedFinal =
      (exactK13ParsedProof right).disclosedFinal) :
    exactPreQ16K13Bad decoder left leftPrior =
      exactPreQ16K13Bad decoder right rightPrior := by
  unfold exactPreQ16K13Bad parsedK13Transcript
  rw [priorExact, rootsExact, scheduleExact, gammaExact, finalExact]

/-- Exact semantic endpoint left after generic probability accounting.  The
four alpha answers and both positioned work answers are already fixed by the
coordinate hypotheses; this predicate asks the production trace/source proof
to transport only the fields actually read by `exactPreQ16K13Bad`. -/
def ExactPreQ16CleanK13PairSemanticInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    leftWitness.joint.prior = rightWitness.joint.prior ∧
      exactK12Roots leftWitness.joint.input =
        exactK12Roots rightWitness.joint.input ∧
      (exactK13ParsedProof leftWitness.joint.input).schedule =
        (exactK13ParsedProof rightWitness.joint.input).schedule ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.joint.input).disclosedFinal

/-- Equal joint context and fold coordinates identify the exact chronological
prefix before the selected final-work exposure for either first-query actor. -/
theorem exact_preQ16_clean_pair_selected_priors_eq
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
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
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
          right).2.1) :
    leftWitness.joint.prior = rightWitness.joint.prior := by
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial leftWitness.joint.prior
      ((.machineFresh leftWitness.joint.pivotActor
        leftWitness.joint.pivotInput leftWitness.joint.pivotAnswer :
          UnifiedExposureRecord) :: leftWitness.joint.later)
      (by simpa only [List.cons_append] using leftWitness.joint.rootExact)
      leftWitness.joint.trialExact programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightPrefix
  exact exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix finalTrial
    hidden left right leftWitness.joint.input rightWitness.joint.input
    leftWitness.joint.prior leftWitness.joint.later rightWitness.joint.prior
    rightWitness.joint.later leftWitness.joint.pivotActor
    rightWitness.joint.pivotActor leftWitness.joint.pivotInput
    rightWitness.joint.pivotInput leftWitness.joint.pivotAnswer
    rightWitness.joint.pivotAnswer leftWitness.joint.rootExact
    rightWitness.joint.rootExact leftWitness.joint.trialExact
    rightWitness.joint.trialExact ⟨rightRemaining, rightPrefix⟩

/-- On the adversary-first branch, the common selected prefix retains both
root-to-final chains.  Reversing those chains fixes the literal C1/C2 absorb
inputs and hence both roots by fixed-layout parsing, not hash injectivity. -/
theorem exact_preQ16_clean_pair_adversary_roots_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (actorExact : leftWitness.joint.pivotActor = .adversary)
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
          right).2.1) :
    exactK12Roots leftWitness.joint.input =
      exactK12Roots rightWitness.joint.input := by
  have priorExact := exact_preQ16_clean_pair_selected_priors_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness programmedCover
      contextExact foldExact
  have leftRootExact : exactFixedRootRecords
      leftWitness.joint.input.package.root =
        leftWitness.joint.prior ++
          (.machineFresh .adversary leftWitness.joint.pivotInput
            leftWitness.joint.pivotAnswer : UnifiedExposureRecord) ::
              leftWitness.joint.later := by
    simpa [actorExact] using leftWitness.joint.rootExact
  have rightRootExact : exactFixedRootRecords
      rightWitness.joint.input.package.root =
        leftWitness.joint.prior ++
          (.machineFresh rightWitness.joint.pivotActor
            rightWitness.joint.pivotInput rightWitness.joint.pivotAnswer :
              UnifiedExposureRecord) :: rightWitness.joint.later := by
    rw [priorExact]
    exact rightWitness.joint.rootExact
  let controller := exactDagTrialController transitionFuel finalTrial
  let initial := exactDagCandidateInitialState leftWitness.joint.input
  have leftAlignedRaw := exact_root_records_aligned_for_dag_controller
    leftWitness.joint.input finalTrial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightWitness.joint.input finalTrial.val
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftWitness.joint.input.package.root) := by
    simpa [controller, initial, exactDagTrialController] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightWitness.joint.input.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftSelectedAligned := leftAligned leftWitness.joint.prior
    (.machineFresh .adversary leftWitness.joint.pivotInput
      leftWitness.joint.pivotAnswer) leftWitness.joint.later leftRootExact
  have rightSelectedAligned := rightAligned leftWitness.joint.prior
    (.machineFresh rightWitness.joint.pivotActor
      rightWitness.joint.pivotInput rightWitness.joint.pivotAnswer)
      rightWitness.joint.later rightRootExact
  have leftInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftWitness.joint.prior
      initial).cursor .adversary leftWitness.joint.pivotInput
      leftWitness.joint.pivotAnswer leftSelectedAligned
  have rightInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftWitness.joint.prior
      initial).cursor rightWitness.joint.pivotActor
      rightWitness.joint.pivotInput rightWitness.joint.pivotAnswer
      rightSelectedAligned
  have selectedInputExact : leftWitness.joint.pivotInput =
      rightWitness.joint.pivotInput :=
    Option.some.inj (leftInputAtCursor.symm.trans rightInputAtCursor)
  obtain ⟨leftC1Before, leftC2Before, leftC1Salt, leftC2Salt,
      leftC1Answer, leftC2Answer, leftTerminal, leftC1Chain, leftC2Chain,
      leftTerminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom leftWitness.joint.input
      finalTrial leftWitness.joint.actualTrial leftWitness.joint.prior
      leftWitness.joint.later .adversary leftWitness.joint.pivotInput
      leftWitness.joint.pivotAnswer leftRootExact leftWitness.joint.trialExact
  obtain ⟨rightC1Before, rightC2Before, rightC1Salt, rightC2Salt,
      rightC1Answer, rightC2Answer, rightTerminal, rightC1Chain, rightC2Chain,
      rightTerminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom
      rightWitness.joint.input finalTrial rightWitness.joint.actualTrial
      leftWitness.joint.prior rightWitness.joint.later
      rightWitness.joint.pivotActor rightWitness.joint.pivotInput
      rightWitness.joint.pivotAnswer rightRootExact
      (by simpa [priorExact] using rightWitness.joint.trialExact)
  have terminalExact : leftTerminal = rightTerminal :=
    literal_prefix_input_eq_fixes_digest leftTerminalPrefix
      rightTerminalPrefix selectedInputExact
  subst rightTerminal
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftRootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have leftC1DataNonempty :
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape leftWitness.joint.input).messages.c1Root
          leftC1Salt).data ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have rightC1DataNonempty :
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape rightWitness.joint.input).messages.c1Root
          rightC1Salt).data ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have c1InputExact := exact_retained_digest_chains_boundary_input_eq
    priorAnswersNodup leftC1Chain rightC1Chain
    (absorb_input_avoids_post_root_state_input c1RootLabel leftC1Before _
      leftC1DataNonempty)
    (absorb_input_avoids_post_root_state_input c1RootLabel rightC1Before _
      rightC1DataNonempty)
  have c2InputExact := exact_retained_digest_chains_boundary_input_eq
    priorAnswersNodup leftC2Chain rightC2Chain
    (c2_absorb_input_avoids_post_c2_state_input leftC2Before leftC2Salt
      (exactOperationalTape leftWitness.joint.input).messages.c2.root)
    (c2_absorb_input_avoids_post_c2_state_input rightC2Before rightC2Salt
      (exactOperationalTape rightWitness.joint.input).messages.c2.root)
  have operationalC1Exact :
      (exactOperationalTape leftWitness.joint.input).messages.c1Root =
        (exactOperationalTape rightWitness.joint.input).messages.c1Root :=
    c1_root_eq_of_absorb_input_eq leftC1Before rightC1Before
      (exactOperationalTape leftWitness.joint.input).messages.c1Root
      (exactOperationalTape rightWitness.joint.input).messages.c1Root
      leftC1Salt rightC1Salt c1InputExact
  have operationalC2Exact :
      (exactOperationalTape leftWitness.joint.input).messages.c2.root =
        (exactOperationalTape rightWitness.joint.input).messages.c2.root :=
    c2_root_eq_of_absorb_input_eq leftC2Before rightC2Before
      (exactOperationalTape leftWitness.joint.input).messages.c2.root
      (exactOperationalTape rightWitness.joint.input).messages.c2.root
      leftC2Salt rightC2Salt c2InputExact
  have leftC1Runtime :
      (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape leftWitness.joint.input).messages.c1Root := by
    change leftWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      leftWitness.joint.input.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← leftWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have rightC1Runtime :
      (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape rightWitness.joint.input).messages.c1Root := by
    change rightWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      rightWitness.joint.input.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← rightWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have leftC2Runtime :
      (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape leftWitness.joint.input).messages.c2.root := by
    change leftWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      leftWitness.joint.input.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← leftWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have rightC2Runtime :
      (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape rightWitness.joint.input).messages.c2.root := by
    change rightWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      rightWitness.joint.input.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← rightWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have runtimeC1Exact := leftC1Runtime.trans
    (operationalC1Exact.trans rightC1Runtime.symm)
  have runtimeC2Exact := leftC2Runtime.trans
    (operationalC2Exact.trans rightC2Runtime.symm)
  unfold exactK12Roots
  rw [runtimeC1Exact, runtimeC2Exact]

/-- Identical selected prefixes force the literal selected SHA input to agree.
This is cursor determinism in the indexed deployed scheduler, not a hash
assumption. -/
theorem exact_preQ16_clean_pair_selected_input_eq
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
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    leftWitness.joint.pivotInput = rightWitness.joint.pivotInput := by
  let controller := exactDagTrialController transitionFuel finalTrial
  let initial := exactDagCandidateInitialState leftWitness.joint.input
  have leftAlignedRaw := exact_root_records_aligned_for_dag_controller
    leftWitness.joint.input finalTrial.val
  have rightAlignedRaw := exact_root_records_aligned_for_dag_controller
    rightWitness.joint.input finalTrial.val
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftWitness.joint.input.package.root) := by
    simpa [controller, initial, exactDagTrialController] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightWitness.joint.input.package.root) := by
    simpa [controller, initial, exactDagTrialController,
      exactDagCandidateInitialState] using rightAlignedRaw
  have leftSelected := leftAligned leftWitness.joint.prior
    (.machineFresh leftWitness.joint.pivotActor leftWitness.joint.pivotInput
      leftWitness.joint.pivotAnswer) leftWitness.joint.later
      leftWitness.joint.rootExact
  have rightSelected := rightAligned rightWitness.joint.prior
    (.machineFresh rightWitness.joint.pivotActor rightWitness.joint.pivotInput
      rightWitness.joint.pivotAnswer) rightWitness.joint.later
      rightWitness.joint.rootExact
  have leftInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftWitness.joint.prior
      initial).cursor leftWitness.joint.pivotActor leftWitness.joint.pivotInput
      leftWitness.joint.pivotAnswer leftSelected
  have rightInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller rightWitness.joint.prior
      initial).cursor rightWitness.joint.pivotActor
      rightWitness.joint.pivotInput rightWitness.joint.pivotAnswer rightSelected
  rw [priorExact] at leftInputAtCursor
  exact Option.some.inj (leftInputAtCursor.symm.trans rightInputAtCursor)

/-- The shared selected prefix contains one identical canonical final256
producer input on both sides. Fixed-width parsing therefore fixes every
serialized final coefficient without SHA injectivity. -/
theorem exact_preQ16_clean_pair_adversary_final_values_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    (exactOperationalTape leftWitness.joint.input).messages.finalValues =
      (exactOperationalTape rightWitness.joint.input).messages.finalValues := by
  classical
  obtain ⟨leftBefore, leftDigest, leftActor, leftLookup, leftMember,
      leftPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial leftWitness.joint
  obtain ⟨rightBefore, rightDigest, rightActor, rightLookup, rightMember,
      rightPrefix⟩ := exact_preQ16_k13_final256_record_mem_prior
        transitionRoom finalTrial rightWitness.joint
  have selectedInputExact := exact_preQ16_clean_pair_selected_input_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness priorExact
  have digestExact : leftDigest = rightDigest :=
    literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
      selectedInputExact
  let leftInput : ShaInput := bytes leftBefore.digest ++
    [domAbsorb, final256Label] ++ encodeBlocks
      (exactOperationalTape leftWitness.joint.input).messages.finalValues
  let rightInput : ShaInput := bytes rightBefore.digest ++
    [domAbsorb, final256Label] ++ encodeBlocks
      (exactOperationalTape rightWitness.joint.input).messages.finalValues
  have rightMemberCommon :
      (.machineFresh rightActor rightInput leftDigest :
        UnifiedExposureRecord) ∈ leftWitness.joint.prior := by
    rw [priorExact]
    simpa [rightInput, digestExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rightMember
  have priorAnswersNodup :
      (leftWitness.joint.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.joint.input
    rw [leftWitness.joint.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have inputExact : leftInput = rightInput := by
    have recordExact :
        (.machineFresh leftActor leftInput leftDigest : UnifiedExposureRecord) =
          .machineFresh rightActor rightInput leftDigest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftInput,
          AspisK1.V7Tag73TranscriptSchedule.Payload.label,
          AspisK1.V7Tag73TranscriptSchedule.Payload.data] using leftMember)
        rightMemberCommon rfl
    injection recordExact
  have leftDrop : List.drop 34 leftInput = encodeBlocks
      (exactOperationalTape leftWitness.joint.input).messages.finalValues := by
    dsimp [leftInput]
    convert (List.drop_append_length
      (l₁ := bytes leftBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape leftWitness.joint.input).messages.finalValues)) using 1 <;>
      simp
  have rightDrop : List.drop 34 rightInput = encodeBlocks
      (exactOperationalTape rightWitness.joint.input).messages.finalValues := by
    dsimp [rightInput]
    convert (List.drop_append_length
      (l₁ := bytes rightBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape rightWitness.joint.input).messages.finalValues)) using 1 <;>
      simp
  apply encode_blocks_injective 16 256
  calc
    encodeBlocks
        (exactOperationalTape leftWitness.joint.input).messages.finalValues =
      List.drop 34 leftInput := leftDrop.symm
    _ = List.drop 34 rightInput := by rw [inputExact]
    _ = encodeBlocks
        (exactOperationalTape rightWitness.joint.input).messages.finalValues :=
      rightDrop

/-- Canonical field decoding transports the byte-exact final256 equality to
the parsed mathematical vector consumed by K1.3. -/
theorem exact_preQ16_clean_pair_adversary_disclosed_final_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (priorExact : leftWitness.joint.prior = rightWitness.joint.prior) :
    (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
      (exactK13ParsedProof rightWitness.joint.input).disclosedFinal := by
  obtain ⟨leftDecoded, leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.joint.input
  obtain ⟨rightDecoded, rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.joint.input
  have operationalFinalExact :=
    exact_preQ16_clean_pair_adversary_final_values_eq transitionRoom foldTrial
      finalTrial hidden left right leftWitness rightWitness priorExact
  have rawFinalExact :
      (fixedTapeRawMessages
        (exactOperationalTape leftWitness.joint.input)).finalValues =
      (fixedTapeRawMessages
        (exactOperationalTape rightWitness.joint.input)).finalValues := by
    simpa [fixedTapeRawMessages, rawOfMessages] using operationalFinalExact
  have decodedExact := decoded_final_message_eq_of_final_values_eq leftDecode
    rightDecode rawFinalExact
  exact leftBinding.disclosedFinalExact.trans
    (decodedExact.trans rightBinding.disclosedFinalExact.symm)

/-- The verifier-first selected final-work branch is fully determined by the
joint non-q16 coordinates.  This is an execution replay fact and uses no hash
injectivity or probability premise. -/
theorem exact_preQ16_clean_pair_verifier_semantic_profile
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
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (actorExact : leftWitness.joint.pivotActor = .verifier)
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
          right).2.1) :
    leftWitness.joint.prior = rightWitness.joint.prior ∧
      exactK12Roots leftWitness.joint.input =
        exactK12Roots rightWitness.joint.input ∧
      (exactK13ParsedProof leftWitness.joint.input).schedule =
        (exactK13ParsedProof rightWitness.joint.input).schedule ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.joint.input).disclosedFinal := by
  have leftRootExact : exactFixedRootRecords
      leftWitness.joint.input.package.root =
        leftWitness.joint.prior ++
          (.machineFresh .verifier leftWitness.joint.pivotInput
            leftWitness.joint.pivotAnswer : UnifiedExposureRecord) ::
              leftWitness.joint.later := by
    simpa [actorExact] using leftWitness.joint.rootExact
  obtain ⟨verifierPrior, _verifierLater, _verifierExact, priorShape⟩ :=
    exact_dag_verifier_root_record_has_completed_prover_prefix
      leftWitness.joint.input leftWitness.joint.prior leftWitness.joint.later
        leftWitness.joint.pivotInput leftWitness.joint.pivotAnswer leftRootExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_fold_armed_coordinates_force_pre_final_tape_prefix
      leftWitness.joint.input foldTrial finalTrial leftWitness.joint.prior
      ((.machineFresh .verifier leftWitness.joint.pivotInput
        leftWitness.joint.pivotAnswer : UnifiedExposureRecord) ::
          leftWitness.joint.later)
      (by simpa only [List.cons_append] using leftRootExact)
      leftWitness.joint.trialExact programmedCover right contextExact foldExact
  rw [fold_alpha_final_work_q16_named_slot_tape_preserves_master_list]
    at rightPrefix
  have selectedPriorsExact : leftWitness.joint.prior =
      rightWitness.joint.prior :=
    exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix finalTrial
      hidden left right leftWitness.joint.input rightWitness.joint.input
      leftWitness.joint.prior leftWitness.joint.later
      rightWitness.joint.prior rightWitness.joint.later .verifier
      rightWitness.joint.pivotActor leftWitness.joint.pivotInput
      rightWitness.joint.pivotInput leftWitness.joint.pivotAnswer
      rightWitness.joint.pivotAnswer leftRootExact rightWitness.joint.rootExact
      leftWitness.joint.trialExact rightWitness.joint.trialExact
      ⟨rightRemaining, rightPrefix⟩
  have priorAnswers :
      leftWitness.joint.prior.map UnifiedExposureRecord.answer =
        leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.freshQueries.map
            Prod.snd ++ verifierPrior.map Prod.snd := by
    rw [priorShape, List.map_append, projected_machine_fresh_record_answers,
      projected_machine_fresh_record_answers]
  rw [priorAnswers] at rightPrefix
  have leftReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine hidden (freshAnswerTapeToList left)
    leftWitness.joint.input.package.root.fixedRoot.base.runtime
    leftWitness.joint.input.package.root.full.projection.rootPrefixes
    (verifierPrior.map Prod.snd ++ rightRemaining)
  have leftReplay' : k12ProverRunFromAnswerPrefix configuration.machine hidden
      (freshAnswerTapeToList right) =
        { halt := .returned
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversaryValue
          oracle :=
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.finalState
          steps :=
            leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversary.steps } := by
    rw [rightPrefix]
    simpa only [List.append_assoc] using leftReplay
  let rightPrefixes :=
    rightWitness.joint.input.package.root.full.projection.rootPrefixes
  have rightReplay := k12_prover_run_from_completed_prefix_append_exact
    configuration.machine hidden (freshAnswerTapeToList right)
    rightWitness.joint.input.package.root.fixedRoot.base.runtime rightPrefixes
    rightPrefixes.adversary.remaining
  have rightAvailable : freshAnswerTapeToList right =
      rightPrefixes.adversary.freshQueries.map Prod.snd ++
        rightPrefixes.adversary.remaining := by
    simpa [rightPrefixes] using rightPrefixes.adversary.availableExact
  rw [← rightAvailable] at rightReplay
  have rawRunExact := leftReplay'.symm.trans rightReplay
  have adversaryExact :
      (exactK12Runtime rightWitness.joint.input).adversaryValue =
        (exactK12Runtime leftWitness.joint.input).adversaryValue := by
    have haltExact := congrArg (fun run => run.halt) rawRunExact
    have valueExact :
        leftWitness.joint.input.package.root.full.projection.rootPrefixes.adversaryValue =
          rightPrefixes.adversaryValue := by
      simpa only [MachineHalt.returned.injEq] using haltExact
    have leftRuntime := congrArg (fun runtime => runtime.adversaryValue)
      leftWitness.joint.input.package.root.full.projection.rootPrefixes.runtimeExact
    have rightRuntime := congrArg (fun runtime => runtime.adversaryValue)
      rightPrefixes.runtimeExact
    simpa [rightPrefixes, exactK12Runtime, operationalRootRuntime] using
      rightRuntime.trans (valueExact.symm.trans leftRuntime.symm)
  have parsedReverse : exactK13ParsedProof rightWitness.joint.input =
      exactK13ParsedProof leftWitness.joint.input := by
    simpa only [exactK13ParsedProof] using congrArg
      (fun value => value.1.publicProof.proof.rawProof) adversaryExact
  have parsedExact := parsedReverse.symm
  have rootsReverse : exactK12Roots rightWitness.joint.input =
      exactK12Roots leftWitness.joint.input := by
    have rootsFromValue := congrArg (fun value =>
      ({ c1 := runtimeDigest208ToMerkleDigest value.rawMessages.c1Root
         c2 := runtimeDigest208ToMerkleDigest value.rawMessages.c2Root } :
        AspisPool.V7MerkleQueryExtractor.Roots)) adversaryExact
    simpa [exactK12Roots] using rootsFromValue
  exact ⟨selectedPriorsExact, rootsReverse.symm,
    congrArg Tag73K12ParsedProof.schedule parsedExact,
    congrArg Tag73K12ParsedProof.gamma parsedExact,
    congrArg Tag73K12ParsedProof.disclosedFinal parsedExact⟩

/-- The only branch not discharged by deterministic prover-prefix replay:
the selected final-work coordinate was exposed by the adversary first. -/
def ExactPreQ16CleanK13PairSemanticInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    leftWitness.joint.pivotActor = .adversary →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    leftWitness.joint.prior = rightWitness.joint.prior ∧
      exactK12Roots leftWitness.joint.input =
        exactK12Roots rightWitness.joint.input ∧
      (exactK13ParsedProof leftWitness.joint.input).schedule =
        (exactK13ParsedProof rightWitness.joint.input).schedule ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.joint.input).disclosedFinal

/-- The genuinely unresolved adversary-first payload after chronology and the
two committed roots have been recovered from the selected record prefix.  It
is deliberately smaller than the full semantic profile, so subsequent source
and replay lemmas cannot accidentally reintroduce the obsolete intrinsic-bad
witness. -/
def ExactPreQ16CleanK13PairRemainingInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    leftWitness.joint.pivotActor = .adversary →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    (exactK13ParsedProof leftWitness.joint.input).schedule =
        (exactK13ParsedProof rightWitness.joint.input).schedule ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.joint.input).disclosedFinal

/-- Source-neutral payload from which the parsed schedule is functional.  The
schedule itself is intentionally absent: canonical source decoding derives it
from the operational alpha-zero value. -/
def ExactPreQ16CleanK13PairOperationalRemainingOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    leftWitness.joint.pivotActor = .adversary →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
        exactOperationalChallenge rightWitness.joint.input (.alpha 0) ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma ∧
      (exactK13ParsedProof leftWitness.joint.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.joint.input).disclosedFinal

/-- Minimal causal transcript endpoint. Final256 is now recovered from the
shared root prefix, and schedule is functional from alpha-zero, leaving only
the two variable-prefix challenge samplers. -/
def ExactPreQ16CleanK13PairAlphaGammaInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    leftWitness.joint.pivotActor = .adversary →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
        exactOperationalChallenge rightWitness.joint.input (.alpha 0) ∧
      (exactK13ParsedProof leftWitness.joint.input).gamma =
        (exactK13ParsedProof rightWitness.joint.input).gamma

/-- The minimal alpha/gamma endpoint plus the proved shared-prefix final256
lemma supplies the complete operational remaining profile. -/
theorem exact_preQ16_clean_pair_operational_remaining_of_alpha_gamma
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (alphaGamma :
      ExactPreQ16CleanK13PairAlphaGammaInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactPreQ16CleanK13PairOperationalRemainingOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness actorExact
    contextExact foldExact workExact
  obtain ⟨alphaExact, gammaExact⟩ := alphaGamma foldTrial finalTrial hidden
    left right leftWitness rightWitness actorExact contextExact foldExact workExact
  have priorExact := exact_preQ16_clean_pair_selected_priors_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness programmedCover
      contextExact foldExact
  have finalExact := exact_preQ16_clean_pair_adversary_disclosed_final_eq source
    transitionRoom foldTrial finalTrial hidden left right leftWitness rightWitness
      priorExact
  exact ⟨alphaExact, gammaExact, finalExact⟩

/-- Canonical source decoding turns operational alpha equality into exact
schedule equality.  Thus the remaining causal work is alpha, gamma, and the
final vector, rather than an independent schedule theorem. -/
theorem exact_preQ16_clean_pair_remaining_of_operational
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (operational :
      ExactPreQ16CleanK13PairOperationalRemainingOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactPreQ16CleanK13PairRemainingInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness actorExact
    contextExact foldExact workExact
  obtain ⟨alphaExact, gammaExact, finalExact⟩ := operational foldTrial
    finalTrial hidden left right leftWitness rightWitness actorExact contextExact
      foldExact workExact
  obtain ⟨leftDecoded, _leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.joint.input
  obtain ⟨rightDecoded, _rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.joint.input
  have scheduleExact := exact_fixed_k13_schedule_eq_of_source_bindings
    leftWitness.joint.input leftDecoded leftBinding rightWitness.joint.input
      rightDecoded rightBinding alphaExact
  exact ⟨scheduleExact, gammaExact, finalExact⟩

/-- Chronology and root-chain recovery close the first two fields of the
adversary profile.  Consequently schedule, gamma, and the disclosed final
vector are exactly the remaining deterministic obligation. -/
theorem exact_preQ16_clean_pair_adversary_semantic_of_remaining
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (remaining :
      ExactPreQ16CleanK13PairRemainingInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder) :
    ExactPreQ16CleanK13PairSemanticInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness actorExact
    contextExact foldExact workExact
  have priorExact := exact_preQ16_clean_pair_selected_priors_eq foldTrial
    finalTrial hidden left right leftWitness rightWitness programmedCover
      contextExact foldExact
  have rootsExact := exact_preQ16_clean_pair_adversary_roots_eq transitionRoom
    foldTrial finalTrial hidden left right leftWitness rightWitness actorExact
      programmedCover contextExact foldExact
  obtain ⟨scheduleExact, gammaExact, finalExact⟩ := remaining foldTrial
    finalTrial hidden left right leftWitness rightWitness actorExact contextExact
      foldExact workExact
  exact ⟨priorExact, rootsExact, scheduleExact, gammaExact, finalExact⟩

/-- Verifier-first is closed above, so the adversary-first endpoint suffices
for the complete corrected semantic invariant. -/
theorem exact_preQ16_clean_pair_semantic_invariant_of_adversary_anchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (adversaryInvariant :
      ExactPreQ16CleanK13PairSemanticInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder) :
    ExactPreQ16CleanK13PairSemanticInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness
    contextExact foldExact workExact
  have pivotMember :
      (.machineFresh leftWitness.joint.pivotActor leftWitness.joint.pivotInput
        leftWitness.joint.pivotAnswer : UnifiedExposureRecord) ∈
        exactFixedRootRecords leftWitness.joint.input.package.root := by
    rw [leftWitness.joint.rootExact]
    simp
  rcases exact_fixed_root_machine_fresh_actor_cases leftWitness.joint.input
      leftWitness.joint.pivotActor leftWitness.joint.pivotInput
      leftWitness.joint.pivotAnswer pivotMember with actorExact | actorExact
  · exact adversaryInvariant foldTrial finalTrial hidden left right leftWitness
      rightWitness actorExact contextExact foldExact workExact
  · exact exact_preQ16_clean_pair_verifier_semantic_profile foldTrial
      finalTrial hidden left right leftWitness rightWitness actorExact
        programmedCover contextExact foldExact

/-- The semantic profile is exactly sufficient to discharge the corrected
coordinate invariant; no q16 answer appears in this proof. -/
theorem exact_preQ16_clean_k13_pair_coordinate_invariant_of_semantic
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (semantic : ExactPreQ16CleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactPreQ16CleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftMember rightMember
  dsimp only
  intro contextExact foldExact workExact
  change Nonempty (ExactPreQ16CleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, left) foldTrial
      finalTrial) at leftMember
  change Nonempty (ExactPreQ16CleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, right) foldTrial
      finalTrial) at rightMember
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  obtain ⟨priorExact, rootsExact, scheduleExact, gammaExact, finalExact⟩ :=
    semantic foldTrial finalTrial hidden left right leftWitness rightWitness
      contextExact foldExact workExact
  have badExact : leftWitness.joint.bad = rightWitness.joint.bad := by
    rw [leftWitness.joint.badExact, rightWitness.joint.badExact]
    exact exact_preQ16_k13_bad_congr_of_semantic_fields decoder
      leftWitness.joint.input rightWitness.joint.input leftWitness.joint.prior
        rightWitness.joint.prior priorExact rootsExact scheduleExact gammaExact
          finalExact
  have leftPointwise : exactPreQ16CleanK13PairPointwiseBad transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial
        (hidden, left) = leftWitness.joint.bad := by
    simpa [exactPreQ16CleanK13PairPointwiseBad, leftMember, leftWitness]
  have rightPointwise : exactPreQ16CleanK13PairPointwiseBad transitionFuel
      configuration projection fixedInstance decoder foldTrial finalTrial
        (hidden, right) = rightWitness.joint.bad := by
    simpa [exactPreQ16CleanK13PairPointwiseBad, rightMember, rightWitness]
  exact leftPointwise.trans (badExact.trans rightPointwise.symm)

#print axioms exact_preQ16_k13_bad_congr_of_semantic_fields
#print axioms exact_preQ16_clean_pair_has_common_final_absorb_tape_prefix
#print axioms exact_preQ16_clean_pair_has_common_final_absorb_trace_prefix
#print axioms ExactPreQ16CleanK13PairSemanticInvariant
#print axioms exact_preQ16_clean_pair_selected_priors_eq
#print axioms exact_preQ16_clean_pair_adversary_roots_eq
#print axioms exact_preQ16_clean_pair_selected_input_eq
#print axioms exact_preQ16_clean_pair_adversary_final_values_eq
#print axioms exact_preQ16_clean_pair_adversary_disclosed_final_eq
#print axioms exact_preQ16_clean_pair_verifier_semantic_profile
#print axioms ExactPreQ16CleanK13PairSemanticInvariantOnAdversaryAnchors
#print axioms
  ExactPreQ16CleanK13PairRemainingInvariantOnAdversaryAnchors
#print axioms
  ExactPreQ16CleanK13PairOperationalRemainingOnAdversaryAnchors
#print axioms
  ExactPreQ16CleanK13PairAlphaGammaInvariantOnAdversaryAnchors
#print axioms
  exact_preQ16_clean_pair_operational_remaining_of_alpha_gamma
#print axioms exact_preQ16_clean_pair_remaining_of_operational
#print axioms exact_preQ16_clean_pair_adversary_semantic_of_remaining
#print axioms
  exact_preQ16_clean_pair_semantic_invariant_of_adversary_anchors
#print axioms exact_preQ16_clean_k13_pair_coordinate_invariant_of_semantic

end

end AspisK1.V7Tag73K13CorrectedPairProfileInvariant
