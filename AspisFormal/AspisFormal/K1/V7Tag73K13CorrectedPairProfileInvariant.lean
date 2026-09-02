import AspisFormal.K1.V7Tag73K13CorrectedPairTrialProbability
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier
import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant
import AspisFormal.K1.V7Tag73ExactPairRootAbsorbChainClosure
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity
import AspisFormal.K1.V7Tag73ExactFixedQ16ScheduleFunctional

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
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73FoldAlphaPreFinalPrefix
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

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
#print axioms ExactPreQ16CleanK13PairSemanticInvariant
#print axioms exact_preQ16_clean_pair_selected_priors_eq
#print axioms exact_preQ16_clean_pair_adversary_roots_eq
#print axioms exact_preQ16_clean_pair_verifier_semantic_profile
#print axioms ExactPreQ16CleanK13PairSemanticInvariantOnAdversaryAnchors
#print axioms
  ExactPreQ16CleanK13PairRemainingInvariantOnAdversaryAnchors
#print axioms
  ExactPreQ16CleanK13PairOperationalRemainingOnAdversaryAnchors
#print axioms exact_preQ16_clean_pair_remaining_of_operational
#print axioms exact_preQ16_clean_pair_adversary_semantic_of_remaining
#print axioms
  exact_preQ16_clean_pair_semantic_invariant_of_adversary_anchors
#print axioms exact_preQ16_clean_k13_pair_coordinate_invariant_of_semantic

end

end AspisK1.V7Tag73K13CorrectedPairProfileInvariant
