import AspisFormal.K1.V7Tag73K13PreQ16TrialProbability
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
import AspisFormal.K1.V7Tag73ExactPairRootAbsorbChainClosure
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity

/-!
# Root invariance for the corrected pre-q16 K1.3 event

Equal causal residuals fix the complete chronological prefix before the
selected final-work/q16 coordinate.  The two retained root-to-final chains
inside that common prefix then identify the literal C1/C2 absorb inputs.
Fixed-layout parsing recovers the committed roots; no hash injectivity is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73K13PreQ16RootInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPairRootAbsorbChainClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TrialProbability
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equal residuals in the corrected event fix both roots absorbed before the
selected q16 forest. -/
theorem exact_preQ16_k13_roots_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (residualExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    exactK12Roots leftWitness.input = exactK12Roots rightWitness.input := by
  have priorExact : leftWitness.prior = rightWitness.prior :=
    exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial hidden
      left right leftWitness.input rightWitness.input leftWitness.prior
      leftWitness.later rightWitness.prior rightWitness.later
      leftWitness.pivotActor rightWitness.pivotActor leftWitness.pivotInput
      rightWitness.pivotInput leftWitness.pivotAnswer rightWitness.pivotAnswer
      leftWitness.rootExact rightWitness.rootExact leftWitness.trialExact
      rightWitness.trialExact programmedCover residualExact
  let commonPrior := leftWitness.prior
  have leftRootExact :
      exactFixedRootRecords leftWitness.input.package.root =
        commonPrior ++
          (.machineFresh leftWitness.pivotActor leftWitness.pivotInput
            leftWitness.pivotAnswer : UnifiedExposureRecord) ::
          leftWitness.later := by
    simpa [commonPrior] using leftWitness.rootExact
  have rightRootExact :
      exactFixedRootRecords rightWitness.input.package.root =
        commonPrior ++
          (.machineFresh rightWitness.pivotActor rightWitness.pivotInput
            rightWitness.pivotAnswer : UnifiedExposureRecord) ::
          rightWitness.later := by
    simpa [commonPrior, priorExact] using rightWitness.rootExact
  have leftTrialExact : trial.val = commonPrior.length := by
    simpa [commonPrior] using leftWitness.trialExact
  have rightTrialExact : trial.val = commonPrior.length := by
    simpa [commonPrior, priorExact] using rightWitness.trialExact
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
  have leftSelectedAligned := leftAligned commonPrior
    (.machineFresh leftWitness.pivotActor leftWitness.pivotInput
      leftWitness.pivotAnswer) leftWitness.later leftRootExact
  have rightSelectedAligned := rightAligned commonPrior
    (.machineFresh rightWitness.pivotActor rightWitness.pivotInput
      rightWitness.pivotAnswer) rightWitness.later rightRootExact
  have leftInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller commonPrior
      initial).cursor
    leftWitness.pivotActor leftWitness.pivotInput leftWitness.pivotAnswer
    leftSelectedAligned
  have rightInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller commonPrior
      initial).cursor
    rightWitness.pivotActor rightWitness.pivotInput rightWitness.pivotAnswer
    rightSelectedAligned
  have selectedInputExact : leftWitness.pivotInput = rightWitness.pivotInput :=
    Option.some.inj (leftInputAtCursor.symm.trans rightInputAtCursor)
  obtain ⟨leftC1Before, leftC2Before, leftC1Salt, leftC2Salt,
      leftC1Answer, leftC2Answer, leftTerminal, leftC1Chain, leftC2Chain,
      leftTerminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom leftWitness.input
      trial leftWitness.actualTrial commonPrior leftWitness.later
      leftWitness.pivotActor leftWitness.pivotInput leftWitness.pivotAnswer
      leftRootExact leftTrialExact
  obtain ⟨rightC1Before, rightC2Before, rightC1Salt, rightC2Salt,
      rightC1Answer, rightC2Answer, rightTerminal, rightC1Chain, rightC2Chain,
      rightTerminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom rightWitness.input
      trial rightWitness.actualTrial commonPrior rightWitness.later
      rightWitness.pivotActor rightWitness.pivotInput rightWitness.pivotAnswer
      rightRootExact rightTrialExact
  have terminalExact : leftTerminal = rightTerminal :=
    literal_prefix_input_eq_fixes_digest leftTerminalPrefix
      rightTerminalPrefix selectedInputExact
  subst rightTerminal
  have priorAnswersNodup :
      (commonPrior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.input
    rw [leftRootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have leftC1DataNonempty :
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape leftWitness.input).messages.c1Root
          leftC1Salt).data ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp [AspisK1.V7Tag73TranscriptSchedule.Payload.data] at lengths
  have rightC1DataNonempty :
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape rightWitness.input).messages.c1Root
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
      (exactOperationalTape leftWitness.input).messages.c2.root)
    (c2_absorb_input_avoids_post_c2_state_input rightC2Before rightC2Salt
      (exactOperationalTape rightWitness.input).messages.c2.root)
  have c1Exact := c1_root_eq_of_absorb_input_eq leftC1Before rightC1Before
    (exactOperationalTape leftWitness.input).messages.c1Root
    (exactOperationalTape rightWitness.input).messages.c1Root leftC1Salt
    rightC1Salt c1InputExact
  have c2Exact := c2_root_eq_of_absorb_input_eq leftC2Before rightC2Before
    (exactOperationalTape leftWitness.input).messages.c2.root
    (exactOperationalTape rightWitness.input).messages.c2.root leftC2Salt
    rightC2Salt c2InputExact
  change Roots.mk
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime leftWitness.input).adversaryValue.rawMessages.c1Root)
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime leftWitness.input).adversaryValue.rawMessages.c2Root) =
    Roots.mk
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime rightWitness.input).adversaryValue.rawMessages.c1Root)
      (runtimeDigest208ToMerkleDigest
        (exactK12Runtime rightWitness.input).adversaryValue.rawMessages.c2Root)
  have leftRaw := leftWitness.input.package.root.fixedRoot.base.rawMessagesExact
  have rightRaw := rightWitness.input.package.root.fixedRoot.base.rawMessagesExact
  have leftC1 :
      (exactK12Runtime leftWitness.input).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape leftWitness.input).messages.c1Root := by
    change leftWitness.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      leftWitness.input.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← leftRaw]
    rfl
  have rightC1 :
      (exactK12Runtime rightWitness.input).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape rightWitness.input).messages.c1Root := by
    change rightWitness.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      rightWitness.input.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← rightRaw]
    rfl
  have leftC2 :
      (exactK12Runtime leftWitness.input).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape leftWitness.input).messages.c2.root := by
    change leftWitness.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      leftWitness.input.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← leftRaw]
    rfl
  have rightC2 :
      (exactK12Runtime rightWitness.input).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape rightWitness.input).messages.c2.root := by
    change rightWitness.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      rightWitness.input.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← rightRaw]
    rfl
  rw [leftC1, rightC1, leftC2, rightC2, c1Exact, c2Exact]

/-- The corrected received word is therefore identical throughout one causal
residual fibre. -/
theorem exact_preQ16_k13_words_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (residualExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    preQ16PrefixWords leftWitness.prior (exactK12Roots leftWitness.input) =
      preQ16PrefixWords rightWitness.prior
        (exactK12Roots rightWitness.input) := by
  apply preQ16PrefixWords_congr
  · exact exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial
      hidden left right leftWitness.input rightWitness.input leftWitness.prior
      leftWitness.later rightWitness.prior rightWitness.later
      leftWitness.pivotActor rightWitness.pivotActor leftWitness.pivotInput
      rightWitness.pivotInput leftWitness.pivotAnswer rightWitness.pivotAnswer
      leftWitness.rootExact rightWitness.rootExact leftWitness.trialExact
      rightWitness.trialExact programmedCover residualExact
  · exact exact_preQ16_k13_roots_eq transitionRoom programmedCover trial
      hidden left right leftWitness rightWitness residualExact

#print axioms exact_preQ16_k13_roots_eq
#print axioms exact_preQ16_k13_words_eq

end

end AspisK1.V7Tag73K13PreQ16RootInvariant
