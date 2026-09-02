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

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPairRootAbsorbChainClosure
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16QueryHandoff
open AspisK1.V7Tag73K13PreQ16ViewAgreement
open AspisK1.V7Tag73K13PreQ16TrialProbability
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
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

/-- Equal residuals reach the same literal selected pre-answer input. -/
theorem exact_preQ16_k13_selected_input_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
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
    leftWitness.pivotInput = rightWitness.pivotInput := by
  have priorExact : leftWitness.prior = rightWitness.prior :=
    exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial hidden
      left right leftWitness.input rightWitness.input leftWitness.prior
      leftWitness.later rightWitness.prior rightWitness.later
      leftWitness.pivotActor rightWitness.pivotActor leftWitness.pivotInput
      rightWitness.pivotInput leftWitness.pivotAnswer rightWitness.pivotAnswer
      leftWitness.rootExact rightWitness.rootExact leftWitness.trialExact
      rightWitness.trialExact programmedCover residualExact
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
  have leftSelected := leftAligned leftWitness.prior
    (.machineFresh leftWitness.pivotActor leftWitness.pivotInput
      leftWitness.pivotAnswer) leftWitness.later leftWitness.rootExact
  have rightSelected := rightAligned rightWitness.prior
    (.machineFresh rightWitness.pivotActor rightWitness.pivotInput
      rightWitness.pivotAnswer) rightWitness.later rightWitness.rootExact
  have leftInput := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftWitness.prior
      initial).cursor leftWitness.pivotActor leftWitness.pivotInput
      leftWitness.pivotAnswer leftSelected
  have rightInput := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller rightWitness.prior
      initial).cursor rightWitness.pivotActor rightWitness.pivotInput
      rightWitness.pivotAnswer rightSelected
  rw [priorExact] at leftInput
  exact Option.some.inj (leftInput.symm.trans rightInput)

/-- The canonical final256 producer record lies in the literal prefix before
every corrected selected trial. -/
theorem exact_preQ16_k13_final256_record_mem_prior
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (trial : ExactCompilerExposureTrial parameters)
    (witness : ExactPreQ16K13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial) :
    ∃ before : EvalState, ∃ digest : Digest256, ∃ actor : QueryActor,
      let producerInput := bytes before.digest ++
        [domAbsorb,
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape witness.input).messages.finalValues).label] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape witness.input).messages.finalValues).data
      tableLookup (exactOperationalTable witness.input) producerInput =
          some digest ∧
        (.machineFresh actor producerInput digest : UnifiedExposureRecord) ∈
          witness.prior ∧
        HasLiteralStatePrefix digest witness.pivotInput := by
  classical
  obtain ⟨actualPrior, actualLater, selectedActor, selectedInput,
      selectedAnswer, digest, _base, _absorbActor, actualRootExact,
      actualTrialExact, selectedPrefix, prefinalOrigin, _baseExact,
      _absorbMember⟩ :=
    exact_fixed_k13_actual_trial_has_selected_prefinal_prefix witness.input
      trial witness.actualTrial
  obtain ⟨before, producerLookup⟩ := prefinalOrigin
  let producerInput := bytes before.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape witness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape witness.input).messages.finalValues).data
  have selectedMember :
      (.machineFresh selectedActor selectedInput selectedAnswer :
        UnifiedExposureRecord) ∈
        exactFixedRootRecords witness.input.package.root := by
    rw [actualRootExact]
    simp
  have selectedLookup := exact_root_machineFresh_has_operational_lookup
    witness.input selectedActor selectedInput selectedAnswer selectedMember
  obtain ⟨beforePairs, middlePairs, afterPairs, pairOrder⟩ :=
    exact_compiler_literal_dependency_has_strict_root_order transitionRoom
      witness.input producerInput selectedInput digest selectedAnswer
      (by simpa [producerInput] using producerLookup) selectedLookup
      selectedPrefix
  obtain ⟨beforeRecords, middleRecords, afterRecords, producerActor,
      orderedSelectedActor, recordOrder⟩ :=
    exact_root_pair_order_lifts_to_records witness.input producerInput
      selectedInput digest selectedAnswer beforePairs middlePairs afterPairs
      pairOrder
  have producerMemberActual :
      (.machineFresh producerActor producerInput digest :
        UnifiedExposureRecord) ∈ actualPrior := by
    have rootNodup :
        (exactFixedRootRecords witness.input.package.root).Nodup :=
      List.Nodup.of_map UnifiedExposureRecord.answer
        (exact_root_record_answers_nodup witness.input)
    have orderedSelectedMember :
        (.machineFresh orderedSelectedActor selectedInput selectedAnswer :
          UnifiedExposureRecord) ∈
          exactFixedRootRecords witness.input.package.root := by
      rw [recordOrder]
      simp
    have selectedRecordExact :
        (.machineFresh orderedSelectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) =
          .machineFresh selectedActor selectedInput selectedAnswer :=
      List.inj_on_of_nodup_map
        (exact_root_record_answers_nodup witness.input)
        orderedSelectedMember selectedMember rfl
    have recordOrder' : exactFixedRootRecords witness.input.package.root =
        beforeRecords ++
          (.machineFresh producerActor producerInput digest :
            UnifiedExposureRecord) :: middleRecords ++
          (.machineFresh selectedActor selectedInput selectedAnswer :
            UnifiedExposureRecord) :: afterRecords := by
      simpa [selectedRecordExact] using recordOrder
    exact mem_canonical_prefix_of_strictly_before_pivot
      (exactFixedRootRecords witness.input.package.root) actualPrior actualLater
      beforeRecords middleRecords afterRecords
      (.machineFresh producerActor producerInput digest)
      (.machineFresh selectedActor selectedInput selectedAnswer) rootNodup
      actualRootExact recordOrder'
  have prefixExact : witness.prior = actualPrior :=
    equal_prefixes_of_equal_decomposition_lengths
      (exactFixedRootRecords witness.input.package.root) witness.prior
      witness.later actualPrior actualLater
      (.machineFresh witness.pivotActor witness.pivotInput witness.pivotAnswer)
      (.machineFresh selectedActor selectedInput selectedAnswer)
      witness.rootExact actualRootExact (by
        rw [← witness.trialExact, ← actualTrialExact])
  have witnessAt :
      (exactFixedRootRecords witness.input.package.root)[trial.val]? =
        some (.machineFresh witness.pivotActor witness.pivotInput
          witness.pivotAnswer : UnifiedExposureRecord) := by
    rw [witness.rootExact, witness.trialExact]
    simp
  have actualAt :
      (exactFixedRootRecords witness.input.package.root)[trial.val]? =
        some (.machineFresh selectedActor selectedInput selectedAnswer :
          UnifiedExposureRecord) := by
    rw [actualRootExact, actualTrialExact]
    simp
  have selectedRecordExact :
      (.machineFresh witness.pivotActor witness.pivotInput witness.pivotAnswer :
          UnifiedExposureRecord) =
        .machineFresh selectedActor selectedInput selectedAnswer := by
    rw [witnessAt] at actualAt
    exact Option.some.inj actualAt
  have selectedInputExact : witness.pivotInput = selectedInput := by
    injection selectedRecordExact
  refine ⟨before, digest, producerActor, ?_, ?_, ?_⟩
  · simpa [producerInput] using producerLookup
  · rw [prefixExact]
    exact producerMemberActual
  · simpa [selectedInputExact] using selectedPrefix

/-- Equal residuals identify the two retained `final256` creation records,
including their common oracle answer.  This is the terminal record from which
the accepted alpha chain can be replayed backwards without hash injectivity. -/
theorem exact_preQ16_k13_common_final256_record
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
    ∃ (leftBefore rightBefore : EvalState) (digest : Digest256)
        (leftActor rightActor : QueryActor),
      let leftInput := bytes leftBefore.digest ++
        [domAbsorb,
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape leftWitness.input).messages.finalValues).data
      let rightInput := bytes rightBefore.digest ++
        [domAbsorb,
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape rightWitness.input).messages.finalValues).data
      leftInput = rightInput ∧
        tableLookup (exactOperationalTable leftWitness.input) leftInput =
          some digest ∧
        tableLookup (exactOperationalTable rightWitness.input) rightInput =
          some digest ∧
        (.machineFresh leftActor leftInput digest : UnifiedExposureRecord) ∈
          leftWitness.prior ∧
        (.machineFresh rightActor rightInput digest : UnifiedExposureRecord) ∈
          rightWitness.prior ∧
        HasLiteralStatePrefix digest leftWitness.pivotInput ∧
        HasLiteralStatePrefix digest rightWitness.pivotInput := by
  classical
  obtain ⟨leftBefore, leftDigest, leftActor, leftLookup, leftMember,
      leftPrefix⟩ :=
    exact_preQ16_k13_final256_record_mem_prior transitionRoom trial leftWitness
  obtain ⟨rightBefore, rightDigest, rightActor, rightLookup, rightMember,
      rightPrefix⟩ :=
    exact_preQ16_k13_final256_record_mem_prior transitionRoom trial rightWitness
  have selectedInputExact := exact_preQ16_k13_selected_input_eq programmedCover
    trial hidden left right leftWitness rightWitness residualExact
  have digestExact : leftDigest = rightDigest :=
    literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
      selectedInputExact
  have priorExact : leftWitness.prior = rightWitness.prior :=
    exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial hidden
      left right leftWitness.input rightWitness.input leftWitness.prior
      leftWitness.later rightWitness.prior rightWitness.later
      leftWitness.pivotActor rightWitness.pivotActor leftWitness.pivotInput
      rightWitness.pivotInput leftWitness.pivotAnswer rightWitness.pivotAnswer
      leftWitness.rootExact rightWitness.rootExact leftWitness.trialExact
      rightWitness.trialExact programmedCover residualExact
  let leftInput := bytes leftBefore.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape leftWitness.input).messages.finalValues).data
  let rightInput := bytes rightBefore.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape rightWitness.input).messages.finalValues).data
  have rightMemberCommon :
      (.machineFresh rightActor rightInput leftDigest :
        UnifiedExposureRecord) ∈ leftWitness.prior := by
    rw [priorExact]
    simpa [rightInput, digestExact] using rightMember
  have priorAnswersNodup :
      (leftWitness.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.input
    rw [leftWitness.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have inputExact : leftInput = rightInput := by
    have recordExact :
        (.machineFresh leftActor leftInput leftDigest :
            UnifiedExposureRecord) =
          .machineFresh rightActor rightInput leftDigest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftInput] using leftMember) rightMemberCommon rfl
    injection recordExact
  refine ⟨leftBefore, rightBefore, leftDigest, leftActor, rightActor, ?_⟩
  exact ⟨inputExact, by simpa [leftInput] using leftLookup,
    by simpa [rightInput, digestExact] using rightLookup,
    by simpa [leftInput] using leftMember,
    by simpa [rightInput, digestExact] using rightMember,
    leftPrefix, by simpa [digestExact] using rightPrefix⟩

/-- Equal residuals fix the complete canonical final256 producer input and
the serialized vector it carries before q16. -/
theorem exact_preQ16_k13_final256_input_and_values_eq
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
    ∃ leftBefore rightBefore : EvalState,
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
      (exactOperationalTape leftWitness.input).messages.finalValues =
        (exactOperationalTape rightWitness.input).messages.finalValues := by
  classical
  obtain ⟨leftBefore, leftDigest, leftActor, leftLookup, leftMember,
      leftPrefix⟩ :=
    exact_preQ16_k13_final256_record_mem_prior transitionRoom trial leftWitness
  obtain ⟨rightBefore, rightDigest, rightActor, rightLookup, rightMember,
      rightPrefix⟩ :=
    exact_preQ16_k13_final256_record_mem_prior transitionRoom trial rightWitness
  have selectedInputExact := exact_preQ16_k13_selected_input_eq programmedCover
    trial hidden left right leftWitness rightWitness residualExact
  have digestExact : leftDigest = rightDigest :=
    literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
      selectedInputExact
  have priorExact : leftWitness.prior = rightWitness.prior :=
    exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial hidden
      left right leftWitness.input rightWitness.input leftWitness.prior
      leftWitness.later rightWitness.prior rightWitness.later
      leftWitness.pivotActor rightWitness.pivotActor leftWitness.pivotInput
      rightWitness.pivotInput leftWitness.pivotAnswer rightWitness.pivotAnswer
      leftWitness.rootExact rightWitness.rootExact leftWitness.trialExact
      rightWitness.trialExact programmedCover residualExact
  let leftInput := bytes leftBefore.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape leftWitness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape leftWitness.input).messages.finalValues).data
  let rightInput := bytes rightBefore.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape rightWitness.input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape rightWitness.input).messages.finalValues).data
  have rightMemberCommon :
      (.machineFresh rightActor rightInput leftDigest :
        UnifiedExposureRecord) ∈ leftWitness.prior := by
    rw [priorExact]
    simpa [rightInput, digestExact] using rightMember
  have priorAnswersNodup :
      (leftWitness.prior.map UnifiedExposureRecord.answer).Nodup := by
    have fullNodup := exact_root_record_answers_nodup leftWitness.input
    rw [leftWitness.rootExact, List.map_append, List.map_cons] at fullNodup
    exact (List.nodup_append.mp fullNodup).1
  have inputExact : leftInput = rightInput := by
    have recordExact :
        (.machineFresh leftActor leftInput leftDigest :
            UnifiedExposureRecord) =
          .machineFresh rightActor rightInput leftDigest :=
      List.inj_on_of_nodup_map priorAnswersNodup
        (by simpa [leftInput] using leftMember) rightMemberCommon rfl
    injection recordExact
  have leftDrop : List.drop 34 leftInput =
      encodeBlocks
        (exactOperationalTape leftWitness.input).messages.finalValues := by
    simp only [leftInput, AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
    convert (List.drop_append_length
      (l₁ := bytes leftBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape leftWitness.input).messages.finalValues)) using 1 <;>
      simp
  have rightDrop : List.drop 34 rightInput =
      encodeBlocks
        (exactOperationalTape rightWitness.input).messages.finalValues := by
    simp only [rightInput, AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
    convert (List.drop_append_length
      (l₁ := bytes rightBefore.digest ++ [domAbsorb, final256Label])
      (l₂ := encodeBlocks
        (exactOperationalTape rightWitness.input).messages.finalValues)) using 1 <;>
      simp
  refine ⟨leftBefore, rightBefore, inputExact, ?_⟩
  apply encode_blocks_injective 16 256
  calc
    encodeBlocks
        (exactOperationalTape leftWitness.input).messages.finalValues =
      List.drop 34 leftInput := leftDrop.symm
    _ = List.drop 34 rightInput := by rw [inputExact]
    _ = encodeBlocks
        (exactOperationalTape rightWitness.input).messages.finalValues :=
      rightDrop

/-- Projection of the stronger producer-input theorem. -/
theorem exact_preQ16_k13_final_values_eq
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
    (exactOperationalTape leftWitness.input).messages.finalValues =
      (exactOperationalTape rightWitness.input).messages.finalValues := by
  obtain ⟨_leftBefore, _rightBefore, _inputExact, valuesExact⟩ :=
    exact_preQ16_k13_final256_input_and_values_eq transitionRoom
      programmedCover trial hidden left right leftWitness rightWitness
      residualExact
  exact valuesExact

/-- Equality of the canonical producer input also fixes the transcript digest
immediately after the gamma/alpha chain and before final256. -/
theorem exact_preQ16_k13_before_final256_digest_eq
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
    ∃ leftBefore rightBefore : EvalState,
      leftBefore.digest = rightBefore.digest := by
  obtain ⟨leftBefore, rightBefore, inputExact, _valuesExact⟩ :=
    exact_preQ16_k13_final256_input_and_values_eq transitionRoom
      programmedCover trial hidden left right leftWitness rightWitness
      residualExact
  refine ⟨leftBefore, rightBefore, ?_⟩
  have bytesExact : bytes leftBefore.digest = bytes rightBefore.digest := by
    calc
      bytes leftBefore.digest = List.take 32
          (bytes leftBefore.digest ++ [domAbsorb, final256Label] ++
            encodeBlocks
              (exactOperationalTape leftWitness.input).messages.finalValues) := by
            simp
      _ = List.take 32
          (bytes rightBefore.digest ++ [domAbsorb, final256Label] ++
            encodeBlocks
              (exactOperationalTape rightWitness.input).messages.finalValues) := by
            exact congrArg (List.take 32) inputExact
      _ = bytes rightBefore.digest := by simp
  exact List.ofFn_injective bytesExact

/-- Canonical production decoding transports the serialized equality to the
mathematical disclosed terminal vector. -/
theorem exact_preQ16_k13_disclosed_final_eq
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
    (exactK13ParsedProof leftWitness.input).disclosedFinal =
      (exactK13ParsedProof rightWitness.input).disclosedFinal := by
  obtain ⟨leftDecoded, leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.input
  obtain ⟨rightDecoded, rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.input
  have operationalFinalExact := exact_preQ16_k13_final_values_eq
    transitionRoom programmedCover trial hidden left right leftWitness
    rightWitness residualExact
  have rawFinalExact :
      (fixedTapeRawMessages
        (exactOperationalTape leftWitness.input)).finalValues =
      (fixedTapeRawMessages
        (exactOperationalTape rightWitness.input)).finalValues := by
    simpa [fixedTapeRawMessages, rawOfMessages] using operationalFinalExact
  have decodedExact := decoded_final_message_eq_of_final_values_eq leftDecode
    rightDecode rawFinalExact
  exact leftBinding.disclosedFinalExact.trans
    (decodedExact.trans rightBinding.disclosedFinalExact.symm)

/-- Production/source endpoint for the three parsed semantic fields used by
the corrected consistency set.  This is deliberately separated from the
mathematical word proof above and is the exact Rust/Aeneas obligation: a
shared completed pre-q16 source prefix must decode to the same schedule,
gamma and disclosed terminal vector. -/
def ExactPreQ16K13ParsedProfileSourceInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16K13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactPreQ16K13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    leftWitness.prior = rightWitness.prior →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    (exactK13ParsedProof leftWitness.input).schedule =
        (exactK13ParsedProof rightWitness.input).schedule ∧
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma ∧
      (exactK13ParsedProof leftWitness.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.input).disclosedFinal

/-- The only nontrivial source branch: the selected final-work/q16 coordinate
was first exposed by the adversary before the verifier reached its cache hit. -/
def ExactPreQ16K13ParsedProfileSourceInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactPreQ16K13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactPreQ16K13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    leftWitness.pivotActor = .adversary →
    leftWitness.prior = rightWitness.prior →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    (exactK13ParsedProof leftWitness.input).schedule =
        (exactK13ParsedProof rightWitness.input).schedule ∧
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma ∧
      (exactK13ParsedProof leftWitness.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.input).disclosedFinal

/-- Verifier-owned first exposures are already closed by the exact scheduler
prefix theorem.  Consequently only the explicitly named adversary-first
source endpoint is required. -/
theorem exact_preQ16_k13_parsed_profile_source_of_adversary_branch
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (adversaryInvariant :
      ExactPreQ16K13ParsedProfileSourceInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactPreQ16K13ParsedProfileSourceInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness priorExact residualExact
  have pivotMember :
      (.machineFresh leftWitness.pivotActor leftWitness.pivotInput
        leftWitness.pivotAnswer : UnifiedExposureRecord) ∈
        exactFixedRootRecords leftWitness.input.package.root := by
    rw [leftWitness.rootExact]
    simp
  rcases exact_fixed_root_machine_fresh_actor_cases leftWitness.input
      leftWitness.pivotActor leftWitness.pivotInput leftWitness.pivotAnswer
      pivotMember with actorExact | actorExact
  ·
      exact adversaryInvariant trial hidden left right leftWitness rightWitness
        actorExact priorExact residualExact
  ·
      have anchor : ExactFixedK13VerifierAnchor leftWitness.input trial := by
        exact ⟨leftWitness.prior, leftWitness.later, leftWitness.pivotInput,
          leftWitness.pivotAnswer, by simpa [actorExact] using
            leftWitness.rootExact, leftWitness.trialExact⟩
      obtain ⟨parsedExact, _wordsExact⟩ :=
        exact_fixed_k13_pre_q16_values_of_verifier_anchor leftWitness.input
          trial anchor programmedCover right rightWitness.input (by
            change
              ((exactCompilerExposureTrialDagRouter parameters transitionFuel
                trial (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
                (finalWorkQ16NamedSlotInputTape
                  (exactCompilerFinalWorkQ16InputTape parameters left))).2 =
              ((exactCompilerExposureTrialDagRouter parameters transitionFuel
                trial (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
                (finalWorkQ16NamedSlotInputTape
                  (exactCompilerFinalWorkQ16InputTape parameters right))).2
              at residualExact
            exact residualExact)
      have parsedForward : exactK13ParsedProof leftWitness.input =
          exactK13ParsedProof rightWitness.input := parsedExact.symm
      exact ⟨congrArg Tag73K12ParsedProof.schedule parsedForward,
        congrArg Tag73K12ParsedProof.gamma parsedForward,
        congrArg Tag73K12ParsedProof.disclosedFinal parsedForward⟩

/-- The root/word theorem plus the exact parsed-source endpoint discharge the
only premise of the corrected finite-measure wrapper. -/
theorem exact_preQ16_k13_residual_work_invariant_of_source
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
    (sourceInvariant : ExactPreQ16K13ParsedProfileSourceInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactPreQ16K13ResidualWorkInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact _workExact
  have leftMember' : Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial) :=
    leftMember
  have rightMember' : Nonempty (ExactPreQ16K13JointTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial) :=
    rightMember
  let leftWitness := Classical.choice leftMember'
  let rightWitness := Classical.choice rightMember'
  have priorExact : leftWitness.prior = rightWitness.prior :=
    exact_fixed_clean_k13_equal_residual_selected_root_priors_eq trial hidden
      left right leftWitness.input rightWitness.input leftWitness.prior
      leftWitness.later rightWitness.prior rightWitness.later
      leftWitness.pivotActor rightWitness.pivotActor leftWitness.pivotInput
      rightWitness.pivotInput leftWitness.pivotAnswer rightWitness.pivotAnswer
      leftWitness.rootExact rightWitness.rootExact leftWitness.trialExact
      rightWitness.trialExact programmedCover residualExact
  obtain ⟨scheduleExact, gammaExact, finalExact⟩ :=
    sourceInvariant trial hidden left right leftWitness rightWitness priorExact
      residualExact
  have wordsExact := exact_preQ16_k13_words_eq transitionRoom programmedCover
    trial hidden left right leftWitness rightWitness residualExact
  have leftPointwise :
      exactPreQ16K13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, left) = leftWitness.bad := by
    rw [exactPreQ16K13PointwiseBad, dif_pos leftMember']
  have rightPointwise :
      exactPreQ16K13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, right) = rightWitness.bad := by
    rw [exactPreQ16K13PointwiseBad, dif_pos rightMember']
  rw [leftPointwise, rightPointwise, leftWitness.badExact,
    rightWitness.badExact]
  unfold exactPreQ16K13Bad
  rw [scheduleExact, wordsExact]
  unfold parsedK13Transcript
  rw [gammaExact, finalExact]

/-- Corrected one-forest probability theorem with only the exact production
parsed-profile source obligation exposed. -/
theorem exact_preQ16_k13_trial_union_probability_le_one_forest_of_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (sourceInvariant : ExactPreQ16K13ParsedProfileSourceInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (exposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial : ExactCompilerExposureTrial parameters,
          exactPreQ16K13JointTrialEvent transitionFuel configuration projection
            fixedInstance decoder trial) ≤ q16SemanticOneForestRawError := by
  apply exact_preQ16_k13_trial_union_probability_le_one_forest hiddenLaw
    (exact_preQ16_k13_residual_work_invariant_of_source transitionRoom
      programmedCover sourceInvariant) reference traceExists exposureCap

#print axioms exact_preQ16_k13_roots_eq
#print axioms exact_preQ16_k13_words_eq
#print axioms exact_preQ16_k13_common_final256_record
#print axioms exact_preQ16_k13_final256_input_and_values_eq
#print axioms exact_preQ16_k13_before_final256_digest_eq
#print axioms ExactPreQ16K13ParsedProfileSourceInvariant
#print axioms exact_preQ16_k13_residual_work_invariant_of_source
#print axioms
  exact_preQ16_k13_trial_union_probability_le_one_forest_of_source

end

end AspisK1.V7Tag73K13PreQ16RootInvariant
