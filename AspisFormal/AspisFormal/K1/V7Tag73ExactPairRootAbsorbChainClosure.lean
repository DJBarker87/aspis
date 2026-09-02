import AspisFormal.K1.V7Tag73ExactLinearTranscriptRootOrder
import AspisFormal.K1.V7Tag73ExactPairPreQ16WordInvariant

/-!
# Cross-fibre C1/C2 absorb-chain closure

This module closes the remaining source-side root invariant for fixed K1.3.
The first step below identifies the pre-final digest carried by any
proof-relevant actual pair with the digest of the verifier's literal accepted
final-nonce input.  Equality follows from their common q16-base answer and
first-creation answer uniqueness, not from SHA-256 injectivity.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactPairRootAbsorbChainClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73ExactLinearTranscriptRootOrder
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairPreQ16WordInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The nonce half of an actual K1.3 final-work pair must use the verifier's
canonical pre-final digest because both nonce inputs produce the same q16
base in one duplicate-free first-creation root. -/
theorem exact_actual_pair_digest_eq_canonical_prefinal
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
    (digest workAnswer base prefinalDigest q16Base : Digest256)
    (pairLabeled : ExactDagFinalWorkPairLabeled input trial
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected)
      workAnswer base)
    (baseExact : base = (exactOperationalRawTrace input).q16BaseDigest)
    (nonceLookup : tableLookup (exactOperationalTable input)
      (bytes prefinalDigest ++ [domAbsorb, finalWorkNonceLabel] ++
        bytes (exactOperationalTape input).messages.finalGrinding.selected) =
      some q16Base)
    (q16BaseExact : q16Base =
      (exactOperationalRawTrace input).q16BaseDigest) :
    digest = prefinalDigest := by
  let actualNonceInput :=
    (literalFinalWorkKey digest
      (exactOperationalTape input).messages.finalGrinding.selected).absorbInput
  have actualNonceMember : ∃ actor,
      (.machineFresh actor actualNonceInput base : UnifiedExposureRecord) ∈
        exactFixedRootRecords input.package.root := by
    rcases pairLabeled with
      ⟨prior, middle, later, workActor, absorbActor, rootExact, _trialExact⟩ |
      ⟨prior, middle, later, workActor, absorbActor, rootExact, _trialExact⟩
    · exact ⟨absorbActor, by rw [rootExact]; simp [actualNonceInput]⟩
    · exact ⟨absorbActor, by rw [rootExact]; simp [actualNonceInput]⟩
  obtain ⟨actualActor, actualMember⟩ := actualNonceMember
  let canonicalNonceInput := bytes prefinalDigest ++
    [domAbsorb, finalWorkNonceLabel] ++
    bytes (exactOperationalTape input).messages.finalGrinding.selected
  obtain ⟨canonicalActor, canonicalMember⟩ :=
    exact_final_table_lookup_has_root_record input canonicalNonceInput q16Base
      (by simpa [canonicalNonceInput] using nonceLookup)
  have baseEq : base = q16Base := baseExact.trans q16BaseExact.symm
  have actualMember' :
      (.machineFresh actualActor actualNonceInput q16Base :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    simpa [baseEq] using actualMember
  have recordExact :
      (.machineFresh actualActor actualNonceInput q16Base :
        UnifiedExposureRecord) =
      .machineFresh canonicalActor canonicalNonceInput q16Base := by
    apply List.inj_on_of_nodup_map (exact_root_record_answers_nodup input)
      actualMember' canonicalMember
    rfl
  have inputExact : actualNonceInput = canonicalNonceInput := by
    injection recordExact
  apply digest_bytes_injective
  have prefixExact := congrArg (List.take 32) inputExact
  simpa [actualNonceInput, canonicalNonceInput, literalFinalWorkKey,
    RawFinalWorkKey.absorbInput] using prefixExact

private theorem selected_record_eq_of_same_index
    {records leftPrior leftLater rightPrior rightLater : List
      UnifiedExposureRecord}
    {left right : UnifiedExposureRecord} {index : Nat}
    (leftExact : records = leftPrior ++ left :: leftLater)
    (leftIndex : index = leftPrior.length)
    (rightExact : records = rightPrior ++ right :: rightLater)
    (rightIndex : index = rightPrior.length) :
    left = right := by
  have leftAt : records[index]? = some left := by
    rw [leftExact, leftIndex]
    simp
  have rightAt : records[index]? = some right := by
    rw [rightExact, rightIndex]
    simp
  rw [leftAt] at rightAt
  exact Option.some.inj rightAt

/-- Retain both complete root-to-final256 chains inside the canonical prefix
selected by one proof-relevant actual K1.3 trial. -/
theorem exact_actual_trial_retains_root_chains
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial)
    (prior later : List UnifiedExposureRecord)
    (pivotActor : QueryActor) (pivotInput : ShaInput)
    (pivotAnswer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later)
    (trialExact : trial.val = prior.length) :
    ∃ (c1Before c2Before c1Salt c2Salt c1Answer c2Answer terminal : Digest256),
      let c1Input := bytes c1Before ++ [domAbsorb, c1RootLabel] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
          (exactOperationalTape input).messages.c1Root c1Salt).data
      let c2Input := bytes c2Before ++ [domAbsorb, c2RootLabel] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
          (exactOperationalTape input).messages.c2.root c2Salt).data
      ExactRetainedDigestChain prior c1Input IsPostC1StateInput c1Answer
          terminal ∧
        ExactRetainedDigestChain prior c2Input IsPostC2StateInput c2Answer
          terminal ∧
        HasLiteralStatePrefix terminal pivotInput := by
  obtain ⟨c1Before, c2Before, c1Salt, c2Salt, c1Answer, c2Answer,
      beforeFinal256, prefinalDigest, canonicalWorkAnswer, q16Base,
      c1Lookup, c2Lookup, final256Lookup, workLookup, workAccepted, nonceLookup,
      q16BaseExact, _c1BeforeFinal, _c2BeforeFinal, _c1BeforeWork,
      _c2BeforeWork, _c1BeforeNonce, _c2BeforeNonce, finalBeforeWork,
      finalBeforeNonce, c2Chain, c1Chain⟩ :=
    exact_operational_root_absorbs_before_final256 transitionRoom input
  obtain ⟨digest, actualWorkAnswer, base, _actualWorkAccepted,
      _prefinalOrigin, baseExact, pairLabeled, _workLabeled,
      _workCoordinate, _realized⟩ := actual
  have digestExact : digest = prefinalDigest :=
    exact_actual_pair_digest_eq_canonical_prefinal input trial digest
      actualWorkAnswer base prefinalDigest q16Base pairLabeled baseExact
      nonceLookup q16BaseExact
  subst digest
  let final256Input := bytes beforeFinal256.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape input).messages.finalValues).data
  let workInput := bytes prefinalDigest ++ [domGrind] ++
    bytes (exactOperationalTape input).messages.finalGrinding.selected
  let nonceInput := bytes prefinalDigest ++ [domAbsorb, finalWorkNonceLabel] ++
    bytes (exactOperationalTape input).messages.finalGrinding.selected
  have pivotRole :
      pivotInput = workInput ∨ pivotInput = nonceInput := by
    rcases pairLabeled with
      ⟨pairPrior, middle, pairLater, workActor, absorbActor, pairRoot,
        pairTrial⟩ |
      ⟨pairPrior, middle, pairLater, workActor, absorbActor, pairRoot,
        pairTrial⟩
    · have pairHead : exactFixedRootRecords input.package.root =
          pairPrior ++
            (.machineFresh workActor workInput actualWorkAnswer :
              UnifiedExposureRecord) ::
            (middle ++
              (.machineFresh absorbActor nonceInput base :
                UnifiedExposureRecord) :: pairLater) := by
        simpa [workInput, nonceInput, literalFinalWorkKey,
          RawFinalWorkKey.workInput, RawFinalWorkKey.absorbInput,
          List.append_assoc] using pairRoot
      have selected := selected_record_eq_of_same_index rootExact trialExact
        pairHead pairTrial
      injection selected with _ inputExact _
      exact Or.inl inputExact
    · have pairHead : exactFixedRootRecords input.package.root =
          pairPrior ++
            (.machineFresh absorbActor nonceInput base :
              UnifiedExposureRecord) ::
            (middle ++
              (.machineFresh workActor workInput actualWorkAnswer :
                UnifiedExposureRecord) :: pairLater) := by
        simpa [workInput, nonceInput, literalFinalWorkKey,
          RawFinalWorkKey.workInput, RawFinalWorkKey.absorbInput,
          List.append_assoc] using pairRoot
      have selected := selected_record_eq_of_same_index rootExact trialExact
        pairHead pairTrial
      injection selected with _ inputExact _
      exact Or.inr inputExact
  refine ⟨c1Before, c2Before, c1Salt, c2Salt, c1Answer, c2Answer,
    prefinalDigest, ?_⟩
  change ExactRetainedDigestChain prior
      (bytes c1Before ++ [domAbsorb, c1RootLabel] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
          (exactOperationalTape input).messages.c1Root c1Salt).data)
      IsPostC1StateInput c1Answer prefinalDigest ∧
    ExactRetainedDigestChain prior
      (bytes c2Before ++ [domAbsorb, c2RootLabel] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
          (exactOperationalTape input).messages.c2.root c2Salt).data)
      IsPostC2StateInput c2Answer prefinalDigest ∧
    HasLiteralStatePrefix prefinalDigest pivotInput
  have retainForOrder (expectedAnswer : Digest256)
      (pairOrder : ExactRootPairBefore input
        (final256Input, prefinalDigest) (pivotInput, expectedAnswer)) :
      ExactRetainedDigestChain prior
          (bytes c1Before ++ [domAbsorb, c1RootLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
              (exactOperationalTape input).messages.c1Root c1Salt).data)
          IsPostC1StateInput c1Answer prefinalDigest ∧
        ExactRetainedDigestChain prior
          (bytes c2Before ++ [domAbsorb, c2RootLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
              (exactOperationalTape input).messages.c2.root c2Salt).data)
          IsPostC2StateInput c2Answer prefinalDigest := by
    classical
    obtain ⟨before, middle, after, pairOrderRaw⟩ := pairOrder
    obtain ⟨beforeRecords, middleRecords, afterRecords, finalActor,
        orderedPivotActor, recordOrder⟩ :=
      exact_root_pair_order_lifts_to_records input final256Input pivotInput
        prefinalDigest expectedAnswer before middle after pairOrderRaw
    have orderedPivotMember :
        (.machineFresh orderedPivotActor pivotInput expectedAnswer :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [recordOrder]
      simp
    have pivotMember :
        (.machineFresh pivotActor pivotInput pivotAnswer :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [rootExact]
      simp
    have pivotRecordExact :
        (.machineFresh orderedPivotActor pivotInput expectedAnswer :
          UnifiedExposureRecord) =
        .machineFresh pivotActor pivotInput pivotAnswer := by
      apply List.inj_on_of_nodup_map
        (exact_root_record_causal_inputs_nodup input)
        orderedPivotMember pivotMember
      simp [causalInput?]
    have recordOrder' : exactFixedRootRecords input.package.root =
        beforeRecords ++
          (.machineFresh finalActor final256Input prefinalDigest :
            UnifiedExposureRecord) ::
          middleRecords ++
          (.machineFresh pivotActor pivotInput pivotAnswer :
            UnifiedExposureRecord) :: afterRecords := by
      simpa [pivotRecordExact] using recordOrder
    have rootNodup : (exactFixedRootRecords input.package.root).Nodup :=
      List.Nodup.of_map UnifiedExposureRecord.answer
        (exact_root_record_answers_nodup input)
    have finalMember := mem_canonical_prefix_of_strictly_before_pivot
      (exactFixedRootRecords input.package.root) prior later beforeRecords
      middleRecords afterRecords
      (.machineFresh finalActor final256Input prefinalDigest)
      (.machineFresh pivotActor pivotInput pivotAnswer) rootNodup rootExact
      recordOrder'
    have finalPrefix : HasLiteralStatePrefix beforeFinal256.digest
        final256Input := by
      simp [HasLiteralStatePrefix, final256Input]
    have retainedC1 := exact_lookup_digest_chain_retained_before_consumer
      transitionRoom input prior later
      (.machineFresh pivotActor pivotInput pivotAnswer) rootExact c1Chain
      final256Input prefinalDigest finalActor
      (by simpa [final256Input] using final256Lookup) finalMember finalPrefix
    have retainedC2 := exact_lookup_digest_chain_retained_before_consumer
      transitionRoom input prior later
      (.machineFresh pivotActor pivotInput pivotAnswer) rootExact c2Chain
      final256Input prefinalDigest finalActor
      (by simpa [final256Input] using final256Lookup) finalMember finalPrefix
    have finalAllowedC1 : IsPostC1StateInput final256Input := by
      exact Or.inr ⟨beforeFinal256.digest,
        AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape input).messages.finalValues,
        by simp [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
          final256Label, c1RootLabel],
        by simp [final256Input]⟩
    have finalAllowedC2 : IsPostC2StateInput final256Input := by
      exact Or.inr ⟨beforeFinal256.digest,
        AspisK1.V7Tag73TranscriptSchedule.Payload.final256
          (exactOperationalTape input).messages.finalValues,
        by simp [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
          final256Label, c2RootLabel],
        by simp [final256Input]⟩
    exact ⟨ExactRetainedDigestChain.step _ _ _ final256Input finalActor
        retainedC1 finalPrefix finalAllowedC1 finalMember,
      ExactRetainedDigestChain.step _ _ _ final256Input finalActor
        retainedC2 finalPrefix finalAllowedC2 finalMember⟩
  rcases pivotRole with workExact | nonceExact
  · subst pivotInput
    refine ⟨(retainForOrder canonicalWorkAnswer (by
      simpa [final256Input, workInput] using finalBeforeWork)).1,
      (retainForOrder canonicalWorkAnswer (by
        simpa [final256Input, workInput] using finalBeforeWork)).2, ?_⟩
    simp [HasLiteralStatePrefix, workInput]
  · subst pivotInput
    refine ⟨(retainForOrder q16Base (by
      simpa [final256Input, nonceInput] using finalBeforeNonce)).1,
      (retainForOrder q16Base (by
        simpa [final256Input, nonceInput] using finalBeforeNonce)).2, ?_⟩
    simp [HasLiteralStatePrefix, nonceInput]

/-- Equal controller state after the common adversary-anchor prefix fixes the
selected input in both executions.  The retained chains therefore share their
pre-final terminal and reverse to identical literal C1/C2 absorb inputs. -/
theorem exact_fixed_clean_pair_k13_root_absorb_inputs_invariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap) :
    ExactFixedCleanK13PairRootAbsorbInputsInvariantOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  obtain ⟨leftPrior, leftLater, rightPrior, rightLater, leftInput, rightInput,
      leftAnswer, rightAnswer, rightActor, leftRootExact, rightRootExact,
      leftTrialExact, rightTrialExact, priorExact⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_root_priors_eq foldTrial
      finalTrial hidden left right leftWitness rightWitness anchor
        programmedCover contextExact foldExact
  have commonPrior := priorExact
  subst rightPrior
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
  have leftSelectedAligned := leftAligned leftPrior
    (.machineFresh .adversary leftInput leftAnswer) leftLater leftRootExact
  have rightSelectedAligned := rightAligned leftPrior
    (.machineFresh rightActor rightInput rightAnswer) rightLater rightRootExact
  have leftInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    .adversary leftInput leftAnswer leftSelectedAligned
  have rightInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    rightActor rightInput rightAnswer rightSelectedAligned
  have selectedInputExact : leftInput = rightInput :=
    Option.some.inj (leftInputAtCursor.symm.trans rightInputAtCursor)
  obtain ⟨leftC1Before, leftC2Before, leftC1Salt, leftC2Salt,
      leftC1Answer, leftC2Answer, leftTerminal, leftC1Chain, leftC2Chain,
      leftTerminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom leftWitness.joint.input
      finalTrial leftWitness.joint.actualTrial leftPrior leftLater .adversary
      leftInput leftAnswer leftRootExact leftTrialExact
  obtain ⟨rightC1Before, rightC2Before, rightC1Salt, rightC2Salt,
      rightC1Answer, rightC2Answer, rightTerminal, rightC1Chain,
      rightC2Chain, rightTerminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom
      rightWitness.joint.input finalTrial rightWitness.joint.actualTrial
      leftPrior rightLater rightActor rightInput rightAnswer rightRootExact
      rightTrialExact
  have terminalExact : leftTerminal = rightTerminal :=
    literal_prefix_input_eq_fixes_digest leftTerminalPrefix
      rightTerminalPrefix selectedInputExact
  subst rightTerminal
  have priorAnswersNodup :
      (leftPrior.map UnifiedExposureRecord.answer).Nodup := by
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
  have leftC1RootExact :
      (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape leftWitness.joint.input).messages.c1Root := by
    change leftWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      leftWitness.joint.input.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← leftWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have rightC1RootExact :
      (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages.c1Root =
        (exactOperationalTape rightWitness.joint.input).messages.c1Root := by
    change rightWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c1Root =
      rightWitness.joint.input.package.root.fixedRoot.base.tape.messages.c1Root
    rw [← rightWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have leftC2RootExact :
      (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape leftWitness.joint.input).messages.c2.root := by
    change leftWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      leftWitness.joint.input.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← leftWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  have rightC2RootExact :
      (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages.c2Root =
        (exactOperationalTape rightWitness.joint.input).messages.c2.root := by
    change rightWitness.joint.input.package.root.fixedRoot.base.runtime.adversaryValue.rawMessages.c2Root =
      rightWitness.joint.input.package.root.fixedRoot.base.tape.messages.c2.root
    rw [← rightWitness.joint.input.package.root.fixedRoot.base.rawMessagesExact]
    rfl
  exact ⟨⟨leftC1Before, rightC1Before, leftC1Salt, rightC1Salt,
      by simpa [leftC1RootExact, rightC1RootExact] using c1InputExact⟩,
    ⟨leftC2Before, rightC2Before, leftC2Salt, rightC2Salt,
      by simpa [leftC2RootExact, rightC2RootExact] using c2InputExact⟩⟩

/-- The closed absorb-input invariant feeds the fixed-layout root parser and
the common-prefix word construction, yielding the complete committed K1.2
word at the selected pre-q16 boundary. -/
theorem exact_fixed_clean_pair_k13_pre_q16_words_invariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap) :
    ExactFixedCleanK13PairPreQ16WordsInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  apply exact_fixed_clean_pair_k13_pre_q16_words_invariant_of_roots
    programmedCover
  apply exact_fixed_clean_pair_k13_roots_invariant_of_absorb_inputs
  exact exact_fixed_clean_pair_k13_root_absorb_inputs_invariant transitionRoom
    programmedCover

#print axioms exact_actual_pair_digest_eq_canonical_prefinal
#print axioms exact_actual_trial_retains_root_chains
#print axioms exact_fixed_clean_pair_k13_root_absorb_inputs_invariant
#print axioms exact_fixed_clean_pair_k13_pre_q16_words_invariant

end

end AspisK1.V7Tag73ExactPairRootAbsorbChainClosure
