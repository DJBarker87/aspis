import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ResidualFactorization
import AspisFormal.K1.V7Tag73ExactFixedQ16AnchorPartition
import AspisFormal.K1.V7Tag73ExactDagPreAnchorResidualPrefix
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73SourceAnchoredNativeCursorFactorization
import AspisFormal.K1.V7Tag73ExactRootPriorQueryHistory

/-!
# Clean-event q16 semantic-profile invariant

K1.6 charges the exact compiler target event separately.  Consequently K1.3
only needs q16 noninterference between two accepted members of the fixed legal
same-tape event.  This file states that exact condition, partitions its one
chronological anchor into verifier- and adversary-owned cases, and proves that
it is sufficient for the clean residual factorization.

The verifier-owned case reuses the existing checked DAG-prefix theorem.  The
sole remaining mathematical endpoint is now the adversary-owned case on two
target-clean executions; no target-hit execution is quantified over.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactDagPreAnchorResidualPrefix
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedCleanQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16AnchorPartition
open AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFixedQ16VerifierDerivedProfile
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootPriorQueryHistory
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

private theorem selected_record_eq_of_same_index
    {records priorLeft laterLeft priorRight laterRight : List
      UnifiedExposureRecord}
    {left right : UnifiedExposureRecord} {index : Nat}
    (leftExact : records = priorLeft ++ left :: laterLeft)
    (leftIndex : index = priorLeft.length)
    (rightExact : records = priorRight ++ right :: laterRight)
    (rightIndex : index = priorRight.length) :
    left = right := by
  have leftAt : records[index]? = some left := by
    rw [leftExact, leftIndex]
    simp
  have rightAt : records[index]? = some right := by
    rw [rightExact, rightIndex]
    simp
  rw [leftAt] at rightAt
  exact Option.some.inj rightAt

/-- A root record labelled adversary-owned is positionally inside the literal
adversary source segment.  In particular, no verifier record can be silently
relabelled by the raw-input ambiguity. -/
theorem exact_fixed_k13_adversary_anchor_has_literal_adversary_prefix
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
    (target : ShaInput) (answer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
        later) :
    ∃ queryPrior queryLater,
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        queryPrior ++ (target, answer) :: queryLater ∧
      prior = projectedMachineFreshRecords .adversary queryPrior := by
  let adversaryQueries :=
    input.package.root.full.projection.rootPrefixes.adversary.freshQueries
  let verifierQueries :=
    input.package.root.full.projection.rootPrefixes.verifier.freshQueries
  have joined :
      projectedMachineFreshRecords .adversary adversaryQueries ++
          projectedMachineFreshRecords .verifier verifierQueries =
        prior ++
          (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
            later := by
    simpa [exactFixedRootRecords, fullProjectedRootRecords, adversaryQueries,
      verifierQueries] using rootExact
  have notVerifier :
      (.machineFresh .adversary target answer : UnifiedExposureRecord) ∉
        projectedMachineFreshRecords .verifier verifierQueries := by
    intro member
    obtain ⟨sourceInput, sourceAnswer, recordExact⟩ :=
      only_machine_fresh_actor_projected_records .verifier verifierQueries
        _ member
    cases recordExact
  rcases append_eq_append_prefix_split
      (projectedMachineFreshRecords .adversary adversaryQueries)
      (projectedMachineFreshRecords .verifier verifierQueries) prior
      ((.machineFresh .adversary target answer : UnifiedExposureRecord) :: later)
      joined with split | split
  · obtain ⟨suffix, adversaryExact, tailExact⟩ := split
    cases suffix with
    | nil =>
        exfalso
        apply notVerifier
        rw [List.nil_append] at tailExact
        rw [← tailExact]
        simp
    | cons head tail =>
        simp only [List.cons_append, List.cons.injEq] at tailExact
        rcases tailExact with ⟨headExact, _laterExact⟩
        subst head
        obtain ⟨queryPrior, queryLater, queriesExact, priorExact,
            _tailRecordsExact⟩ :=
          projected_machine_fresh_records_decomposition .adversary
            adversaryQueries prior target answer tail (by
              simpa only [List.cons_append] using adversaryExact)
        exact ⟨queryPrior, queryLater, queriesExact, priorExact⟩
  · obtain ⟨suffix, _priorExact, verifierExact⟩ := split
    exfalso
    apply notVerifier
    rw [verifierExact]
    simp

/-- Equal residual coordinates replay the complete raw answer prefix before a
clean adversary-owned anchor.  The statement is in the original compiler-tape
order, not merely in the router's casted tape type. -/
theorem exact_fixed_clean_k13_adversary_anchor_replays_raw_pre_anchor_tape
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
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ prior later target answer rightRemaining,
      exactFixedRootRecords leftWitness.input.package.root =
          prior ++
            (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
              later ∧
      trial.val = prior.length ∧
      freshAnswerTapeToList right =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  obtain ⟨prior, later, target, answer, rootExact, trialExact⟩ := anchor
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_dag_residual_coordinate_forces_pre_anchor_tape_prefix
      leftWitness.input trial prior
        ((.machineFresh .adversary target answer : UnifiedExposureRecord) ::
          later)
      (by simpa only [List.cons_append] using rootExact) trialExact
      programmedCover right (by
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
  rw [final_work_q16_named_slot_tape_preserves_master_list] at rightPrefix
  exact ⟨prior, later, target, answer, rightRemaining, rootExact, trialExact,
    rightPrefix⟩

/-- Strong operational form of the preceding result.  Equal residuals reach
the exact same adversary request from the same hidden-tape root cursor, with
the right master tape beginning with precisely the answers that led there.
This is the deterministic pause required by the remaining transcript-profile
binding argument. -/
theorem exact_fixed_clean_k13_adversary_anchor_has_shared_native_pause
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
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    ∃ queryPrior queryLater target answer requestState rightRemaining,
      leftWitness.input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
          queryPrior ++ (target, answer) :: queryLater ∧
      freshAnswerTapeToList right =
          queryPrior.map Prod.snd ++ rightRemaining ∧
      IsExactSchedulerNativeMachineFreshRequest .adversary requestState target
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration hidden)
            (queryPrior.map Prod.snd))) := by
  obtain ⟨prior, later, target, answer, rightRemaining, rootExact,
      _trialExact, rightPrefix⟩ :=
    exact_fixed_clean_k13_adversary_anchor_replays_raw_pre_anchor_tape
      trial hidden left right leftWitness anchor programmedCover coordinateExact
  obtain ⟨queryPrior, queryLater, adversaryExact, priorExact⟩ :=
    exact_fixed_k13_adversary_anchor_has_literal_adversary_prefix
      leftWitness.input prior later target answer rootExact
  obtain ⟨requestState, _priorHistory, requestExact⟩ :=
    exact_root_adversary_query_has_global_prior_history transitionRoom
      leftWitness.input queryPrior target answer queryLater adversaryExact
  have rightPrefix' : freshAnswerTapeToList right =
      queryPrior.map Prod.snd ++ rightRemaining := by
    rw [priorExact, projected_machine_fresh_record_answers] at rightPrefix
    exact rightPrefix
  exact ⟨queryPrior, queryLater, target, answer, requestState, rightRemaining,
    adversaryExact, rightPrefix', requestExact⟩

/-- The adversary-owned selected anchor is literally one of the two deployed
final-work inputs and therefore carries the accepted pre-final transcript
digest in its first 32 bytes.  This is derived from the proof-relevant actual
trial, not from a fallible raw-coordinate role classifier. -/
theorem exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (trial : ExactCompilerExposureTrial parameters)
    (witness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder sample trial)
    (anchor : ExactFixedK13AdversaryAnchor witness.input trial) :
    ∃ prior later target answer digest,
      exactFixedRootRecords witness.input.package.root =
          prior ++
            (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
              later ∧
      trial.val = prior.length ∧
      HasLiteralStatePrefix digest target := by
  obtain ⟨anchorPrior, anchorLater, target, answer, anchorExact,
      anchorIndex⟩ := anchor
  obtain ⟨digest, workAnswer, base, _workAccepted, _baseExact, pairLabeled,
      _workLabeled, _workCoordinate, _realized⟩ := witness.actualTrial
  rcases pairLabeled with
      ⟨pairPrior, middle, pairLater, workActor, absorbActor, pairExact,
        pairIndex⟩ |
      ⟨pairPrior, middle, pairLater, workActor, absorbActor, pairExact,
        pairIndex⟩
  · have pairHeadExact :
        exactFixedRootRecords witness.input.package.root =
          pairPrior ++
            (.machineFresh workActor
              (literalFinalWorkKey digest
                (exactOperationalTape witness.input).messages.finalGrinding.selected).workInput
              workAnswer : UnifiedExposureRecord) ::
              (middle ++
                (.machineFresh absorbActor
                  (literalFinalWorkKey digest
                    (exactOperationalTape witness.input).messages.finalGrinding.selected).absorbInput
                  base : UnifiedExposureRecord) :: pairLater) := by
      simpa only [List.cons_append, List.append_assoc] using pairExact
    have selectedExact :
        (.machineFresh .adversary target answer : UnifiedExposureRecord) =
          .machineFresh workActor
            (literalFinalWorkKey digest
              (exactOperationalTape witness.input).messages.finalGrinding.selected).workInput
            workAnswer :=
      selected_record_eq_of_same_index anchorExact anchorIndex pairHeadExact pairIndex
    injection selectedExact with _actorExact targetExact _answerExact
    subst target
    refine ⟨anchorPrior, anchorLater,
      (literalFinalWorkKey digest
        (exactOperationalTape witness.input).messages.finalGrinding.selected).workInput,
      answer, digest, anchorExact, anchorIndex, ?_⟩
    simp [HasLiteralStatePrefix, RawFinalWorkKey.workInput,
      literalFinalWorkKey]
  · have pairHeadExact :
        exactFixedRootRecords witness.input.package.root =
          pairPrior ++
            (.machineFresh absorbActor
              (literalFinalWorkKey digest
                (exactOperationalTape witness.input).messages.finalGrinding.selected).absorbInput
              base : UnifiedExposureRecord) ::
              (middle ++
                (.machineFresh workActor
                  (literalFinalWorkKey digest
                    (exactOperationalTape witness.input).messages.finalGrinding.selected).workInput
                  workAnswer : UnifiedExposureRecord) :: pairLater) := by
      simpa only [List.cons_append, List.append_assoc] using pairExact
    have selectedExact :
        (.machineFresh .adversary target answer : UnifiedExposureRecord) =
          .machineFresh absorbActor
            (literalFinalWorkKey digest
              (exactOperationalTape witness.input).messages.finalGrinding.selected).absorbInput
            base :=
      selected_record_eq_of_same_index anchorExact anchorIndex pairHeadExact pairIndex
    injection selectedExact with _actorExact targetExact _answerExact
    subst target
    refine ⟨anchorPrior, anchorLater,
      (literalFinalWorkKey digest
        (exactOperationalTape witness.input).messages.finalGrinding.selected).absorbInput,
      answer, digest, anchorExact, anchorIndex, ?_⟩
    simp [HasLiteralStatePrefix, RawFinalWorkKey.absorbInput,
      literalFinalWorkKey]

/-- Equality of the four q16 semantic inputs is required only between two
accepted, target-clean members of the same residual fibre. -/
def ExactFixedCleanK13DerivedPreQ16ProfileInvariant
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
      (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, right) trial),
    (hidden, left) ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
        configuration projection fixedInstance →
    (hidden, right) ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
        configuration projection fixedInstance →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

/-- The unresolved clean condition restricted to an adversary-owned first
exposure of the selected final-work pair. -/
def ExactFixedCleanK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
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
      (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, right) trial),
    (hidden, left) ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
        configuration projection fixedInstance →
    (hidden, right) ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel
        configuration projection fixedInstance →
    ExactFixedK13AdversaryAnchor leftWitness.input trial →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

/-- The checked verifier-owned theorem plus the clean adversary-owned theorem
cover every genuine clean K1.3 trial. -/
theorem exact_fixed_clean_k13_derived_profile_invariant_of_anchor_partition
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (adversaryInvariant :
      ExactFixedCleanK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13DerivedPreQ16ProfileInvariant transitionFuel
      configuration projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness leftClean rightClean
    coordinateExact
  rcases exact_fixed_k13_actual_joint_trial_anchor_actor_cases leftWitness.input
      trial leftWitness.actualTrial with verifierAnchor | adversaryAnchor
  · exact exact_fixed_k13_derived_profile_of_left_verifier_anchor source trial
      hidden left right leftWitness rightWitness verifierAnchor programmedCover
      coordinateExact
  · exact adversaryInvariant trial hidden left right leftWitness rightWitness
      leftClean rightClean adversaryAnchor coordinateExact

/-- The clean profile condition is exactly sufficient for the clean residual
bad-set equality used by the q16 probability bound. -/
theorem exact_fixed_clean_k13_residual_invariant_of_derived_profile
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (profileInvariant : ExactFixedCleanK13DerivedPreQ16ProfileInvariant
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact
  let leftWitness := Classical.choice leftMember.1
  let rightWitness := Classical.choice rightMember.1
  have profileExact := profileInvariant trial hidden left right leftWitness
    rightWitness leftMember.2 rightMember.2 residualExact
  obtain ⟨leftDecoded, leftBinding⟩ := source _ leftWitness.input
  obtain ⟨rightDecoded, rightBinding⟩ := source _ rightWitness.input
  have wordsExact := congrArg ExactFixedK13Q16SemanticProfile.words profileExact
  have gammaOperationalExact :=
    congrArg ExactFixedK13Q16SemanticProfile.gamma profileExact
  have finalExact :=
    congrArg ExactFixedK13Q16SemanticProfile.disclosedFinal profileExact
  have alphaOperationalExact :=
    congrArg ExactFixedK13Q16SemanticProfile.alphaZero profileExact
  have gammaExact :
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma := by
    calc
      (exactK13ParsedProof leftWitness.input).gamma =
          exactOperationalChallenge leftWitness.input .gamma :=
        leftBinding.gammaExact
      _ = exactOperationalChallenge rightWitness.input .gamma :=
        gammaOperationalExact
      _ = (exactK13ParsedProof rightWitness.input).gamma :=
        rightBinding.gammaExact.symm
  have scheduleExact :
      (exactK13ParsedProof leftWitness.input).schedule =
        (exactK13ParsedProof rightWitness.input).schedule := by
    exact exact_fixed_k13_schedule_eq_of_source_bindings
      leftWitness.input leftDecoded leftBinding rightWitness.input rightDecoded
        rightBinding alphaOperationalExact
  have intrinsicExact :
      exactFixedK13IntrinsicBad decoder leftWitness.input =
        exactFixedK13IntrinsicBad decoder rightWitness.input :=
    exact_fixed_k13_intrinsic_bad_congr_of_semantic_fields decoder
      leftWitness.input rightWitness.input wordsExact gammaExact finalExact
      scheduleExact
  have leftPointwise :
      exactFixedK13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, left) = leftWitness.bad := by
    simpa [leftWitness] using
      (exact_fixed_k13_pointwise_bad_eq_choice
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, left) leftMember.1)
  have rightPointwise :
      exactFixedK13PointwiseBad transitionFuel configuration projection
          fixedInstance decoder trial (hidden, right) = rightWitness.bad := by
    simpa [rightWitness] using
      (exact_fixed_k13_pointwise_bad_eq_choice
        (configuration := configuration) (projection := projection)
        (fixedInstance := fixedInstance) (decoder := decoder) trial
        (hidden, right) rightMember.1)
  rw [leftPointwise, rightPointwise, leftWitness.badExact,
    rightWitness.badExact]
  exact intrinsicExact

/-- Final clean-event K1.3 handoff: only the literal clean adversary-anchor
causal theorem remains before the already-proved finite q16 bound applies. -/
theorem exact_fixed_clean_k13_residual_invariant_of_adversary_anchor_profile
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (adversaryInvariant :
      ExactFixedCleanK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  apply exact_fixed_clean_k13_residual_invariant_of_derived_profile source
  exact exact_fixed_clean_k13_derived_profile_invariant_of_anchor_partition
    source programmedCover adversaryInvariant

#print axioms ExactFixedCleanK13DerivedPreQ16ProfileInvariant
#print axioms
  exact_fixed_k13_adversary_anchor_has_literal_adversary_prefix
#print axioms
  exact_fixed_k13_adversary_anchor_has_prefinal_digest_prefix
#print axioms
  exact_fixed_clean_k13_adversary_anchor_replays_raw_pre_anchor_tape
#print axioms
  exact_fixed_clean_k13_adversary_anchor_has_shared_native_pause
#print axioms
  ExactFixedCleanK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_k13_derived_profile_invariant_of_anchor_partition
#print axioms exact_fixed_clean_k13_residual_invariant_of_derived_profile
#print axioms
  exact_fixed_clean_k13_residual_invariant_of_adversary_anchor_profile

end

end AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
