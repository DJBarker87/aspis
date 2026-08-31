import AspisFormal.K1.V7Tag73ExactCompilerQ16EventHandoff
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73ExactDagQ16ChainRouting

/-!
# Exact fixed-root K1.3 query event to a joint final-work/q16 trial

The measured K1.6 capstone uses the fixed K1.2--K1.4 stages.  In particular,
its q16 premise concerns `exactTag73K13QueryEvent`, whose K1.2 certificate pins
the extracted words to the canonical completed-prover prefix.  This file keeps
that canonical source value explicit and maps every member of the actual event
to one chronological final-work/q16 exposure trial.

This is a deterministic handoff.  It does not yet assert the remaining
residual-fibre noninterference property or a probability bound.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16JointEventHandoff

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerQ16EventHandoff
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalQ16ForestHandoff
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The exact fixed-root consistency set, with the K1.2 words replaced by
their certificate-pinned canonical value.  Unlike the restoration-wide event,
there is no arbitrary existential word choice in this definition. -/
def exactFixedK13IntrinsicBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Finset (Fin 262144) :=
  consistencySet (exactK13ParsedProof input).schedule
    (exactK13Encoders decoder)
    (extractedIdealTranscript (exactPrefixK12Words input)
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal)

/-- Any proof-relevant K1.2 certificate induces exactly the same fixed-root
q16 consistency set. -/
theorem exact_fixed_k13_intrinsic_bad_eq_certificate
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) :
    exactFixedK13IntrinsicBad decoder input =
      consistencySet (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12) := by
  simp only [exactFixedK13IntrinsicBad, exactK13Transcript, k12.wordsExact]

/-- The exact 513-coordinate factor selected by one chronological exposure
trial on one compiler sample. -/
def exactFixedK13TrialCoordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    ExactCompilerFinalWorkQ16Residual parameters ×
      (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerCausalFinalWorkQ16Coordinates parameters
    (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration sample.1).erase) sample.2

/-- A trial used by the fixed-root q16 event is not an arbitrary index into
the master tape.  It is tied to the literal accepted final-work record and to
the exact first-cap-203 q16 realization of the same source input.  Keeping
this fact proof-relevant prevents a later residual argument from silently
quantifying over synthetic early trial placements. -/
def ExactFixedK13ActualJointTrial
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
    (trial : ExactCompilerExposureTrial parameters) : Prop :=
  ∃ (digest workAnswer base : Digest256),
    FinalWork34Accepted workAnswer ∧
    base = (exactOperationalRawTrace input).q16BaseDigest ∧
    ExactDagFinalWorkPairLabeled input trial
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected)
      workAnswer base ∧
    ExactDagFinalWorkLabeled input trial
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected)
      workAnswer ∧
    (exactFixedK13TrialCoordinates transitionFuel configuration trial sample).2.1 =
      workAnswer ∧
    OperationalQ16ForestRealization
      (exactOperationalTape input).frontierNodes
      (exactOperationalTape input).search
      (exactFixedK13TrialCoordinates transitionFuel configuration trial sample).2.2

/-- The source root itself supplies the only meaningful owner split for a
selected final-work coordinate.  There is deliberately no classifier from the
raw SHA input: the identical bytes may be queried by the adversary before the
verifier.  This theorem instead exposes the actual chronological first-fresh
record, which is either an adversary query or the verifier's query. -/
theorem exact_fixed_k13_actual_joint_trial_root_actor_cases
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
    ∃ (digest workAnswer : Digest256),
      FinalWork34Accepted workAnswer ∧
        ((∃ prior later,
            exactFixedRootRecords input.package.root =
              prior ++ (.machineFresh .adversary
                (literalFinalWorkKey digest
                  (exactOperationalTape input).messages.finalGrinding.selected).workInput
                workAnswer : UnifiedExposureRecord) :: later ∧
            (exactDagTrialController transitionFuel trial).preferredSlot
              (indexedStateAfterRecords transitionFuel
                (exactDagTrialController transitionFuel trial) prior
                (exactDagCandidateInitialState input)) = some none) ∨
          (∃ prior later,
            exactFixedRootRecords input.package.root =
              prior ++ (.machineFresh .verifier
                (literalFinalWorkKey digest
                  (exactOperationalTape input).messages.finalGrinding.selected).workInput
                workAnswer : UnifiedExposureRecord) :: later ∧
            (exactDagTrialController transitionFuel trial).preferredSlot
              (indexedStateAfterRecords transitionFuel
                (exactDagTrialController transitionFuel trial) prior
                (exactDagCandidateInitialState input)) = some none)) := by
  obtain ⟨digest, workAnswer, _base, workAccepted, _baseExact, _pairLabeled,
      workLabeled, _workCoordinate, _realized⟩ := actual
  obtain ⟨prior, later, actor, rootExact, preferred⟩ := workLabeled
  have member : (.machineFresh actor
      (literalFinalWorkKey digest
        (exactOperationalTape input).messages.finalGrinding.selected).workInput
      workAnswer : UnifiedExposureRecord) ∈
      exactFixedRootRecords input.package.root := by
    rw [rootExact]
    simp
  unfold exactFixedRootRecords fullProjectedRootRecords at member
  rw [List.mem_append] at member
  refine ⟨digest, workAnswer, workAccepted, ?_⟩
  rcases member with adversary | verifier
  · obtain ⟨queryInput, answer, recordExact⟩ :=
      only_machine_fresh_actor_projected_records .adversary
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries
        _ adversary
    injection recordExact with actorExact _inputExact _answerExact
    subst actor
    exact Or.inl ⟨prior, later, rootExact, preferred⟩
  · obtain ⟨queryInput, answer, recordExact⟩ :=
      only_machine_fresh_actor_projected_records .verifier
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries
        _ verifier
    injection recordExact with actorExact _inputExact _answerExact
    subst actor
    exact Or.inr ⟨prior, later, rootExact, preferred⟩

/-- Current-source decoding supplies the only semantic bridge needed here:
the parsed proof's selected q16 positions are the positions consumed by the
literal operational search. -/
def ExactFixedK13ParsedSourceProvider
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) : Prop :=
  ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample),
    ∃ decoded : Fin 641 → QM31Exact,
      ExactParsedProofSourceBinding input decoded

/-- Every member of the fixed-root q16 event supplies one canonical bad set
and one chronological joint final-work/q16 trial whose coordinate lands in the
successful bad event for that exact set. -/
theorem exact_fixed_k13_query_failure_has_joint_trial_coordinate
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
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (frontierExact : ∀
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (member : sample ∈ exactTag73K13QueryEvent transitionFuel configuration
      projection fixedInstance decoder) :
    ∃ (input : ExactK12OperationalInput transitionFuel configuration projection
          fixedInstance sample)
        (bad : Finset (Fin 262144))
        (trial : ExactCompilerExposureTrial parameters),
      bad = exactFixedK13IntrinsicBad decoder input ∧
      bad.card ≤ 9557 ∧
      ExactFixedK13ActualJointTrial input trial ∧
      exactFixedK13TrialCoordinates transitionFuel configuration trial sample ∈
        dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
          (fun _residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
            finalWorkQ16SuccessfulBadEvent bad) := by
  obtain ⟨input, k12, failure⟩ := member
  obtain ⟨decoded, sourceBinding⟩ := source sample input
  let bad := exactFixedK13IntrinsicBad decoder input
  have badCertificate : bad =
      consistencySet (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) (exactK13Transcript input k12) := by
    exact exact_fixed_k13_intrinsic_bad_eq_certificate decoder input k12
  have badCard : bad.card ≤ 9557 := by
    rw [badCertificate]
    exact failure.2
  have allBad : AllInBad bad
      (exactOperationalTape input).search.selectedSchedule.positions := by
    rw [badCertificate]
    exact exact_query_phase_failure_selected_all_in_bad sourceBinding failure
  obtain ⟨digest, workAnswer, base, trial, workAccepted, baseExact,
      pairLabeled, workLabeled, workCoordinate, realized⟩ :=
    exact_compiler_accepted_dag_q16_operational_realization transitionRoom
      programmedCover input (frontierExact input)
  have actualTrial : ExactFixedK13ActualJointTrial input trial :=
    ⟨digest, workAnswer, base, workAccepted, baseExact, pairLabeled, workLabeled,
      workCoordinate, realized⟩
  refine ⟨input, bad, trial, rfl, badCard, actualTrial, ?_⟩
  have q16Success :=
    operational_realization_implies_q16_digest_forest_succeeds realized
  have q16Bad : successfulQ16DigestForestEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          sample).2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad := by
    apply operational_all_in_bad_implies_successful_coordinate_bad realized bad
    exact allBad
  refine ⟨q16Success, ?_⟩
  change FinalWork34Accepted
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).2.1 ∧
    successfulQ16DigestForestEquiv
        ⟨(exactFixedK13TrialCoordinates transitionFuel configuration trial
          sample).2.2, q16Success⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad
  exact ⟨workCoordinate ▸ workAccepted, q16Bad⟩

/-! ## Proof-relevant trial event -/

/-- Proof-relevant membership in one genuine fixed-root K1.3 joint trial. -/
structure ExactFixedK13JointTrialWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (sample : ExactCompilerSample HiddenTape parameters)
    (trial : ExactCompilerExposureTrial parameters) : Type where
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance sample
  bad : Finset (Fin 262144)
  badExact : bad = exactFixedK13IntrinsicBad decoder input
  badCard : bad.card ≤ 9557
  actualTrial : ExactFixedK13ActualJointTrial input trial
  coordinate :
    exactFixedK13TrialCoordinates transitionFuel configuration trial sample ∈
      dependentSuccessfulSubtypeEvent finalWorkQ16TotalSucceeds
        (fun _residual => successfulFinalWorkQ16TotalEquiv ⁻¹'
          finalWorkQ16SuccessfulBadEvent bad)

/-- The event for one chronological exposure trial. -/
def exactFixedK13JointTrialEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | Nonempty
    (ExactFixedK13JointTrialWitness transitionFuel configuration projection
      fixedInstance decoder sample trial)}

/-- The pointwise coordinate theorem inhabits one exact trial event. -/
theorem exact_fixed_k13_query_failure_has_joint_trial_witness
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
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (frontierExact : ∀
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (member : sample ∈ exactTag73K13QueryEvent transitionFuel configuration
      projection fixedInstance decoder) :
    ∃ trial : ExactCompilerExposureTrial parameters,
      sample ∈ exactFixedK13JointTrialEvent transitionFuel configuration
        projection fixedInstance decoder trial := by
  obtain ⟨input, bad, trial, badExact, badCard, actualTrial, coordinate⟩ :=
    exact_fixed_k13_query_failure_has_joint_trial_coordinate transitionRoom
      programmedCover source frontierExact member
  refine ⟨trial, ⟨?_⟩⟩
  exact
    { input := input
      bad := bad
      badExact := badExact
      badCard := badCard
      actualTrial := actualTrial
      coordinate := coordinate }

/-! ## Exact residual-fibre obligation -/

/-- Choose the canonical bad set attached to an event member, totalized by
the empty set outside the event. -/
noncomputable def exactFixedK13PointwiseBad
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    Finset (Fin 262144) := by
  classical
  exact if member : Nonempty
        (ExactFixedK13JointTrialWitness transitionFuel configuration projection
          fixedInstance decoder sample trial) then
      (Classical.choice member).bad
    else
      ∅

theorem exact_fixed_k13_pointwise_bad_eq_choice
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (member : Nonempty
      (ExactFixedK13JointTrialWitness transitionFuel configuration projection
        fixedInstance decoder sample trial)) :
    exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial sample =
      (Classical.choice member).bad := by
  classical
  simp [exactFixedK13PointwiseBad, member]

theorem exact_fixed_k13_pointwise_bad_card
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (exactFixedK13PointwiseBad transitionFuel configuration projection
      fixedInstance decoder trial sample).card ≤ 9557 := by
  classical
  by_cases member : Nonempty
      (ExactFixedK13JointTrialWitness transitionFuel configuration projection
        fixedInstance decoder sample trial)
  · simpa [exactFixedK13PointwiseBad, member] using
      (Classical.choice member).badCard
  · simp [exactFixedK13PointwiseBad, member]

/-- The remaining source noninterference statement on the event actually used
by the measured capstone.  It is deliberately much tighter than the rejected
restoration-wide formulation: the bad set is canonical per accepted input. -/
def ExactFixedK13ResidualInvariant
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
        (exactCompilerTargetCaps parameters).length),
    (hidden, left) ∈ exactFixedK13JointTrialEvent transitionFuel configuration
        projection fixedInstance decoder trial →
    (hidden, right) ∈ exactFixedK13JointTrialEvent transitionFuel configuration
        projection fixedInstance decoder trial →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, left) =
      exactFixedK13PointwiseBad transitionFuel configuration projection
        fixedInstance decoder trial (hidden, right)

#print axioms exact_fixed_k13_intrinsic_bad_eq_certificate
#print axioms ExactFixedK13ActualJointTrial
#print axioms exact_fixed_k13_actual_joint_trial_root_actor_cases
#print axioms exact_fixed_k13_query_failure_has_joint_trial_coordinate
#print axioms exact_fixed_k13_query_failure_has_joint_trial_witness
#print axioms exact_fixed_k13_pointwise_bad_card

end

end AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
