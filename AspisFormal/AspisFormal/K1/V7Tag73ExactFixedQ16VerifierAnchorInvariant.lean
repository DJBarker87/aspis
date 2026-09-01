import AspisFormal.K1.V7Tag73ExactFixedQ16SourceNoninterference
import AspisFormal.K1.V7Tag73ExactDagVerifierAnchorPrefix

/-!
# Verifier-owned partition of the fixed K1.3 q16 source invariant

The fixed K1.3 residual invariant has two chronological cases for its selected
final-work/q16 anchor.  This module closes exactly the verifier-owned case.
It is deliberately parameterized by the literal root record at the trial
index: this is a chronological fact, not a classifier on SHA-input bytes.

The adversary-first/cache-hit partition remains separate.  It must use the
same-tape cache-aware replay model and cannot be discharged by treating the
root record as verifier fresh.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16SourceNoninterference
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The selected chronological trial anchor was first created by the
verifier.  The target remains explicit because raw input bytes do not encode
their first-query actor. -/
def ExactFixedK13VerifierAnchor
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
    (trial : ExactCompilerExposureTrial parameters) : Prop :=
  ∃ prior later target answer,
    exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .verifier target answer : UnifiedExposureRecord) ::
        later ∧
    trial.val = prior.length

/-- The complementary chronological case: an arbitrary adversary created the
selected anchor before the verifier reached it.  This case is retained as a
first-class predicate so a later replay proof cannot silently relabel it. -/
def ExactFixedK13AdversaryAnchor
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
    (trial : ExactCompilerExposureTrial parameters) : Prop :=
  ∃ prior later target answer,
    exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh .adversary target answer : UnifiedExposureRecord) ::
        later ∧
    trial.val = prior.length

/-- Root records cannot first originate from an internal replay actor.  This
is a property of the exact accepted-root projection, rather than a property
of the raw input bytes. -/
theorem exact_fixed_root_machine_fresh_actor_cases
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
    (actor : QueryActor) (target : ShaInput) (answer : Digest256)
    (member : (.machineFresh actor target answer : UnifiedExposureRecord) ∈
      exactFixedRootRecords input.package.root) :
    actor = .adversary ∨ actor = .verifier := by
  unfold exactFixedRootRecords fullProjectedRootRecords at member
  rw [List.mem_append] at member
  rcases member with adversary | verifier
  · obtain ⟨sourceInput, sourceAnswer, recordExact⟩ :=
      only_machine_fresh_actor_projected_records .adversary
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries
        _ adversary
    injection recordExact with actorExact _targetExact _answerExact
    exact Or.inl actorExact
  · obtain ⟨sourceInput, sourceAnswer, recordExact⟩ :=
      only_machine_fresh_actor_projected_records .verifier
        input.package.root.full.projection.rootPrefixes.verifier.freshQueries
        _ verifier
    injection recordExact with actorExact _targetExact _answerExact
    exact Or.inr actorExact

/-- The actual paired final-work witness partitions at its earlier root
record.  There is no third case: the selected anchor was first created by
either the adversary or the verifier. -/
theorem exact_fixed_k13_actual_joint_trial_anchor_actor_cases
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
    ExactFixedK13VerifierAnchor input trial ∨
      ExactFixedK13AdversaryAnchor input trial := by
  obtain ⟨digest, workAnswer, base, _workAccepted, _prefinalOrigin,
      _baseExact, pairLabeled, _workLabeled, _workCoordinate, _realized⟩ :=
    actual
  let key := literalFinalWorkKey digest
    (exactOperationalTape input).messages.finalGrinding.selected
  change ExactDagFinalWorkPairLabeled input trial key workAnswer base at pairLabeled
  rcases pairLabeled with
      ⟨prior, middle, later, workActor, absorbActor, recordsExact, trialExact⟩ |
      ⟨prior, middle, later, workActor, absorbActor, recordsExact, trialExact⟩
  · have workMember : (.machineFresh workActor key.workInput workAnswer :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [recordsExact]
      simp
    rcases exact_fixed_root_machine_fresh_actor_cases input workActor
        key.workInput workAnswer workMember with workActorExact | workActorExact
    · subst workActor
      exact Or.inr ⟨prior,
          middle ++ (.machineFresh absorbActor key.absorbInput base :
            UnifiedExposureRecord) :: later,
          key.workInput, workAnswer, by
            simpa only [List.cons_append, List.append_assoc] using recordsExact,
          trialExact⟩
    · subst workActor
      exact Or.inl ⟨prior,
          middle ++ (.machineFresh absorbActor key.absorbInput base :
            UnifiedExposureRecord) :: later,
          key.workInput, workAnswer, by
            simpa only [List.cons_append, List.append_assoc] using recordsExact,
          trialExact⟩
  · have absorbMember : (.machineFresh absorbActor key.absorbInput base :
        UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
      rw [recordsExact]
      simp
    rcases exact_fixed_root_machine_fresh_actor_cases input absorbActor
        key.absorbInput base absorbMember with absorbActorExact | absorbActorExact
    · subst absorbActor
      exact Or.inr ⟨prior,
          middle ++ (.machineFresh workActor key.workInput workAnswer :
            UnifiedExposureRecord) :: later,
          key.absorbInput, base, by
            simpa only [List.cons_append, List.append_assoc] using recordsExact,
          trialExact⟩
    · subst absorbActor
      exact Or.inl ⟨prior,
          middle ++ (.machineFresh workActor key.workInput workAnswer :
            UnifiedExposureRecord) :: later,
          key.absorbInput, base, by
            simpa only [List.cons_append, List.append_assoc] using recordsExact,
          trialExact⟩

/-- Equal residual coordinates preserve the K1.3 pre-q16 values throughout
the verifier-owned part of a chronological trial fibre. -/
theorem exact_fixed_k13_pre_q16_values_of_verifier_anchor
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
    (anchor : ExactFixedK13VerifierAnchor input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance (sample.1, right))
    (coordinateExact :
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters sample.2))).2 =
      ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
        (exactPlainRomCursor configuration sample.1).erase).coordinateEquiv
        (finalWorkQ16NamedSlotInputTape
          (exactCompilerFinalWorkQ16InputTape parameters right))).2) :
    exactK13ParsedProof rightInput = exactK13ParsedProof input ∧
      exactPrefixK12Words rightInput = exactPrefixK12Words input := by
  obtain ⟨prior, later, target, answer, rootExact, trialExact⟩ := anchor
  exact exact_dag_residual_coordinate_preserves_pre_k13_values_at_verifier_anchor
    input trial prior later target answer rootExact trialExact programmedCover
      right rightInput coordinateExact

/-- The preceding theorem in the proof-relevant fixed K1.3 event form.
Only the left execution needs to be verifier anchored: equal residual
coordinates construct the comparison against the exact right event input. -/
theorem exact_fixed_k13_joint_trial_pre_q16_values_of_left_verifier_anchor
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
    (anchor : ExactFixedK13VerifierAnchor leftWitness.input trial)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (coordinateExact :
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1) :
    exactK13ParsedProof rightWitness.input =
        exactK13ParsedProof leftWitness.input ∧
      exactPrefixK12Words rightWitness.input =
        exactPrefixK12Words leftWitness.input := by
  apply exact_fixed_k13_pre_q16_values_of_verifier_anchor
    leftWitness.input trial anchor programmedCover right rightWitness.input
  change
    ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters left))).2 =
    ((exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase).coordinateEquiv
      (finalWorkQ16NamedSlotInputTape
        (exactCompilerFinalWorkQ16InputTape parameters right))).2 at coordinateExact
  exact coordinateExact

#print axioms ExactFixedK13VerifierAnchor
#print axioms ExactFixedK13AdversaryAnchor
#print axioms exact_fixed_root_machine_fresh_actor_cases
#print axioms exact_fixed_k13_actual_joint_trial_anchor_actor_cases
#print axioms exact_fixed_k13_pre_q16_values_of_verifier_anchor
#print axioms exact_fixed_k13_joint_trial_pre_q16_values_of_left_verifier_anchor

end

end AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
