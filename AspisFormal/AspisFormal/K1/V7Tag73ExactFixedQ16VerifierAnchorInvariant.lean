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
open AspisK1.V7Tag73ExactDagVerifierAnchorPrefix
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16SourceNoninterference
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
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
#print axioms exact_fixed_k13_pre_q16_values_of_verifier_anchor
#print axioms exact_fixed_k13_joint_trial_pre_q16_values_of_left_verifier_anchor

end

end AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
