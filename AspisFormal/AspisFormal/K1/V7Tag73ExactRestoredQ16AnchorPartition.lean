import AspisFormal.K1.V7Tag73RestoredK12CanonicalWordCongruence

/-!
# Restored K1.3 q16 source invariant by chronological anchor actor

Every genuine restored q16 trial now retains its deployed final-work
chronology.  This file splits the remaining committed pre-q16 source theorem
into the verifier-first and adversary-first cases.  The split is on the
literal first-fresh root record, never on raw SHA input bytes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredQ16AnchorPartition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73RestoredK12CanonicalWordCongruence
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The verifier-first half of the committed restored q16 source theorem. -/
def ExactRestoredRootCommittedPreQ16InvariantOnVerifierAnchors
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
      (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    ExactFixedK13VerifierAnchor leftWitness.input trial →
    (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    ∃ candidate : ExtractedWords,
      exactRestoredRootCompleteWords leftWitness.input = .words candidate ∧
      exactRestoredRootCompleteWords rightWitness.input = .words candidate ∧
      (exactRestoredRootK13View leftWitness.input).gamma =
        (exactRestoredRootK13View rightWitness.input).gamma ∧
      (exactRestoredRootK13View leftWitness.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.input).schedule =
        (exactRestoredRootK13View rightWitness.input).schedule

/-- The adversary-first/cache-hit half.  Keeping it separate prevents a raw
coordinate classifier from being smuggled into the proof. -/
def ExactRestoredRootCommittedPreQ16InvariantOnAdversaryAnchors
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
      (leftWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactRestoredRootK13JointTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    ExactFixedK13AdversaryAnchor leftWitness.input trial →
    (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactRestoredRootK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    ∃ candidate : ExtractedWords,
      exactRestoredRootCompleteWords leftWitness.input = .words candidate ∧
      exactRestoredRootCompleteWords rightWitness.input = .words candidate ∧
      (exactRestoredRootK13View leftWitness.input).gamma =
        (exactRestoredRootK13View rightWitness.input).gamma ∧
      (exactRestoredRootK13View leftWitness.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.input).schedule =
        (exactRestoredRootK13View rightWitness.input).schedule

/-- The exact chronological actor partition closes the unsplit source
invariant once its two honest branches are proved. -/
theorem exact_restored_root_committed_pre_q16_invariant_of_anchor_partition
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (verifier : ExactRestoredRootCommittedPreQ16InvariantOnVerifierAnchors
      transitionFuel configuration projection fixedInstance decoder)
    (adversary : ExactRestoredRootCommittedPreQ16InvariantOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder) :
    ExactRestoredRootCommittedPreQ16Invariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact
  rcases exact_fixed_k13_actual_joint_trial_anchor_actor_cases
      leftWitness.input trial leftWitness.actualTrial with
    verifierAnchor | adversaryAnchor
  · exact verifier trial hidden left right leftWitness rightWitness
      verifierAnchor residualExact
  · exact adversary trial hidden left right leftWitness rightWitness
      adversaryAnchor residualExact

#print axioms
  exact_restored_root_committed_pre_q16_invariant_of_anchor_partition

end

end AspisK1.V7Tag73ExactRestoredQ16AnchorPartition
