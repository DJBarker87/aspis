import AspisFormal.K1.V7Tag73ExactFixedCleanQ16ProfileInvariant
import AspisFormal.K1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization

/-!
# Clean q16 profile invariant after the final-work answer is exposed

The q16 forest is sampled only after the selected 34-bit final-work answer.
Consequently K1.3 needs the semantic profile to be constant only when both the
causal residual and that already-exposed answer agree.  This file connects that
minimal profile statement to the final-work-dependent probability theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16ProfileInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedCleanQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16AnchorPartition
open AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFixedQ16VerifierDerivedProfile
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact semantic profile need agree only after the residual and the
already-exposed final-work answer have both been fixed. -/
def ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariant
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
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).2.1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).2.1 →
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

/-- The sole protocol-specific endpoint after the verifier-owned partition is
discharged: clean adversary-owned first exposures, compared at equal residual
and equal final-work answer. -/
def ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariantOnAdversaryAnchors
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
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).2.1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).2.1 →
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

/-- The existing verifier-owned theorem and the narrowed adversary-owned
theorem cover every clean chronological K1.3 trial. -/
theorem exact_fixed_clean_k13_derived_profile_work_invariant_of_anchor_partition
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
      ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariant transitionFuel
      configuration projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness leftClean rightClean
    residualExact workExact
  rcases exact_fixed_k13_actual_joint_trial_anchor_actor_cases leftWitness.input
      trial leftWitness.actualTrial with verifierAnchor | adversaryAnchor
  · exact exact_fixed_k13_derived_profile_of_left_verifier_anchor source trial
      hidden left right leftWitness rightWitness verifierAnchor programmedCover
      residualExact
  · exact adversaryInvariant trial hidden left right leftWitness rightWitness
      leftClean rightClean adversaryAnchor residualExact workExact

/-- Equality of the minimal semantic profile gives exactly the bad-set
equality consumed by the work-dependent q16 factorization. -/
theorem exact_fixed_clean_k13_residual_work_invariant_of_derived_profile
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
    (profileInvariant : ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariant
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13ResidualWorkInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftMember rightMember residualExact workExact
  let leftWitness := Classical.choice leftMember.1
  let rightWitness := Classical.choice rightMember.1
  have profileExact := profileInvariant trial hidden left right leftWitness
    rightWitness leftMember.2 rightMember.2 residualExact workExact
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

/-- Final K1.3 handoff with the exact remaining adversary-anchor endpoint. -/
theorem exact_fixed_clean_k13_residual_work_invariant_of_adversary_anchor_profile
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
      ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13ResidualWorkInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  apply exact_fixed_clean_k13_residual_work_invariant_of_derived_profile source
  exact
    exact_fixed_clean_k13_derived_profile_work_invariant_of_anchor_partition
      source programmedCover adversaryInvariant

#print axioms ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariant
#print axioms
  ExactFixedCleanK13DerivedPreQ16ProfileWorkInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_k13_derived_profile_work_invariant_of_anchor_partition
#print axioms
  exact_fixed_clean_k13_residual_work_invariant_of_derived_profile
#print axioms
  exact_fixed_clean_k13_residual_work_invariant_of_adversary_anchor_profile

end

end AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16ProfileInvariant
