import AspisFormal.K1.V7Tag73ExactFixedQ16VerifierDerivedProfile

/-!
# Chronological anchor partition for the fixed Tag-73 K1.3 q16 profile

Every genuine fixed K1.3 trial has one literal first-fresh final-work anchor.
That root record is either verifier-owned or adversary-owned.  The former
case is already derived from the exact DAG prefix theorem; this leaf packages
the complement as the sole remaining source/causality condition.

In particular, this file does **not** call an adversary-first cache hit fresh,
and it does not turn the unresolved condition into an unlabelled global
premise.  It proves that an adversary-anchor profile theorem, plus the checked
verifier-anchor theorem, is exactly sufficient for the existing K1.3 residual
accounting.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16AnchorPartition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactFixedQ16VerifierDerivedProfile
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact remaining K1.3 q16 source condition.  It is restricted to a
literal adversary-owned first exposure in the accepted root trace.  Cache hits
remain cache hits; this condition must be discharged by the state-restoring
q16 response/coupling argument. -/
def ExactFixedK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
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
    ExactFixedK13AdversaryAnchor leftWitness.input trial →
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactFixedK13Q16SemanticProfileOf leftWitness.input =
      exactFixedK13Q16SemanticProfileOf rightWitness.input

/-- Any global profile invariant restricts to the adversary-owned partition.
Together with the next theorem, this makes the remaining condition an exact
logical boundary rather than merely a sufficient approximation. -/
theorem exact_fixed_k13_adversary_profile_invariant_of_derived_profile
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (profileInvariant : ExactFixedK13DerivedPreQ16ProfileInvariant
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness _adversaryAnchor
    coordinateExact
  exact profileInvariant trial hidden left right leftWitness rightWitness
    coordinateExact

set_option maxHeartbeats 800000 in
/-- The literal anchor split turns the two chronological profile conditions
into the unqualified profile invariant consumed by K1.3 accounting. -/
theorem exact_fixed_k13_derived_profile_invariant_of_anchor_partition
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (verifierInvariant :
      ExactFixedK13DerivedPreQ16ProfileInvariantOnVerifierAnchors
        transitionFuel configuration projection fixedInstance decoder)
    (adversaryInvariant :
      ExactFixedK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedK13DerivedPreQ16ProfileInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness coordinateExact
  rcases exact_fixed_k13_actual_joint_trial_anchor_actor_cases leftWitness.input
      trial leftWitness.actualTrial with verifierAnchor | adversaryAnchor
  · exact verifierInvariant trial hidden left right leftWitness rightWitness
      verifierAnchor coordinateExact
  · exact adversaryInvariant trial hidden left right leftWitness rightWitness
      adversaryAnchor coordinateExact

/-- Once the checked verifier-owned condition is supplied, the global K1.3
profile invariant is equivalent to the adversary-first/cache-hit condition.
No event is discarded in either direction. -/
theorem exact_fixed_k13_derived_profile_invariant_iff_adversary_anchor
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (verifierInvariant :
      ExactFixedK13DerivedPreQ16ProfileInvariantOnVerifierAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedK13DerivedPreQ16ProfileInvariant transitionFuel configuration
      projection fixedInstance decoder ↔
      ExactFixedK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder := by
  constructor
  · exact exact_fixed_k13_adversary_profile_invariant_of_derived_profile
  · exact exact_fixed_k13_derived_profile_invariant_of_anchor_partition
      verifierInvariant

/-- With the existing verifier-anchor theorem instantiated, only the
adversary-first/cache-hit profile condition remains before the normal K1.3
residual invariant follows. -/
theorem exact_fixed_k13_residual_invariant_of_adversary_anchor_profile
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
    (scheduleFunctional : ExactFixedK13SourceScheduleFunctional transitionFuel
      configuration projection fixedInstance)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (adversaryInvariant :
      ExactFixedK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  apply exact_fixed_k13_residual_invariant_of_derived_profile source
    scheduleFunctional
  apply exact_fixed_k13_derived_profile_invariant_of_anchor_partition
  · exact exact_fixed_k13_derived_profile_invariant_on_verifier_anchors source
      programmedCover
  · exact adversaryInvariant

#print axioms
  ExactFixedK13DerivedPreQ16ProfileInvariantOnAdversaryAnchors
#print axioms exact_fixed_k13_adversary_profile_invariant_of_derived_profile
#print axioms exact_fixed_k13_derived_profile_invariant_of_anchor_partition
#print axioms exact_fixed_k13_derived_profile_invariant_iff_adversary_anchor
#print axioms exact_fixed_k13_residual_invariant_of_adversary_anchor_profile

end

end AspisK1.V7Tag73ExactFixedQ16AnchorPartition
