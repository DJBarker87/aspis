import AspisFormal.K1.V7Tag73DerivedK13Q16Handoff
import AspisFormal.K1.V7Tag73DerivedK13SourceBridge
import AspisFormal.K1.V7Tag73ExactFixedQ16SemanticNoninterference

/-!
# Derived-profile endpoint for fixed Tag-73 K1.3 q16 causality

This module joins the verifier-derived q16 profile to the existing fixed
finite probability package.  It deliberately leaves one source/causality
statement visible: equal non-q16 residual coordinates must preserve the four
components of the derived profile.  Everything else, including canonical
field decoding, gamma/alpha binding, total inverse schedules, and the legacy
residual-factorization interface, is derived in Lean.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DerivedK13Q16Handoff
open AspisK1.V7Tag73DerivedK13SourceBridge
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16ResidualFactorization
open AspisK1.V7Tag73ExactFixedQ16SemanticNoninterference
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The canonical fixed-field decoder selected from the already explicit
parsed-source provider.  Functionality of the decoder means its value is not
a new proof assumption. -/
noncomputable def exactFixedK13DerivedDecoded
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Fin 641 → QM31Exact :=
  Classical.choose (source sample input)

/-- The binding corresponding to `exactFixedK13DerivedDecoded`. -/
theorem exact_fixed_k13_derived_decoded_binding
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactParsedProofSourceBinding input
      (exactFixedK13DerivedDecoded transitionFuel configuration projection
        fixedInstance source input) := by
  exact Classical.choose_spec (source sample input)

/-- The only four values whose q16 noninterference is needed.  The selected
schedule, openings, and opaque parsed-proof identity are intentionally absent.
-/
noncomputable def exactFixedK13DerivedQ16Profile
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : DerivedK13Q16BadProfile where
  words := exactPrefixK12Words input
  decoded := exactFixedK13DerivedDecoded transitionFuel configuration
    projection fixedInstance source input
  gamma := exactOperationalChallenge input .gamma
  alphaZero := exactOperationalChallenge input (.alpha 0)

/-- Exact remaining K1.3 q16 source obligation.  This is a profile equality,
not an equality of returned proofs, parser objects, or query schedules. -/
def ExactFixedK13DerivedPreQ16ProfileInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
        projection fixedInstance decoder (hidden, right) trial),
    (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, left)).1 =
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        (hidden, right)).1 →
    exactFixedK13DerivedQ16Profile transitionFuel configuration projection
        fixedInstance source leftWitness.input =
      exactFixedK13DerivedQ16Profile transitionFuel configuration projection
        fixedInstance source rightWitness.input

-- The source bindings normalize the legacy parsed fields; only the profile
-- equality itself remains a causality/source theorem.
set_option maxHeartbeats 800000 in
theorem exact_fixed_k13_semantic_invariant_of_derived_profile
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
    (profileInvariant : ExactFixedK13DerivedPreQ16ProfileInvariant
      transitionFuel configuration projection fixedInstance decoder source) :
    ExactFixedK13PreQ16SemanticInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact
  have profileExact := profileInvariant trial hidden left right leftWitness
    rightWitness residualExact
  have leftBinding := exact_fixed_k13_derived_decoded_binding transitionFuel
    configuration projection fixedInstance source leftWitness.input
  have rightBinding := exact_fixed_k13_derived_decoded_binding transitionFuel
    configuration projection fixedInstance source rightWitness.input
  have wordsExact := congrArg DerivedK13Q16BadProfile.words profileExact
  have decodedExact := congrArg DerivedK13Q16BadProfile.decoded profileExact
  have gammaOperationalExact :=
    congrArg DerivedK13Q16BadProfile.gamma profileExact
  have alphaOperationalExact :=
    congrArg DerivedK13Q16BadProfile.alphaZero profileExact
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
  have finalExact :
      (exactK13ParsedProof leftWitness.input).disclosedFinal =
        (exactK13ParsedProof rightWitness.input).disclosedFinal := by
    calc
      (exactK13ParsedProof leftWitness.input).disclosedFinal =
          decodedFinalMessage
            (exactFixedK13DerivedDecoded transitionFuel configuration
              projection fixedInstance source leftWitness.input) :=
        leftBinding.disclosedFinalExact
      _ = decodedFinalMessage
            (exactFixedK13DerivedDecoded transitionFuel configuration
              projection fixedInstance source rightWitness.input) := by
        rw [decodedExact]
      _ = (exactK13ParsedProof rightWitness.input).disclosedFinal :=
        rightBinding.disclosedFinalExact.symm
  have scheduleExact :
      (exactK13ParsedProof leftWitness.input).schedule =
        (exactK13ParsedProof rightWitness.input).schedule := by
    calc
      (exactK13ParsedProof leftWitness.input).schedule =
          AspisK1.V7Tag73CanonicalOneFoldSchedule.canonicalOneFoldSchedule
            (exactOperationalChallenge leftWitness.input (.alpha 0)) :=
        exact_parsed_schedule_eq_canonical_of_source_binding leftBinding
      _ = AspisK1.V7Tag73CanonicalOneFoldSchedule.canonicalOneFoldSchedule
            (exactOperationalChallenge rightWitness.input (.alpha 0)) := by
        rw [alphaOperationalExact]
      _ = (exactK13ParsedProof rightWitness.input).schedule :=
        (exact_parsed_schedule_eq_canonical_of_source_binding rightBinding).symm
  exact ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩

/-- The exact derived-profile condition discharges the existing finite q16
residual invariant, preserving all already checked q16 probability algebra. -/
theorem exact_fixed_k13_residual_invariant_of_derived_profile
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
    (profileInvariant : ExactFixedK13DerivedPreQ16ProfileInvariant
      transitionFuel configuration projection fixedInstance decoder source) :
    ExactFixedK13ResidualInvariant transitionFuel configuration projection
      fixedInstance decoder := by
  exact exact_fixed_k13_residual_invariant_of_pre_q16_semantics
    (exact_fixed_k13_semantic_invariant_of_derived_profile source
      profileInvariant)

#print axioms exact_fixed_k13_derived_decoded_binding
#print axioms exact_fixed_k13_semantic_invariant_of_derived_profile
#print axioms exact_fixed_k13_residual_invariant_of_derived_profile

end

end AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
