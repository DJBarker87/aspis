import AspisFormal.K1.V7Tag73CurrentSourceDecodeBridge
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
import AspisFormal.K1.V7Tag73ExactFixedQ16DerivedProfileInvariant

/-!
# Final-vector closure at an adversary-owned K1.3 anchor

The canonical `final256` producer input is fixed across equal residual fibres.
This module connects that byte equality to the decoded mathematical final
vector through the exact canonical fixed-field decoder and parsed-source
binding.  The source provider is deliberately stronger than the legacy parsed
provider: it retains the raw decode certificate needed to justify the bridge.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CurrentSourceDecodeBridge
open AspisK1.V7Tag73ExactAdversaryAnchorSelectedInputInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedCleanQ16ProfileInvariant
open AspisK1.V7Tag73ExactFixedQ16DerivedProfileInvariant
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Production parsing must retain both canonical fixed-field decoding and
the exact parsed-view binding.  This is the natural Rust/Aeneas source
certificate; unlike the legacy provider, it cannot choose unrelated final
coefficients. -/
def ExactFixedK13DecodedParsedSourceProvider
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
      FixedFieldDecodeExact
          (fixedTapeRawMessages (exactOperationalTape input)) decoded ∧
        ExactParsedProofSourceBinding input decoded

/-- The stronger current-source certificate supplies the legacy parsed source
provider used by the existing K1.3 reductions. -/
theorem decoded_parsed_source_provider_implies_parsed_source_provider
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance) :
    ExactFixedK13ParsedSourceProvider transitionFuel configuration projection
      fixedInstance := by
  intro sample input
  obtain ⟨decoded, _decodeExact, binding⟩ := source sample input
  exact ⟨decoded, binding⟩

/-- Equal serialized final blocks decode to the same mathematical final
message under the canonical field decoder. -/
theorem decoded_final_message_eq_of_final_values_eq
    {leftRaw rightRaw : RawTag73ProverMessages}
    {leftDecoded rightDecoded : Fin 641 → QM31Exact}
    (leftDecode : FixedFieldDecodeExact leftRaw leftDecoded)
    (rightDecode : FixedFieldDecodeExact rightRaw rightDecoded)
    (finalValuesExact : leftRaw.finalValues = rightRaw.finalValues) :
    decodedFinalMessage leftDecoded = decodedFinalMessage rightDecoded := by
  funext coefficient
  have leftExact := decode_final_of_fixedFieldDecodeExact leftDecode coefficient
  have rightExact := decode_final_of_fixedFieldDecodeExact rightDecode coefficient
  rw [finalValuesExact] at leftExact
  exact Option.some.inj (leftExact.symm.trans rightExact)

/-- The adversary-anchor chronology therefore fixes the parsed disclosed
final vector, with no hash-injectivity assumption. -/
theorem exact_fixed_clean_k13_adversary_anchor_disclosed_final_eq
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
    (leftWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactFixedK13JointTrialWitness transitionFuel configuration
      projection fixedInstance decoder (hidden, right) trial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.input trial)
    (coordinateExact :
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
  have operationalFinalExact :=
    exact_fixed_clean_k13_adversary_anchor_final_values_eq transitionRoom trial
      hidden left right leftWitness rightWitness anchor programmedCover
      coordinateExact
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

#print axioms
  decoded_parsed_source_provider_implies_parsed_source_provider
#print axioms decoded_final_message_eq_of_final_values_eq
#print axioms
  exact_fixed_clean_k13_adversary_anchor_disclosed_final_eq

end

end AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
