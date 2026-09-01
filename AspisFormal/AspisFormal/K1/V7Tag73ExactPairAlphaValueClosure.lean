import AspisFormal.K1.V7Tag73ExactPairAdversaryProfileClosure

/-!
# Pair-specific alpha-zero value closure

This leaf separates the remaining source-routing obligation from the finite
sampler argument.  Once each accepted alpha-zero block list is the literal
prefix of its four fold-armed router coordinates, equality of the clean pair
context forces the same first accepted prefix and hence the same operational
alpha-zero value.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactPairAlphaValueClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPairAdversaryProfileClosure
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact source endpoint still required from the fold-armed controller: the
deployed bounded decoder consumed a prefix of the four named alpha answers.
No equality, probability claim, or hash assumption is included. -/
def ExactFoldArmedAlphaPrefixBinding
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
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters) : Prop :=
  ∃ (blocks : List Digest256) (rawValue : Qm31Bytes)
      (exactValue : QM31Exact),
    blocks =
        (List.ofFn
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
            sample.2).1.2).take blocks.length ∧
    decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0) blocks =
        some rawValue ∧
    decodeTagQM31ExactLE rawValue = some exactValue ∧
    exactOperationalChallenge input (.alpha 0) = exactValue

/-- Equal complete alpha coordinates force equal operational alpha-zero values
for two accepted source bindings. -/
theorem exact_pair_operational_alpha_zero_eq_of_prefix_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (leftInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (rightInput : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftRouter rightRouter :
      ExactCompilerCausalFoldAlphaFinalWorkQ16Router parameters)
    (contextExact :
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters leftRouter
          leftSample.2).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters rightRouter
          rightSample.2).1)
    (leftBinding : ExactFoldArmedAlphaPrefixBinding leftInput leftRouter)
    (rightBinding : ExactFoldArmedAlphaPrefixBinding rightInput rightRouter) :
    exactOperationalChallenge leftInput (.alpha 0) =
      exactOperationalChallenge rightInput (.alpha 0) := by
  obtain ⟨leftBlocks, leftRaw, leftValue, leftPrefix, leftAccepted,
      leftDecode, leftOperational⟩ := leftBinding
  obtain ⟨rightBlocks, rightRaw, rightValue, rightPrefix, rightAccepted,
      rightDecode, rightOperational⟩ := rightBinding
  have alphaCoordinatesExact := congrArg Prod.snd contextExact
  have rightPrefix' :
      rightBlocks =
        (List.ofFn
          (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
            leftRouter leftSample.2).1.2).take rightBlocks.length := by
    rw [rightPrefix]
    congr 2
    exact alphaCoordinatesExact.symm
  obtain ⟨_blocksExact, rawExact⟩ :=
    exact_challenge_prefixes_of_same_four_blocks_eq
      exactSecureCircleParameterMap (.alpha 0)
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters leftRouter
        leftSample.2).1.2
      leftBlocks rightBlocks leftRaw rightRaw leftPrefix rightPrefix'
      leftAccepted rightAccepted
  have valueExact : leftValue = rightValue := by
    apply Option.some.inj
    calc
      some leftValue = decodeTagQM31ExactLE leftRaw := leftDecode.symm
      _ = decodeTagQM31ExactLE rightRaw := by rw [rawExact]
      _ = some rightValue := rightDecode
  exact leftOperational.trans (valueExact.trans rightOperational.symm)

/-- Production-source obligation for alpha routing, stated per accepted input
and the literal fold/final trial indices.  This is the single endpoint to be
discharged by the fold-armed controller proof. -/
def ExactFoldArmedAlphaPrefixSourceProvider
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) : Prop :=
  ∀ (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (foldTrial finalTrial : ExactCompilerExposureTrial parameters),
    (exactAcceptedFoldTrial input).trial = foldTrial →
    ExactFoldArmedAlphaPrefixBinding input
      (exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters transitionFuel
        foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration sample.1).erase)

/-- The only remaining transcript challenge endpoint after alpha routing is
factored out: pair-specific parsed-gamma equality on the clean fibre. -/
def ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (exactK13ParsedProof leftWitness.joint.input).gamma =
      (exactK13ParsedProof rightWitness.joint.input).gamma

/-- The fold-armed alpha source provider plus the remaining gamma endpoint
construct the exact transcript invariant consumed by K1.3. -/
theorem exact_fixed_clean_pair_k13_transcript_invariant_of_gamma_and_alpha_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      QM31Exact}
    (alphaSource : ExactFoldArmedAlphaPrefixSourceProvider transitionFuel
      configuration projection fixedInstance)
    (gammaInvariant : ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
      transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairTranscriptInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  have gammaExact := gammaInvariant foldTrial finalTrial hidden left right
    leftWitness rightWitness anchor contextExact foldExact
  let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
    transitionFuel foldTrial.val finalTrial.val
    (exactPlainRomCursor configuration hidden).erase
  have leftBinding : ExactFoldArmedAlphaPrefixBinding leftWitness.joint.input
      router := by
    simpa [router] using alphaSource (hidden, left) leftWitness.joint.input
      foldTrial finalTrial leftWitness.foldExact
  have rightBinding : ExactFoldArmedAlphaPrefixBinding rightWitness.joint.input
      router := by
    simpa [router] using alphaSource (hidden, right) rightWitness.joint.input
      foldTrial finalTrial rightWitness.foldExact
  have alphaExact := exact_pair_operational_alpha_zero_eq_of_prefix_bindings
    leftWitness.joint.input rightWitness.joint.input router router
      (by simpa [router] using contextExact) leftBinding rightBinding
  exact ⟨gammaExact, alphaExact⟩

#print axioms ExactFoldArmedAlphaPrefixBinding
#print axioms exact_pair_operational_alpha_zero_eq_of_prefix_bindings
#print axioms ExactFoldArmedAlphaPrefixSourceProvider
#print axioms ExactFixedCleanK13PairGammaInvariantOnAdversaryAnchors
#print axioms
  exact_fixed_clean_pair_k13_transcript_invariant_of_gamma_and_alpha_source

end

end AspisK1.V7Tag73ExactPairAlphaValueClosure
