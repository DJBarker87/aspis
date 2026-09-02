import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant
import AspisFormal.K1.V7Tag73K13PreQ16MerkleWordSource
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity

/-!
# Pair-coordinate invariance of the pre-q16 Merkle word

The adversary-anchor scheduler theorem already identifies the complete
chronological record prefixes before the selected final-work/q16 coordinate.
This module isolates the only remaining Merkle-source fact—equality of the
two roots absorbed in that common prefix—and turns it into equality of the
received words actually suitable for a q16 probability argument.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactPairPreQ16WordInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73RootAbsorbInputInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Execution-facing root boundary: the two literal C1/C2 absorb inputs in
the common pre-q16 history agree.  Prior digests and salts remain existential
because root recovery uses fixed byte slices and does not require them to be
equal separately. -/
def ExactFixedCleanK13PairRootAbsorbInputsInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
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
    let leftMessages :=
      (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages
    let rightMessages :=
      (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages
    (∃ leftBefore rightBefore : Digest256,
        ∃ leftSalt rightSalt : Digest256,
        bytes leftBefore ++ [domAbsorb, c1RootLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
              leftMessages.c1Root leftSalt).data =
          bytes rightBefore ++ [domAbsorb, c1RootLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
              rightMessages.c1Root rightSalt).data) ∧
      (∃ leftBefore rightBefore : Digest256,
        ∃ leftSalt rightSalt : Digest256,
        bytes leftBefore ++ [domAbsorb, c2RootLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
              leftMessages.c2Root leftSalt).data =
          bytes rightBefore ++ [domAbsorb, c2RootLabel] ++
            (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
              rightMessages.c2Root rightSalt).data)

/-- The exact remaining root-binding endpoint.  It is deliberately separate
from Merkle extraction: both roots were absorbed before final work, so this
is a transcript/source fact rather than a collision-resistance premise. -/
def ExactFixedCleanK13PairRootsInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
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
    exactK12Roots leftWitness.joint.input =
      exactK12Roots rightWitness.joint.input

/-- Exact absorb-input equality recovers both roots by fixed-layout parsing;
no hash injectivity premise is used. -/
theorem exact_fixed_clean_pair_k13_roots_invariant_of_absorb_inputs
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source :
      ExactFixedCleanK13PairRootAbsorbInputsInvariantOnAdversaryAnchors
        transitionFuel configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairRootsInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  obtain ⟨⟨leftC1Before, rightC1Before, leftC1Salt, rightC1Salt, c1InputExact⟩,
      ⟨leftC2Before, rightC2Before, leftC2Salt, rightC2Salt, c2InputExact⟩⟩ :=
    source foldTrial finalTrial hidden left right leftWitness rightWitness
      anchor contextExact foldExact
  have c1Exact := c1_root_eq_of_absorb_input_eq leftC1Before rightC1Before
    (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages.c1Root
    (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages.c1Root
    leftC1Salt rightC1Salt c1InputExact
  have c2Exact := c2_root_eq_of_absorb_input_eq leftC2Before rightC2Before
    (exactK12Runtime leftWitness.joint.input).adversaryValue.rawMessages.c2Root
    (exactK12Runtime rightWitness.joint.input).adversaryValue.rawMessages.c2Root
    leftC2Salt rightC2Salt c2InputExact
  simp only [exactK12Roots]
  rw [c1Exact, c2Exact]

/-- Correct q16 word invariance, stated for the word fixed immediately before
the selected final-work/q16 coordinate. -/
def ExactFixedCleanK13PairPreQ16WordsInvariantOnAdversaryAnchors
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
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
    exactTrialPreQ16Words leftWitness.joint.input finalTrial =
      exactTrialPreQ16Words rightWitness.joint.input finalTrial

/-- Common chronological priors plus root binding construct the complete
pre-q16 word invariant. -/
theorem exact_fixed_clean_pair_k13_pre_q16_words_invariant_of_roots
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (rootsInvariant :
      ExactFixedCleanK13PairRootsInvariantOnAdversaryAnchors transitionFuel
        configuration projection fixedInstance decoder) :
    ExactFixedCleanK13PairPreQ16WordsInvariantOnAdversaryAnchors transitionFuel
      configuration projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftWitness rightWitness anchor
    contextExact foldExact
  obtain ⟨leftPrior, leftLater, rightPrior, rightLater, leftInput, rightInput,
      leftAnswer, rightAnswer, rightActor, leftRootExact, rightRootExact,
      leftTrialExact, rightTrialExact, priorExact⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_root_priors_eq foldTrial
      finalTrial hidden left right leftWitness rightWitness anchor
        programmedCover contextExact foldExact
  apply exactTrialPreQ16Words_eq_of_common_anchor_prior
    leftWitness.joint.input rightWitness.joint.input finalTrial leftPrior
      leftLater rightPrior rightLater
      (.machineFresh .adversary leftInput leftAnswer)
      (.machineFresh rightActor rightInput rightAnswer) leftRootExact
      rightRootExact leftTrialExact rightTrialExact priorExact
  exact rootsInvariant foldTrial finalTrial hidden left right leftWitness
    rightWitness anchor contextExact foldExact

#print axioms
  exact_fixed_clean_pair_k13_roots_invariant_of_absorb_inputs
#print axioms
  exact_fixed_clean_pair_k13_pre_q16_words_invariant_of_roots

end

end AspisK1.V7Tag73ExactPairPreQ16WordInvariant
