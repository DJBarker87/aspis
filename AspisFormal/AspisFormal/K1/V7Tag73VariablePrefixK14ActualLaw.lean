import AspisFormal.K1.V7Tag73VariablePrefixK14Probability
import AspisFormal.K1.V7Tag73VariablePrefixK14MeasureTransport
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger

/-!
# Variable-prefix K1.4 actual-law bridge

The algebraic target and its exact cardinality are already proved. This leaf
isolates the only remaining production-law input: a fixed-hidden coordinate
equivalence together with a deterministic cover of the literal K1.4 event by
the scheduler-native pre-gamma provider target.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73VariablePrefixK14ActualLaw

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisK1.V7Tag73VariablePrefixK14MeasureTransport
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Exact K1.4 measure theorem once the production compiler supplies its
literal variable-prefix coordinates and event inclusion. The provider is
constructed from the scheduler-native pre-gamma family, not caller-selected
after observing gamma. -/
theorem exact_tag73_k14_width29_probability_le_of_variable_prefix_source
    {HiddenTape Residual TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape] [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × TotalGammaDuplexTape)
    (words : HiddenTape → Residual →
      AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (provider : ∀ hidden residual,
      VariablePrefixK14Provider decoder (words hidden residual))
    (covered : ∀ hidden,
      jointEventSlice
          (exactTag73K14Width29Event transitionFuel configuration projection
            fixedInstance decoder) hidden ⊆
        coordinates hidden ⁻¹'
          dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
            (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
              (variablePrefixK14FailureGammaTarget
                (provider hidden residual)))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73K14Width29Event transitionFuel configuration projection
          fixedInstance decoder) ≤ exactK14IdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (exactTag73K14Width29Event transitionFuel configuration projection
          fixedInstance decoder) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)
  apply hidden_tape_variable_prefix_k14_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length
    coordinates
    (fun hidden residual ↦
      variablePrefixK14FailureGammaTarget (provider hidden residual))
    initialBatchChallengeCap
  · intro hidden residual skeleton
    exact variable_prefix_k14_failure_target_card_le
      initialEncoderExact published (provider hidden residual) skeleton
  · exact covered

#print axioms
  exact_tag73_k14_width29_probability_le_of_variable_prefix_source

end

end AspisK1.V7Tag73VariablePrefixK14ActualLaw
