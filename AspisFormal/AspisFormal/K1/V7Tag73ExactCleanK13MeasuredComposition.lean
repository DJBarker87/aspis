import AspisFormal.K1.V7Tag73ExactFixedCleanWorkDependentQ16ProfileInvariant
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent
import AspisFormal.K1.V7Tag73K13IdealErrorLedger

/-!
# Clean-restricted measured K1.3 composition

This small module isolates the event algebra needed to install the causal,
work-dependent q16 theorem in K1.6.  Keeping it separate prevents the full
restoration/K1.5 dependency graph from being replayed while this seam is
checked.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactMeasuredCleanK16Assembly

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The K1.3 error expression before replacing the semantic cap-203 count by
the frozen decimal release certificate.  Keeping this definition here avoids
pulling thousands of generated count-certificate modules into every semantic
composition build.  The separate release bridge proves it equal to
`exactK13IdealRawError`. -/
def exactK13SemanticRawError : ENNReal :=
  q16SemanticOneForestRawError + exactOneFoldIdealRawError +
    exactJointQueryBatchIdealRawError + exactLaterRelationAlphaIdealRawError

/-- Restricted K1.3 composition.  Only q16 needs its new clean-event bound;
the remaining unconditional event bounds are safely restricted by monotonicity.
-/
theorem exact_assembled_k13_clean_error_measure_bound
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (q16CleanBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73K13QueryEvent transitionFuel configuration projection
              fixedInstance decoder) ≤ q16SemanticOneForestRawError)
    (oneFoldBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13OneFoldEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ exactOneFoldIdealRawError)
    (jointBatchBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13JointQueryBatchCollisionEvent transitionFuel
            configuration projection fixedInstance decoder source) ≤
        exactJointQueryBatchIdealRawError)
    (laterAlphaBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
            projection fixedInstance decoder source) ≤
        exactLaterRelationAlphaIdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73ProofRelevantStages transitionFuel configuration
              projection fixedInstance relation decoder decoderBinding k15)) ≤
      exactK13SemanticRawError := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  let q16 := exactTag73K13QueryEvent transitionFuel configuration projection
    fixedInstance decoder
  let oneFold := exactTag73K13OneFoldEvent transitionFuel configuration
    projection fixedInstance decoder
  let joint := exactTag73K13JointQueryBatchCollisionEvent transitionFuel
    configuration projection fixedInstance decoder source
  let later := exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
    projection fixedInstance decoder source
  have covered :
      clean ∩ k13CircleListDecodeErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15) ⊆
        (((clean ∩ q16) ∪ (clean ∩ oneFold)) ∪ (clean ∩ joint)) ∪
          (clean ∩ later) := by
    rintro sample ⟨cleanMember, errorMember⟩
    have classified := assembled_k13_error_subset_complete transitionFuel
      configuration projection fixedInstance relation decoder decoderBinding
      k15 initialEncoderExact source errorMember
    change sample ∈ ((q16 ∪ oneFold) ∪ joint) ∪ later at classified
    rcases classified with ((query | fold) | batch) | alpha
    · exact Or.inl (Or.inl (Or.inl ⟨cleanMember, query⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨cleanMember, fold⟩))
    · exact Or.inl (Or.inr ⟨cleanMember, batch⟩)
    · exact Or.inr ⟨cleanMember, alpha⟩
  have oneFoldClean : law.toOuterMeasure (clean ∩ oneFold) ≤
      exactOneFoldIdealRawError :=
    (law.toOuterMeasure.mono Set.inter_subset_right).trans oneFoldBound
  have jointClean : law.toOuterMeasure (clean ∩ joint) ≤
      exactJointQueryBatchIdealRawError :=
    (law.toOuterMeasure.mono Set.inter_subset_right).trans jointBatchBound
  have laterClean : law.toOuterMeasure (clean ∩ later) ≤
      exactLaterRelationAlphaIdealRawError :=
    (law.toOuterMeasure.mono Set.inter_subset_right).trans laterAlphaBound
  calc
    law.toOuterMeasure
        (clean ∩ k13CircleListDecodeErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15)) ≤
      law.toOuterMeasure
        ((((clean ∩ q16) ∪ (clean ∩ oneFold)) ∪ (clean ∩ joint)) ∪
          (clean ∩ later)) := law.toOuterMeasure.mono covered
    _ ≤ law.toOuterMeasure
          (((clean ∩ q16) ∪ (clean ∩ oneFold)) ∪ (clean ∩ joint)) +
        law.toOuterMeasure (clean ∩ later) := measure_union_le _ _
    _ ≤ (law.toOuterMeasure ((clean ∩ q16) ∪ (clean ∩ oneFold)) +
          law.toOuterMeasure (clean ∩ joint)) +
        law.toOuterMeasure (clean ∩ later) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((law.toOuterMeasure (clean ∩ q16) +
            law.toOuterMeasure (clean ∩ oneFold)) +
          law.toOuterMeasure (clean ∩ joint)) +
        law.toOuterMeasure (clean ∩ later) :=
      add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ ((q16SemanticOneForestRawError + exactOneFoldIdealRawError) +
          exactJointQueryBatchIdealRawError) +
        exactLaterRelationAlphaIdealRawError :=
      add_le_add
        (add_le_add (add_le_add q16CleanBound oneFoldClean) jointClean)
        laterClean
    _ = exactK13SemanticRawError := rfl

end


#print axioms exactK13SemanticRawError
#print axioms exact_assembled_k13_clean_error_measure_bound

end AspisK1.V7Tag73ExactMeasuredCleanK16Assembly
