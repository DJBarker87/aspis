import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events

/-!
# Exact measured composition of Tag-73 K1.3 and K1.4

This is the final measure glue between the deterministic K1.3/K1.4 error
reductions and the corrected concrete K1.6 capstone.  K1.3 is covered by the
q16 compact-schedule event, the causal one-fold event, the repaired joint
degree-at-most-16 query/relation collision, and the three later degree-six
relation-alpha repair events.  K1.4 is covered by one restoration-wide
width-29 event.

No independence is assumed and no proof-of-work normalization is applied.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K13K14EventComposition

open MeasureTheory
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact K1.3 measure bound from deterministic coverage by the four genuine
raw error events. -/
theorem k13_error_measure_bound_of_query_onefold_joint_later_cover
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (q16Event oneFoldEvent jointBatchEvent laterAlphaEvent :
      Set (ExactCompilerSample HiddenTape parameters))
    (covered : k13CircleListDecodeErrorEvent stages ⊆
      ((q16Event ∪ oneFoldEvent) ∪ jointBatchEvent) ∪ laterAlphaEvent)
    (q16Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure q16Event ≤
        exactQ16IdealRawError)
    (oneFoldBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          oneFoldEvent ≤ exactOneFoldIdealRawError)
    (jointBatchBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          jointBatchEvent ≤ exactJointQueryBatchIdealRawError)
    (laterAlphaBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          laterAlphaEvent ≤ exactLaterRelationAlphaIdealRawError) :
    K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      exactK13IdealRawError := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  calc
    law.toOuterMeasure (k13CircleListDecodeErrorEvent stages) ≤
        law.toOuterMeasure
          (((q16Event ∪ oneFoldEvent) ∪ jointBatchEvent) ∪
            laterAlphaEvent) :=
      law.toOuterMeasure.mono covered
    _ ≤ law.toOuterMeasure ((q16Event ∪ oneFoldEvent) ∪ jointBatchEvent) +
        law.toOuterMeasure laterAlphaEvent :=
      measure_union_le _ _
    _ ≤ (law.toOuterMeasure (q16Event ∪ oneFoldEvent) +
          law.toOuterMeasure jointBatchEvent) +
        law.toOuterMeasure laterAlphaEvent :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((law.toOuterMeasure q16Event + law.toOuterMeasure oneFoldEvent) +
          law.toOuterMeasure jointBatchEvent) +
        law.toOuterMeasure laterAlphaEvent :=
      add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ ((exactQ16IdealRawError + exactOneFoldIdealRawError) +
          exactJointQueryBatchIdealRawError) +
        exactLaterRelationAlphaIdealRawError :=
      add_le_add
        (add_le_add (add_le_add q16Bound oneFoldBound) jointBatchBound)
        laterAlphaBound
    _ = exactK13IdealRawError := rfl

/-- Exact K1.4 measure bound from its single restoration-wide width-29
event. -/
theorem k14_error_measure_bound_of_width29_cover
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {OperationalInput : ExactCompilerSample HiddenTape parameters → Type}
    (stages : ProofRelevantK12ToK15Stages transitionFuel configuration
      fixedInstance relation OperationalInput)
    (width29Event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : k14CoherentChainErrorEvent stages ⊆ width29Event)
    (width29Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          width29Event ≤ exactK14IdealRawError) :
    K14CoherentChainErrorMeasureBound hiddenLaw stages
      exactK14IdealRawError := by
  exact (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
    covered |>.trans width29Bound

/-! ## Exact assembled-stage specializations -/

/-- Once the three literal source events have their raw probability bounds, the
concrete K1.3 classifier has exactly the corrected combined error budget.  The
event cover is proved here from the executable classifier rather than retained
as a capstone premise. -/
theorem exact_assembled_k13_error_measure_bound
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
    (q16Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) ≤ exactQ16IdealRawError)
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
    K13CircleListDecodeErrorMeasureBound hiddenLaw
      (exactTag73ProofRelevantStages transitionFuel configuration projection
        fixedInstance relation decoder decoderBinding k15)
      exactK13IdealRawError := by
  exact k13_error_measure_bound_of_query_onefold_joint_later_cover hiddenLaw
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15)
    (exactTag73K13QueryEvent transitionFuel configuration projection
      fixedInstance decoder)
    (exactTag73K13OneFoldEvent transitionFuel configuration projection
      fixedInstance decoder)
    (exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
      projection fixedInstance decoder source)
    (exactTag73K13LaterRelationAlphaEvent transitionFuel configuration
      projection fixedInstance decoder source)
    (assembled_k13_error_subset_complete transitionFuel
      configuration projection fixedInstance relation decoder decoderBinding
      k15 initialEncoderExact source)
    q16Bound oneFoldBound jointBatchBound laterAlphaBound

/-- The concrete K1.4 classifier has the exact one-cap width-29 budget as soon
as its literal operational event has the causal published-theorem bound. -/
theorem exact_assembled_k14_error_measure_bound
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
    (width29Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactTag73K14Width29Event transitionFuel configuration projection
            fixedInstance decoder) ≤ exactK14IdealRawError) :
    K14CoherentChainErrorMeasureBound hiddenLaw
      (exactTag73ProofRelevantStages transitionFuel configuration projection
        fixedInstance relation decoder decoderBinding k15)
      exactK14IdealRawError := by
  exact k14_error_measure_bound_of_width29_cover hiddenLaw
    (exactTag73ProofRelevantStages transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15)
    (exactTag73K14Width29Event transitionFuel configuration projection
      fixedInstance decoder)
    (assembled_k14_error_subset_width29 transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15)
    width29Bound

end

#print axioms k13_error_measure_bound_of_query_onefold_joint_later_cover
#print axioms k14_error_measure_bound_of_width29_cover
#print axioms exact_assembled_k13_error_measure_bound
#print axioms exact_assembled_k14_error_measure_bound

end AspisK1.V7Tag73K13K14EventComposition
