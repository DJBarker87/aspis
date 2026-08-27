import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface

/-!
# Exact measured composition of Tag-73 K1.3 and K1.4

This is the final measure glue between the deterministic K1.3/K1.4 error
reductions and the corrected concrete K1.6 capstone.  K1.3 is covered by the
q16 compact-schedule event plus the causal one-fold event.  K1.4 is covered by
one restoration-wide width-29 event.

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

noncomputable section

/-- Exact K1.3 measure bound from deterministic coverage by the two genuine
raw error events. -/
theorem k13_error_measure_bound_of_query_onefold_cover
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
    (q16Event oneFoldEvent : Set (ExactCompilerSample HiddenTape parameters))
    (covered : k13CircleListDecodeErrorEvent stages ⊆
      q16Event ∪ oneFoldEvent)
    (q16Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure q16Event ≤
        exactQ16IdealRawError)
    (oneFoldBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          oneFoldEvent ≤ exactOneFoldIdealRawError) :
    K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      exactK13IdealRawError := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  calc
    law.toOuterMeasure (k13CircleListDecodeErrorEvent stages) ≤
        law.toOuterMeasure (q16Event ∪ oneFoldEvent) :=
      law.toOuterMeasure.mono covered
    _ ≤ law.toOuterMeasure q16Event + law.toOuterMeasure oneFoldEvent :=
      measure_union_le _ _
    _ ≤ exactQ16IdealRawError + exactOneFoldIdealRawError :=
      add_le_add q16Bound oneFoldBound
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

end

#print axioms k13_error_measure_bound_of_query_onefold_cover
#print axioms k14_error_measure_bound_of_width29_cover

end AspisK1.V7Tag73K13K14EventComposition
