import AspisFormal.K1.V7Tag73K15ExactMeasureLedger
import AspisFormal.K1.V7Tag73RestoredCausalErrorLedger
import AspisFormal.K1.V7Tag73ProofRelevantUpstreamInterface

/-!
# Exact measured composition of restoration-aware Tag-73 K1.5

The corrected K1.5 classifier has two measured failure shapes:

* the eight fixed-family events, totaling `396430 / (P^4 - 1)`; and
* the constrained restored-gamma residual after usable restorations have been
  routed to extraction, totaling one `initialBatchChallengeCap / (P^4 - 1)`.

This file composes those already proved bounds into the exact
`K15SpendWitnessErrorMeasureBound` consumed by the final K1.6 capstone.  The
remaining source obligation is only deterministic coverage by the two event
sets plus the component bounds themselves.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RestoredK15EventComposition

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RestoredCausalErrorLedger

noncomputable section

/-- Exact two-event composition for any concrete restoration-aware K1.5
stage.  No event independence is assumed. -/
theorem restored_k15_error_measure_bound_of_cover
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
    (fixedEvents : FixedK15Events (ExactCompilerSample HiddenTape parameters))
    (restoredResidual : Set (ExactCompilerSample HiddenTape parameters))
    (covered : k15SpendWitnessErrorEvent stages ⊆
      fixedEvents.failure ∪ restoredResidual)
    (fixedBounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters) fixedEvents)
    (restoredBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          restoredResidual ≤ exactK14IdealRawError) :
    K15SpendWitnessErrorMeasureBound hiddenLaw stages
      exactK15RestoredCausalRawError := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  calc
    law.toOuterMeasure (k15SpendWitnessErrorEvent stages) ≤
        law.toOuterMeasure (fixedEvents.failure ∪ restoredResidual) :=
      law.toOuterMeasure.mono covered
    _ ≤ law.toOuterMeasure fixedEvents.failure +
        law.toOuterMeasure restoredResidual := measure_union_le _ _
    _ ≤ exactK15IdealRawError + exactK14IdealRawError :=
      add_le_add
        (fixed_k15_failure_probability_le law fixedEvents fixedBounds)
        restoredBound
    _ = exactK15RestoredCausalRawError := by
      unfold exactK15RestoredCausalRawError
      ac_rfl

end

#print axioms restored_k15_error_measure_bound_of_cover

end AspisK1.V7Tag73RestoredK15EventComposition
