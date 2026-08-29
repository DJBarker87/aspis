import AspisFormal.K1.V7Tag73CausalQ16ProbabilityBridge
import AspisFormal.K1.V7Tag73Q16CountCertificateBridge

/-!
# Causal q16 probability bound at the frozen release denominator

This is the release-facing form of the adaptive scheduler theorem.  It
combines the causal online routing result with the generated cap-203 count
certificate, so callers receive `exactQ16IdealRawError` directly rather than
supplying or trusting an equality between two denominator representations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalQ16ReleaseBound

open MeasureTheory
open AspisK1.V7Tag73CausalQ16ProbabilityBridge
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73Q16CountCertificateBridge
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Exact hidden-tape averaged causal q16 bound, with the generated semantic
count already identified with the frozen release integer. -/
theorem exact_compiler_causal_q16_event_probability_le_release
    {HiddenTape : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (router : HiddenTape → ExactCompilerCausalQ16Router parameters)
    (bad : HiddenTape → ExactCompilerQ16Residual parameters →
      Finset (Fin 262144))
    (badCard : ∀ hidden residual, (bad hidden residual).card ≤ 9557)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      exactCompilerCausalQ16Coordinates parameters (router hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent q16DigestForestSucceeds
          (fun residual => successfulQ16DigestForestEquiv ⁻¹'
            q16SuccessfulCoordinatesBadEvent (bad hidden residual))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      exactQ16IdealRawError := by
  have bound := exact_compiler_causal_q16_event_probability_le_semantic
    hiddenLaw parameters router bad badCard reference traceExists event covered
  unfold exactQ16IdealRawError
  rwa [semanticCompactFavourable_eq_exactK13CompactFavourable] at bound

end


#print axioms exact_compiler_causal_q16_event_probability_le_release

end AspisK1.V7Tag73CausalQ16ReleaseBound
