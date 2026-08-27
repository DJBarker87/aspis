import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73Q16RawENNRealProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningBridge

/-!
# Compiler-tape conditioning for the Tag-73 first-cap-203 q16 scan

The finite q16 theorem is stated on successful first-admitted scan traces.
This module transports it to the exact compiler fresh-answer tape while
allowing every residual coordinate and hidden prover tape to select a
different pre-q16 consistency set of size at most 9,557.

The generated frontier certificate enters only through the exact equality
between the semantic admitted-schedule count and the frozen release number.
No proof-of-work normalization is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SuccessfulQ16ConditioningBridge

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Transport a residual-dependent successful q16 bad event to one complete
uniform fresh-answer tape. -/
theorem uniform_tape_dependent_q16_event_probability_le
    {Tape Total Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : Tape ≃ Residual × Total)
    (successfulCoordinates : {a : Total // success a} ≃
      FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)
    (bad : Residual → Finset (Fin 262144))
    (badCard : ∀ residual, (bad residual).card ≤ 9557)
    (reference : Residual → AdmittedResult SemanticCap203Admitted)
    (traceExists : ∀ residual, Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        (reference residual).1))
    (countExact : semanticCompactFavourable = exactK13CompactFavourable)
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      dependentSuccessfulSubtypeEvent success (fun residual =>
        successfulCoordinates ⁻¹' q16FirstAdmittedBadEvent (bad residual))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      exactQ16IdealRawError := by
  letI : Nonempty
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64) :=
    ⟨successfulCoordinates
      (Classical.choice (inferInstance : Nonempty {a : Total // success a}))⟩
  apply uniform_tape_dependent_successful_event_probability_le success
    coordinates successfulCoordinates
    (fun residual => q16FirstAdmittedBadEvent (bad residual))
    exactQ16IdealRawError
  · intro residual
    have bound := q16_first_cap203_bad_measure_le_semantic_choose
      (bad residual) (badCard residual) (reference residual)
      (traceExists residual)
    unfold exactQ16IdealRawError
    rwa [countExact] at bound
  · exact covered

/-- Average the fixed-hidden q16 conditioning bridge over the compiler's
arbitrary hidden-tape law. -/
theorem exact_compiler_dependent_q16_event_probability_le
    {HiddenTape Total Residual : Type} [Fintype HiddenTape]
    [Fintype Total] [Nonempty Total]
    [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape) (freshExposures : Nat)
    (success : Total → Prop) [DecidablePred success]
    [Nonempty {a : Total // success a}]
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 freshExposures ≃ Residual × Total)
    (successfulCoordinates : {a : Total // success a} ≃
      FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)
    (bad : HiddenTape → Residual → Finset (Fin 262144))
    (badCard : ∀ hidden residual, (bad hidden residual).card ≤ 9557)
    (reference : HiddenTape → Residual →
      AdmittedResult SemanticCap203Admitted)
    (traceExists : ∀ hidden residual, Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        (reference hidden residual).1))
    (countExact : semanticCompactFavourable = exactK13CompactFavourable)
    (event : Set (HiddenTape × FreshAnswerTape Digest256 freshExposures))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent success (fun residual =>
          successfulCoordinates ⁻¹'
            q16FirstAdmittedBadEvent (bad hidden residual))) :
    (hiddenTapeUniformFreshJointLaw hiddenLaw freshExposures).toOuterMeasure
        event ≤ exactQ16IdealRawError := by
  apply joint_event_probability_le_of_every_slice_le
  intro hidden
  exact uniform_tape_dependent_q16_event_probability_le success
    (coordinates hidden) successfulCoordinates (bad hidden) (badCard hidden)
    (reference hidden) (traceExists hidden) countExact
    (jointEventSlice event hidden) (covered hidden)

end

#print axioms uniform_tape_dependent_q16_event_probability_le
#print axioms exact_compiler_dependent_q16_event_probability_le

end AspisK1.V7Tag73SuccessfulQ16ConditioningBridge
