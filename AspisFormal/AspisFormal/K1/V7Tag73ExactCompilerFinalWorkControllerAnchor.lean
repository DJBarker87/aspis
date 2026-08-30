import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment

/-!
# Accepted source to exact final-work/q16 controller anchor

This module composes the exact accepted root-record selector with the literal
unified-scheduler trace and the indexed pre-answer controller.  The result is
the production-facing deterministic starting point for the remaining q16
continuation proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerFinalWorkControllerAnchor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFinalWorkEarliestExposure
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Strict accepted production execution supplies an exact causal controller
anchor inside the conservative `Fin F` inventory.  Its selected answer is
already the accepted 34-bit work digest or the exact returned q16 base. -/
theorem exact_compiler_accepted_final_work_has_exact_controller_anchor
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer q16Base : Digest256)
        (trial : ExactCompilerExposureTrial parameters),
      FinalWork34Accepted workAnswer ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      ExactLiteralPairControllerAnchor transitionFuel
        (exactPlainRomCursor configuration sample.1).erase
        (runExactPlainRom transitionFuel configuration sample).trace
        digest
        (exactOperationalTape input).messages.finalGrinding.selected
        workAnswer q16Base trial.val := by
  obtain ⟨digest, workAnswer, q16Base, trial, accepted, q16BaseExact,
      earliest⟩ :=
    exact_compiler_accepted_final_work_has_exact_earliest_exposure_trial input
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2)) =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa only [exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  have anchor := earliest_exact_literal_pair_aligns_candidate_controller
    (exactPlainRomCursor configuration sample.1).erase
    (operationalTapeCoordinates
      (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters sample.2))
    (runExactPlainRom transitionFuel configuration sample).trace digest
    (exactOperationalTape input).messages.finalGrinding.selected
    workAnswer q16Base earliest traceExact
  exact ⟨digest, workAnswer, q16Base, trial, accepted, q16BaseExact, anchor⟩

#print axioms exact_compiler_accepted_final_work_has_exact_controller_anchor

end

end AspisK1.V7Tag73ExactCompilerFinalWorkControllerAnchor
