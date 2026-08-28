import AspisFormal.K1.V7Tag73ExactCompilerJoinedPauseSplit
import AspisFormal.K1.V7Tag73ExactCompilerGammaCoordinateStep
import AspisFormal.K1.V7Tag73ExactCompilerGammaCachedCoordinate
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixReplayLift

/-!
# Actual exact-compiler gamma replay closure

This leaf composes the cursor-relative cache-or-future-fresh source alignment
with the executable variable-prefix gamma replay.  The transition-room premise
is the genuine scheduler reserve already carried by the concrete capstones; it
is not a probability or replay premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerActualGammaReplayClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactCompilerJoinedPauseSplit
open AspisK1.V7Tag73ExactCompilerGammaCoordinateStep
open AspisK1.V7Tag73ExactCompilerGammaCachedCoordinate
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting

noncomputable section

/-- Every exact fixed-table gamma coordinate can be consumed from an aligned
production cut.  A cache hit is inert; a miss is routed to its exact remaining
fresh exposure and advances the chronological alignment. -/
theorem exact_compiler_actual_gamma_coordinate_step
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactCompilerGammaCoordinateStep input := by
  intro kind expectedInput expectedAnswer state aligned finalFound
  cases current : lookupEntry state.oracle expectedInput with
  | some entry =>
      have answerExact : entry.output = expectedAnswer :=
        exact_compiler_aligned_cached_answer_exact input state aligned
          expectedInput expectedAnswer entry current finalFound
      refine ⟨state, ?_, ⟨aligned⟩⟩
      exact consume_scheduler_native_gamma_cached_is_inert transitionFuel kind
        expectedInput expectedAnswer state entry current answerExact
  | none =>
      have future : (expectedInput, expectedAnswer) ∈ aligned.future :=
        exact_compiler_aligned_missing_coordinate_mem_future input state aligned
          expectedInput expectedAnswer current finalFound
      obtain ⟨prior, later, pause, futureExact, paused, targetAnswerExact,
          consumedAnswersExact, _remainingAnswersExact, requestTableExact⟩ :=
        exact_compiler_aligned_future_pause_split transitionRoom input state
          aligned expectedInput expectedAnswer future
      exact exact_compiler_aligned_future_pause_preserves_alignment input state
        aligned kind expectedInput expectedAnswer prior later futureExact current
          pause paused targetAnswerExact consumedAnswersExact requestTableExact

/-- The literal production sampler admits the executable pre-gamma replay
family, and replay at its actual routed value reconstructs the exact production
run. -/
theorem exact_compiler_actual_gamma_replay_closure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ initialDigest flat response,
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample := by
  exact exact_compiler_actual_gamma_routed_replay_closure input
    (exact_compiler_actual_gamma_coordinate_step transitionRoom input)

#print axioms exact_compiler_actual_gamma_coordinate_step
#print axioms exact_compiler_actual_gamma_replay_closure

end

end AspisK1.V7Tag73ExactCompilerActualGammaReplayClosure
