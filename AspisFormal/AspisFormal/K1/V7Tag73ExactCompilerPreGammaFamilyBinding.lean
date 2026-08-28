import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence
import AspisFormal.K1.V7Tag73SchedulerNativePreGammaFamily

/-!
# Source binding of the exact compiler pre-gamma family

The evaluator/table proof supplies the literal first-gamma digest and forces
the result-carrying compiler scan into its paused branch.  This module rewrites
the whole exact compiler counterfactual family to the executable occurrence
driver at that source-derived pause.  No caller supplies `firstScan` or an
occurrence premise.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerPreGammaFamilyBinding

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact compiler family is based at a genuinely occurring source pause.
For every fixed nuisance skeleton, the whole gamma-indexed function is the
occurrence replay from that one pause. -/
theorem exact_compiler_pre_gamma_family_source_paused
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample) :
    ∃ initialDigest,
      ∃ pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (gammaOutputInput initialDigest),
        exactCompilerFullTargetScan input
            (gammaOutputInput initialDigest) = .paused pause ∧
        ∀ skeleton : VariableGammaCompleteSkeleton,
          exactCompilerPreGammaFamily input initialDigest skeleton =
            fun gamma => replaySchedulerNativeOccurrenceAtGamma transitionFuel
              pause
              (routedSuccessfulGammaToFlat
                (routedForSkeletonValue skeleton gamma)).1 gamma := by
  obtain ⟨initialDigest, pause, paused⟩ :=
    exact_compiler_full_gamma_target_scan_paused input
  refine ⟨initialDigest, pause, paused, ?_⟩
  intro skeleton
  funext gamma
  unfold exactCompilerPreGammaFamily schedulerNativePreGammaFamily
    schedulerNativeRoutedReplay
  rw [paused]
  simp [replaySchedulerNativeAtGamma, routedForSkeletonValue_returns_value]

#print axioms exact_compiler_pre_gamma_family_source_paused

end

end AspisK1.V7Tag73ExactCompilerPreGammaFamilyBinding
