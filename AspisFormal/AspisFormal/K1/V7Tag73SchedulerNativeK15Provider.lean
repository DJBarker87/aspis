import AspisFormal.K1.V7Tag73SchedulerNativePreGammaFamily
import AspisFormal.K1.V7Tag73VariablePrefixGammaProbability
import AspisFormal.K1.V7Tag73VariablePrefixRestoredK15ConditioningBridge

/-!
# K1.5 provider constructed from scheduler-native pre-gamma data

This module packages the executable scheduler replay family into the provider
consumed by the variable-prefix K1.5 root bound.  The point and point-claim
matrix are ordinary prefix data, fixed even before the gamma-sampler nuisance
skeleton.  The selected response is derived from one whole executable replay
family over every nonzero gamma.

There is no source equality in this construction.  A production use must
separately project the two prefix values and the pause from the actual machine
state; it may not obtain them from a completed proof context.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeK15Provider

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixRestoredK15ConditioningBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Data values already fixed by the deployed transcript before gamma is
sampled.  The four defaults are used only on unavailable replay branches. -/
structure SchedulerNativeK15FixedPrefix
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) where
  point : Fin 10 → QM31Exact
  claims : Fin 3 → Fin 29 → QM31Exact
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : ExactSchedule
  defaultSelected : ExactCandidatePair

/-- Construct the complete variable-prefix K1.5 provider from one frozen
scheduler scan and one pre-gamma prefix.  In particular, `selected` is not a
caller-supplied provider: it is derived by filtering the executable replay
family at every gamma. -/
noncomputable def variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (fixed : SchedulerNativeK15FixedPrefix decoder words)
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest)) :
    VariablePrefixRestoredK15PreGammaProvider decoder words where
  point := fun _ => fixed.point
  claims := fun _ => fixed.claims
  selected := fun skeleton =>
    restoredSelectedProviderOfSchedulerPreGammaFamily
      fixed.defaultResponse fixed.defaultDisclosedFinal
      fixed.defaultSchedule fixed.defaultSelected transitionFuel nuisance
      firstScan skeleton

@[simp] theorem variablePrefixRestoredK15ProviderOfScheduler_point
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (fixed : SchedulerNativeK15FixedPrefix decoder words)
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton) :
    (variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily fixed
      transitionFuel nuisance firstScan).point skeleton = fixed.point := by
  rfl

@[simp] theorem variablePrefixRestoredK15ProviderOfScheduler_claims
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (fixed : SchedulerNativeK15FixedPrefix decoder words)
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton) :
    (variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily fixed
      transitionFuel nuisance firstScan).claims skeleton = fixed.claims := by
  rfl

@[simp] theorem variablePrefixRestoredK15ProviderOfScheduler_selected
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (fixed : SchedulerNativeK15FixedPrefix decoder words)
    (transitionFuel : Nat) (nuisance : SchedulerNativeGammaNuisance)
    (firstScan : SchedulerNativeTargetScan globalOracleCalls
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)
      (gammaOutputInput nuisance.initialDigest))
    (skeleton : VariableGammaCompleteSkeleton) :
    (variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily fixed
      transitionFuel nuisance firstScan).selected skeleton =
        restoredSelectedProviderOfSchedulerPreGammaFamily
          fixed.defaultResponse fixed.defaultDisclosedFinal
          fixed.defaultSchedule fixed.defaultSelected transitionFuel nuisance
          firstScan skeleton := by
  rfl

/-- Fixed-hidden probability bridge with no opaque K1.5 provider argument.
Every response family is constructed from the corresponding scheduler pause;
only the literal finite coordinate equivalence and deterministic event
inclusion remain for a source specialization. -/
theorem uniform_tape_scheduler_native_restored_k15_residual_probability_le
    {Tape Residual : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    {globalOracleCalls : Nat}
    {TapeIdentity Statement Payload Result : Type}
    (coordinates : Equiv Tape (Residual × TotalGammaDuplexTape))
    {decoder : ExactDecoderInstantiation QM31Exact}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (words : Residual → AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (fixed : ∀ residual,
      SchedulerNativeK15FixedPrefix decoder (words residual))
    (transitionFuel : Nat)
    (nuisance : Residual → SchedulerNativeGammaNuisance)
    (firstScan : ∀ residual,
      SchedulerNativeTargetScan globalOracleCalls
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (gammaOutputInput (nuisance residual).initialDigest))
    (event : Set Tape)
    (covered : event ⊆ coordinates ⁻¹'
      AspisK1.V7Tag73SuccessfulSamplerConditioningBridge.dependentSuccessfulSubtypeEvent
        GammaPrefixSucceeds (fun residual =>
          AspisK1.V7Tag73VariablePrefixGammaFlatProbability.variablePrefixRestoredK15ResidualFlatEvent
            (variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily
              (fixed residual) transitionFuel (nuisance residual)
              (firstScan residual)))) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
      (AspisV6PublishedTheoremInterfaces.initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact
    uniform_tape_dependent_variable_prefix_restored_k15_residual_event_probability_le
      coordinates published words
      (fun residual =>
        variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily
          (fixed residual) transitionFuel (nuisance residual)
          (firstScan residual))
      event covered

/-- Exact-compiler specialization: the result-carrying scan is definitionally
the compiler's full unified master-tape scan. -/
noncomputable def exactCompilerVariablePrefixRestoredK15Provider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (fixed : SchedulerNativeK15FixedPrefix decoder words)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256) :
    VariablePrefixRestoredK15PreGammaProvider decoder words where
  point := fun _ => fixed.point
  claims := fun _ => fixed.claims
  selected := fun skeleton =>
    exactCompilerRestoredSelectedProvider fixed.defaultResponse
      fixed.defaultDisclosedFinal fixed.defaultSchedule fixed.defaultSelected
      input initialDigest skeleton

@[simp] theorem exactCompilerVariablePrefixRestoredK15Provider_selected
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (fixed : SchedulerNativeK15FixedPrefix decoder words)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    (exactCompilerVariablePrefixRestoredK15Provider fixed input
      initialDigest).selected skeleton =
        exactCompilerRestoredSelectedProvider fixed.defaultResponse
          fixed.defaultDisclosedFinal fixed.defaultSchedule
          fixed.defaultSelected input initialDigest skeleton := by
  rfl

#print axioms variablePrefixRestoredK15ProviderOfSchedulerPreGammaFamily
#print axioms variablePrefixRestoredK15ProviderOfScheduler_point
#print axioms variablePrefixRestoredK15ProviderOfScheduler_claims
#print axioms variablePrefixRestoredK15ProviderOfScheduler_selected
#print axioms
  uniform_tape_scheduler_native_restored_k15_residual_probability_le
#print axioms exactCompilerVariablePrefixRestoredK15Provider
#print axioms exactCompilerVariablePrefixRestoredK15Provider_selected

end

end AspisK1.V7Tag73SchedulerNativeK15Provider
