import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff

/-!
# Literal same-tape response family for fixed Tag-73 final-work/q16 trials

For a fixed hidden adversary tape and chronological exposure trial, the
existing causal-router equivalence gives a concrete response family indexed by
the exact residual and all 513 final-work/q16 coordinates.  This leaf defines
that family by *inverting the existing finite tape equivalence* and running
the literal production scheduler.

It does not claim that every counterfactual run accepts, returns a parsed
proof, realizes the supplied q16 forest operationally, or has the original
pre-q16 profile.  Those are the remaining q16 causality obligations.  What is
proved here is the important construction boundary: every member is an actual
same-hidden-tape production run, and the original sample is recovered at its
own routed coordinates.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFixedQ16ResponseFamily

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The one fixed causal-router equivalence attached to a hidden tape and
chronological exposure trial.  It is independent of the counterfactual
answers subsequently installed in the master tape. -/
noncomputable def exactFixedK13ResponseCoordinateEquiv
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerFinalWorkQ16Residual parameters ×
        (Digest256 × Q16CandidateDigestForest) :=
  exactCompilerCausalFinalWorkQ16Coordinates parameters
    (exactCompilerExposureTrialDagRouter parameters transitionFuel trial
      (exactPlainRomCursor configuration hidden).erase)

/-- Install a chosen residual and final-work/q16 coordinate tuple through the
literal causal-router inverse.  The hidden adversary tape is preserved
definitionally. -/
noncomputable def exactFixedK13CounterfactualSample
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :
    ExactCompilerSample HiddenTape parameters :=
  (hidden,
    (exactFixedK13ResponseCoordinateEquiv transitionFuel configuration trial
      hidden).symm (residual, coordinates))

/-- Run the production result-carrying scheduler on one explicitly installed
counterfactual coordinate tuple.  This is a computation on an ordinary exact
compiler sample, not an abstract continuation supplied by a caller. -/
noncomputable def exactFixedK13CounterfactualRun
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :=
  runExactPlainRom transitionFuel configuration
    (exactFixedK13CounterfactualSample transitionFuel configuration trial
      hidden residual coordinates)

/-- Every response is exactly the literal production scheduler evaluated at
the sample constructed by the causal-router inverse. -/
theorem exact_fixed_k13_counterfactual_run_is_literal
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :
    exactFixedK13CounterfactualRun transitionFuel configuration trial hidden
        residual coordinates =
      runExactPlainRom transitionFuel configuration
        (exactFixedK13CounterfactualSample transitionFuel configuration trial
          hidden residual coordinates) := by
  rfl

/-- Reapplying the exact trial-coordinate map to a constructed response
recovers precisely the supplied residual and 513-coordinate tuple. -/
theorem exact_fixed_k13_counterfactual_coordinates_exact
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :
    exactFixedK13TrialCoordinates transitionFuel configuration trial
      (exactFixedK13CounterfactualSample transitionFuel configuration trial
        hidden residual coordinates) = (residual, coordinates) := by
  exact (exactFixedK13ResponseCoordinateEquiv transitionFuel configuration
    trial hidden).apply_symm_apply (residual, coordinates)

/-- The actual accepted sample is the response at its own exact causal
coordinates.  This is the base case for relating a response-family argument
back to the deployed execution. -/
theorem exact_fixed_k13_counterfactual_sample_of_actual_coordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters) :
    exactFixedK13CounterfactualSample transitionFuel configuration trial
      sample.1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).2 = sample := by
  apply Prod.ext
  · rfl
  · exact (exactFixedK13ResponseCoordinateEquiv transitionFuel configuration
      trial sample.1).symm_apply_apply sample.2

/-- Consequently the counterfactual response run at actual coordinates is
the literal deployed scheduler run, byte-for-byte at the semantic model level.
-/
theorem exact_fixed_k13_counterfactual_run_of_actual_coordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters) :
    exactFixedK13CounterfactualRun transitionFuel configuration trial sample.1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).2 = runExactPlainRom transitionFuel configuration sample := by
  unfold exactFixedK13CounterfactualRun
  rw [exact_fixed_k13_counterfactual_sample_of_actual_coordinates input trial]

#print axioms exactFixedK13ResponseCoordinateEquiv
#print axioms exactFixedK13CounterfactualSample
#print axioms exactFixedK13CounterfactualRun
#print axioms exact_fixed_k13_counterfactual_run_is_literal
#print axioms exact_fixed_k13_counterfactual_coordinates_exact
#print axioms exact_fixed_k13_counterfactual_sample_of_actual_coordinates
#print axioms exact_fixed_k13_counterfactual_run_of_actual_coordinates

end

end AspisK1.V7Tag73ExactFixedQ16ResponseFamily
