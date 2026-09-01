import AspisFormal.K1.V7Tag73ExactFixedQ16JointEventHandoff
import AspisFormal.K1.V7Tag73ExactCompilerQ16ForestReplayClosure

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
open AspisK1.V7Tag73ExactCompilerQ16ForestReplayClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactCompilerQ16CoordinateStep
open AspisK1.V7Tag73ExactCompilerQ16DuplexForest
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeQ16ForestReplay
open AspisK1.V7Tag73SchedulerNativeQ16SourcePlan
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
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

/-- The corresponding initial-only run exposes the returned root runtime
before any restoration client is entered.  It is the response projection used
by the later q16 source/decoder bridge. -/
noncomputable def exactFixedK13CounterfactualRootRun
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :=
  runExactPlainRomRoot transitionFuel configuration
    (exactFixedK13CounterfactualSample transitionFuel configuration trial
      hidden residual coordinates)

/-- A total, fail-closed projection of a counterfactual root run.  `none`
means the ordinary source scheduler did not complete its initial stage. -/
noncomputable def exactFixedK13CounterfactualRoot?
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :=
  exactPlainRomRoot? transitionFuel configuration
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

/-- The root projection is likewise an ordinary initial-only production run,
not a synthesized response object. -/
theorem exact_fixed_k13_counterfactual_root_run_is_literal
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerFinalWorkQ16Residual parameters)
    (coordinates : Digest256 × Q16CandidateDigestForest) :
    exactFixedK13CounterfactualRootRun transitionFuel configuration trial hidden
        residual coordinates =
      runExactPlainRomRoot transitionFuel configuration
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

/-- The actual initial-only source run is recovered at the same coordinates;
this supplies the exact root-runtime base case for a typed q16 response
family. -/
theorem exact_fixed_k13_counterfactual_root_run_of_actual_coordinates
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
    exactFixedK13CounterfactualRootRun transitionFuel configuration trial
      sample.1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).2 = runExactPlainRomRoot transitionFuel configuration sample := by
  unfold exactFixedK13CounterfactualRootRun
  rw [exact_fixed_k13_counterfactual_sample_of_actual_coordinates input trial]

/-- The fail-closed root-runtime projection agrees at actual coordinates as
well, without assuming that arbitrary counterfactual coordinates complete. -/
theorem exact_fixed_k13_counterfactual_root_of_actual_coordinates
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
    exactFixedK13CounterfactualRoot? transitionFuel configuration trial sample.1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).1
      (exactFixedK13TrialCoordinates transitionFuel configuration trial
        sample).2 = exactPlainRomRoot? transitionFuel configuration sample := by
  unfold exactFixedK13CounterfactualRoot?
  rw [exact_fixed_k13_counterfactual_sample_of_actual_coordinates input trial]

/-- At its original coordinates, the literal response family inherits the
complete cache-aware q16 replay of the deployed execution.  This joins the
same-hidden-tape response construction to the existing source-aligned q16
forest closure without asserting anything about counterfactual responses.

In particular, this theorem does not turn an adversary-first cache hit into a
fresh verifier draw: `exact_compiler_actual_q16_forest_closure` is the
cache-aware source replay, and the final equality only rewrites the original
member of the response family back to the actual scheduler run. -/
theorem exact_fixed_k13_counterfactual_actual_q16_closure
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (frontierExact : ∀ schedule,
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions) :
    ∃ final,
      runSchedulerNativeQ16BranchList transitionFuel
          (exactOperationalQ16DuplexForest input)
          (schedulerNativeQ16BranchesOfSearch
            (exactOperationalQ16InitialDigest input)
            (exactOperationalTape input).search)
          (exactCompilerInitialQ16Cursor input) = .ok final ∧
      (finishSchedulerNativeQ16Forest transitionFuel final).run =
        exactFixedK13CounterfactualRun transitionFuel configuration trial sample.1
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            sample).1
          (exactFixedK13TrialCoordinates transitionFuel configuration trial
            sample).2 ∧
      q16DigestForestSucceeds (exactOperationalQ16DuplexForest input).1 := by
  obtain ⟨final, replayed, actualRun, forestSucceeds⟩ :=
    exact_compiler_actual_q16_forest_closure transitionRoom input frontierExact
  refine ⟨final, replayed, ?_, forestSucceeds⟩
  rw [exact_fixed_k13_counterfactual_run_of_actual_coordinates input trial]
  exact actualRun

#print axioms exactFixedK13ResponseCoordinateEquiv
#print axioms exactFixedK13CounterfactualSample
#print axioms exactFixedK13CounterfactualRun
#print axioms exactFixedK13CounterfactualRootRun
#print axioms exactFixedK13CounterfactualRoot?
#print axioms exact_fixed_k13_counterfactual_run_is_literal
#print axioms exact_fixed_k13_counterfactual_root_run_is_literal
#print axioms exact_fixed_k13_counterfactual_coordinates_exact
#print axioms exact_fixed_k13_counterfactual_sample_of_actual_coordinates
#print axioms exact_fixed_k13_counterfactual_run_of_actual_coordinates
#print axioms exact_fixed_k13_counterfactual_root_run_of_actual_coordinates
#print axioms exact_fixed_k13_counterfactual_root_of_actual_coordinates
#print axioms exact_fixed_k13_counterfactual_actual_q16_closure

end

end AspisK1.V7Tag73ExactFixedQ16ResponseFamily
