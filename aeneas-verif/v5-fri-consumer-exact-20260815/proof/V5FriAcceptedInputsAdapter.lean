import V5FriConsumerEndToEndProof

/-!
# Accepted FRI execution retains its exact inputs

This small adapter strengthens the already checked end-to-end FRI execution
witness without rebuilding the older extraction snapshot.  The successful
top-level call is inverted once, and the resulting execution record stores
the very same alpha array and inverse function supplied to that call.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriAcceptedInputsAdapter

open V5FriConsumerExact
open AspisV5FriConsumerExactProof

/-- A successful production FRI call yields a complete four-pass execution
whose alpha and inverse inputs are definitionally the inputs of that call. -/
theorem accepted_call_yields_complete_fri_execution_with_exact_inputs
    (openings : VerifiedOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (alphas : Array aspis_core.field.QM31 4#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (inverse : aspis_core.field.M31 → aspis_core.field.M31)
    (sink : fri_checks.V5FriCheckSink)
    (haccept : fri_checks.check_v5_fri_queries openings prepared alphas
      finalPolynomial inverse = .ok (.Ok sink)) :
    ∃ execution : AcceptedProductionFriExecution openings prepared
        finalPolynomial sink,
      execution.sourceAlphas = alphas ∧
        execution.sourceInverse = inverse := by
  obtain ⟨coordinates, alphaPowers, foldedStart, hlayerZero, hpreparation⟩ :=
    top_level_acceptance_exposes_preparation_and_layerZero_loop openings prepared
      alphas finalPolynomial inverse sink haccept
  obtain ⟨foldedFinal, houter⟩ :=
    layerZero_accepted_reaches_outer openings openings.c1.count
      openings.c1.value_width openings.c1.offsets openings.c2.count
      openings.c2.value_width openings.c2.offsets openings.later
      openings.indices.later prepared.inner.claims prepared.inner.powers
      prepared.c1_weight_limbs prepared.c2_multipliers finalPolynomial
      coordinates alphaPowers (alloc.vec.Vec.deref openings.indices.layer0)
      0#usize foldedStart 0#usize sink (by simp) hlayerZero
  obtain ⟨laterRuns⟩ := outer_accepted_three_pass_runs
    openings.later openings.indices.later finalPolynomial alphaPowers
    foldedFinal coordinates sink houter
  refine ⟨{
    sourceAlphas := alphas
    sourceInverse := inverse
    coordinates := coordinates
    alphaPowers := alphaPowers
    foldedStart := foldedStart
    foldedFinal := foldedFinal
    sourceAcceptance := haccept
    preparationTrace := hpreparation
    layerZeroRun := hlayerZero
    outerRun := houter
    laterRuns := laterRuns
    layerZeroReads := ?_
    later0Reads := ?_
    later1Reads := ?_
    later2Reads := ?_ }, rfl, rfl⟩
  · intro target htarget
    exact production_layerZero_accepted_loop_reads_target openings
      openings.c1.count openings.c1.value_width openings.c1.offsets
      openings.c2.count openings.c2.value_width openings.c2.offsets
      openings.later openings.indices.later prepared.inner.claims
      prepared.inner.powers prepared.c1_weight_limbs prepared.c2_multipliers
      finalPolynomial coordinates alphaPowers
      (alloc.vec.Vec.deref openings.indices.layer0) 0#usize target foldedStart
      0#usize sink (by simp) htarget hlayerZero
  · intro target htarget
    exact production_later_completed_loop_reads_target openings.later
      openings.indices.later finalPolynomial coordinates
      laterRuns.coordinates1 alphaPowers 0#usize (by simp) none none
      (alloc.vec.Vec.deref laterRuns.indices0) 0#usize target 0#usize
      (by simp) htarget laterRuns.run0
  · intro target htarget
    exact production_later_completed_loop_reads_target openings.later
      openings.indices.later finalPolynomial laterRuns.coordinates1
      laterRuns.coordinates2 alphaPowers 1#usize (by simp) none none
      (alloc.vec.Vec.deref laterRuns.indices1) 0#usize target 0#usize
      (by simp) htarget laterRuns.run1
  · intro target htarget
    exact production_terminal_completed_loop_reads_target openings.later
      openings.indices.later finalPolynomial laterRuns.coordinates2
      laterRuns.coordinates3 alphaPowers 2#usize (by simp) none none
      (alloc.vec.Vec.deref laterRuns.indices2) 0#usize target 0#usize
      (by simp) htarget laterRuns.run2

#print axioms accepted_call_yields_complete_fri_execution_with_exact_inputs

end AspisV5FriAcceptedInputsAdapter
