import RuntimeFourRoundReleasedTrace
import RuntimePackerSixSegmentBridge
import RuntimeMaintainedRoundSelectors

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimePublicPackerCapstone

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCDownstreamDeployed
open AspisV5ComponentCRelationRowLinearity
open ComponentCRuntimeFourRoundReleasedTrace
open ComponentCRuntimePackerMaintainedOutput
open ComponentCRuntimePackerSixSegmentBridge

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize
abbrev RuntimeTrace := v5_mask.relation_prover.V5RelationTrace

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The exact arithmetic facts still required after the authentic public
four-round trace and packer control flow have been proved.  The record is
intentionally concrete: it exposes the three generated vectors, their runtime
counts, and each of the six decoded field families. -/
structure ReleasedTraceFamilies
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (later : RuntimeLater)
    (trace : RuntimeTrace) where
  later0 : alloc.vec.Vec RawQM31
  later1 : alloc.vec.Vec RawQM31
  later2 : alloc.vec.Vec RawQM31
  later_eq : later = Array.make 3#usize [later0, later1, later2]
  count0 : Std.Usize
  count1 : Std.Usize
  count2 : Std.Usize
  count0_exact : count0.val = rt.later1Count
  count1_exact : count1.val = rt.later2Count
  count2_exact : count2.val = rt.later3Count
  count0_bound : count0.val ≤ 18
  count1_bound : count1.val ≤ 18
  count2_bound : count2.val ≤ 18
  later0_length : later0.val.length = 4 * rt.later1Count
  later1_length : later1.val.length = 4 * rt.later2Count
  later2_length : later2.val.length = 4 * rt.later3Count
  ood0_source : ∀ sample : Fin 2,
    ∃ value : K, ∃ weights : Fin 1024 → K,
      ∃ coefficients : Fin 1024 → K,
      view (trace.ood_values.val[0]!.val[sample.val]!) = value ∧
        value = maintainedSourceDot weights coefficients ∧
        (decodeRelationSchedule rt).ood0 sample = weights ∧
        coefficients = c
  ood1_source : ∀ sample : Fin 2,
    ∃ value : K, ∃ weights : Fin 256 → K,
      ∃ coefficients : Fin 256 → K,
      view (trace.ood_values.val[1]!.val[sample.val]!) = value ∧
        value = maintainedSourceDot weights coefficients ∧
        (decodeRelationSchedule rt).ood1 sample = weights ∧
        coefficients = round1Coefficients (decodeRelationSchedule rt) c
  ood2_source : ∀ sample : Fin 2,
    ∃ value : K, ∃ weights : Fin 64 → K,
      ∃ coefficients : Fin 64 → K,
      view (trace.ood_values.val[2]!.val[sample.val]!) = value ∧
        value = maintainedSourceDot weights coefficients ∧
        (decodeRelationSchedule rt).ood2 sample = weights ∧
        coefficients = round2Coefficients (decodeRelationSchedule rt) c
  ood3_source : ∀ sample : Fin 2,
    ∃ value : K, ∃ weights : Fin 16 → K,
      ∃ coefficients : Fin 16 → K,
      view (trace.ood_values.val[3]!.val[sample.val]!) = value ∧
        value = maintainedSourceDot weights coefficients ∧
        (decodeRelationSchedule rt).ood3 sample = weights ∧
        coefficients = round3Coefficients (decodeRelationSchedule rt) c
  polynomial0_source : ∀ degree : Fin 7,
    ∃ value : K, ∃ weights : Fin 1024 → K,
      ∃ coefficients : Fin 1024 → K,
      view (trace.sumchecks.val[0]!.val[degree.val]!) = value ∧
        value = maintainedSourcePolynomial 256 weights coefficients degree ∧
        (decodeRelationSchedule rt).poly0 = weights ∧
        coefficients = c
  polynomial1_source : ∀ degree : Fin 7,
    ∃ value : K, ∃ weights : Fin 256 → K,
      ∃ coefficients : Fin 256 → K,
      view (trace.sumchecks.val[1]!.val[degree.val]!) = value ∧
        value = maintainedSourcePolynomial 64 weights coefficients degree ∧
        (decodeRelationSchedule rt).poly1 = weights ∧
        coefficients = round1Coefficients (decodeRelationSchedule rt) c
  polynomial2_source : ∀ degree : Fin 7,
    ∃ value : K, ∃ weights : Fin 64 → K,
      ∃ coefficients : Fin 64 → K,
      view (trace.sumchecks.val[2]!.val[degree.val]!) = value ∧
        value = maintainedSourcePolynomial 16 weights coefficients degree ∧
        (decodeRelationSchedule rt).poly2 = weights ∧
        coefficients = round2Coefficients (decodeRelationSchedule rt) c
  polynomial3_source : ∀ degree : Fin 7,
    ∃ value : K, ∃ weights : Fin 16 → K,
      ∃ coefficients : Fin 16 → K,
      view (trace.sumchecks.val[3]!.val[degree.val]!) = value ∧
        value = maintainedSourcePolynomial 4 weights coefficients degree ∧
        (decodeRelationSchedule rt).poly3 = weights ∧
        coefficients = round3Coefficients (decodeRelationSchedule rt) c
  later0_read : ∀ (index : Fin rt.later1Count) (slot : Fin 4),
    view (later0.val[4 * index.val + slot.val]!) =
      later1ReadMap (decodeFriSchedule rt) enc c (index, slot)
  later1_read : ∀ (index : Fin rt.later2Count) (slot : Fin 4),
    view (later1.val[4 * index.val + slot.val]!) =
      later2ReadMap (decodeFriSchedule rt) enc c (index, slot)
  later2_read : ∀ (index : Fin rt.later3Count) (slot : Fin 4),
    view (later2.val[4 * index.val + slot.val]!) =
      later3ReadMap (decodeFriSchedule rt) enc c (index, slot)
  final_read : ∀ coefficient : Fin 4,
    view (trace.final_coefficients.val[coefficient.val]!) =
      finalCoefficientMap (decodeFriSchedule rt) c coefficient

/-- The source-shaped OOD witnesses imply the maintained four-round selector
without asking the concrete QM31 instance elaborator to normalize the whole
round selector at a construction site. -/
theorem ReleasedTraceFamilies.ood
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (later : RuntimeLater)
    (trace : RuntimeTrace)
    (families : ReleasedTraceFamilies rt enc c view later trace) :
    ∀ (round : Fin 4) (sample : Fin 2),
      view (trace.ood_values.val[round.val]!.val[sample.val]!) =
        roundOodRows (decodeRelationSchedule rt) round c sample := by
  intro round sample
  have hcases : round.val = 0 ∨ round.val = 1 ∨
      round.val = 2 ∨ round.val = 3 := by omega
  rcases hcases with hround | hround | hround | hround
  · rcases families.ood0_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourceDot_eq] at hvalue
    have hr : round = 0 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundOodRows_zero_scalar, hweights, ← hcoefficients]
    exact hvalue
  · rcases families.ood1_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourceDot_eq] at hvalue
    have hr : round = 1 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundOodRows_one, hweights, ← hcoefficients]
    exact hvalue
  · rcases families.ood2_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourceDot_eq] at hvalue
    have hr : round = 2 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundOodRows_two, hweights, ← hcoefficients]
    exact hvalue
  · rcases families.ood3_source sample with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourceDot_eq] at hvalue
    have hr : round = 3 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundOodRows_three, hweights, ← hcoefficients]
    exact hvalue

#print axioms ReleasedTraceFamilies.ood

theorem ReleasedTraceFamilies.polynomial
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (later : RuntimeLater)
    (trace : RuntimeTrace)
    (families : ReleasedTraceFamilies rt enc c view later trace) :
    ∀ (round : Fin 4) (degree : Fin 7),
      view (trace.sumchecks.val[round.val]!.val[degree.val]!) =
        roundPolynomialRows (decodeRelationSchedule rt) round c degree := by
  intro round degree
  have hcases : round.val = 0 ∨ round.val = 1 ∨
      round.val = 2 ∨ round.val = 3 := by omega
  rcases hcases with hround | hround | hround | hround
  · rcases families.polynomial0_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourcePolynomial_eq] at hvalue
    have hr : round = 0 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundPolynomialRows_zero, hweights, ← hcoefficients]
    exact hvalue
  · rcases families.polynomial1_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourcePolynomial_eq] at hvalue
    have hr : round = 1 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundPolynomialRows_one_scalar, hweights,
      ← hcoefficients]
    exact hvalue
  · rcases families.polynomial2_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourcePolynomial_eq] at hvalue
    have hr : round = 2 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundPolynomialRows_two, hweights, ← hcoefficients]
    exact hvalue
  · rcases families.polynomial3_source degree with
      ⟨value, weights, coefficients, hstored, hevaluated,
        hweights, hcoefficients⟩
    have hvalue := hstored.trans hevaluated
    rw [maintainedSourcePolynomial_eq] at hvalue
    have hr : round = 3 := Fin.eq_of_val_eq hround
    rw [hround, hr, roundPolynomialRows_three, hweights, ← hcoefficients]
    exact hvalue

#print axioms ReleasedTraceFamilies.polynomial

/-- The explicit released-trace family record discharges the packer's sole
per-row arithmetic interface. -/
theorem released_trace_families_build_rows_match_deployed
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (later : RuntimeLater)
    (trace : RuntimeTrace)
    (families : ReleasedTraceFamilies rt enc c view later trace) :
    GeneratedPackerRowsMatchDeployed rt enc c view
      trace.ood_values trace.sumchecks
      (Array.make 3#usize [families.later0, families.later1, families.later2])
      trace.final_coefficients := by
  exact six_segment_facts_build_rows_match_deployed rt enc c view
    trace.ood_values trace.sumchecks
    families.later0 families.later1 families.later2 trace.final_coefficients
    families.later0_length families.later1_length families.later2_length
    families.ood families.polynomial families.later0_read families.later1_read
    families.later2_read families.final_read

#print axioms released_trace_families_build_rows_match_deployed

/-- Public-entrypoint capstone.  A successful authentic Component-C execution
already supplies the exact four-round relation arrays and the very output of
the authentic public packer.  Once the explicit six arithmetic families are
provided for those returned objects, that same output is identified
coordinatewise with the maintained deployed evaluator. -/
theorem generated_public_success_output_matches_deployed
    (schedule :
      v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule)
    (coefficients codeword : Slice RawQM31)
    (expectedInactiveClaim : RawQM31)
    (output : alloc.vec.Vec RawQM31)
    (hrun :
      v5_mask.component_c_runtime.evaluate_component_c_runtime_private_view
          schedule coefficients codeword expectedInactiveClaim =
        ok (core.result.Result.Ok output))
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (hfamilies : ∀ (later : RuntimeLater) (trace : RuntimeTrace),
      (∃ w : FourRoundReleasedWitness,
        ReleasedCoordinatesMatch trace.ood_values trace.sumchecks w) →
      ReleasedTraceFamilies rt enc c view later trace) :
    ∃ later : RuntimeLater, ∃ trace : RuntimeTrace,
    ∃ w : FourRoundReleasedWitness,
      ReleasedCoordinatesMatch trace.ood_values trace.sumchecks w ∧
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later trace.final_coefficients =
        ok (core.result.Result.Ok output) ∧
      output.val.length = fRows (decodeFriSchedule rt) ∧
      ∀ row : Fin (fRows (decodeFriSchedule rt)),
        view output.val[row.val]! = deployedEvaluate rt enc c row := by
  rcases generated_public_success_has_released_trace
      schedule coefficients codeword expectedInactiveClaim output hrun with
    ⟨later, trace, w, hreleased, hpack⟩
  let families := hfamilies later trace ⟨w, hreleased⟩
  have hpack' :
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks
          (Array.make 3#usize
            [families.later0, families.later1, families.later2])
          trace.final_coefficients = ok (core.result.Result.Ok output) := by
    simpa [families.later_eq] using hpack
  have hrows := released_trace_families_build_rows_match_deployed
    rt enc c view later trace families
  have hidentified := generated_successful_pack_output_matches_deployed
    rt enc c view trace.ood_values trace.sumchecks
    families.later0 families.later1 families.later2 trace.final_coefficients
    families.count0 families.count1 families.count2 output hpack'
    (by rw [families.later0_length, families.count0_exact])
    (by rw [families.later1_length, families.count1_exact])
    (by rw [families.later2_length, families.count2_exact])
    families.count0_bound families.count1_bound families.count2_bound
    families.count0_exact families.count1_exact families.count2_exact hrows
  exact ⟨later, trace, w, hreleased, hpack, hidentified.1, hidentified.2⟩

#print axioms generated_public_success_output_matches_deployed

/-- Concrete specialization used by the current-source join.  Unlike
`generated_public_success_output_matches_deployed`, this theorem consumes the
one `later`/`trace` family returned by the actual execution; it does not demand
a family constructor for every unrelated pair sharing only the released
coordinates. -/
theorem concrete_released_trace_families_output_matches_deployed
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (later : RuntimeLater)
    (trace : RuntimeTrace)
    (output : alloc.vec.Vec RawQM31)
    (families : ReleasedTraceFamilies rt enc c view later trace)
    (hpack :
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks later trace.final_coefficients =
        ok (core.result.Result.Ok output)) :
    output.val.length = fRows (decodeFriSchedule rt) ∧
      ∀ row : Fin (fRows (decodeFriSchedule rt)),
        view output.val[row.val]! = deployedEvaluate rt enc c row := by
  have hpack' :
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          trace.ood_values trace.sumchecks
          (Array.make 3#usize
            [families.later0, families.later1, families.later2])
          trace.final_coefficients = ok (core.result.Result.Ok output) := by
    simpa [families.later_eq] using hpack
  have hrows := released_trace_families_build_rows_match_deployed
    rt enc c view later trace families
  exact generated_successful_pack_output_matches_deployed
    rt enc c view trace.ood_values trace.sumchecks
    families.later0 families.later1 families.later2 trace.final_coefficients
    families.count0 families.count1 families.count2 output hpack'
    (by rw [families.later0_length, families.count0_exact])
    (by rw [families.later1_length, families.count1_exact])
    (by rw [families.later2_length, families.count2_exact])
    families.count0_bound families.count1_bound families.count2_bound
    families.count0_exact families.count1_exact families.count2_exact hrows

#print axioms concrete_released_trace_families_output_matches_deployed

end aspis_prover.ComponentCRuntimePublicPackerCapstone
