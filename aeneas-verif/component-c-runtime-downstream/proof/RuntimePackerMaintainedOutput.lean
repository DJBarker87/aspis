import RuntimePackerFullCorrespondence
import AspisFormal.V5ComponentCDownstreamDeployed

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimePackerMaintainedOutput

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCDownstreamDeployed
open ComponentCRuntimePackerProof
open ComponentCRuntimePackerFullCorrespondence

abbrev RawQM31 := aspis_core.field.QM31

private theorem array3_read_zero {T : Type} [Inhabited T]
    (a b c : T) :
    Array.index_usize (Array.make 3#usize [a, b, c]) 0#usize = ok a := by
  simp [Array.index_usize, Array.make]

private theorem array3_read_one {T : Type} [Inhabited T]
    (a b c : T) :
    Array.index_usize (Array.make 3#usize [a, b, c]) 1#usize = ok b := by
  simp [Array.index_usize, Array.make]

private theorem array3_read_two {T : Type} [Inhabited T]
    (a b c : T) :
    Array.index_usize (Array.make 3#usize [a, b, c]) 2#usize = ok c := by
  simp [Array.index_usize, Array.make]

private theorem vec_len_val {T : Type} (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.len v).val = v.val.length := by
  rfl

private theorem usize_div_four_exact
    (length count : Std.Usize) (h : length.val = 4 * count.val) :
    length / 4#usize = ok count := by
  obtain ⟨result, hrun, hval⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.div_spec length (y := 4#usize) (by norm_num))
  have heq : result = count := by
    apply UScalar.eq_of_val_eq
    rw [hval]
    norm_num
    rw [h]
    omega
  simpa [heq] using hrun

private theorem usize_rem_four_zero
    (length count : Std.Usize) (h : length.val = 4 * count.val) :
    length % 4#usize = ok 0#usize := by
  obtain ⟨result, hrun, hval⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.rem_spec length (y := 4#usize) (by norm_num))
  have heq : result = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [hval]
    norm_num
    rw [h]
    omega
  simpa [heq] using hrun

/-- The actual generated public packer is an order-preserving wrapper around
the already-proved generated row-value dispatcher.  This theorem includes the
three divide/remainder checks, runtime row-count calculation, allocation and
the complete generated loop; no serializer model is substituted for Rust. -/
theorem generated_public_packer_exact
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later0 later1 later2 : alloc.vec.Vec RawQM31)
    (finalCoefficients : Array RawQM31 4#usize)
    (count0 count1 count2 : Std.Usize)
    (hlen0 : later0.val.length = 4 * count0.val)
    (hlen1 : later1.val.length = 4 * count1.val)
    (hlen2 : later2.val.length = 4 * count2.val)
    (hcount0 : count0.val ≤ 18)
    (hcount1 : count1.val ≤ 18)
    (hcount2 : count2.val ≤ 18)
    (valueAt : Nat → RawQM31)
    (hlookup : ∀ row : Std.Usize,
      row.val < 40 + 4 * (count0.val + count1.val + count2.val) →
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
          oodValues polynomials
          (Array.make 3#usize [later0, later1, later2])
          finalCoefficients row = ok (some (valueAt row.val))) :
    ∃ output,
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          oodValues polynomials
          (Array.make 3#usize [later0, later1, later2])
          finalCoefficients = ok (core.result.Result.Ok output) ∧
      output.val =
        (List.range (40 + 4 * (count0.val + count1.val + count2.val))).map
          valueAt := by
  let later := Array.make 3#usize [later0, later1, later2]
  have hread0 : Array.index_usize later 0#usize = ok later0 := by
    exact array3_read_zero later0 later1 later2
  have hread1 : Array.index_usize later 1#usize = ok later1 := by
    exact array3_read_one later0 later1 later2
  have hread2 : Array.index_usize later 2#usize = ok later2 := by
    exact array3_read_two later0 later1 later2
  have hdiv0 : alloc.vec.Vec.len later0 / 4#usize = ok count0 := by
    apply usize_div_four_exact
    rw [vec_len_val, hlen0]
  have hdiv1 : alloc.vec.Vec.len later1 / 4#usize = ok count1 := by
    apply usize_div_four_exact
    rw [vec_len_val, hlen1]
  have hdiv2 : alloc.vec.Vec.len later2 / 4#usize = ok count2 := by
    apply usize_div_four_exact
    rw [vec_len_val, hlen2]
  have hrem0 : alloc.vec.Vec.len later0 % 4#usize = ok 0#usize := by
    apply usize_rem_four_zero (count := count0)
    rw [vec_len_val, hlen0]
  have hrem1 : alloc.vec.Vec.len later1 % 4#usize = ok 0#usize := by
    apply usize_rem_four_zero (count := count1)
    rw [vec_len_val, hlen1]
  have hrem2 : alloc.vec.Vec.len later2 % 4#usize = ok 0#usize := by
    apply usize_rem_four_zero (count := count2)
    rw [vec_len_val, hlen2]
  obtain ⟨rows, hrowsRun, hrowsValue⟩ :=
    generated_runtime_rows_exact count0 count1 count2
      hcount0 hcount1 hcount2
  let initial := alloc.vec.Vec.with_capacity RawQM31 rows
  have hinitial : initial.val = [] := by
    rfl
  have hcapacity : initial.val.length + rows.val ≤ Std.Usize.max := by
    rw [hinitial]
    simp only [List.length_nil, zero_add]
    have hrowBound := UScalar.hSize rows
    have hSizeEq : UScalar.size .Usize = Std.Usize.max + 1 := by
      simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
    rw [hSizeEq] at hrowBound
    omega
  have hlookupRows : ∀ row : Std.Usize, row.val < rows.val →
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
          oodValues polynomials later finalCoefficients row =
        ok (some (valueAt row.val)) := by
    intro row hrow
    apply hlookup row
    simpa [later, hrowsValue] using hrow
  obtain ⟨output, hloop, houtput⟩ :=
    generated_pack_loop_exact_output oodValues polynomials later
      finalCoefficients rows initial valueAt hlookupRows hcapacity
  refine ⟨output, ?_, ?_⟩
  · unfold v5_mask.component_c_runtime.pack_component_c_runtime_downstream
    rw [hread0]
    simp only [bind_tc_ok]
    rw [hdiv0]
    simp only [bind_tc_ok]
    rw [hread1]
    simp only [bind_tc_ok]
    rw [hdiv1]
    simp only [bind_tc_ok]
    rw [hread2]
    simp only [bind_tc_ok]
    rw [hdiv2]
    simp only [bind_tc_ok]
    rw [hrem0]
    simp only [bind_tc_ok]
    have hguard : ¬ ((0#usize != 0#usize) = true) := by norm_num
    rw [if_neg hguard]
    rw [hrem1]
    simp only [bind_tc_ok]
    rw [if_neg hguard]
    rw [hrem2]
    simp only [bind_tc_ok]
    rw [if_neg hguard]
    rw [hrowsRun]
    simpa [initial] using hloop
  · rw [houtput, hinitial, List.nil_append, hrowsValue]

#print axioms generated_public_packer_exact

section MaintainedOutput

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Exact arithmetic input expected by the packer bridge.  It names the real
generated `component_c_runtime_downstream_value_at` call at every accepted
runtime row and separately identifies the decoded value with the maintained
evaluator.  Thus it does not assume packer traversal, output length or output
ordering; those are conclusions below. -/
def GeneratedPackerRowsMatchDeployed
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec RawQM31) 3#usize)
    (finalCoefficients : Array RawQM31 4#usize) : Prop :=
  ∃ valueAt : Nat → RawQM31,
    (∀ row : Std.Usize, row.val < fRows (decodeFriSchedule rt) →
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
          oodValues polynomials later finalCoefficients row =
        ok (some (valueAt row.val))) ∧
    (∀ row : Fin (fRows (decodeFriSchedule rt)),
      view (valueAt row.val) = deployedEvaluate rt enc c row)

/-- End-to-end public-packer capstone.  Given the exact per-row arithmetic
facts, the authentic generated public wrapper returns precisely the maintained
runtime-sized view, with no missing row, padding row, or hidden permutation. -/
theorem generated_public_packer_matches_deployed
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later0 later1 later2 : alloc.vec.Vec RawQM31)
    (finalCoefficients : Array RawQM31 4#usize)
    (count0 count1 count2 : Std.Usize)
    (hlen0 : later0.val.length = 4 * count0.val)
    (hlen1 : later1.val.length = 4 * count1.val)
    (hlen2 : later2.val.length = 4 * count2.val)
    (hcount0 : count0.val ≤ 18)
    (hcount1 : count1.val ≤ 18)
    (hcount2 : count2.val ≤ 18)
    (hcount0Exact : count0.val = rt.later1Count)
    (hcount1Exact : count1.val = rt.later2Count)
    (hcount2Exact : count2.val = rt.later3Count)
    (hrows : GeneratedPackerRowsMatchDeployed rt enc c view
      oodValues polynomials
      (Array.make 3#usize [later0, later1, later2]) finalCoefficients) :
    ∃ output,
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          oodValues polynomials
          (Array.make 3#usize [later0, later1, later2])
          finalCoefficients = ok (core.result.Result.Ok output) ∧
      output.val.length = fRows (decodeFriSchedule rt) ∧
      ∀ row : Fin (fRows (decodeFriSchedule rt)),
        view output.val[row.val]! = deployedEvaluate rt enc c row := by
  rcases hrows with ⟨valueAt, hlookup, hview⟩
  have htotal :
      fRows (decodeFriSchedule rt) =
        40 + 4 * (count0.val + count1.val + count2.val) := by
    rw [deployed_output_dimension, hcount0Exact, hcount1Exact, hcount2Exact]
  have hlookupTotal : ∀ row : Std.Usize,
      row.val < 40 + 4 * (count0.val + count1.val + count2.val) →
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
          oodValues polynomials
          (Array.make 3#usize [later0, later1, later2])
          finalCoefficients row = ok (some (valueAt row.val)) := by
    intro row hrow
    apply hlookup row
    simpa [htotal] using hrow
  obtain ⟨output, hrun, houtput⟩ :=
    generated_public_packer_exact oodValues polynomials later0 later1 later2
      finalCoefficients count0 count1 count2 hlen0 hlen1 hlen2
      hcount0 hcount1 hcount2 valueAt hlookupTotal
  refine ⟨output, hrun, ?_, ?_⟩
  · rw [houtput]
    simp [htotal]
  · intro row
    rw [houtput]
    have hrowBound :
        row.val < 40 + 4 * (count0.val + count1.val + count2.val) := by
      rw [← htotal]
      exact row.isLt
    have hrange :
        (List.range (40 + 4 * (count0.val + count1.val + count2.val)))[row.val]? =
          some row.val := by
      simp [hrowBound]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, hrange]
    exact hview row

#print axioms generated_public_packer_matches_deployed

/-- Identification form used by the private-view control-flow theorem: if a
successful generated execution already returned `output`, the public packer
capstone identifies that very vector—not merely some extensionally equal
witness—with the maintained deployed view. -/
theorem generated_successful_pack_output_matches_deployed
    (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (c : CWord K)
    (view : RawQM31 → K)
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later0 later1 later2 : alloc.vec.Vec RawQM31)
    (finalCoefficients : Array RawQM31 4#usize)
    (count0 count1 count2 : Std.Usize)
    (output : alloc.vec.Vec RawQM31)
    (hpack :
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream
          oodValues polynomials
          (Array.make 3#usize [later0, later1, later2])
          finalCoefficients = ok (core.result.Result.Ok output))
    (hlen0 : later0.val.length = 4 * count0.val)
    (hlen1 : later1.val.length = 4 * count1.val)
    (hlen2 : later2.val.length = 4 * count2.val)
    (hcount0 : count0.val ≤ 18)
    (hcount1 : count1.val ≤ 18)
    (hcount2 : count2.val ≤ 18)
    (hcount0Exact : count0.val = rt.later1Count)
    (hcount1Exact : count1.val = rt.later2Count)
    (hcount2Exact : count2.val = rt.later3Count)
    (hrows : GeneratedPackerRowsMatchDeployed rt enc c view
      oodValues polynomials
      (Array.make 3#usize [later0, later1, later2]) finalCoefficients) :
    output.val.length = fRows (decodeFriSchedule rt) ∧
    ∀ row : Fin (fRows (decodeFriSchedule rt)),
      view output.val[row.val]! = deployedEvaluate rt enc c row := by
  obtain ⟨expected, hpackExpected, hlength, hcoordinates⟩ :=
    generated_public_packer_matches_deployed rt enc c view oodValues
      polynomials later0 later1 later2 finalCoefficients
      count0 count1 count2 hlen0 hlen1 hlen2 hcount0 hcount1 hcount2
      hcount0Exact hcount1Exact hcount2Exact hrows
  have hsame : output = expected := by
    rw [hpack] at hpackExpected
    cases hpackExpected
    rfl
  subst expected
  exact ⟨hlength, hcoordinates⟩

#print axioms generated_successful_pack_output_matches_deployed

end MaintainedOutput

end aspis_prover.ComponentCRuntimePackerMaintainedOutput
