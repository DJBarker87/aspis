import RuntimePackerCorrespondence
import Aeneas.Tactic.Step.StepStar

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimePackerFullCorrespondence

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31

private def packedPrefix (valueAt : Nat → RawQM31) (count : Nat) :
    List RawQM31 :=
  (List.range count).map valueAt

private theorem packedPrefix_succ (valueAt : Nat → RawQM31) (count : Nat) :
    packedPrefix valueAt (count + 1) =
      packedPrefix valueAt count ++ [valueAt count] := by
  simp [packedPrefix, List.range_succ]

private def PackLoopInvariant
    (valueAt : Nat → RawQM31) (rows : Std.Usize)
    (initial : alloc.vec.Vec RawQM31)
    (state : alloc.vec.Vec RawQM31 × Std.Usize) : Prop :=
  state.2.val ≤ rows.val ∧
  state.1.val = initial.val ++ packedPrefix valueAt state.2.val

private def PackLoopPost
    (valueAt : Nat → RawQM31) (rows : Std.Usize)
    (initial : alloc.vec.Vec RawQM31)
    (result : core.result.Result (alloc.vec.Vec RawQM31)
      v5_mask.component_c_runtime.V5ComponentCRuntimeError) : Prop :=
  ∃ output,
    result = core.result.Result.Ok output ∧
    output.val = initial.val ++ packedPrefix valueAt rows.val

/-- The actual extracted packing loop is an order-preserving traversal of
every runtime row.  Its only semantic input is the already-proved row-value
dispatcher; no fixed 256-row layout is assumed. -/
theorem generated_pack_loop_exact
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec RawQM31) 3#usize)
    (finalCoefficients : Array RawQM31 4#usize)
    (rows : Std.Usize) (initial : alloc.vec.Vec RawQM31)
    (valueAt : Nat → RawQM31)
    (hlookup : ∀ row : Std.Usize, row.val < rows.val →
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
          oodValues polynomials later finalCoefficients row =
        ok (some (valueAt row.val)))
    (hcapacity : initial.val.length + rows.val ≤ Std.Usize.max) :
    v5_mask.component_c_runtime.pack_component_c_runtime_downstream_loop
        oodValues polynomials later finalCoefficients rows initial 0#usize
      ⦃ result => PackLoopPost valueAt rows initial result ⦄ := by
  unfold v5_mask.component_c_runtime.pack_component_c_runtime_downstream_loop
  apply loop.spec_decr_nat
    (fun state : alloc.vec.Vec RawQM31 × Std.Usize =>
      rows.val - state.2.val)
    (PackLoopInvariant valueAt rows initial)
    (PackLoopPost valueAt rows initial)
  · rintro ⟨output, row⟩ ⟨hrowBound, houtput⟩
    dsimp only at hrowBound houtput ⊢
    change row.val ≤ rows.val at hrowBound
    change output.val = initial.val ++ packedPrefix valueAt row.val at houtput
    unfold v5_mask.component_c_runtime.pack_component_c_runtime_downstream_loop.body
    by_cases hactive : row.val < rows.val
    · have hactiveScalar : row < rows := by scalar_tac
      rw [if_pos hactiveScalar, hlookup row hactive]
      simp only [bind_tc_ok]
      have houtputLength : output.val.length < Std.Usize.max := by
        rw [houtput, List.length_append]
        simp [packedPrefix]
        omega
      step as ⟨outputAfter, houtputAfter⟩
      step as ⟨rowAfter, hrowAfter⟩
      have hrowAfterVal : rowAfter.val = row.val + 1 := by
        rw [hrowAfter, Std.Usize.wrapping_add_val_eq]
        apply Nat.mod_eq_of_lt
        have hrowsSize := UScalar.hSize rows
        norm_num at hrowsSize ⊢
        omega
      change
        (PackLoopInvariant valueAt rows initial (outputAfter, rowAfter) ∧
          rows.val - rowAfter.val < rows.val - row.val)
      constructor
      · constructor
        · rw [hrowAfterVal]
          omega
        · change outputAfter.val = _
          rw [houtputAfter, houtput, hrowAfterVal, packedPrefix_succ]
          simp only [List.append_assoc]
      · rw [hrowAfterVal]
        omega
    · have hdone : row.val = rows.val := by omega
      have hnotActive : ¬ row < rows := by scalar_tac
      rw [if_neg hnotActive]
      change PackLoopPost valueAt rows initial
        (core.result.Result.Ok output)
      refine ⟨output, rfl, ?_⟩
      simpa [hdone] using houtput
  · constructor
    · norm_num
    · simp [packedPrefix]

#print axioms generated_pack_loop_exact

/-- Explicit-result form of `generated_pack_loop_exact`, exported for the
public packer/output bridge. -/
theorem generated_pack_loop_exact_output
    (oodValues : Array (Array RawQM31 2#usize) 4#usize)
    (polynomials : Array (Array RawQM31 7#usize) 4#usize)
    (later : Array (alloc.vec.Vec RawQM31) 3#usize)
    (finalCoefficients : Array RawQM31 4#usize)
    (rows : Std.Usize) (initial : alloc.vec.Vec RawQM31)
    (valueAt : Nat → RawQM31)
    (hlookup : ∀ row : Std.Usize, row.val < rows.val →
      v5_mask.component_c_runtime.component_c_runtime_downstream_value_at
          oodValues polynomials later finalCoefficients row =
        ok (some (valueAt row.val)))
    (hcapacity : initial.val.length + rows.val ≤ Std.Usize.max) :
    ∃ output,
      v5_mask.component_c_runtime.pack_component_c_runtime_downstream_loop
          oodValues polynomials later finalCoefficients rows initial 0#usize =
        ok (core.result.Result.Ok output) ∧
      output.val = initial.val ++ (List.range rows.val).map valueAt := by
  obtain ⟨result, hrun, hpost⟩ := Aeneas.Std.WP.spec_imp_exists
    (generated_pack_loop_exact oodValues polynomials later finalCoefficients
      rows initial valueAt hlookup hcapacity)
  rcases hpost with ⟨output, hresult, houtput⟩
  subst result
  exact ⟨output, hrun, by simpa [packedPrefix] using houtput⟩

#print axioms generated_pack_loop_exact_output

end aspis_prover.ComponentCRuntimePackerFullCorrespondence
