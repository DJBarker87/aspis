import ComponentCRuntimeGenerated
import Aeneas.Tactic.Step.StepStar

set_option autoImplicit false

/-!
# Source-authentic Component-C later-fibre release

The runtime prover releases four consecutive values for each deduplicated
later-layer fibre.  This file proves the exact four-slot order directly about
the Charon/Aeneas extraction.  It is intentionally independent of the relation
accumulator and of the field interpretation: this part of the wire is pure
indexing.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimeLaterFibreProof

open aspis_prover

abbrev RawQM31 := aspis_core.field.QM31

deriving instance Inhabited for aspis_core.field.CM31
deriving instance Inhabited for aspis_core.field.QM31

def releasedPrefix (folded : Slice RawQM31) (start count : Nat) : List RawQM31 :=
  (List.range count).map fun slot => folded.val[start + slot]!

private theorem usize_small_add_val
    (left right : Std.Usize)
    (h : left.val + right.val < Std.Usize.size) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [Usize.size] using h

private def AppendLoopInvariant
    (folded : Slice RawQM31) (initial : alloc.vec.Vec RawQM31)
    (start : Std.Usize)
    (state : alloc.vec.Vec RawQM31 × Std.Usize) : Prop :=
  state.2.val ≤ 4 ∧
  state.1.val = initial.val ++ releasedPrefix folded start.val state.2.val

private def AppendLoopPost
    (folded : Slice RawQM31) (initial : alloc.vec.Vec RawQM31)
    (start : Std.Usize) (out : alloc.vec.Vec RawQM31) : Prop :=
  out.val = initial.val ++ releasedPrefix folded start.val 4

/-- The generated fixed-four loop appends exactly slots `start + 0..3`, in
that order.  The two bounds are precisely the source conditions needed for the
four slice reads and four vector pushes. -/
theorem extracted_append_loop_exact
    (folded : Slice RawQM31) (initial : alloc.vec.Vec RawQM31)
    (start : Std.Usize)
    (hread : start.val + 4 ≤ folded.val.length)
    (hcapacity : initial.val.length + 4 ≤ Std.Usize.max) :
    v5_mask.component_c_runtime.append_component_c_runtime_later_fibre_loop
        folded initial start 0#usize
      ⦃ out => AppendLoopPost folded initial start out ⦄ := by
  unfold v5_mask.component_c_runtime.append_component_c_runtime_later_fibre_loop
  apply loop.spec_decr_nat
    (fun state => 4 - state.2.val)
    (AppendLoopInvariant folded initial start)
    (AppendLoopPost folded initial start)
  · rintro ⟨target, slot⟩ ⟨hslot, htarget⟩
    change slot.val ≤ 4 at hslot
    change target.val =
      initial.val ++ releasedPrefix folded start.val slot.val at htarget
    unfold v5_mask.component_c_runtime.append_component_c_runtime_later_fibre_loop.body
    by_cases hactive : slot.val < 4
    · have hslotScalar : slot < 4#usize := by scalar_tac
      have hstartSlot : start.val + slot.val < folded.val.length := by omega
      have hUsizeSize : Std.Usize.size = Std.Usize.max + 1 := by
        simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
      have hstartSlotSize : start.val + slot.val < Std.Usize.size := by
        rw [hUsizeSize]
        have hfoldedMax := folded.property
        omega
      have hslotSuccSize : slot.val + 1 < Std.Usize.size := by
        rw [hUsizeSize]
        scalar_tac
      have hstartAdd := usize_small_add_val start slot hstartSlotSize
      have hslotAdd := usize_small_add_val slot 1#usize hslotSuccSize
      have htargetLength : target.val.length < Std.Usize.max := by
        rw [htarget]
        simp only [List.length_append]
        simp [releasedPrefix]
        omega
      step*
      change
        (slot1.val ≤ 4 ∧
          target1.val = initial.val ++
            releasedPrefix folded start.val slot1.val) ∧
          4 - slot1.val < 4 - slot.val
      have hiVal : i.val = start.val + slot.val := by
        rw [i_post, hstartAdd]
      have hq : q = folded.val[start.val + slot.val] := by
        simpa [hiVal] using q_post
      have hslot1Val : slot1.val = slot.val + 1 := by
        rw [slot1_post, hslotAdd]
        rfl
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hslot1Val]
      rw [target1_post, htarget, hq]
      simp only [releasedPrefix]
      rw [show slot.val + 1 = Nat.succ slot.val by omega,
        List.range_succ, List.map_append]
      simp [hstartSlot]
    · have hdone : slot.val = 4 := by omega
      have hslotEq : slot = 4#usize := by
        apply UScalar.val_eq_imp
        simpa using hdone
      subst slot
      step*
      simpa [AppendLoopPost] using htarget
  · constructor
    · simp
    · simp [releasedPrefix]

/-- The actual extracted public helper succeeds on every in-range runtime
fibre and releases exactly its four consecutive slots.  This includes the
`u32 -> usize` cast, checked multiply/add, layer-tag conversion, bounds check,
and the fixed-four append loop. -/
theorem extracted_append_fibre_exact
    (folded : Slice RawQM31) (initial : alloc.vec.Vec RawQM31)
    (layer : Std.Usize) (fibre : Std.U32)
    (hread : 4 * fibre.val + 4 ≤ folded.val.length)
    (hcapacity : initial.val.length + 4 ≤ Std.Usize.max) :
    v5_mask.component_c_runtime.append_component_c_runtime_later_fibre
        folded initial layer fibre
      ⦃ result =>
        result.1 = core.result.Result.Ok () ∧
        result.2.val =
          initial.val ++ releasedPrefix folded (4 * fibre.val) 4 ⦄ := by
  unfold v5_mask.component_c_runtime.append_component_c_runtime_later_fibre
  step*
  have hi : i.val = fibre.val := by
    rw [i_post]
    exact U32.cast_Usize_val_eq fibre
  cases o with
  | none =>
      simp only at o_post
      have hfoldedMax := folded.property
      omega
  | some start =>
      simp only at o_post
      rcases o_post with ⟨_hstartFits, hstart, _hstartBv⟩
      simp only [core.option.Option.ok_or, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
      step*
      cases o1 with
      | none =>
          simp only at o1_post
          have hfoldedMax := folded.property
          omega
      | some finish =>
          simp only at o1_post
          rcases o1_post with ⟨_hfinishFits, hfinish, _hfinishBv⟩
          simp only [bind_tc_ok]
          have hnotPast : ¬ finish > Slice.len folded := by
            intro hpast
            have hlen : (Slice.len folded).val = folded.val.length := by simp
            have hfinishVal : finish.val = 4 * fibre.val + 4 := by
              rw [hfinish, hstart, hi]
            scalar_tac
          rw [if_neg hnotPast]
          have hloop := extracted_append_loop_exact folded initial start
            (by rw [hstart, hi]; exact hread) hcapacity
          obtain ⟨out, hrun, hout⟩ := Aeneas.Std.WP.spec_imp_exists hloop
          rw [hrun]
          simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, true_and]
          unfold AppendLoopPost at hout
          rw [hout, hstart, hi]

#print axioms extracted_append_loop_exact
#print axioms extracted_append_fibre_exact

end aspis_prover.ComponentCRuntimeLaterFibreProof
