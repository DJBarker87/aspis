import ComponentBLayoutBindingsGenerated
import AspisFormal.V5CompactTerminal
import Aeneas.Tactic.Step.StepStar
import Aeneas.Tactic.Solver.ScalarDecrTac

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators QuadraticAlgebra

namespace ComponentBLayoutBindingsProof

open ComponentBGenerated
open AspisV5CompactTerminal

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev ExactQM31 := ComponentBRealEvaluatorProof.ExactQM31

instance exactRootlessInstance : Fact
    (∀ z : ComponentBRealEvaluatorProof.ExactCM31,
      z ^ 2 ≠ ComponentBRealEvaluatorProof.exactQm31R + 0 * z) := by
  change Fact
    (∀ z : AspisV5ComponentCQM31TowerExact.CM31Exact,
      z ^ 2 ≠ AspisV5ComponentCQM31TowerExact.qm31R + 0 * z)
  infer_instance

noncomputable instance exactFieldInstance : Field ExactQM31 := by
  infer_instance

local instance : Inhabited QM31 :=
  ⟨ComponentBGenerated.aspis_core.field.QM31.ZERO⟩

def CanonicalVec (values : alloc.vec.Vec QM31) : Prop :=
  ∀ index : Nat, index < values.length →
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 values.val[index]!

def exactVecAt (values : alloc.vec.Vec QM31) (index : Nat) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact values.val[index]!

def CanonicalArray {n : Std.Usize} (values : Array QM31 n) : Prop :=
  ∀ index : Nat, index < n.val →
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 values.val[index]!

def exactArrayAt {n : Std.Usize} (values : Array QM31 n)
    (index : Nat) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact values.val[index]!

theorem generated_ZERO_canonical :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
      ComponentBGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
    ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus,
    ComponentBGenerated.aspis_core.field.QM31.ZERO]

theorem generated_ZERO_exact :
    ComponentBRealEvaluatorProof.generatedQm31ToExact
      ComponentBGenerated.aspis_core.field.QM31.ZERO = (0 : ExactQM31) := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [ComponentBRealEvaluatorProof.generatedQm31ToExact,
        ComponentBRealEvaluatorProof.generatedCm31ToExact,
        ComponentBGenerated.aspis_core.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;>
      simp [ComponentBRealEvaluatorProof.generatedQm31ToExact,
        ComponentBRealEvaluatorProof.generatedCm31ToExact,
        ComponentBGenerated.aspis_core.field.QM31.ZERO]

theorem generated_ONE_canonical :
    ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
      ComponentBGenerated.aspis_core.field.QM31.ONE := by
  norm_num [ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
    ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus,
    ComponentBGenerated.aspis_core.field.QM31.ONE]

theorem generated_ONE_exact :
    ComponentBRealEvaluatorProof.generatedQm31ToExact
      ComponentBGenerated.aspis_core.field.QM31.ONE = (1 : ExactQM31) := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [ComponentBRealEvaluatorProof.generatedQm31ToExact,
        ComponentBRealEvaluatorProof.generatedCm31ToExact,
        ComponentBGenerated.aspis_core.field.QM31.ONE]
  · apply QuadraticAlgebra.ext <;>
      simp [ComponentBRealEvaluatorProof.generatedQm31ToExact,
        ComponentBRealEvaluatorProof.generatedCm31ToExact,
        ComponentBGenerated.aspis_core.field.QM31.ONE]

private theorem generated_ZERO_clone :
    ComponentBGenerated.aspis_core.field.QM31.Insts.CoreCloneClone.clone
        ComponentBGenerated.aspis_core.field.QM31.ZERO =
      ok ComponentBGenerated.aspis_core.field.QM31.ZERO := by
  rfl

private theorem generated_zero_vec_exists (n : Std.Usize) :
    ∃ values,
      alloc.vec.from_elem
          ComponentBGenerated.aspis_core.field.QM31.Insts.CoreCloneClone
          ComponentBGenerated.aspis_core.field.QM31.ZERO n = ok values ∧
      values.val = List.replicate n.val
        ComponentBGenerated.aspis_core.field.QM31.ZERO ∧
      values.length = n.val := by
  exact WP.spec_imp_exists (alloc.vec.from_elem_spec
    ComponentBGenerated.aspis_core.field.QM31.Insts.CoreCloneClone
    ComponentBGenerated.aspis_core.field.QM31.ZERO n generated_ZERO_clone)

private theorem generated_zero_replicate_getElemBang (n index : Nat) :
    (List.replicate n
      ComponentBGenerated.aspis_core.field.QM31.ZERO)[index]! =
        ComponentBGenerated.aspis_core.field.QM31.ZERO := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

private theorem generated_trace_rows_eq :
    ComponentBGenerated.v5_mask.V5_TRACE_ROWS = 1024#usize := by
  norm_num [ComponentBGenerated.v5_mask.V5_TRACE_ROWS]

private theorem exact_one_mul (value : ExactQM31) :
    (1 : ExactQM31) * value = value := one_mul value

private theorem exact_eq_one_mul (value : ExactQM31) :
    value = (1 : ExactQM31) * value := (one_mul value).symm

private theorem eq_one_mul_of_eq {left value : ExactQM31}
    (equal : left = value) : left = (1 : ExactQM31) * value :=
  equal.trans (exact_eq_one_mul value)

private theorem exact_zero_add_sum_zero {I : Type} [Fintype I] :
    (0 : ExactQM31) + (∑ _index : I, (0 : ExactQM31)) = 0 := by
  rw [Finset.sum_const_zero, add_zero]

theorem wrapping_add_val_of_lt (left right : Std.Usize)
    (h : left.val + right.val < Usize.size) :
    (left.wrapping_add right).val = left.val + right.val := by
  simp only [Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

private theorem wrapping_add_one_val (value : Std.Usize)
    (hvalue : value.val < 1024) :
    (value.wrapping_add 1#usize).val = value.val + 1 := by
  apply wrapping_add_val_of_lt
  have hsize : 1025 < Usize.size := by
    simpa using UScalar.hSize (1025#usize)
  norm_num
  omega

private theorem wrapping_sub_one_val (value : Std.Usize)
    (hvalue : 1 ≤ value.val) :
    (value.wrapping_sub 1#usize).val = value.val - 1 := by
  simp only [Usize.wrapping_sub_val_eq]
  norm_num
  have hsize : value.val < Usize.size := by
    simpa only [UScalar.size_UScalarTyUsize] using value.hSize
  have hreorder : value.val + (Usize.size - 1) =
      (value.val - 1) + Usize.size := by omega
  rw [hreorder, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem vec_set_get_same
    (values : alloc.vec.Vec QM31) (index : Std.Usize) (value : QM31)
    (hIndex : index.val < values.length) :
    (values.set index value).val[index.val]! = value := by
  simp only [alloc.vec.Vec.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨hIndex, rfl⟩

private theorem vec_set_get_ne
    (values : alloc.vec.Vec QM31) (index : Std.Usize) (value : QM31)
    (other : Nat) (hNe : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

private theorem canonicalVec_set
    (values : alloc.vec.Vec QM31) (index : Std.Usize) (value : QM31)
    (hIndex : index.val < values.length)
    (hValues : CanonicalVec values)
    (hValue : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 value) :
    CanonicalVec (values.set index value) := by
  intro other hOther
  by_cases hSame : other = index.val
  · subst other
    rw [vec_set_get_same values index value hIndex]
    exact hValue
  · rw [vec_set_get_ne values index value other hSame]
    exact hValues other (by simpa using hOther)

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

private theorem vec_index_usize_run
    (values : alloc.vec.Vec QM31) (index : Std.Usize)
    (hIndex : index.val < values.length) :
    values.index_usize index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hIndex)
  rw [hRun]
  congr
  rw [hValue]
  exact list_get_eq_getElemBang values.val index.val (by
    simpa using hIndex)

private theorem array_index_usize_run
    {T : Type} [Inhabited T] {n : Std.Usize}
    (values : Array T n) (index : Std.Usize)
    (hIndex : index.val < n.val) :
    values.index_usize index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  rw [hRun]
  congr
  rw [hValue]
  exact list_get_eq_getElemBang values.val index.val (by
    simpa [Array.length_eq] using hIndex)

theorem array_repeat_get_bang
    {T : Type} [Inhabited T] (n : Std.Usize) (value : T)
    (index : Nat) (hindex : index < n.val) :
    (Array.repeat n value).val[index]! = value := by
  change (List.replicate n.val value)[index]! = value
  rw [← list_get_eq_getElemBang (List.replicate n.val value) index (by
    simpa using hindex)]
  simp

private theorem wrapping_mul_val_of_lt (left right : Std.Usize)
    (h : left.val * right.val < Usize.size) :
    (left.wrapping_mul right).val = left.val * right.val := by
  simp only [Usize.wrapping_mul_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

private theorem wrapping_sub_val_of_le (left right : Std.Usize)
    (hle : right.val ≤ left.val) :
    (left.wrapping_sub right).val = left.val - right.val := by
  simp only [Usize.wrapping_sub_val_eq]
  have hleft : left.val < Usize.size := by
    simpa only [UScalar.size_UScalarTyUsize] using left.hSize
  have hright : right.val < Usize.size := by
    simpa only [UScalar.size_UScalarTyUsize] using right.hSize
  have hreorder : left.val + (Usize.size - right.val) =
      (left.val - right.val) + Usize.size := by omega
  have hreorder' : left.val +
      (UScalar.size UScalarTy.Usize - right.val) =
      (left.val - right.val) + UScalar.size UScalarTy.Usize := by
    simpa only [UScalar.size_UScalarTyUsize] using hreorder
  rw [hreorder', Nat.add_mod_right]
  have hdiff : left.val - right.val < Usize.size := by omega
  exact Nat.mod_eq_of_lt (by
    simpa only [UScalar.size_UScalarTyUsize] using hdiff)

theorem generated_round_block_value
    (round : Fin 10) :
    (ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS.val[
      round.val]!).val = blockSelector round := by
  fin_cases round <;>
    norm_num [ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS,
      blockSelector, Array.make]

theorem array_set_get_same
    {n : Std.Usize} (values : Array QM31 n) (index : Std.Usize)
    (value : QM31) (hIndex : index.val < n.val) :
    (values.set index value).val[index.val]! = value := by
  simp only [Array.set_val_eq]
  apply List.set_getElem!_eq
  exact ⟨by simpa [Array.length_eq] using hIndex, rfl⟩

theorem array_set_get_ne
    {n : Std.Usize} (values : Array QM31 n) (index : Std.Usize)
    (value : QM31) (other : Nat) (hNe : other ≠ index.val) :
    (values.set index value).val[other]! = values.val[other]! := by
  apply List.set_getElem!_ne
  omega

theorem canonicalArray_set
    {n : Std.Usize} (values : Array QM31 n) (index : Std.Usize)
    (value : QM31) (hIndex : index.val < n.val)
    (hValues : CanonicalArray values)
    (hValue : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 value) :
    CanonicalArray (values.set index value) := by
  intro other hOther
  by_cases hSame : other = index.val
  · subst other
    rw [array_set_get_same values index value hIndex]
    exact hValue
  · rw [array_set_get_ne values index value other hSame]
    exact hValues other hOther

private theorem generated_mul_spec
    (left right : QM31)
    (hleft : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 left)
    (hright : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 right) :
    ComponentBGenerated.aspis_core.field.QM31.mul left right ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        ComponentBRealEvaluatorProof.generatedQm31ToExact left *
          ComponentBRealEvaluatorProof.generatedQm31ToExact right ⦄ := by
  obtain ⟨out, run, canonical, exact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_mul_corresponds
      left right hleft hright
  rw [run]
  exact ⟨canonical, exact⟩

private def HalfPowerPrefix (halfExact : ExactQM31)
    (values : Array QM31 11#usize) (exponent : Std.Usize) : Prop :=
  CanonicalArray values ∧ 1 ≤ exponent.val ∧ exponent.val ≤ 11 ∧
    ∀ index : Nat, index < 11 →
      exactArrayAt values index =
        if index < exponent.val then halfExact ^ index else 1

private theorem terminal_half_power_loop_spec
    (half : QM31) (halfExact : ExactQM31)
    (values : Array QM31 11#usize) (exponent : Std.Usize)
    (hhalf : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 half)
    (hhalfExact :
      ComponentBRealEvaluatorProof.generatedQm31ToExact half = halfExact)
    (hprefix : HalfPowerPrefix halfExact values exponent) :
    ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0
        half values exponent ⦃ out =>
      CanonicalArray out ∧
      ∀ index : Nat, index < 11 →
        exactArrayAt out index = halfExact ^ index ⦄ := by
  simp only [ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0]
  apply loop.spec_decr_nat
    (fun state => 11 - state.2.val)
    (fun state => HalfPowerPrefix halfExact state.1 state.2)
    (fun out => CanonicalArray out ∧
      ∀ index : Nat, index < 11 →
        exactArrayAt out index = halfExact ^ index)
  · rintro ⟨current, currentExponent⟩ hcurrent
    rcases hcurrent with
      ⟨hcurrentCanonical, hcurrentOne, hcurrentBound, hcurrentExact⟩
    simp only at hcurrentCanonical hcurrentOne hcurrentBound hcurrentExact
    unfold ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0.body
    simp only [lift, bind_tc_ok]
    have hlen : Slice.len (Array.to_slice current) = 11#usize := by
      apply UScalar.eq_of_val_eq
      simp
    rw [hlen]
    by_cases hlt : currentExponent < 11#usize
    · rw [if_pos hlt]
      have hexponentLt : currentExponent.val < 11 := hlt
      have hpreviousVal := wrapping_sub_one_val currentExponent hcurrentOne
      have hpreviousBound :
          (currentExponent.wrapping_sub 1#usize).val < (11#usize).val := by
        rw [hpreviousVal]
        norm_num
        omega
      have hread := Array.index_usize_spec current
        (currentExponent.wrapping_sub 1#usize) (by
          simpa [Array.length_eq] using hpreviousBound)
      obtain ⟨previous, previousRun, previousEq⟩ := WP.spec_imp_exists hread
      rw [previousRun]
      simp only [bind_tc_ok]
      have hpreviousCanonical :
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 previous := by
        rw [previousEq]
        rw [list_get_eq_getElemBang current.val _ (by
          simpa [Array.length_eq] using hpreviousBound)]
        exact hcurrentCanonical _ hpreviousBound
      have hproduct := generated_mul_spec previous half
        hpreviousCanonical hhalf
      obtain ⟨product, productRun, productCanonical, productExact⟩ :=
        WP.spec_imp_exists hproduct
      rw [productRun]
      simp only [bind_tc_ok]
      have hupdate := Array.update_spec current currentExponent product (by
        simpa [Array.length_eq] using hexponentLt)
      obtain ⟨updated, updatedRun, updatedEq⟩ := WP.spec_imp_exists hupdate
      rw [updatedRun]
      simp only [bind_tc_ok]
      subst updated
      have hnextVal := wrapping_add_one_val currentExponent (by omega)
      simp only [WP.spec, WP.theta]
      refine ⟨?_, ?_⟩
      · unfold HalfPowerPrefix
        refine ⟨canonicalArray_set current currentExponent product
          hexponentLt hcurrentCanonical productCanonical, ?_, ?_, ?_⟩
        · rw [hnextVal]
          omega
        · rw [hnextVal]
          omega
        · intro index hindex
          simp only [Prod.fst, Prod.snd]
          by_cases hsame : index = currentExponent.val
          · subst index
            unfold exactArrayAt
            rw [array_set_get_same current currentExponent product hexponentLt]
            have hpreviousExact := hcurrentExact
              (currentExponent.wrapping_sub 1#usize).val (by
                simpa using hpreviousBound)
            rw [if_pos (by rw [hpreviousVal]; omega)] at hpreviousExact
            have previousBang :
                current.val[(currentExponent.wrapping_sub 1#usize).val]! =
                  previous := by
              rw [previousEq]
              exact (list_get_eq_getElemBang current.val _ (by
                simpa [Array.length_eq] using hpreviousBound)).symm
            unfold exactArrayAt at hpreviousExact
            rw [previousBang, hpreviousVal] at hpreviousExact
            rw [productExact, hpreviousExact, hhalfExact]
            rw [hnextVal, if_pos (by omega)]
            conv_rhs =>
              rw [show currentExponent.val =
                (currentExponent.val - 1) + 1 by omega, pow_succ']
            exact mul_comm _ _
          · unfold exactArrayAt
            rw [array_set_get_ne current currentExponent product index hsame]
            change exactArrayAt current index = _
            rw [hcurrentExact index hindex]
            by_cases hbefore : index < currentExponent.val
            · rw [if_pos hbefore, if_pos (by rw [hnextVal]; omega)]
            · rw [if_neg hbefore, if_neg (by rw [hnextVal]; omega)]
      · rw [hnextVal]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta]
      have heq : currentExponent.val = 11 := by
        have hnot : ¬ currentExponent.val < 11 := hlt
        omega
      exact ⟨hcurrentCanonical, fun index hindex => by
        rw [hcurrentExact index hindex, if_pos (by omega)]⟩
  · exact hprefix

/-- For one fixed target degree, the authentic inner terminal-covector loop
overwrites exactly that target with `scale * challenge ^ degree`.  This is a
query-specific loop invariant, so it does not assume a dense-vector equality. -/
private theorem terminal_inner_target_spec
    (covector : alloc.vec.Vec QM31)
    (challenge scale power : QM31)
    (start offset : Std.Usize) (target : Fin 28)
    (baseline : ExactQM31)
    (hlength : covector.length = 1024)
    (hstart : start.val + 28 ≤ 1024)
    (hoffset : offset.val ≤ 28)
    (hcovector : CanonicalVec covector)
    (hchallenge : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge)
    (hscale : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 scale)
    (hpower : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 power)
    (hpowerExact :
      ComponentBRealEvaluatorProof.generatedQm31ToExact power =
        ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ offset.val)
    (htarget :
      exactVecAt covector (start.val + target.val) =
        if offset.val ≤ target.val then baseline
        else ComponentBRealEvaluatorProof.generatedQm31ToExact scale *
          ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ target.val) :
    ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0
        covector challenge scale start power offset ⦃ out =>
      out.length = 1024 ∧ CanonicalVec out ∧
      exactVecAt out (start.val + target.val) =
        ComponentBRealEvaluatorProof.generatedQm31ToExact scale *
          ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ target.val ⦄ := by
  simp only [ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0]
  apply loop.spec_decr_nat
    (fun state => 28 - state.2.2.val)
    (fun state =>
      state.1.length = 1024 ∧ state.2.2.val ≤ 28 ∧ CanonicalVec state.1 ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 state.2.1 ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact state.2.1 =
        ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ state.2.2.val ∧
      exactVecAt state.1 (start.val + target.val) =
        if state.2.2.val ≤ target.val then baseline
        else ComponentBRealEvaluatorProof.generatedQm31ToExact scale *
          ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ target.val)
    (fun out => out.length = 1024 ∧ CanonicalVec out ∧
      exactVecAt out (start.val + target.val) =
        ComponentBRealEvaluatorProof.generatedQm31ToExact scale *
          ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ target.val)
  · rintro ⟨current, currentPower, currentOffset⟩
      ⟨hcurrentLength, hcurrentOffset, hcurrentCanonical, hcurrentPower,
        hcurrentPowerExact, hcurrentTarget⟩
    simp only [Prod.fst, Prod.snd] at hcurrentLength hcurrentOffset hcurrentCanonical hcurrentPower hcurrentPowerExact hcurrentTarget
    unfold ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0.body
    simp only [ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS]
    by_cases hlt : currentOffset < 28#usize
    · rw [if_pos hlt]
      have hoffsetLt : currentOffset.val < 28 := by exact hlt
      have hsize : 1025 < Usize.size := by
        simpa using UScalar.hSize (1025#usize)
      have hsum : start.val + currentOffset.val < Usize.size := by omega
      have hindexVal := wrapping_add_val_of_lt start currentOffset hsum
      have hindexBound : (start.wrapping_add currentOffset).val < current.length := by
        rw [hcurrentLength, hindexVal]
        omega
      have hq := generated_mul_spec scale currentPower hscale hcurrentPower
      obtain ⟨qOut, qRun, qCanonical, qExact⟩ := WP.spec_imp_exists hq
      rw [qRun]
      simp only [bind_tc_ok, lift]
      rw [alloc.vec.Vec.index_mut_slice_index]
      unfold alloc.vec.Vec.index_mut_usize
      rw [vec_index_usize_run current
        (start.wrapping_add currentOffset) hindexBound]
      simp only [bind_tc_ok]
      have hp := generated_mul_spec currentPower challenge
        hcurrentPower hchallenge
      obtain ⟨powerOut, powerRun, powerCanonical, powerExact⟩ :=
        WP.spec_imp_exists hp
      rw [powerRun]
      simp only [bind_tc_ok]
      let next := current.set (start.wrapping_add currentOffset) qOut
      have hnextOffset := wrapping_add_one_val currentOffset (by omega)
      have hnextCanonical : CanonicalVec next :=
        canonicalVec_set current (start.wrapping_add currentOffset) qOut
          hindexBound hcurrentCanonical qCanonical
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [next] using hcurrentLength
      · rw [hnextOffset]
        omega
      · exact hnextCanonical
      · exact powerCanonical
      · rw [powerExact, hcurrentPowerExact, hnextOffset, pow_succ]
      · simp only [Prod.fst, Prod.snd]
        by_cases hsame : target.val = currentOffset.val
        · have hrow : start.val + target.val =
              (start.wrapping_add currentOffset).val := by
            rw [hindexVal, hsame]
          unfold exactVecAt
          rw [hrow, vec_set_get_same current
            (start.wrapping_add currentOffset) qOut hindexBound]
          rw [qExact, hcurrentPowerExact]
          rw [if_neg (by rw [hnextOffset, hsame]; omega), hsame]
        · have hrowNe : start.val + target.val ≠
              (start.wrapping_add currentOffset).val := by
            rw [hindexVal]
            omega
          unfold exactVecAt
          rw [vec_set_get_ne current (start.wrapping_add currentOffset)
            qOut (start.val + target.val) hrowNe]
          change exactVecAt current (start.val + target.val) = _
          rw [hcurrentTarget]
          by_cases hbefore : currentOffset.val < target.val
          · have holdLe : currentOffset.val ≤ target.val := by omega
            have hnewLe : (currentOffset.wrapping_add 1#usize).val ≤
                target.val := by
              rw [hnextOffset]
              omega
            rw [if_pos holdLe, if_pos hnewLe]
          · have holdNot : ¬ currentOffset.val ≤ target.val := by omega
            have hnewNot : ¬ (currentOffset.wrapping_add 1#usize).val ≤
                target.val := by
              rw [hnextOffset]
              omega
            rw [if_neg holdNot, if_neg hnewNot]
      · rw [hnextOffset]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta]
      have hoffsetEq : currentOffset.val = 28 := by
        have hnot : ¬ currentOffset.val < 28 := by
          intro hsmall
          exact hlt hsmall
        omega
      rw [if_neg (by omega)] at hcurrentTarget
      exact ⟨hcurrentLength, hcurrentCanonical, hcurrentTarget⟩
  · exact ⟨hlength, hoffset, hcovector, hpower, hpowerExact, htarget⟩

/-- The authentic inner loop leaves a queried row unchanged when that row is
outside the 28 coefficient positions of the block being written. -/
private theorem terminal_inner_preserve_spec
    (covector : alloc.vec.Vec QM31)
    (challenge scale power : QM31)
    (start offset : Std.Usize) (query : Nat)
    (baseline : ExactQM31)
    (hlength : covector.length = 1024)
    (hstart : start.val + 28 ≤ 1024)
    (hoffset : offset.val ≤ 28)
    (hcovector : CanonicalVec covector)
    (hchallenge : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge)
    (hscale : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 scale)
    (hpower : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 power)
    (hpowerExact :
      ComponentBRealEvaluatorProof.generatedQm31ToExact power =
        ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ offset.val)
    (hquery : ∀ degree : Nat, degree < 28 →
      query ≠ start.val + degree)
    (hbaseline : exactVecAt covector query = baseline) :
    ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0
        covector challenge scale start power offset ⦃ out =>
      out.length = 1024 ∧ CanonicalVec out ∧
        exactVecAt out query = baseline ⦄ := by
  simp only [ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0]
  apply loop.spec_decr_nat
    (fun state => 28 - state.2.2.val)
    (fun state =>
      state.1.length = 1024 ∧ state.2.2.val ≤ 28 ∧ CanonicalVec state.1 ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 state.2.1 ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact state.2.1 =
        ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ state.2.2.val ∧
      exactVecAt state.1 query = baseline)
    (fun out => out.length = 1024 ∧ CanonicalVec out ∧
      exactVecAt out query = baseline)
  · rintro ⟨current, currentPower, currentOffset⟩
      ⟨hcurrentLength, hcurrentOffset, hcurrentCanonical, hcurrentPower,
        hcurrentPowerExact, hcurrentQuery⟩
    simp only [Prod.fst, Prod.snd] at hcurrentLength hcurrentOffset hcurrentCanonical hcurrentPower hcurrentPowerExact hcurrentQuery
    unfold ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0.body
    simp only [ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS]
    by_cases hlt : currentOffset < 28#usize
    · rw [if_pos hlt]
      have hoffsetLt : currentOffset.val < 28 := hlt
      have hsize : 1025 < Usize.size := by
        simpa using UScalar.hSize (1025#usize)
      have hsum : start.val + currentOffset.val < Usize.size := by omega
      have hindexVal := wrapping_add_val_of_lt start currentOffset hsum
      have hindexBound : (start.wrapping_add currentOffset).val < current.length := by
        rw [hcurrentLength, hindexVal]
        omega
      have hq := generated_mul_spec scale currentPower hscale hcurrentPower
      obtain ⟨qOut, qRun, qCanonical, _⟩ := WP.spec_imp_exists hq
      rw [qRun]
      simp only [bind_tc_ok, lift]
      rw [alloc.vec.Vec.index_mut_slice_index]
      unfold alloc.vec.Vec.index_mut_usize
      rw [vec_index_usize_run current
        (start.wrapping_add currentOffset) hindexBound]
      simp only [bind_tc_ok]
      have hp := generated_mul_spec currentPower challenge
        hcurrentPower hchallenge
      obtain ⟨powerOut, powerRun, powerCanonical, powerExact⟩ :=
        WP.spec_imp_exists hp
      rw [powerRun]
      simp only [bind_tc_ok]
      let next := current.set (start.wrapping_add currentOffset) qOut
      have hnextOffset := wrapping_add_one_val currentOffset (by omega)
      have hnextCanonical : CanonicalVec next :=
        canonicalVec_set current (start.wrapping_add currentOffset) qOut
          hindexBound hcurrentCanonical qCanonical
      have hqueryNe : query ≠ (start.wrapping_add currentOffset).val := by
        rw [hindexVal]
        exact hquery currentOffset.val hoffsetLt
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [next] using hcurrentLength
      · rw [hnextOffset]
        omega
      · exact hnextCanonical
      · exact powerCanonical
      · rw [powerExact, hcurrentPowerExact, hnextOffset, pow_succ]
      · simp only [Prod.fst, Prod.snd]
        unfold exactVecAt
        rw [vec_set_get_ne current (start.wrapping_add currentOffset)
          qOut query hqueryNe]
        exact hcurrentQuery
      · rw [hnextOffset]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta]
      exact ⟨hcurrentLength, hcurrentCanonical, hcurrentQuery⟩
  · exact ⟨hlength, hoffset, hcovector, hpower, hpowerExact, hbaseline⟩

private noncomputable def coefficientTerminalValue
    (point : Array QM31 10#usize) (halfExact : ExactQM31)
    (index : CoefficientIndex) : ExactQM31 :=
  halfExact ^ (9 - index.1.val) *
    ComponentBRealEvaluatorProof.generatedQm31ToExact
      point.val[index.1.val]! ^ index.2.val

/-- Query-specific correspondence for one maintained coefficient row through
the authentic generated ten-round outer loop. -/
private theorem terminal_outer_coefficient_spec
    (point : Array QM31 10#usize)
    (halfPowers : Array QM31 11#usize)
    (covector : alloc.vec.Vec QM31) (round : Std.Usize)
    (target : CoefficientIndex) (baseline halfExact : ExactQM31)
    (hpointCanonical : CanonicalArray point)
    (hhalfCanonical : CanonicalArray halfPowers)
    (hhalfExact : ∀ index : Nat, index < 11 →
      exactArrayAt halfPowers index = halfExact ^ index)
    (hlength : covector.length = 1024)
    (hround : round.val ≤ 10)
    (hcovector : CanonicalVec covector)
    (htarget :
      exactVecAt covector (coefficientRow target).val =
        if round.val ≤ target.1.val then baseline
        else coefficientTerminalValue point halfExact target) :
    ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1
        point halfPowers covector round ⦃ out =>
      out.length = 1024 ∧ CanonicalVec out ∧
      exactVecAt out (coefficientRow target).val =
        coefficientTerminalValue point halfExact target ⦄ := by
  simp only [ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1]
  apply loop.spec_decr_nat
    (fun state => 10 - state.2.val)
    (fun state =>
      state.1.length = 1024 ∧ state.2.val ≤ 10 ∧ CanonicalVec state.1 ∧
      exactVecAt state.1 (coefficientRow target).val =
        if state.2.val ≤ target.1.val then baseline
        else coefficientTerminalValue point halfExact target)
    (fun out => out.length = 1024 ∧ CanonicalVec out ∧
      exactVecAt out (coefficientRow target).val =
        coefficientTerminalValue point halfExact target)
  · rintro ⟨current, currentRound⟩
      ⟨hcurrentLength, hcurrentRound, hcurrentCanonical, hcurrentTarget⟩
    simp only [Prod.fst, Prod.snd] at hcurrentLength hcurrentRound hcurrentCanonical hcurrentTarget
    unfold ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1.body
    simp only [lift, bind_tc_ok]
    have hpointLen : Slice.len (Array.to_slice point) = 10#usize := by
      apply UScalar.eq_of_val_eq
      simp
    rw [hpointLen]
    by_cases hlt : currentRound < 10#usize
    · rw [if_pos hlt]
      have hroundLt : currentRound.val < 10 := hlt
      rw [array_index_usize_run point currentRound hroundLt]
      simp only [bind_tc_ok]
      have hreverseVal := wrapping_sub_val_of_le 9#usize currentRound (by
        norm_num
        omega)
      have hreverseBound :
          (Std.Usize.wrapping_sub 9#usize currentRound).val < 11 := by
        rw [hreverseVal]
        norm_num
        omega
      rw [array_index_usize_run halfPowers
        (Std.Usize.wrapping_sub 9#usize currentRound) hreverseBound]
      simp only [bind_tc_ok]
      rw [array_index_usize_run
        ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS
        currentRound hroundLt]
      simp only [bind_tc_ok,
        ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCK_ROWS]
      let currentFin : Fin 10 := ⟨currentRound.val, hroundLt⟩
      let challenge := point.val[currentRound.val]!
      let scale := halfPowers.val[
        (Std.Usize.wrapping_sub 9#usize currentRound).val]!
      let block :=
        ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS.val[
          currentRound.val]!
      let start := block.wrapping_mul 32#usize
      have hblockVal : block.val = blockSelector currentFin := by
        exact generated_round_block_value currentFin
      have hstartVal : start.val = 32 * blockSelector currentFin := by
        unfold start
        rw [wrapping_mul_val_of_lt]
        · rw [hblockVal]
          norm_num
          omega
        · rw [hblockVal]
          norm_num
          have := blockSelector_le_thirty currentFin
          have hsize : 1025 < Usize.size := by
            simpa using UScalar.hSize (1025#usize)
          omega
      have hstartBound : start.val + 28 ≤ 1024 := by
        rw [hstartVal]
        have := blockSelector_le_thirty currentFin
        omega
      have hchallengeCanonical :
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge := by
        exact hpointCanonical currentRound.val hroundLt
      have hscaleCanonical :
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 scale := by
        exact hhalfCanonical _ hreverseBound
      have hscaleExact :
          ComponentBRealEvaluatorProof.generatedQm31ToExact scale =
            halfExact ^ (9 - currentRound.val) := by
        exact (hhalfExact _ hreverseBound).trans (by
          rw [hreverseVal]
          norm_num)
      have honePower :
          ComponentBRealEvaluatorProof.generatedQm31ToExact
              ComponentBGenerated.aspis_core.field.QM31.ONE =
            ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ 0 := by
        rw [generated_ONE_exact, pow_zero]
      by_cases hsame : currentFin = target.1
      · have hcurrentEq : currentRound.val = target.1.val :=
          congrArg Fin.val hsame
        have hbaselineNow :
            exactVecAt current (coefficientRow target).val = baseline := by
          rw [hcurrentTarget, if_pos (by omega)]
        have hrow : (coefficientRow target).val =
            start.val + target.2.val := by
          rw [coefficientRow_val, hstartVal, hsame]
        have hinner := terminal_inner_target_spec current challenge scale
          ComponentBGenerated.aspis_core.field.QM31.ONE start 0#usize target.2
          baseline hcurrentLength hstartBound (by norm_num) hcurrentCanonical
          hchallengeCanonical hscaleCanonical generated_ONE_canonical honePower
          (by simpa [hrow] using hbaselineNow)
        obtain ⟨next, nextRun, nextLength, nextCanonical, nextTarget⟩ :=
          WP.spec_imp_exists hinner
        rw [nextRun]
        simp only [bind_tc_ok]
        have hnextRound := wrapping_add_one_val currentRound (by omega)
        simp only [WP.spec, WP.theta]
        refine ⟨⟨nextLength, ?_, nextCanonical, ?_⟩, ?_⟩
        · rw [hnextRound]
          omega
        · rw [if_neg (by rw [hnextRound]; omega)]
          simp only [Prod.fst, Prod.snd]
          rw [hrow, nextTarget]
          unfold coefficientTerminalValue
          rw [hscaleExact, hcurrentEq]
          unfold challenge
          rw [hcurrentEq]
        · rw [hnextRound]
          omega
      · have hselectorNe :
            blockSelector target.1 ≠ blockSelector currentFin := by
          intro heq
          exact hsame (blockSelector_injective heq).symm
        have hqueryOutside : ∀ degree : Nat, degree < 28 →
            (coefficientRow target).val ≠ start.val + degree := by
          intro degree hdegree heq
          rw [coefficientRow_val, hstartVal] at heq
          apply hselectorNe
          omega
        have hinner := terminal_inner_preserve_spec current challenge scale
          ComponentBGenerated.aspis_core.field.QM31.ONE start 0#usize
          (coefficientRow target).val
          (exactVecAt current (coefficientRow target).val)
          hcurrentLength hstartBound (by norm_num) hcurrentCanonical
          hchallengeCanonical hscaleCanonical generated_ONE_canonical honePower
          hqueryOutside rfl
        obtain ⟨next, nextRun, nextLength, nextCanonical, nextTarget⟩ :=
          WP.spec_imp_exists hinner
        rw [nextRun]
        simp only [bind_tc_ok]
        have hnextRound := wrapping_add_one_val currentRound (by omega)
        simp only [WP.spec, WP.theta]
        refine ⟨⟨nextLength, ?_, nextCanonical, ?_⟩, ?_⟩
        · rw [hnextRound]
          omega
        · rw [nextTarget, hcurrentTarget]
          have hiff : currentRound.val ≤ target.1.val ↔
              (currentRound.wrapping_add 1#usize).val ≤ target.1.val := by
            rw [hnextRound]
            constructor <;> intro hle
            · have hne : currentRound.val ≠ target.1.val := by
                intro heq
                apply hsame
                exact Fin.ext heq
              omega
            · omega
          by_cases hle : currentRound.val ≤ target.1.val
          · rw [if_pos hle, if_pos (hiff.mp hle)]
          · rw [if_neg hle, if_neg (fun h => hle (hiff.mpr h))]
        · rw [hnextRound]
          omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta]
      have hroundEq : currentRound.val = 10 := by
        have hnot : ¬ currentRound.val < 10 := hlt
        omega
      have htargetLt : target.1.val < 10 := by
        exact target.1.isLt
      rw [if_neg (by omega)] at hcurrentTarget
      exact ⟨hcurrentLength, hcurrentCanonical, hcurrentTarget⟩
  · exact ⟨hlength, hround, hcovector, htarget⟩

/-- The authentic generated outer loop preserves any query which is outside
all ten 28-row coefficient supports. -/
private theorem terminal_outer_preserve_spec
    (point : Array QM31 10#usize)
    (halfPowers : Array QM31 11#usize)
    (covector : alloc.vec.Vec QM31) (round : Std.Usize)
    (query : Nat) (baseline : ExactQM31)
    (hpointCanonical : CanonicalArray point)
    (hhalfCanonical : CanonicalArray halfPowers)
    (hlength : covector.length = 1024)
    (hround : round.val ≤ 10)
    (hcovector : CanonicalVec covector)
    (hquery : ∀ current : Fin 10, ∀ degree : Nat, degree < 28 →
      query ≠ 32 * blockSelector current + degree)
    (hbaseline : exactVecAt covector query = baseline) :
    ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1
        point halfPowers covector round ⦃ out =>
      out.length = 1024 ∧ CanonicalVec out ∧
        exactVecAt out query = baseline ⦄ := by
  simp only [ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1]
  apply loop.spec_decr_nat
    (fun state => 10 - state.2.val)
    (fun state => state.1.length = 1024 ∧ state.2.val ≤ 10 ∧
      CanonicalVec state.1 ∧ exactVecAt state.1 query = baseline)
    (fun out => out.length = 1024 ∧ CanonicalVec out ∧
      exactVecAt out query = baseline)
  · rintro ⟨current, currentRound⟩
      ⟨hcurrentLength, hcurrentRound, hcurrentCanonical, hcurrentQuery⟩
    simp only [Prod.fst, Prod.snd] at hcurrentLength hcurrentRound hcurrentCanonical hcurrentQuery
    unfold ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1.body
    simp only [lift, bind_tc_ok]
    have hpointLen : Slice.len (Array.to_slice point) = 10#usize := by
      apply UScalar.eq_of_val_eq
      simp
    rw [hpointLen]
    by_cases hlt : currentRound < 10#usize
    · rw [if_pos hlt]
      have hroundLt : currentRound.val < 10 := hlt
      rw [array_index_usize_run point currentRound hroundLt]
      simp only [bind_tc_ok]
      have hreverseVal := wrapping_sub_val_of_le 9#usize currentRound (by
        norm_num
        omega)
      have hreverseBound :
          (Std.Usize.wrapping_sub 9#usize currentRound).val < 11 := by
        rw [hreverseVal]
        norm_num
        omega
      rw [array_index_usize_run halfPowers
        (Std.Usize.wrapping_sub 9#usize currentRound) hreverseBound]
      simp only [bind_tc_ok]
      rw [array_index_usize_run
        ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS
        currentRound hroundLt]
      simp only [bind_tc_ok,
        ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCK_ROWS]
      let currentFin : Fin 10 := ⟨currentRound.val, hroundLt⟩
      let challenge := point.val[currentRound.val]!
      let scale := halfPowers.val[
        (Std.Usize.wrapping_sub 9#usize currentRound).val]!
      let block :=
        ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS.val[
          currentRound.val]!
      let start := block.wrapping_mul 32#usize
      have hblockVal : block.val = blockSelector currentFin :=
        generated_round_block_value currentFin
      have hstartVal : start.val = 32 * blockSelector currentFin := by
        unfold start
        rw [wrapping_mul_val_of_lt]
        · rw [hblockVal]
          norm_num
          omega
        · rw [hblockVal]
          norm_num
          have := blockSelector_le_thirty currentFin
          have hsize : 1025 < Usize.size := by
            simpa using UScalar.hSize (1025#usize)
          omega
      have hstartBound : start.val + 28 ≤ 1024 := by
        rw [hstartVal]
        have := blockSelector_le_thirty currentFin
        omega
      have hchallengeCanonical :
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 challenge :=
        hpointCanonical currentRound.val hroundLt
      have hscaleCanonical :
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 scale :=
        hhalfCanonical _ hreverseBound
      have honePower :
          ComponentBRealEvaluatorProof.generatedQm31ToExact
              ComponentBGenerated.aspis_core.field.QM31.ONE =
            ComponentBRealEvaluatorProof.generatedQm31ToExact challenge ^ 0 := by
        rw [generated_ONE_exact, pow_zero]
      have hqueryOutside : ∀ degree : Nat, degree < 28 →
          query ≠ start.val + degree := by
        intro degree hdegree
        rw [hstartVal]
        exact hquery currentFin degree hdegree
      have hinner := terminal_inner_preserve_spec current challenge scale
        ComponentBGenerated.aspis_core.field.QM31.ONE start 0#usize query
        baseline hcurrentLength hstartBound (by norm_num) hcurrentCanonical
        hchallengeCanonical hscaleCanonical generated_ONE_canonical honePower
        hqueryOutside hcurrentQuery
      obtain ⟨next, nextRun, nextLength, nextCanonical, nextQuery⟩ :=
        WP.spec_imp_exists hinner
      rw [nextRun]
      simp only [bind_tc_ok]
      have hnextRound := wrapping_add_one_val currentRound (by omega)
      simp only [WP.spec, WP.theta]
      refine ⟨⟨nextLength, ?_, nextCanonical, nextQuery⟩, ?_⟩
      · rw [hnextRound]
        omega
      · rw [hnextRound]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta]
      exact ⟨hcurrentLength, hcurrentCanonical, hcurrentQuery⟩
  · exact ⟨hlength, hround, hcovector, hbaseline⟩

theorem terminalWeights_eq_zero_of_outside
    (point : Round → ExactQM31) (row : Row)
    (hinitial : row ≠ initialRow)
    (hcoefficient : ∀ index : CoefficientIndex,
      row ≠ coefficientRow index) :
    terminalWeights point 1 row = 0 := by
  classical
  simp only [terminalWeights, Pi.add_apply, basis, if_neg hinitial]
  simp only [zero_add, Finset.sum_apply]
  have hBasis : ∀ (index : CoefficientIndex) (value : ExactQM31),
      basis (coefficientRow index) value row = 0 := by
    intro index value
    simp only [basis, if_neg (hcoefficient index)]
  simp only [hBasis]
  simp only [Finset.sum_const, nsmul_zero]

private theorem terminal_initial_matches
    (covector : alloc.vec.Vec QM31) (point : Round → ExactQM31)
    (hinitial : exactVecAt covector initialRow.val =
      AspisV5SumcheckCommitment.half ^ 10) :
    exactVecAt covector initialRow.val = terminalWeights point 1 initialRow := by
  rw [terminalWeights_at_initial]
  exact eq_one_mul_of_eq hinitial

/-- Source-authentic top-level correspondence for the generated terminal
covector.  Every one of the 1,024 generated rows is identified with the
maintained sparse `terminalWeights point 1`; no model/model alias is used. -/
theorem extracted_terminal_covector_rows_eq_terminalWeights
    (point : Array QM31 10#usize)
    (hpointCanonical : CanonicalArray point) :
    ∃ covector,
      ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector
          point = ok covector ∧
      covector.length = 1024 ∧ CanonicalVec covector ∧
      ∀ row : Row,
        exactVecAt covector row.val =
          terminalWeights
            (fun round =>
              ComponentBRealEvaluatorProof.generatedQm31ToExact
                point.val[round.val]!) 1 row := by
  obtain ⟨halfValue, halfRun, halfCanonical, _⟩ :=
    ComponentBHalfCombinedProof.generated_qm31_half_doubles_canonical
      ComponentBGenerated.aspis_core.field.QM31.ONE (by
        simpa [ComponentBHalfCombinedProof.CanonicalQM31,
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
          ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
          AspisAeneasCM31Multiplicative.CanonicalRawM31,
          AspisAeneasCM31Multiplicative.m31Modulus] using
            generated_ONE_canonical)
  have halfExactPair :=
    ComponentBMaintainedTerminalBridge.generated_half_exact
      ComponentBGenerated.aspis_core.field.QM31.ONE halfValue
      (by
        intro h
        have hre := congrArg QuadraticAlgebra.re h
        have hrere := congrArg QuadraticAlgebra.re hre
        change (2 : AspisAeneasCM31Exact.M31Exact) = 0 at hrere
        exact (by decide : (2 : AspisAeneasCM31Exact.M31Exact) ≠ 0) hrere)
      generated_ONE_canonical halfRun
  have halfExact :
      ComponentBRealEvaluatorProof.generatedQm31ToExact halfValue =
        AspisV5SumcheckCommitment.half := by
    rw [halfExactPair.2, generated_ONE_exact]
    exact mul_one _
  let seed : Array QM31 11#usize :=
    Array.repeat 11#usize ComponentBGenerated.aspis_core.field.QM31.ONE
  have seedCanonical : CanonicalArray seed := by
    intro index hindex
    norm_num at hindex
    have hentry : seed.val[index]! =
        ComponentBGenerated.aspis_core.field.QM31.ONE := by
      unfold seed
      exact array_repeat_get_bang 11#usize _ index hindex
    rw [hentry]
    exact generated_ONE_canonical
  have seedPrefix : HalfPowerPrefix AspisV5SumcheckCommitment.half
      seed 1#usize := by
    unfold HalfPowerPrefix
    refine ⟨seedCanonical, by norm_num, by norm_num, ?_⟩
    intro index hindex
    unfold exactArrayAt seed
    have hentry :
        (Array.repeat 11#usize
          ComponentBGenerated.aspis_core.field.QM31.ONE).val[index]! =
          ComponentBGenerated.aspis_core.field.QM31.ONE := by
      exact array_repeat_get_bang 11#usize _ index (by
        norm_num
        exact hindex)
    rw [hentry, generated_ONE_exact]
    have honeVal : (1#usize).val = 1 := by norm_num
    rw [honeVal]
    by_cases hzero : index < 1
    · have : index = 0 := by omega
      subst index
      rfl
    · rw [if_neg hzero]
  have halfLoop := terminal_half_power_loop_spec halfValue
    AspisV5SumcheckCommitment.half seed 1#usize halfExactPair.1 halfExact
    seedPrefix
  obtain ⟨halfPowers, halfPowersRun, halfPowersCanonical,
      halfPowersExact⟩ := WP.spec_imp_exists halfLoop
  obtain ⟨zeroVec, zeroVecRun, zeroVecValues, zeroVecLength⟩ :=
    generated_zero_vec_exists 1024#usize
  have zeroVecCanonical : CanonicalVec zeroVec := by
    intro index hindex
    have hentry : zeroVec.val[index]! =
        ComponentBGenerated.aspis_core.field.QM31.ZERO := by
      rw [zeroVecValues]
      exact generated_zero_replicate_getElemBang _ _
    rw [hentry]
    exact generated_ZERO_canonical
  have zeroVecExact (index : Nat) : exactVecAt zeroVec index = 0 := by
    unfold exactVecAt
    have hentry : zeroVec.val[index]! =
        ComponentBGenerated.aspis_core.field.QM31.ZERO := by
      rw [zeroVecValues]
      exact generated_zero_replicate_getElemBang _ _
    rw [hentry, generated_ZERO_exact]
  have htenBound : (10#usize).val < (11#usize).val := by norm_num
  have halfTenRun := array_index_usize_run halfPowers 10#usize htenBound
  let halfTen := halfPowers.val[10]!
  have halfTenCanonical :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 halfTen :=
    halfPowersCanonical 10 (by norm_num)
  have halfTenExact :
      ComponentBRealEvaluatorProof.generatedQm31ToExact halfTen =
        AspisV5SumcheckCommitment.half ^ 10 :=
    halfPowersExact 10 (by norm_num)
  let preOuter := zeroVec.set
    ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW halfTen
  have initialIndexVal :
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW.val =
        initialRow.val := by norm_num [ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW,
          initialRow]
  have initialIndexBound :
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW.val <
        zeroVec.length := by
    rw [zeroVecLength]
    norm_num [ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW]
  have preOuterLength : preOuter.length = 1024 := by
    simpa [preOuter] using zeroVecLength
  have preOuterCanonical : CanonicalVec preOuter :=
    canonicalVec_set zeroVec
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
      halfTen initialIndexBound zeroVecCanonical halfTenCanonical
  have preOuterInitial :
      exactVecAt preOuter initialRow.val =
        AspisV5SumcheckCommitment.half ^ 10 := by
    unfold preOuter exactVecAt
    rw [← initialIndexVal, vec_set_get_same zeroVec
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
      halfTen initialIndexBound, halfTenExact]
  have initialOutside : ∀ current : Fin 10, ∀ degree : Nat,
      degree < 28 → initialRow.val ≠ 32 * blockSelector current + degree := by
    intro current degree hdegree heq
    have := blockSelector_le_thirty current
    norm_num [initialRow] at heq
    omega
  have outerInitial := terminal_outer_preserve_spec point halfPowers preOuter
    0#usize initialRow.val (AspisV5SumcheckCommitment.half ^ 10)
    hpointCanonical halfPowersCanonical preOuterLength (by norm_num)
    preOuterCanonical initialOutside preOuterInitial
  obtain ⟨finalCovector, finalOuterRun, finalLength, finalCanonical,
      finalInitial⟩ := WP.spec_imp_exists outerInitial
  refine ⟨finalCovector, ?_, finalLength, finalCanonical, ?_⟩
  · unfold ComponentBGenerated.v5_mask.split_layer_zero.v5_structured_terminal_covector
    rw [halfRun]
    simp only [bind_tc_ok]
    rw [halfPowersRun]
    simp only [bind_tc_ok]
    rw [generated_trace_rows_eq, zeroVecRun, halfTenRun]
    simp only [bind_tc_ok]
    rw [alloc.vec.Vec.index_mut_slice_index]
    unfold alloc.vec.Vec.index_mut_usize
    rw [vec_index_usize_run zeroVec
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
      initialIndexBound]
    simp only [bind_tc_ok]
    exact finalOuterRun
  · intro row
    by_cases hinitial : row = initialRow
    · subst row
      exact terminal_initial_matches finalCovector _ finalInitial
    · by_cases hcoefficient : ∃ index : CoefficientIndex,
          row = coefficientRow index
      · obtain ⟨index, rfl⟩ := hcoefficient
        have preCoefficient :
            exactVecAt preOuter (coefficientRow index).val = 0 := by
          unfold preOuter exactVecAt
          rw [vec_set_get_ne]
          · exact zeroVecExact _
          · rw [initialIndexVal]
            intro hval
            apply coefficientRow_ne_initial index
            exact Fin.ext hval
        have outerCoefficient := terminal_outer_coefficient_spec point
          halfPowers preOuter 0#usize index 0
          AspisV5SumcheckCommitment.half hpointCanonical
          halfPowersCanonical halfPowersExact preOuterLength (by norm_num)
          preOuterCanonical (by simpa using preCoefficient)
        obtain ⟨candidate, candidateRun, _, _, candidateExact⟩ :=
          WP.spec_imp_exists outerCoefficient
        have candidateEq : candidate = finalCovector :=
          Result.ok.inj (candidateRun.symm.trans finalOuterRun)
        subst candidate
        rw [candidateExact, terminalWeights_at_coefficient]
        unfold coefficientTerminalValue
        exact congrArg
          (fun value : ExactQM31 => value *
            ComponentBRealEvaluatorProof.generatedQm31ToExact
              point.val[index.1.val]! ^ index.2.val)
          (one_mul _).symm
      · have rowOutside : ∀ current : Fin 10, ∀ degree : Nat,
            degree < 28 →
            row.val ≠ 32 * blockSelector current + degree := by
          intro current degree hdegree heq
          let stored : Fin 28 := ⟨degree, hdegree⟩
          apply hcoefficient
          refine ⟨(current, stored), Fin.ext ?_⟩
          simpa [coefficientRow_val, stored] using heq
        have preRow : exactVecAt preOuter row.val = 0 := by
          unfold preOuter exactVecAt
          rw [vec_set_get_ne]
          · exact zeroVecExact _
          · rw [initialIndexVal]
            intro hval
            apply hinitial
            exact Fin.ext hval
        have outerRow := terminal_outer_preserve_spec point halfPowers
          preOuter 0#usize row.val 0 hpointCanonical halfPowersCanonical
          preOuterLength (by norm_num) preOuterCanonical rowOutside preRow
        obtain ⟨candidate, candidateRun, _, _, candidateExact⟩ :=
          WP.spec_imp_exists outerRow
        have candidateEq : candidate = finalCovector :=
          Result.ok.inj (candidateRun.symm.trans finalOuterRun)
        subst candidate
        rw [candidateExact]
        symm
        exact terminalWeights_eq_zero_of_outside _ row hinitial (by
          intro index heq
          exact hcoefficient ⟨index, heq⟩)

#print axioms terminal_inner_target_spec
#print axioms terminal_inner_preserve_spec
#print axioms terminal_outer_coefficient_spec
#print axioms terminal_outer_preserve_spec
#print axioms extracted_terminal_covector_rows_eq_terminalWeights

end ComponentBLayoutBindingsProof
