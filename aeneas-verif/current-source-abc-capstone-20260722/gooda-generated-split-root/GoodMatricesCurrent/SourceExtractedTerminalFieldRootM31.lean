import GoodMatricesCurrent.SourceExtractedTerminalField

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalField

open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCQM31RustFormulaSeam
open AspisV5M31RawMulReduction
open AspisV5M31RawSubNeg

private theorem u32_wrapping_add_val_exact (left right : Std.U32)
    (hbound : left.val + right.val < UScalar.size .U32) :
    (Std.U32.wrapping_add left right).val = left.val + right.val := by
  rw [Std.U32.wrapping_add_val_eq, Nat.mod_eq_of_lt hbound]

private theorem u32_wrapping_sub_val_of_le (left right : Std.U32)
    (hle : right.val ≤ left.val) :
    (Std.U32.wrapping_sub left right).val = left.val - right.val := by
  rw [Std.U32.wrapping_sub_val_eq]
  have hrearrange :
      left.val + (UScalar.size .U32 - right.val) =
        (left.val - right.val) + UScalar.size .U32 := by
    have hleft := left.hSize
    have hright := right.hSize
    omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by
    have hleft := left.hSize
    omega)

theorem root_m31_sub_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.sub left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) - (right.val : ExactM31) := by
  let biased : Std.U32 := Std.U32.wrapping_add left 2147483647#u32
  let reduced : Std.U32 := Std.U32.wrapping_sub biased right
  have hbiasedBound : left.val + P < UScalar.size .U32 := by
    have h := canonicalRawM31_sub_add_lt_u32 hleft hright
    simpa [UScalar.size, Std.U32.size, Std.U32.numBits] using h
  have hbiased : biased.val = left.val + P := by
    unfold biased
    rw [u32_wrapping_add_val_exact]
    · norm_num [P]
    · simpa [P] using hbiasedBound
  have hnoUnderflow : right.val ≤ biased.val := by
    rw [hbiased]
    exact canonicalRawM31_sub_no_underflow hleft hright
  have hreduced : reduced.val = left.val + P - right.val := by
    unfold reduced
    rw [u32_wrapping_sub_val_of_le _ _ hnoUnderflow, hbiased]
  by_cases hhigh : P ≤ reduced.val
  · have hcondition : reduced >= 2147483647#u32 := by
      apply (UScalar.le_equiv _ _).2
      simpa [P] using hhigh
    let output := Std.U32.wrapping_sub reduced 2147483647#u32
    have hout : output.val = left.val + P - right.val - P := by
      unfold output
      rw [u32_wrapping_sub_val_of_le]
      · rw [hreduced]
        norm_num [P]
      · exact (UScalar.le_equiv _ _).1 hcondition
    refine ⟨output, ?_, ?_, ?_⟩
    · unfold _root_.aspis_core.field.M31.sub
      unfold AspisCoreAdditive.field.M31.sub
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [AspisCoreAdditive.field.P]
      rw [if_pos (by simpa [reduced, P] using hhigh)]
      rfl
    · change output.val < P
      rw [hout]
      exact (rawM31Sub_high_branch hleft hright
        (by simpa [hreduced] using hhigh)).2.2
    · calc
        (output.val : ExactM31) =
            (rawM31Sub left.val right.val : ExactM31) := by
              rw [(rawM31Sub_high_branch hleft hright
                (by simpa [hreduced] using hhigh)).1, hout]
        _ = (left.val : ExactM31) - (right.val : ExactM31) :=
          residue_rawM31Sub hleft hright
  · have hcondition : ¬ reduced >= 2147483647#u32 := by
      intro hge
      apply hhigh
      have := (UScalar.le_equiv _ _).1 hge
      simpa [P] using this
    refine ⟨reduced, ?_, ?_, ?_⟩
    · unfold _root_.aspis_core.field.M31.sub
      unfold AspisCoreAdditive.field.M31.sub
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [AspisCoreAdditive.field.P]
      rw [if_neg (by simpa [reduced, P] using hcondition)]
    · change reduced.val < P
      omega
    · rw [hreduced]
      have hlow : left.val + P - right.val < P := by omega
      calc
        ((left.val + P - right.val : Nat) : ExactM31) =
            (rawM31Sub left.val right.val : ExactM31) := by
              rw [(rawM31Sub_low_branch hlow).1]
        _ = (left.val : ExactM31) - (right.val : ExactM31) :=
          residue_rawM31Sub hleft hright

#exit

private theorem u64_cast_u32_val (value : Std.U32) :
    (UScalar.cast .U64 value : Std.U64).val = value.val := by
  simp

theorem root_m31_mul_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.mul left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) * (right.val : ExactM31) := by
  let wideLeft : Std.U64 := UScalar.cast .U64 left
  let wideRight : Std.U64 := UScalar.cast .U64 right
  let product : Std.U64 := Std.U64.wrapping_mul wideLeft wideRight
  have hproductBound : left.val * right.val < 2 ^ 64 :=
    canonicalMul_lt_two_pow64 hleft hright
  have hproduct : product.val = left.val * right.val := by
    unfold product
    rw [Std.U64.wrapping_mul_val_eq, u64_cast_u32_val, u64_cast_u32_val]
    apply Nat.mod_eq_of_lt
    simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hproductBound
  obtain ⟨output, hcall, hout⟩ :=
    GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec product
  refine ⟨output, ?_, ?_, ?_⟩
  · unfold _root_.aspis_core.field.M31.mul
    unfold AuthenticFieldPow.field.M31.mul
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    simp [wideLeft, wideRight, product, hcall]
  · change output.val < P
    rw [hout, hproduct]
    exact rawReduceU64_canonical _ hproductBound
  · rw [hout, hproduct]
    exact rawReduceU64_residue _ hproductBound |>.trans (by rw [Nat.cast_mul])

theorem root_m31_add_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.add left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) + (right.val : ExactM31) := by
  simpa [aspis_verifier.aspis_core.field.M31.add] using
    local_m31_add_corresponds left right hleft hright

end GoodMatricesCurrent.SourceExtractedTerminalField
