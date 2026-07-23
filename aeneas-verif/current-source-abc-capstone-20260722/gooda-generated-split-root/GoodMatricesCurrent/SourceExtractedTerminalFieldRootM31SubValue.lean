import GoodMatricesCurrent.SourceExtractedTerminalFieldRootM31SubCall

open Aeneas Aeneas.Std Result ControlFlow Error

namespace GoodMatricesCurrent.SourceExtractedTerminalField

open AspisV5ComponentCQM31TowerExact
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

theorem rootM31SubOutput_val (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    (rootM31SubOutput left right).val = rawM31Sub left.val right.val := by
  let biased := Std.U32.wrapping_add left 2147483647#u32
  let reduced := Std.U32.wrapping_sub biased right
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
    have hout : (Std.U32.wrapping_sub reduced 2147483647#u32).val =
        left.val + P - right.val - P := by
      rw [u32_wrapping_sub_val_of_le]
      · rw [hreduced]
        norm_num [P]
      · exact (UScalar.le_equiv _ _).1 hcondition
    rw [rootM31SubOutput, if_pos hcondition, hout,
      (rawM31Sub_high_branch hleft hright
        (by simpa [hreduced] using hhigh)).1]
  · have hcondition : ¬ reduced >= 2147483647#u32 := by
      intro hge
      apply hhigh
      have := (UScalar.le_equiv _ _).1 hge
      simpa [P] using this
    have hlow : left.val + P - right.val < P := by
      rw [← hreduced]
      omega
    rw [rootM31SubOutput, if_neg hcondition, hreduced,
      (rawM31Sub_low_branch hlow).1]

theorem root_m31_sub_corresponds (left right : _root_.aspis_core.field.M31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    ∃ output : _root_.aspis_core.field.M31,
      _root_.aspis_core.field.M31.sub left right = .ok output ∧
      CanonicalLocalM31 output ∧
      (output.val : ExactM31) =
        (left.val : ExactM31) - (right.val : ExactM31) := by
  refine ⟨rootM31SubOutput left right, root_m31_sub_call left right, ?_, ?_⟩
  · change (rootM31SubOutput left right).val < P
    rw [rootM31SubOutput_val left right hleft hright]
    exact rawM31Sub_canonical hleft hright
  · rw [rootM31SubOutput_val left right hleft hright]
    exact residue_rawM31Sub hleft hright

end GoodMatricesCurrent.SourceExtractedTerminalField
