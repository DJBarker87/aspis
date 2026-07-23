import GoodMatricesCurrent.SourceExtractedTerminalField

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalField

open AspisV5ComponentCQM31TowerExact
open AspisV5M31RawMulReduction

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
  · change output.val < AspisV5ComponentCQM31TowerExact.P
    rw [hout, hproduct]
    exact rawReduceU64_canonical _ hproductBound
  · rw [hout, hproduct]
    exact rawReduceU64_residue _ hproductBound |>.trans (by rw [Nat.cast_mul])

end GoodMatricesCurrent.SourceExtractedTerminalField
