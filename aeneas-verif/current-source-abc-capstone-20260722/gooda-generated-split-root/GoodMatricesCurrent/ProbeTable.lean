import GoodMatricesCurrent.Funs
import AspisFormal.V5GoodGateSparseShift

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier
open AspisV5GoodGateSparseShift

example (index : Std.Usize) (hindex : index.val < 47)
    (hodd : index.val % 2 ≠ 0) :
    Exists fun word : Std.U8 =>
      Array.index_usize
          v5_cu_probe.good_gate_probe.ODD_NATURAL_TRAILING_ONES
          (Std.Usize.wrapping_shr index 1#u32) = .ok word /\
      (core.convert.num.FromUsizeU8.from word).val = trailingOnes index.val := by
  have hhalf : (Std.Usize.wrapping_shr index 1#u32).val < 24 := by
    change index.bv.toNat >>> (1 % System.Platform.numBits) < 24
    rw [Std.Usize.bv_toNat, Nat.shiftRight_eq_div_pow]
    rcases System.Platform.numBits_eq with hp | hp <;> simp [hp] <;> omega
  obtain ⟨word, hword, hvalue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec
      v5_cu_probe.good_gate_probe.ODD_NATURAL_TRAILING_ONES
      (Std.Usize.wrapping_shr index 1#u32) (by simpa using hhalf))
  refine ⟨word, hword, ?_⟩
  rw [hvalue]
  have hshrVal : (Std.Usize.wrapping_shr index 1#u32).val = index.val / 2 := by
    change index.bv.toNat >>> (1 % System.Platform.numBits) = index.val / 2
    rw [Std.Usize.bv_toNat, Nat.shiftRight_eq_div_pow]
    rcases System.Platform.numBits_eq with hp | hp <;> simp [hp]
  interval_cases hi : index.val <;>
    simp [v5_cu_probe.good_gate_probe.ODD_NATURAL_TRAILING_ONES,
      trailingOnes, hshrVal, hi] at hodd ⊢
  all_goals rfl
