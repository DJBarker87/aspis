import GoodMatricesCurrent.Funs
import AspisFormal.V5ComponentCQM31RustFormulaSeam
import AspisFormal.V5M31RawMulReduction
import AspisFormal.V5M31RawSubNeg

open Aeneas Aeneas.Std
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedField

open AspisV5ComponentCQM31RustFormulaSeam
open AspisV5M31RawMulReduction
open AspisV5M31RawSubNeg

private abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
private abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
private abbrev Modulus := AspisV5ComponentCQM31TowerExact.P

def m31ToExact (value : LocalM31) : ExactM31 := value.val

def CanonicalLocalM31 (value : LocalM31) : Prop := value.val < Modulus

private theorem u32_size_eq_rawWordCount :
    Std.U32.size = AspisV5ComponentCRejectionSampler.rawWordCount := by
  norm_num [Std.U32.size, Std.U32.numBits,
    AspisV5ComponentCRejectionSampler.rawWordCount]

private theorem u32_wrapping_sub_val_of_le (left right : Std.U32)
    (hle : right.val ≤ left.val) :
    (Std.U32.wrapping_sub left right).val = left.val - right.val := by
  rw [Std.U32.wrapping_sub_val_eq]
  have hleft := left.hSize
  have hright := right.hSize
  have hrearrange :
      left.val + (UScalar.size .U32 - right.val) =
        (left.val - right.val) + UScalar.size .U32 := by
    omega
  rw [hrearrange]
  simp only [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem local_m31_add_word_spec (left right : LocalM31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    Exists fun result =>
      aspis_verifier.aspis_core.field.M31.add left right = .ok result /\
      result.val = rawM31Add left.val right.val := by
  unfold aspis_verifier.aspis_core.field.M31.add
  unfold aspis_core.field.M31.add
  simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
  rw [aspis_core.field.P]
  by_cases hhigh : Modulus ≤ left.val + right.val
  · have hsum :
        (Std.U32.wrapping_add left right).val = left.val + right.val := by
      rw [Std.U32.wrapping_add_val_eq]
      have hlt := canonicalRawM31_add_lt_u32 hleft hright
      apply Nat.mod_eq_of_lt
      simpa only [UScalar.size_UScalarTyU32,
        u32_size_eq_rawWordCount] using hlt
    have hge : Std.U32.wrapping_add left right >= 2147483647#u32 := by
      apply (UScalar.le_equiv _ _).2
      rw [hsum]
      simpa [Modulus] using hhigh
    rw [if_pos hge]
    refine ⟨Std.U32.wrapping_sub (Std.U32.wrapping_add left right)
        2147483647#u32, rfl, ?_⟩
    rw [u32_wrapping_sub_val_of_le]
    · rw [hsum]
      have hpval : (2147483647#u32 : Std.U32).val = Modulus := by
        norm_num [Modulus]
      rw [hpval]
      exact (rawM31Add_high_branch hleft hright hhigh).1.symm
    · exact (UScalar.le_equiv _ _).1 hge
  · have hlow : left.val + right.val < Modulus := by omega
    have hsum :
        (Std.U32.wrapping_add left right).val = left.val + right.val := by
      rw [Std.U32.wrapping_add_val_eq]
      have hlt := canonicalRawM31_add_lt_u32 hleft hright
      apply Nat.mod_eq_of_lt
      simpa only [UScalar.size_UScalarTyU32,
        u32_size_eq_rawWordCount] using hlt
    have hnge : ¬ Std.U32.wrapping_add left right >= 2147483647#u32 := by
      intro hge
      apply hhigh
      have hval := (UScalar.le_equiv _ _).1 hge
      rw [hsum] at hval
      simpa [Modulus] using hval
    rw [if_neg hnge]
    refine ⟨Std.U32.wrapping_add left right, rfl, ?_⟩
    rw [hsum]
    exact (rawM31Add_low_branch hlow).1.symm

theorem local_m31_add_exact_spec (left right : LocalM31)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right) :
    Exists fun result =>
      aspis_verifier.aspis_core.field.M31.add left right = .ok result /\
      CanonicalLocalM31 result /\
      m31ToExact result = m31ToExact left + m31ToExact right := by
  obtain ⟨result, hresult, hword⟩ :=
    local_m31_add_word_spec left right hleft hright
  refine ⟨result, hresult, ?_, ?_⟩
  · change result.val < Modulus
    rw [hword]
    exact rawM31Add_canonical hleft hright
  · simp only [m31ToExact, hword]
    exact residue_rawM31Add hleft hright

def rawM31Half (value : Nat) : Nat :=
  if value % 2 = 0 then value / 2 else (value + Modulus) / 2

@[simp] private theorem u32_and_one_val (value : Std.U32) :
    (value &&& 1#u32).val = value.val % 2 := by
  change value.val &&& 1 = value.val % 2
  exact Nat.and_one_is_mod value.val

@[simp] private theorem u32_wrapping_shr_one_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 1#u32).val = value.val / 2 := by
  change value.bv.toNat >>> (1 % 32) = value.val / 2
  simp only [Std.U32.bv_toNat, Nat.shiftRight_eq_div_pow]

@[simp] private theorem u64_wrapping_shr_one_val (value : Std.U64) :
    (Std.U64.wrapping_shr value 1#u32).val = value.val / 2 := by
  change value.bv.toNat >>> (1 % 64) = value.val / 2
  simp only [Std.U64.bv_toNat, Nat.shiftRight_eq_div_pow]

private theorem canonical_sum_lt_u64 {value : Nat}
    (hvalue : value < Modulus) : value + Modulus < UScalar.size .U64 := by
  calc
    value + Modulus < Modulus + Modulus := Nat.add_lt_add_right hvalue Modulus
    _ < UScalar.size .U64 := by
      norm_num [Modulus, UScalar.size, Std.U64.size, Std.U64.numBits]

private theorem canonical_half_sum_lt_u32 {value : Nat}
    (hvalue : value < Modulus) : (value + Modulus) / 2 < 2 ^ 32 := by
  have hlt : (value + Modulus) / 2 < Modulus := by
    norm_num [Modulus] at hvalue ⊢
    omega
  norm_num [Modulus] at hlt ⊢
  omega

private theorem local_m31_half_word_spec (value : LocalM31)
    (hvalue : CanonicalLocalM31 value) :
    Exists fun result =>
      aspis_verifier.aspis_core.field.M31.half value = .ok result /\
      result.val = rawM31Half value.val := by
  unfold aspis_verifier.aspis_core.field.M31.half
  unfold aspis_core.field.M31.half
  unfold AuthenticFieldHalf.field.M31.half
  simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
  by_cases heven : value.val % 2 = 0
  · have hbit : value &&& 1#u32 = 0#u32 := by
      apply UScalar.eq_of_val_eq
      simpa using heven
    rw [if_pos hbit]
    refine ⟨Std.U32.wrapping_shr value 1#u32, rfl, ?_⟩
    simp [rawM31Half, heven]
  · have hbit : value &&& 1#u32 ≠ 0#u32 := by
      intro equal
      have hval := congrArg UScalar.val equal
      simp at hval
      exact heven hval
    rw [if_neg hbit]
    let wideValue : Std.U64 := UScalar.cast .U64 value
    let wideP : Std.U64 := UScalar.cast .U64 AuthenticFieldHalf.field.P
    let wideSum : Std.U64 := Std.U64.wrapping_add wideValue wideP
    let wideHalf : Std.U64 := Std.U64.wrapping_shr wideSum 1#u32
    let result : Std.U32 := UScalar.cast .U32 wideHalf
    refine ⟨result, rfl, ?_⟩
    have hpval : AuthenticFieldHalf.field.P.val = Modulus := by
      rw [AuthenticFieldHalf.field.P]
      norm_num [Modulus]
    have hwideValue : wideValue.val = value.val := by
      simp [wideValue]
    have hwideP : wideP.val = Modulus := by
      simp [wideP, hpval]
    have hsumBound : value.val + Modulus < UScalar.size .U64 := by
      exact canonical_sum_lt_u64 hvalue
    have hwideSum : wideSum.val = value.val + Modulus := by
      simp only [wideSum, Std.U64.wrapping_add_val_eq]
      rw [hwideValue, hwideP, Nat.mod_eq_of_lt hsumBound]
    have hwideHalf : wideHalf.val = (value.val + Modulus) / 2 := by
      simp [wideHalf, hwideSum]
    have hhalfBound : wideHalf.val < 2 ^ 32 := by
      rw [hwideHalf]
      exact canonical_half_sum_lt_u32 hvalue
    have hresult : result.val = wideHalf.val := by
      exact UScalar.cast_val_mod_pow_of_inBounds_eq .U32 wideHalf hhalfBound
    rw [hresult, hwideHalf]
    simp [rawM31Half, heven]

theorem rawM31Half_canonical {value : Nat}
    (hvalue : value < Modulus) : rawM31Half value < Modulus := by
  unfold rawM31Half
  split <;> omega

theorem rawM31Half_double {value : Nat}
    (_hvalue : value < Modulus) :
    (2 : ExactM31) * (rawM31Half value : ExactM31) = (value : ExactM31) := by
  unfold rawM31Half
  split <;> rename_i hparity
  · have hdouble : 2 * (value / 2) = value := by omega
    change ((2 : Nat) : ExactM31) * ((value / 2 : Nat) : ExactM31) =
      (value : ExactM31)
    rw [← Nat.cast_mul, hdouble]
  · have hmod : value % 2 = 1 := by omega
    have hpmod : Modulus % 2 = 1 := by norm_num [Modulus]
    have hdouble : 2 * ((value + Modulus) / 2) = value + Modulus := by
      omega
    change ((2 : Nat) : ExactM31) *
      (((value + Modulus) / 2 : Nat) : ExactM31) = (value : ExactM31)
    rw [← Nat.cast_mul, hdouble, Nat.cast_add, ZMod.natCast_self, add_zero]

theorem local_m31_half_exact_spec (value : LocalM31)
    (hvalue : CanonicalLocalM31 value) :
    Exists fun result =>
      aspis_verifier.aspis_core.field.M31.half value = .ok result /\
      CanonicalLocalM31 result /\
      m31ToExact result = (2 : ExactM31)⁻¹ * m31ToExact value := by
  obtain ⟨result, hresult, hword⟩ := local_m31_half_word_spec value hvalue
  refine ⟨result, hresult, ?_, ?_⟩
  · change result.val < Modulus
    rw [hword]
    exact rawM31Half_canonical hvalue
  · have htwo : (2 : ExactM31) ≠ 0 := by
      change (2 : ZMod 2147483647) ≠ 0
      decide
    apply mul_left_cancel₀ htwo
    simp only [m31ToExact, hword]
    rw [rawM31Half_double hvalue]
    rw [← mul_assoc, mul_inv_cancel₀ htwo, one_mul]

theorem authentic_reduce_u64_word_spec (input : Std.U64) :
    Exists fun result : Std.U32 =>
      AuthenticFieldPow.field.reduce_u64 input = .ok result /\
      result.val = rawReduceU64 input.val := by
  unfold AuthenticFieldPow.field.reduce_u64
  rw [AuthenticFieldPow.field.P]
  simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
  let wideP : Std.U64 := UScalar.cast .U64 (2147483647#u32 : Std.U32)
  have hwideP : wideP.val = AspisV5ComponentCQM31TowerExact.P := by
    simp [wideP, AspisV5ComponentCQM31TowerExact.P]
  let low1 : Std.U64 := input &&& wideP
  have hlow1 : low1.val = input.val &&& AspisV5ComponentCQM31TowerExact.P := by
    simp [low1, hwideP]
  let high1 : Std.U64 := Std.U64.wrapping_shr input 31#u32
  have hhigh1 : high1.val = input.val >>> 31 := by
    change input.bv.toNat >>> (31 % 64) = input.val >>> 31
    simp
  let folded1 : Std.U64 := Std.U64.wrapping_add low1 high1
  have hfolded1 : folded1.val = foldBits input.val := by
    unfold folded1
    rw [Std.U64.wrapping_add_val_eq, hlow1, hhigh1]
    unfold foldBits
    apply Nat.mod_eq_of_lt
    have hinput : input.val < 2 ^ 64 := by
      simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using input.hSize
    have hfold := first_fold_lt input.val hinput
    exact hfold.trans (by norm_num [UScalar.size, Std.U64.size,
      Std.U64.numBits])
  let low2 : Std.U64 := folded1 &&& wideP
  have hlow2 : low2.val = folded1.val &&& AspisV5ComponentCQM31TowerExact.P := by
    simp [low2, hwideP]
  let high2 : Std.U64 := Std.U64.wrapping_shr folded1 31#u32
  have hhigh2 : high2.val = folded1.val >>> 31 := by
    change folded1.bv.toNat >>> (31 % 64) = folded1.val >>> 31
    simp
  let folded2 : Std.U64 := Std.U64.wrapping_add low2 high2
  have hfolded2 : folded2.val = foldBits (foldBits input.val) := by
    unfold folded2
    rw [Std.U64.wrapping_add_val_eq, hlow2, hhigh2, hfolded1]
    unfold foldBits
    apply Nat.mod_eq_of_lt
    have hinput : input.val < 2 ^ 64 := by
      simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using input.hSize
    have hfold := second_fold_lt_two_pow32 input.val hinput
    exact hfold.trans (by norm_num [UScalar.size, Std.U64.size,
      Std.U64.numBits])
  let output : Std.U32 := UScalar.cast .U32 folded2
  have houtput : output.val = truncU32 (foldBits (foldBits input.val)) := by
    change (folded2.bv.setWidth 32).toNat =
      foldBits (foldBits input.val) % 2 ^ 32
    rw [BitVec.toNat_setWidth, Std.U64.bv_toNat, hfolded2]
  change Exists fun result : Std.U32 =>
    (if output >= 2147483647#u32 then
      Result.ok (Std.U32.wrapping_sub output 2147483647#u32)
    else Result.ok output) = Result.ok result /\
      result.val = rawReduceU64 input.val
  have hpval : (2147483647#u32 : Std.U32).val =
      AspisV5ComponentCQM31TowerExact.P := by
    norm_num [AspisV5ComponentCQM31TowerExact.P]
  by_cases hhigh : AspisV5ComponentCQM31TowerExact.P ≤ output.val
  · have hcondition : output >= 2147483647#u32 := by
      apply (UScalar.le_equiv _ _).2
      simpa [hpval] using hhigh
    rw [if_pos hcondition]
    let result := Std.U32.wrapping_sub output 2147483647#u32
    refine ⟨result, rfl, ?_⟩
    have hresult : result.val =
        output.val - AspisV5ComponentCQM31TowerExact.P := by
      unfold result
      rw [Std.U32.wrapping_sub_val_eq, hpval]
      have houtputBound := output.hSize
      have hpBound := (2147483647#u32 : Std.U32).hSize
      have hrearrange :
          output.val +
              (UScalar.size .U32 - AspisV5ComponentCQM31TowerExact.P) =
            (output.val - AspisV5ComponentCQM31TowerExact.P) +
              UScalar.size .U32 := by
        omega
      rw [hrearrange, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hresult]
    unfold rawReduceU64 condSubP
    rw [← houtput, if_pos hhigh]
  · have hcondition : ¬ output >= 2147483647#u32 := by
      intro hge
      apply hhigh
      have hval := (UScalar.le_equiv _ _).1 hge
      simpa [hpval] using hval
    rw [if_neg hcondition]
    refine ⟨output, rfl, ?_⟩
    unfold rawReduceU64 condSubP
    rw [← houtput, if_neg hhigh]

end GoodMatricesCurrent.SourceExtractedField
