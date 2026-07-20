import AspisCorePow
import M31MulProof

/-!
# Source-authentic `M31::pow`

This file proves the actual Aeneas `loop` generated from the production binary
exponentiation body.  The invariant connects the generated accumulator, base,
and remaining `u64` exponent to exact M31 exponentiation.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31Pow

open AspisCorePow
open AspisAeneasM31ReduceU64

abbrev CanonicalRawM31 := AspisAeneasM31ReduceU64.CanonicalRawM31
abbrev M31Exact := AspisAeneasM31ReduceU64.M31Exact

private theorem namespacedReduceU64Eq (x : Std.U64) :
    field.reduce_u64 x = AspisCoreMul.field.reduce_u64 x := by
  have hP : field.P = AspisCoreMul.field.P := by
    apply UScalar.eq_of_val_eq
    unfold field.P AspisCoreMul.field.P
    rfl
  unfold field.reduce_u64 AspisCoreMul.field.reduce_u64
  rw [hP]

private theorem namespacedM31MulEq (x y : field.M31) :
    field.M31.mul x y = AspisCoreMul.field.M31.mul x y := by
  unfold field.M31.mul AspisCoreMul.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [namespacedReduceU64Eq]

private theorem generatedM31MulCorresponds
    (x y : field.M31)
    (hx : CanonicalRawM31 x.val) (hy : CanonicalRawM31 y.val) :
    ∃ out : field.M31,
      field.M31.mul x y = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (x.val : M31Exact) * (y.val : M31Exact) := by
  rcases AspisAeneasM31Mul.extracted_m31_mul_corresponds x y hx hy with
    ⟨out, hout, _hraw, hcanonical, hexact⟩
  exact ⟨out, namespacedM31MulEq x y ▸ hout, hcanonical, hexact⟩

private theorem shiftOneU64Val (x : Std.U64) :
    (Std.U64.wrapping_shr x 1#i32).val = x.val / 2 := by
  change
    (Std.U64.wrapping_shr x ((1#i32 : Std.I32) : Std.U32)).bv.toNat =
      x.bv.toNat / 2
  rw [halfShiftCountOne_exact, Std.U64.wrapping_shr_bv_eq,
    BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  norm_num

private theorem lowBitU64Val (x : Std.U64) :
    (x &&& 1#u64).val = x.val % 2 := by
  rw [UScalar.val_and]
  norm_num [Nat.and_one_is_mod]

private theorem divTwoLtSelf {n : Nat} (hn : 0 < n) : n / 2 < n := by
  omega

private theorem evenExponentStep (a b : M31Exact) (n : Nat)
    (heven : n % 2 = 0) :
    a * (b * b) ^ (n / 2) = a * b ^ n := by
  have hdecomp : n % 2 + (n / 2) * 2 = n := Nat.mod_add_div' n 2
  have hn : n = 2 * (n / 2) := by omega
  calc
    a * (b * b) ^ (n / 2) = a * b ^ (2 * (n / 2)) := by
      rw [pow_mul]
      simp [pow_two]
    _ = a * b ^ n := (congrArg (fun k : Nat => a * b ^ k) hn).symm

private theorem oddExponentStep (a b : M31Exact) (n : Nat)
    (hodd : n % 2 = 1) :
    (a * b) * (b * b) ^ (n / 2) = a * b ^ n := by
  have hdecomp : n % 2 + (n / 2) * 2 = n := Nat.mod_add_div' n 2
  have hn : n = 2 * (n / 2) + 1 := by omega
  calc
    (a * b) * (b * b) ^ (n / 2) =
        a * b ^ (2 * (n / 2) + 1) := by
      rw [pow_add, pow_mul]
      simp [pow_two]
      ac_rfl
    _ = a * b ^ n := (congrArg (fun k : Nat => a * b ^ k) hn).symm

def M31PowInvariant (target : M31Exact)
    (state : Std.U64 × field.M31 × field.M31) : Prop :=
  CanonicalRawM31 state.2.1.val ∧
  CanonicalRawM31 state.2.2.val ∧
  (state.2.2.val : M31Exact) *
      (state.2.1.val : M31Exact) ^ state.1.val = target

private theorem m31PowLoopSpec
    (target : M31Exact)
    (exp : Std.U64) (base acc : field.M31)
    (hinv : M31PowInvariant target (exp, base, acc)) :
    field.M31.pow_loop exp base acc ⦃ out =>
      CanonicalRawM31 out.val ∧ (out.val : M31Exact) = target ⦄ := by
  unfold field.M31.pow_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun state : Std.U64 × field.M31 × field.M31 => state.1.val)
    (inv := M31PowInvariant target)
  · intro state hstate
    rcases state with ⟨currentExp, currentBase, currentAcc⟩
    change M31PowInvariant target
      (currentExp, currentBase, currentAcc) at hstate
    rcases hstate with
      ⟨hbaseCanonical, haccCanonical, hstateExact⟩
    dsimp only
    unfold field.M31.pow_loop.body
    by_cases hpositive : currentExp > 0#u64
    · have hpositiveVal : 0 < currentExp.val := by simpa using hpositive
      have hshift :
          (Std.U64.wrapping_shr currentExp 1#i32).val =
            currentExp.val / 2 := shiftOneU64Val currentExp
      have hdecrease : currentExp.val / 2 < currentExp.val :=
        divTwoLtSelf hpositiveVal
      have hbit : (currentExp &&& 1#u64).val = currentExp.val % 2 :=
        lowBitU64Val currentExp
      have hmodlt : currentExp.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rcases (show currentExp.val % 2 = 0 ∨ currentExp.val % 2 = 1 by omega) with
        heven | hodd
      · have hbitNotOne : (currentExp &&& 1#u64) ≠ 1#u64 := by
          intro h
          have := congrArg UScalar.val h
          norm_num [hbit, heven] at this
        rcases generatedM31MulCorresponds currentBase currentBase
            hbaseCanonical hbaseCanonical with
          ⟨baseNext, hbaseNext, hbaseNextCanonical, hbaseNextExact⟩
        rw [if_pos hpositive]
        simp only [Std.lift, bind_tc_ok]
        rw [if_neg hbitNotOne, hbaseNext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, M31PowInvariant]
        refine ⟨⟨hbaseNextCanonical, haccCanonical, ?_⟩, ?_⟩
        · rw [hbaseNextExact, hshift]
          exact (evenExponentStep
            (currentAcc.val : M31Exact)
            (currentBase.val : M31Exact) currentExp.val heven).trans hstateExact
        · rw [hshift]
          exact hdecrease
      · have hbitOne : (currentExp &&& 1#u64) = 1#u64 := by
          apply UScalar.eq_of_val_eq
          norm_num [hbit, hodd]
        rcases generatedM31MulCorresponds currentAcc currentBase
            haccCanonical hbaseCanonical with
          ⟨accNext, haccNext, haccNextCanonical, haccNextExact⟩
        rcases generatedM31MulCorresponds currentBase currentBase
            hbaseCanonical hbaseCanonical with
          ⟨baseNext, hbaseNext, hbaseNextCanonical, hbaseNextExact⟩
        rw [if_pos hpositive]
        simp only [Std.lift, bind_tc_ok]
        rw [if_pos hbitOne, haccNext, hbaseNext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, M31PowInvariant]
        refine ⟨⟨hbaseNextCanonical, haccNextCanonical, ?_⟩, ?_⟩
        · rw [haccNextExact, hbaseNextExact, hshift]
          exact (oddExponentStep
            (currentAcc.val : M31Exact)
            (currentBase.val : M31Exact) currentExp.val hodd).trans hstateExact
        · rw [hshift]
          exact hdecrease
    · have hzero : currentExp.val = 0 := by
        have : ¬0 < currentExp.val := by simpa using hpositive
        omega
      rw [if_neg hpositive]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨haccCanonical, ?_⟩
      simpa [hzero] using hstateExact
  · exact hinv

/-- The actual generated `M31::pow` loop succeeds for every canonical base
and every Rust `u64` exponent, returns a canonical limb, and denotes exact
field exponentiation. -/
theorem extracted_m31_pow_corresponds
    (x : field.M31) (exp : Std.U64) (hx : CanonicalRawM31 x.val) :
    ∃ out : field.M31,
      field.M31.pow x exp = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (x.val : M31Exact) ^ exp.val := by
  have hOneCanonical : CanonicalRawM31 field.M31.ONE.val := by
    norm_num [field.M31.ONE, CanonicalRawM31,
      AspisAeneasM31ReduceU64.CanonicalRawM31, m31Modulus]
  have hinv : M31PowInvariant ((x.val : M31Exact) ^ exp.val)
      (exp, x, field.M31.ONE) := by
    refine ⟨hx, hOneCanonical, ?_⟩
    simp [field.M31.ONE]
  have hspec := m31PowLoopSpec ((x.val : M31Exact) ^ exp.val)
    exp x field.M31.ONE hinv
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, hout, hcanonical, hexact⟩

/-- Explicit exponent-zero generated-call tooth. -/
theorem extracted_m31_pow_zero_tooth
    (x : field.M31) (hx : CanonicalRawM31 x.val) :
    ∃ out : field.M31,
      field.M31.pow x 0#u64 = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = 1 := by
  simpa using extracted_m31_pow_corresponds x 0#u64 hx

/-- Explicit exponent-one generated-call tooth. -/
theorem extracted_m31_pow_one_tooth
    (x : field.M31) (hx : CanonicalRawM31 x.val) :
    ∃ out : field.M31,
      field.M31.pow x 1#u64 = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) = (x.val : M31Exact) := by
  simpa using extracted_m31_pow_corresponds x 1#u64 hx

#print axioms extracted_m31_pow_corresponds
#print axioms extracted_m31_pow_zero_tooth
#print axioms extracted_m31_pow_one_tooth

end AspisAeneasM31Pow
