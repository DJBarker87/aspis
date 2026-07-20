import AspisCorePow
import CM31SquareProof

/-!
# Source-authentic `CM31::pow`

The generated pow module has its own nominal Rust structures, so this file
first transports the already-proved base-field kernels into that extraction
namespace, then follows the generated CM31 multiplication, optimized square,
and binary-exponentiation loop bodies.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Pow

open AspisCorePow
open AspisAeneasCM31Exact

abbrev M31Exact := AspisAeneasCM31Exact.M31Exact
abbrev CM31Exact := AspisAeneasCM31Exact.CM31Exact
abbrev m31Modulus : Nat := 2147483647

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def CanonicalCM31 (x : field.CM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def toExact (x : field.CM31) : CM31Exact := ofRaw x.a.val x.b.val

private theorem namespacedPEq :
    field.P = AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold field.P AspisCoreCM31Multiplicative.field.P
  rfl

private theorem namespacedReduceU64Eq (x : Std.U64) :
    field.reduce_u64 x = AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold field.reduce_u64 AspisCoreCM31Multiplicative.field.reduce_u64
  rw [namespacedPEq]

private theorem namespacedM31AddEq (x y : field.M31) :
    field.M31.add x y =
      AspisCoreCM31Multiplicative.field.M31.add x y := by
  unfold field.M31.add AspisCoreCM31Multiplicative.field.M31.add
  rw [namespacedPEq]

private theorem namespacedM31SubEq (x y : field.M31) :
    field.M31.sub x y =
      AspisCoreCM31Multiplicative.field.M31.sub x y := by
  unfold field.M31.sub AspisCoreCM31Multiplicative.field.M31.sub
  rw [namespacedPEq]

private theorem namespacedM31MulEq (x y : field.M31) :
    field.M31.mul x y =
      AspisCoreCM31Multiplicative.field.M31.mul x y := by
  unfold field.M31.mul AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [namespacedReduceU64Eq]

private theorem namespacedM31DoubleEq (x : field.M31) :
    field.M31.double x =
      AspisCoreCM31Multiplicative.field.M31.double x := by
  unfold field.M31.double AspisCoreCM31Multiplicative.field.M31.double
  exact namespacedM31AddEq x x

private abbrev OldCM31 := AspisCoreCM31Multiplicative.field.CM31

private def toOld (x : field.CM31) : OldCM31 := ⟨x.a, x.b⟩
private def fromOld (x : OldCM31) : field.CM31 := ⟨x.a, x.b⟩

private def mapResult {α β : Type} (f : α → β) (r : Result α) : Result β :=
  match r with
  | ok x => ok (f x)
  | fail e => fail e
  | div => div

@[simp] private theorem mapResult_ok {α β : Type} (f : α → β) (x : α) :
    mapResult f (ok x) = ok (f x) := rfl

@[simp] private theorem mapResult_bind {α β γ : Type}
    (f : β → γ) (r : Result α) (k : α → Result β) :
    mapResult f (do let x ← r; k x) =
      (do let x ← r; mapResult f (k x)) := by
  cases r <;> rfl

private theorem generatedCM31MulBridge (x y : field.CM31) :
    field.CM31.mul x y =
      mapResult fromOld
        (AspisCoreCM31Multiplicative.field.CM31.mul (toOld x) (toOld y)) := by
  unfold field.CM31.mul AspisCoreCM31Multiplicative.field.CM31.mul
  simp only [namespacedM31MulEq, namespacedM31AddEq,
    namespacedM31SubEq, mapResult_bind, mapResult_ok, toOld, fromOld]

private theorem generatedCM31SquareBridge (x : field.CM31) :
    field.CM31.square x =
      mapResult fromOld
        (AspisCoreCM31Multiplicative.field.CM31.square (toOld x)) := by
  unfold field.CM31.square AspisCoreCM31Multiplicative.field.CM31.square
  simp only [namespacedM31AddEq, namespacedM31SubEq, namespacedM31MulEq,
    namespacedM31DoubleEq, mapResult_bind, mapResult_ok, toOld, fromOld]

private theorem generatedCM31MulCorresponds
    (x y : field.CM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : field.CM31,
      field.CM31.mul x y = ok out ∧
      CanonicalCM31 out ∧
      toExact out = toExact x * toExact y := by
  have hxOld : AspisAeneasCM31Multiplicative.CanonicalCM31 (toOld x) := by
    simpa [toOld, CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      CanonicalRawM31, AspisAeneasCM31Multiplicative.CanonicalRawM31] using hx
  have hyOld : AspisAeneasCM31Multiplicative.CanonicalCM31 (toOld y) := by
    simpa [toOld, CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      CanonicalRawM31, AspisAeneasCM31Multiplicative.CanonicalRawM31] using hy
  rcases AspisAeneasCM31Multiplicative.extracted_cm31_mul_corresponds
      (toOld x) (toOld y) hxOld hyOld with
    ⟨outOld, houtOld, hcanonicalOld, _hcoordinates, hexactOld⟩
  refine ⟨fromOld outOld, ?_, ?_, ?_⟩
  · rw [generatedCM31MulBridge, houtOld]
    rfl
  · simpa [fromOld, CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      CanonicalRawM31, AspisAeneasCM31Multiplicative.CanonicalRawM31]
      using hcanonicalOld
  · simpa [fromOld, toOld, toExact,
      AspisAeneasCM31Multiplicative.toExact] using hexactOld

private theorem generatedCM31SquareCorresponds
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.square x = ok out ∧
      CanonicalCM31 out ∧
      toExact out = toExact x * toExact x := by
  have hxOld : AspisAeneasCM31Multiplicative.CanonicalCM31 (toOld x) := by
    simpa [toOld, CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      CanonicalRawM31, AspisAeneasCM31Multiplicative.CanonicalRawM31] using hx
  rcases AspisAeneasCM31Square.extracted_cm31_square_corresponds
      (toOld x) hxOld with
    ⟨outOld, houtOld, hcanonicalOld, _hreal, _himag, hexactOld⟩
  refine ⟨fromOld outOld, ?_, ?_, ?_⟩
  · rw [generatedCM31SquareBridge, houtOld]
    rfl
  · simpa [fromOld, CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      CanonicalRawM31, AspisAeneasCM31Multiplicative.CanonicalRawM31]
      using hcanonicalOld
  · simpa [fromOld, toOld, toExact,
      AspisAeneasCM31Multiplicative.toExact] using hexactOld

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

private theorem evenExponentStep (a b : CM31Exact) (n : Nat)
    (heven : n % 2 = 0) :
    a * (b * b) ^ (n / 2) = a * b ^ n := by
  have hdecomp : n % 2 + (n / 2) * 2 = n := Nat.mod_add_div' n 2
  have hn : n = 2 * (n / 2) := by omega
  calc
    a * (b * b) ^ (n / 2) = a * b ^ (2 * (n / 2)) := by
      rw [pow_mul]
      simp [pow_two]
    _ = a * b ^ n := (congrArg (fun k : Nat => a * b ^ k) hn).symm

private theorem oddExponentStep (a b : CM31Exact) (n : Nat)
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

def CM31PowInvariant (target : CM31Exact)
    (state : Std.U64 × field.CM31 × field.CM31) : Prop :=
  CanonicalCM31 state.2.1 ∧
  CanonicalCM31 state.2.2 ∧
  toExact state.2.2 * toExact state.2.1 ^ state.1.val = target

private theorem cm31PowLoopSpec
    (target : CM31Exact)
    (exp : Std.U64) (base acc : field.CM31)
    (hinv : CM31PowInvariant target (exp, base, acc)) :
    field.CM31.pow_loop exp base acc ⦃ out =>
      CanonicalCM31 out ∧ toExact out = target ⦄ := by
  unfold field.CM31.pow_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun state : Std.U64 × field.CM31 × field.CM31 => state.1.val)
    (inv := CM31PowInvariant target)
  · intro state hstate
    rcases state with ⟨currentExp, currentBase, currentAcc⟩
    change CM31PowInvariant target
      (currentExp, currentBase, currentAcc) at hstate
    rcases hstate with
      ⟨hbaseCanonical, haccCanonical, hstateExact⟩
    dsimp only
    unfold field.CM31.pow_loop.body
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
        rcases generatedCM31SquareCorresponds currentBase hbaseCanonical with
          ⟨baseNext, hbaseNext, hbaseNextCanonical, hbaseNextExact⟩
        rw [if_pos hpositive]
        simp only [Std.lift, bind_tc_ok]
        rw [if_neg hbitNotOne, hbaseNext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, CM31PowInvariant]
        refine ⟨⟨hbaseNextCanonical, haccCanonical, ?_⟩, ?_⟩
        · rw [hbaseNextExact, hshift]
          exact (evenExponentStep (toExact currentAcc)
            (toExact currentBase) currentExp.val heven).trans hstateExact
        · rw [hshift]
          exact hdecrease
      · have hbitOne : (currentExp &&& 1#u64) = 1#u64 := by
          apply UScalar.eq_of_val_eq
          norm_num [hbit, hodd]
        rcases generatedCM31MulCorresponds currentAcc currentBase
            haccCanonical hbaseCanonical with
          ⟨accNext, haccNext, haccNextCanonical, haccNextExact⟩
        rcases generatedCM31SquareCorresponds currentBase hbaseCanonical with
          ⟨baseNext, hbaseNext, hbaseNextCanonical, hbaseNextExact⟩
        rw [if_pos hpositive]
        simp only [Std.lift, bind_tc_ok]
        rw [if_pos hbitOne, haccNext, hbaseNext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, CM31PowInvariant]
        refine ⟨⟨hbaseNextCanonical, haccNextCanonical, ?_⟩, ?_⟩
        · rw [haccNextExact, hbaseNextExact, hshift]
          exact (oddExponentStep (toExact currentAcc)
            (toExact currentBase) currentExp.val hodd).trans hstateExact
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

/-- The actual generated `CM31::pow` loop succeeds for every canonical pair
and every Rust `u64` exponent, returns canonical limbs, and denotes exact
quadratic-extension exponentiation. -/
theorem extracted_cm31_pow_corresponds
    (x : field.CM31) (exp : Std.U64) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.pow x exp = ok out ∧
      CanonicalCM31 out ∧
      toExact out = toExact x ^ exp.val := by
  have hOneCanonical : CanonicalCM31 field.CM31.ONE := by
    norm_num [field.CM31.ONE, CanonicalCM31, CanonicalRawM31, m31Modulus]
  have hOneExact : toExact field.CM31.ONE = 1 := by
    rw [field.CM31.ONE]
    rfl
  have hinv : CM31PowInvariant (toExact x ^ exp.val)
      (exp, x, field.CM31.ONE) := by
    refine ⟨hx, hOneCanonical, ?_⟩
    rw [hOneExact, one_mul]
  have hspec := cm31PowLoopSpec (toExact x ^ exp.val)
    exp x field.CM31.ONE hinv
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, hout, hcanonical, hexact⟩

theorem extracted_cm31_pow_zero_tooth
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.pow x 0#u64 = ok out ∧
      CanonicalCM31 out ∧ toExact out = 1 := by
  simpa using extracted_cm31_pow_corresponds x 0#u64 hx

theorem extracted_cm31_pow_one_tooth
    (x : field.CM31) (hx : CanonicalCM31 x) :
    ∃ out : field.CM31,
      field.CM31.pow x 1#u64 = ok out ∧
      CanonicalCM31 out ∧ toExact out = toExact x := by
  simpa using extracted_cm31_pow_corresponds x 1#u64 hx

#print axioms extracted_cm31_pow_corresponds
#print axioms extracted_cm31_pow_zero_tooth
#print axioms extracted_cm31_pow_one_tooth

end AspisAeneasCM31Pow
