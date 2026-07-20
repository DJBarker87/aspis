import AspisCorePow
import QM31MulProof
import QM31SquareScalarsProof

/-!
# Source-authentic `QM31::pow`

The actual pow extraction has nominally distinct Rust structures from the two
authenticated QM31 kernel extractions.  Explicit structure/result adapters
transport the proved generated QM31 multiplication and optimized-square
capstones into the pow extraction before the generated binary loop is proved.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasQM31Pow

open AspisCorePow

abbrev M31Exact := AspisAeneasQM31Mul.M31Exact
abbrev CM31Exact := AspisAeneasQM31Mul.CM31Exact
abbrev QM31Exact := AspisAeneasQM31Mul.QM31Exact
abbrev m31Modulus : Nat := 2147483647

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def CanonicalCM31 (x : field.CM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : field.QM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31ToExact (x : field.CM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : field.QM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

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

@[simp] private theorem bind_mapResult {α β γ : Type}
    (f : α → β) (r : Result α) (k : β → Result γ) :
    (do let x ← mapResult f r; k x) =
      (do let x ← r; k (f x)) := by
  cases r <;> rfl

/-! ## Adapter to the generated QM31 multiplication capstone -/

private abbrev MulOldCM31 := AspisCoreCM31Multiplicative.field.CM31
private abbrev MulOldQM31 := AspisCoreCM31Multiplicative.field.QM31

private def toMulOldCM (x : field.CM31) : MulOldCM31 := ⟨x.a, x.b⟩
private def fromMulOldCM (x : MulOldCM31) : field.CM31 := ⟨x.a, x.b⟩
private def toMulOldQM (x : field.QM31) : MulOldQM31 :=
  ⟨toMulOldCM x.c0, toMulOldCM x.c1⟩
private def fromMulOldQM (x : MulOldQM31) : field.QM31 :=
  ⟨fromMulOldCM x.c0, fromMulOldCM x.c1⟩

private theorem mulOldPEq :
    field.P = AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold field.P AspisCoreCM31Multiplicative.field.P
  rfl

private theorem mulOldReduceEq (x : Std.U64) :
    field.reduce_u64 x = AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold field.reduce_u64 AspisCoreCM31Multiplicative.field.reduce_u64
  rw [mulOldPEq]

private theorem mulOldM31AddEq (x y : field.M31) :
    field.M31.add x y = AspisCoreCM31Multiplicative.field.M31.add x y := by
  unfold field.M31.add AspisCoreCM31Multiplicative.field.M31.add
  rw [mulOldPEq]

private theorem mulOldM31SubEq (x y : field.M31) :
    field.M31.sub x y = AspisCoreCM31Multiplicative.field.M31.sub x y := by
  unfold field.M31.sub AspisCoreCM31Multiplicative.field.M31.sub
  rw [mulOldPEq]

private theorem mulOldM31MulEq (x y : field.M31) :
    field.M31.mul x y = AspisCoreCM31Multiplicative.field.M31.mul x y := by
  unfold field.M31.mul AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [mulOldReduceEq]

private theorem mulOldM31DoubleEq (x : field.M31) :
    field.M31.double x = AspisCoreCM31Multiplicative.field.M31.double x := by
  unfold field.M31.double AspisCoreCM31Multiplicative.field.M31.double
  exact mulOldM31AddEq x x

private theorem mulOldCMAddBridge (x y : field.CM31) :
    field.CM31.add x y = mapResult fromMulOldCM
      (AspisCoreCM31Multiplicative.field.CM31.add
        (toMulOldCM x) (toMulOldCM y)) := by
  unfold field.CM31.add AspisCoreCM31Multiplicative.field.CM31.add
  simp only [mulOldM31AddEq, mapResult_bind, mapResult_ok,
    toMulOldCM, fromMulOldCM]

private theorem mulOldCMSubBridge (x y : field.CM31) :
    field.CM31.sub x y = mapResult fromMulOldCM
      (AspisCoreCM31Multiplicative.field.CM31.sub
        (toMulOldCM x) (toMulOldCM y)) := by
  unfold field.CM31.sub AspisCoreCM31Multiplicative.field.CM31.sub
  simp only [mulOldM31SubEq, mapResult_bind, mapResult_ok,
    toMulOldCM, fromMulOldCM]

private theorem mulOldCMMulBridge (x y : field.CM31) :
    field.CM31.mul x y = mapResult fromMulOldCM
      (AspisCoreCM31Multiplicative.field.CM31.mul
        (toMulOldCM x) (toMulOldCM y)) := by
  unfold field.CM31.mul AspisCoreCM31Multiplicative.field.CM31.mul
  simp only [mulOldM31AddEq, mulOldM31SubEq, mulOldM31MulEq,
    mapResult_bind, mapResult_ok, toMulOldCM, fromMulOldCM]

private theorem mulOldMulByRBridge (x : field.CM31) :
    field.mul_by_r x = mapResult fromMulOldCM
      (AspisCoreCM31Multiplicative.field.mul_by_r (toMulOldCM x)) := by
  unfold field.mul_by_r AspisCoreCM31Multiplicative.field.mul_by_r
  simp only [mulOldM31AddEq, mulOldM31SubEq, mulOldM31DoubleEq,
    mapResult_bind, mapResult_ok, toMulOldCM, fromMulOldCM]

private theorem generatedQM31MulBridge (x y : field.QM31) :
    field.QM31.mul x y = mapResult fromMulOldQM
      (AspisCoreCM31Multiplicative.field.QM31.mul
        (toMulOldQM x) (toMulOldQM y)) := by
  unfold field.QM31.mul AspisCoreCM31Multiplicative.field.QM31.mul
  simp only [mulOldCMMulBridge, mulOldCMAddBridge, mulOldCMSubBridge,
    mulOldMulByRBridge, bind_mapResult, mapResult_bind, mapResult_ok,
    toMulOldQM, fromMulOldQM, toMulOldCM, fromMulOldCM]

private theorem generatedQM31MulCorresponds
    (x y : field.QM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out : field.QM31,
      field.QM31.mul x y = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x * qm31ToExact y := by
  have hxOld : AspisAeneasQM31Mul.CanonicalQM31 (toMulOldQM x) := by
    simpa [toMulOldQM, toMulOldCM, CanonicalQM31, CanonicalCM31,
      CanonicalRawM31, AspisAeneasQM31Mul.CanonicalQM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hx
  have hyOld : AspisAeneasQM31Mul.CanonicalQM31 (toMulOldQM y) := by
    simpa [toMulOldQM, toMulOldCM, CanonicalQM31, CanonicalCM31,
      CanonicalRawM31, AspisAeneasQM31Mul.CanonicalQM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hy
  rcases AspisAeneasQM31Mul.extracted_qm31_mul_corresponds
      (toMulOldQM x) (toMulOldQM y) hxOld hyOld with
    ⟨outOld, houtOld, hcanonicalOld, hexactOld⟩
  refine ⟨fromMulOldQM outOld, ?_, ?_, ?_⟩
  · rw [generatedQM31MulBridge, houtOld]
    rfl
  · simpa [fromMulOldQM, fromMulOldCM, CanonicalQM31, CanonicalCM31,
      CanonicalRawM31, AspisAeneasQM31Mul.CanonicalQM31,
      AspisAeneasCM31Multiplicative.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hcanonicalOld
  · simpa [fromMulOldQM, fromMulOldCM, toMulOldQM, toMulOldCM,
      qm31ToExact, cm31ToExact, AspisAeneasQM31Mul.qm31ToExact,
      AspisAeneasQM31Mul.cm31ToExact] using hexactOld

/-! ## Adapter to the generated optimized QM31-square capstone -/

private abbrev SqOldCM31 := AspisLane5QM31SquareScalars.field.CM31
private abbrev SqOldQM31 := AspisLane5QM31SquareScalars.field.QM31

private def toSqOldCM (x : field.CM31) : SqOldCM31 := ⟨x.a, x.b⟩
private def fromSqOldCM (x : SqOldCM31) : field.CM31 := ⟨x.a, x.b⟩
private def toSqOldQM (x : field.QM31) : SqOldQM31 :=
  ⟨toSqOldCM x.c0, toSqOldCM x.c1⟩
private def fromSqOldQM (x : SqOldQM31) : field.QM31 :=
  ⟨fromSqOldCM x.c0, fromSqOldCM x.c1⟩

private theorem sqOldPEq : field.P = AspisLane5QM31SquareScalars.field.P := by
  apply UScalar.eq_of_val_eq
  unfold field.P AspisLane5QM31SquareScalars.field.P
  rfl

private theorem sqOldReduceEq (x : Std.U64) :
    field.reduce_u64 x = AspisLane5QM31SquareScalars.field.reduce_u64 x := by
  unfold field.reduce_u64 AspisLane5QM31SquareScalars.field.reduce_u64
  rw [sqOldPEq]

private theorem sqOldM31AddEq (x y : field.M31) :
    field.M31.add x y = AspisLane5QM31SquareScalars.field.M31.add x y := by
  unfold field.M31.add AspisLane5QM31SquareScalars.field.M31.add
  rw [sqOldPEq]

private theorem sqOldM31SubEq (x y : field.M31) :
    field.M31.sub x y = AspisLane5QM31SquareScalars.field.M31.sub x y := by
  unfold field.M31.sub AspisLane5QM31SquareScalars.field.M31.sub
  rw [sqOldPEq]

private theorem sqOldM31MulEq (x y : field.M31) :
    field.M31.mul x y = AspisLane5QM31SquareScalars.field.M31.mul x y := by
  unfold field.M31.mul AspisLane5QM31SquareScalars.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [sqOldReduceEq]

private theorem sqOldM31DoubleEq (x : field.M31) :
    field.M31.double x = AspisLane5QM31SquareScalars.field.M31.double x := by
  unfold field.M31.double AspisLane5QM31SquareScalars.field.M31.double
  exact sqOldM31AddEq x x

private theorem sqOldCMAddBridge (x y : field.CM31) :
    field.CM31.add x y = mapResult fromSqOldCM
      (AspisLane5QM31SquareScalars.field.CM31.add
        (toSqOldCM x) (toSqOldCM y)) := by
  unfold field.CM31.add AspisLane5QM31SquareScalars.field.CM31.add
  simp only [sqOldM31AddEq, mapResult_bind, mapResult_ok,
    toSqOldCM, fromSqOldCM]

private theorem sqOldCMMulBridge (x y : field.CM31) :
    field.CM31.mul x y = mapResult fromSqOldCM
      (AspisLane5QM31SquareScalars.field.CM31.mul
        (toSqOldCM x) (toSqOldCM y)) := by
  unfold field.CM31.mul AspisLane5QM31SquareScalars.field.CM31.mul
  simp only [sqOldM31AddEq, sqOldM31SubEq, sqOldM31MulEq,
    mapResult_bind, mapResult_ok, toSqOldCM, fromSqOldCM]

private theorem sqOldCMDoubleBridge (x : field.CM31) :
    field.CM31.double x = mapResult fromSqOldCM
      (AspisLane5QM31SquareScalars.field.CM31.double (toSqOldCM x)) := by
  unfold field.CM31.double AspisLane5QM31SquareScalars.field.CM31.double
  exact sqOldCMAddBridge x x

private theorem sqOldCMSquareBridge (x : field.CM31) :
    field.CM31.square x = mapResult fromSqOldCM
      (AspisLane5QM31SquareScalars.field.CM31.square (toSqOldCM x)) := by
  unfold field.CM31.square AspisLane5QM31SquareScalars.field.CM31.square
  simp only [sqOldM31AddEq, sqOldM31SubEq, sqOldM31MulEq,
    sqOldM31DoubleEq, mapResult_bind, mapResult_ok, toSqOldCM, fromSqOldCM]

private theorem sqOldMulByRBridge (x : field.CM31) :
    field.mul_by_r x = mapResult fromSqOldCM
      (AspisLane5QM31SquareScalars.field.mul_by_r (toSqOldCM x)) := by
  unfold field.mul_by_r AspisLane5QM31SquareScalars.field.mul_by_r
  simp only [sqOldM31AddEq, sqOldM31SubEq, sqOldM31DoubleEq,
    mapResult_bind, mapResult_ok, toSqOldCM, fromSqOldCM]

private theorem generatedQM31SquareBridge (x : field.QM31) :
    field.QM31.square x = mapResult fromSqOldQM
      (AspisLane5QM31SquareScalars.field.QM31.square (toSqOldQM x)) := by
  unfold field.QM31.square AspisLane5QM31SquareScalars.field.QM31.square
  simp only [sqOldCMSquareBridge, sqOldMulByRBridge, sqOldCMAddBridge,
    sqOldCMMulBridge, sqOldCMDoubleBridge, bind_mapResult,
    mapResult_bind, mapResult_ok, toSqOldQM, fromSqOldQM,
    toSqOldCM, fromSqOldCM]

private theorem generatedQM31SquareCorresponds
    (x : field.QM31) (hx : CanonicalQM31 x) :
    ∃ out : field.QM31,
      field.QM31.square x = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x * qm31ToExact x := by
  have hxOld : AspisLane5QM31SquareScalarsProof.CanonicalQM31 (toSqOldQM x) := by
    simpa [toSqOldQM, toSqOldCM, CanonicalQM31, CanonicalCM31,
      CanonicalRawM31, AspisLane5QM31SquareScalarsProof.CanonicalQM31,
      AspisLane5QM31SquareScalarsProof.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hx
  rcases AspisLane5QM31SquareScalarsProof.extracted_qm31_square_corresponds
      (toSqOldQM x) hxOld with
    ⟨outOld, houtOld, hcanonicalOld, _hseven, hexactOld⟩
  refine ⟨fromSqOldQM outOld, ?_, ?_, ?_⟩
  · rw [generatedQM31SquareBridge, houtOld]
    rfl
  · simpa [fromSqOldQM, fromSqOldCM, CanonicalQM31, CanonicalCM31,
      CanonicalRawM31, AspisLane5QM31SquareScalarsProof.CanonicalQM31,
      AspisLane5QM31SquareScalarsProof.CanonicalCM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31] using hcanonicalOld
  · apply QuadraticAlgebra.ext
    · have hre := congrArg QuadraticAlgebra.re hexactOld
      simpa [fromSqOldQM, fromSqOldCM, toSqOldQM, toSqOldCM,
        qm31ToExact, cm31ToExact,
        AspisLane5QM31SquareScalarsProof.qm31ToExact,
        AspisLane5QM31SquareScalarsProof.cm31ToExact,
        CM31Exact, AspisLane5QM31SquareScalarsProof.CM31Exact,
        AspisAeneasQM31Mul.CM31Exact,
        AspisLane5QM31SquareScalarsProof.qm31R,
        AspisAeneasQM31Mul.qm31R, QuadraticAlgebra.re_mul] using hre
    · have him := congrArg QuadraticAlgebra.im hexactOld
      simpa [fromSqOldQM, fromSqOldCM, toSqOldQM, toSqOldCM,
        qm31ToExact, cm31ToExact,
        AspisLane5QM31SquareScalarsProof.qm31ToExact,
        AspisLane5QM31SquareScalarsProof.cm31ToExact,
        CM31Exact, AspisLane5QM31SquareScalarsProof.CM31Exact,
        AspisAeneasQM31Mul.CM31Exact,
        AspisLane5QM31SquareScalarsProof.qm31R,
        AspisAeneasQM31Mul.qm31R, QuadraticAlgebra.im_mul] using him

/-! ## Generated binary-exponentiation loop -/

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

private theorem evenExponentStep (a b : QM31Exact) (n : Nat)
    (heven : n % 2 = 0) :
    a * (b * b) ^ (n / 2) = a * b ^ n := by
  have hdecomp : n % 2 + (n / 2) * 2 = n := Nat.mod_add_div' n 2
  have hn : n = 2 * (n / 2) := by omega
  calc
    a * (b * b) ^ (n / 2) = a * b ^ (2 * (n / 2)) := by
      rw [pow_mul]
      simp [pow_two]
    _ = a * b ^ n := (congrArg (fun k : Nat => a * b ^ k) hn).symm

private theorem oddExponentStep (a b : QM31Exact) (n : Nat)
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

def QM31PowInvariant (target : QM31Exact)
    (state : Std.U64 × field.QM31 × field.QM31) : Prop :=
  CanonicalQM31 state.2.1 ∧
  CanonicalQM31 state.2.2 ∧
  qm31ToExact state.2.2 * qm31ToExact state.2.1 ^ state.1.val = target

private theorem qm31PowLoopSpec
    (target : QM31Exact)
    (exp : Std.U64) (base acc : field.QM31)
    (hinv : QM31PowInvariant target (exp, base, acc)) :
    field.QM31.pow_loop exp base acc ⦃ out =>
      CanonicalQM31 out ∧ qm31ToExact out = target ⦄ := by
  unfold field.QM31.pow_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun state : Std.U64 × field.QM31 × field.QM31 => state.1.val)
    (inv := QM31PowInvariant target)
  · intro state hstate
    rcases state with ⟨currentExp, currentBase, currentAcc⟩
    change QM31PowInvariant target
      (currentExp, currentBase, currentAcc) at hstate
    rcases hstate with
      ⟨hbaseCanonical, haccCanonical, hstateExact⟩
    dsimp only
    unfold field.QM31.pow_loop.body
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
        rcases generatedQM31SquareCorresponds currentBase hbaseCanonical with
          ⟨baseNext, hbaseNext, hbaseNextCanonical, hbaseNextExact⟩
        rw [if_pos hpositive]
        simp only [Std.lift, bind_tc_ok]
        rw [if_neg hbitNotOne, hbaseNext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, QM31PowInvariant]
        refine ⟨⟨hbaseNextCanonical, haccCanonical, ?_⟩, ?_⟩
        · rw [hbaseNextExact, hshift]
          exact (evenExponentStep (qm31ToExact currentAcc)
            (qm31ToExact currentBase) currentExp.val heven).trans hstateExact
        · rw [hshift]
          exact hdecrease
      · have hbitOne : (currentExp &&& 1#u64) = 1#u64 := by
          apply UScalar.eq_of_val_eq
          norm_num [hbit, hodd]
        rcases generatedQM31MulCorresponds currentAcc currentBase
            haccCanonical hbaseCanonical with
          ⟨accNext, haccNext, haccNextCanonical, haccNextExact⟩
        rcases generatedQM31SquareCorresponds currentBase hbaseCanonical with
          ⟨baseNext, hbaseNext, hbaseNextCanonical, hbaseNextExact⟩
        rw [if_pos hpositive]
        simp only [Std.lift, bind_tc_ok]
        rw [if_pos hbitOne, haccNext, hbaseNext]
        simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok, QM31PowInvariant]
        refine ⟨⟨hbaseNextCanonical, haccNextCanonical, ?_⟩, ?_⟩
        · rw [haccNextExact, hbaseNextExact, hshift]
          exact (oddExponentStep (qm31ToExact currentAcc)
            (qm31ToExact currentBase) currentExp.val hodd).trans hstateExact
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

/-- The actual generated `QM31::pow` loop succeeds for every canonical
four-limb value and every Rust `u64` exponent, preserves all four canonical
limbs, and denotes exponentiation in the exact nested tower. -/
theorem extracted_qm31_pow_corresponds
    (x : field.QM31) (exp : Std.U64) (hx : CanonicalQM31 x) :
    ∃ out : field.QM31,
      field.QM31.pow x exp = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x ^ exp.val := by
  have hOneCanonical : CanonicalQM31 field.QM31.ONE := by
    norm_num [field.QM31.ONE, CanonicalQM31, CanonicalCM31,
      CanonicalRawM31, m31Modulus]
  have hOneExact : qm31ToExact field.QM31.ONE = 1 := by
    rw [field.QM31.ONE]
    rfl
  have hinv : QM31PowInvariant (qm31ToExact x ^ exp.val)
      (exp, x, field.QM31.ONE) := by
    refine ⟨hx, hOneCanonical, ?_⟩
    rw [hOneExact, one_mul]
  have hspec := qm31PowLoopSpec (qm31ToExact x ^ exp.val)
    exp x field.QM31.ONE hinv
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨out, hout, hcanonical, hexact⟩
  exact ⟨out, hout, hcanonical, hexact⟩

theorem extracted_qm31_pow_zero_tooth
    (x : field.QM31) (hx : CanonicalQM31 x) :
    ∃ out : field.QM31,
      field.QM31.pow x 0#u64 = ok out ∧
      CanonicalQM31 out ∧ qm31ToExact out = 1 := by
  simpa using extracted_qm31_pow_corresponds x 0#u64 hx

theorem extracted_qm31_pow_one_tooth
    (x : field.QM31) (hx : CanonicalQM31 x) :
    ∃ out : field.QM31,
      field.QM31.pow x 1#u64 = ok out ∧
      CanonicalQM31 out ∧ qm31ToExact out = qm31ToExact x := by
  simpa using extracted_qm31_pow_corresponds x 1#u64 hx

theorem canonical_qm31_pow_nonempty :
    ∃ x : field.QM31, CanonicalQM31 x := by
  refine ⟨⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩, ?_⟩
  norm_num [CanonicalQM31, CanonicalCM31, CanonicalRawM31, m31Modulus]

#print axioms extracted_qm31_pow_corresponds
#print axioms extracted_qm31_pow_zero_tooth
#print axioms extracted_qm31_pow_one_tooth
#print axioms canonical_qm31_pow_nonempty

end AspisAeneasQM31Pow
