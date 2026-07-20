import AspisCoreCm31Multiplicative
import M31MulProof
import CM31ExactModel

/-!
# Source-authentic CM31 multiplicative correspondence

The generated definitions in this file come from the actual `CM31::mul`,
`CM31::square`, and `CM31::mul_m31` bodies in the tracked Rust source.  The
proof follows their M31 call graphs and maps the result into the exact
quadratic algebra `M31[i] / (i^2 + 1)`.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Multiplicative

open AspisAeneasCM31Exact

abbrev RustM31 := AspisCoreCM31Multiplicative.field.M31
abbrev RustCM31 := AspisCoreCM31Multiplicative.field.CM31

abbrev m31Modulus : Nat := 2147483647
abbrev u32Cardinality : Nat := 2 ^ 32

def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus

def CanonicalCM31 (x : RustCM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def toExact (x : RustCM31) : CM31Exact := ofRaw x.a.val x.b.val

@[simp] theorem extracted_P_val :
    AspisCoreCM31Multiplicative.field.P.val = m31Modulus := by
  unfold AspisCoreCM31Multiplicative.field.P
  rfl

theorem u32_size_eq : UScalar.size .U32 = u32Cardinality := by
  rw [UScalar.size_def, UScalarTy.U32_numBits_eq]

/-! ## Base-field addition in the unified extraction -/

theorem extracted_m31_add_eq_conditional (a b : RustM31) :
    AspisCoreCM31Multiplicative.field.M31.add a b =
      if m31Modulus ≤ (Std.U32.wrapping_add a b).val then
        ok (Std.U32.wrapping_sub
          (Std.U32.wrapping_add a b)
          AspisCoreCM31Multiplicative.field.P)
      else ok (Std.U32.wrapping_add a b) := by
  simp [AspisCoreCM31Multiplicative.field.M31.add, Std.lift]

theorem canonical_sum_lt_u32
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    a.val + b.val < u32Cardinality := by
  unfold CanonicalRawM31 at ha hb
  norm_num [m31Modulus, u32Cardinality] at ha hb ⊢
  omega

theorem wrapping_add_val_of_canonical
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U32.wrapping_add a b).val = a.val + b.val := by
  rw [Std.U32.wrapping_add_val_eq, u32_size_eq,
    Nat.mod_eq_of_lt (canonical_sum_lt_u32 a b ha hb)]

theorem wrapping_add_sub_P_val
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val)
    (hhigh : m31Modulus ≤ a.val + b.val) :
    (Std.U32.wrapping_sub
        (Std.U32.wrapping_add a b)
        AspisCoreCM31Multiplicative.field.P).val =
      a.val + b.val - m31Modulus := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val,
    wrapping_add_val_of_canonical a b ha hb]
  have hsum := canonical_sum_lt_u32 a b ha hb
  have hreduced : a.val + b.val - m31Modulus < u32Cardinality := by
    omega
  have hrewrite :
      a.val + b.val + (u32Cardinality - m31Modulus) =
        (a.val + b.val - m31Modulus) + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hreduced]

theorem extracted_m31_add_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisCoreCM31Multiplicative.field.M31.add a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (b.val : M31Exact) := by
  have hadd := wrapping_add_val_of_canonical a b ha hb
  by_cases hhigh : m31Modulus ≤ a.val + b.val
  · let out := Std.U32.wrapping_sub
      (Std.U32.wrapping_add a b)
      AspisCoreCM31Multiplicative.field.P
    have hbranch : m31Modulus ≤ (Std.U32.wrapping_add a b).val := by
      simpa [hadd] using hhigh
    have hout : out.val = a.val + b.val - m31Modulus :=
      wrapping_add_sub_P_val a b ha hb hhigh
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_add_eq_conditional, if_pos hbranch]
    · rw [hout]
      unfold CanonicalRawM31 at ha hb ⊢
      omega
    · rw [hout, Nat.cast_sub hhigh, Nat.cast_add,
        ZMod.natCast_self, sub_zero]
  · let out := Std.U32.wrapping_add a b
    have hbranch : ¬ m31Modulus ≤ (Std.U32.wrapping_add a b).val := by
      simpa [hadd] using hhigh
    have hout : out.val = a.val + b.val := hadd
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_add_eq_conditional, if_neg hbranch]
    · rw [hout]
      exact Nat.lt_of_not_ge hhigh
    · rw [hout, Nat.cast_add]

/-! ## Base-field subtraction in the unified extraction -/

theorem extracted_m31_sub_eq_conditional (a b : RustM31) :
    AspisCoreCM31Multiplicative.field.M31.sub a b =
      let sum := Std.U32.wrapping_add
        a AspisCoreCM31Multiplicative.field.P
      let shifted := Std.U32.wrapping_sub sum b
      if m31Modulus ≤ shifted.val then
        ok (Std.U32.wrapping_sub
          shifted AspisCoreCM31Multiplicative.field.P)
      else ok shifted := by
  simp [AspisCoreCM31Multiplicative.field.M31.sub, Std.lift]

theorem add_P_lt_u32
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    a.val + m31Modulus < u32Cardinality := by
  unfold CanonicalRawM31 at ha
  norm_num [m31Modulus, u32Cardinality] at ha ⊢
  omega

theorem wrapping_add_P_val
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    (Std.U32.wrapping_add
      a AspisCoreCM31Multiplicative.field.P).val =
      a.val + m31Modulus := by
  rw [Std.U32.wrapping_add_val_eq, u32_size_eq, extracted_P_val,
    Nat.mod_eq_of_lt (add_P_lt_u32 a ha)]

theorem shifted_sub_val
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    (Std.U32.wrapping_sub
      (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P)
      b).val = a.val + m31Modulus - b.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq,
    wrapping_add_P_val a ha]
  have hdiff : a.val + m31Modulus - b.val < u32Cardinality := by
    have := add_P_lt_u32 a ha
    omega
  have hb_u32 : b.val ≤ u32Cardinality := by
    unfold CanonicalRawM31 at hb
    norm_num [m31Modulus, u32Cardinality] at hb ⊢
    omega
  have hrewrite :
      a.val + m31Modulus + (u32Cardinality - b.val) =
        (a.val + m31Modulus - b.val) + u32Cardinality := by
    unfold CanonicalRawM31 at hb
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hdiff]

theorem shifted_high_iff
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    m31Modulus ≤
        (Std.U32.wrapping_sub
          (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P)
          b).val ↔
      b.val ≤ a.val := by
  rw [shifted_sub_val a b ha hb]
  unfold CanonicalRawM31 at hb
  omega

theorem high_sub_P_val
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val)
    (hhigh : b.val ≤ a.val) :
    (Std.U32.wrapping_sub
      (Std.U32.wrapping_sub
        (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P)
        b)
      AspisCoreCM31Multiplicative.field.P).val = a.val - b.val := by
  rw [Std.U32.wrapping_sub_val_eq, u32_size_eq, extracted_P_val,
    shifted_sub_val a b ha hb]
  have hshift :
      a.val + m31Modulus - b.val = a.val - b.val + m31Modulus := by
    omega
  rw [hshift]
  have hsmall : a.val - b.val < u32Cardinality := by
    unfold CanonicalRawM31 at ha
    norm_num [m31Modulus, u32Cardinality] at ha ⊢
    omega
  have hp_le_u32 : m31Modulus ≤ u32Cardinality := by
    norm_num [m31Modulus, u32Cardinality]
  have hrewrite :
      a.val - b.val + m31Modulus + (u32Cardinality - m31Modulus) =
        a.val - b.val + u32Cardinality := by
    omega
  rw [hrewrite, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

theorem extracted_m31_sub_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisCoreCM31Multiplicative.field.M31.sub a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) - (b.val : M31Exact) := by
  let shifted := Std.U32.wrapping_sub
    (Std.U32.wrapping_add a AspisCoreCM31Multiplicative.field.P) b
  by_cases hhigh : b.val ≤ a.val
  · let out := Std.U32.wrapping_sub
      shifted AspisCoreCM31Multiplicative.field.P
    have hbranch : m31Modulus ≤ shifted.val :=
      (shifted_high_iff a b ha hb).2 hhigh
    have hout : out.val = a.val - b.val :=
      high_sub_P_val a b ha hb hhigh
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_pos hbranch]
    · rw [hout]
      unfold CanonicalRawM31 at ha ⊢
      omega
    · rw [hout, Nat.cast_sub hhigh]
  · let out := shifted
    have hbranch : ¬ m31Modulus ≤ shifted.val := by
      intro h
      exact hhigh ((shifted_high_iff a b ha hb).1 h)
    have hout : out.val = a.val + m31Modulus - b.val :=
      shifted_sub_val a b ha hb
    have hb_le : b.val ≤ a.val + m31Modulus := by
      unfold CanonicalRawM31 at hb
      omega
    refine ⟨out, ?_, ?_, ?_⟩
    · rw [extracted_m31_sub_eq_conditional, if_neg hbranch]
    · rw [hout]
      unfold CanonicalRawM31 at hb ⊢
      omega
    · rw [hout, Nat.cast_sub hb_le, Nat.cast_add,
        ZMod.natCast_self, add_zero]

/-! ## Transfer of the already-proved generated M31 multiplication -/

theorem extracted_reduce_u64_eq_existing (x : Std.U64) :
    AspisCoreCM31Multiplicative.field.reduce_u64 x =
      AspisCoreMul.field.reduce_u64 x := by
  have hP : AspisCoreCM31Multiplicative.field.P =
      AspisCoreMul.field.P := by
    apply UScalar.eq_of_val_eq
    unfold AspisCoreCM31Multiplicative.field.P AspisCoreMul.field.P
    rfl
  unfold AspisCoreCM31Multiplicative.field.reduce_u64
    AspisCoreMul.field.reduce_u64
  rw [hP]

theorem extracted_m31_mul_eq_existing (a b : RustM31) :
    AspisCoreCM31Multiplicative.field.M31.mul a b =
      AspisCoreMul.field.M31.mul a b := by
  unfold AspisCoreCM31Multiplicative.field.M31.mul
    AspisCoreMul.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [extracted_reduce_u64_eq_existing]

theorem extracted_m31_mul_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisCoreCM31Multiplicative.field.M31.mul a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) * (b.val : M31Exact) := by
  have ha' : AspisAeneasM31Mul.CanonicalRawM31 a.val := ha
  have hb' : AspisAeneasM31Mul.CanonicalRawM31 b.val := hb
  rcases AspisAeneasM31Mul.extracted_m31_mul_corresponds
      a b ha' hb' with ⟨out, hout, _hraw, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [extracted_m31_mul_eq_existing]
  exact hout

theorem extracted_m31_double_corresponds
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    ∃ out : RustM31,
      AspisCoreCM31Multiplicative.field.M31.double a = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (a.val : M31Exact) := by
  rcases extracted_m31_add_corresponds a a ha ha with
    ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  exact hout

/-! ## Actual Rust CM31 Karatsuba multiplication -/

def KaratsubaCoordinates (x y out : RustCM31) : Prop :=
  ((out.a.val : Nat) : M31Exact) =
      (x.a.val : M31Exact) * (y.a.val : M31Exact) -
        (x.b.val : M31Exact) * (y.b.val : M31Exact) ∧
  ((out.b.val : Nat) : M31Exact) =
      (x.a.val : M31Exact) * (y.b.val : M31Exact) +
        (x.b.val : M31Exact) * (y.a.val : M31Exact)

/-- The Aeneas translation of the production Karatsuba body returns canonical
coordinates and is exactly multiplication in `M31[i] / (i^2 + 1)`. -/
theorem extracted_cm31_mul_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.mul x y = ok out ∧
      CanonicalCM31 out ∧
      KaratsubaCoordinates x y out ∧
      toExact out = toExact x * toExact y := by
  rcases extracted_m31_mul_corresponds x.a y.a hx.1 hy.1 with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases extracted_m31_mul_corresponds x.b y.b hx.2 hy.2 with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases extracted_m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨xsum, hxsum, hxsumCanonical, hxsumExact⟩
  rcases extracted_m31_add_corresponds y.a y.b hy.1 hy.2 with
    ⟨ysum, hysum, hysumCanonical, hysumExact⟩
  rcases extracted_m31_mul_corresponds
      xsum ysum hxsumCanonical hysumCanonical with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases extracted_m31_sub_corresponds
      m0 m1 hm0Canonical hm1Canonical with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases extracted_m31_sub_corresponds
      m2 m0 hm2Canonical hm0Canonical with
    ⟨imagPartial, himagPartial, himagPartialCanonical, himagPartialExact⟩
  rcases extracted_m31_sub_corresponds
      imagPartial m1 himagPartialCanonical hm1Canonical with
    ⟨imag, himag, himagCanonical, himagExact⟩
  have hrealCoordinate :
      ((real.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (y.a.val : M31Exact) -
          (x.b.val : M31Exact) * (y.b.val : M31Exact) := by
    rw [hrealExact, hm0Exact, hm1Exact]
  have himagCoordinate :
      ((imag.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (y.b.val : M31Exact) +
          (x.b.val : M31Exact) * (y.a.val : M31Exact) := by
    calc
      ((imag.val : Nat) : M31Exact) =
          ((imagPartial.val : Nat) : M31Exact) -
            ((m1.val : Nat) : M31Exact) := himagExact
      _ = (((m2.val : Nat) : M31Exact) -
            ((m0.val : Nat) : M31Exact)) -
            ((m1.val : Nat) : M31Exact) := by rw [himagPartialExact]
      _ = (((x.a.val : M31Exact) + (x.b.val : M31Exact)) *
            ((y.a.val : M31Exact) + (y.b.val : M31Exact)) -
            (x.a.val : M31Exact) * (y.a.val : M31Exact)) -
            (x.b.val : M31Exact) * (y.b.val : M31Exact) := by
          rw [hm2Exact, hxsumExact, hysumExact, hm0Exact, hm1Exact]
      _ = (x.a.val : M31Exact) * (y.b.val : M31Exact) +
            (x.b.val : M31Exact) * (y.a.val : M31Exact) := by ring
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCanonical, himagCanonical⟩,
    ⟨hrealCoordinate, himagCoordinate⟩, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.CM31.mul,
      hm0, hm1, hxsum, hysum, hm2, hreal, himagPartial, himag]
  · ext
    · simpa [toExact, ofRaw, sub_eq_add_neg] using hrealCoordinate
    · simpa [toExact, ofRaw] using himagCoordinate

/-! ## Concrete algebraic teeth -/

/-- Bug model that reverses the real Karatsuba subtraction `m0 - m1`. -/
def wrongSwappedRealSub (x y : CM31Exact) : CM31Exact :=
  ⟨x.im * y.im - x.re * y.re,
    x.re * y.im + x.im * y.re⟩

/-- Bug model that adds, rather than subtracts, the final `m1` in the
Karatsuba cross term. -/
def wrongCrossTermSign (x y : CM31Exact) : CM31Exact :=
  ⟨x.re * y.re - x.im * y.im,
    (x.re + x.im) * (y.re + y.im) - x.re * y.re + x.im * y.im⟩

theorem wrong_swapped_real_sub_breaks_at_i :
    wrongSwappedRealSub (ofRaw 0 1) (ofRaw 0 1) ≠
      ofRaw 0 1 * ofRaw 0 1 := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  norm_num [wrongSwappedRealSub, ofRaw] at hre
  change (1 : ZMod 2147483647) = -1 at hre
  exact (by decide : (1 : ZMod 2147483647) ≠ -1) hre

theorem wrong_cross_term_sign_breaks_at_i :
    wrongCrossTermSign (ofRaw 0 1) (ofRaw 0 1) ≠
      ofRaw 0 1 * ofRaw 0 1 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  norm_num [wrongCrossTermSign, ofRaw] at him
  change (2 : ZMod 2147483647) = 0 at him
  exact (by decide : (2 : ZMod 2147483647) ≠ 0) him

#print axioms extracted_reduce_u64_eq_existing
#print axioms extracted_m31_add_corresponds
#print axioms extracted_m31_sub_corresponds
#print axioms extracted_m31_mul_corresponds
#print axioms extracted_cm31_mul_corresponds
#print axioms wrong_swapped_real_sub_breaks_at_i
#print axioms wrong_cross_term_sign_breaks_at_i

end AspisAeneasCM31Multiplicative
