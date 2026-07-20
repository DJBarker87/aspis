import AspisCoreQm31SquareScalars
import CM31MultiplicativeProof
import QM31MulProof

/-!
# Source-authentic QM31 square and scalar kernels

The functions consumed below are the Aeneas definitions extracted directly
from the frozen `crates/aspis-core/src/field.rs`.  The exact target repeats
the two-line QM31 extension of the existing CM31 exact model (and is
definitionally the tower used by `QM31AddSubNegProof`):

* `M31Exact = ZMod (2^31 - 1)`;
* `CM31Exact = M31Exact[i] / (i^2 + 1)`;
* `QM31Exact = CM31Exact[u] / (u^2 - (2+i))`.

In particular, the square proof follows the generated two specialized CM31
squares, generated `mul_by_r`, and generated CM31 multiply/double cross term.
Its coordinate predicate exposes the seven deployed M31 products.
-/

open Aeneas Aeneas.Std Result

namespace AspisLane5QM31SquareScalarsProof

abbrev RustM31 := AspisLane5QM31SquareScalars.field.M31
abbrev RustCM31 := AspisLane5QM31SquareScalars.field.CM31
abbrev RustQM31 := AspisLane5QM31SquareScalars.field.QM31

abbrev M31Exact := AspisAeneasCM31Exact.M31Exact
abbrev CM31Exact := AspisAeneasCM31Exact.CM31Exact

abbrev qm31R : CM31Exact := AspisAeneasQM31Mul.qm31R

abbrev QM31Exact := AspisAeneasQM31Mul.QM31Exact

abbrev CanonicalRawM31 :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31

def CanonicalCM31 (x : RustCM31) : Prop :=
  CanonicalRawM31 x.a.val ∧ CanonicalRawM31 x.b.val

def CanonicalQM31 (x : RustQM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

def cm31ToExact (x : RustCM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

def qm31ToExact (x : RustQM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

def m31ToCM31Exact (r : RustM31) : CM31Exact :=
  ⟨(r.val : M31Exact), 0⟩

def embedM31 (r : RustM31) : QM31Exact :=
  ⟨m31ToCM31Exact r, 0⟩

def embedCM31 (r : RustCM31) : QM31Exact :=
  ⟨cm31ToExact r, 0⟩

/-! ## Transfer of the already kernel-checked M31 operations -/

private theorem P_eq_existing :
    AspisLane5QM31SquareScalars.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold AspisLane5QM31SquareScalars.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem m31_add_eq_existing (a b : RustM31) :
    AspisLane5QM31SquareScalars.field.M31.add a b =
      AspisCoreCM31Multiplicative.field.M31.add a b := by
  unfold AspisLane5QM31SquareScalars.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [P_eq_existing]

private theorem m31_sub_eq_existing (a b : RustM31) :
    AspisLane5QM31SquareScalars.field.M31.sub a b =
      AspisCoreCM31Multiplicative.field.M31.sub a b := by
  unfold AspisLane5QM31SquareScalars.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [P_eq_existing]

private theorem reduce_u64_eq_existing (x : Std.U64) :
    AspisLane5QM31SquareScalars.field.reduce_u64 x =
      AspisCoreCM31Multiplicative.field.reduce_u64 x := by
  unfold AspisLane5QM31SquareScalars.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [P_eq_existing]

private theorem m31_mul_eq_existing (a b : RustM31) :
    AspisLane5QM31SquareScalars.field.M31.mul a b =
      AspisCoreCM31Multiplicative.field.M31.mul a b := by
  unfold AspisLane5QM31SquareScalars.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [reduce_u64_eq_existing]

private theorem m31_add_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisLane5QM31SquareScalars.field.M31.add a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (b.val : M31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      a b ha hb with ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [m31_add_eq_existing]
  exact hout

private theorem m31_sub_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisLane5QM31SquareScalars.field.M31.sub a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) - (b.val : M31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      a b ha hb with ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [m31_sub_eq_existing]
  exact hout

private theorem m31_mul_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      AspisLane5QM31SquareScalars.field.M31.mul a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) * (b.val : M31Exact) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      a b ha hb with ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [m31_mul_eq_existing]
  exact hout

private theorem m31_double_corresponds
    (a : RustM31) (ha : CanonicalRawM31 a.val) :
    ∃ out : RustM31,
      AspisLane5QM31SquareScalars.field.M31.double a = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) + (a.val : M31Exact) := by
  rcases m31_add_corresponds a a ha ha with
    ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  simpa [AspisLane5QM31SquareScalars.field.M31.double] using hout

/-! ## Generated CM31 call-graph lemmas -/

private theorem cm31_add_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisLane5QM31SquareScalars.field.CM31.add x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x + cm31ToExact y := by
  rcases m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  let out : RustCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.CM31.add,
      hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem cm31_mul_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisLane5QM31SquareScalars.field.CM31.mul x y = ok out ∧
      CanonicalCM31 out ∧
      ((out.a.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (y.a.val : M31Exact) -
          (x.b.val : M31Exact) * (y.b.val : M31Exact) ∧
      ((out.b.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (y.b.val : M31Exact) +
          (x.b.val : M31Exact) * (y.a.val : M31Exact) ∧
      cm31ToExact out = cm31ToExact x * cm31ToExact y := by
  rcases m31_mul_corresponds x.a y.a hx.1 hy.1 with
    ⟨m0, hm0, hm0Can, hm0Exact⟩
  rcases m31_mul_corresponds x.b y.b hx.2 hy.2 with
    ⟨m1, hm1, hm1Can, hm1Exact⟩
  rcases m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨xsum, hxsum, hxsumCan, hxsumExact⟩
  rcases m31_add_corresponds y.a y.b hy.1 hy.2 with
    ⟨ysum, hysum, hysumCan, hysumExact⟩
  rcases m31_mul_corresponds xsum ysum hxsumCan hysumCan with
    ⟨m2, hm2, hm2Can, hm2Exact⟩
  rcases m31_sub_corresponds m0 m1 hm0Can hm1Can with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases m31_sub_corresponds m2 m0 hm2Can hm0Can with
    ⟨imagPartial, himagPartial, himagPartialCan, himagPartialExact⟩
  rcases m31_sub_corresponds imagPartial m1 himagPartialCan hm1Can with
    ⟨imag, himag, himagCan, himagExact⟩
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
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩,
    hrealCoordinate, himagCoordinate, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.CM31.mul,
      hm0, hm1, hxsum, hysum, hm2, hreal, himagPartial, himag]
  · apply QuadraticAlgebra.ext
    · simpa [cm31ToExact, sub_eq_add_neg] using hrealCoordinate
    · simpa [cm31ToExact] using himagCoordinate

private theorem cm31_square_corresponds
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ out : RustCM31,
      AspisLane5QM31SquareScalars.field.CM31.square x = ok out ∧
      CanonicalCM31 out ∧
      ((out.a.val : Nat) : M31Exact) =
        ((x.a.val : M31Exact) + (x.b.val : M31Exact)) *
          ((x.a.val : M31Exact) - (x.b.val : M31Exact)) ∧
      ((out.b.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (x.b.val : M31Exact) +
          (x.a.val : M31Exact) * (x.b.val : M31Exact) ∧
      cm31ToExact out = cm31ToExact x * cm31ToExact x := by
  rcases m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨sum, hsum, hsumCan, hsumExact⟩
  rcases m31_sub_corresponds x.a x.b hx.1 hx.2 with
    ⟨difference, hdifference, hdifferenceCan, hdifferenceExact⟩
  rcases m31_mul_corresponds sum difference hsumCan hdifferenceCan with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases m31_mul_corresponds x.a x.b hx.1 hx.2 with
    ⟨product, hproduct, hproductCan, hproductExact⟩
  rcases m31_double_corresponds product hproductCan with
    ⟨imag, himag, himagCan, himagExact⟩
  have hrealCoordinate :
      ((real.val : Nat) : M31Exact) =
        ((x.a.val : M31Exact) + (x.b.val : M31Exact)) *
          ((x.a.val : M31Exact) - (x.b.val : M31Exact)) := by
    rw [hrealExact, hsumExact, hdifferenceExact]
  have himagCoordinate :
      ((imag.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (x.b.val : M31Exact) +
          (x.a.val : M31Exact) * (x.b.val : M31Exact) := by
    rw [himagExact, hproductExact]
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩,
    hrealCoordinate, himagCoordinate, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.CM31.square,
      hsum, hdifference, hreal, hproduct, himag]
  · apply QuadraticAlgebra.ext
    · calc
        (cm31ToExact ⟨real, imag⟩).re =
            ((real.val : Nat) : M31Exact) := rfl
        _ = ((x.a.val : M31Exact) + (x.b.val : M31Exact)) *
              ((x.a.val : M31Exact) - (x.b.val : M31Exact)) :=
                hrealCoordinate
        _ = (cm31ToExact x * cm31ToExact x).re := by
          simp [cm31ToExact]
          ring
    · calc
        (cm31ToExact ⟨real, imag⟩).im =
            ((imag.val : Nat) : M31Exact) := rfl
        _ = (x.a.val : M31Exact) * (x.b.val : M31Exact) +
              (x.a.val : M31Exact) * (x.b.val : M31Exact) :=
                himagCoordinate
        _ = (cm31ToExact x * cm31ToExact x).im := by
          simp [cm31ToExact]
          ring

private theorem cm31_mul_m31_corresponds
    (x : RustCM31) (r : RustM31)
    (hx : CanonicalCM31 x) (hr : CanonicalRawM31 r.val) :
    ∃ out : RustCM31,
      AspisLane5QM31SquareScalars.field.CM31.mul_m31 x r = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x * m31ToCM31Exact r := by
  rcases m31_mul_corresponds x.a r hx.1 hr with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases m31_mul_corresponds x.b r hx.2 hr with
    ⟨imag, himag, himagCan, himagExact⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.CM31.mul_m31,
      hreal, himag]
  · apply QuadraticAlgebra.ext
    · simpa [cm31ToExact, m31ToCM31Exact] using hrealExact
    · simpa [cm31ToExact, m31ToCM31Exact] using himagExact

private theorem cm31_double_corresponds
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ out : RustCM31,
      AspisLane5QM31SquareScalars.field.CM31.double x = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x + cm31ToExact x := by
  rcases cm31_add_corresponds x x hx hx with
    ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  simpa [AspisLane5QM31SquareScalars.field.CM31.double] using hout

/-! `mul_by_r` is kept local to this lane so the square proof is independent
of the parallel QM31 multiplication lane. -/

theorem extracted_mul_by_r_corresponds
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ out : RustCM31,
      AspisLane5QM31SquareScalars.field.mul_by_r x = ok out ∧
      CanonicalCM31 out ∧
      ((out.a.val : Nat) : M31Exact) =
        ((x.a.val : M31Exact) + (x.a.val : M31Exact)) -
          (x.b.val : M31Exact) ∧
      ((out.b.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) +
          ((x.b.val : M31Exact) + (x.b.val : M31Exact)) ∧
      cm31ToExact out = qm31R * cm31ToExact x := by
  rcases m31_double_corresponds x.a hx.1 with
    ⟨doubleA, hdoubleA, hdoubleACan, hdoubleAExact⟩
  rcases m31_sub_corresponds doubleA x.b hdoubleACan hx.2 with
    ⟨real, hreal, hrealCan, hrealExact⟩
  rcases m31_double_corresponds x.b hx.2 with
    ⟨doubleB, hdoubleB, hdoubleBCan, hdoubleBExact⟩
  rcases m31_add_corresponds x.a doubleB hx.1 hdoubleBCan with
    ⟨imag, himag, himagCan, himagExact⟩
  have hrealCoordinate :
      ((real.val : Nat) : M31Exact) =
        ((x.a.val : M31Exact) + (x.a.val : M31Exact)) -
          (x.b.val : M31Exact) := by
    rw [hrealExact, hdoubleAExact]
  have himagCoordinate :
      ((imag.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) +
          ((x.b.val : M31Exact) + (x.b.val : M31Exact)) := by
    rw [himagExact, hdoubleBExact]
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCan, himagCan⟩,
    hrealCoordinate, himagCoordinate, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.mul_by_r,
      hdoubleA, hreal, hdoubleB, himag]
  · apply QuadraticAlgebra.ext
    · simp [cm31ToExact, qm31R, AspisAeneasQM31Mul.qm31R,
        hrealCoordinate]
      ring
    · simp [cm31ToExact, qm31R, AspisAeneasQM31Mul.qm31R,
        himagCoordinate]
      ring

/-! ## Exact seven-product QM31 square -/

def SevenM31ProductSquareCoordinates (x out : RustQM31) : Prop :=
  let a : M31Exact := x.c0.a.val
  let b : M31Exact := x.c0.b.val
  let c : M31Exact := x.c1.a.val
  let d : M31Exact := x.c1.b.val
  let p0 := (a + b) * (a - b)
  let p1 := a * b
  let p2 := (c + d) * (c - d)
  let p3 := c * d
  let p4 := a * c
  let p5 := b * d
  let p6 := (a + b) * (c + d)
  ((out.c0.a.val : Nat) : M31Exact) =
      p0 + (p2 + p2) - (p3 + p3) ∧
  ((out.c0.b.val : Nat) : M31Exact) =
      (p1 + p1) + p2 + ((p3 + p3) + (p3 + p3)) ∧
  ((out.c1.a.val : Nat) : M31Exact) =
      (p4 - p5) + (p4 - p5) ∧
  ((out.c1.b.val : Nat) : M31Exact) =
      ((p6 - p4) - p5) + ((p6 - p4) - p5)

/-- The generated optimized QM31 square succeeds for arbitrary canonical
limbs, returns four canonical limbs, exposes the deployed seven-M31-product
formula, and equals squaring in the exact nested tower. -/
theorem extracted_qm31_square_corresponds
    (x : RustQM31) (hx : CanonicalQM31 x) :
    ∃ out : RustQM31,
      AspisLane5QM31SquareScalars.field.QM31.square x = ok out ∧
      CanonicalQM31 out ∧
      SevenM31ProductSquareCoordinates x out ∧
      qm31ToExact out = qm31ToExact x * qm31ToExact x := by
  rcases cm31_square_corresponds x.c0 hx.1 with
    ⟨c0Square, hc0Square, hc0SquareCan,
      hc0SquareReal, hc0SquareImag, hc0SquareExact⟩
  rcases cm31_square_corresponds x.c1 hx.2 with
    ⟨c1Square, hc1Square, hc1SquareCan,
      hc1SquareReal, hc1SquareImag, hc1SquareExact⟩
  rcases extracted_mul_by_r_corresponds c1Square hc1SquareCan with
    ⟨rTimesC1Square, hrTimes, hrTimesCan,
      hrTimesReal, hrTimesImag, hrTimesExact⟩
  rcases cm31_add_corresponds
      c0Square rTimesC1Square hc0SquareCan hrTimesCan with
    ⟨low, hlow, hlowCan, hlowExact⟩
  rcases cm31_mul_corresponds x.c0 x.c1 hx.1 hx.2 with
    ⟨cross, hcross, hcrossCan, hcrossReal, hcrossImag, hcrossExact⟩
  rcases cm31_double_corresponds cross hcrossCan with
    ⟨high, hhigh, hhighCan, hhighExact⟩
  let out : RustQM31 := ⟨low, high⟩
  refine ⟨out, ?_, ⟨hlowCan, hhighCan⟩, ?_, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.QM31.square,
      hc0Square, hc1Square, hrTimes, hlow, hcross, hhigh, out]
  · unfold SevenM31ProductSquareCoordinates
    dsimp
    constructor
    · have hcoord := congrArg QuadraticAlgebra.re hlowExact
      simp [cm31ToExact, hrTimesReal, hc0SquareReal,
        hc1SquareReal, hc1SquareImag] at hcoord ⊢
      ring_nf at hcoord ⊢
      exact hcoord
    constructor
    · have hcoord := congrArg QuadraticAlgebra.im hlowExact
      simp [cm31ToExact, hrTimesImag, hc0SquareImag,
        hc1SquareReal, hc1SquareImag] at hcoord ⊢
      ring_nf at hcoord ⊢
      exact hcoord
    constructor
    · have hcoord := congrArg QuadraticAlgebra.re hhighExact
      simp [cm31ToExact, hcrossReal] at hcoord ⊢
      ring_nf at hcoord ⊢
      exact hcoord
    · have hcoord := congrArg QuadraticAlgebra.im hhighExact
      simp [cm31ToExact, hcrossImag] at hcoord ⊢
      ring_nf at hcoord ⊢
      exact hcoord
  · apply QuadraticAlgebra.ext
    · calc
        (qm31ToExact out).re = cm31ToExact low := rfl
        _ = cm31ToExact c0Square + cm31ToExact rTimesC1Square :=
          hlowExact
        _ = cm31ToExact x.c0 * cm31ToExact x.c0 +
              qm31R * (cm31ToExact x.c1 * cm31ToExact x.c1) := by
          rw [hc0SquareExact, hrTimesExact, hc1SquareExact]
        _ = (qm31ToExact x * qm31ToExact x).re := by
          rw [QuadraticAlgebra.re_mul]
          change cm31ToExact x.c0 * cm31ToExact x.c0 +
              qm31R * (cm31ToExact x.c1 * cm31ToExact x.c1) =
            cm31ToExact x.c0 * cm31ToExact x.c0 +
              qm31R * cm31ToExact x.c1 * cm31ToExact x.c1
          ring
    · calc
        (qm31ToExact out).im = cm31ToExact high := rfl
        _ = cm31ToExact cross + cm31ToExact cross := hhighExact
        _ = cm31ToExact x.c0 * cm31ToExact x.c1 +
              cm31ToExact x.c0 * cm31ToExact x.c1 := by
          rw [hcrossExact]
        _ = (qm31ToExact x * qm31ToExact x).im := by
          rw [QuadraticAlgebra.im_mul]
          change cm31ToExact x.c0 * cm31ToExact x.c1 +
              cm31ToExact x.c0 * cm31ToExact x.c1 =
            cm31ToExact x.c0 * cm31ToExact x.c1 +
              cm31ToExact x.c1 * cm31ToExact x.c0 +
                (0 : CM31Exact) * cm31ToExact x.c1 * cm31ToExact x.c1
          ring

/-! ## Generated scalar kernels -/

/-- The generated QM31-by-M31 kernel scales both tower blocks, preserves
canonicality, and equals multiplication by the embedded M31 value. -/
theorem extracted_qm31_mul_m31_corresponds
    (x : RustQM31) (r : RustM31)
    (hx : CanonicalQM31 x) (hr : CanonicalRawM31 r.val) :
    ∃ out : RustQM31,
      AspisLane5QM31SquareScalars.field.QM31.mul_m31 x r = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x * embedM31 r := by
  rcases cm31_mul_m31_corresponds x.c0 r hx.1 hr with
    ⟨low, hlow, hlowCan, hlowExact⟩
  rcases cm31_mul_m31_corresponds x.c1 r hx.2 hr with
    ⟨high, hhigh, hhighCan, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCan, hhighCan⟩, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.QM31.mul_m31,
      hlow, hhigh]
  · apply QuadraticAlgebra.ext
    · simpa [qm31ToExact, embedM31] using hlowExact
    · simpa [qm31ToExact, embedM31] using hhighExact

/-- The freshly generated QM31-by-CM31 kernel scales both tower blocks,
preserves canonicality, and equals multiplication by the embedded CM31
value. -/
theorem extracted_qm31_mul_cm31_corresponds
    (x : RustQM31) (r : RustCM31)
    (hx : CanonicalQM31 x) (hr : CanonicalCM31 r) :
    ∃ out : RustQM31,
      AspisLane5QM31SquareScalars.field.QM31.mul_cm31 x r = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x * embedCM31 r := by
  rcases cm31_mul_corresponds x.c0 r hx.1 hr with
    ⟨low, hlow, hlowCan, _hlowReal, _hlowImag, hlowExact⟩
  rcases cm31_mul_corresponds x.c1 r hx.2 hr with
    ⟨high, hhigh, hhighCan, _hhighReal, _hhighImag, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCan, hhighCan⟩, ?_⟩
  · simp [AspisLane5QM31SquareScalars.field.QM31.mul_cm31,
      hlow, hhigh]
  · apply QuadraticAlgebra.ext
    · simpa [qm31ToExact, embedCM31] using hlowExact
    · simpa [qm31ToExact, embedCM31] using hhighExact

/-! ## Concrete negative teeth -/

def wrongUndoubledCrossSquare (x : QM31Exact) : QM31Exact :=
  ⟨x.re * x.re + qm31R * (x.im * x.im), x.re * x.im⟩

def wrongRPlacementSquare (x : QM31Exact) : QM31Exact :=
  ⟨qm31R * (x.re * x.re) + x.im * x.im,
    x.re * x.im + x.re * x.im⟩

def swapTowerBlocks (x : QM31Exact) : QM31Exact := ⟨x.im, x.re⟩

def wrongOneBlockScalar (x : QM31Exact) (r : CM31Exact) : QM31Exact :=
  ⟨x.re * r, x.im⟩

def exactOneQM31 : QM31Exact := ⟨1, 0⟩

def exactU : QM31Exact := ⟨0, 1⟩

/-- Omitting the cross-term doubling changes the square at `1+u`. -/
theorem cross_term_doubling_is_load_bearing :
    wrongUndoubledCrossSquare (exactOneQM31 + exactU) ≠
      (exactOneQM31 + exactU) * (exactOneQM31 + exactU) := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.im.re) h
  norm_num [wrongUndoubledCrossSquare, exactOneQM31, exactU,
    qm31R] at hcoord
  change (1 : M31Exact) = 2 at hcoord
  exact (by decide : (1 : M31Exact) ≠ 2) hcoord

/-- Applying `R` to `c0^2` instead of `c1^2` changes `1^2`. -/
theorem mul_by_r_placement_is_load_bearing :
    wrongRPlacementSquare exactOneQM31 ≠ exactOneQM31 * exactOneQM31 := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.im) h
  norm_num [wrongRPlacementSquare, exactOneQM31, qm31R] at hcoord
  change (1 : M31Exact) = 0 at hcoord
  exact (by decide : (1 : M31Exact) ≠ 0) hcoord

/-- Swapping the returned `c0` and `c1` blocks changes `1^2`. -/
theorem square_tower_block_order_is_load_bearing :
    swapTowerBlocks (exactOneQM31 * exactOneQM31) ≠
      exactOneQM31 * exactOneQM31 := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.re) h
  norm_num [swapTowerBlocks, exactOneQM31] at hcoord
  change (0 : M31Exact) = 1 at hcoord
  exact (by decide : (0 : M31Exact) ≠ 1) hcoord

/-- Scaling only `c0` leaves the `u` block wrong for scalar two. -/
theorem scalar_must_reach_both_tower_blocks :
    wrongOneBlockScalar exactU (2 : CM31Exact) ≠
      exactU * (⟨(2 : CM31Exact), 0⟩ : QM31Exact) := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.im.re) h
  norm_num [wrongOneBlockScalar, exactU] at hcoord
  change (1 : M31Exact) = 2 at hcoord
  exact (by decide : (1 : M31Exact) ≠ 2) hcoord

/-! ## Kernel dependency audit -/

#print axioms extracted_mul_by_r_corresponds
#print axioms extracted_qm31_square_corresponds
#print axioms extracted_qm31_mul_m31_corresponds
#print axioms extracted_qm31_mul_cm31_corresponds
#print axioms cross_term_doubling_is_load_bearing
#print axioms mul_by_r_placement_is_load_bearing
#print axioms square_tower_block_order_is_load_bearing
#print axioms scalar_must_reach_both_tower_blocks

end AspisLane5QM31SquareScalarsProof
