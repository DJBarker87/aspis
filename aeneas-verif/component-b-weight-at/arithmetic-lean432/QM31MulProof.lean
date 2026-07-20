import CM31MultiplicativeProof

/-!
# Source-authentic QM31 multiplication correspondence

The Rust operations in the two capstones are the Aeneas definitions generated
directly from the frozen `aspis-core/src/field.rs` source.  The target is the
same literal quadratic tower already used by `QM31AddSubNegProof`:

* `M31Exact = ZMod (2^31 - 1)`;
* `CM31Exact = M31Exact[i] / (i^2 + 1)`;
* `QM31Exact = CM31Exact[u] / (u^2 - (2 + i))`.

The inner two levels reuse `AspisAeneasCM31Exact` directly.  Importing
`QM31AddSubNegProof` itself is impossible in this extraction universe: its
unnamespaced additive generated module and the reduction module under the
multiplicative proof chain both declare `aspis_core.field.P`.  The only local
mathematical declarations are therefore the identical two-line outer tower
(`R = 2 + i` and `QuadraticAlgebra CM31Exact R 0`) plus the structure adapter.
The main proof follows the generated nested Karatsuba calls and the generated
`mul_by_r`; it does not replace them with a handwritten Rust model.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasQM31Mul

abbrev RustCM31 := AspisCoreCM31Multiplicative.field.CM31
abbrev RustQM31 := AspisCoreCM31Multiplicative.field.QM31
abbrev M31Exact := AspisAeneasCM31Exact.M31Exact
abbrev CM31Exact := AspisAeneasCM31Exact.CM31Exact

/-- The same non-residue declaration as `QM31AddSubNegProof.qm31R`. -/
def qm31R : CM31Exact := ⟨2, 1⟩

/-- The same exact outer tower as `QM31AddSubNegProof.QM31Exact`. -/
abbrev QM31Exact := QuadraticAlgebra CM31Exact qm31R 0

/-- The sole CM31 adapter from the multiplicative extraction into the exact
pair representation already used by the additive QM31 proof. -/
def cm31ToExact (x : RustCM31) : CM31Exact :=
  ⟨(x.a.val : M31Exact), (x.b.val : M31Exact)⟩

/-- The sole QM31 adapter from the multiplicative extraction into the existing
exact nested tower. -/
def qm31ToExact (x : RustQM31) : QM31Exact :=
  ⟨cm31ToExact x.c0, cm31ToExact x.c1⟩

abbrev CanonicalRawM31 := AspisAeneasCM31Multiplicative.CanonicalRawM31
abbrev CanonicalCM31 := AspisAeneasCM31Multiplicative.CanonicalCM31

def CanonicalQM31 (x : RustQM31) : Prop :=
  CanonicalCM31 x.c0 ∧ CanonicalCM31 x.c1

/-- A concrete witness that the canonical-input domain of the capstones is
nonempty. -/
theorem canonical_qm31_nonempty :
    ∃ x : RustQM31, CanonicalQM31 x := by
  refine ⟨⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩, ?_⟩
  norm_num [CanonicalQM31,
    AspisAeneasCM31Multiplicative.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem cm31ToExact_eq_existing (x : RustCM31) :
    cm31ToExact x = AspisAeneasCM31Multiplicative.toExact x := by
  rfl

private theorem extracted_cm31_add_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.add x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x + cm31ToExact y := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  let out : RustCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.CM31.add, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem extracted_cm31_sub_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.sub x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x - cm31ToExact y := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  let out : RustCM31 := ⟨oa, ob⟩
  refine ⟨out, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.CM31.sub, hcallA, hcallB, out]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

private theorem extracted_cm31_mul_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.mul x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x * cm31ToExact y := by
  rcases AspisAeneasCM31Multiplicative.extracted_cm31_mul_corresponds
      x y hx hy with
    ⟨out, hcall, hcanonical, _hcoordinates, hexact⟩
  exact ⟨out, hcall, hcanonical, by simpa [cm31ToExact_eq_existing] using hexact⟩

/-- The generated production helper implements `(a + bi) * (2 + i)` exactly;
the returned M31 limbs are canonical for every canonical input pair.  In
particular, this capstone fixes the deployed first coordinate as `2a - b`. -/
theorem extracted_mul_by_r_corresponds
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.mul_by_r x = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x * qm31R := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_double_corresponds
      x.a hx.1 with
    ⟨twoA, htwoA, hcanTwoA, hexactTwoA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      twoA x.b hcanTwoA hx.2 with
    ⟨real, hreal, hcanReal, hexactReal⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_double_corresponds
      x.b hx.2 with
    ⟨twoB, htwoB, hcanTwoB, hexactTwoB⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x.a twoB hx.1 hcanTwoB with
    ⟨imag, himag, hcanImag, hexactImag⟩
  refine ⟨⟨real, imag⟩, ?_, ⟨hcanReal, hcanImag⟩, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.mul_by_r,
      htwoA, hreal, htwoB, himag]
  · apply QuadraticAlgebra.ext
    · simp only [cm31ToExact, QuadraticAlgebra.re_mul,
        qm31R]
      rw [hexactReal, hexactTwoA]
      ring
    · simp only [cm31ToExact, QuadraticAlgebra.im_mul,
        qm31R]
      rw [hexactImag, hexactTwoB]
      ring

/-- The actual generated nested Karatsuba multiplication succeeds for every
pair of canonical four-limb inputs, returns four canonical limbs, and equals
multiplication in `CM31[u] / (u^2 - (2 + i))`. -/
theorem extracted_qm31_mul_corresponds
    (x y : RustQM31) (hx : CanonicalQM31 x) (hy : CanonicalQM31 y) :
    ∃ out : RustQM31,
      AspisCoreCM31Multiplicative.field.QM31.mul x y = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact x * qm31ToExact y := by
  rcases extracted_cm31_mul_corresponds x.c0 y.c0 hx.1 hy.1 with
    ⟨m0, hm0, hcanM0, hexactM0⟩
  rcases extracted_cm31_mul_corresponds x.c1 y.c1 hx.2 hy.2 with
    ⟨m1, hm1, hcanM1, hexactM1⟩
  rcases extracted_cm31_add_corresponds x.c0 x.c1 hx.1 hx.2 with
    ⟨xsum, hxsum, hcanXsum, hexactXsum⟩
  rcases extracted_cm31_add_corresponds y.c0 y.c1 hy.1 hy.2 with
    ⟨ysum, hysum, hcanYsum, hexactYsum⟩
  rcases extracted_cm31_mul_corresponds xsum ysum hcanXsum hcanYsum with
    ⟨m2, hm2, hcanM2, hexactM2⟩
  rcases extracted_mul_by_r_corresponds m1 hcanM1 with
    ⟨rM1, hrM1, hcanRM1, hexactRM1⟩
  rcases extracted_cm31_add_corresponds m0 rM1 hcanM0 hcanRM1 with
    ⟨low, hlow, hcanLow, hexactLow⟩
  rcases extracted_cm31_sub_corresponds m2 m0 hcanM2 hcanM0 with
    ⟨highPartial, hhighPartial, hcanHighPartial, hexactHighPartial⟩
  rcases extracted_cm31_sub_corresponds
      highPartial m1 hcanHighPartial hcanM1 with
    ⟨high, hhigh, hcanHigh, hexactHigh⟩
  have hlowTower :
      cm31ToExact low =
        cm31ToExact x.c0 * cm31ToExact y.c0 +
          qm31R * (cm31ToExact x.c1 * cm31ToExact y.c1) := by
    rw [hexactLow, hexactM0, hexactRM1, hexactM1]
    ring
  have hhighTower :
      cm31ToExact high =
        cm31ToExact x.c0 * cm31ToExact y.c1 +
          cm31ToExact x.c1 * cm31ToExact y.c0 := by
    calc
      cm31ToExact high =
          cm31ToExact highPartial - cm31ToExact m1 := hexactHigh
      _ = (cm31ToExact m2 - cm31ToExact m0) - cm31ToExact m1 := by
        rw [hexactHighPartial]
      _ = ((cm31ToExact x.c0 + cm31ToExact x.c1) *
            (cm31ToExact y.c0 + cm31ToExact y.c1) -
            cm31ToExact x.c0 * cm31ToExact y.c0) -
            cm31ToExact x.c1 * cm31ToExact y.c1 := by
        rw [hexactM2, hexactXsum, hexactYsum, hexactM0, hexactM1]
      _ = cm31ToExact x.c0 * cm31ToExact y.c1 +
            cm31ToExact x.c1 * cm31ToExact y.c0 := by ring
  refine ⟨⟨low, high⟩, ?_, ⟨hcanLow, hcanHigh⟩, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.QM31.mul,
      hm0, hm1, hxsum, hysum, hm2,
      hrM1, hlow, hhighPartial, hhigh]
  · apply QuadraticAlgebra.ext
    · change cm31ToExact low =
        cm31ToExact x.c0 * cm31ToExact y.c0 +
          qm31R * cm31ToExact x.c1 * cm31ToExact y.c1
      rw [hlowTower]
      ring
    · simpa [qm31ToExact] using hhighTower

/-! ## Concrete mutation teeth -/

/-- Bug formula obtained by changing the deployed `2a - b` to `2a + b`. -/
def wrongMulByRFirstSign (x : CM31Exact) : CM31Exact :=
  ⟨2 * x.re + x.im, x.re + 2 * x.im⟩

def exactI : CM31Exact := ⟨0, 1⟩

/-- The wrong sign in `2a - b` is observably different already at `x = i`. -/
theorem wrong_mul_by_r_first_sign_tooth :
    wrongMulByRFirstSign exactI ≠ exactI * qm31R := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  norm_num [wrongMulByRFirstSign, exactI, qm31R] at hre
  change (1 : M31Exact) = -1 at hre
  exact (by decide : (1 : M31Exact) ≠ -1) hre

/-- Bug formula obtained by reversing the final Karatsuba high-coordinate
subtraction: `m1 - (m2 - m0)` instead of `(m2 - m0) - m1`. -/
def wrongKaratsubaHighOrder (x y : QM31Exact) : QM31Exact :=
  ⟨x.re * y.re + qm31R * x.im * y.im,
    x.im * y.im - ((x.re + x.im) * (y.re + y.im) - x.re * y.re)⟩

def exactOuterOne : QM31Exact := ⟨1, 0⟩
def exactOuterU : QM31Exact := ⟨0, 1⟩

/-- Reversing the high-coordinate subtraction changes `1 * u` into a value
whose `u` coefficient is `-1`. -/
theorem wrong_karatsuba_high_order_tooth :
    wrongKaratsubaHighOrder exactOuterOne exactOuterU ≠
      exactOuterOne * exactOuterU := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.im.re) h
  norm_num [wrongKaratsubaHighOrder, exactOuterOne, exactOuterU,
    qm31R] at hcoord
  change (-1 : M31Exact) = 1 at hcoord
  exact (by decide : (-1 : M31Exact) ≠ 1) hcoord

/-- Bug post-processing that swaps the returned `c0` and `c1` tower blocks. -/
def swapTowerBlocks (x : QM31Exact) : QM31Exact := ⟨x.im, x.re⟩

/-- Swapping `c0` and `c1` changes the product `1 * 1`. -/
theorem wrong_c0_c1_swap_tooth :
    swapTowerBlocks (exactOuterOne * exactOuterOne) ≠
      exactOuterOne * exactOuterOne := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.re) h
  norm_num [swapTowerBlocks, exactOuterOne, qm31R] at hcoord
  exact (by decide : (0 : M31Exact) ≠ 1) hcoord

/-- The conjugated, incorrect candidate non-residue `2 - i`. -/
def wrongR : CM31Exact := ⟨2, -1⟩

/-- QM31 Karatsuba with the incorrect non-residue `2 - i`. -/
def wrongRKaratsuba (x y : QM31Exact) : QM31Exact :=
  ⟨x.re * y.re + wrongR * x.im * y.im,
    (x.re + x.im) * (y.re + y.im) - x.re * y.re - x.im * y.im⟩

/-- Replacing `R = 2 + i` by `2 - i` changes the defining product `u * u`. -/
theorem wrong_two_minus_i_nonresidue_tooth :
    wrongRKaratsuba exactOuterU exactOuterU ≠ exactOuterU * exactOuterU := by
  intro h
  have hcoord := congrArg (fun z : QM31Exact => z.re.im) h
  norm_num [wrongRKaratsuba, wrongR, exactOuterU, qm31R] at hcoord
  change (-1 : M31Exact) = 1 at hcoord
  exact (by decide : (-1 : M31Exact) ≠ 1) hcoord

/-! ## Kernel dependency audit -/

#print axioms extracted_mul_by_r_corresponds
#print axioms extracted_qm31_mul_corresponds
#print axioms canonical_qm31_nonempty
#print axioms wrong_mul_by_r_first_sign_tooth
#print axioms wrong_karatsuba_high_order_tooth
#print axioms wrong_c0_c1_swap_tooth
#print axioms wrong_two_minus_i_nonresidue_tooth

end AspisAeneasQM31Mul
