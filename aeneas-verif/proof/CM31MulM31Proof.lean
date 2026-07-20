import CM31MultiplicativeProof

/-!
# Source-authentic CM31-by-M31 multiplication correspondence

This proof follows the two independent base-field multiplications in the
Aeneas translation of the deployed Rust `CM31::mul_m31` implementation.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31MulM31

open AspisAeneasCM31Exact
open AspisAeneasCM31Multiplicative

abbrev RustM31 := AspisCoreCM31Multiplicative.field.M31
abbrev RustCM31 := AspisCoreCM31Multiplicative.field.CM31

/-- Embed a base-field word in the real coordinate of the exact CM31 model. -/
def scalarExact (r : RustM31) : CM31Exact := ofRaw r.val 0

/-- The actual Rust scalar multiplication is canonical and equals
multiplication by the real embedding of the scalar. -/
theorem extracted_cm31_mul_m31_corresponds
    (x : RustCM31) (r : RustM31)
    (hx : CanonicalCM31 x) (hr : CanonicalRawM31 r.val) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.mul_m31 x r = ok out ∧
      CanonicalCM31 out ∧
      ((out.a.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (r.val : M31Exact) ∧
      ((out.b.val : Nat) : M31Exact) =
        (x.b.val : M31Exact) * (r.val : M31Exact) ∧
      toExact out = toExact x * scalarExact r := by
  rcases extracted_m31_mul_corresponds x.a r hx.1 hr with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases extracted_m31_mul_corresponds x.b r hx.2 hr with
    ⟨imaginary, himaginary, himaginaryCanonical, himaginaryExact⟩
  refine ⟨⟨real, imaginary⟩, ?_,
    ⟨hrealCanonical, himaginaryCanonical⟩,
    hrealExact, himaginaryExact, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.CM31.mul_m31,
      hreal, himaginary]
  · apply QuadraticAlgebra.ext
    · calc
        (toExact ⟨real, imaginary⟩).re =
            ((real.val : Nat) : M31Exact) := rfl
        _ = (x.a.val : M31Exact) * (r.val : M31Exact) := hrealExact
        _ = (toExact x * scalarExact r).re := by
          simp [toExact, scalarExact, ofRaw]
    · calc
        (toExact ⟨real, imaginary⟩).im =
            ((imaginary.val : Nat) : M31Exact) := rfl
        _ = (x.b.val : M31Exact) * (r.val : M31Exact) := himaginaryExact
        _ = (toExact x * scalarExact r).im := by
          simp [toExact, scalarExact, ofRaw]

/-! ## Concrete negative tooth -/

/-- The tempting but wrong scalar kernel that swaps the two CM31 limbs. -/
def wrongScalarLimbSwap (x : CM31Exact) (r : M31Exact) : CM31Exact :=
  ⟨x.im * r, x.re * r⟩

def exactOne : CM31Exact := ofRaw 1 0

/-- At `(1,0)` scaled by one, swapping limbs returns `(0,1)`. -/
theorem scalar_limb_order_is_load_bearing :
    wrongScalarLimbSwap exactOne 1 ≠ exactOne * exactOne := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  norm_num [wrongScalarLimbSwap, exactOne, ofRaw] at hre
  change (0 : ZMod 2147483647) = 1 at hre
  exact (by decide : (0 : ZMod 2147483647) ≠ 1) hre

#print axioms extracted_cm31_mul_m31_corresponds
#print axioms scalar_limb_order_is_load_bearing

end AspisAeneasCM31MulM31
