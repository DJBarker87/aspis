import CM31MultiplicativeProof

/-!
# Source-authentic CM31 squaring correspondence

This proof follows the Aeneas translation of the deployed Rust `CM31::square`
call graph.  It uses the unified extraction's proved M31 operations and maps
the two canonical output words into `QuadraticAlgebra (ZMod P) (-1) 0`.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasCM31Square

open AspisAeneasCM31Exact
open AspisAeneasCM31Multiplicative

abbrev RustCM31 := AspisCoreCM31Multiplicative.field.CM31

/-- The actual optimized Rust square is canonical and equals multiplication
by itself in the exact quadratic-algebra model.  The two coordinate equations
make the subtraction order and imaginary-coordinate doubling explicit. -/
theorem extracted_cm31_square_corresponds
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.square x = ok out ∧
      CanonicalCM31 out ∧
      ((out.a.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (x.a.val : M31Exact) -
          (x.b.val : M31Exact) * (x.b.val : M31Exact) ∧
      ((out.b.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (x.b.val : M31Exact) +
          (x.a.val : M31Exact) * (x.b.val : M31Exact) ∧
      toExact out = toExact x * toExact x := by
  rcases extracted_m31_add_corresponds x.a x.b hx.1 hx.2 with
    ⟨sum, hsum, hsumCanonical, hsumExact⟩
  rcases extracted_m31_sub_corresponds x.a x.b hx.1 hx.2 with
    ⟨difference, hdifference, hdifferenceCanonical, hdifferenceExact⟩
  rcases extracted_m31_mul_corresponds
      sum difference hsumCanonical hdifferenceCanonical with
    ⟨real, hreal, hrealCanonical, hrealProduct⟩
  rcases extracted_m31_mul_corresponds x.a x.b hx.1 hx.2 with
    ⟨product, hproduct, hproductCanonical, hproductExact⟩
  rcases extracted_m31_double_corresponds product hproductCanonical with
    ⟨imaginary, himaginary, himaginaryCanonical, himaginaryDouble⟩
  have hrealExact :
      ((real.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (x.a.val : M31Exact) -
          (x.b.val : M31Exact) * (x.b.val : M31Exact) := by
    calc
      ((real.val : Nat) : M31Exact) =
          ((sum.val : Nat) : M31Exact) *
            ((difference.val : Nat) : M31Exact) := hrealProduct
      _ = ((x.a.val : M31Exact) + (x.b.val : M31Exact)) *
            ((x.a.val : M31Exact) - (x.b.val : M31Exact)) := by
              rw [hsumExact, hdifferenceExact]
      _ = (x.a.val : M31Exact) * (x.a.val : M31Exact) -
            (x.b.val : M31Exact) * (x.b.val : M31Exact) := by ring
  have himaginaryExact :
      ((imaginary.val : Nat) : M31Exact) =
        (x.a.val : M31Exact) * (x.b.val : M31Exact) +
          (x.a.val : M31Exact) * (x.b.val : M31Exact) := by
    calc
      ((imaginary.val : Nat) : M31Exact) =
          ((product.val : Nat) : M31Exact) +
            ((product.val : Nat) : M31Exact) := himaginaryDouble
      _ = (x.a.val : M31Exact) * (x.b.val : M31Exact) +
            (x.a.val : M31Exact) * (x.b.val : M31Exact) := by
              rw [hproductExact]
  refine ⟨⟨real, imaginary⟩, ?_,
    ⟨hrealCanonical, himaginaryCanonical⟩,
    hrealExact, himaginaryExact, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.CM31.square,
      hsum, hdifference, hreal, hproduct, himaginary]
  · apply QuadraticAlgebra.ext
    · calc
        (toExact ⟨real, imaginary⟩).re =
            ((real.val : Nat) : M31Exact) := rfl
        _ = (x.a.val : M31Exact) * (x.a.val : M31Exact) -
              (x.b.val : M31Exact) * (x.b.val : M31Exact) := hrealExact
        _ = (toExact x * toExact x).re := by
          simp [toExact, ofRaw]
          ring
    · calc
        (toExact ⟨real, imaginary⟩).im =
            ((imaginary.val : Nat) : M31Exact) := rfl
        _ = (x.a.val : M31Exact) * (x.b.val : M31Exact) +
              (x.a.val : M31Exact) * (x.b.val : M31Exact) :=
                himaginaryExact
        _ = (toExact x * toExact x).im := by
          simp [toExact, ofRaw]
          ring

/-! ## Concrete negative teeth -/

/-- The tempting but wrong square obtained by reversing `a - b`. -/
def wrongSubtractionOrderSquare (x : CM31Exact) : CM31Exact :=
  ⟨(x.re + x.im) * (x.im - x.re),
    x.re * x.im + x.re * x.im⟩

/-- Reversing the subtraction changes `i²` from `-1` to `+1`. -/
theorem subtraction_order_is_load_bearing :
    wrongSubtractionOrderSquare imaginaryUnit ≠
      imaginaryUnit * imaginaryUnit := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  norm_num [wrongSubtractionOrderSquare, imaginaryUnit] at hre
  change (1 : ZMod 2147483647) = -1 at hre
  exact (by decide : (1 : ZMod 2147483647) ≠ -1) hre

/-- The tempting but wrong square that forgets to double the cross product. -/
def wrongUndoubledSquare (x : CM31Exact) : CM31Exact :=
  ⟨(x.re + x.im) * (x.re - x.im), x.re * x.im⟩

def onePlusI : CM31Exact := ofRaw 1 1

/-- At `1+i`, omitting the double returns imaginary coordinate `1`, while the
true square has imaginary coordinate `2`. -/
theorem imaginary_doubling_is_load_bearing :
    wrongUndoubledSquare onePlusI ≠ onePlusI * onePlusI := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  norm_num [wrongUndoubledSquare, onePlusI, ofRaw] at him
  change (1 : ZMod 2147483647) = 2 at him
  exact (by decide : (1 : ZMod 2147483647) ≠ 2) him

#print axioms extracted_cm31_square_corresponds
#print axioms subtraction_order_is_load_bearing
#print axioms imaginary_doubling_is_load_bearing

end AspisAeneasCM31Square
