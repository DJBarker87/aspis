import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Exact CM31 target used by the extracted Rust composition proofs

`QuadraticAlgebra R (-1) 0` is the literal pair representation whose second
basis element squares to `-1`.  Its two coordinates therefore match Rust's
`CM31 { a, b }` layout directly.
-/

namespace AspisAeneasCM31Exact

abbrev m31Modulus : Nat := 2147483647
abbrev M31Exact := ZMod m31Modulus
abbrev CM31Exact := QuadraticAlgebra M31Exact (-1) 0

/-- Embed two raw canonical M31 words as the literal real and imaginary
coordinates of the exact CM31 target. -/
def ofRaw (a b : Nat) : CM31Exact := ⟨a, b⟩

@[simp] theorem ofRaw_re (a b : Nat) : (ofRaw a b).re = (a : M31Exact) := rfl
@[simp] theorem ofRaw_im (a b : Nat) : (ofRaw a b).im = (b : M31Exact) := rfl

/-- Coordinate form of complex conjugation. -/
def conjugateExact (x : CM31Exact) : CM31Exact := ⟨x.re, -x.im⟩

/-- Coordinate form of multiplication by the quadratic basis element `i`. -/
def mulIExact (x : CM31Exact) : CM31Exact := ⟨-x.im, x.re⟩

/-- The quadratic basis element satisfying `i^2 = -1`. -/
def imaginaryUnit : CM31Exact := ⟨0, 1⟩

theorem mulIExact_eq_mul (x : CM31Exact) :
    mulIExact x = imaginaryUnit * x := by
  ext <;> simp [mulIExact, imaginaryUnit]

end AspisAeneasCM31Exact
