import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Nat.BitIndices

/-!
# Lightweight natural line-basis evaluator

These are the evaluator-facing declarations used by the source-extracted
Rust correspondence.  Matrix conversion algebra lives in
`CircleNaturalBasis`; keeping it separate avoids loading the full matrix
corpus into the executable proof.
-/

namespace AspisCircleTensorBinding

open Polynomial Polynomial.Chebyshev

variable {K : Type*} [CommRing K]

/-- The repeated doubling factor used by the Rust natural-basis evaluator. -/
def doubledFactor (x : K) : ℕ → K
  | 0 => x
  | bit + 1 => 2 * (doubledFactor x bit) ^ 2 - 1

/-- Repeated `2x²-1` is evaluation of the power-of-two Chebyshev factor. -/
theorem doubledFactor_eq_chebyshev (x : K) : ∀ bit : ℕ,
    doubledFactor x bit = (T K (2 ^ bit : ℕ)).eval x
  | 0 => by simp [doubledFactor]
  | bit + 1 => by
      rw [doubledFactor, doubledFactor_eq_chebyshev]
      rw [show (2 ^ (bit + 1) : ℕ) = 2 * 2 ^ bit by omega]
      change 2 * (T K (2 ^ bit : ℕ)).eval x ^ 2 - 1 =
        (T K ((2 : ℤ) * (2 ^ bit : ℕ))).eval x
      rw [T_mul, T_two, Polynomial.eval_comp]
      simp

/-- The real encoder's natural line basis polynomial. Its set bits select the
Chebyshev factors `T_(2^k)`, exactly matching the repeated `2x²-1` factors in
the circle FFT. -/
noncomputable def naturalLinePoly (K : Type*) [CommRing K] (index : ℕ) : K[X] :=
  ∏ bit ∈ index.bitIndices.toFinset, T K (2 ^ bit : ℕ)

/-- The product evaluator used by Rust is evaluation of `naturalLinePoly`. -/
def naturalLineValue (x : K) (index : ℕ) : K :=
  ∏ bit ∈ index.bitIndices.toFinset, doubledFactor x bit

theorem naturalLineValue_eq_eval (x : K) (index : ℕ) :
    naturalLineValue x index = (naturalLinePoly K index).eval x := by
  rw [naturalLineValue, naturalLinePoly, Polynomial.eval_prod]
  simp only [doubledFactor_eq_chebyshev]

end AspisCircleTensorBinding
