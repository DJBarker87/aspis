import Mathlib

/-!
# Exact radix-eight evaluation of the atomic theta composition

The deployed atomic-v3 composition has four packed Poseidon coefficients,
twenty packed semantic coefficients, and the copy constraint as the leading
coefficient.  The deployed Rust evaluates those twenty-five coefficients by
Horner's rule.  A measured candidate grouped the first twenty-four
coefficients into three radix-eight blocks and left the copy coefficient at
degree 24.  The candidate was exact but was rejected after SBF measurement:
it saved only 706 CU and had a poor code-size footprint.  The deployed Horner
evaluator is unchanged.

This file proves the regrouping over an arbitrary commutative semiring.  It is
therefore an exact field identity: it does not rely on bounds, probability, or
an approximation specific to M31.
-/

namespace AspisAtomicThetaRadix8

variable {K : Type*} [CommSemiring K]

/-- The exact low-to-high coefficient order used by the original Horner loop.
The final `copy` argument is the initial Horner accumulator, hence the
coefficient of `theta^24`. -/
def atomicThetaPrefix (poseidon : Fin 4 → K) (semantic : Fin 20 → K) : List K :=
  [poseidon 0, poseidon 1, poseidon 2, poseidon 3,
   semantic 0, semantic 1, semantic 2, semantic 3,
   semantic 4, semantic 5, semantic 6, semantic 7,
   semantic 8, semantic 9, semantic 10, semantic 11,
   semantic 12, semantic 13, semantic 14, semantic 15,
   semantic 16, semantic 17, semantic 18, semantic 19]

/-- The original 24-step Horner evaluation, written in the same direction as
the Rust reverse iterators. -/
def atomicThetaHorner (poseidon : Fin 4 → K) (semantic : Fin 20 → K)
    (copy theta : K) : K :=
  (atomicThetaPrefix poseidon semantic).foldr
    (fun coefficient accumulator ↦ coefficient + theta * accumulator) copy

/-- Degrees 0 through 7: all four Poseidon coefficients and semantic 0..3. -/
def atomicThetaBlock0 (poseidon : Fin 4 → K) (semantic : Fin 20 → K)
    (theta : K) : K :=
  poseidon 0 + theta * poseidon 1 + theta ^ 2 * poseidon 2 +
    theta ^ 3 * poseidon 3 + theta ^ 4 * semantic 0 +
    theta ^ 5 * semantic 1 + theta ^ 6 * semantic 2 +
    theta ^ 7 * semantic 3

/-- Degrees 8 through 15, with the common `theta^8` factored out. -/
def atomicThetaBlock1 (semantic : Fin 20 → K) (theta : K) : K :=
  semantic 4 + theta * semantic 5 + theta ^ 2 * semantic 6 +
    theta ^ 3 * semantic 7 + theta ^ 4 * semantic 8 +
    theta ^ 5 * semantic 9 + theta ^ 6 * semantic 10 +
    theta ^ 7 * semantic 11

/-- Degrees 16 through 23, with the common `theta^16` factored out. -/
def atomicThetaBlock2 (semantic : Fin 20 → K) (theta : K) : K :=
  semantic 12 + theta * semantic 13 + theta ^ 2 * semantic 14 +
    theta ^ 3 * semantic 15 + theta ^ 4 * semantic 16 +
    theta ^ 5 * semantic 17 + theta ^ 6 * semantic 18 +
    theta ^ 7 * semantic 19

/-- The three-block radix-eight candidate that was measured and rejected. -/
def atomicThetaRadix8 (poseidon : Fin 4 → K) (semantic : Fin 20 → K)
    (copy theta : K) : K :=
  atomicThetaBlock0 poseidon semantic theta + theta ^ 8 *
    (atomicThetaBlock1 semantic theta + theta ^ 8 *
      (atomicThetaBlock2 semantic theta + theta ^ 8 * copy))

omit [CommSemiring K] in
@[simp]
theorem atomicThetaPrefix_length (poseidon : Fin 4 → K) (semantic : Fin 20 → K) :
    (atomicThetaPrefix poseidon semantic).length = 24 := by
  rfl

/-- Radix eight is exactly the original Horner polynomial, with coefficient
order

`poseidon[0..4] || semantic[0..20] || [copy]`.
-/
theorem atomicThetaRadix8_eq_originalHorner
    (poseidon : Fin 4 → K) (semantic : Fin 20 → K) (copy theta : K) :
    atomicThetaRadix8 poseidon semantic copy theta =
      atomicThetaHorner poseidon semantic copy theta := by
  simp [atomicThetaRadix8, atomicThetaBlock0, atomicThetaBlock1,
    atomicThetaBlock2, atomicThetaHorner, atomicThetaPrefix]
  ring

end AspisAtomicThetaRadix8
