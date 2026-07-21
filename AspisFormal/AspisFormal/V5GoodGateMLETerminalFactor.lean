import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact 6+1 Boolean-MLE terminal factor used by the v5 Good gate

The Good-gate CU path builds the equality weights for six relation coordinates
once, then factors the final low row bit separately.  This leaf proves that
factorisation and the resulting p/q dot identities over an arbitrary
commutative semiring.
-/

namespace AspisV5GoodGateMLETerminalFactor

variable {R : Type*} [CommSemiring R]

/-- One Boolean equality factor, with its zero- and one-branch values supplied
separately.  In the deployed field these are `1 - x` and `x`; keeping the
complement explicit makes the factorisation valid over every semiring. -/
def bitFactor (zeroFactor oneFactor : R) (bit : Bool) : R :=
  if bit then oneFactor else zeroFactor

/-- The cached equality weight for the fixed six-coordinate suffix. -/
def prefixWeight6 (zeroFactor oneFactor : Fin 6 → R) (bits : Fin 6 → Bool) : R :=
  ∏ coordinate : Fin 6,
    bitFactor (zeroFactor coordinate) (oneFactor coordinate) (bits coordinate)

/-- The same equality weight after appending the seventh, low row bit. -/
def splitWeight7 (zeroFactor oneFactor : Fin 6 → R) (lastZero lastOne : R)
    (bits : Fin 6 → Bool) (lowBit : Bool) : R :=
  prefixWeight6 zeroFactor oneFactor bits * bitFactor lastZero lastOne lowBit

/-- Reading aligned row `2*i` multiplies the cached six-coordinate weight by
`1-z`. -/
theorem splitWeight7_low_zero (zeroFactor oneFactor : Fin 6 → R) (lastZero lastOne : R)
    (bits : Fin 6 → Bool) :
    splitWeight7 zeroFactor oneFactor lastZero lastOne bits false =
      lastZero * prefixWeight6 zeroFactor oneFactor bits := by
  simp [splitWeight7, bitFactor, mul_comm]

/-- Reading aligned row `2*i+1` multiplies the cached six-coordinate weight by
`z`. -/
theorem splitWeight7_low_one (zeroFactor oneFactor : Fin 6 → R) (lastZero lastOne : R)
    (bits : Fin 6 → Bool) :
    splitWeight7 zeroFactor oneFactor lastZero lastOne bits true =
      lastOne * prefixWeight6 zeroFactor oneFactor bits := by
  simp [splitWeight7, bitFactor, mul_comm]

/-- Exact p-block dot formula for the fixed 64 cached suffix leaves. -/
theorem pDot_factor (zeroFactor oneFactor : Fin 6 → R) (lastZero lastOne : R)
    (rowBits : Fin 64 → Fin 6 → Bool) (values : Fin 64 → R) :
    (∑ row : Fin 64,
        splitWeight7 zeroFactor oneFactor lastZero lastOne (rowBits row) false * values row) =
      lastZero *
        ∑ row : Fin 64, prefixWeight6 zeroFactor oneFactor (rowBits row) * values row := by
  simp_rw [splitWeight7_low_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [mul_assoc]

/-- Exact q-block dot formula for the fixed 64 cached suffix leaves. -/
theorem qDot_factor (zeroFactor oneFactor : Fin 6 → R) (lastZero lastOne : R)
    (rowBits : Fin 64 → Fin 6 → Bool) (values : Fin 64 → R) :
    (∑ row : Fin 64,
        splitWeight7 zeroFactor oneFactor lastZero lastOne (rowBits row) true * values row) =
      lastOne *
        ∑ row : Fin 64, prefixWeight6 zeroFactor oneFactor (rowBits row) * values row := by
  simp_rw [splitWeight7_low_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [mul_assoc]

/-- The two aligned rows reconstruct the unfactored six-coordinate dot when
their values agree.  This is a small consistency tooth for the `1-z,z` split. -/
theorem pDot_add_qDot_same_values (zeroFactor oneFactor : Fin 6 → R)
    (lastZero lastOne : R) (hlast : lastZero + lastOne = 1)
    (rowBits : Fin 64 → Fin 6 → Bool) (values : Fin 64 → R) :
    (∑ row : Fin 64,
        splitWeight7 zeroFactor oneFactor lastZero lastOne (rowBits row) false * values row) +
        (∑ row : Fin 64,
          splitWeight7 zeroFactor oneFactor lastZero lastOne (rowBits row) true * values row) =
      ∑ row : Fin 64,
        prefixWeight6 zeroFactor oneFactor (rowBits row) * values row := by
  rw [pDot_factor, qDot_factor]
  rw [← add_mul, hlast, one_mul]

#print axioms AspisV5GoodGateMLETerminalFactor.splitWeight7_low_zero
#print axioms AspisV5GoodGateMLETerminalFactor.splitWeight7_low_one
#print axioms AspisV5GoodGateMLETerminalFactor.pDot_factor
#print axioms AspisV5GoodGateMLETerminalFactor.qDot_factor
#print axioms AspisV5GoodGateMLETerminalFactor.pDot_add_qDot_same_values

end AspisV5GoodGateMLETerminalFactor
