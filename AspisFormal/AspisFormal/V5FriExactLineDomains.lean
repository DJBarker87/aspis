import AspisFormal.CircleGroupOrder

set_option maxRecDepth 20000

/-!
# Exact line domains used by the V5 FRI rounds

The four output codes are evaluated on M31 half-odd line domains of lengths
`2^17`, `2^15`, `2^13`, and `2^11`.  This file defines those domains directly
from the released circle generator and proves that their x-coordinates are
pairwise distinct.  The proof uses the already checked order `2^31` of that
specific generator; it is not a generic distinct-points assumption.

The order below is natural exponent order.  Bit reversal only permutes these
points and therefore does not alter the distance result.
-/

namespace AspisV5FriExactLineDomains

open AspisCircleGroupOrder

/-- Natural-order point of the `2^17` first line domain. -/
def line17Point (i : Fin 131072) : C :=
  g ^ (4096 + 16384 * (i : Int))

/-- Natural-order point of the `2^15` second line domain. -/
def line15Point (i : Fin 32768) : C :=
  g ^ (16384 + 65536 * (i : Int))

/-- Natural-order point of the `2^13` third line domain. -/
def line13Point (i : Fin 8192) : C :=
  g ^ (65536 + 262144 * (i : Int))

/-- Natural-order point of the `2^11` final line domain. -/
def line11Point (i : Fin 2048) : C :=
  g ^ (262144 + 1048576 * (i : Int))

def line17X (i : Fin 131072) : ZMod P := X (line17Point i)
def line15X (i : Fin 32768) : ZMod P := X (line15Point i)
def line13X (i : Fin 8192) : ZMod P := X (line13Point i)
def line11X (i : Fin 2048) : ZMod P := X (line11Point i)

theorem line17X_injective : Function.Injective line17X := by
  intro i j hij
  have hm := (sameXCoord_exp
    (4096 + 16384 * (i : Int))
    (4096 + 16384 * (j : Int))).mp hij
  apply Fin.ext
  unfold Int.ModEq at hm
  have hi := i.isLt
  have hj := j.isLt
  norm_num at hi hj hm ⊢
  rcases hm with hm | hm <;> omega

theorem line15X_injective : Function.Injective line15X := by
  intro i j hij
  have hm := (sameXCoord_exp
    (16384 + 65536 * (i : Int))
    (16384 + 65536 * (j : Int))).mp hij
  apply Fin.ext
  unfold Int.ModEq at hm
  have hi := i.isLt
  have hj := j.isLt
  norm_num at hi hj hm ⊢
  rcases hm with hm | hm <;> omega

theorem line13X_injective : Function.Injective line13X := by
  intro i j hij
  have hm := (sameXCoord_exp
    (65536 + 262144 * (i : Int))
    (65536 + 262144 * (j : Int))).mp hij
  apply Fin.ext
  unfold Int.ModEq at hm
  have hi := i.isLt
  have hj := j.isLt
  norm_num at hi hj hm ⊢
  rcases hm with hm | hm <;> omega

theorem line11X_injective : Function.Injective line11X := by
  intro i j hij
  have hm := (sameXCoord_exp
    (262144 + 1048576 * (i : Int))
    (262144 + 1048576 * (j : Int))).mp hij
  apply Fin.ext
  unfold Int.ModEq at hm
  have hi := i.isLt
  have hj := j.isLt
  norm_num at hi hj hm ⊢
  rcases hm with hm | hm <;> omega

/-! ## Coordinate doubling -/

/-- The x-coordinate of a squared circle point is `2*x^2-1`. -/
theorem X_sq (point : C) : X (point ^ 2) = 2 * X point ^ 2 - 1 := by
  have hcircle : point.1.1 ^ 2 + point.1.2 ^ 2 = 1 := point.2
  rw [pow_two]
  simp only [X, mul_re]
  change point.1.1 * point.1.1 - point.1.2 * point.1.2 =
    2 * point.1.1 ^ 2 - 1
  linear_combination -hcircle

/-- Fourfold group multiplication gives the twice-doubled line coordinate. -/
theorem X_pow_four (point : C) :
    X (point ^ 4) = 2 * (2 * X point ^ 2 - 1) ^ 2 - 1 := by
  rw [show point ^ 4 = (point ^ 2) ^ 2 by group]
  rw [X_sq, X_sq]

/-! ## The half-turn sign change -/

/-- The deployed generator's half-order power has x-coordinate `-1`. -/
theorem generatorHalfTurn_x :
    X (g ^ ((2 : Int) ^ 30)) = -1 := by
  rw [show (2 : Int) ^ 30 = ((2 ^ 30 : Nat) : Int) by norm_num,
    zpow_natCast, ← sq_iterate 30 g]
  decide

/-- The deployed generator's half-order power has y-coordinate zero. -/
theorem generatorHalfTurn_y :
    (g ^ ((2 : Int) ^ 30)).1.2 = 0 := by
  rw [show (2 : Int) ^ 30 = ((2 ^ 30 : Nat) : Int) by norm_num,
    zpow_natCast, ← sq_iterate 30 g]
  decide

/-- Adding the half-order exponent negates the x-coordinate.  This is the
sign relation between the two members of each stored radix-four pair. -/
theorem X_zpow_add_halfTurn (exponent : Int) :
    X (g ^ (exponent + (2 : Int) ^ 30)) = -X (g ^ exponent) := by
  rw [zpow_add]
  unfold X
  rw [mul_re]
  rw [show (g ^ ((2 : Int) ^ 30)).1.1 = -1 by
      exact generatorHalfTurn_x]
  rw [generatorHalfTurn_y]
  ring

/-! ## Audit -/

#print axioms line17X_injective
#print axioms line15X_injective
#print axioms line13X_injective
#print axioms line11X_injective
#print axioms X_sq
#print axioms X_pow_four
#print axioms X_zpow_add_halfTurn

end AspisV5FriExactLineDomains
