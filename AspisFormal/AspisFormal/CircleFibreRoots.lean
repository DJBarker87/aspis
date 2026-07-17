import Mathlib

/-!
# Kernel-checked circle fibre-root distinctness (Check 4)

`tools/verify_soundness_params.py`, Check 4, enumerates the 2¹⁷ = 131072
arity-four fibre roots on the deployed 2¹⁹ circle coset and checks two finite
conditions that make the circle→GRS (line) transport injective:

* the 131072 fibre roots `t = 2x² − 1` are **pairwise distinct**, and
* **none equals 1**.

`SoundnessLedger.lean` left this as the one soundness finite-parameter fact it
could *not* pull into the kernel ("not tractable by a clean structural Lean
argument at reasonable cost"). This file proves it is tractable, structurally,
with **no brute-force enumeration** — the two facts are number theory, not a
131072-way case split.

## The deployed geometry (from `aspis-core/params.rs`, `circle_candidate.rs`)

M31 is the field `𝔽ₚ`, `P = 2³¹ − 1`. `CM31 = 𝔽ₚ[i]/(i²+1)` carries the circle
group of unit-norm elements `{(x,y) : x²+y² = 1}`, cyclic of order `2³¹`, with
generator `g = CIRCLE_GEN = (2, 1268011823)`. The verifier's circle→line
projection is the **x-coordinate doubling**
`π(x) = 2x² − 1`,
which is exactly the x-coordinate of `2·P` when `P = (x,y)` is on the circle
(`x(2P) = x² − y² = 2x² − 1`). So `π` on x-coordinates is the group doubling
pushed to the x-axis; it is 2-to-1 (a point and its conjugate/inverse `(x,−y)`
share `x`), and the arity-four fibre is the four circle points sharing one
root `t`.

The fibre representatives are `g^{eⱼ}`, `eⱼ = 2¹¹ + 2¹³·j`, `j = 0 … 2¹⁷−1`
(`init = 2¹¹`, `step = 2¹³` in the walk). The fibre root is
`tⱼ = π(x(g^{eⱼ})) = x(g^{2eⱼ})`, the x-coordinate of the **doubled** exponent
`dⱼ = 2eⱼ = 2¹² + 2¹⁴·j`.

## What is proved here vs. stated as interface

* **§1 — the ramification of `π` itself (fully proved, in the field 𝔽ₚ).**
  `π a = π b ↔ a = b ∨ a = −b` and `π a = 1 ↔ a = 1 ∨ a = −1`. This is the
  algebraic reason the ONLY way two roots collide is the sign ambiguity `±x`,
  and the only way a root hits `1` is `x = ±1`. Needs `P` prime (⟹ 𝔽ₚ a field,
  no zero divisors); `Nat.Prime (2³¹−1)` is discharged by `norm_num`
  (Mersenne prime M31). Corollaries give injectivity on any coset avoiding
  `±`-pairs and image-avoidance of `1` off `{±1}` — the "coset in standard
  position" hypotheses, stated explicitly.

* **§2 — the deployed 2¹⁷ exponents (fully proved, number theory mod 2³¹).**
  The x-coordinate of `g^a` equals that of `g^b` iff `a ≡ ±b (mod 2³¹)` — this
  is the standard reflection fact (inverse = complex conjugate flips only the
  y-coordinate), and is the **single interface hypothesis** carried by
  `SameXCoord` below (it is the geometry of the circle group, whose full
  construction — proving `g` has order exactly `2³¹` — is the only part not
  reduced to the kernel). Given it, that the 131072 doubled exponents
  `dⱼ = 2¹² + 2¹⁴·j` are pairwise non-collinear under `±` and none is `≡ 0`
  is proved by `omega` from the 2-adic valuations — no enumeration.

Together: §2 proves the deployed instance; §1 proves the field-algebra that
`SameXCoord` encodes. The proofs are sorry-free with axioms exactly
`[propext, Classical.choice, Quot.sound]` (no `native_decide` / `ofReduceBool`).
-/

namespace AspisCircleFibreRoots

/-! ## §1. Ramification of the x-doubling `π(x) = 2x² − 1` over 𝔽ₚ -/

/-- The M31 prime `P = 2³¹ − 1`; `𝔽ₚ = ZMod P`. -/
abbrev P : ℕ := 2 ^ 31 - 1

/-- `P` is the Mersenne prime M31, so `ZMod P` is a field. -/
instance : Fact (Nat.Prime P) := ⟨by norm_num⟩

/-- `2 ≠ 0` in `𝔽ₚ` (`P` is an odd prime). -/
lemma two_ne_zero_P : (2 : ZMod P) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; decide
  simpa using h

/-- The verifier's circle→line projection on x-coordinates, `π(x) = 2x² − 1`. -/
def pi (x : ZMod P) : ZMod P := 2 * x ^ 2 - 1

/-- In the field 𝔽ₚ, `a² = b²` iff `a = ±b` (no zero divisors). -/
lemma sq_eq_sq_iff (a b : ZMod P) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have hz : (a - b) * (a + b) = 0 := by ring_nf; linear_combination h
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h2)
  · rintro (rfl | rfl) <;> ring

/-- **Ramification of `π`.** Two x-coordinates give the same fibre root iff they
differ only by the circle's sign ambiguity `±x`. This is the whole reason a
fibre is arity four and the root map is otherwise injective. -/
lemma pi_eq_iff (a b : ZMod P) : pi a = pi b ↔ a = b ∨ a = -b := by
  rw [← sq_eq_sq_iff]
  unfold pi
  constructor
  · intro h
    have h2 : (2 : ZMod P) * (a ^ 2 - b ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with hz | hz
    · exact absurd hz two_ne_zero_P
    · linear_combination hz
  · intro h; rw [h]

/-- **`π(x) = 1` iff `x = ±1`.** The root value `1` is hit only at the circle
points `(±1, 0)` — the ramification points excluded from a standard-position
coset. -/
lemma pi_eq_one_iff (a : ZMod P) : pi a = 1 ↔ a = 1 ∨ a = -1 := by
  have h1 : pi a = pi 1 ↔ a = 1 ∨ a = -1 := by rw [pi_eq_iff]
  have h2 : pi (1 : ZMod P) = 1 := by unfold pi; norm_num
  rw [← h2]; exact h1

/-- **Structural injectivity of the root map on a standard-position coset.**
If a set `S` of fibre x-coordinates contains no genuine `±`-pair
(`a, −a ∈ S ⟹ a = −a`), then `π` is injective on `S`: the roots are pairwise
distinct. This is the coset hypothesis stated explicitly (interface-style),
with the injectivity itself fully proved from `pi_eq_iff`. -/
theorem pi_injOn_of_no_neg_pair (S : Set (ZMod P))
    (hS : ∀ a ∈ S, ∀ b ∈ S, a = -b → a = b) : Set.InjOn pi S := by
  intro a ha b hb hab
  rcases (pi_eq_iff a b).mp hab with h | h
  · exact h
  · exact hS a ha b hb h

/-- **Root ≠ 1 on a standard-position coset.** If `x ≠ ±1` then its root is
not `1`. -/
theorem pi_ne_one_of_ne_pm_one (a : ZMod P) (h1 : a ≠ 1) (h2 : a ≠ -1) :
    pi a ≠ 1 := by
  intro h; rcases (pi_eq_one_iff a).mp h with h' | h'
  · exact h1 h'
  · exact h2 h'

/-! ## §2. The deployed 2¹⁷ fibre roots: pairwise distinct, none equal 1

The fibre root `tⱼ` is the x-coordinate of the doubled point `g^{dⱼ}`,
`dⱼ = 2¹² + 2¹⁴·j`. On the circle, `x(g^a) = x(g^b) ⟺ a ≡ ±b (mod 2³¹)`
(reflection: inverse = conjugate). We package this collision criterion as
`SameXCoord` — it is the one geometric interface fact — and prove the deployed
exponents satisfy the two Check-4 conditions. -/

/-- Exponent (mod 2³¹) of the doubled circle point whose x-coordinate is the
`j`-th fibre root: `dⱼ = 2·eⱼ = 2¹² + 2¹⁴·j`. -/
def fiberRootExp (j : ℕ) : ℤ := 2 ^ 12 + 2 ^ 14 * (j : ℤ)

/-- **x-coordinate collision criterion (circle-group interface).**
`x(g^a) = x(g^b)` on the M31 circle iff `a ≡ b` or `a ≡ −b (mod 2³¹)`. The two
disjuncts are the point and its conjugate/inverse, which share an x-coordinate.
Distinct fibre roots ⟺ the exponents are NOT `SameXCoord`. -/
def SameXCoord (a b : ℤ) : Prop :=
  a ≡ b [ZMOD 2 ^ 31] ∨ a ≡ -b [ZMOD 2 ^ 31]

/-- **Check 4, condition 1 — pairwise distinctness.**
The 2¹⁷ deployed fibre roots are pairwise distinct: if two of them collide
(are `SameXCoord`), the fibre indices are equal. Proved by `omega` from the
2-adic valuations — no enumeration.

*`+` case:* `2¹⁴(i−j) ≡ 0 (mod 2³¹) ⟹ 2¹⁷ ∣ (i−j)`, impossible for
`|i−j| < 2¹⁷` unless `i = j`. *`−` case:* `2¹³(1 + 2(i+j)) ≡ 0 (mod 2³¹)`
forces `2¹⁸ ∣` an odd number — never. -/
theorem fiber_roots_distinct (i j : ℕ) (hi : i < 2 ^ 17) (hj : j < 2 ^ 17)
    (h : SameXCoord (fiberRootExp i) (fiberRootExp j)) : i = j := by
  unfold SameXCoord fiberRootExp Int.ModEq at h
  rcases h with h | h <;> omega

/-- **Check 4, condition 2 — no root equals 1.**
The fibre root value `1` would require `x(g^{dⱼ}) = x(g^0) = 1`, i.e.
`dⱼ ≡ ±0 (mod 2³¹)`; but `dⱼ = 2¹²(1 + 4j)` has 2-adic valuation exactly `12 < 31`
(the cofactor `1 + 4j` is odd), so `dⱼ ≢ 0`. Proved by `omega`. -/
theorem fiber_root_ne_one (j : ℕ) (hj : j < 2 ^ 17) :
    ¬ SameXCoord (fiberRootExp j) 0 := by
  intro h
  unfold SameXCoord fiberRootExp Int.ModEq at h
  rcases h with h | h <;> omega

/-! ## Axiom audit -/

#print axioms pi_eq_iff
#print axioms pi_eq_one_iff
#print axioms pi_injOn_of_no_neg_pair
#print axioms pi_ne_one_of_ne_pm_one
#print axioms fiber_roots_distinct
#print axioms fiber_root_ne_one

end AspisCircleFibreRoots
