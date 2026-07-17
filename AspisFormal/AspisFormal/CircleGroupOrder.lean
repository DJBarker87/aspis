import Mathlib

/- The two generator-order checks are 31-fold repeated squarings reduced by the
Lean **kernel** (`decide`); the default recursion budget is too small for a
chain of 31 `ZMod (2³¹−1)` multiplications, so we raise it. This keeps the
computation kernel-checked (axioms `[propext, Classical.choice, Quot.sound]`)
rather than compiled (`native_decide`, which would add `Lean.ofReduceBool`). -/
set_option maxRecDepth 20000

/-!
# The M31 circle group and the order of the deployed generator

This file backs the one geometric interface hypothesis carried by
`CircleFibreRoots.lean` (`SameXCoord`): that on the deployed M31 circle group
the x-coordinate collision criterion
`x(g^a) = x(g^b) ⟺ a ≡ ±b (mod 2³¹)`
is a **fact**, not an assumption.  Its two ingredients are

* the *x-collision criterion* `x(P) = x(Q) ⟺ Q = P ∨ Q = P⁻¹` — pure group-law
  algebra over `𝔽ₚ`, proved structurally here, and
* the *order of the generator* `g = (2, 1268011823)` is exactly `2³¹`, which
  turns `g^a = g^{±b}` into `a ≡ ±b (mod 2³¹)`.

The circle group is `C = {(x,y) ∈ 𝔽ₚ² : x²+y² = 1}` with the rotation law
`(x₁,y₁)·(x₂,y₂) = (x₁x₂ − y₁y₂, x₁y₂ + y₁x₂)`, `𝔽ₚ = ZMod (2³¹−1)`.  We build
`C` as a concrete `CommGroup` (the unit-norm elements of `𝔽ₚ[i]`), prove the
x-collision criterion from the group law, and pin the generator's order with the
prime-power criterion `orderOf_eq_prime_pow`: it reduces to the two concrete
2-power checks `g^{2³⁰} ≠ 1` and `g^{2³¹} = 1`.

## Honesty note on the order computation

The two 2-power checks are genuine finite computations about the specific field
element `1268011823`; there is no structural shortcut (the answer depends on the
number).  They are discharged by the **kernel** `decide` on a **31-fold repeated
squaring** (not a `2³¹`-step exponentiation), so the work is 31 field
multiplications, not two billion.  Because this is kernel reduction (not the
compiled `native_decide`), it adds **no** `Lean.ofReduceBool` axiom: every
theorem below, including `orderOf_g` and `sameXCoord_exp`, closes with axioms
exactly `[propext, Classical.choice, Quot.sound]`. See the audit at the bottom.
-/

namespace AspisCircleGroupOrder

/-- The M31 prime `P = 2³¹ − 1`; `𝔽ₚ = ZMod P`. -/
abbrev P : ℕ := 2 ^ 31 - 1

/-- `P` is the Mersenne prime M31, so `ZMod P` is a field. -/
instance : Fact (Nat.Prime P) := ⟨by norm_num⟩

/-- In the field `𝔽ₚ`, `a² = b²` iff `a = ±b` (no zero divisors). -/
lemma sq_eq_sq_iff (a b : ZMod P) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have hz : (a - b) * (a + b) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h2)
  · rintro (rfl | rfl) <;> ring

/-! ## §1. The circle group `C` as a concrete `CommGroup` -/

/-- The unit-norm predicate `x² + y² = 1` cutting out the circle in `𝔽ₚ²`. -/
def OnCircle (z : ZMod P × ZMod P) : Prop := z.1 ^ 2 + z.2 ^ 2 = 1

/-- The M31 circle group carrier: unit-norm points of `𝔽ₚ²`. -/
def C : Type := { z : ZMod P × ZMod P // OnCircle z }

instance : DecidableEq C := by unfold C; infer_instance
instance : DecidablePred OnCircle := fun z => by unfold OnCircle; infer_instance
instance : Fintype C := by unfold C OnCircle; infer_instance

/-- Rotation product `(x₁,y₁)·(x₂,y₂) = (x₁x₂ − y₁y₂, x₁y₂ + y₁x₂)` — closed on
the circle by the Brahmagupta–Fibonacci norm-multiplicativity identity. -/
def mulC (z w : C) : C :=
  ⟨(z.1.1 * w.1.1 - z.1.2 * w.1.2, z.1.1 * w.1.2 + z.1.2 * w.1.1), by
    have hz : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := z.2
    have hw : w.1.1 ^ 2 + w.1.2 ^ 2 = 1 := w.2
    show (z.1.1 * w.1.1 - z.1.2 * w.1.2) ^ 2 + (z.1.1 * w.1.2 + z.1.2 * w.1.1) ^ 2 = 1
    have key : (z.1.1 * w.1.1 - z.1.2 * w.1.2) ^ 2 + (z.1.1 * w.1.2 + z.1.2 * w.1.1) ^ 2
             = (z.1.1 ^ 2 + z.1.2 ^ 2) * (w.1.1 ^ 2 + w.1.2 ^ 2) := by ring
    rw [key, hz, hw]; ring⟩

/-- The identity rotation `(1, 0)`. -/
def oneC : C := ⟨(1, 0), by show (1 : ZMod P) ^ 2 + (0 : ZMod P) ^ 2 = 1; ring⟩

/-- The inverse rotation `(x, y)⁻¹ = (x, −y)` (complex conjugation). -/
def invC (z : C) : C :=
  ⟨(z.1.1, -z.1.2), by
    have hz : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := z.2
    show z.1.1 ^ 2 + (-z.1.2) ^ 2 = 1
    rw [show z.1.1 ^ 2 + (-z.1.2) ^ 2 = z.1.1 ^ 2 + z.1.2 ^ 2 from by ring]; exact hz⟩

instance : CommGroup C where
  mul := mulC
  one := oneC
  inv := invC
  mul_assoc a b c := by
    apply Subtype.ext
    show (mulC (mulC a b) c).1 = (mulC a (mulC b c)).1
    simp only [mulC]
    refine Prod.ext ?_ ?_ <;> · show _ = _; ring
  one_mul a := by
    apply Subtype.ext
    show (mulC oneC a).1 = a.1
    simp only [mulC, oneC]
    refine Prod.ext ?_ ?_ <;> · show _ = _; ring
  mul_one a := by
    apply Subtype.ext
    show (mulC a oneC).1 = a.1
    simp only [mulC, oneC]
    refine Prod.ext ?_ ?_ <;> · show _ = _; ring
  inv_mul_cancel a := by
    apply Subtype.ext
    show (mulC (invC a) a).1 = oneC.1
    have ha : a.1.1 ^ 2 + a.1.2 ^ 2 = 1 := a.2
    simp only [mulC, invC, oneC]
    refine Prod.ext ?_ ?_
    · show a.1.1 * a.1.1 - -a.1.2 * a.1.2 = 1; linear_combination ha
    · show a.1.1 * a.1.2 + -a.1.2 * a.1.1 = 0; ring
  mul_comm a b := by
    apply Subtype.ext
    show (mulC a b).1 = (mulC b a).1
    simp only [mulC]
    refine Prod.ext ?_ ?_ <;> · show _ = _; ring

@[simp] lemma mul_re (z w : C) : (z * w).1.1 = z.1.1 * w.1.1 - z.1.2 * w.1.2 := rfl
@[simp] lemma mul_im (z w : C) : (z * w).1.2 = z.1.1 * w.1.2 + z.1.2 * w.1.1 := rfl
@[simp] lemma one_re : (1 : C).1.1 = 1 := rfl
@[simp] lemma one_im : (1 : C).1.2 = 0 := rfl
@[simp] lemma inv_re (z : C) : (z⁻¹).1.1 = z.1.1 := rfl
@[simp] lemma inv_im (z : C) : (z⁻¹).1.2 = -z.1.2 := rfl

/-! ## §2. The x-collision criterion (structural) -/

/-- The x-coordinate projection `x(P)`. -/
def X (z : C) : ZMod P := z.1.1

/-- **x-collision criterion.** Two circle points share an x-coordinate iff they
are equal or inverse (conjugate).  This is the whole reason the x-doubling fibre
is arity two per point: `(x, y)` and `(x, −y)` are the only points on the circle
with first coordinate `x`, and `(x, −y) = (x, y)⁻¹`. Proved from the group law
and `y² = 1 − x²` (no cyclicity, no order needed). -/
theorem sameX_iff (z w : C) : X z = X w ↔ w = z ∨ w = z⁻¹ := by
  unfold X
  constructor
  · intro hx
    have hz : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := z.2
    have hw : w.1.1 ^ 2 + w.1.2 ^ 2 = 1 := w.2
    have hsq : w.1.2 ^ 2 = z.1.2 ^ 2 := by
      have hxx : z.1.1 ^ 2 = w.1.1 ^ 2 := by rw [hx]
      linear_combination hw - hz + hxx
    rcases (sq_eq_sq_iff w.1.2 z.1.2).mp hsq with h | h
    · left
      apply Subtype.ext
      rw [Prod.ext_iff]
      exact ⟨hx.symm, h⟩
    · right
      apply Subtype.ext
      rw [Prod.ext_iff]
      refine ⟨?_, ?_⟩
      · show w.1.1 = (z⁻¹).1.1; rw [inv_re]; exact hx.symm
      · show w.1.2 = (z⁻¹).1.2; rw [inv_im]; exact h
  · rintro (rfl | rfl)
    · rfl
    · rw [inv_re]

/-! ## §3. The deployed generator and its order

`g = CIRCLE_GEN = (2, 1268011823)`.  We show `orderOf g = 2³¹` via the
prime-power criterion, which needs exactly the two 2-power checks.  Both are
computed as 31-fold repeated squarings, so the cost is 31 multiplications. -/

/-- The deployed circle generator `g = (2, 1268011823)` (`CIRCLE_GEN`). Its
membership `2² + 1268011823² = 1` in `𝔽ₚ` is a single field computation. -/
def g : C := ⟨(2, 1268011823), by decide⟩

/-- Repeated squaring as `k`-fold iteration of `z ↦ z²`, matched to `z^(2^k)`:
this is what makes the 2-power checks 31 multiplications instead of `2³¹`. -/
lemma sq_iterate (k : ℕ) (z : C) : (fun z => z ^ 2)^[k] z = z ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih, ← pow_mul, pow_succ]

/-- `g^{2³¹} = 1` — the group order kills `g`.  Reduced to a 31-fold squaring
check. -/
lemma g_pow_2_31 : g ^ (2 ^ 31) = 1 := by
  rw [← sq_iterate 31 g]; decide

/-- `g^{2³⁰} ≠ 1` — the half-order power does not kill `g`, so the order is not a
proper power of two.  Reduced to a 30-fold squaring check. -/
lemma g_pow_2_30 : g ^ (2 ^ 30) ≠ 1 := by
  rw [← sq_iterate 30 g]; decide

/-- **The deployed generator has order exactly `2³¹`.**  `orderOf_eq_prime_pow`
(with prime `2`, exponent `30`) turns the two 2-power checks into equality. -/
theorem orderOf_g : orderOf g = 2 ^ 31 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 30) (x := g) g_pow_2_30 g_pow_2_31
  exact h

/-! ## §4. `SameXCoord` is a fact

Combining §2 and §3: `x(g^a) = x(g^b) ⟺ a ≡ ±b (mod 2³¹)`, matching the
`SameXCoord` interface used by `CircleFibreRoots.lean`, discharged with no
remaining hypothesis. -/

/-- `g^m = g^n` iff the exponents agree mod the order `2³¹`. -/
lemma g_zpow_eq_iff (m n : ℤ) : g ^ m = g ^ n ↔ m ≡ n [ZMOD 2 ^ 31] := by
  have hdiff : g ^ m = g ^ n ↔ g ^ (m - n) = 1 := by
    rw [zpow_sub, mul_inv_eq_one]
  rw [hdiff, ← orderOf_dvd_iff_zpow_eq_one, orderOf_g, Int.modEq_iff_dvd]
  have hcast : ((2 ^ 31 : ℕ) : ℤ) = (2 : ℤ) ^ 31 := by norm_num
  rw [hcast, ← dvd_neg, neg_sub]

/-- **The circle-group interface as a theorem (SameXCoord).**
`x(g^a) = x(g^b)` on the M31 circle iff `a ≡ b` or `a ≡ −b (mod 2³¹)`. This is
exactly the `SameXCoord` predicate that `CircleFibreRoots.lean` carries as its
single geometric hypothesis; here it is proved (no assumption) from the
x-collision criterion (§2) and `orderOf g = 2³¹` (§3). -/
theorem sameXCoord_exp (a b : ℤ) :
    X (g ^ a) = X (g ^ b) ↔ a ≡ b [ZMOD 2 ^ 31] ∨ a ≡ -b [ZMOD 2 ^ 31] := by
  rw [sameX_iff (g ^ a) (g ^ b)]
  have hinv : (g ^ a)⁻¹ = g ^ (-a) := (zpow_neg g a).symm
  rw [hinv, g_zpow_eq_iff b a, g_zpow_eq_iff b (-a)]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by simp only [Int.ModEq] at h ⊢; omega)
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by simp only [Int.ModEq] at h ⊢; omega)

/-! ## §5. Cardinality: what is structural and what remains

From `orderOf g = 2³¹` the cyclic subgroup `⟨g⟩` already gives the lower bound
and divisibility `2³¹ ∣ |C|`.  The *exact* value `|C| = 2³¹ = p+1` is the
norm-one count in `𝔽ₚ[i]` and needs the finite-field norm/character machinery
(surjectivity of the norm `𝔽_{p²}ˣ → 𝔽ₚˣ`); it is **not** required for the
`SameXCoord` deliverable and is left as the named residue below. -/

/-- Structural lower bound: `2³¹` divides the order of the circle group. -/
theorem card_C_dvd : 2 ^ 31 ∣ Fintype.card C := by
  rw [← orderOf_g]; exact orderOf_dvd_card

/-- Structural lower bound `2³¹ ≤ |C|`. -/
theorem card_C_ge : 2 ^ 31 ≤ Fintype.card C :=
  Nat.le_of_dvd Fintype.card_pos card_C_dvd

/-- **Named residue.** The exact cardinality `|C| = 2³¹ = p+1`.  Everything the
`SameXCoord` interface needs is proved above without it; this is stated as the
one interface fact whose structural proof (finite-field norm surjectivity) is
out of scope here.  It upgrades `2³¹ ∣ |C|` to equality and makes `C` cyclic. -/
def CircleCardInterface : Prop := Fintype.card C = 2 ^ 31

/-! ## Axiom audit -/

#print axioms sameX_iff
#print axioms orderOf_g
#print axioms sameXCoord_exp
#print axioms card_C_dvd

end AspisCircleGroupOrder
