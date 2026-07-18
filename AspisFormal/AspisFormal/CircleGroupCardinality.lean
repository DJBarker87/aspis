import AspisFormal.CircleGroupOrder

/-!
# Exact cardinality of the M31 circle group

This file discharges the named residue `AspisCircleGroupOrder.CircleCardInterface`
left open in `CircleGroupOrder.lean`: the circle group
`C = {(x,y) ∈ 𝔽ₚ² : x²+y² = 1}` over `𝔽ₚ = ZMod (2³¹−1)` has cardinality exactly
`2³¹ = P + 1`.

The structural lower bound `2³¹ ≤ |C|` is already available (`card_C_ge`, coming
from `orderOf g = 2³¹`).  Here we supply the matching upper bound `|C| ≤ 2³¹` by
the **stereographic injection**

  `stereo : C → Option 𝔽ₚ`,  `(x,y) ↦ if x = -1 then none else some (y / (1+x))`,

which is injective.  Since `|Option 𝔽ₚ| = P + 1 = 2³¹`, this bounds `|C| ≤ 2³¹`,
and antisymmetry gives the exact value.

Injectivity is pure field algebra over `𝔽ₚ`.  For `x ≠ -1` the chart value
`t = y/(1+x)` determines the point: cross-multiplying and squaring, then using
`y² = 1 − x²`, forces `x₁ = x₂` after cancelling the nonzero factor
`(1+x₁)(1+x₂)·2` (this is the only place oddness of `P` enters, via `2 ≠ 0`), and
the cross-multiplication then forces `y₁ = y₂`.  The single point `(-1,0)` — the
only circle point with `x = -1`, since then `y² = 1 − 1 = 0` — is the fibre over
`none`.

No new axioms and no raised limits: everything below closes at default settings
with axioms exactly `[propext, Classical.choice, Quot.sound]` (see the audit at
the bottom).
-/

namespace AspisCircleGroupOrder

/-- The stereographic chart `C → Option 𝔽ₚ`.  The single point `(-1,0)` (the only
circle point with `x = -1`) is sent to `none`; every other point `(x,y)` is sent
to `some (y/(1+x))`. -/
def stereo (z : C) : Option (ZMod P) :=
  if z.1.1 = -1 then none else some (z.1.2 / (1 + z.1.1))

/-- `(2 : 𝔽ₚ) ≠ 0`: `P = 2³¹ − 1` is an odd prime, so `P ∤ 2`. -/
lemma two_ne_zero_ZModP : (2 : ZMod P) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod P) ≠ 0 := by
    simp only [ne_eq, ZMod.natCast_eq_zero_iff]
    decide
  simpa using h

/-- **The stereographic chart is injective.**  Over `none` the fibre is the single
point `(-1,0)`; over `some t` the field relation `t = y/(1+x)` pins down `(x,y)`. -/
lemma stereo_injective : Function.Injective stereo := by
  intro z w h
  have hcz : z.1.1 ^ 2 + z.1.2 ^ 2 = 1 := z.2
  have hcw : w.1.1 ^ 2 + w.1.2 ^ 2 = 1 := w.2
  simp only [stereo] at h
  by_cases hz : z.1.1 = -1 <;> by_cases hw : w.1.1 = -1
  · -- both x = -1, hence both y = 0, so both points are `(-1,0)`
    have hy1 : z.1.2 = 0 := by
      have hsq : z.1.2 ^ 2 = 0 := by rw [hz] at hcz; linear_combination hcz
      exact sq_eq_zero_iff.mp hsq
    have hy2 : w.1.2 = 0 := by
      have hsq : w.1.2 ^ 2 = 0 := by rw [hw] at hcw; linear_combination hcw
      exact sq_eq_zero_iff.mp hsq
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show z.1.1 = w.1.1; rw [hz, hw]
    · show z.1.2 = w.1.2; rw [hy1, hy2]
  · rw [if_pos hz, if_neg hw] at h; simp at h
  · rw [if_neg hz, if_pos hw] at h; simp at h
  · -- both x ≠ -1: the field argument
    rw [if_neg hz, if_neg hw, Option.some.injEq] at h
    have hb1 : (1 : ZMod P) + z.1.1 ≠ 0 := by
      intro hcon; exact hz (by linear_combination hcon)
    have hb2 : (1 : ZMod P) + w.1.1 ≠ 0 := by
      intro hcon; exact hw (by linear_combination hcon)
    -- cross-multiply the chart equality
    have hcross : z.1.2 * (1 + w.1.1) = w.1.2 * (1 + z.1.1) :=
      (div_eq_div_iff hb1 hb2).mp h
    have hsq : (z.1.2 * (1 + w.1.1)) ^ 2 = (w.1.2 * (1 + z.1.1)) ^ 2 := by rw [hcross]
    have hy1 : z.1.2 ^ 2 = 1 - z.1.1 ^ 2 := by linear_combination hcz
    have hy2 : w.1.2 ^ 2 = 1 - w.1.1 ^ 2 := by linear_combination hcw
    -- substitute `y² = 1 − x²`; the difference factors as a nonzero multiple of `x₂ − x₁`
    have hfac : ((1 + z.1.1) * (1 + w.1.1) * 2) * (w.1.1 - z.1.1) = 0 := by
      linear_combination hsq - (1 + w.1.1) ^ 2 * hy1 + (1 + z.1.1) ^ 2 * hy2
    have hne : (1 + z.1.1) * (1 + w.1.1) * 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hb1 hb2) two_ne_zero_ZModP
    have hdiff : w.1.1 - z.1.1 = 0 := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact absurd h' hne
      · exact h'
    have hxeq : z.1.1 = w.1.1 := (sub_eq_zero.mp hdiff).symm
    have hyeq : z.1.2 = w.1.2 := by
      have hmm : z.1.2 * (1 + w.1.1) = w.1.2 * (1 + w.1.1) := by rw [hcross, hxeq]
      exact mul_right_cancel₀ hb2 hmm
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show z.1.1 = w.1.1; exact hxeq
    · show z.1.2 = w.1.2; exact hyeq

/-- Stereographic upper bound `|C| ≤ 2³¹`: the injection `stereo` lands in
`Option 𝔽ₚ`, which has `P + 1 = 2³¹` elements. -/
theorem card_C_le : Fintype.card C ≤ 2 ^ 31 := by
  have hle := Fintype.card_le_of_injective stereo stereo_injective
  rw [Fintype.card_option, ZMod.card] at hle
  -- hle : Fintype.card C ≤ P + 1
  have hP1 : P + 1 = 2 ^ 31 := by show 2 ^ 31 - 1 + 1 = 2 ^ 31; norm_num
  rw [hP1] at hle
  exact hle

/-- **The M31 circle group has cardinality exactly `2³¹`.**  Antisymmetry of the
structural lower bound `card_C_ge` (`2³¹ ≤ |C|`, from `orderOf g = 2³¹`) and the
stereographic upper bound `card_C_le` (`|C| ≤ 2³¹`). -/
theorem card_C_eq : Fintype.card C = 2 ^ 31 :=
  le_antisymm card_C_le card_C_ge

/-- The named residue `CircleCardInterface` (`|C| = 2³¹`) is now a theorem, not an
assumption. -/
theorem circleCardInterface_holds : CircleCardInterface := card_C_eq

/-! ## Axiom audit -/

#print axioms card_C_eq
#print axioms circleCardInterface_holds

end AspisCircleGroupOrder
