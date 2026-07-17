import Mathlib

/-!
# Kernel-checked Johnson threshold and agreement-cap arithmetic

Scope, stated honestly.  `tools/verify_soundness_params.py` performs the full
finite-parameter check: fibre-root distinctness and root≠1, the circle-to-line
transport, the width-29 MCA generator condition, every event degree, and the
union-bound / BCS-endpoint arithmetic.  **This file proves only TWO of those
facts** — the Johnson-threshold inequality `ρ ≤ α²` and the integer agreement
cap `A = ⌊αN⌋ = 6082`.  Everything else remains Python-verified, NOT
kernel-verified.

Two further caveats, so this is not mis-read:
* The constants below (`rho`, `alpha`, `Nfib`) are Lean literals.  Nothing here
  proves they equal the constants compiled into the Rust verifier, or that the
  `1/20` slack comes from the configured multiplicity `m=10`.  Binding Lean to
  the frozen profile (ideally: generate both from one manifest and let CI reject
  disagreement) is future work.  So this is math about the *intended*
  parameters, not verification of the *deployed* ones.
* The published Johnson/MCA/transport/WHIR theorems themselves are cited, not
  proved here.

Parameters: rate ρ = 1/512; Johnson slack 1/20 (so α = (1+1/20)·√ρ); layer-zero
fiber count N = 2¹⁷.  The two facts are "we are in the proven Johnson regime,
not the (now-disproven) capacity regime" and "the agreement cap is 6082".
-/

namespace AspisSoundness

/-- Rate ρ = 1/512. -/
noncomputable def rho : ℝ := 1 / 512
/-- Johnson agreement parameter α = (1 + 1/20)·√ρ. -/
noncomputable def alpha : ℝ := (21 / 20) * Real.sqrt rho
/-- Layer-zero fiber count N = 2¹⁷. -/
def Nfib : ℕ := 131072

private lemma sqrt_rho_sq : Real.sqrt rho ^ 2 = rho :=
  Real.sq_sqrt (by norm_num [rho])

private lemma sqrt_rho_nonneg : (0 : ℝ) ≤ Real.sqrt rho := Real.sqrt_nonneg rho

/-- **Proven-Johnson regime membership.**  α ≥ √ρ: the agreement sits at or above
the Johnson list-decoding radius, so soundness uses the *proven* regime, not the
capacity conjecture (disproven over large fields in 2025).  Stated in squared
form `ρ ≤ α²` (both sides nonnegative). -/
theorem regime_membership : rho ≤ alpha ^ 2 := by
  have h := sqrt_rho_sq
  unfold alpha
  nlinarith [h, sqrt_rho_nonneg]

/-- **Johnson agreement cap A = ⌊αN⌋ = 6082.**  We prove `6082 ≤ αN < 6083`, so
the integer cap the verifier uses is exactly 6082. -/
theorem johnson_cap : (6082 : ℝ) ≤ alpha * Nfib ∧ alpha * Nfib < 6083 := by
  have h := sqrt_rho_sq
  have hnn := sqrt_rho_nonneg
  unfold alpha Nfib rho at *
  refine ⟨?_, ?_⟩ <;> nlinarith [h, hnn]

end AspisSoundness

#print axioms AspisSoundness.regime_membership
#print axioms AspisSoundness.johnson_cap
