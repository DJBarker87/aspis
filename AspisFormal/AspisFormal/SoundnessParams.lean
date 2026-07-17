import Mathlib

/-!
# Kernel-checked finite-parameter soundness instantiation

The soundness argument *cites* published list-decoding theorems (Johnson bound,
MCA).  Whether those theorems *apply at Aspis's exact parameters* is a finite
arithmetic check, currently done by `tools/verify_soundness_params.py` (a script
I wrote — i.e. AI-trusted).  Here that check's load-bearing facts are proved in
Lean, so the *instantiation* is kernel-verified and only the published theorems
remain external citations.

Parameters: rate ρ = 1/512; Johnson slack 1/20 (so α = (1+1/20)·√ρ); layer-zero
fiber count N = 2¹⁷.  The two facts below are exactly "we are in the proven
Johnson regime, not the (now-disproven) capacity regime" and "the agreement cap
is A = ⌊αN⌋ = 6082".
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
