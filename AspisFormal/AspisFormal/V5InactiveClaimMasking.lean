import AspisFormal.V5RankOneOpeningHiding

/-!
# Masking the carried v5 copy-inactive claim

Deleting the historical H/G/D lanes means the gamma-combined copy-inactive
functional is not generally zero.  The sound relation must carry its actual
value.  This file records the minimal hiding repair: reserve one fresh uniform
QM31 coordinate in Component B at an inactive row whose terminal covector is
zero.  Once the nonzero lane coefficient `gammaB` is fixed, the released claim
has the form

`base + gammaB * pivot`.

Multiplication by a nonzero field element is surjective, so a uniform pivot
makes this single released field element independent of `base`.  The theorem
is deliberately conditional on a uniform pre-challenge pivot and nonzero
`gammaB`; Rust/transcript correspondence remains a separate obligation.
-/

namespace AspisV5InactiveClaimMasking

variable {K : Type*} [Field K]

/-- The linear contribution of the fresh Component-B inactive-row pivot. -/
def pivotMap (gammaB : K) : K →ₗ[K] K where
  toFun pivot := gammaB * pivot
  map_add' left right := by simp [mul_add]
  map_smul' scalar pivot := by
    simp only [smul_eq_mul, RingHom.id_apply]
    ac_rfl

@[simp]
theorem pivotMap_apply (gammaB pivot : K) :
    pivotMap gammaB pivot = gammaB * pivot := rfl

/-- A nonzero gamma lane coefficient makes the pivot contribution hit every
possible carried claim. -/
theorem pivotMap_surjective (gammaB : K) (hgammaB : gammaB ≠ 0) :
    Function.Surjective (pivotMap gammaB) := by
  intro target
  refine ⟨gammaB⁻¹ * target, ?_⟩
  simp [pivotMap, hgammaB]

/-- The released copy-inactive claim after adding the fresh pivot. -/
def carriedClaim (base gammaB pivot : K) : K :=
  base + pivotMap gammaB pivot

section Distribution

variable [Fintype K]

/-- With a fresh uniform pivot and nonzero Component-B gamma coefficient, the
carried inactive claim has exactly the same law for any two witness-dependent
base claims. -/
theorem carriedClaim_pmf_indep
    (gammaB : K) (hgammaB : gammaB ≠ 0) (base₁ base₂ : K) :
    (PMF.uniformOfFintype K).map (fun pivot => carriedClaim base₁ gammaB pivot) =
      (PMF.uniformOfFintype K).map (fun pivot => carriedClaim base₂ gammaB pivot) := by
  classical
  simpa [carriedClaim] using
    (AspisV5RankOneOpeningHiding.released_view_pmf_indep (pivotMap gammaB)
      (pivotMap_surjective gammaB hgammaB) base₁ base₂)

/-- Any deterministic downstream transcript observation preserves the same
witness-independent law. -/
theorem observed_carriedClaim_pmf_indep
    {View : Type*} (observe : K → View)
    (gammaB : K) (hgammaB : gammaB ≠ 0) (base₁ base₂ : K) :
    (PMF.uniformOfFintype K).map
        (fun pivot => observe (carriedClaim base₁ gammaB pivot)) =
      (PMF.uniformOfFintype K).map
        (fun pivot => observe (carriedClaim base₂ gammaB pivot)) := by
  classical
  have h := congrArg (fun distribution : PMF K => distribution.map observe)
    (carriedClaim_pmf_indep gammaB hgammaB base₁ base₂)
  simpa only [PMF.map_comp, Function.comp_def] using h

end Distribution

#print axioms pivotMap_surjective
#print axioms carriedClaim_pmf_indep
#print axioms observed_carriedClaim_pmf_indep

end AspisV5InactiveClaimMasking
