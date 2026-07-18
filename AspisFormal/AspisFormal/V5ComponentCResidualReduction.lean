import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# v5 Component C: reduce C-DEC to the normalized residual invariant

This file records a small but load-bearing reduction for Component C.

For a fixed public-coin schedule, let `x₁` and `x₂` be the two pre-C words
after the Component-A and Component-B view-matching translations have been
applied.  If their difference preserves

* the copy-inactive relation `ℓ`, and
* all 76 coordinates conditioned/released from the C lane, represented by
  `E`,

then that difference already belongs to the admissible, conditioned C-mask
space `ker ℓ ⊓ ker E`.  Consequently its `F`-image is covered by that mask
space for *every* linear post-combination map `F`; no surjectivity or rank
claim is needed.

This is an exact implication from the stated matched-`ell`/matched-`E`
premises, not a characterization of every way C-DEC can hold and not a
deployed Component-C proof.  It is deliberately stronger than the weakest
fixed-`F` condition: the frozen audit has a 19-dimensional quotient
obstruction, and proving `E`-equality bypasses all 19 coordinates at once.
This file does **not** prove that the real Rust A/B normalization has the two
invariants above, that its 76-row evaluator is `E`, that the post-combination
evaluator is `F`, that genuine residuals annihilate those 19 quotient
functionals, or that a Fiat--Shamir transcript can be reduced to the
fixed-schedule experiment.  Those remain named deployment/correspondence
obligations outside this file.
-/

namespace AspisV5ComponentCResidualReduction

open AspisV5ComponentCConditionalDecoupling

variable {K M U Y : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-- Equality of the relation and conditioned coordinates puts the word
difference in the exact admissible conditioned-mask space. -/
theorem sub_mem_ker_inf_ker
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) {x₁ x₂ : M}
    (hell : ell x₁ = ell x₂) (hE : E x₁ = E x₂) :
    x₂ - x₁ ∈ LinearMap.ker ell ⊓ LinearMap.ker E := by
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
    map_sub, map_sub]
  exact ⟨sub_eq_zero.mpr hell.symm, sub_eq_zero.mpr hE.symm⟩

/-- Any legal-difference space already contained in the admissible
conditioned-mask space satisfies C-DEC for every post-combination map. -/
theorem cDecAudit_of_le_ker_inf_ker
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (Delta : Submodule K M)
    (hDelta : Delta ≤ LinearMap.ker ell ⊓ LinearMap.ker E) :
    CDecAudit ell E F Delta := by
  exact Submodule.map_mono hDelta

/-- The largest difference space for this stronger containment-based route,
which works uniformly for every linear `F`: `ker ell ⊓ ker E` itself.
For a fixed `F`, C-DEC can hold on larger spaces. -/
theorem cDecAudit_ker_inf_ker
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y) :
    CDecAudit ell E F (LinearMap.ker ell ⊓ LinearMap.ker E) := by
  exact cDecAudit_of_le_ker_inf_ker ell E F _ le_rfl

/-- Pointwise formulation useful at the deployment seam.  It is enough to
show that every normalized legal difference preserves `ell` and `E`; the
abstract C-DEC premise consumed by the hiding theorem then follows. -/
theorem cDecAudit_of_normalized_residual_invariant
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (Delta : Submodule K M)
    (hinvariant : ∀ d ∈ Delta, ell d = 0 ∧ E d = 0) :
    CDecAudit ell E F Delta := by
  apply cDecAudit_of_le_ker_inf_ker ell E F Delta
  intro d hd
  obtain ⟨hell, hE⟩ := hinvariant d hd
  exact Submodule.mem_inf.mpr
    ⟨LinearMap.mem_ker.mpr hell, LinearMap.mem_ker.mpr hE⟩

/-- Exact conditioned-law consequence for a pair of normalized pre-C words.

The assumptions `ell x₁ = ell x₂` and `E x₁ = E x₂` are the two
deployment facts that must be supplied by the A/B normalization and accepted
relation.  Once supplied, the C mask absorbs the whole post-combination
difference for any linear `F`. -/
theorem full_fold_decoupling_of_matched_normalized_residuals
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0) {x₁ x₂ : M}
    (hell : ell x₁ = ell x₂) (hE : E x₁ = E x₂) (e : U)
    [Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}] :
    (PMF.uniformOfFintype {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e}).map
        (fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
          F (x₁ + gamma ^ 18 • ((c : LinearMap.ker ell) : M)))
      =
    (PMF.uniformOfFintype {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e}).map
        (fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
          F (x₂ + gamma ^ 18 • ((c : LinearMap.ker ell) : M))) := by
  exact componentC_full_fold_conditional_decoupling ell E F hgamma
    (cDecAudit_ker_inf_ker ell E F)
    (sub_mem_ker_inf_ker ell E hell hE) e

/-! ## Honest deployment interfaces

These propositions name the two facts needed to apply the reduction to a
deployed normalizer.  They are definitions only and are not proved here.
-/

namespace UnmetDeployment

/-- The deployed A/B-normalized pre-C words preserve the accepted
copy-inactive relation for every legal same-statement pair. -/
def NormalizedResidualPreservesInactive
    (LegalPair : M → M → Prop) (normalize : M → M)
    (ell : M →ₗ[K] K) : Prop :=
  ∀ x₁ x₂, LegalPair x₁ x₂ → ell (normalize x₁) = ell (normalize x₂)

/-- The deployed A/B normalization makes all 76 C-conditioned coordinates
agree for every legal same-statement pair. -/
def NormalizedResidualPreservesConditionedView
    (LegalPair : M → M → Prop) (normalize : M → M)
    (E : M →ₗ[K] U) : Prop :=
  ∀ x₁ x₂, LegalPair x₁ x₂ → E (normalize x₁) = E (normalize x₂)

end UnmetDeployment

#print axioms sub_mem_ker_inf_ker
#print axioms cDecAudit_of_le_ker_inf_ker
#print axioms cDecAudit_ker_inf_ker
#print axioms cDecAudit_of_normalized_residual_invariant
#print axioms full_fold_decoupling_of_matched_normalized_residuals
#print axioms UnmetDeployment.NormalizedResidualPreservesInactive
#print axioms UnmetDeployment.NormalizedResidualPreservesConditionedView

end AspisV5ComponentCResidualReduction
