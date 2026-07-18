import AspisFormal.V5ComponentCResidualReduction

/-!
# v5 Component C: affine coupling beyond a fixed conditioned fibre

This file proves the exact fixed-public-coin algebra needed when the two
pre-Component-C runs need not have the same released `E`-view.

For a fixed scalar `a = gamma ^ 18`, write the joint view as

    (u + E c, F (x + a * c)),

where `u` is the pre-C contribution to the released coordinates, `x` is the
pre-C word, and `c` is uniform on `ker ell`.  A single mask translation hides
both residuals exactly when the scaled pair

    (a * (u2 - u1), F x2 - F x1)

lies in the image of the joint map `(E,F)` restricted to `ker ell`.  If `d`
is a witness for that image membership, translation by `a^-1 * d` makes the
two joint views pointwise equal.  Uniformity on `ker ell` then gives equality
of the complete joint `PMF`s.

Unlike the earlier conditioned-fibre theorem, this criterion allows
`u1 != u2` (and in particular `E x1 != E x2`).  It is both necessary and
sufficient for an intertwining *translation*, not a full-rank or
surjectivity assumption.

This is fixed-public-coin linear algebra only.  It does **not** prove a
Fiat--Shamir coupling, identify `E` or `F` with deployed Rust evaluators,
establish that a deployed A/B normalizer produces an absorbable residual, or
establish sampler/serialization correspondence.
-/

open scoped ENNReal

namespace AspisV5ComponentCAffineCoupling

open AspisV5ComponentCConditionalDecoupling

variable {K M U Y : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-! ## The exact affine view and residual criterion -/

/-- The joint mask evaluator restricted to the admissible mask space
`ker ell`. -/
def jointMaskMap (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y) :
    LinearMap.ker ell →ₗ[K] U × Y :=
  (E.domRestrict (LinearMap.ker ell)).prod
    (F.domRestrict (LinearMap.ker ell))

/-- The full released/downstream view for one fixed public-coin schedule.
The first coordinate is the pre-C released contribution plus the released
mask evaluation.  The second coordinate is the downstream evaluator on the
pre-C word plus the batched mask. -/
def affineJointView (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (a : K) (u : U) (x : M) (c : LinearMap.ker ell) : U × Y :=
  (u + E (c : M), F (x + a • (c : M)))

/-- The residual which a single unscaled mask word must absorb.  The
released-coordinate residual is multiplied by `a` because the actual
translation is `a⁻¹ d`, whereas the downstream word contains `a * c`. -/
def scaledJointResidual (F : M →ₗ[K] Y) (a : K)
    (u₁ u₂ : U) (x₁ x₂ : M) : U × Y :=
  (a • (u₂ - u₁), F x₂ - F x₁)

/-- Exact algebraic applicability condition for the affine Component-C
coupling.  This is image membership for the *joint* map restricted to
`ker ell`; it is not a surjectivity claim. -/
def AffineResidualAbsorbable (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (F : M →ₗ[K] Y) (a : K) (u₁ u₂ : U) (x₁ x₂ : M) : Prop :=
  scaledJointResidual F a u₁ u₂ x₁ x₂ ∈
    LinearMap.range (jointMaskMap ell E F)

/-- Translation by a kernel element, as a genuine self-equivalence of the
whole admissible mask space. -/
def kerTranslationEquiv (ell : M →ₗ[K] K) (t : LinearMap.ker ell) :
    LinearMap.ker ell ≃ LinearMap.ker ell where
  toFun c := c + t
  invFun c := c - t
  left_inv c := by simp
  right_inv c := by simp

@[simp] theorem kerTranslationEquiv_apply (ell : M →ₗ[K] K)
    (t c : LinearMap.ker ell) :
    kerTranslationEquiv ell t c = c + t :=
  rfl

/-- For one proposed translation `t`, pointwise intertwining of the full
joint view is equivalent to the two exact residual equations.  This is the
necessity half as well as the sufficiency half: neither equation is
decorative. -/
theorem affineJointView_translation_iff
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (a : K) (u₁ u₂ : U) (x₁ x₂ : M) (t : LinearMap.ker ell) :
    (∀ c : LinearMap.ker ell,
        affineJointView ell E F a u₁ x₁ (kerTranslationEquiv ell t c)
          = affineJointView ell E F a u₂ x₂ c)
      ↔ E (t : M) = u₂ - u₁ ∧
          a • F (t : M) = F x₂ - F x₁ := by
  constructor
  · intro h
    have h₀ := h (0 : LinearMap.ker ell)
    rw [kerTranslationEquiv_apply] at h₀
    simp only [affineJointView, Submodule.coe_zero,
      map_zero, map_add, map_smul, zero_add, add_zero, smul_zero] at h₀
    have hp := Prod.mk.inj h₀
    constructor
    · have hE : u₁ + E (t : M) = u₂ := hp.1
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hE
    · have hF : F x₁ + a • F (t : M) = F x₂ := hp.2
      rw [eq_sub_iff_add_eq]
      simpa [add_comm] using hF
  · rintro ⟨hE, hF⟩ c
    apply Prod.ext
    · simp only [affineJointView, kerTranslationEquiv_apply,
        Submodule.coe_add, map_add]
      rw [hE]
      abel
    · simp only [affineJointView, kerTranslationEquiv_apply,
        Submodule.coe_add, smul_add, map_add, map_smul]
      rw [hF]
      abel

/-- Constructive form of the forward coupling.  If `d : ker ell` absorbs
the scaled released residual and the downstream residual, then translation
by exactly `a⁻¹ d` intertwines the complete views pointwise. -/
theorem affineJointView_translate_by_absorber
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {a : K} (ha : a ≠ 0) (u₁ u₂ : U) (x₁ x₂ : M)
    (d : LinearMap.ker ell)
    (hE : E (d : M) = a • (u₂ - u₁))
    (hF : F (d : M) = F x₂ - F x₁)
    (c : LinearMap.ker ell) :
    affineJointView ell E F a u₁ x₁
        (kerTranslationEquiv ell (a⁻¹ • d) c)
      = affineJointView ell E F a u₂ x₂ c := by
  apply (affineJointView_translation_iff ell E F a u₁ u₂ x₁ x₂
    (a⁻¹ • d)).2
  constructor
  · rw [Submodule.coe_smul, map_smul, hE, inv_smul_smul₀ ha]
  · rw [Submodule.coe_smul, map_smul, hF, smul_inv_smul₀ ha]

/-- **Necessity and sufficiency, exact image form.**  For `a != 0`, the
scaled joint residual lies in the image of `(E,F)|ker ell` iff there exists
a translation of `ker ell` that pointwise intertwines the two complete
affine views.  The forward translation is exactly `a⁻¹ d`, where `d` is
the image-membership witness; the reverse witness is exactly `a * t`. -/
theorem affineResidualAbsorbable_iff_translation
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {a : K} (ha : a ≠ 0) (u₁ u₂ : U) (x₁ x₂ : M) :
    AffineResidualAbsorbable ell E F a u₁ u₂ x₁ x₂ ↔
      ∃ t : LinearMap.ker ell, ∀ c : LinearMap.ker ell,
        affineJointView ell E F a u₁ x₁ (kerTranslationEquiv ell t c)
          = affineJointView ell E F a u₂ x₂ c := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := LinearMap.mem_range.mp h
    have hpair :
        (E (d : M), F (d : M)) =
          (a • (u₂ - u₁), F x₂ - F x₁) := hd
    rw [Prod.mk.injEq] at hpair
    refine ⟨a⁻¹ • d,
      (affineJointView_translation_iff ell E F a u₁ u₂ x₁ x₂
        (a⁻¹ • d)).2 ⟨?_, ?_⟩⟩
    · rw [Submodule.coe_smul, map_smul, hpair.1, inv_smul_smul₀ ha]
    · rw [Submodule.coe_smul, map_smul, hpair.2, smul_inv_smul₀ ha]
  · rintro ⟨t, ht⟩
    obtain ⟨hE, hF⟩ :=
      (affineJointView_translation_iff ell E F a u₁ u₂ x₁ x₂ t).1 ht
    refine LinearMap.mem_range.mpr ⟨a • t, ?_⟩
    change (E ((a • t : LinearMap.ker ell) : M),
        F ((a • t : LinearMap.ker ell) : M)) =
      (a • (u₂ - u₁), F x₂ - F x₁)
    rw [Submodule.coe_smul, map_smul, map_smul, hE, hF]

/-! ## Equality of the complete joint laws -/

/-- **The affine Component-C coupling theorem.**  At a fixed public-coin
schedule with nonzero batching scalar, exact joint-residual image membership
implies equality of the complete released/downstream laws under a uniform
mask on `ker ell`.  No conditioning `E c = e` and no equality `u₁ = u₂` is
required. -/
theorem componentC_affine_joint_law
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0) (u₁ u₂ : U) (x₁ x₂ : M)
    (habs : AffineResidualAbsorbable ell E F (gamma ^ 18)
      u₁ u₂ x₁ x₂) :
    (PMF.uniformOfFintype (LinearMap.ker ell)).map
        (affineJointView ell E F (gamma ^ 18) u₁ x₁)
      = (PMF.uniformOfFintype (LinearMap.ker ell)).map
          (affineJointView ell E F (gamma ^ 18) u₂ x₂) := by
  obtain ⟨t, ht⟩ :=
    (affineResidualAbsorbable_iff_translation ell E F
      (pow_ne_zero _ hgamma) u₁ u₂ x₁ x₂).1 habs
  exact uniform_map_eq_of_equiv_comp (kerTranslationEquiv ell t) ht

/-- Pre-word specialisation which makes the permitted `E`-difference
explicit: take the released offsets to be `E x₁` and `E x₂`.  The theorem
does not assume those values equal. -/
theorem componentC_preword_joint_law
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0) (x₁ x₂ : M)
    (habs : AffineResidualAbsorbable ell E F (gamma ^ 18)
      (E x₁) (E x₂) x₁ x₂) :
    (PMF.uniformOfFintype (LinearMap.ker ell)).map
        (affineJointView ell E F (gamma ^ 18) (E x₁) x₁)
      = (PMF.uniformOfFintype (LinearMap.ker ell)).map
          (affineJointView ell E F (gamma ^ 18) (E x₂) x₂) :=
  componentC_affine_joint_law ell E F hgamma (E x₁) (E x₂) x₁ x₂ habs

/-- **Unconditioned deployed-shape corollary.**  Suppose two normalized
pre-Component-C words agree under both the copy-inactive functional `ell`
and the released Component-C map `E`.  Then a mask sampled uniformly from
the whole space `ker ell` gives the same joint law of

`(E c, F (x + gamma^18 * c))`

for the two words.  This is the shape required of a candidate Rust
Component-C sampler and serializer: the first coordinate releases the C lane's own
`E c`, not `E x + E c`.  No fixed-fibre conditioning, disintegration
interface, or surjectivity hypothesis is needed. -/
theorem componentC_unconditioned_joint_law_of_matched_residuals
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {gamma : K} (hgamma : gamma ≠ 0) {x₁ x₂ : M}
    (hell : ell x₁ = ell x₂) (hE : E x₁ = E x₂) :
    (PMF.uniformOfFintype (LinearMap.ker ell)).map
        (fun c : LinearMap.ker ell =>
          (E ((c : LinearMap.ker ell) : M),
            F (x₁ + gamma ^ 18 • ((c : LinearMap.ker ell) : M))))
      = (PMF.uniformOfFintype (LinearMap.ker ell)).map
          (fun c : LinearMap.ker ell =>
            (E ((c : LinearMap.ker ell) : M),
              F (x₂ + gamma ^ 18 • ((c : LinearMap.ker ell) : M)))) := by
  let d : LinearMap.ker ell := ⟨x₂ - x₁, LinearMap.mem_ker.mpr (by
    rw [map_sub, sub_eq_zero]
    exact hell.symm)⟩
  have habs : AffineResidualAbsorbable ell E F (gamma ^ 18)
      0 0 x₁ x₂ := by
    refine LinearMap.mem_range.mpr ⟨d, ?_⟩
    change (E (x₂ - x₁), F (x₂ - x₁)) =
      ((gamma ^ 18) • (0 - 0), F x₂ - F x₁)
    rw [map_sub, map_sub]
    simp [hE]
  have hview₁ : affineJointView ell E F (gamma ^ 18) (0 : U) x₁ =
      fun c : LinearMap.ker ell =>
        (E ((c : LinearMap.ker ell) : M),
          F (x₁ + gamma ^ 18 • ((c : LinearMap.ker ell) : M))) := by
    funext c
    simp only [affineJointView, zero_add]
  have hview₂ : affineJointView ell E F (gamma ^ 18) (0 : U) x₂ =
      fun c : LinearMap.ker ell =>
        (E ((c : LinearMap.ker ell) : M),
          F (x₂ + gamma ^ 18 • ((c : LinearMap.ker ell) : M))) := by
    funext c
    simp only [affineJointView, zero_add]
  rw [← hview₁, ← hview₂]
  exact componentC_affine_joint_law ell E F hgamma
    (0 : U) (0 : U) x₁ x₂ habs

/-! ## Non-vacuity and a load-bearing negative model -/

section ScalarModels

variable (K : Type*) [Field K]

/-- Non-vacuity: with no relation restriction and identity `E,F`, the
nonzero residual `(1,1)` is absorbed by the single mask word `d = 1`. -/
theorem identity_model_absorbable :
    AffineResidualAbsorbable
      (0 : K →ₗ[K] K) (LinearMap.id : K →ₗ[K] K)
      (LinearMap.id : K →ₗ[K] K) 1 0 1 0 1 := by
  refine LinearMap.mem_range.mpr ⟨⟨1, by simp⟩, ?_⟩
  change ((1 : K), (1 : K)) = (1 • (1 - 0), 1 - 0)
  simp

/-- Negative model: when `ell` is the identity, the admissible mask space
is trivial, so the same nonzero residual is not in the restricted joint
image.  This proves that the image-membership premise is load-bearing. -/
theorem trivial_mask_space_not_absorbable :
    ¬ AffineResidualAbsorbable
      (LinearMap.id : K →ₗ[K] K) (LinearMap.id : K →ₗ[K] K)
      (LinearMap.id : K →ₗ[K] K) 1 0 1 0 1 := by
  intro h
  obtain ⟨d, hd⟩ := LinearMap.mem_range.mp h
  have hd₀ : (d : K) = 0 := LinearMap.mem_ker.mp d.2
  have hfirst := congrArg Prod.fst hd
  change (d : K) = 1 • (1 - 0) at hfirst
  rw [hd₀] at hfirst
  simp only [one_smul, sub_zero] at hfirst
  exact zero_ne_one hfirst

/-- The negative model also has no intertwining translation.  By the exact
iff above, this is not merely failure of our chosen witness construction. -/
theorem trivial_mask_space_no_translation :
    ¬ ∃ t : LinearMap.ker (LinearMap.id : K →ₗ[K] K),
      ∀ c : LinearMap.ker (LinearMap.id : K →ₗ[K] K),
        affineJointView (LinearMap.id : K →ₗ[K] K)
            (LinearMap.id : K →ₗ[K] K) (LinearMap.id : K →ₗ[K] K)
            1 0 0
            (kerTranslationEquiv (LinearMap.id : K →ₗ[K] K) t c)
          = affineJointView (LinearMap.id : K →ₗ[K] K)
              (LinearMap.id : K →ₗ[K] K) (LinearMap.id : K →ₗ[K] K)
              1 1 1 c := by
  rw [← affineResidualAbsorbable_iff_translation
    (LinearMap.id : K →ₗ[K] K) (LinearMap.id : K →ₗ[K] K)
    (LinearMap.id : K →ₗ[K] K) one_ne_zero 0 1 0 1]
  exact trivial_mask_space_not_absorbable K

end ScalarModels

/-- Concrete negative law over `ZMod 2`: after deleting the absorbability
premise, the two complete joint distributions in the trivial-mask model are
actually unequal.  Their released first coordinates are the distinct point
masses `0` and `1`. -/
theorem trivial_mask_space_joint_laws_differ :
    (PMF.uniformOfFintype
        (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))).map
        (affineJointView (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 0 0)
      ≠
    (PMF.uniformOfFintype
        (LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))).map
        (affineJointView (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
          (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 1 1) := by
  intro hcontra
  let C := LinearMap.ker (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
  have hleft :
      (Prod.fst ∘ affineJointView
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 0 0)
        = fun _ : C => (0 : ZMod 2) := by
    funext c
    have hc : (c : ZMod 2) = 0 := LinearMap.mem_ker.mp c.2
    simp [Function.comp_apply, affineJointView, hc]
  have hright :
      (Prod.fst ∘ affineJointView
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)
        (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) 1 1 1)
        = fun _ : C => (1 : ZMod 2) := by
    funext c
    have hc : (c : ZMod 2) = 0 := LinearMap.mem_ker.mp c.2
    simp [Function.comp_apply, affineJointView, hc]
  have hpure := congrArg
    (fun q : PMF (ZMod 2 × ZMod 2) => q.map Prod.fst) hcontra
  rw [PMF.map_comp, PMF.map_comp, hleft, hright] at hpure
  have hzero :
      (PMF.uniformOfFintype C).map (fun _ : C => (0 : ZMod 2))
        = PMF.pure 0 := by
    simpa [Function.const_def] using
      (PMF.map_const (PMF.uniformOfFintype C) (0 : ZMod 2))
  have hone :
      (PMF.uniformOfFintype C).map (fun _ : C => (1 : ZMod 2))
        = PMF.pure 1 := by
    simpa [Function.const_def] using
      (PMF.map_const (PMF.uniformOfFintype C) (1 : ZMod 2))
  rw [hzero, hone] at hpure
  have h₀ := congrArg (fun q : PMF (ZMod 2) => q 0) hpure
  rw [PMF.pure_apply, PMF.pure_apply, if_pos (by decide),
    if_neg (by decide)] at h₀
  exact one_ne_zero h₀

/-! ## Honest deployment interfaces -/

namespace UnmetDeployment

/-- The deployed fixed-public-coin A/B normalizer produces a joint
released/downstream residual in the image certified above.  This is a named,
unproved correspondence/interface proposition. -/
def NormalizedJointResidualAbsorbable
    (LegalPair : (U × M) → (U × M) → Prop)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (a : K) : Prop :=
  ∀ z₁ z₂, LegalPair z₁ z₂ →
    AffineResidualAbsorbable ell E F a z₁.1 z₂.1 z₁.2 z₂.2

/-- The abstract affine view above equals the deployed byte-decoded view for
the fixed public-coin schedule.  Left as an explicit unproved edge. -/
def DeployedViewIsAffine
    (ell : M →ₗ[K] K)
    (deployedView : (U × M) → LinearMap.ker ell → U × Y)
    (E : M →ₗ[K] U) (F : M →ₗ[K] Y) (a : K) : Prop :=
  ∀ z c, deployedView z c = affineJointView ell E F a z.1 z.2 c

end UnmetDeployment

#print axioms jointMaskMap
#print axioms affineJointView_translation_iff
#print axioms affineJointView_translate_by_absorber
#print axioms affineResidualAbsorbable_iff_translation
#print axioms componentC_affine_joint_law
#print axioms componentC_preword_joint_law
#print axioms componentC_unconditioned_joint_law_of_matched_residuals
#print axioms identity_model_absorbable
#print axioms trivial_mask_space_not_absorbable
#print axioms trivial_mask_space_no_translation
#print axioms trivial_mask_space_joint_laws_differ
#print axioms UnmetDeployment.NormalizedJointResidualAbsorbable
#print axioms UnmetDeployment.DeployedViewIsAffine

end AspisV5ComponentCAffineCoupling
