import AspisFormal.CoreHidingPMF

/-!
# Revealing one authenticated terminal functional of a mask: the hiding statement

This file formalises, as **pure linear algebra over a finite field plus a
finite-field probability-mass-function argument**, the sense in which opening a
single authenticated *terminal* functional of a mask leaves the remaining
*released* view independent of the witness.

The setting is a finite field `K`, a `K`-module `M` (the mask space), a linear
functional `terminal : M →ₗ[K] K` (the one opened value), and a linear map
`released : M →ₗ[K] V` (the rest of the released view).

Four statements are proved.

1. **Combined-surjective ⟹ restricted-surjective**
   (`restricted_surjective_of_prod_surjective`,
    `releasedKer_surjective_of_prod_surjective`).  If the joint map
   `m ↦ (terminal m, released m)` is surjective onto `K × V`, then `released`
   restricted to `LinearMap.ker terminal` is surjective onto `V` (hit the target
   `(0, v)`).

2. **Restricted-surjective ⟹ PMF equality** (`released_view_indep_on_ker`, with
   the reusable engine `released_view_pmf_indep`).  If `released` restricted to
   `LinearMap.ker terminal` is surjective, then adding a *uniform* element of
   `LinearMap.ker terminal` to any two witness-dependent released shifts yields
   the **same** released-view `PMF`.  This is `CoreHidingPMF.view_pmf_indep_of_witness`
   (the uniform pushforward through a surjective linear map is witness-free)
   transported from the coordinate space `Fin n → K` to an abstract finite
   `K`-module via a choice of basis.

3. **Affine-fibre equivalence** (`kerFibreEquiv`).  For a base point `m_t` with
   `terminal m_t = t`, the shift `k ↦ k + m_t` is a bijection
   `LinearMap.ker terminal ≃ {m // terminal m = t}`.  This is what lets the
   uniform-over-`ker` law model the uniform-over-`{terminal = t}` conditional.

4. **Final assembly** (`terminalOpening_hides_released_view`).  Fixing the
   terminal opening to `t` (so the first view coordinate is constantly `t`), the
   full released view `(terminal (m + k), released (m + k))` with `k` uniform in
   `LinearMap.ker terminal` has a distribution independent of which witness `m`
   with `terminal m = t` was used, provided the restricted view map is surjective.

**Scope of the claim.**  Everything here is a statement about linear maps of a
finite-dimensional vector space over a finite field and the uniform `PMF` on a
finite type.  Nothing is claimed about any deployed polynomial-commitment scheme,
about Fiat–Shamir adaptivity, or about computational binding; the surjectivity of
the restricted view map is an explicit hypothesis, not established here.
-/

open scoped ENNReal

namespace AspisV5RankOneOpeningHiding

/-! ## Decidability of kernel membership

Over a field with decidable equality the predicate `x ∈ LinearMap.ker terminal`
is decidable, which is what makes `LinearMap.ker terminal` a `Fintype` when the
mask space is finite. -/
instance decPredKer {K M : Type*} [Field K] [DecidableEq K] [AddCommGroup M] [Module K M]
    (terminal : M →ₗ[K] K) : DecidablePred (· ∈ LinearMap.ker terminal) :=
  fun x => decidable_of_iff (terminal x = 0) LinearMap.mem_ker.symm

/-! ## Auxiliary: the uniform `PMF` is carried to the uniform `PMF` by a bijection

Needed to transport `CoreHidingPMF.view_pmf_indep_of_witness` (stated on the
coordinate space `Fin n → K`) to an abstract finite `K`-module through a basis. -/

/-- Pushing the uniform distribution on a finite nonempty type `α` forward along a
bijection `e : α ≃ β` gives the uniform distribution on `β`. -/
theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  have hzero : ∀ a, a ≠ e.symm b →
      (if b = e a then (PMF.uniformOfFintype α) a else 0) = 0 := by
    intro a ha
    apply if_neg
    intro hba
    exact ha (by rw [hba, Equiv.symm_apply_apply])
  rw [tsum_eq_single (e.symm b) hzero, Equiv.apply_symm_apply, if_pos rfl,
      PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- The linear-equivalence flavour of `uniform_map_equiv`: a `K`-linear
isomorphism carries the uniform `PMF` to the uniform `PMF`. -/
theorem uniform_map_linearEquiv {K α β : Type*} [Field K]
    [AddCommGroup α] [Module K α] [AddCommGroup β] [Module K β]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (e : α ≃ₗ[K] β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β :=
  uniform_map_equiv e.toEquiv

/-! ## Theorem 1. Combined-surjective ⟹ restricted-surjective -/

/-- **Hitting the target `(0, v)`.**  If the joint map `m ↦ (terminal m, released m)`
is surjective onto `K × V`, then for every `v` there is a mask `m` on the
hyperplane `terminal m = 0` whose released view is `v`.  Proof: apply a section
(right inverse) of the joint map to the target `(0, v)`. -/
theorem restricted_surjective_of_prod_surjective
    {K M V : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup V] [Module K V]
    (terminal : M →ₗ[K] K) (released : M →ₗ[K] V)
    (hsurj : Function.Surjective (terminal.prod released)) :
    ∀ v : V, ∃ m : M, terminal m = 0 ∧ released m = v := by
  obtain ⟨g, hg⟩ := hsurj.hasRightInverse
  intro v
  exact ⟨g (0, v), congrArg Prod.fst (hg (0, v)), congrArg Prod.snd (hg (0, v))⟩

/-- **Restricted view map is surjective.**  The same fact stated as surjectivity
of `released` composed with the inclusion of `LinearMap.ker terminal`: this is the
hypothesis consumed by the `PMF` statements below. -/
theorem releasedKer_surjective_of_prod_surjective
    {K M V : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup V] [Module K V]
    (terminal : M →ₗ[K] K) (released : M →ₗ[K] V)
    (hsurj : Function.Surjective (terminal.prod released)) :
    Function.Surjective (released ∘ₗ (LinearMap.ker terminal).subtype) := by
  intro v
  obtain ⟨m, hmem, hv⟩ := restricted_surjective_of_prod_surjective terminal released hsurj v
  exact ⟨⟨m, LinearMap.mem_ker.mpr hmem⟩, hv⟩

/-! ## Theorem 2. Restricted-surjective ⟹ PMF equality

The reusable engine `released_view_pmf_indep` is `view_pmf_indep_of_witness`
(from `CoreHidingPMF`, on the coordinate space `Fin n → K`) transported to an
abstract finite `K`-module `D` and abstract finite-dimensional codomain `V` by
choosing bases `D ≃ₗ Fin (finrank K D) → K` and `V ≃ₗ Fin (finrank K V) → K`.
No fibre-counting is redone here; the whole content is imported. -/

/-- **Uniform mask through a surjective linear map hides the additive shift.**
For a surjective `K`-linear `A : D →ₗ[K] V` between finite `K`-vector spaces,
sampling `k` uniformly from `D` and forming `w + A k` yields a released-view `PMF`
that does not depend on the shift `w`.  Proof: transport
`CoreHidingPMF.view_pmf_indep_of_witness` along bases of `D` and `V`. -/
theorem released_view_pmf_indep
    {K D V : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommGroup D] [Module K D] [Fintype D] [Nonempty D]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : D →ₗ[K] V) (hA : Function.Surjective A) (w₁ w₂ : V) :
    (PMF.uniformOfFintype D).map (fun k => w₁ + A k)
      = (PMF.uniformOfFintype D).map (fun k => w₂ + A k) := by
  haveI : FiniteDimensional K D := Module.Finite.of_finite
  set eD := (Module.finBasis K D).equivFun
  set eV := (Module.finBasis K V).equivFun
  set A' : (Fin (Module.finrank K D) → K) →ₗ[K] (Fin (Module.finrank K V) → K) :=
      eV.toLinearMap ∘ₗ A ∘ₗ eD.symm.toLinearMap with hA'def
  have hA' : Function.Surjective A' := by
    rw [hA'def]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
    exact eV.surjective.comp (hA.comp eD.symm.surjective)
  -- transport identity: viewing the released `PMF` through `eV` recovers the
  -- coordinate-space `PMF` that `CoreHidingPMF` speaks about.
  have key : ∀ w : V,
      ((PMF.uniformOfFintype D).map (fun k => w + A k)).map eV
        = (PMF.uniformOfFintype (Fin (Module.finrank K D) → K)).map (fun R => eV w + A' R) := by
    intro w
    rw [PMF.map_comp, ← uniform_map_linearEquiv eD.symm, PMF.map_comp]
    congr 1
    funext R
    rw [hA'def]
    simp only [Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, map_add]
  have hcore := view_pmf_indep_of_witness A' hA' (eV w₁) (eV w₂)
  have hcomp_id : (⇑eV.symm ∘ ⇑eV) = id := funext fun x => eV.symm_apply_apply x
  calc (PMF.uniformOfFintype D).map (fun k => w₁ + A k)
      = (((PMF.uniformOfFintype D).map (fun k => w₁ + A k)).map eV).map eV.symm := by
        rw [PMF.map_comp, hcomp_id, PMF.map_id]
    _ = ((PMF.uniformOfFintype (Fin (Module.finrank K D) → K)).map
          (fun R => eV w₁ + A' R)).map eV.symm := by rw [key w₁]
    _ = ((PMF.uniformOfFintype (Fin (Module.finrank K D) → K)).map
          (fun R => eV w₂ + A' R)).map eV.symm := by rw [hcore]
    _ = (((PMF.uniformOfFintype D).map (fun k => w₂ + A k)).map eV).map eV.symm := by rw [key w₂]
    _ = (PMF.uniformOfFintype D).map (fun k => w₂ + A k) := by
        rw [PMF.map_comp, hcomp_id, PMF.map_id]

/-- **Theorem 2 in the terminal/released language.**  If `released` restricted to
`LinearMap.ker terminal` is surjective, then adding a uniform element of
`LinearMap.ker terminal` to two witness-dependent released shifts `w₁`, `w₂`
produces the same released-view `PMF`.  A direct specialisation of
`released_view_pmf_indep` with `D := LinearMap.ker terminal` and
`A := released ∘ₗ (LinearMap.ker terminal).subtype`. -/
theorem released_view_indep_on_ker
    {K M V : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommGroup M] [Module K M] [Fintype M]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (terminal : M →ₗ[K] K) (released : M →ₗ[K] V)
    (hrel : Function.Surjective (released ∘ₗ (LinearMap.ker terminal).subtype))
    (w₁ w₂ : V) :
    (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun (k : LinearMap.ker terminal) => w₁ + released (k : M))
      = (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun (k : LinearMap.ker terminal) => w₂ + released (k : M)) :=
  released_view_pmf_indep (released ∘ₗ (LinearMap.ker terminal).subtype) hrel w₁ w₂

/-! ## Theorem 3. The affine-fibre equivalence -/

/-- **Affine-fibre equivalence.**  For a base point `m_t` with `terminal m_t = t`,
the shift `k ↦ k + m_t` is a bijection from the kernel hyperplane
`LinearMap.ker terminal` onto the affine fibre `{m // terminal m = t}`, with
inverse `m ↦ m - m_t`.  This realises the uniform distribution on the fibre as the
pushforward of the uniform distribution on `LinearMap.ker terminal`. -/
def kerFibreEquiv {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (terminal : M →ₗ[K] K) (t : K) (m_t : M) (ht : terminal m_t = t) :
    (LinearMap.ker terminal) ≃ {m : M // terminal m = t} where
  toFun k := ⟨(k : M) + m_t, by
    rw [map_add, LinearMap.mem_ker.mp k.2, zero_add, ht]⟩
  invFun m := ⟨(m : M) - m_t, LinearMap.mem_ker.mpr (by rw [map_sub, m.2, ht, sub_self])⟩
  left_inv k := by apply Subtype.ext; simp
  right_inv m := by apply Subtype.ext; simp

/-! ## Theorem 4. Final assembly in v5 language -/

/-- **Revealing one terminal opening hides the remaining released view.**
Fix the terminal opening to `t`, and take two witnesses `m₁`, `m₂` realising it
(`terminal m₁ = terminal m₂ = t`).  Randomising each by a uniform element `k` of
`LinearMap.ker terminal`, the full released view `(terminal (mᵢ + k), released (mᵢ + k))`
— whose first coordinate is constantly `t` — has a distribution independent of the
witness, provided the restricted view map `released ∘ₗ (LinearMap.ker terminal).subtype`
is surjective. -/
theorem terminalOpening_hides_released_view
    {K M V : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommGroup M] [Module K M] [Fintype M]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (terminal : M →ₗ[K] K) (released : M →ₗ[K] V)
    (hrel : Function.Surjective (released ∘ₗ (LinearMap.ker terminal).subtype))
    (t : K) (m₁ m₂ : M) (h₁ : terminal m₁ = t) (h₂ : terminal m₂ = t) :
    (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun (k : LinearMap.ker terminal) => (terminal (m₁ + (k : M)), released (m₁ + (k : M))))
      = (PMF.uniformOfFintype (LinearMap.ker terminal)).map
        (fun (k : LinearMap.ker terminal) =>
          (terminal (m₂ + (k : M)), released (m₂ + (k : M)))) := by
  have hview := released_view_indep_on_ker terminal released hrel (released m₁) (released m₂)
  have hrw : ∀ m : M, terminal m = t →
      (fun k : LinearMap.ker terminal => (terminal (m + (k : M)), released (m + (k : M))))
        = (fun x => (t, x)) ∘
          (fun k : LinearMap.ker terminal => released m + released (k : M)) := by
    intro m hm
    funext k
    have hk : terminal (k : M) = 0 := LinearMap.mem_ker.mp k.2
    simp only [Function.comp_apply, map_add, hk, add_zero, hm]
  rw [hrw m₁ h₁, hrw m₂ h₂, ← PMF.map_comp, ← PMF.map_comp, hview]

/-! ## Non-vacuity witness

The hypotheses above are satisfiable, so the statements are not vacuous.  Over any
finite field `K`, the mask space `Fin 2 → K` with `terminal` the first coordinate
and `released` the second has a surjective joint map; hence (by Theorem 1) its
restricted view map `released ∘ₗ (ker terminal).subtype` is surjective — the
explicit hypothesis of Theorems 2 and 4. -/
theorem restricted_view_map_instantiable {K : Type*} [Field K] :
    Function.Surjective
      ((LinearMap.proj 1 : (Fin 2 → K) →ₗ[K] K) ∘ₗ
        (LinearMap.ker (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K)).subtype) := by
  apply releasedKer_surjective_of_prod_surjective
  intro p
  exact ⟨![p.1, p.2], by simp⟩

#print axioms uniform_map_equiv
#print axioms uniform_map_linearEquiv
#print axioms restricted_surjective_of_prod_surjective
#print axioms releasedKer_surjective_of_prod_surjective
#print axioms released_view_pmf_indep
#print axioms released_view_indep_on_ker
#print axioms kerFibreEquiv
#print axioms terminalOpening_hides_released_view
#print axioms restricted_view_map_instantiable

end AspisV5RankOneOpeningHiding
