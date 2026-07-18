import AspisFormal.V5RankOneOpeningHiding

/-!
# v5 Component C: the conditional-decoupling (C-DEC) translation/fibre theorem

This file formalises the exact theorem named `(C-DEC)` in
`results/spend/v5_component_c_design_audit.md`, and nothing stronger.

**The audit's statement, reproduced.**  For the fixed Fiat–Shamir schedule
`σ` the audit defines the mask space `C = ker ℓ` (a hyperplane of the
coefficient-word space `V`), the map `E_σ : C → K^76` of the 76
conditioned/released Component-C coordinates (72 authenticated layer-zero
values, three MLE claims, one structured terminal claim), the map
`F_σ : V → Y_σ` of every post-combination field coordinate (all four rounds'
OOD and relation-sumcheck values, the three later FRI opening layers, the
four final coefficients), and the legal witness-difference space `Δ_σ`
(the span of the differences `X_γ(w) − X_γ(w')` allowed by the accepted v5
relation — **not** all of `V`).  The required containment is

    F_σ(Δ_σ) ≤ image (F_σ restricted to (C ∩ ker E_σ))          (C-DEC)

equivalently, with `J_σ(c) = (E_σ(c), F_σ(γ^18 · c))`,

    (0, F_σ(δ)) ∈ image J_σ   for every δ ∈ Δ_σ.

The audit is explicit that full row rank of the 332×1023 joint matrix is
sufficient but **not** necessary, and that `(C-DEC)` — not any surjectivity
slogan — is the correct target.  Accordingly:

* the hypothesis used everywhere below is exactly `(C-DEC)` (`CDec`,
  `CDecAudit`), never surjectivity of `E`, of `F`, or of `E.prod F`;
* the file exhibits a model (`toyE`, `toyF`) in which `(C-DEC)` holds while
  `E`, `F` and `(E, F)` are all **non**-surjective, so the hypothesis cannot
  secretly be a full-rank assumption.

**What is proved.**  Under `(C-DEC)`, for two legal witnesses whose
released-view difference lies in the legal difference space, translation by
the `(C-DEC)` witness `c₀` (which satisfies `E c₀ = 0` and `F c₀ = δ`) is a
bijection of the conditioned mask fibre `{mask // E mask = e}` that
intertwines the two complete post-combination views
(`cDec_translation_fibre`, `componentC_translation_between_witness_fibres`).
Consequently the `F`-view of a uniform mask conditioned on `E = e` is a
witness-independent probability distribution, as an exact `PMF` equality
(`cDec_view_pmf_indep`, `cDec_complete_view_pmf_indep`,
`componentC_full_fold_conditional_decoupling`), and the same holds for the
literal conditional law obtained by `PMF.filter`-conditioning the uniform
distribution on all of `C` on the event `E = e`
(`cDec_conditional_law_witness_indep`).

**What is not proved.**  Nothing here identifies these abstract linear maps
with the deployed Rust arithmetic, establishes sampler uniformity,
Fiat–Shamir ordering, claim authentication, serialization completeness, or
the circle/arity-4 fold transport.  Each of those is recorded as an explicit
*named*, *unproved* interface `Prop` at the end of the file; none of them is
discharged by definition.  The dimension counts (76, 40 + 4·(n₁+n₂+n₃), 332)
are pinned as kernel arithmetic and are labelled as bookkeeping only — they
are *not* evidence for `(C-DEC)`.

The uniform-pushforward machinery is reused from
`AspisFormal.V5RankOneOpeningHiding` (`uniform_map_equiv`) and, through it,
from `AspisFormal.CoreHidingPMF`.
-/

open scoped ENNReal
open AspisV5RankOneOpeningHiding

namespace AspisV5ComponentCConditionalDecoupling

/-! ## The C-DEC hypothesis and its equivalent forms

`C` is the mask space (in the audit, the hyperplane `ker ℓ`; here an
arbitrary `K`-module so that the statement can be instantiated both
abstractly and on `ker ℓ` below).  `E` is the map of conditioned/released
coordinates, `F` the map of post-combination coordinates, and `Δ` the legal
witness-difference space *transported into the view space* `Y` (the audit's
`F_σ(Δ_σ)`; the word-space form is `CDecAudit` below). -/

section AbstractCDEC

variable {K : Type*} [Field K] {C U Y : Type*}
  [AddCommGroup C] [Module K C] [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-- **The C-DEC hypothesis, exactly as in the audit.**  Every legal
witness-difference direction `δ ∈ Δ` is realised by a mask `c` that is
invisible to the conditioned coordinates (`E c = 0`) and shifts the
post-combination view by exactly `δ` (`F c = δ`).  This is the containment
`Δ ≤ image (F restricted to ker E)`, i.e. the audit's
`F_σ(Δ_σ) ≤ image (F_σ | C ∩ ker E_σ)`.  It is **not** surjectivity of `E`,
of `F`, or of the joint map. -/
def CDec (E : C →ₗ[K] U) (F : C →ₗ[K] Y) (Δ : Submodule K Y) : Prop :=
  ∀ δ ∈ Δ, ∃ c : C, E c = 0 ∧ F c = δ

/-- C-DEC restated as the audit's image-membership form: for every `δ ∈ Δ`
the pair `(0, δ)` lies in the image of the joint map `c ↦ (E c, F c)`. -/
theorem cDec_iff_zero_pair_mem_range (E : C →ₗ[K] U) (F : C →ₗ[K] Y)
    (Δ : Submodule K Y) :
    CDec E F Δ ↔ ∀ δ ∈ Δ, ((0 : U), δ) ∈ LinearMap.range (E.prod F) := by
  constructor
  · intro h δ hδ
    obtain ⟨c, h0, hc⟩ := h δ hδ
    refine LinearMap.mem_range.mpr ⟨c, ?_⟩
    show (E c, F c) = (0, δ)
    rw [h0, hc]
  · intro h δ hδ
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (h δ hδ)
    have hc' : (E c, F c) = (0, δ) := hc
    rw [Prod.mk.injEq] at hc'
    exact ⟨c, hc'.1, hc'.2⟩

/-- C-DEC restated as the audit's containment form:
`Δ ≤ Submodule.map F (ker E)`, i.e. the legal difference space is contained
in the image of `F` restricted to the `E`-invisible masks. -/
theorem cDec_iff_le_map_ker (E : C →ₗ[K] U) (F : C →ₗ[K] Y)
    (Δ : Submodule K Y) :
    CDec E F Δ ↔ Δ ≤ Submodule.map F (LinearMap.ker E) := by
  constructor
  · intro h δ hδ
    obtain ⟨c, h0, hc⟩ := h δ hδ
    exact Submodule.mem_map.mpr ⟨c, LinearMap.mem_ker.mpr h0, hc⟩
  · intro h δ hδ
    obtain ⟨c, hker, hc⟩ := Submodule.mem_map.mp (h hδ)
    exact ⟨c, LinearMap.mem_ker.mp hker, hc⟩

/-- The audit's joint map `J_σ(c) = (E_σ(c), F_σ(γ^18 · c))`, as a linear
map.  The scalar `γ^18` is the lane-batching power that the C helper receives
in `prepare_generic16`/`generic_combine`. -/
def Jmap (E : C →ₗ[K] U) (F : C →ₗ[K] Y) (γ : K) : C →ₗ[K] U × Y :=
  E.prod (γ ^ 18 • F)

/-- `Jmap` computes the audit's formula `J_σ(c) = (E_σ(c), F_σ(γ^18 · c))`. -/
theorem Jmap_apply (E : C →ₗ[K] U) (F : C →ₗ[K] Y) (γ : K) (c : C) :
    Jmap E F γ c = (E c, F (γ ^ 18 • c)) := by
  simp [Jmap, LinearMap.prod_apply, map_smul]

/-- **C-DEC in the audit's `J_σ` form.**  For `γ ≠ 0`, the hypothesis
`CDec E F Δ` is equivalent to: `(0, δ) ∈ image J_σ` for every `δ ∈ Δ`.
The nonzero batching power `γ^18` neither helps nor hurts: it only rescales
the witnessing mask. -/
theorem cDec_iff_J (E : C →ₗ[K] U) (F : C →ₗ[K] Y) (Δ : Submodule K Y)
    {γ : K} (hγ : γ ≠ 0) :
    CDec E F Δ ↔ ∀ δ ∈ Δ, ((0 : U), δ) ∈ LinearMap.range (Jmap E F γ) := by
  have h18 : γ ^ 18 ≠ 0 := pow_ne_zero _ hγ
  constructor
  · intro h δ hδ
    obtain ⟨c, h0, hc⟩ := h δ hδ
    refine LinearMap.mem_range.mpr ⟨(γ ^ 18)⁻¹ • c, ?_⟩
    rw [Jmap_apply, smul_inv_smul₀ h18, hc, map_smul, h0, smul_zero]
  · intro h δ hδ
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (h δ hδ)
    rw [Jmap_apply, Prod.mk.injEq] at hc
    exact ⟨γ ^ 18 • c, by rw [map_smul, hc.1, smul_zero], hc.2⟩

/-- C-DEC is stable under rescaling the view map by a nonzero scalar (used to
absorb the batching power `γ^18` into `F`). -/
theorem cDec_smul {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {Δ : Submodule K Y}
    {a : K} (ha : a ≠ 0) (h : CDec E F Δ) : CDec E (a • F) Δ := by
  intro δ hδ
  obtain ⟨c, h0, hc⟩ := h δ hδ
  refine ⟨a⁻¹ • c, ?_, ?_⟩
  · rw [map_smul, h0, smul_zero]
  · rw [LinearMap.smul_apply, map_smul, smul_inv_smul₀ ha, hc]

/-- **The full-rank slogan is sufficient but strictly stronger.**  If the
joint map `c ↦ (E c, F c)` is surjective then C-DEC holds for *every* `Δ`.
This lemma is recorded only to locate C-DEC below the slogan; it is *not*
the hypothesis used by any theorem in this file, and `toy_cDec` below shows
the converse fails. -/
theorem cDec_of_prod_surjective {E : C →ₗ[K] U} {F : C →ₗ[K] Y}
    (h : Function.Surjective (E.prod F)) (Δ : Submodule K Y) :
    CDec E F Δ := by
  intro δ _
  obtain ⟨c, hc⟩ := h (0, δ)
  have hc' : (E c, F c) = (0, δ) := hc
  rw [Prod.mk.injEq] at hc'
  exact ⟨c, hc'.1, hc'.2⟩

/-! ## The translation bijection of the conditioned mask fibre -/

/-- **Translation of the conditioned fibre by an `E`-invisible mask.**
For `c₀` with `E c₀ = 0`, the map `mask ↦ mask + c₀` is a bijection of the
conditioned mask fibre `{mask // E mask = e}` (inverse: subtract `c₀`).
This is the audit's "translation by any legal witness difference permutes
that fibre": instantiated at the C-DEC witness `c₀` for a legal difference,
it carries one witness's conditional mask ensemble onto the other's. -/
def translationEquiv (E : C →ₗ[K] U) (e : U) (c₀ : C) (hc₀ : E c₀ = 0) :
    {c : C // E c = e} ≃ {c : C // E c = e} where
  toFun c := ⟨(c : C) + c₀, by rw [map_add, c.2, hc₀, add_zero]⟩
  invFun c := ⟨(c : C) - c₀, by rw [map_sub, c.2, hc₀, sub_zero]⟩
  left_inv c := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp

/-- `translationEquiv` acts on the underlying mask by adding `c₀`. -/
@[simp] theorem translationEquiv_apply (E : C →ₗ[K] U) (e : U) (c₀ : C)
    (hc₀ : E c₀ = 0) (c : {c : C // E c = e}) :
    ((translationEquiv E e c₀ hc₀ c : {c : C // E c = e}) : C) = (c : C) + c₀ :=
  rfl

/-- **The C-DEC translation/fibre theorem (exact, no finiteness needed).**
Assume C-DEC, and let `y₁`, `y₂` be the two witnesses' contributions to the
post-combination view, with legal difference `y₂ - y₁ ∈ Δ`.  Then there is a
C-DEC witness `c₀` — `E`-invisible, `F`-image exactly the difference — such
that for *every* conditioning value `e`, translation by `c₀` is a bijection
of the conditioned mask fibre `{c // E c = e}` intertwining the two complete
views: `y₁ + F (c + c₀) = y₂ + F c`.  The `E`-conditioning is untouched
because `E c₀ = 0`; the `F`-view is shifted by exactly the legal difference
because `F c₀ = y₂ - y₁`. -/
theorem cDec_translation_fibre {E : C →ₗ[K] U} {F : C →ₗ[K] Y}
    {Δ : Submodule K Y} (hdec : CDec E F Δ) {y₁ y₂ : Y}
    (hy : y₂ - y₁ ∈ Δ) :
    ∃ (c₀ : C) (hc₀ : E c₀ = 0), F c₀ = y₂ - y₁ ∧
      ∀ (e : U) (c : {c : C // E c = e}),
        y₁ + F ((translationEquiv E e c₀ hc₀ c : {c : C // E c = e}) : C)
          = y₂ + F (c : C) := by
  obtain ⟨c₀, hc₀, hFc₀⟩ := hdec _ hy
  refine ⟨c₀, hc₀, hFc₀, fun e c => ?_⟩
  rw [translationEquiv_apply, map_add, hFc₀]
  abel

/-- **The conditioned fibre is an affine coset of `ker E`.**  Any base point
`c_e` with `E c_e = e` shifts the kernel onto the fibre bijectively.  This is
the audit's "the conditional fibre of C is a uniform affine coset". -/
def fibreEquivKer (E : C →ₗ[K] U) (e : U) (c_e : C) (h : E c_e = e) :
    LinearMap.ker E ≃ {c : C // E c = e} where
  toFun k := ⟨(k : C) + c_e, by rw [map_add, LinearMap.mem_ker.mp k.2, zero_add, h]⟩
  invFun c := ⟨(c : C) - c_e,
    LinearMap.mem_ker.mpr (by rw [map_sub, c.2, h, sub_self])⟩
  left_inv k := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp

end AbstractCDEC

/-! ## The exact PMF statements (finite mask space)

The audit's requirement is an equality of conditional *laws*:

    Law(F_σ(W_γ(w, C_uniform)) | E_σ(C_uniform) = e)
      = Law(F_σ(W_γ(w', C_uniform)) | E_σ(C_uniform) = e).

Here this is proved twice, exactly: once with the conditional law modelled
as the uniform distribution on the conditioned fibre (which
`uniform_conditioned_eq_uniform_fibre` shows *is* the `PMF.filter`
conditioning of the uniform mask law), and once literally as a
`PMF.filter` statement. -/

section PMFLayer

/-- Pushing the uniform distribution through `f` and through `g` gives the
same `PMF` whenever `g` is `f` precomposed with a self-bijection.  This is
`uniform_map_equiv` (uniformity is translation invariant) specialised to the
intertwining shape produced by `cDec_translation_fibre`. -/
theorem uniform_map_eq_of_equiv_comp {α β : Type*} [Fintype α] [Nonempty α]
    (T : α ≃ α) {f g : α → β} (h : ∀ a, f (T a) = g a) :
    (PMF.uniformOfFintype α).map f = (PMF.uniformOfFintype α).map g := by
  have hg : g = f ∘ ⇑T := funext fun a => (h a).symm
  rw [hg, ← PMF.map_comp, uniform_map_equiv T]

variable {K : Type*} [Field K] {C U Y : Type*}
  [AddCommGroup C] [Module K C] [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-- **C-DEC ⟹ the conditioned released view is witness-independent (exact
`PMF` equality).**  Sample the mask uniformly from the conditioned fibre
`{c // E c = e}` and release `yᵢ + F c` (the witness's post-combination
contribution plus the mask's).  Under C-DEC, if the witness difference
`y₂ - y₁` is legal, the two released-view distributions are the *same* `PMF`.
The proof is translation by the C-DEC witness `c₀`: it fixes the fibre
(because `E c₀ = 0`), pushes the uniform law to itself, and shifts the
`F`-view by exactly the legal difference (because `F c₀ = y₂ - y₁`). -/
theorem cDec_view_pmf_indep [Fintype C] [DecidableEq U]
    {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {Δ : Submodule K Y}
    (hdec : CDec E F Δ) {y₁ y₂ : Y} (hy : y₂ - y₁ ∈ Δ) (e : U)
    [Nonempty {c : C // E c = e}] :
    (PMF.uniformOfFintype {c : C // E c = e}).map
        (fun c : {c : C // E c = e} => y₁ + F (c : C))
      = (PMF.uniformOfFintype {c : C // E c = e}).map
          (fun c : {c : C // E c = e} => y₂ + F (c : C)) := by
  obtain ⟨c₀, hc₀, _, hview⟩ := cDec_translation_fibre hdec hy
  exact uniform_map_eq_of_equiv_comp (translationEquiv E e c₀ hc₀)
    (f := fun c : {c : C // E c = e} => y₁ + F (c : C))
    (g := fun c : {c : C // E c = e} => y₂ + F (c : C)) (hview e)

/-- **C-DEC ⟹ the *complete* view (conditioned coordinates and
post-combination view together) is witness-independent.**  The released pair
is `(E c, yᵢ + F c)`; on the conditioned fibre the first component is
constantly `e`, and the second is handled by `cDec_view_pmf_indep`.  This is
the "complete post-combination view law" form: nothing about the joint law
of the 76 conditioned coordinates and the post-combination coordinates
distinguishes the witnesses. -/
theorem cDec_complete_view_pmf_indep [Fintype C] [DecidableEq U]
    {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {Δ : Submodule K Y}
    (hdec : CDec E F Δ) {y₁ y₂ : Y} (hy : y₂ - y₁ ∈ Δ) (e : U)
    [Nonempty {c : C // E c = e}] :
    (PMF.uniformOfFintype {c : C // E c = e}).map
        (fun c : {c : C // E c = e} => (E (c : C), y₁ + F (c : C)))
      = (PMF.uniformOfFintype {c : C // E c = e}).map
          (fun c : {c : C // E c = e} => (E (c : C), y₂ + F (c : C))) := by
  obtain ⟨c₀, hc₀, _, hview⟩ := cDec_translation_fibre hdec hy
  refine uniform_map_eq_of_equiv_comp (translationEquiv E e c₀ hc₀)
    (f := fun c : {c : C // E c = e} => (E (c : C), y₁ + F (c : C)))
    (g := fun c : {c : C // E c = e} => (E (c : C), y₂ + F (c : C)))
    (fun c => ?_)
  simp only [Prod.mk.injEq]
  exact ⟨by rw [(translationEquiv E e c₀ hc₀ c).2, c.2], hview e c⟩

/-- The conditioning event `{c | E c = e}` is charged by the uniform mask
law as soon as the fibre is nonempty — i.e. exactly when `e` is in the image
of `E`, which is the audit's "every `e` in the image of `E_σ`". -/
theorem fibre_conditioning_witness [Fintype C] {E : C →ₗ[K] U} (e : U)
    [ne : Nonempty {c : C // E c = e}] :
    ∃ c ∈ {c : C | E c = e}, c ∈ (PMF.uniformOfFintype C).support := by
  obtain ⟨c⟩ := ne
  exact ⟨c.1, c.2, PMF.mem_support_uniformOfFintype c.1⟩

/-- **Conditioning the uniform mask law on `E = e` *is* the uniform law on
the fibre.**  The `PMF.filter`-conditional of `PMF.uniformOfFintype C` on the
event `{c | E c = e}` equals the pushforward of the uniform distribution on
the subtype `{c // E c = e}`.  This discharges the modelling step "the
conditional law of a uniform mask given its conditioned coordinates is
uniform on the conditioned fibre" as a theorem instead of a convention. -/
theorem uniform_conditioned_eq_uniform_fibre [Fintype C] [DecidableEq U]
    (E : C →ₗ[K] U) (e : U) [Nonempty {c : C // E c = e}]
    (h : ∃ c ∈ {c : C | E c = e}, c ∈ (PMF.uniformOfFintype C).support) :
    (PMF.uniformOfFintype C).filter {c : C | E c = e} h
      = (PMF.uniformOfFintype {c : C // E c = e}).map Subtype.val := by
  have hC0 : (Fintype.card C : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hCt : (Fintype.card C : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hcard : Fintype.card ↥{c : C | E c = e}
      = Fintype.card {c : C // E c = e} := Fintype.card_congr (Equiv.refl _)
  apply PMF.ext
  intro a
  rw [PMF.filter_apply, PMF.map_apply, ← PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  by_cases ha : E a = e
  · rw [Set.indicator_of_mem (show a ∈ {c : C | E c = e} from ha),
      PMF.uniformOfFintype_apply, hcard,
      tsum_eq_single (⟨a, ha⟩ : {c : C // E c = e}), if_pos rfl,
      PMF.uniformOfFintype_apply,
      ENNReal.inv_div (Or.inl hCt) (Or.inl hC0), div_eq_mul_inv,
      ← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]
    intro b hb
    exact if_neg (mt (fun hab : a = (b : C) => Subtype.ext (Eq.symm hab)) hb)
  · rw [Set.indicator_of_notMem (show a ∉ {c : C | E c = e} from ha), zero_mul]
    refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
    exact if_neg fun hab : a = (b : C) => ha (by rw [hab]; exact b.2)

/-- **C-DEC ⟹ the literal conditional law is witness-independent.**  The
audit's statement verbatim: conditioning the uniform mask distribution on
the released coordinates `E = e` (via `PMF.filter`), the distribution of the
post-combination view `yᵢ + F c` is the same for both witnesses whenever
their difference is legal.  Obtained by rewriting the conditional as the
uniform fibre law (`uniform_conditioned_eq_uniform_fibre`) and applying
`cDec_view_pmf_indep`. -/
theorem cDec_conditional_law_witness_indep [Fintype C] [DecidableEq U]
    {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {Δ : Submodule K Y}
    (hdec : CDec E F Δ) {y₁ y₂ : Y} (hy : y₂ - y₁ ∈ Δ) (e : U)
    [Nonempty {c : C // E c = e}]
    (h : ∃ c ∈ {c : C | E c = e}, c ∈ (PMF.uniformOfFintype C).support) :
    ((PMF.uniformOfFintype C).filter {c : C | E c = e} h).map
        (fun c => y₁ + F c)
      = ((PMF.uniformOfFintype C).filter {c : C | E c = e} h).map
          (fun c => y₂ + F c) := by
  rw [uniform_conditioned_eq_uniform_fibre E e h, PMF.map_comp, PMF.map_comp]
  exact cDec_view_pmf_indep hdec hy e

end PMFLayer

/-! ## C-DEC is not a full-rank slogan: a witness model

The audit warns that "full row rank … is sufficient but not necessary" and
forbids replacing C-DEC by a surjectivity assumption.  The following toy
model certifies, inside the kernel, that the C-DEC hypothesis used above is
strictly weaker than every surjectivity variant: `CDec toyE toyF Δ` holds
while `toyE`, `toyF` and `toyE.prod toyF` are all non-surjective.  Hence no
theorem in this file can be secretly consuming "E and F independently
surjective" — that hypothesis is *false* in this model while C-DEC and all
the theorems above still apply to it. -/

section NotFullRank

variable (K : Type*) [Field K]

/-- Toy conditioned-coordinate map: `c ↦ Pi.single 0 (c 1)`.  Deliberately
not surjective. -/
def toyE : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (LinearMap.single K (fun _ : Fin 2 => K) 0) ∘ₗ
    (LinearMap.proj 1 : (Fin 2 → K) →ₗ[K] K)

/-- Toy post-combination view map: `c ↦ Pi.single 0 (c 0)`.  Deliberately
not surjective. -/
def toyF : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (LinearMap.single K (fun _ : Fin 2 => K) 0) ∘ₗ
    (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K)

/-- `toyE` computes `Pi.single 0 (c 1)`. -/
theorem toyE_apply (c : Fin 2 → K) : toyE K c = Pi.single 0 (c 1) := rfl

/-- `toyF` computes `Pi.single 0 (c 0)`. -/
theorem toyF_apply (c : Fin 2 → K) : toyF K c = Pi.single 0 (c 0) := rfl

/-- In the toy model, C-DEC holds with `Δ` the full range of the view map:
every legal difference `F v` is realised by the `E`-invisible mask `F v`
itself. -/
theorem toy_cDec : CDec (toyE K) (toyF K) (LinearMap.range (toyF K)) := by
  intro δ hδ
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hδ
  refine ⟨toyF K v, ?_, ?_⟩
  · rw [toyE_apply, toyF_apply,
      Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), Pi.single_zero]
  · rw [toyF_apply, toyF_apply, Pi.single_eq_same]

/-- In the toy model the conditioned-coordinate map is *not* surjective:
C-DEC does not require it to be. -/
theorem toyE_not_surjective : ¬ Function.Surjective (toyE K) := by
  intro h
  obtain ⟨c, hc⟩ := h (Pi.single 1 1)
  have h1 := congrFun hc 1
  rw [toyE_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_same] at h1
  exact zero_ne_one h1

/-- In the toy model the view map is *not* surjective: C-DEC does not
require it to be. -/
theorem toyF_not_surjective : ¬ Function.Surjective (toyF K) := by
  intro h
  obtain ⟨c, hc⟩ := h (Pi.single 1 1)
  have h1 := congrFun hc 1
  rw [toyF_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_same] at h1
  exact zero_ne_one h1

/-- In the toy model even the *joint* map is not surjective, yet C-DEC holds
(`toy_cDec`).  So the hypothesis of this file is strictly weaker than the
full-rank slogan, exactly as the audit requires. -/
theorem toy_prod_not_surjective :
    ¬ Function.Surjective ((toyE K).prod (toyF K)) := by
  intro h
  refine toyF_not_surjective K fun z => ?_
  obtain ⟨c, hc⟩ := h ((0 : Fin 2 → K), z)
  exact ⟨c, congrArg Prod.snd hc⟩

end NotFullRank

/-! ## The audit's instantiation: mask space `ker ℓ`, batching power `γ^18`

The audit fixes `C = ker ℓ` inside the coefficient-word space `M`, states
C-DEC as `F_σ(Δ_σ) ≤ image (F_σ | C ∩ ker E_σ)` with `Δ_σ` a submodule of
the *word* space, and folds the mask into the combined word as
`W_γ(w, c) = X_γ(w) + γ^18 · c`, so the mask's contribution to every
post-combination coordinate is `γ^18 · F c`.  This section reproduces that
exact shape and derives the full-fold conditional-decoupling law from it. -/

section AuditInstantiation

variable {K M U Y : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup U] [Module K U]
  [AddCommGroup Y] [Module K Y]

/-- **The audit's (C-DEC) line, verbatim shape.**  With `E`, `F` defined on
the word space and the mask space cut out as `ker ℓ`, C-DEC is the
containment `F(Δ_w) ≤ image (F restricted to (ker ℓ ⊓ ker E))`, where `Δ_w`
is the legal witness-difference space in the *word* space (the span of the
differences `X_γ(w) − X_γ(w')` allowed by the accepted relation). -/
def CDecAudit (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (Δw : Submodule K M) : Prop :=
  Submodule.map F Δw
    ≤ Submodule.map F (LinearMap.ker ell ⊓ LinearMap.ker E)

/-- The word-space form `CDecAudit` is exactly `CDec` for the maps
restricted to the mask space `ker ℓ`, with the legal difference space
transported into the view space by `F`. -/
theorem cDecAudit_iff_cDec (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    (F : M →ₗ[K] Y) (Δw : Submodule K M) :
    CDecAudit ell E F Δw
      ↔ CDec (E.domRestrict (LinearMap.ker ell))
          (F.domRestrict (LinearMap.ker ell)) (Submodule.map F Δw) := by
  constructor
  · intro h δ hδ
    obtain ⟨m, hm, hFm⟩ := Submodule.mem_map.mp (h hδ)
    rw [Submodule.mem_inf] at hm
    exact ⟨⟨m, hm.1⟩, LinearMap.mem_ker.mp hm.2, hFm⟩
  · intro h δ hδ
    obtain ⟨c, hcE, hcF⟩ := h δ hδ
    exact Submodule.mem_map.mpr ⟨(c : M),
      Submodule.mem_inf.mpr ⟨c.2, LinearMap.mem_ker.mpr hcE⟩, hcF⟩

/-- **The audit's `J_σ` form at the word level.**  For `γ ≠ 0`, `CDecAudit`
is equivalent to: `(0, F δ) ∈ image J_σ` for every `δ ∈ Δ_w`, where
`J_σ(c) = (E_σ(c), F_σ(γ^18 · c))` on the mask space `ker ℓ`.  This is the
audit's displayed requirement, line for line. -/
theorem cDecAudit_iff_J (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    (Δw : Submodule K M) {γ : K} (hγ : γ ≠ 0) :
    CDecAudit ell E F Δw
      ↔ ∀ δ ∈ Δw, ((0 : U), F δ) ∈ LinearMap.range
          (Jmap (E.domRestrict (LinearMap.ker ell))
            (F.domRestrict (LinearMap.ker ell)) γ) := by
  rw [cDecAudit_iff_cDec,
    cDec_iff_J (E.domRestrict (LinearMap.ker ell))
      (F.domRestrict (LinearMap.ker ell)) (Submodule.map F Δw) hγ]
  constructor
  · intro h δ hδ
    exact h (F δ) (Submodule.mem_map_of_mem hδ)
  · intro h y hy
    obtain ⟨δ, hδ, rfl⟩ := Submodule.mem_map.mp hy
    exact h δ hδ

/-- **Translation between the two witnesses' conditioned mask fibres, in the
audit's full-fold arithmetic.**  Fix `γ ≠ 0` and assume `CDecAudit`.  For two
legal witness words `x₁`, `x₂` (the audit's `X_γ(w)`, `X_γ(w')`) with
`x₂ - x₁ ∈ Δ_w`, there is a mask `c₀ ∈ ker ℓ` that is invisible to the 76
conditioned coordinates (`E_σ c₀ = 0`) and whose batched view contribution
is exactly the legal difference (`γ^18 • F c₀ = F x₂ - F x₁`), such that for
every conditioning value `e`, translation by `c₀` is a bijection of the
conditioned mask fibre `{c : ker ℓ // E_σ c = e}` carrying witness 1's
complete post-combination view onto witness 2's:
`F (x₁ + γ^18 • (c + c₀)) = F (x₂ + γ^18 • c)`. -/
theorem componentC_translation_between_witness_fibres
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {γ : K} (hγ : γ ≠ 0) {Δw : Submodule K M}
    (hdec : CDecAudit ell E F Δw)
    {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : U) :
    ∃ (c₀ : LinearMap.ker ell)
      (hc₀ : E.domRestrict (LinearMap.ker ell) c₀ = 0),
      γ ^ 18 • F (c₀ : M) = F x₂ - F x₁ ∧
      ∀ c : {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e},
        F (x₁ + γ ^ 18 •
            ((translationEquiv (E.domRestrict (LinearMap.ker ell)) e c₀ hc₀ c :
              LinearMap.ker ell) : M))
          = F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M)) := by
  have h18 : γ ^ 18 ≠ 0 := pow_ne_zero _ hγ
  have hmem : F x₂ - F x₁ ∈ Submodule.map F Δw := by
    rw [← map_sub]
    exact Submodule.mem_map_of_mem hlegal
  obtain ⟨c₁, hc₁E, hc₁F⟩ := (cDecAudit_iff_cDec ell E F Δw).mp hdec _ hmem
  have hc₁F' : F (c₁ : M) = F x₂ - F x₁ := hc₁F
  refine ⟨(γ ^ 18)⁻¹ • c₁, ?_, ?_, ?_⟩
  · rw [map_smul, hc₁E, smul_zero]
  · rw [Submodule.coe_smul, map_smul, smul_inv_smul₀ h18, hc₁F']
  · intro c
    rw [translationEquiv_apply, Submodule.coe_add, Submodule.coe_smul,
      smul_add, smul_inv_smul₀ h18, map_add, map_add, map_add,
      map_smul, hc₁F']
    abel

/-- **The C-DEC full-fold conditional-decoupling theorem (audit headline,
exact `PMF` form).**  Fix a schedule with `γ ≠ 0` and assume the audit's
(C-DEC).  Sample the Component-C mask uniformly from the conditioned fibre
`{c : ker ℓ // E_σ c = e}` (the conditional law of the uniform mask given
the 76 released coordinates, by `uniform_conditioned_eq_uniform_fibre`).
Then for two legal witnesses `x₁`, `x₂` with `x₂ - x₁ ∈ Δ_w`, the complete
post-combination field view of the folded word,
`c ↦ F (xᵢ + γ^18 • c)`, has the *same* distribution for both witnesses:

    Law(F_σ(W_γ(w, C)) | E_σ(C) = e) = Law(F_σ(W_γ(w', C)) | E_σ(C) = e).

The nonemptiness instance is exactly "`e` is in the image of `E_σ`". -/
theorem componentC_full_fold_conditional_decoupling
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {γ : K} (hγ : γ ≠ 0) {Δw : Submodule K M}
    (hdec : CDecAudit ell E F Δw)
    {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : U)
    [Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}] :
    (PMF.uniformOfFintype {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e}).map
        (fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
          F (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))
      = (PMF.uniformOfFintype {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e}).map
          (fun c : {c : LinearMap.ker ell //
              E.domRestrict (LinearMap.ker ell) c = e} =>
            F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) := by
  obtain ⟨c₀, hc₀, _, hview⟩ :=
    componentC_translation_between_witness_fibres ell E F hγ hdec hlegal e
  exact uniform_map_eq_of_equiv_comp
    (translationEquiv (E.domRestrict (LinearMap.ker ell)) e c₀ hc₀)
    (f := fun c : {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e} =>
      F (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))
    (g := fun c : {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e} =>
      F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) hview

/-- **Complete-view form of the full-fold theorem.**  The released pair
`(E_σ c, F (xᵢ + γ^18 • c))` — the 76 conditioned coordinates together with
every post-combination coordinate of the folded word — has a
witness-independent law on the conditioned fibre.  The first component is
constantly `e` on the fibre; the second is the previous theorem. -/
theorem componentC_full_fold_conditional_decoupling_complete_view
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {γ : K} (hγ : γ ≠ 0) {Δw : Submodule K M}
    (hdec : CDecAudit ell E F Δw)
    {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : U)
    [Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}] :
    (PMF.uniformOfFintype {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e}).map
        (fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
          (E.domRestrict (LinearMap.ker ell) (c : LinearMap.ker ell),
            F (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M))))
      = (PMF.uniformOfFintype {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e}).map
          (fun c : {c : LinearMap.ker ell //
              E.domRestrict (LinearMap.ker ell) c = e} =>
            (E.domRestrict (LinearMap.ker ell) (c : LinearMap.ker ell),
              F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))) := by
  obtain ⟨c₀, hc₀, _, hview⟩ :=
    componentC_translation_between_witness_fibres ell E F hγ hdec hlegal e
  refine uniform_map_eq_of_equiv_comp
    (translationEquiv (E.domRestrict (LinearMap.ker ell)) e c₀ hc₀)
    (f := fun c : {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e} =>
      (E.domRestrict (LinearMap.ker ell) (c : LinearMap.ker ell),
        F (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M))))
    (g := fun c : {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e} =>
      (E.domRestrict (LinearMap.ker ell) (c : LinearMap.ker ell),
        F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))))
    (fun c => ?_)
  simp only [Prod.mk.injEq]
  exact ⟨by
    rw [(translationEquiv (E.domRestrict (LinearMap.ker ell)) e c₀ hc₀ c).2,
      c.2], hview c⟩

/-- **Literal conditional-law form of the full-fold theorem.**  The audit's
`Law(F_σ(W_γ(w, C_uniform)) | E_σ(C_uniform) = e)` with the conditioning
spelled as `PMF.filter`: condition the uniform distribution on the whole
mask space `ker ℓ` on the event `E_σ = e`, push forward through the folded
view `c ↦ F (x + γ^18 • c)`, and the result is the same `PMF` for any two
legal witnesses.  No modelling shortcut remains: the conditional is the
textbook normalised restriction. -/
theorem componentC_full_fold_conditional_law_filter
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U) (F : M →ₗ[K] Y)
    {γ : K} (hγ : γ ≠ 0) {Δw : Submodule K M}
    (hdec : CDecAudit ell E F Δw)
    {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : U)
    [Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}]
    (h : ∃ c ∈ {c : LinearMap.ker ell |
        E.domRestrict (LinearMap.ker ell) c = e},
      c ∈ (PMF.uniformOfFintype (LinearMap.ker ell)).support) :
    ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell |
          E.domRestrict (LinearMap.ker ell) c = e} h).map
        (fun c : LinearMap.ker ell => F (x₁ + γ ^ 18 • (c : M)))
      = ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
          {c : LinearMap.ker ell |
            E.domRestrict (LinearMap.ker ell) c = e} h).map
          (fun c : LinearMap.ker ell => F (x₂ + γ ^ 18 • (c : M))) := by
  have hdec' : CDec (E.domRestrict (LinearMap.ker ell))
      (γ ^ 18 • F.domRestrict (LinearMap.ker ell)) (Submodule.map F Δw) :=
    cDec_smul (pow_ne_zero _ hγ) ((cDecAudit_iff_cDec ell E F Δw).mp hdec)
  have hy : F x₂ - F x₁ ∈ Submodule.map F Δw := by
    rw [← map_sub]
    exact Submodule.mem_map_of_mem hlegal
  have hfun : ∀ x : M, (fun c : LinearMap.ker ell => F (x + γ ^ 18 • (c : M)))
      = fun c : LinearMap.ker ell =>
        F x + (γ ^ 18 • F.domRestrict (LinearMap.ker ell)) c := by
    intro x
    funext c
    rw [map_add, map_smul, LinearMap.smul_apply, LinearMap.domRestrict_apply]
  rw [hfun x₁, hfun x₂]
  exact cDec_conditional_law_witness_indep hdec' hy e h

end AuditInstantiation

/-! ## Finite-field instantiation

The hypotheses of the `PMF` theorems are satisfiable over any finite field
on concrete coordinate spaces (in the audit, `K = QM31`, mask space
`K^1023`, 76 conditioned coordinates, at most 256 post-combination
coordinates).  This wrapper witnesses that the instances resolve. -/

section FiniteField

/-- `cDec_view_pmf_indep` specialised to coordinate spaces over a finite
field: all finiteness/decidability instances resolve automatically, so the
abstract hypotheses are satisfiable in the audit's intended shape. -/
theorem cDec_view_pmf_indep_coordinates
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n u y : ℕ}
    {E : (Fin n → K) →ₗ[K] (Fin u → K)} {F : (Fin n → K) →ₗ[K] (Fin y → K)}
    {Δ : Submodule K (Fin y → K)} (hdec : CDec E F Δ)
    {y₁ y₂ : Fin y → K} (hy : y₂ - y₁ ∈ Δ) (e : Fin u → K)
    [Nonempty {c : Fin n → K // E c = e}] :
    (PMF.uniformOfFintype {c : Fin n → K // E c = e}).map
        (fun c : {c : Fin n → K // E c = e} => y₁ + F (c : Fin n → K))
      = (PMF.uniformOfFintype {c : Fin n → K // E c = e}).map
          (fun c : {c : Fin n → K // E c = e} => y₂ + F (c : Fin n → K)) :=
  cDec_view_pmf_indep hdec hy e

end FiniteField

/-! ## Dimension inventory: kernel arithmetic, bookkeeping ONLY

The following are the audit's coordinate counts, checked by the kernel.
They are **counts, not the decoupling theorem**: none of them is evidence
for `(C-DEC)`, and the audit states explicitly that dimension comparison
(`1023 > 332`) does not prove it. -/

namespace DimensionInventory

/-- Bookkeeping only (NOT C-DEC): the conditioned Component-C coordinates
are 72 authenticated layer-zero values plus 4 claims (three MLE claims and
the structured terminal claim): `72 + 4 = 76`. -/
theorem conditioned_coordinate_count : 72 + 4 = 76 := by decide

/-- Bookkeeping only (NOT C-DEC): the audit's grammar for the
post-combination dimension, `dim Y_σ = 4·9 + 4·(n₁+n₂+n₃) + 4
= 40 + 4·(n₁+n₂+n₃)` (four rounds × (2 OOD + 7 relation-sumcheck), later
opening layers, four final coefficients). -/
theorem post_combination_dimension_formula (n₁ n₂ n₃ : ℕ) :
    4 * 9 + 4 * (n₁ + n₂ + n₃) + 4 = 40 + 4 * (n₁ + n₂ + n₃) := by omega

/-- Bookkeeping only (NOT C-DEC): the derived-count bounds
`8 ≤ n₁+n₂+n₃ ≤ 54` give `72 ≤ dim Y_σ ≤ 256`. -/
theorem post_combination_dimension_bounds (n₁ n₂ n₃ : ℕ)
    (h₈ : 8 ≤ n₁ + n₂ + n₃) (h₅₄ : n₁ + n₂ + n₃ ≤ 54) :
    72 ≤ 40 + 4 * (n₁ + n₂ + n₃) ∧ 40 + 4 * (n₁ + n₂ + n₃) ≤ 256 := by
  omega

/-- Bookkeeping only (NOT C-DEC): the frozen q18 fixture has no parent
collisions, so `n₁ = n₂ = n₃ = 18` and `dim Y_σ = 256`. -/
theorem frozen_q18_dimension : 40 + 4 * (18 + 18 + 18) = 256 := by norm_num

/-- Bookkeeping only (NOT C-DEC): the worst-case joint linear inventory
relevant to C is `76 + 256 = 332` QM31 coordinates. -/
theorem worst_case_joint_inventory : 76 + 256 = 332 := by decide

end DimensionInventory

/-! ## Unresolved interfaces: named, explicit, NOT proved

Everything above is linear algebra and finite probability about *abstract*
maps.  Connecting it to the deployed system requires the following facts,
each stated as a named `Prop` and **left unproved**.  None of them is (or
may be) discharged by definition; a future proof must supply each one
against the real Rust artefacts or a precisely cited external theorem.
Until all six hold, the honest status of Component C remains the audit's:
"full-fold conditional decoupling remains open" for the deployed wire. -/

namespace UnresolvedInterfaces

/-- **UNRESOLVED INTERFACE (not proved): concrete 332-row Rust↔Lean map
correspondence.**  The 332 worst-case joint rows evaluated by the Rust side
(76 conditioned coordinates followed by 256 post-combination coordinates,
in serialisation order) must agree, row by row, with the Lean maps `E` and
`F` used in the theorems above.  `rustRow i` abstracts the Rust evaluation
of joint row `i` on a mask. -/
def RustLeanRowCorrespondence332 {K C : Type*} [Field K] [AddCommGroup C]
    [Module K C] (rustRow : Fin 332 → C →ₗ[K] K)
    (E : C →ₗ[K] Fin 76 → K) (F : C →ₗ[K] Fin 256 → K) : Prop :=
  ∀ c : C, (fun i : Fin 332 => rustRow i c)
    = Fin.append (fun i : Fin 76 => E c i) (fun j : Fin 256 => F c j) ∘
        Fin.cast (by norm_num : (332 : ℕ) = 76 + 256)

/-- **UNRESOLVED INTERFACE (not proved): Component-C sampler uniformity on
`ker ℓ`.**  The deployed sampler (`V5ComponentCLane::encode_free_coordinates`
applied to uniform free coordinates) must induce exactly the uniform
distribution on the mask hyperplane `ker ℓ`.  `sampler` abstracts the law
actually produced by the Rust sampler. -/
def SamplerUniformOnKerEll {K M : Type*} [Field K] [DecidableEq K]
    [AddCommGroup M] [Module K M] [Fintype M] (ell : M →ₗ[K] K)
    (sampler : PMF (LinearMap.ker ell)) : Prop :=
  sampler = PMF.uniformOfFintype (LinearMap.ker ell)

/-- **UNRESOLVED INTERFACE (not proved): the C commitment is bound before
`γ`, and `γ ≠ 0`.**  `commitPrefix t` is the transcript prefix up to and
including the binding Component-C commitment; `gammaOf t` is the batching
challenge.  The interface demands that `γ` is a function of that prefix
(commitment strictly precedes the challenge — the audit's causal condition,
which no frozen matrix rank can replace) and is never zero. -/
def CommitmentBeforeGammaAndGammaNeZero {K T P : Type*} [Zero K]
    (commitPrefix : T → P) (gammaOf : T → K) : Prop :=
  (∀ t : T, gammaOf t ≠ 0) ∧
    ∀ t₁ t₂ : T, commitPrefix t₁ = commitPrefix t₂ → gammaOf t₁ = gammaOf t₂

/-- **UNRESOLVED INTERFACE (not proved): authentication of all 76 claims.**
The 76 released values the theorems condition on (`e`) must be exactly the
`E`-image of the committed mask — i.e. every layer-zero opening and all four
non-point claims are authenticated against the Component-C commitment, with
no unauthenticated substitute accepted by the verifier. -/
def AllSeventySixClaimsAuthenticated {K C : Type*} [Field K]
    [AddCommGroup C] [Module K C] (E : C →ₗ[K] Fin 76 → K)
    (committedMask : C) (releasedClaims : Fin 76 → K) : Prop :=
  releasedClaims = E committedMask

/-- **UNRESOLVED INTERFACE (not proved): exact serialization completeness.**
The v5 serialisation must enumerate every post-combination `F`-coordinate
exactly once — no omission and no duplication.  Formally: the serialised
row family is a permutation of the coordinate functionals of `F`. -/
def SerializationEnumeratesFExactlyOnce {K C : Type*} [Field K]
    [AddCommGroup C] [Module K C] {n : ℕ}
    (serializedRow : Fin n → C →ₗ[K] K) (F : C →ₗ[K] Fin n → K) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ (j : Fin n) (c : C),
    serializedRow j c = F c (σ j)

/-- **UNRESOLVED INTERFACE (not proved): circle / arity-4 FRI transport.**
The concrete Aspis fold pipeline — circle code, arity-four folds, the three
later opening layers and final coefficients — must act on the mask as the
linear map `F` used above.  This is the circle, arity-4 analogue of the
decoupling step of Haböck–Al Kindi, ePrint 2024/1037 (Protocol 2, Lemma 2,
Theorems 4 and 6, stated there for binary univariate Reed–Solomon FRI over
a subgroup/coset); either this interface is proved for the Aspis grammar or
that external theorem is transported through an explicit kernel-checked
circle-code/GRS isomorphism. -/
def CircleArityFourFoldTransport {K C Y : Type*} [Field K]
    [AddCommGroup C] [Module K C] [AddCommGroup Y] [Module K Y]
    (concreteFoldView : C → Y) (F : C →ₗ[K] Y) : Prop :=
  ∀ c : C, concreteFoldView c = F c

end UnresolvedInterfaces

/-! ## Axiom audit -/

#print axioms cDec_iff_zero_pair_mem_range
#print axioms cDec_iff_le_map_ker
#print axioms Jmap_apply
#print axioms cDec_iff_J
#print axioms cDec_smul
#print axioms cDec_of_prod_surjective
#print axioms translationEquiv
#print axioms translationEquiv_apply
#print axioms cDec_translation_fibre
#print axioms fibreEquivKer
#print axioms uniform_map_eq_of_equiv_comp
#print axioms cDec_view_pmf_indep
#print axioms cDec_complete_view_pmf_indep
#print axioms fibre_conditioning_witness
#print axioms uniform_conditioned_eq_uniform_fibre
#print axioms cDec_conditional_law_witness_indep
#print axioms toy_cDec
#print axioms toyE_not_surjective
#print axioms toyF_not_surjective
#print axioms toy_prod_not_surjective
#print axioms cDecAudit_iff_cDec
#print axioms cDecAudit_iff_J
#print axioms componentC_translation_between_witness_fibres
#print axioms componentC_full_fold_conditional_decoupling
#print axioms componentC_full_fold_conditional_decoupling_complete_view
#print axioms componentC_full_fold_conditional_law_filter
#print axioms cDec_view_pmf_indep_coordinates
#print axioms DimensionInventory.conditioned_coordinate_count
#print axioms DimensionInventory.post_combination_dimension_formula
#print axioms DimensionInventory.post_combination_dimension_bounds
#print axioms DimensionInventory.frozen_q18_dimension
#print axioms DimensionInventory.worst_case_joint_inventory

end AspisV5ComponentCConditionalDecoupling
