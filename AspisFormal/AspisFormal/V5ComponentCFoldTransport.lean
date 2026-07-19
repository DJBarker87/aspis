import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# v5 Component C: the circle / arity-4 fold-transport theorem (conditional)

This file closes the Component-C hiding argument **modulo one explicitly named,
unproved transport hypothesis** — the circle/arity-four analogue of the
decoupling step of Haböck–Al Kindi, ePrint 2024/1037.  It does *not* assert
that the cited paper (whose Protocol 2 / Lemma 2 / Theorems 4, 6 are stated for
**binary univariate Reed–Solomon FRI over a subgroup/coset**) already covers
the Aspis circle code with arity-four folds.  The gap identified in
`results/spend/v5_component_c_design_audit.md` §"What must be adapted", item 1
("Circle transport") is kept as a load-bearing hypothesis `CircleArity4Transport`
until a literature audit or a direct Lean proof discharges it.

## What is modelled

Over a field `K` we model, exactly in the audit's shape:

* the **coefficient encoder** `enc : M →ₗ[K] A` of the deployed circle-code lane
  (`V5ComponentCLane`), taking a coefficient word to its circle codeword;
* the **arity-4 fold sequence** as four maps `cf 0, cf 1, cf 2, cf 3 : A → A`
  (the four fold rounds of Profile24), *a priori arbitrary functions* — nothing
  here assumes they are linear;
* the **binary/GRS ↔ circle transport** as a `K`-linear isomorphism
  `Φ : A ≃ₗ[K] B` together with four **linear** GRS-side fold operators
  `gf 0..gf 3 : B →ₗ[K] B` (the operators the published lemma actually covers);
* the **OOD / fold released view** as per-round linear read-offs
  `ρ 0..ρ 4 : A →ₗ[K] V` — at each of the five layer words the verifier reads its
  OOD values, its relation-sumcheck values, and its folded/opened values — with
  the complete released view being the whole five-layer vector
  `circleFoldView : M → (Fin 5 → V)`, not a probe of layer zero or OOD alone.

## The named transport hypothesis

`CircleArity4Transport Φ gf cf` is the **commuting-diagram** property

    Φ (cf i a) = gf i (Φ a)      for every fold `i : Fin 4` and every `a : A`,

i.e. each of the four circle folds is intertwined by the transport `Φ` with a
linear GRS fold.  This is exactly the audit's requirement to "show that the
coefficient encoder and four arity-four folds give the same linear-oracle
experiment used in `F_σ`, or transport it through an explicit circle-code/GRS
isomorphism".  It is stated as a `Prop` and **never discharged by definition**.

## What is proved (conditional on that hypothesis)

`circleFoldView_eq_model`: under `CircleArity4Transport`, the concrete circle
released view equals a genuine `K`-linear map `foldLinearModel` (the audit's
`F_σ`).  This is the whole content of "circle transport": the four
possibly-nonlinear circle folds, conjugate to linear GRS folds, compose to a
*linear* released-view evaluator.

Feeding that linearity into the C-DEC machinery of
`AspisFormal.V5ComponentCConditionalDecoupling` gives the headline results:

* `circleArity4_conditioned_view_indep` — `CircleArity4Transport` **plus**
  C-DEC (`CDec E foldLinearModel Δ`) imply the conditioned circle-fold released
  view is a witness-independent `PMF` (a witness-free simulator: any two legal
  witnesses induce the *same* released law), by translation of the conditioned
  mask fibre;
* `circleArity4_full_fold_conditional_decoupling` — the same, in the audit's
  full `ker ℓ` / `γ^18`-batched shape, upgrading
  `componentC_full_fold_conditional_decoupling` from an abstract linear `F` to
  the deployed four-arity-four-fold circle view.

## Load-bearing, not decorative

The hypothesis is proved necessary, not ornamental.  The negative section
exhibits a concrete circle "fold" (a squaring at round 0 over `ZMod 3`) for
which **no** transport isomorphism and GRS folds can satisfy
`CircleArity4Transport` (`negative_model_no_transport`), and for which the two
legal witnesses' released fold-view laws are genuinely **different** `PMF`s
(`negative_model_laws_differ`).  Drop the transport hypothesis and the
conclusion fails.

## What is NOT proved

`CircleArity4Transport` itself.  Nothing here identifies the abstract `cf`, `Φ`,
`gf`, `ρ` with the deployed Rust circle folds, proves that the published binary
Reed–Solomon lemma transports to the circle code, or establishes any of the
other Component-C deployment interfaces (sampler uniformity, Fiat–Shamir
ordering, claim authentication, serialization completeness) recorded as unproved
`Prop`s in the imported file.  The honest status remains the audit's: **HVZK
for Component C modulo exactly the cited circle/arity-4 transport assumption**,
not unconditional zero-knowledge.
-/

open scoped ENNReal
open AspisV5ComponentCConditionalDecoupling

namespace AspisV5ComponentCFoldTransport

/-! ## The arity-4 fold tower, its released view, and the transport interface -/

section Model

variable {K : Type*} [Field K]
  {M A B V : Type*}
  [AddCommGroup M] [Module K M]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup V] [Module K V]

/-- **The five circle-code layer words.**  Layer `0` is the encoded coefficient
word `enc m`; layer `i+1` is the `i`-th arity-four circle fold applied to layer
`i`.  The four folds `cf 0, cf 1, cf 2, cf 3` are arbitrary functions `A → A`;
linearity is *not* assumed here — it is exactly what the transport hypothesis
buys back below. -/
def circleWords (enc : M →ₗ[K] A) (cf : Fin 4 → A → A) (m : M) : Fin 5 → A :=
  ![ enc m,
     cf 0 (enc m),
     cf 1 (cf 0 (enc m)),
     cf 2 (cf 1 (cf 0 (enc m))),
     cf 3 (cf 2 (cf 1 (cf 0 (enc m)))) ]

/-- **The complete concrete released fold view.**  At each of the five layers,
the verifier's per-round read-off `ρ i` (its OOD values, relation-sumcheck
values, and folded/opened values, packaged as a linear functional vector into
`V`) is applied to the `i`-th circle layer word.  The released view is the whole
five-layer vector — the audit's "complete fold view", not a single layer. -/
def circleFoldView (enc : M →ₗ[K] A) (cf : Fin 4 → A → A)
    (ρ : Fin 5 → A →ₗ[K] V) (m : M) : Fin 5 → V :=
  fun i => ρ i (circleWords enc cf m i)

/-- The GRS-side image of the mask's circle codeword under the transport
isomorphism `Φ` (the binary/Reed–Solomon model the published lemma covers). -/
def grsEnc (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B) : M →ₗ[K] B :=
  Φ.toLinearMap ∘ₗ enc

/-- **The five GRS-side layer maps**, each a genuine `K`-linear map `M →ₗ[K] B`:
the encoded word and its four *linear* GRS folds `gf 0..gf 3`.  These are the
operators for which the Haböck–Al Kindi decoupling is stated. -/
def grsLayers (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B) (gf : Fin 4 → B →ₗ[K] B) :
    Fin 5 → (M →ₗ[K] B) :=
  ![ grsEnc enc Φ,
     gf 0 ∘ₗ grsEnc enc Φ,
     gf 1 ∘ₗ gf 0 ∘ₗ grsEnc enc Φ,
     gf 2 ∘ₗ gf 1 ∘ₗ gf 0 ∘ₗ grsEnc enc Φ,
     gf 3 ∘ₗ gf 2 ∘ₗ gf 1 ∘ₗ gf 0 ∘ₗ grsEnc enc Φ ]

/-- **The transported linear released-view model `F_σ`.**  Read off layer `i`
with `ρ i`, transported back to the circle side by `Φ⁻¹`, of the `i`-th GRS
layer map.  This is an honest `K`-linear map `M →ₗ[K] (Fin 5 → V)`: it is the
linear-oracle experiment the audit asks the circle folds to reproduce. -/
def foldLinearModel (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B) (gf : Fin 4 → B →ₗ[K] B)
    (ρ : Fin 5 → A →ₗ[K] V) : M →ₗ[K] (Fin 5 → V) :=
  LinearMap.pi (fun i => (ρ i ∘ₗ Φ.symm.toLinearMap) ∘ₗ grsLayers enc Φ gf i)

/-- **The `CircleArity4Transport` interface (named, unproved hypothesis).**

The commuting-diagram / conjugacy property of the four arity-four circle folds:
for each fold `i : Fin 4`, the concrete circle fold `cf i` is intertwined by the
circle↔GRS transport isomorphism `Φ` with the linear GRS fold `gf i`:

    Φ (cf i a) = gf i (Φ a)   for all `a : A`.

Equivalently the four squares

    A --cf i-->  A          commute.
    |            |
    Φ            Φ
    v            v
    B --gf i-->  B

This is precisely the "circle transport" gate of the design audit: it asserts
that the deployed circle folds are the transport, through an explicit
circle-code/GRS isomorphism, of the linear GRS folds covered by the published
binary Reed–Solomon lemma.  It is **not** discharged anywhere in this file. -/
def CircleArity4Transport (Φ : A ≃ₗ[K] B) (gf : Fin 4 → B →ₗ[K] B)
    (cf : Fin 4 → A → A) : Prop :=
  ∀ (i : Fin 4) (a : A), Φ (cf i a) = gf i (Φ a)

/-- Each concrete circle layer word is the `Φ⁻¹`-transport of the corresponding
linear GRS layer, *provided* the four folds satisfy the transport diagram.  The
transport hypothesis is consumed exactly four times — once per fold. -/
theorem circleWords_eq_transported (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B)
    (gf : Fin 4 → B →ₗ[K] B) (cf : Fin 4 → A → A)
    (htr : CircleArity4Transport Φ gf cf) (m : M) (i : Fin 5) :
    circleWords enc cf m i = Φ.symm (grsLayers enc Φ gf i m) := by
  fin_cases i
  · -- layer 0: enc m = Φ⁻¹ (Φ (enc m))
    change enc m = Φ.symm (grsEnc enc Φ m)
    rw [grsEnc, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Φ.symm_apply_apply]
  · -- layer 1: uses the diagram at fold 0
    change cf 0 (enc m) = Φ.symm ((gf 0 ∘ₗ grsEnc enc Φ) m)
    rw [LinearMap.comp_apply, grsEnc, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, ← htr 0 (enc m), Φ.symm_apply_apply]
  · -- layer 2: folds 0,1
    change cf 1 (cf 0 (enc m)) = Φ.symm ((gf 1 ∘ₗ gf 0 ∘ₗ grsEnc enc Φ) m)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, grsEnc, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, ← htr 0 (enc m),
      ← htr 1 (cf 0 (enc m)), Φ.symm_apply_apply]
  · -- layer 3: folds 0,1,2
    change cf 2 (cf 1 (cf 0 (enc m)))
        = Φ.symm ((gf 2 ∘ₗ gf 1 ∘ₗ gf 0 ∘ₗ grsEnc enc Φ) m)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      grsEnc, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ← htr 0 (enc m), ← htr 1 (cf 0 (enc m)),
      ← htr 2 (cf 1 (cf 0 (enc m))), Φ.symm_apply_apply]
  · -- layer 4: all four folds
    change cf 3 (cf 2 (cf 1 (cf 0 (enc m))))
        = Φ.symm ((gf 3 ∘ₗ gf 2 ∘ₗ gf 1 ∘ₗ gf 0 ∘ₗ grsEnc enc Φ) m)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, grsEnc, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, ← htr 0 (enc m), ← htr 1 (cf 0 (enc m)),
      ← htr 2 (cf 1 (cf 0 (enc m))), ← htr 3 (cf 2 (cf 1 (cf 0 (enc m)))),
      Φ.symm_apply_apply]

/-- **Circle transport, exactly.**  Under `CircleArity4Transport`, the concrete
circle released view equals the linear model `foldLinearModel` (the audit's
`F_σ`) on every coefficient word.  The four possibly-nonlinear circle folds,
being conjugate to linear GRS folds, compose to a *linear* released-view
evaluator.  This is the single fact the rest of the file consumes. -/
theorem circleFoldView_eq_model (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B)
    (gf : Fin 4 → B →ₗ[K] B) (cf : Fin 4 → A → A) (ρ : Fin 5 → A →ₗ[K] V)
    (htr : CircleArity4Transport Φ gf cf) (m : M) :
    circleFoldView enc cf ρ m = foldLinearModel enc Φ gf ρ m := by
  funext i
  rw [circleFoldView, foldLinearModel, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    circleWords_eq_transported enc Φ gf cf htr m i]

/-- The structured `CircleArity4Transport` interface **refines** the coarse,
unstructured circle-transport interface `CircleArityFourFoldTransport` recorded
in the imported audit file: the commuting diagram of the four folds implies the
concrete fold view coincides with the linear model on every input.  So proving
the structured diagram would discharge the imported placeholder — but neither is
proved here. -/
theorem structured_refines_placeholder (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B)
    (gf : Fin 4 → B →ₗ[K] B) (cf : Fin 4 → A → A) (ρ : Fin 5 → A →ₗ[K] V)
    (htr : CircleArity4Transport Φ gf cf) :
    UnresolvedInterfaces.CircleArityFourFoldTransport
      (circleFoldView enc cf ρ) (foldLinearModel enc Φ gf ρ) :=
  fun m => circleFoldView_eq_model enc Φ gf cf ρ htr m

end Model

/-! ## Headline theorems: transport + C-DEC ⟹ witness-free released fold view -/

section Decoupling

variable {K : Type*} [Field K]
  {M A B V U : Type*}
  [AddCommGroup M] [Module K M]
  [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]
  [AddCommGroup V] [Module K V]
  [AddCommGroup U] [Module K U]

/-- **The circle/arity-4 conditioned fold-view decoupling theorem (conditional
on transport).**

Assume:

* `CircleArity4Transport Φ gf cf` — the four circle folds transport through `Φ`
  to the linear GRS folds (the named, unproved circle-transport hypothesis);
* `CDec E (foldLinearModel enc Φ gf ρ) Δ` — the C-DEC containment
  `Δ ≤ image (F_σ | ker E)` for the transported linear released-view model.

Then for any two legal witness contributions `y₁, y₂` whose difference is legal
(`y₂ - y₁ ∈ Δ`), and any conditioning value `e` in the image of `E`, the
**concrete circle-fold released view** `c ↦ yᵢ + circleFoldView … c`, with the
mask `c` uniform on the conditioned fibre `{c // E c = e}`, has the *same* `PMF`
for both witnesses.  The released law is therefore a function of `e` alone: a
witness-free simulator for the released C fold view.

Both hypotheses are load-bearing: transport linearises the concrete fold
(`circleFoldView_eq_model`), and C-DEC supplies the mask that absorbs the legal
witness difference (`cDec_view_pmf_indep`). -/
theorem circleArity4_conditioned_view_indep [Fintype M] [DecidableEq U]
    (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B) (gf : Fin 4 → B →ₗ[K] B)
    (cf : Fin 4 → A → A) (ρ : Fin 5 → A →ₗ[K] V)
    {E : M →ₗ[K] U} {Δ : Submodule K (Fin 5 → V)}
    (htr : CircleArity4Transport Φ gf cf)
    (hdec : CDec E (foldLinearModel enc Φ gf ρ) Δ)
    {y₁ y₂ : Fin 5 → V} (hy : y₂ - y₁ ∈ Δ) (e : U)
    [Nonempty {c : M // E c = e}] :
    (PMF.uniformOfFintype {c : M // E c = e}).map
        (fun c : {c : M // E c = e} => y₁ + circleFoldView enc cf ρ (c : M))
      = (PMF.uniformOfFintype {c : M // E c = e}).map
          (fun c : {c : M // E c = e} => y₂ + circleFoldView enc cf ρ (c : M)) := by
  have hEq : ∀ m : M, circleFoldView enc cf ρ m = foldLinearModel enc Φ gf ρ m :=
    fun m => circleFoldView_eq_model enc Φ gf cf ρ htr m
  have h₁ : (fun c : {c : M // E c = e} => y₁ + circleFoldView enc cf ρ (c : M))
      = (fun c : {c : M // E c = e} =>
          y₁ + foldLinearModel enc Φ gf ρ (c : M)) := by
    funext c; rw [hEq]
  have h₂ : (fun c : {c : M // E c = e} => y₂ + circleFoldView enc cf ρ (c : M))
      = (fun c : {c : M // E c = e} =>
          y₂ + foldLinearModel enc Φ gf ρ (c : M)) := by
    funext c; rw [hEq]
  rw [h₁, h₂]
  exact cDec_view_pmf_indep hdec hy e

/-- **Complete-view form.**  The released pair `(E c, yᵢ + circleFoldView … c)` —
the conditioned coordinates together with the entire concrete circle-fold view —
has a witness-independent law on the conditioned fibre.  Same two hypotheses. -/
theorem circleArity4_conditioned_complete_view_indep [Fintype M] [DecidableEq U]
    (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B) (gf : Fin 4 → B →ₗ[K] B)
    (cf : Fin 4 → A → A) (ρ : Fin 5 → A →ₗ[K] V)
    {E : M →ₗ[K] U} {Δ : Submodule K (Fin 5 → V)}
    (htr : CircleArity4Transport Φ gf cf)
    (hdec : CDec E (foldLinearModel enc Φ gf ρ) Δ)
    {y₁ y₂ : Fin 5 → V} (hy : y₂ - y₁ ∈ Δ) (e : U)
    [Nonempty {c : M // E c = e}] :
    (PMF.uniformOfFintype {c : M // E c = e}).map
        (fun c : {c : M // E c = e} =>
          (E (c : M), y₁ + circleFoldView enc cf ρ (c : M)))
      = (PMF.uniformOfFintype {c : M // E c = e}).map
          (fun c : {c : M // E c = e} =>
            (E (c : M), y₂ + circleFoldView enc cf ρ (c : M))) := by
  have hEq : ∀ m : M, circleFoldView enc cf ρ m = foldLinearModel enc Φ gf ρ m :=
    fun m => circleFoldView_eq_model enc Φ gf cf ρ htr m
  have h₁ : (fun c : {c : M // E c = e} =>
        (E (c : M), y₁ + circleFoldView enc cf ρ (c : M)))
      = (fun c : {c : M // E c = e} =>
          (E (c : M), y₁ + foldLinearModel enc Φ gf ρ (c : M))) := by
    funext c; rw [hEq]
  have h₂ : (fun c : {c : M // E c = e} =>
        (E (c : M), y₂ + circleFoldView enc cf ρ (c : M)))
      = (fun c : {c : M // E c = e} =>
          (E (c : M), y₂ + foldLinearModel enc Φ gf ρ (c : M))) := by
    funext c; rw [hEq]
  rw [h₁, h₂]
  exact cDec_complete_view_pmf_indep hdec hy e

/-- **The audit's full-fold headline, for the deployed circle view (conditional
on transport).**  In the audit's exact `ker ℓ` / `γ^18`-batched shape: sample the
Component-C mask uniformly from the conditioned fibre `{c : ker ℓ // E c = e}`,
fold the batched word `xᵢ + γ^18 · c` through the *concrete four-arity-four-fold
circle pipeline*, and read the complete released view.  Under
`CircleArity4Transport` and the audit's `CDecAudit`, the resulting law is the
same for any two legal witnesses `x₁, x₂` with `x₂ - x₁ ∈ Δ_w`:

    Law(circleFoldView(x + γ^18·C) | E(C) = e)  is independent of the witness.

This upgrades `componentC_full_fold_conditional_decoupling` from an abstract
linear `F` to the deployed circle folds — conditional on the still-open circle
transport. -/
theorem circleArity4_full_fold_conditional_decoupling
    [DecidableEq K] [Fintype M] [DecidableEq U]
    (enc : M →ₗ[K] A) (Φ : A ≃ₗ[K] B) (gf : Fin 4 → B →ₗ[K] B)
    (cf : Fin 4 → A → A) (ρ : Fin 5 → A →ₗ[K] V)
    (ell : M →ₗ[K] K) (E : M →ₗ[K] U)
    {γ : K} (hγ : γ ≠ 0) {Δw : Submodule K M}
    (htr : CircleArity4Transport Φ gf cf)
    (hdec : CDecAudit ell E (foldLinearModel enc Φ gf ρ) Δw)
    {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : U)
    [Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}] :
    (PMF.uniformOfFintype {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e}).map
        (fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
          circleFoldView enc cf ρ (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))
      = (PMF.uniformOfFintype {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e}).map
          (fun c : {c : LinearMap.ker ell //
              E.domRestrict (LinearMap.ker ell) c = e} =>
            circleFoldView enc cf ρ
              (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) := by
  have hEq : ∀ m : M, circleFoldView enc cf ρ m = foldLinearModel enc Φ gf ρ m :=
    fun m => circleFoldView_eq_model enc Φ gf cf ρ htr m
  have h₁ : (fun c : {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e} =>
          circleFoldView enc cf ρ (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))
      = (fun c : {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e} =>
            foldLinearModel enc Φ gf ρ
              (x₁ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) := by
    funext c; rw [hEq]
  have h₂ : (fun c : {c : LinearMap.ker ell //
        E.domRestrict (LinearMap.ker ell) c = e} =>
          circleFoldView enc cf ρ (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M)))
      = (fun c : {c : LinearMap.ker ell //
          E.domRestrict (LinearMap.ker ell) c = e} =>
            foldLinearModel enc Φ gf ρ
              (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) := by
    funext c; rw [hEq]
  rw [h₁, h₂]
  exact componentC_full_fold_conditional_decoupling ell E
    (foldLinearModel enc Φ gf ρ) hγ hdec hlegal e

end Decoupling

/-! ## Non-vacuous positive model

A concrete finite-field instance in which `CircleArity4Transport` **and** C-DEC
both hold and the conclusion follows.  The transport is realised at `Φ = id`
with the circle folds equal to genuine linear arity-four folds
`v ↦ Pi.single 0 (∑_{r<4} βᵣ v r)`; the read-off reads slot 0.  C-DEC holds with
`E = 0` and `Δ = range F` (the `toy_cDec` shape), which is *weaker* than any
surjectivity assumption.  The model is non-degenerate: the released view genuinely
reads the encoded word (`positive_model_nondegenerate`). -/

namespace PositiveModel

/-- `ZMod 5` is a field once its primality is supplied (unlike `ZMod 2, 3`,
there is no global `Fact (Nat.Prime 5)` instance in scope). -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The working field of the positive model. -/
abbrev K : Type := ZMod 5

/-- Layer word space: one arity-four fiber, four `K`-symbols. -/
abbrev A : Type := Fin 4 → K

/-- A genuine linear **arity-four fold** with challenge `β`: fold the four fiber
symbols by `∑_{r<4} βʳ · v r`, deposited in slot `0`. -/
def arity4Fold (β : K) : A →ₗ[K] A :=
  (LinearMap.single K (fun _ : Fin 4 => K) 0) ∘ₗ
    (∑ r : Fin 4, β ^ (r : ℕ) • LinearMap.proj r)

/-- The four fold challenges of the fixed schedule (any four scalars). -/
def β : Fin 4 → K := ![2, 3, 4, 1]

/-- The four **linear** GRS folds: here the arity-four folds themselves. -/
def gf : Fin 4 → A →ₗ[K] A := fun i => arity4Fold (β i)

/-- The four concrete **circle** folds: the underlying functions of `gf`, so the
transport diagram commutes definitionally at `Φ = id`. -/
def cf : Fin 4 → A → A := fun i => ⇑(gf i)

/-- The circle-code encoder: the identity (`A = M`). -/
def enc : A →ₗ[K] A := LinearMap.id

/-- The transport isomorphism: the identity circle↔GRS map. -/
def Φ : A ≃ₗ[K] A := LinearEquiv.refl K A

/-- Each of the five per-round read-offs: read slot `0`. -/
def ρ : Fin 5 → A →ₗ[K] K := fun _ => LinearMap.proj 0

/-- The released-view model of this instance, as a genuine linear map. -/
def F : A →ₗ[K] (Fin 5 → K) := foldLinearModel enc Φ gf ρ

/-- **Transport holds in the positive model** (definitionally: `cf i = ⇑(gf i)`
and `Φ = id`). -/
theorem transport_holds : CircleArity4Transport Φ gf cf := fun _ _ => rfl

/-- **C-DEC holds in the positive model**, with `E = 0` and `Δ = range F`.  This
is the audit's containment `Δ ≤ image (F | ker E)`, satisfied because every
`δ ∈ range F` is `F c` for an `E`-invisible `c` (all `c` are, since `E = 0`). -/
theorem cdec_holds :
    CDec (0 : A →ₗ[K] (Fin 1 → K)) F (LinearMap.range F) := by
  intro δ hδ
  obtain ⟨c, rfl⟩ := hδ
  exact ⟨c, rfl, rfl⟩

/-- Nonemptiness of the conditioning fibre at `e = 0`. -/
instance : Nonempty {c : A // (0 : A →ₗ[K] (Fin 1 → K)) c = 0} :=
  ⟨⟨0, rfl⟩⟩

/-- **Non-degeneracy.**  The released view genuinely reads the encoded word: at
the standard basis word `Pi.single 0 1`, layer-0 coordinate of the released view
is `1`, not `0`.  So the model is not the trivial all-zero collapse. -/
theorem positive_model_nondegenerate :
    circleFoldView enc cf ρ (Pi.single (0 : Fin 4) 1) 0 = 1 := by
  change (ρ 0) (circleWords enc cf (Pi.single (0 : Fin 4) 1) 0) = 1
  rw [circleWords]
  change (LinearMap.proj 0) (enc (Pi.single (0 : Fin 4) 1)) = 1
  rw [enc]
  simp

/-- **The conclusion follows in the positive model.**  Instantiating the
headline decoupling theorem at this concrete data with witnesses `y₁ = 0` and
`y₂ = F (Pi.single 0 1)` (a legal difference, being in `range F`), the two
released circle-fold laws are equal — a genuine, non-vacuous `PMF` identity. -/
theorem positive_model_decoupling :
    (PMF.uniformOfFintype {c : A // (0 : A →ₗ[K] (Fin 1 → K)) c = 0}).map
        (fun c : {c : A // (0 : A →ₗ[K] (Fin 1 → K)) c = 0} =>
          (0 : Fin 5 → K) + circleFoldView enc cf ρ (c : A))
      = (PMF.uniformOfFintype {c : A // (0 : A →ₗ[K] (Fin 1 → K)) c = 0}).map
          (fun c : {c : A // (0 : A →ₗ[K] (Fin 1 → K)) c = 0} =>
            F (Pi.single (0 : Fin 4) 1) + circleFoldView enc cf ρ (c : A)) :=
  circleArity4_conditioned_view_indep enc Φ gf cf ρ transport_holds cdec_holds
    (by
      -- `F (single 0 1) - 0 ∈ range F`
      rw [sub_zero]
      exact LinearMap.mem_range_self F _)
    0

end PositiveModel

/-! ## Negative model: the transport hypothesis is load-bearing

Over `ZMod 3`, replace fold round `0` by a **squaring** `a ↦ a * a` (a genuinely
nonlinear circle "fold").  Then:

* `negative_model_no_transport`: **no** transport isomorphism `Φ` and linear GRS
  folds `gf` can satisfy `CircleArity4Transport` — the commuting diagram would
  force `a ↦ a*a` to be additive, which fails at `a = b = 1`;
* `negative_model_laws_differ`: the two legal witnesses' released circle-fold
  laws are genuinely **different** `PMF`s.

So the headline decoupling theorem's conclusion is false in this model, while its
transport hypothesis is exactly the thing that fails.  The hypothesis is
load-bearing, not decorative. -/

namespace NegativeModel

/-- The working field. -/
abbrev K : Type := ZMod 3

/-- Layer word space (a single symbol suffices to break linearity). -/
abbrev A : Type := K

/-- The concrete circle folds: round `0` **squares** its input (nonlinear over
`ZMod 3`); the later rounds are the identity. -/
def cf : Fin 4 → A → A := ![(fun a => a * a), id, id, id]

/-- The encoder: the identity. -/
def enc : A →ₗ[K] A := LinearMap.id

/-- The read-offs: read the symbol. -/
def ρ : Fin 5 → A →ₗ[K] K := fun _ => LinearMap.id

/-- `cf 0` is exactly squaring. -/
theorem cf_zero (a : A) : cf 0 a = a * a := rfl

/-- **No transport diagram can hold.**  For every candidate transport
isomorphism `Φ` and every choice of linear GRS folds `gf`, the commuting square
at fold `0` fails: it would force squaring to be additive on `ZMod 3`, but
`(1+1)*(1+1) = 1 ≠ 2 = 1*1 + 1*1`.  Hence `CircleArity4Transport` is genuinely
unsatisfiable here — the hypothesis is not vacuously available. -/
theorem negative_model_no_transport
    (Φ : A ≃ₗ[K] A) (gf : Fin 4 → A →ₗ[K] A) :
    ¬ CircleArity4Transport Φ gf cf := by
  intro h
  have h0 : ∀ a : A, Φ (a * a) = gf 0 (Φ a) := by
    intro a; rw [← cf_zero a]; exact h 0 a
  -- the diagram forces squaring to be additive
  have hadd : ∀ a b : A, (a + b) * (a + b) = a * a + b * b := by
    intro a b
    apply Φ.injective
    rw [h0 (a + b), map_add, map_add, ← h0 a, ← h0 b, map_add]
  have hcontra := hadd 1 1
  revert hcontra
  decide

/-- **The released laws differ.**  Take witness contributions `y₁ = 0` and
`y₂ = Pi.single 1 1` (difference supported on layer 1).  Projecting the released
view to layer 1 gives the pushforward of `c ↦ c*c` on the left and
`c ↦ 1 + c*c` on the right.  The value `2 : ZMod 3` is hit by the right law
(at `c = 1`) but by no square, so it lies in the support of one law and not the
other: the two released circle-fold `PMF`s are unequal.  This is the conclusion
of the decoupling theorem failing once transport is dropped. -/
theorem negative_model_laws_differ :
    (PMF.uniformOfFintype A).map
        (fun c : A => (0 : Fin 5 → K) + circleFoldView enc cf ρ c)
      ≠ (PMF.uniformOfFintype A).map
          (fun c : A =>
            (Pi.single 1 1 : Fin 5 → K) + circleFoldView enc cf ρ c) := by
  intro hEq
  -- project both laws to layer 1
  have hproj := congrArg
    (fun q : PMF (Fin 5 → K) => q.map (fun y : Fin 5 → K => y 1)) hEq
  rw [PMF.map_comp, PMF.map_comp] at hproj
  have hL : (fun y : Fin 5 → K => y 1) ∘
        (fun c : A => (0 : Fin 5 → K) + circleFoldView enc cf ρ c)
      = fun c : A => c * c := by
    funext c
    change (0 : Fin 5 → K) 1 + circleFoldView enc cf ρ c 1 = c * c
    rw [circleFoldView]
    change (0 : Fin 5 → K) 1 + (ρ 1) (circleWords enc cf c 1) = c * c
    rw [circleWords]
    change (0 : Fin 5 → K) 1 + (ρ 1) (cf 0 (enc c)) = c * c
    rw [enc, ρ, cf_zero]
    simp
  have hR : (fun y : Fin 5 → K => y 1) ∘
        (fun c : A => (Pi.single 1 1 : Fin 5 → K) + circleFoldView enc cf ρ c)
      = fun c : A => 1 + c * c := by
    funext c
    change (Pi.single 1 1 : Fin 5 → K) 1 + circleFoldView enc cf ρ c 1 = 1 + c * c
    rw [circleFoldView]
    change (Pi.single 1 1 : Fin 5 → K) 1 + (ρ 1) (circleWords enc cf c 1)
        = 1 + c * c
    rw [circleWords]
    change (Pi.single 1 1 : Fin 5 → K) 1 + (ρ 1) (cf 0 (enc c)) = 1 + c * c
    rw [enc, ρ, cf_zero, Pi.single_eq_same]
    simp
  rw [hL, hR] at hproj
  -- `2` is in the right support but not the left
  have hmem : (2 : K) ∈ ((PMF.uniformOfFintype A).map (fun c : A => 1 + c * c)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨1, PMF.mem_support_uniformOfFintype 1, by decide⟩
  rw [← hproj, PMF.mem_support_map_iff] at hmem
  obtain ⟨c, _, hc⟩ := hmem
  exact (by decide : ¬ ∃ c : K, c * c = 2) ⟨c, hc⟩

end NegativeModel

/-! ## Axiom audit

Every export is checked to depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  The circle transport is a *hypothesis* of the headline theorems,
never an axiom. -/

#print axioms circleWords
#print axioms circleFoldView
#print axioms grsEnc
#print axioms grsLayers
#print axioms foldLinearModel
#print axioms CircleArity4Transport
#print axioms circleWords_eq_transported
#print axioms circleFoldView_eq_model
#print axioms structured_refines_placeholder
#print axioms circleArity4_conditioned_view_indep
#print axioms circleArity4_conditioned_complete_view_indep
#print axioms circleArity4_full_fold_conditional_decoupling
#print axioms PositiveModel.arity4Fold
#print axioms PositiveModel.transport_holds
#print axioms PositiveModel.cdec_holds
#print axioms PositiveModel.positive_model_nondegenerate
#print axioms PositiveModel.positive_model_decoupling
#print axioms NegativeModel.cf_zero
#print axioms NegativeModel.negative_model_no_transport
#print axioms NegativeModel.negative_model_laws_differ

end AspisV5ComponentCFoldTransport
