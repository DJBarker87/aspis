import AspisFormal.V5RankOneOpeningHiding
import AspisFormal.V5InactiveClaimJointHiding
import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# The v5 CONDITIONAL complete-view hiding capstone

This file states and proves ONE theorem
(`conditional_complete_view_hiding`): the released v5 complete view —
decomposed into the Component-A masked point-evaluations, the
inactive-claim/Component-B carried coordinates (authenticated terminal
opening, carried inactive claim, residual released view), and the
Component-C conditioned/post-combination coordinates — has a
witness-independent distribution, **conditional on an explicit bundle of
named hypotheses, every one of which is consumed by the proof**.  It is the
composition of the three already-proved component distribution equalities:

* Component A: `AspisV5RankOneOpeningHiding.released_view_pmf_indep`
  (uniform mask through a surjective linear map hides the witness shift on
  the masked point-evaluations);
* Component B: `AspisV5InactiveClaimJointHiding.terminalOpening_inactiveClaim_joint_hiding`
  (one uniform kernel draw feeding terminal opening, carried inactive claim
  and residual view is witness-independent on the terminal fibre);
* Component C: `AspisV5ComponentCConditionalDecoupling.componentC_full_fold_conditional_decoupling_complete_view`
  (under the audit's C-DEC containment, the conditioned-fibre law of the
  full-fold complete view is witness-independent).

**HARD FENCE — read before citing.**  This theorem does **not** say "v5 is
zero-knowledge", and nothing in this repository proves that.  What is proved
is an *implication*: IF the deployed system satisfies the named interface
hypotheses below (commitment binding, commit-before-challenge ordering,
Rust↔Lean map correspondence, sampler uniformity, exact serialization,
nonzero lane/batching challenges, circle/arity-4 fold transport, C-DEC, the
component surjectivity/pivot facts, and independence of the three mask
sources), THEN the modeled complete-view distribution carries no witness
information.  Every hypothesis is load-bearing: the file ends with concrete
counterexamples showing the conclusion is *false* once the
sampler-uniformity premise or the nonzero-batching-challenge premise is
dropped, and with a concrete finite instantiation showing the whole bundle
is simultaneously satisfiable (so the implication is not vacuous).

## The four honesty tiers

1. **Kernel facts proved here** (machine-checked, axioms ⊆
   `{propext, Classical.choice, Quot.sound}`): the composition theorem
   `conditional_complete_view_hiding` itself; the product-pushforward
   lemmas `tripleProduct_map` / `tripleProduct_map_fst`; the
   data-processing lemma `map_encode_congr`; the row-extraction lemma
   `rustConditionedRows_eq_of_correspondence`; the satisfiability witness
   `rustRowOfMaps_correspondence`; the non-vacuity instantiation
   `capstone_hypotheses_instantiable`; and the two negative tests.
2. **Cited external assumptions** (mathematics believed on citation, not
   re-proved here): the circle/arity-4 FRI decoupling transport enters only
   as the named hypothesis `CircleArityFourFoldTransport` — the intended
   discharge is the circle-code analogue of Haböck–Al Kindi,
   ePrint 2024/1037 (Protocol 2, Lemma 2, Theorems 4 and 6), which is
   stated there for binary univariate Reed–Solomon FRI and has **not** been
   transported to the Aspis circle/arity-4 grammar.
3. **Computational assumptions** (true only against bounded adversaries,
   modeled here as perfect): `PivotBoundByPreChallengeCommitment` models a
   *computationally* binding commitment as perfectly binding, and
   `CommitmentBeforeGammaAndGammaNeZero` models Fiat–Shamir challenge
   derivation as a function of the transcript prefix (random-oracle-style
   ordering).  A computationally bounded reduction replacing these perfect
   models with negligible-error ones is not formalised anywhere in this
   repository.
4. **Still-open code/model interfaces** (named `Prop`s consumed as
   hypotheses, discharged here only for the toy model, never for the
   deployed artefacts): `RustLeanRowCorrespondence332` for the deployed
   serializer rows, `SamplerUniformOnKerEll` for the deployed sampler,
   `DeployedTerminalMatchesModel` for the deployed terminal evaluator, the
   exact-serialization equations `hserialize₁/₂` for the deployed byte
   stream, the C-DEC containment `CDecAudit` for the deployed matrices, the
   independence/product structure `hindependent` for the deployed joint
   sampler, and the Component-B pivot/surjectivity facts for the deployed
   layout beyond the row-993 kernel fact already proved in
   `V5InactiveClaimJointHiding`.

Until every tier-4 interface is discharged against the real artefacts and
the tier-2/3 assumptions are either proved or explicitly carried, the
honest summary remains: **v5 complete-view hiding is conditional, and v5 is
not proven zero-knowledge.**
-/

open scoped ENNReal

namespace AspisV5ConditionalHidingCapstone

open AspisV5RankOneOpeningHiding AspisV5InactiveClaimJointHiding
  AspisV5ComponentCConditionalDecoupling
  AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces

/-! ## 1. Product plumbing: independent triples of samplers

The three components draw from three mask sources.  That they are
*independent* is NOT assumed silently: the capstone takes the explicit named
hypothesis `hindependent : jointSampler = tripleProduct …`, and the lemmas
here are what consume it.  `tripleProduct` is the standard monadic product
(sample `a`, then `b`, then `c`, return the triple); `tripleProduct_map`
says a componentwise map of an independent triple is the triple of the
mapped components — the exact factorisation step of the capstone proof. -/

section ProductPlumbing

variable {α β γ α' β' γ' : Type*}

/-- The independent product of three samplers: draw each coordinate from its
own `PMF`, with no coordinate reading another's sample. -/
noncomputable def tripleProduct (pA : PMF α) (pB : PMF β) (pC : PMF γ) :
    PMF (α × β × γ) :=
  pA.bind fun a => pB.bind fun b => pC.map fun c => (a, b, c)

/-- **Componentwise maps factor through independent triples.**  Pushing an
independent triple through a function that acts on each coordinate
separately yields the independent triple of the pushed components.  This is
the step that turns "the joint sampler is a product" (hypothesis
`hindependent` of the capstone) into "the complete-view law is the product
of the three component-view laws". -/
theorem tripleProduct_map (pA : PMF α) (pB : PMF β) (pC : PMF γ)
    (fA : α → α') (fB : β → β') (fC : γ → γ') :
    (tripleProduct pA pB pC).map (fun s => (fA s.1, fB s.2.1, fC s.2.2))
      = tripleProduct (pA.map fA) (pB.map fB) (pC.map fC) := by
  simp only [tripleProduct, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def]

/-- The first marginal of an independent triple is the first factor.  Used
by the negative test to project a complete-view law equality down to the
Component-A law, where the failure is visible. -/
theorem tripleProduct_map_fst (pA : PMF α) (pB : PMF β) (pC : PMF γ) :
    (tripleProduct pA pB pC).map Prod.fst = pA := by
  have hconst : ∀ a : α, (pC.map fun _ : γ => a) = PMF.pure a :=
    fun a => PMF.map_const pC a
  simp only [tripleProduct, PMF.map_bind, PMF.map_comp, Function.comp_def,
    hconst, PMF.bind_const, PMF.bind_pure]

/-- Mapping any sampler through a constant function gives the point mass:
`PMF.map_const` with the constant spelled as a lambda.  Used by the
negative tests to compute degenerate view laws. -/
theorem map_const_eq_pure {α β : Type*} (p : PMF α) (b : β) :
    p.map (fun _ => b) = PMF.pure b :=
  PMF.map_const p b

/-- **Deterministic post-processing preserves equality of laws.**  This is
the data-processing step that consumes the exact-serialization hypotheses
`hserialize₁/₂`: once the released byte stream is known to be a function of
exactly the modeled complete view, equality of the view laws forces
equality of the byte laws. -/
theorem map_encode_congr {α V B : Type*} (P : PMF α) (encode : V → B)
    {v w : α → V} (h : P.map v = P.map w) :
    P.map (fun s => encode (v s)) = P.map (fun s => encode (w s)) := by
  calc P.map (fun s => encode (v s))
      = (P.map v).map encode := (PMF.map_comp v P encode).symm
    _ = (P.map w).map encode := by rw [h]
    _ = P.map (fun s => encode (w s)) := PMF.map_comp w P encode

end ProductPlumbing

/-! ## 2. The released complete view, in deployed spelling

The view functions below are written in terms of the *deployed* maps — the
deployed terminal evaluator, the deployed serializer rows, the deployed
fold pipeline — so that the Rust↔Lean correspondence hypotheses are forced
to do real work in the proof: without them the deployed functions have no
linear structure and none of the component theorems applies. -/

section Views

variable {K : Type*} [Field K]

/-- The complete released view type: Component-A masked point-evaluations,
the Component-B triple (authenticated terminal opening, carried inactive
claim, residual released view), and the Component-C pair (76 conditioned
coordinates, 256 post-combination coordinates). -/
abbrev CompleteViewType (K VA VB : Type*) : Type _ :=
  VA × (K × K × VB) × ((Fin 76 → K) × (Fin 256 → K))

/-- Component-A released view: the masked point-evaluations `wA + LA r`,
the witness contribution shifted by the mask's evaluations. -/
def componentAView {MA VA : Type*} [AddCommGroup MA] [Module K MA]
    [AddCommGroup VA] [Module K VA] (LA : MA →ₗ[K] VA) (wA : VA) :
    MA → VA :=
  fun r => wA + LA r

/-- Component-B released view, deployed spelling: the authenticated
terminal opening (evaluated by the *deployed* terminal evaluator), the
carried inactive-claim coordinate, and the residual released view, all
three functionals of the same kernel draw added to the witness mask `mB`. -/
def componentBView {MB VB : Type*} [AddCommGroup MB] [Module K MB]
    [AddCommGroup VB] [Module K VB]
    (terminalB : MB →ₗ[K] K) (deployedTerminalB : MB → K)
    (inactiveB : MB →ₗ[K] K) (residualB : MB →ₗ[K] VB) (mB : MB) :
    LinearMap.ker terminalB → K × K × VB :=
  fun u => (deployedTerminalB (mB + (u : MB)), inactiveB (mB + (u : MB)),
    residualB (mB + (u : MB)))

/-- The 76 conditioned Component-C coordinates as released by the deployed
serializer: joint rows `0..75` (through the 332-row cast) evaluated on the
mask. -/
def rustConditionedRows {MC : Type*} [AddCommGroup MC] [Module K MC]
    (rustRow : Fin 332 → MC →ₗ[K] K) (m : MC) : Fin 76 → K :=
  fun i => rustRow
    (Fin.cast (by norm_num : (76 + 256 : ℕ) = 332) (Fin.castAdd 256 i)) m

/-- Component-C released view, deployed spelling: the 76 conditioned rows
of the deployed serializer on the mask, and the deployed fold pipeline on
the `γ^18`-folded word. -/
def componentCView {MC : Type*} [AddCommGroup MC] [Module K MC]
    (ell : MC →ₗ[K] K) (rustRow : Fin 332 → MC →ₗ[K] K)
    (concreteFold : MC → Fin 256 → K) (xC : MC) (γ : K) :
    LinearMap.ker ell → (Fin 76 → K) × (Fin 256 → K) :=
  fun c => (rustConditionedRows rustRow (c : MC),
    concreteFold (xC + γ ^ 18 • ((c : LinearMap.ker ell) : MC)))

/-- The complete released view of one run: the three component views, each
reading its own coordinate of the three-part mask sample. -/
def completeView {MA VA MB VB MC : Type*}
    [AddCommGroup MA] [Module K MA] [AddCommGroup VA] [Module K VA]
    [AddCommGroup MB] [Module K MB] [AddCommGroup VB] [Module K VB]
    [AddCommGroup MC] [Module K MC]
    (LA : MA →ₗ[K] VA) (wA : VA)
    (terminalB : MB →ₗ[K] K) (deployedTerminalB : MB → K)
    (inactiveB : MB →ₗ[K] K) (residualB : MB →ₗ[K] VB) (mB : MB)
    (ell : MC →ₗ[K] K) (rustRow : Fin 332 → MC →ₗ[K] K)
    (concreteFold : MC → Fin 256 → K) (xC : MC) (γ : K) :
    MA × LinearMap.ker terminalB × LinearMap.ker ell →
      CompleteViewType K VA VB :=
  fun s => (componentAView LA wA s.1,
    componentBView terminalB deployedTerminalB inactiveB residualB mB s.2.1,
    componentCView ell rustRow concreteFold xC γ s.2.2)

/-- `completeView` unfolded to the componentwise-product shape consumed by
`tripleProduct_map`. -/
theorem completeView_eq {MA VA MB VB MC : Type*}
    [AddCommGroup MA] [Module K MA] [AddCommGroup VA] [Module K VA]
    [AddCommGroup MB] [Module K MB] [AddCommGroup VB] [Module K VB]
    [AddCommGroup MC] [Module K MC]
    (LA : MA →ₗ[K] VA) (wA : VA)
    (terminalB : MB →ₗ[K] K) (deployedTerminalB : MB → K)
    (inactiveB : MB →ₗ[K] K) (residualB : MB →ₗ[K] VB) (mB : MB)
    (ell : MC →ₗ[K] K) (rustRow : Fin 332 → MC →ₗ[K] K)
    (concreteFold : MC → Fin 256 → K) (xC : MC) (γ : K) :
    completeView LA wA terminalB deployedTerminalB inactiveB residualB mB
        ell rustRow concreteFold xC γ
      = fun s : MA × LinearMap.ker terminalB × LinearMap.ker ell =>
          (componentAView LA wA s.1,
            componentBView terminalB deployedTerminalB inactiveB residualB
              mB s.2.1,
            componentCView ell rustRow concreteFold xC γ s.2.2) :=
  rfl

end Views

/-! ## 3. Extracting the Lean maps from the Rust row correspondence -/

section RowCorrespondence

variable {K : Type*} [Field K] {MC : Type*} [AddCommGroup MC] [Module K MC]

/-- **The row correspondence pins the deployed conditioned rows to `E`.**
Under `RustLeanRowCorrespondence332`, the first 76 deployed serializer rows
evaluate on any mask exactly as the Lean conditioned-coordinate map `E`.
This is the only route from the deployed spelling of the Component-C view
back to the linear map the decoupling theorem speaks about; the capstone
proof cannot proceed without it. -/
theorem rustConditionedRows_eq_of_correspondence
    {rustRow : Fin 332 → MC →ₗ[K] K}
    {E : MC →ₗ[K] Fin 76 → K} {F : MC →ₗ[K] Fin 256 → K}
    (hrow : RustLeanRowCorrespondence332 rustRow E F) (m : MC) :
    rustConditionedRows rustRow m = E m := by
  funext i
  have h := congrFun (hrow m)
    (Fin.cast (by norm_num : (76 + 256 : ℕ) = 332) (Fin.castAdd 256 i))
  simp only [rustConditionedRows, Function.comp_apply] at h ⊢
  rw [h]
  have hcast : Fin.cast (by norm_num : (332 : ℕ) = 76 + 256)
      (Fin.cast (by norm_num : (76 + 256 : ℕ) = 332) (Fin.castAdd 256 i))
        = Fin.castAdd 256 i := by
    apply Fin.ext
    simp
  rw [hcast, Fin.append_left]

/-- Evaluating an append of two families of linear maps commutes with
evaluating each family pointwise.  Bookkeeping for
`rustRowOfMaps_correspondence`. -/
theorem append_apply_pointwise {m n : ℕ}
    (u : Fin m → MC →ₗ[K] K) (v : Fin n → MC →ₗ[K] K)
    (j : Fin (m + n)) (c : MC) :
    Fin.append u v j c
      = Fin.append (fun a => u a c) (fun b => v b c) j := by
  induction j using Fin.addCases with
  | left i => simp only [Fin.append_left]
  | right i => simp only [Fin.append_right]

/-- A model serializer built from the Lean maps themselves.  It satisfies
the 332-row correspondence (`rustRowOfMaps_correspondence`), witnessing
that the `RustLeanRowCorrespondence332` interface is satisfiable — for the
*model*.  Nothing here says the deployed Rust serializer equals it. -/
def rustRowOfMaps (E : MC →ₗ[K] Fin 76 → K) (F : MC →ₗ[K] Fin 256 → K) :
    Fin 332 → MC →ₗ[K] K :=
  fun i => Fin.append (fun a => LinearMap.proj a ∘ₗ E)
    (fun b => LinearMap.proj b ∘ₗ F)
    (Fin.cast (by norm_num : (332 : ℕ) = 76 + 256) i)

/-- The model serializer satisfies the row correspondence: the interface
hypothesis of the capstone is not unsatisfiable by construction. -/
theorem rustRowOfMaps_correspondence
    (E : MC →ₗ[K] Fin 76 → K) (F : MC →ₗ[K] Fin 256 → K) :
    RustLeanRowCorrespondence332 (rustRowOfMaps E F) E F := by
  intro c
  funext i
  simp only [rustRowOfMaps, Function.comp_apply]
  exact append_apply_pointwise _ _ _ c

end RowCorrespondence

/-! ## 4. The capstone theorem -/

section Capstone

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  {MA VA : Type*} [AddCommGroup MA] [Module K MA] [Fintype MA] [Nonempty MA]
  [AddCommGroup VA] [Module K VA] [FiniteDimensional K VA]
  {MB VB : Type*} [AddCommGroup MB] [Module K MB] [Fintype MB]
  [AddCommGroup VB] [Module K VB] [FiniteDimensional K VB]
  {MC : Type*} [AddCommGroup MC] [Module K MC] [Fintype MC]
  {CommitmentB Transcript TranscriptPrefix Bytes : Type*}

/-- **The v5 CONDITIONAL complete-view hiding capstone.**

One-line reading: *given* commitment binding, commit-before-challenge
ordering, Rust↔Lean map correspondence, sampler uniformity, exact
serialization, nonzero lane/batching challenges, the circle/arity-4 fold
transport, C-DEC, the component pivot/surjectivity facts, and independence
of the three mask sources, the released complete-view byte stream has
exactly the same distribution for the two witness runs.

The two runs release
`releasedBytes_i = encode ∘ completeView(wA_i, mB_i, xC_i, γ(t_i))`, the
serialization of the triple (Component-A masked point-evaluations,
Component-B terminal/inactive/residual triple, Component-C conditioned and
post-combination coordinates), and the joint sampler draws the three mask
coordinates.  The conclusion is an exact `PMF` equality of the two byte
laws.

Where each named hypothesis is consumed (none is decorative):

* `hbinding` + `hsharedCommit` (PCS/commitment binding): produce
  `terminalB mB₂ = terminalB mB₁`, the second fibre condition `h₂` of the
  Component-B joint-hiding theorem — the shared released commitment is what
  forces the two runs onto the same authenticated terminal fibre.
* `hordering` + `hsharedPrefix` (commit-before-challenge ordering): the
  prefix-determinism half collapses the two runs' batching challenges
  (`gammaOf t₂ = gammaOf t₁`), without which the two Component-C views use
  different folds and the C theorem cannot be applied; the nonzeroness half
  supplies `hγ` to the C decoupling theorem.
* `hrow` (Rust↔Lean row correspondence): rewrites the deployed serializer
  rows `rustConditionedRows rustRow` into the Lean map `E`
  (`rustConditionedRows_eq_of_correspondence`); without it the deployed
  view has no linear structure.
* `hterminal` (deployed-terminal correspondence): rewrites the deployed
  terminal evaluator into the Lean functional `terminalB` inside the
  Component-B view.
* `hsamplerA`, `hsamplerB`, `hsamplerC` (sampler uniformity on the mask
  space / terminal kernel / `ker ℓ`): substituted into the joint law; the
  component hiding theorems are about the uniform laws and nothing else.
* `hindependent` (independence/product structure): substitutes the joint
  sampler by `tripleProduct`, after which `tripleProduct_map` factors the
  complete-view law into the three component laws.  The three views do
  **not** silently factor: this hypothesis is the only reason they do.
* `hserialize₁/₂` (exact serialization): substitute the byte functions by
  `encode ∘ completeView`, consumed by the data-processing lemma
  `map_encode_congr`; they assert the released bytes are a function of
  exactly the modeled coordinates (no extra mask-dependent leak).
* `hlane` + `hgammaB` (lane coefficient, `gammaB ≠ 0`): discharge
  `inactiveB kB ≠ 0` via `pivot_inactive_nonzero_of_gammaB`, the pivot
  premise of the Component-B theorem.
* `htransport` (circle/arity-4 FRI transport, cited external): rewrites
  the deployed fold pipeline into the Lean map `F` inside the Component-C
  view.
* `hA_surj`: the surjectivity premise of Component A's
  `released_view_pmf_indep`.
* `hB_pivot_ker`, `hB_fresh`, `hB_rel`: the pivot-kernel, pivot-freshness
  and restricted-surjectivity premises of Component B's
  `terminalOpening_inactiveClaim_joint_hiding`.
* `hCdec` + `hlegal`: the C-DEC containment and witness-difference
  legality premises of Component C's
  `componentC_full_fold_conditional_decoupling_complete_view`.
* `hsupp`: the conditioning event `E = e` is charged by the C sampler
  (equivalently, `e` is in the image of the conditioned coordinates); it
  is the well-definedness argument of the `PMF.filter` conditioning and
  yields the nonemptiness of the conditioned fibre.

**This is a conditional statement.**  It does not prove v5 zero-knowledge;
see the module docstring for the four-tier honesty ledger. -/
theorem conditional_complete_view_hiding
    -- released-view data
    (LA : MA →ₗ[K] VA) (wA₁ wA₂ : VA)
    (terminalB inactiveB : MB →ₗ[K] K) (residualB : MB →ₗ[K] VB)
    (deployedTerminalB : MB → K) (kB mB₁ mB₂ : MB) (gammaB : K)
    (commitB : MB → CommitmentB)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] Fin 76 → K) (F : MC →ₗ[K] Fin 256 → K)
    (Δw : Submodule K MC) (xC₁ xC₂ : MC) (e : Fin 76 → K)
    (rustRow : Fin 332 → MC →ₗ[K] K) (concreteFold : MC → Fin 256 → K)
    (commitPrefixC : Transcript → TranscriptPrefix) (gammaOf : Transcript → K)
    (t₁ t₂ : Transcript)
    -- sampler and serialization data
    (samplerA : PMF MA) (samplerB : PMF (LinearMap.ker terminalB))
    (samplerCKer : PMF (LinearMap.ker ell))
    (hsupp : ∃ c ∈ {c : LinearMap.ker ell |
        E.domRestrict (LinearMap.ker ell) c = e}, c ∈ samplerCKer.support)
    (jointSampler : PMF (MA × LinearMap.ker terminalB × LinearMap.ker ell))
    (encode : CompleteViewType K VA VB → Bytes)
    (releasedBytes₁ releasedBytes₂ :
      MA × LinearMap.ker terminalB × LinearMap.ker ell → Bytes)
    -- (H1) PCS/commitment binding
    (hbinding : PivotBoundByPreChallengeCommitment commitB (⇑terminalB))
    (hsharedCommit : commitB mB₁ = commitB mB₂)
    -- (H2) commit-before-challenge ordering
    (hordering : CommitmentBeforeGammaAndGammaNeZero commitPrefixC gammaOf)
    (hsharedPrefix : commitPrefixC t₁ = commitPrefixC t₂)
    -- (H3) Rust↔Lean correspondence
    (hrow : RustLeanRowCorrespondence332 rustRow E F)
    (hterminal : DeployedTerminalMatchesModel deployedTerminalB terminalB)
    -- (H4) sampler uniformity
    (hsamplerA : samplerA = PMF.uniformOfFintype MA)
    (hsamplerB : samplerB = PMF.uniformOfFintype (LinearMap.ker terminalB))
    (hsamplerC : SamplerUniformOnKerEll ell samplerCKer)
    -- (H5) independence/product structure of the three mask sources
    (hindependent : jointSampler
      = tripleProduct samplerA samplerB
          (samplerCKer.filter
            {c : LinearMap.ker ell |
              E.domRestrict (LinearMap.ker ell) c = e} hsupp))
    -- (H6) exact serialization
    (hserialize₁ : releasedBytes₁ = fun s => encode
      (completeView LA wA₁ terminalB deployedTerminalB inactiveB residualB
        mB₁ ell rustRow concreteFold xC₁ (gammaOf t₁) s))
    (hserialize₂ : releasedBytes₂ = fun s => encode
      (completeView LA wA₂ terminalB deployedTerminalB inactiveB residualB
        mB₂ ell rustRow concreteFold xC₂ (gammaOf t₂) s))
    -- (H7) lane coefficient and gammaB ≠ 0
    (hlane : PivotCoefficientIsGammaB inactiveB kB gammaB)
    (hgammaB : gammaB ≠ 0)
    -- (H8) circle/arity-4 FRI transport (cited external; see module docstring)
    (htransport : CircleArityFourFoldTransport concreteFold F)
    -- (H9) component-internal irreducible edges
    (hA_surj : Function.Surjective LA)
    (hB_pivot_ker : terminalB kB = 0)
    (hB_fresh : residualB kB = 0)
    (hB_rel : Function.Surjective
      (residualB ∘ₗ (LinearMap.ker terminalB).subtype))
    (hCdec : CDecAudit ell E F Δw)
    (hlegal : xC₂ - xC₁ ∈ Δw) :
    jointSampler.map releasedBytes₁ = jointSampler.map releasedBytes₂ := by
  -- (H6) exact serialization, (H5) independence, (H4) A/B sampler
  -- uniformity: substitute the deployed objects by their modeled values.
  subst hserialize₁ hserialize₂ hindependent hsamplerA hsamplerB
  -- (H4) C sampler uniformity, through the named interface `Prop`.
  have hCuniform : samplerCKer = PMF.uniformOfFintype (LinearMap.ker ell) :=
    hsamplerC
  subst hCuniform
  -- (H1) binding + shared commitment: the runs share the terminal value.
  have hsharedTerminal : terminalB mB₂ = terminalB mB₁ :=
    (hbinding mB₁ mB₂ hsharedCommit).symm
  -- (H7) lane coefficient + gammaB ≠ 0: the pivot feeds the inactive claim.
  have hpivot_inactive : inactiveB kB ≠ 0 :=
    pivot_inactive_nonzero_of_gammaB inactiveB kB gammaB hlane hgammaB
  -- (H2) ordering: γ is prefix-determined and nonzero.
  have hord : (∀ t, gammaOf t ≠ 0) ∧ ∀ u₁ u₂ : Transcript,
      commitPrefixC u₁ = commitPrefixC u₂ → gammaOf u₁ = gammaOf u₂ :=
    hordering
  have hγeq : gammaOf t₂ = gammaOf t₁ := (hord.2 t₁ t₂ hsharedPrefix).symm
  have hγne : gammaOf t₁ ≠ 0 := hord.1 t₁
  -- (H3) correspondences, in applied form.
  have hterminal' : ∀ m : MB, deployedTerminalB m = terminalB m := hterminal
  have htransport' : ∀ v : MC, concreteFold v = F v := htransport
  -- the conditioned Component-C fibre is inhabited (from hsupp).
  haveI hfibNE : Nonempty {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e} :=
    ⟨⟨hsupp.choose, hsupp.choose_spec.1⟩⟩
  -- Component A law equality (uses hA_surj).
  have hAlaw : (PMF.uniformOfFintype MA).map (componentAView LA wA₁)
      = (PMF.uniformOfFintype MA).map (componentAView LA wA₂) :=
    released_view_pmf_indep LA hA_surj wA₁ wA₂
  -- Component B law equality (uses hterminal, hB_pivot_ker,
  -- hpivot_inactive, hB_fresh, hB_rel, hsharedTerminal).
  have hBview : ∀ mB : MB,
      componentBView terminalB deployedTerminalB inactiveB residualB mB
        = fun u : LinearMap.ker terminalB =>
            (terminalB (mB + (u : MB)), inactiveB (mB + (u : MB)),
              residualB (mB + (u : MB))) := by
    intro mB
    funext u
    simp only [componentBView, hterminal']
  have hBlaw : (PMF.uniformOfFintype (LinearMap.ker terminalB)).map
        (componentBView terminalB deployedTerminalB inactiveB residualB mB₁)
      = (PMF.uniformOfFintype (LinearMap.ker terminalB)).map
        (componentBView terminalB deployedTerminalB inactiveB residualB
          mB₂) := by
    rw [hBview mB₁, hBview mB₂]
    exact terminalOpening_inactiveClaim_joint_hiding terminalB inactiveB
      residualB kB hB_pivot_ker hpivot_inactive hB_fresh hB_rel
      (terminalB mB₁) mB₁ mB₂ rfl hsharedTerminal
  -- Component C law equality (uses hrow, htransport, hγeq, hγne, hCdec,
  -- hlegal, hsupp).
  have hCview : ∀ (xC : MC) (γ : K),
      ((componentCView ell rustRow concreteFold xC γ) ∘
          (Subtype.val : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} → LinearMap.ker ell))
        = fun c : {c : LinearMap.ker ell //
            E.domRestrict (LinearMap.ker ell) c = e} =>
            (E.domRestrict (LinearMap.ker ell) (c : LinearMap.ker ell),
              F (xC + γ ^ 18 • ((c : LinearMap.ker ell) : MC))) := by
    intro xC γ
    funext c
    simp only [Function.comp_apply, componentCView,
      rustConditionedRows_eq_of_correspondence hrow, htransport',
      LinearMap.domRestrict_apply]
  have hClaw : ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell | E.domRestrict (LinearMap.ker ell) c = e}
        hsupp).map (componentCView ell rustRow concreteFold xC₁ (gammaOf t₁))
      = ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell | E.domRestrict (LinearMap.ker ell) c = e}
        hsupp).map
        (componentCView ell rustRow concreteFold xC₂ (gammaOf t₂)) := by
    rw [hγeq,
      uniform_conditioned_eq_uniform_fibre
        (E.domRestrict (LinearMap.ker ell)) e hsupp,
      PMF.map_comp, PMF.map_comp, hCview xC₁ (gammaOf t₁),
      hCview xC₂ (gammaOf t₁)]
    exact componentC_full_fold_conditional_decoupling_complete_view ell E F
      hγne hCdec hlegal e
  -- data processing: serialization preserves the view-law equality.
  refine map_encode_congr _ encode ?_
  -- factor the complete view through the independent triple product and
  -- rewrite each component law.
  rw [completeView_eq, completeView_eq,
    tripleProduct_map (PMF.uniformOfFintype MA)
      (PMF.uniformOfFintype (LinearMap.ker terminalB))
      ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell |
          E.domRestrict (LinearMap.ker ell) c = e} hsupp)
      (componentAView LA wA₁)
      (componentBView terminalB deployedTerminalB inactiveB residualB mB₁)
      (componentCView ell rustRow concreteFold xC₁ (gammaOf t₁)),
    tripleProduct_map (PMF.uniformOfFintype MA)
      (PMF.uniformOfFintype (LinearMap.ker terminalB))
      ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell |
          E.domRestrict (LinearMap.ker ell) c = e} hsupp)
      (componentAView LA wA₂)
      (componentBView terminalB deployedTerminalB inactiveB residualB mB₂)
      (componentCView ell rustRow concreteFold xC₂ (gammaOf t₂)),
    hAlaw, hBlaw, hClaw]

end Capstone

/-! ## 5. Non-vacuity: the whole hypothesis bundle is satisfiable

A concrete finite instantiation over `ZMod 2`.  Component A is the identity
map on a one-dimensional mask space; Component B is the `Fin 3` projection
model with pivot `![0, 1, 0]` (the same model used for non-vacuity in
`V5InactiveClaimJointHiding`); Component C is a one-dimensional word space
embedded in coordinate `0` of the 256 post-combination coordinates, with
nothing conditioned (`E = 0`, so C-DEC holds with the full difference
space) and the model serializer `rustRowOfMaps`.  Every named hypothesis of
the capstone is discharged, so the capstone is not vacuously true. -/

section NonVacuityAndNegativeTests

/-- The example Component-C view map: embed the one-dimensional word space
into coordinate `0` of the 256 post-combination coordinates. -/
def egF : ZMod 2 →ₗ[ZMod 2] (Fin 256 → ZMod 2) :=
  LinearMap.single (ZMod 2) (fun _ : Fin 256 => ZMod 2) 0

/-- The example conditioning event is charged: the zero mask lies on the
fibre `E = 0` and in the support of the uniform sampler. -/
theorem egSupp : ∃ c ∈ {c : LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) |
    (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)).domRestrict
      (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) c = 0},
    c ∈ (PMF.uniformOfFintype
      (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2))).support :=
  ⟨0, by simp, PMF.mem_support_uniformOfFintype 0⟩

/-- The example joint sampler, parameterised by the Component-A sampler so
that the negative test below can swap out uniformity while keeping every
other datum fixed. -/
noncomputable def egJoint (pA : PMF (ZMod 2)) :
    PMF (ZMod 2 ×
      LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) :=
  tripleProduct pA
    (PMF.uniformOfFintype (LinearMap.ker
      (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)))
    ((PMF.uniformOfFintype
      (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2))).filter
      {c : LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) |
        (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)).domRestrict
          (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) c = 0} egSupp)

/-- The example complete view of one run (batching challenge fixed at the
example's `gammaOf () = 1`). -/
def egView (wA : ZMod 2) (mB : Fin 3 → ZMod 2) (xC : ZMod 2) :
    ZMod 2 ×
      LinearMap.ker (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ×
      LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) →
      CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2) :=
  completeView (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) wA
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (⇑(LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) mB
    (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
    (rustRowOfMaps (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF)
    (⇑egF) xC 1

/-- **Non-vacuity of the capstone.**  Every named hypothesis of
`conditional_complete_view_hiding` is discharged for the concrete `ZMod 2`
data, with the two runs differing in the Component-A witness (`wA₁` vs
`wA₂`), the Component-B witness (`![0,0,0]` vs `![0,1,1]`, differing in
inactive and residual components on the shared terminal fibre), and the
Component-C witness word (`0` vs `1`, a legal difference).  The capstone
conclusion therefore holds for it: the theorem is not vacuously true. -/
theorem capstone_hypotheses_instantiable (wA₁ wA₂ : ZMod 2) :
    (egJoint (PMF.uniformOfFintype (ZMod 2))).map (egView wA₁ ![0, 0, 0] 0)
      = (egJoint (PMF.uniformOfFintype (ZMod 2))).map
        (egView wA₂ ![0, 1, 1] 1) :=
  conditional_complete_view_hiding
    (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) wA₁ wA₂
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (⇑(LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    ![0, 1, 0] ![0, 0, 0] ![0, 1, 1] 1
    (fun m => m 0)
    (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
    (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF ⊤ 0 1 0
    (rustRowOfMaps (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF) (⇑egF)
    (fun _ => ()) (fun _ => 1) () ()
    (PMF.uniformOfFintype (ZMod 2))
    (PMF.uniformOfFintype _)
    (PMF.uniformOfFintype _)
    egSupp
    (egJoint (PMF.uniformOfFintype (ZMod 2)))
    id
    (egView wA₁ ![0, 0, 0] 0) (egView wA₂ ![0, 1, 1] 1)
    -- (H1) binding: the commitment reveals coordinate 0, which is the
    -- terminal functional's value.
    (fun _ _ h => h)
    -- shared commitment of the two Component-B witnesses
    rfl
    -- (H2) ordering: γ is the constant 1, prefix-determined and nonzero.
    ⟨fun _ => one_ne_zero, fun _ _ _ => rfl⟩
    rfl
    -- (H3) correspondences: the model serializer and the model evaluators.
    (rustRowOfMaps_correspondence 0 egF)
    (fun _ => rfl)
    -- (H4) sampler uniformity: the example samplers are uniform.
    rfl rfl rfl
    -- (H5) independence: the example joint sampler is the triple product.
    rfl
    -- (H6) exact serialization: `encode = id`, bytes are the view itself.
    rfl rfl
    -- (H7) lane coefficient (the shared `Fin 3` pivot model) and gammaB ≠ 0.
    pivotCoefficient_interface_nonvacuous
    one_ne_zero
    -- (H8) fold transport: the model fold is `egF` itself.
    (fun _ => rfl)
    -- (H9) component-internal edges.
    (fun x => ⟨x, rfl⟩)
    rfl
    rfl
    example_restricted_surjective
    (by simp [CDecAudit, LinearMap.ker_zero])
    Submodule.mem_top

/-! ## 6. Load-bearing negative tests

Two premises are removed, one at a time, and the conclusion is shown to be
**false** for the removed-premise instantiation while the surrounding data
still satisfies the rest of the bundle (as discharged in
`capstone_hypotheses_instantiable`, which uses the same example data).
This is the proof that the hypothesis bundle contains no decorative
premise of these kinds: the route genuinely breaks without them. -/

/-- **Negative test 1: sampler uniformity is load-bearing.**  Identical
data to `capstone_hypotheses_instantiable` except the Component-A sampler
is the point mass at `0` instead of the uniform distribution — violating
exactly `hsamplerA` and nothing else (no other premise mentions
`samplerA`).  The capstone conclusion is then FALSE: the degenerate mask
releases the Component-A witness in the clear, and the two complete-view
laws have different `Prod.fst` marginals (`pure wA₁ ≠ pure wA₂`). -/
theorem samplerA_uniformity_isLoadBearing :
    (egJoint (PMF.pure 0)).map (egView 0 ![0, 0, 0] 0)
      ≠ (egJoint (PMF.pure 0)).map (egView 1 ![0, 0, 0] 0) := by
  intro hcontra
  have hmarg : ∀ wA : ZMod 2,
      ((egJoint (PMF.pure 0)).map (egView wA ![0, 0, 0] 0)).map Prod.fst
        = PMF.pure wA := by
    intro wA
    have hfst : ((egJoint (PMF.pure 0)).map (egView wA ![0, 0, 0] 0)).map
          Prod.fst
        = (PMF.pure (0 : ZMod 2)).map (componentAView (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) wA) := by
      rw [show (egJoint (PMF.pure 0)).map (egView wA ![0, 0, 0] 0)
            = tripleProduct
                ((PMF.pure (0 : ZMod 2)).map (componentAView (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) wA))
                ((PMF.uniformOfFintype (LinearMap.ker
                    (LinearMap.proj 0 :
                      (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))).map
                  (componentBView (LinearMap.proj 0) (⇑(LinearMap.proj 0))
                    (LinearMap.proj 1) (LinearMap.proj 2) ![0, 0, 0]))
                (((PMF.uniformOfFintype (LinearMap.ker
                    (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2))).filter
                    {c : LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) |
                      (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)).domRestrict
                        (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) c = 0}
                    egSupp).map
                  (componentCView (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
                    (rustRowOfMaps (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2))
                      egF) (⇑egF) 0 1))
          from tripleProduct_map _ _ _ _ _ _,
        tripleProduct_map_fst]
    rw [hfst, PMF.pure_map]
    simp [componentAView]
  have h01 := (hmarg 0).symm.trans
    ((congrArg (fun q => q.map Prod.fst) hcontra).trans (hmarg 1))
  have h0 := congrArg (fun q : PMF (ZMod 2) => q 0) h01
  rw [PMF.pure_apply, PMF.pure_apply, if_pos rfl,
    if_neg (by decide : ¬((0 : ZMod 2) = 1))] at h0
  exact one_ne_zero h0

/-- **Negative test 2: the nonzero batching challenge is load-bearing.**
For the same Component-C data, both the C-DEC containment and the
witness-difference legality still hold (first two conjuncts) — but with
the batching challenge `γ = 0`, violating exactly the nonzeroness half of
`CommitmentBeforeGammaAndGammaNeZero`, the Component-C conditioned law is
NOT witness-independent: the fold contribution `γ^18 • c` vanishes, the
post-combination view degenerates to the witness word's own image, and the
two laws are distinct point masses (third conjunct).  So `γ ≠ 0` cannot be
dropped from the bundle. -/
theorem gammaNeZero_isLoadBearing :
    CDecAudit (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
        (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF ⊤
      ∧ (1 : ZMod 2) - 0 ∈ (⊤ : Submodule (ZMod 2) (ZMod 2))
      ∧ ((PMF.uniformOfFintype (LinearMap.ker
            (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2))).filter
            {c : LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) |
              (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)).domRestrict
                (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) c = 0}
            egSupp).map
            (componentCView 0 (rustRowOfMaps 0 egF) (⇑egF) 0 0)
        ≠ ((PMF.uniformOfFintype (LinearMap.ker
            (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2))).filter
            {c : LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) |
              (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)).domRestrict
                (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) c = 0}
            egSupp).map
            (componentCView 0 (rustRowOfMaps 0 egF) (⇑egF) 1 0) := by
  refine ⟨by simp [CDecAudit, LinearMap.ker_zero], Submodule.mem_top, ?_⟩
  intro hcontra
  have hconst : ∀ xC : ZMod 2,
      componentCView (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) (rustRowOfMaps 0 egF)
          (⇑egF) xC 0
        = fun _ => ((0 : Fin 76 → ZMod 2), egF xC) := by
    intro xC
    funext c
    simp only [componentCView,
      rustConditionedRows_eq_of_correspondence
        (rustRowOfMaps_correspondence 0 egF),
      LinearMap.zero_apply, zero_pow (by norm_num : (18 : ℕ) ≠ 0),
      zero_smul, add_zero]
  rw [hconst 0, hconst 1, map_const_eq_pure, map_const_eq_pure] at hcontra
  have hFne : egF (0 : ZMod 2) ≠ egF 1 := by
    intro hEq
    have h1 := congrFun hEq 0
    rw [map_zero] at h1
    rw [show egF (1 : ZMod 2) = Pi.single (0 : Fin 256) (1 : ZMod 2) from rfl,
      Pi.single_eq_same, Pi.zero_apply] at h1
    exact (by decide : ¬((0 : ZMod 2) = 1)) h1
  have hpairne : ((0 : Fin 76 → ZMod 2), egF (0 : ZMod 2))
      ≠ ((0 : Fin 76 → ZMod 2), egF 1) :=
    fun hEq => hFne (congrArg Prod.snd hEq)
  have h0 := congrArg
    (fun q : PMF ((Fin 76 → ZMod 2) × (Fin 256 → ZMod 2)) =>
      q ((0 : Fin 76 → ZMod 2), egF 0)) hcontra
  rw [PMF.pure_apply, PMF.pure_apply, if_pos rfl, if_neg hpairne] at h0
  exact one_ne_zero h0

end NonVacuityAndNegativeTests

/-! ## 7. Honesty ledger (final restatement)

* **Tier (i) — kernel facts proved in this file**: the conditional
  composition `conditional_complete_view_hiding`; the product/marginal
  lemmas; the correspondence-extraction and model-serializer lemmas; the
  non-vacuity instantiation; the two negative tests.  All check with
  axioms within `{propext, Classical.choice, Quot.sound}`.
* **Tier (ii) — cited external assumptions**: the circle/arity-4 FRI
  decoupling transport (`CircleArityFourFoldTransport`), whose intended
  discharge is the circle-code analogue of Haböck–Al Kindi,
  ePrint 2024/1037 (Protocol 2, Lemma 2, Theorems 4, 6) — not transported
  to the Aspis grammar here or anywhere in this repository.
* **Tier (iii) — computational assumptions modeled as perfect**:
  commitment binding (`PivotBoundByPreChallengeCommitment`) and
  Fiat–Shamir prefix-determined challenges
  (`CommitmentBeforeGammaAndGammaNeZero`).  No computational reduction or
  negligible-error accounting exists in this repository.
* **Tier (iv) — still-open code/model interfaces**: for the deployed
  artefacts, every one of `RustLeanRowCorrespondence332`,
  `SamplerUniformOnKerEll`, `DeployedTerminalMatchesModel`, the exact
  serialization equations, `CDecAudit`, the joint-sampler product
  structure, and the Component-B pivot/surjectivity facts (beyond the
  proved row-993 kernel fact of `V5InactiveClaimJointHiding`) remains an
  obligation.  This file discharges them only for the `ZMod 2` model.

Consequently: this file proves **conditional** complete-view hiding.  It
does not prove, and must not be cited as, "v5 is zero-knowledge". -/

/-! ## Axiom audit -/

#print axioms tripleProduct
#print axioms tripleProduct_map
#print axioms tripleProduct_map_fst
#print axioms map_const_eq_pure
#print axioms map_encode_congr
#print axioms componentAView
#print axioms componentBView
#print axioms rustConditionedRows
#print axioms componentCView
#print axioms completeView
#print axioms completeView_eq
#print axioms rustConditionedRows_eq_of_correspondence
#print axioms append_apply_pointwise
#print axioms rustRowOfMaps
#print axioms rustRowOfMaps_correspondence
#print axioms conditional_complete_view_hiding
#print axioms egF
#print axioms egSupp
#print axioms egJoint
#print axioms egView
#print axioms capstone_hypotheses_instantiable
#print axioms samplerA_uniformity_isLoadBearing
#print axioms gammaNeZero_isLoadBearing

end AspisV5ConditionalHidingCapstone
