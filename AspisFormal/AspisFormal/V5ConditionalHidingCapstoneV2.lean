import AspisFormal.V5RankOneOpeningHiding
import AspisFormal.V5InactiveClaimJointHiding
import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# The v5 CONDITIONAL complete-view hiding capstone, v2 (correlated Component B)

This file states and proves ONE theorem
(`conditional_complete_view_hiding_v2`): the released v5 complete view —
Component-A masked point-evaluations, the Component-B shared-pivot triple
(authenticated terminal opening, carried inactive claim, residual released
view, all three functionals of ONE uniform pivot scalar), and the
Component-C conditioned/post-combination coordinates — has a
witness-independent distribution, **conditional on an explicit bundle of
named hypotheses, every one of which is consumed by the proof**.

**What is new against the v1 capstone** (`V5ConditionalHidingCapstone`):
the Component-B leg is routed through the CORRELATED-invariant law
`AspisV5InactiveClaimJointHiding.sharedPivotView_pmf_indep` instead of the
pivot-freshness route.  The v1 capstone assumed the reserved pivot is fresh
for the residual view (`residualB kB = 0`) and drew a whole kernel vector;
this file draws ONE uniform pivot scalar, does **not** assume freshness,
and instead takes the exact correlation invariant as a named, load-bearing
deployed premise:

    hCarriedB :
      releasedB mB₁ - ((inactiveB kB)⁻¹ * inactiveB mB₁) • releasedB kB
        = releasedB mB₂ - ((inactiveB kB)⁻¹ * inactiveB mB₂) • releasedB kB

— the two witnesses' residual views must agree after subtracting each
witness's inactive-coordinate multiple of the pivot's residual direction.
The fresh configuration (`releasedB kB = 0`) is proved ONLY as a fenced
corollary (`conditional_complete_view_hiding_v2_fresh_corollary`): under
freshness the invariant collapses to residual-view equality, so the fresh
case is a special case, **never** the deployed result of this file.

**HARD FENCE — read before citing.**  This theorem does **not** say "v5 is
zero-knowledge", and nothing in this repository proves that.  What is
proved is an *implication*: IF the deployed system satisfies the named
interface hypotheses (commitment binding, commit-before-challenge ordering,
Rust↔Lean map correspondence, sampler uniformity, exact serialization,
nonzero lane/batching challenges, circle/arity-4 fold transport, C-DEC, the
pivot-kernel fact, the correlated invariant `hCarriedB`, and independence
of the three mask sources), THEN the modeled complete-view distribution
carries no witness information.  Deployed applicability is STILL BLOCKED,
prominently, by

* **(a) the correlated-invariant CORRESPONDENCE**: no theorem anywhere in
  this repository shows that the deployed released view — the actual
  Component-B lane layout the Rust prover serializes — satisfies
  `hCarriedB` for the witness pairs the protocol quantifies over.  It is a
  named open interface (`UnmetDeployment.DeployedCarriedInvariantCorrespondence`
  below), not a discharged fact; and
* **(b) the NONEXISTENT Component-C deployed map/certificate**: there is no
  kernel-checked identification of the deployed Component-C serializer
  rows and fold pipeline with the Lean maps `E`/`F`
  (`RustLeanRowCorrespondence332`, `CircleArityFourFoldTransport`), and no
  C-DEC certificate (`CDecAudit`) for the deployed matrices.  The C leg of
  this capstone consumes those as hypotheses; nothing here or elsewhere in
  the repository discharges them for the deployed artefacts.

## The four honesty tiers

1. **Kernel facts proved here** (machine-checked, axioms ⊆
   `{propext, Classical.choice, Quot.sound}`): the composition theorem
   `conditional_complete_view_hiding_v2`; the product-pushforward lemma
   `tripleProduct_map`; the data-processing lemma `map_encode_congr`; the
   row-extraction lemma `rustConditionedRows_eq_of_correspondence`; the
   satisfiability witness `rustRowOfMaps_correspondence`; the fresh-case
   implication `carried_invariant_of_freshB` and its fenced corollary; the
   non-vacuity instantiation `capstone_v2_hypotheses_instantiable` (which
   is provably OUT of reach of the fresh route: `capstone_v2_beyond_fresh`);
   and the two premise-deletion negative tests.
2. **Cited external assumptions** (mathematics believed on citation, not
   re-proved here): the circle/arity-4 FRI decoupling transport enters only
   as the named hypothesis `CircleArityFourFoldTransport` — the intended
   discharge is the circle-code analogue of Haböck–Al Kindi,
   ePrint 2024/1037 (Protocol 2, Lemma 2, Theorems 4 and 6), stated there
   for binary univariate Reed–Solomon FRI and **not** transported to the
   Aspis circle/arity-4 grammar.
3. **Computational assumptions** (true only against bounded adversaries,
   modeled here as perfect): `PivotBoundByPreChallengeCommitment` models a
   *computationally* binding commitment as perfectly binding, and
   `CommitmentBeforeGammaAndGammaNeZero` models Fiat–Shamir challenge
   derivation as a function of the transcript prefix.  No computational
   reduction with negligible-error accounting exists in this repository.
4. **Still-open code/model interfaces** (named `Prop`s consumed as
   hypotheses, discharged here only for the `ZMod 2` toy model, never for
   the deployed artefacts): the correlated-invariant correspondence
   `hCarriedB` for the deployed lane layout (blocker (a) above);
   `RustLeanRowCorrespondence332`, `CircleArityFourFoldTransport` and
   `CDecAudit` for the deployed Component-C maps (blocker (b) above);
   `SamplerUniformOnKerEll` and the A/B sampler-uniformity equations for
   the deployed samplers; `DeployedTerminalMatchesModel` for the deployed
   terminal evaluator; the exact-serialization equations `hserialize₁/₂`
   for the deployed byte stream; the independence/product structure
   `hindependent` for the deployed joint sampler; and the lane-coefficient
   interface `PivotCoefficientIsGammaB` beyond the row-993 kernel fact
   already proved in `V5InactiveClaimJointHiding`.

Until every tier-4 interface is discharged against the real artefacts and
the tier-2/3 assumptions are either proved or explicitly carried, the
honest summary remains: **v5 complete-view hiding is kernel-checked but
CONDITIONAL, and v5 is not proven zero-knowledge.**
-/

open scoped ENNReal

namespace AspisV5ConditionalHidingCapstoneV2

open AspisV5RankOneOpeningHiding AspisV5InactiveClaimJointHiding
  AspisV5ComponentCConditionalDecoupling
  AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces

/-! ## 1. Product plumbing: independent triples of samplers

The three components draw from three mask sources: the Component-A mask
space, the ONE Component-B pivot scalar, and the conditioned Component-C
kernel fibre.  That they are *independent* is NOT assumed silently: the
capstone takes the explicit named hypothesis
`hindependent : jointSampler = tripleProduct …`, and the lemmas here are
what consume it. -/

section ProductPlumbing

variable {α β γ α' β' γ' : Type*}

/-- The independent product of three samplers: draw each coordinate from
its own `PMF`, with no coordinate reading another's sample. -/
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

/-- Mapping any sampler through a constant function gives the point mass:
`PMF.map_const` with the constant spelled as a lambda.  Used by the
negative tests to compute the degenerate view laws that witness failure. -/
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

The view functions are written in terms of the *deployed* maps — the
deployed terminal evaluator, the deployed serializer rows, the deployed
fold pipeline — so that the Rust↔Lean correspondence hypotheses are forced
to do real work in the proof.  The Component-B view is the v2 change: ONE
uniform pivot scalar `p` scales the reserved pivot direction `kB`, and the
terminal opening, the carried inactive claim and the residual released
view are all evaluated at the same masked witness `mB + p • kB` — exactly
`AspisV5InactiveClaimJointHiding.sharedPivotView` after the deployed
terminal evaluator is identified with the model functional. -/

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

/-- Component-B released view, v2 deployed spelling: ONE pivot scalar `p`
scales the reserved pivot direction `kB`, and the authenticated terminal
opening (evaluated by the *deployed* terminal evaluator), the carried
inactive-claim coordinate, and the residual released view are all three
evaluated at the same masked witness `mB + p • kB`.  Nothing is padded
independently; every correlation between the three coordinates through the
shared scalar is retained. -/
def componentBViewV2 {MB VB : Type*} [AddCommGroup MB] [Module K MB]
    [AddCommGroup VB] [Module K VB]
    (deployedTerminalB : MB → K) (inactiveB : MB →ₗ[K] K)
    (releasedB : MB →ₗ[K] VB) (kB mB : MB) :
    K → K × K × VB :=
  fun p => (deployedTerminalB (mB + p • kB), inactiveB (mB + p • kB),
    releasedB (mB + p • kB))

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
reading its own coordinate of the three-part mask sample
`(r, p, c) : MA × K × LinearMap.ker ell`. -/
def completeViewV2 {MA VA MB VB MC : Type*}
    [AddCommGroup MA] [Module K MA] [AddCommGroup VA] [Module K VA]
    [AddCommGroup MB] [Module K MB] [AddCommGroup VB] [Module K VB]
    [AddCommGroup MC] [Module K MC]
    (LA : MA →ₗ[K] VA) (wA : VA)
    (deployedTerminalB : MB → K) (inactiveB : MB →ₗ[K] K)
    (releasedB : MB →ₗ[K] VB) (kB mB : MB)
    (ell : MC →ₗ[K] K) (rustRow : Fin 332 → MC →ₗ[K] K)
    (concreteFold : MC → Fin 256 → K) (xC : MC) (γ : K) :
    MA × K × LinearMap.ker ell → CompleteViewType K VA VB :=
  fun s => (componentAView LA wA s.1,
    componentBViewV2 deployedTerminalB inactiveB releasedB kB mB s.2.1,
    componentCView ell rustRow concreteFold xC γ s.2.2)

/-- `completeViewV2` unfolded to the componentwise-product shape consumed
by `tripleProduct_map`. -/
theorem completeViewV2_eq {MA VA MB VB MC : Type*}
    [AddCommGroup MA] [Module K MA] [AddCommGroup VA] [Module K VA]
    [AddCommGroup MB] [Module K MB] [AddCommGroup VB] [Module K VB]
    [AddCommGroup MC] [Module K MC]
    (LA : MA →ₗ[K] VA) (wA : VA)
    (deployedTerminalB : MB → K) (inactiveB : MB →ₗ[K] K)
    (releasedB : MB →ₗ[K] VB) (kB mB : MB)
    (ell : MC →ₗ[K] K) (rustRow : Fin 332 → MC →ₗ[K] K)
    (concreteFold : MC → Fin 256 → K) (xC : MC) (γ : K) :
    completeViewV2 LA wA deployedTerminalB inactiveB releasedB kB mB
        ell rustRow concreteFold xC γ
      = fun s : MA × K × LinearMap.ker ell =>
          (componentAView LA wA s.1,
            componentBViewV2 deployedTerminalB inactiveB releasedB kB mB
              s.2.1,
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

/-! ## 4. The capstone theorem (v2) -/

section Capstone

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  {MA VA : Type*} [AddCommGroup MA] [Module K MA] [Fintype MA] [Nonempty MA]
  [AddCommGroup VA] [Module K VA] [FiniteDimensional K VA]
  {MB VB : Type*} [AddCommGroup MB] [Module K MB]
  [AddCommGroup VB] [Module K VB]
  {MC : Type*} [AddCommGroup MC] [Module K MC] [Fintype MC]
  {CommitmentB Transcript TranscriptPrefix Bytes : Type*}

/-- **The v5 CONDITIONAL complete-view hiding capstone, v2.**

One-line reading: *given* commitment binding, commit-before-challenge
ordering, Rust↔Lean map correspondence, sampler uniformity, exact
serialization, the nonzero lane and batching challenges, the
circle/arity-4 fold transport, C-DEC, the pivot-kernel fact, the
CORRELATED INVARIANT `hCarriedB`, and independence of the three mask
sources, the released complete-view byte stream has exactly the same
distribution for the two witness runs.

The v2 delta: the Component-B leg is
`AspisV5InactiveClaimJointHiding.sharedPivotView_pmf_indep` — the
general correlated form of the shared-pivot joint law.  Pivot freshness
(`releasedB kB = 0`) is NOT assumed; a correlated pivot that the residual
view reads is allowed, and the exact correlation invariant is the named
premise `hCarriedB` instead.

Where each named hypothesis is consumed (none is decorative):

* `hbinding` + `hsharedCommit` (PCS/commitment binding): produce
  `terminalB mB₂ = terminalB mB₁`, the second fibre condition `h₂` of
  `sharedPivotView_pmf_indep` — the shared released commitment is what
  forces the two runs onto the same authenticated terminal fibre.
* `hordering` + `hsharedPrefix` (commit-before-challenge ordering): the
  prefix-determinism half collapses the two runs' batching challenges
  (`gammaOf t₂ = gammaOf t₁`), without which the two Component-C views use
  different folds and the C theorem cannot be applied; the nonzeroness
  half supplies `hγ` to the C decoupling theorem.
* `hrow` (Rust↔Lean row correspondence): rewrites the deployed serializer
  rows `rustConditionedRows rustRow` into the Lean map `E`
  (`rustConditionedRows_eq_of_correspondence`); without it the deployed
  view has no linear structure.
* `hterminal` (deployed-terminal correspondence): rewrites the deployed
  terminal evaluator into the Lean functional `terminalB` inside the
  Component-B view, which is what identifies `componentBViewV2` with
  `sharedPivotView terminalB inactiveB releasedB kB mB`.
* `hsamplerA`, `hsamplerB`, `hsamplerC` (sampler uniformity on the mask
  space / the pivot-scalar line `K` / `ker ℓ`): substituted into the joint
  law; the component hiding theorems are about the uniform laws and
  nothing else.
* `hindependent` (independence/product structure): substitutes the joint
  sampler by `tripleProduct`, after which `tripleProduct_map` factors the
  complete-view law into the three component laws.  The three views do
  **not** silently factor: this hypothesis is the only reason they do.
* `hserialize₁/₂` (exact serialization): substitute the byte functions by
  `encode ∘ completeViewV2`, consumed by the data-processing lemma
  `map_encode_congr`; they assert the released bytes are a function of
  exactly the modeled coordinates (no extra mask-dependent leak).
* `hlane` + `hgammaB` (lane coefficient, `gammaB ≠ 0`): discharge
  `inactiveB kB ≠ 0` via `pivot_inactive_nonzero_of_gammaB` — the nonzero
  pivot coefficient `hgamma` of `sharedPivotView_pmf_indep`, the scalar
  one-time pad on the carried inactive claim.
* `htransport` (circle/arity-4 FRI transport, cited external): rewrites
  the deployed fold pipeline into the Lean map `F` inside the Component-C
  view.
* `hA_surj`: the surjectivity premise of Component A's
  `released_view_pmf_indep`.
* `hB_pivot_ker`: the pivot-kernel premise `hk` of
  `sharedPivotView_pmf_indep` (for the transcribed deployed covector this
  is the proved row-993 fact `terminalDotFunctional_pivot_eq_zero`; here
  it stays a named hypothesis of the abstract layout).
* `hCarriedB` (**the v2 premise**): the correlation invariant
  `releasedB mB - ((inactiveB kB)⁻¹ * inactiveB mB) • releasedB kB` agrees
  for the two witnesses.  It is fed verbatim to
  `sharedPivotView_pmf_indep` as its `hcarried` premise; the exact joint
  law `sharedPivotView_law` shows the witness enters the B law through
  this invariant and nothing else, so without it the B laws genuinely
  differ (negative test `carriedInvariantB_isLoadBearing`).  Whether the
  DEPLOYED released view satisfies it is open — see the module docstring,
  blocker (a).
* `hCdec` + `hlegal`: the C-DEC containment and witness-difference
  legality premises of Component C's
  `componentC_full_fold_conditional_decoupling_complete_view`.
* `hsupp`: the conditioning event `E = e` is charged by the C sampler; it
  is the well-definedness argument of the `PMF.filter` conditioning and
  yields the nonemptiness of the conditioned fibre.

**This is a conditional statement.**  It does not prove v5 zero-knowledge;
see the module docstring for the four-tier honesty ledger and the two
prominent deployment blockers. -/
theorem conditional_complete_view_hiding_v2
    -- released-view data
    (LA : MA →ₗ[K] VA) (wA₁ wA₂ : VA)
    (terminalB inactiveB : MB →ₗ[K] K) (releasedB : MB →ₗ[K] VB)
    (deployedTerminalB : MB → K) (kB mB₁ mB₂ : MB) (gammaB : K)
    (commitB : MB → CommitmentB)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] Fin 76 → K) (F : MC →ₗ[K] Fin 256 → K)
    (Δw : Submodule K MC) (xC₁ xC₂ : MC) (e : Fin 76 → K)
    (rustRow : Fin 332 → MC →ₗ[K] K) (concreteFold : MC → Fin 256 → K)
    (commitPrefixC : Transcript → TranscriptPrefix) (gammaOf : Transcript → K)
    (t₁ t₂ : Transcript)
    -- sampler and serialization data
    (samplerA : PMF MA) (samplerB : PMF K)
    (samplerCKer : PMF (LinearMap.ker ell))
    (hsupp : ∃ c ∈ {c : LinearMap.ker ell |
        E.domRestrict (LinearMap.ker ell) c = e}, c ∈ samplerCKer.support)
    (jointSampler : PMF (MA × K × LinearMap.ker ell))
    (encode : CompleteViewType K VA VB → Bytes)
    (releasedBytes₁ releasedBytes₂ : MA × K × LinearMap.ker ell → Bytes)
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
    (hsamplerB : samplerB = PMF.uniformOfFintype K)
    (hsamplerC : SamplerUniformOnKerEll ell samplerCKer)
    -- (H5) independence/product structure of the three mask sources
    (hindependent : jointSampler
      = tripleProduct samplerA samplerB
          (samplerCKer.filter
            {c : LinearMap.ker ell |
              E.domRestrict (LinearMap.ker ell) c = e} hsupp))
    -- (H6) exact serialization
    (hserialize₁ : releasedBytes₁ = fun s => encode
      (completeViewV2 LA wA₁ deployedTerminalB inactiveB releasedB kB mB₁
        ell rustRow concreteFold xC₁ (gammaOf t₁) s))
    (hserialize₂ : releasedBytes₂ = fun s => encode
      (completeViewV2 LA wA₂ deployedTerminalB inactiveB releasedB kB mB₂
        ell rustRow concreteFold xC₂ (gammaOf t₂) s))
    -- (H7) lane coefficient and gammaB ≠ 0
    (hlane : PivotCoefficientIsGammaB inactiveB kB gammaB)
    (hgammaB : gammaB ≠ 0)
    -- (H8) circle/arity-4 FRI transport (cited external; see module docstring)
    (htransport : CircleArityFourFoldTransport concreteFold F)
    -- (H9) component-internal irreducible edges
    (hA_surj : Function.Surjective LA)
    (hB_pivot_ker : terminalB kB = 0)
    -- ★ the v2 premise: the CORRELATED INVARIANT, replacing pivot freshness
    (hCarriedB : releasedB mB₁
        - ((inactiveB kB)⁻¹ * inactiveB mB₁) • releasedB kB
      = releasedB mB₂
        - ((inactiveB kB)⁻¹ * inactiveB mB₂) • releasedB kB)
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
  -- Component B, v2: the deployed view is the shared-pivot view (uses
  -- hterminal); its law equality is the CORRELATED-invariant theorem
  -- (uses hB_pivot_ker, hpivot_inactive, hsharedTerminal, hCarriedB).
  have hBview : ∀ mB : MB,
      componentBViewV2 deployedTerminalB inactiveB releasedB kB mB
        = sharedPivotView terminalB inactiveB releasedB kB mB := by
    intro mB
    funext p
    simp only [componentBViewV2, sharedPivotView, hterminal']
  have hBlaw : (PMF.uniformOfFintype K).map
        (componentBViewV2 deployedTerminalB inactiveB releasedB kB mB₁)
      = (PMF.uniformOfFintype K).map
        (componentBViewV2 deployedTerminalB inactiveB releasedB kB mB₂) := by
    rw [hBview mB₁, hBview mB₂]
    exact sharedPivotView_pmf_indep terminalB inactiveB releasedB kB
      (terminalB mB₁) mB₁ mB₂ hB_pivot_ker hpivot_inactive rfl
      hsharedTerminal hCarriedB
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
  rw [completeViewV2_eq, completeViewV2_eq,
    tripleProduct_map (PMF.uniformOfFintype MA)
      (PMF.uniformOfFintype K)
      ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell |
          E.domRestrict (LinearMap.ker ell) c = e} hsupp)
      (componentAView LA wA₁)
      (componentBViewV2 deployedTerminalB inactiveB releasedB kB mB₁)
      (componentCView ell rustRow concreteFold xC₁ (gammaOf t₁)),
    tripleProduct_map (PMF.uniformOfFintype MA)
      (PMF.uniformOfFintype K)
      ((PMF.uniformOfFintype (LinearMap.ker ell)).filter
        {c : LinearMap.ker ell |
          E.domRestrict (LinearMap.ker ell) c = e} hsupp)
      (componentAView LA wA₂)
      (componentBViewV2 deployedTerminalB inactiveB releasedB kB mB₂)
      (componentCView ell rustRow concreteFold xC₂ (gammaOf t₂)),
    hAlaw, hBlaw, hClaw]

/-! ## 5. The FRESH case, as a fenced corollary ONLY

The v1 route assumed the pivot is fresh for the residual view
(`releasedB kB = 0`).  Under freshness the correlation invariant collapses
to the residual view itself, so the fresh configuration is a *special
case* of the v2 capstone — proved here as a corollary and fenced as such.
Neither statement in this subsection is the deployed result of this file:
the deployed premise of the v2 capstone is `hCarriedB`, and whether the
deployed lane layout satisfies either `hCarriedB` or freshness is open
(module docstring, blocker (a)). -/

omit [Fintype K] [DecidableEq K] in
/-- **Freshness implies the correlated invariant.**  If the pivot is fresh
for the residual view (`releasedB kB = 0`) and the two witnesses agree on
the residual released view, the correlation invariant `hCarriedB` holds:
both correction terms vanish.  This is the exact sense in which the v1
pivot-freshness route is a special case of the v2 correlated route. -/
theorem carried_invariant_of_freshB
    (inactiveB : MB →ₗ[K] K) (releasedB : MB →ₗ[K] VB) (kB mB₁ mB₂ : MB)
    (hfresh : releasedB kB = 0)
    (hreleasedEq : releasedB mB₁ = releasedB mB₂) :
    releasedB mB₁ - ((inactiveB kB)⁻¹ * inactiveB mB₁) • releasedB kB
      = releasedB mB₂ - ((inactiveB kB)⁻¹ * inactiveB mB₂) • releasedB kB := by
  rw [hfresh, smul_zero, smul_zero, sub_zero, sub_zero, hreleasedEq]

/-- **FRESH-PIVOT COROLLARY — NOT the deployed result of this file.**  The
v2 capstone specialised to a fresh pivot: `releasedB kB = 0` together with
residual-view agreement `releasedB mB₁ = releasedB mB₂` implies the
correlated invariant (`carried_invariant_of_freshB`), so the conclusion
follows from `conditional_complete_view_hiding_v2`.  This corollary exists
to certify, inside the kernel, that the v2 premise strictly generalises
the v1 freshness premise.  Do not cite it as the capstone: the deployed
premise is `hCarriedB`, and the non-vacuity instantiation below
(`capstone_v2_hypotheses_instantiable`) is provably outside this
corollary's reach (`capstone_v2_beyond_fresh`). -/
theorem conditional_complete_view_hiding_v2_fresh_corollary
    (LA : MA →ₗ[K] VA) (wA₁ wA₂ : VA)
    (terminalB inactiveB : MB →ₗ[K] K) (releasedB : MB →ₗ[K] VB)
    (deployedTerminalB : MB → K) (kB mB₁ mB₂ : MB) (gammaB : K)
    (commitB : MB → CommitmentB)
    (ell : MC →ₗ[K] K) (E : MC →ₗ[K] Fin 76 → K) (F : MC →ₗ[K] Fin 256 → K)
    (Δw : Submodule K MC) (xC₁ xC₂ : MC) (e : Fin 76 → K)
    (rustRow : Fin 332 → MC →ₗ[K] K) (concreteFold : MC → Fin 256 → K)
    (commitPrefixC : Transcript → TranscriptPrefix) (gammaOf : Transcript → K)
    (t₁ t₂ : Transcript)
    (samplerA : PMF MA) (samplerB : PMF K)
    (samplerCKer : PMF (LinearMap.ker ell))
    (hsupp : ∃ c ∈ {c : LinearMap.ker ell |
        E.domRestrict (LinearMap.ker ell) c = e}, c ∈ samplerCKer.support)
    (jointSampler : PMF (MA × K × LinearMap.ker ell))
    (encode : CompleteViewType K VA VB → Bytes)
    (releasedBytes₁ releasedBytes₂ : MA × K × LinearMap.ker ell → Bytes)
    (hbinding : PivotBoundByPreChallengeCommitment commitB (⇑terminalB))
    (hsharedCommit : commitB mB₁ = commitB mB₂)
    (hordering : CommitmentBeforeGammaAndGammaNeZero commitPrefixC gammaOf)
    (hsharedPrefix : commitPrefixC t₁ = commitPrefixC t₂)
    (hrow : RustLeanRowCorrespondence332 rustRow E F)
    (hterminal : DeployedTerminalMatchesModel deployedTerminalB terminalB)
    (hsamplerA : samplerA = PMF.uniformOfFintype MA)
    (hsamplerB : samplerB = PMF.uniformOfFintype K)
    (hsamplerC : SamplerUniformOnKerEll ell samplerCKer)
    (hindependent : jointSampler
      = tripleProduct samplerA samplerB
          (samplerCKer.filter
            {c : LinearMap.ker ell |
              E.domRestrict (LinearMap.ker ell) c = e} hsupp))
    (hserialize₁ : releasedBytes₁ = fun s => encode
      (completeViewV2 LA wA₁ deployedTerminalB inactiveB releasedB kB mB₁
        ell rustRow concreteFold xC₁ (gammaOf t₁) s))
    (hserialize₂ : releasedBytes₂ = fun s => encode
      (completeViewV2 LA wA₂ deployedTerminalB inactiveB releasedB kB mB₂
        ell rustRow concreteFold xC₂ (gammaOf t₂) s))
    (hlane : PivotCoefficientIsGammaB inactiveB kB gammaB)
    (hgammaB : gammaB ≠ 0)
    (htransport : CircleArityFourFoldTransport concreteFold F)
    (hA_surj : Function.Surjective LA)
    (hB_pivot_ker : terminalB kB = 0)
    -- the FRESH premises, replacing hCarriedB in this corollary only
    (hB_fresh : releasedB kB = 0)
    (hB_releasedEq : releasedB mB₁ = releasedB mB₂)
    (hCdec : CDecAudit ell E F Δw)
    (hlegal : xC₂ - xC₁ ∈ Δw) :
    jointSampler.map releasedBytes₁ = jointSampler.map releasedBytes₂ :=
  conditional_complete_view_hiding_v2 LA wA₁ wA₂ terminalB inactiveB
    releasedB deployedTerminalB kB mB₁ mB₂ gammaB commitB ell E F Δw xC₁
    xC₂ e rustRow concreteFold commitPrefixC gammaOf t₁ t₂ samplerA
    samplerB samplerCKer hsupp jointSampler encode releasedBytes₁
    releasedBytes₂ hbinding hsharedCommit hordering hsharedPrefix hrow
    hterminal hsamplerA hsamplerB hsamplerC hindependent hserialize₁
    hserialize₂ hlane hgammaB htransport hA_surj hB_pivot_ker
    (carried_invariant_of_freshB inactiveB releasedB kB mB₁ mB₂ hB_fresh
      hB_releasedEq)
    hCdec hlegal

end Capstone

/-! ## 6. Non-vacuity: the whole v2 hypothesis bundle is satisfiable

A concrete finite instantiation over `ZMod 2`.  Component A is the
identity on a one-dimensional mask space; Component C is the
one-dimensional word space embedded in coordinate `0` of the 256
post-combination coordinates, with nothing conditioned (`E = 0`) and the
model serializer `rustRowOfMaps`.  Component B is the `Fin 3` projection
model with pivot `![0, 1, 1]` — a pivot the residual view READS
(`releasedB kB = 1 ≠ 0`), so the fresh route does not apply — and
witnesses `![0, 0, 0]` and `![0, 1, 1]`, which differ in BOTH the inactive
claim and the residual coordinate but share the correlation invariant
`m 2 - m 1 = 0`.  Every named hypothesis of the v2 capstone is discharged,
so the capstone is not vacuously true, and it is discharged on data the
fresh corollary provably cannot reach (`capstone_v2_beyond_fresh`). -/

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

/-- The example joint sampler: the independent triple of the uniform
Component-A mask, the uniform Component-B pivot scalar, and the
conditioned uniform Component-C kernel fibre. -/
noncomputable def egJointV2 :
    PMF (ZMod 2 × ZMod 2 ×
      LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) :=
  tripleProduct (PMF.uniformOfFintype (ZMod 2))
    (PMF.uniformOfFintype (ZMod 2))
    ((PMF.uniformOfFintype
      (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2))).filter
      {c : LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) |
        (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)).domRestrict
          (LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)) c = 0} egSupp)

/-- The example complete view of one run, parameterised by the pivot
direction `kB` and the Component-B witness `mB` so that the negative
tests below can vary exactly one premise at a time (batching challenge
fixed at the example's `gammaOf () = 1`). -/
def egViewV2 (wA : ZMod 2) (kB mB : Fin 3 → ZMod 2) (xC : ZMod 2) :
    ZMod 2 × ZMod 2 × LinearMap.ker (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2) →
      CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2) :=
  completeViewV2 (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) wA
    (⇑(LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) kB mB
    (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
    (rustRowOfMaps (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF)
    (⇑egF) xC 1

/-- The example lane fact: the carried claim reads the pivot `![0, 1, 1]`
with coefficient exactly `gammaB = 1`. -/
theorem egLaneCoefficient :
    PivotCoefficientIsGammaB
      (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      ![0, 1, 1] 1 :=
  rfl

/-- The example CORRELATED invariant: for the correlated pivot
`![0, 1, 1]` (which the residual view reads with coefficient `1`), the
witnesses `![0, 0, 0]` and `![0, 1, 1]` have the same invariant
`m 2 - m 1`: `0 - 0 = 1 - 1`.  This is the `hCarriedB` instance consumed
by the non-vacuity theorem. -/
theorem egCarriedInvariant :
    (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 0]
        - (((LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 1, 1])⁻¹
            * (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 0, 0])
          • (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
            ![0, 1, 1]
      = (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 1, 1]
        - (((LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 1, 1])⁻¹
            * (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 1, 1])
          • (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
            ![0, 1, 1] := by
  show (0 : ZMod 2) - ((1 : ZMod 2)⁻¹ * 0) • (1 : ZMod 2)
      = 1 - ((1 : ZMod 2)⁻¹ * 1) • 1
  simp

/-- **Non-vacuity of the v2 capstone.**  Every named hypothesis of
`conditional_complete_view_hiding_v2` is discharged for the concrete
`ZMod 2` data, with the two runs differing in the Component-A witness
(`wA₁` vs `wA₂`), the Component-B witness (`![0, 0, 0]` vs `![0, 1, 1]`,
differing in BOTH the inactive claim and the residual coordinate, on the
shared terminal fibre, with matching correlation invariant), and the
Component-C witness word (`0` vs `1`, a legal difference).  The pivot is
`![0, 1, 1]`, which the residual view READS — the fresh route is
inapplicable to this instantiation (`capstone_v2_beyond_fresh`).  The
capstone conclusion holds for it: the theorem is not vacuously true. -/
theorem capstone_v2_hypotheses_instantiable (wA₁ wA₂ : ZMod 2) :
    egJointV2.map (egViewV2 wA₁ ![0, 1, 1] ![0, 0, 0] 0)
      = egJointV2.map (egViewV2 wA₂ ![0, 1, 1] ![0, 1, 1] 1) :=
  conditional_complete_view_hiding_v2
    (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2) wA₁ wA₂
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (⇑(LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    ![0, 1, 1] ![0, 0, 0] ![0, 1, 1] 1
    (fun m => m 0)
    (0 : ZMod 2 →ₗ[ZMod 2] ZMod 2)
    (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF ⊤ 0 1 0
    (rustRowOfMaps (0 : ZMod 2 →ₗ[ZMod 2] (Fin 76 → ZMod 2)) egF) (⇑egF)
    (fun _ => ()) (fun _ => 1) () ()
    (PMF.uniformOfFintype (ZMod 2))
    (PMF.uniformOfFintype (ZMod 2))
    (PMF.uniformOfFintype _)
    egSupp
    egJointV2
    id
    (egViewV2 wA₁ ![0, 1, 1] ![0, 0, 0] 0)
    (egViewV2 wA₂ ![0, 1, 1] ![0, 1, 1] 1)
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
    -- (H7) lane coefficient (pivot ![0,1,1] read with gammaB = 1) and
    -- gammaB ≠ 0.
    egLaneCoefficient
    one_ne_zero
    -- (H8) fold transport: the model fold is `egF` itself.
    (fun _ => rfl)
    -- (H9) component-internal edges.
    (fun x => ⟨x, rfl⟩)
    rfl
    -- ★ the correlated invariant hCarriedB, discharged for the example.
    egCarriedInvariant
    (by simp [CDecAudit, LinearMap.ker_zero])
    Submodule.mem_top

/-- **The non-vacuity instantiation is OUT of reach of the fresh route.**
Both fresh-corollary premises fail for the example data: the pivot
`![0, 1, 1]` is NOT fresh for the residual view (`releasedB kB = 1 ≠ 0`),
and the two witnesses do NOT agree on the residual released view
(`0 ≠ 1`).  So `capstone_v2_hypotheses_instantiable` genuinely exercises
the correlated v2 route, not the v1 freshness special case. -/
theorem capstone_v2_beyond_fresh :
    (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 1, 1] ≠ 0
      ∧ (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 0]
        ≠ (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
          ![0, 1, 1] :=
  ⟨one_ne_zero, by decide⟩

/-! ## 7. Load-bearing negative tests

Two premises of the v2 Component-B leg are removed, one at a time, and
the capstone conclusion is shown to be **false** for the removed-premise
instantiation while the surrounding data still satisfies the rest of the
bundle (the A/C data, samplers, serialization and ordering are identical
to `capstone_v2_hypotheses_instantiable`; the conjuncts of each test
kernel-check the B-local premises that continue to hold).  This is the
proof that the v2 bundle contains no decorative premise of these kinds:
the route genuinely breaks without them. -/

/-- **Negative test 1: the correlated invariant `hCarriedB` is
load-bearing.**  Identical data to `capstone_v2_hypotheses_instantiable`
— same pivot `![0, 1, 1]`, same first witness, same A/C data and samplers
— except the second Component-B witness is `![0, 0, 1]`, chosen so that
exactly `hCarriedB` fails (the invariants are `0 - 0 = 0` and
`1 - 0 = 1`) while the pivot-kernel fact, the nonzero pivot coefficient,
the shared commitment/terminal fibre, and every non-B premise continue to
hold.  The capstone conclusion is then FALSE: the released residual
coordinate minus the released inactive coordinate is the deterministic
invariant `m 2 - m 1` (the shared pivot scalar cancels), so it reveals
`0` for the first witness and `1` for the second, and the two
complete-view laws map to distinct point masses.  So `hCarriedB` cannot
be dropped from the bundle. -/
theorem carriedInvariantB_isLoadBearing :
    -- the other B-local premises still hold for the pair:
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 1, 1] = 0
    ∧ (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 1, 1] ≠ 0
    ∧ (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 0]
        = (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 1]
    -- the DELETED premise hCarriedB is false for the pair:
    ∧ ¬((LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 0]
          - (((LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 1, 1])⁻¹
              * (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 0, 0])
            • (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 1, 1]
        = (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 1]
          - (((LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 1, 1])⁻¹
              * (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 0, 1])
            • (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 1, 1])
    -- and the capstone conclusion is FALSE:
    ∧ egJointV2.map (egViewV2 0 ![0, 1, 1] ![0, 0, 0] 0)
        ≠ egJointV2.map (egViewV2 0 ![0, 1, 1] ![0, 0, 1] 0) := by
  refine ⟨rfl, one_ne_zero, rfl, ?_, ?_⟩
  · show ¬((0 : ZMod 2) - ((1 : ZMod 2)⁻¹ * 0) • (1 : ZMod 2)
        = 1 - ((1 : ZMod 2)⁻¹ * 0) • (1 : ZMod 2))
    simp
  · intro hcontra
    -- the residual-minus-inactive discriminator is the deterministic
    -- correlation invariant m 2 - m 1: the shared pivot scalar cancels.
    have hlaw : ∀ mB : Fin 3 → ZMod 2,
        (egJointV2.map (egViewV2 0 ![0, 1, 1] mB 0)).map
            (fun v : CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2) =>
              v.2.1.2.2 - v.2.1.2.1)
          = PMF.pure (mB 2 - mB 1) := by
      intro mB
      have hfun : ((fun v : CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2) =>
            v.2.1.2.2 - v.2.1.2.1) ∘ egViewV2 0 ![0, 1, 1] mB 0)
          = fun _ => mB 2 - mB 1 := by
        funext s
        show mB 2 + s.2.1 * 1 - (mB 1 + s.2.1 * 1) = mB 2 - mB 1
        ring
      rw [PMF.map_comp, hfun, map_const_eq_pure]
    have hpp := (hlaw ![0, 0, 0]).symm.trans
      ((congrArg
          (fun q : PMF (CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2)) =>
            q.map fun v => v.2.1.2.2 - v.2.1.2.1) hcontra).trans
        (hlaw ![0, 0, 1]))
    have h0 := congrArg (fun q : PMF (ZMod 2) => q 0) hpp
    rw [PMF.pure_apply, PMF.pure_apply, if_pos (by decide),
      if_neg (by decide)] at h0
    exact one_ne_zero h0

/-- **Negative test 2: the nonzero pivot coefficient (`γ ≠ 0`, i.e.
`inactiveB kB ≠ 0`, deployed name `gammaB`) is load-bearing.**  The pivot
is replaced by `![0, 0, 1]`, which still lies in the terminal kernel, and
the witnesses `![0, 0, 0]` and `![0, 1, 0]` still share the terminal
fibre AND still satisfy the correlated invariant `hCarriedB` (both sides
reduce to `0` because `(0 : ZMod 2)⁻¹ = 0`) — but the pivot's inactive
coefficient is `0`, violating exactly the `γ ≠ 0` premise that
`hlane + hgammaB` discharge.  The capstone conclusion is then FALSE: with
no pivot pad on the inactive coordinate, the carried inactive claim is
released in the clear (`0` vs `1`), and the two complete-view laws map to
distinct point masses.  So `γ ≠ 0` cannot be dropped from the bundle,
even keeping `hCarriedB`. -/
theorem pivotGammaB_nonzero_isLoadBearing :
    -- the pivot is still in the terminal kernel, the fibre is shared:
    (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 1] = 0
    ∧ (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 0]
        = (LinearMap.proj 0 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 1, 0]
    -- the DELETED premise: the pivot's inactive coefficient is zero:
    ∧ (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 1] = 0
    -- hCarriedB still HOLDS for the pair (deletion isolated to γ ≠ 0):
    ∧ ((LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 0, 0]
          - (((LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 0, 1])⁻¹
              * (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 0, 0])
            • (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 0, 1]
        = (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) ![0, 1, 0]
          - (((LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 0, 1])⁻¹
              * (LinearMap.proj 1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
                ![0, 1, 0])
            • (LinearMap.proj 2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
              ![0, 0, 1])
    -- and the capstone conclusion is FALSE:
    ∧ egJointV2.map (egViewV2 0 ![0, 0, 1] ![0, 0, 0] 0)
        ≠ egJointV2.map (egViewV2 0 ![0, 0, 1] ![0, 1, 0] 0) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · show (0 : ZMod 2) - ((0 : ZMod 2)⁻¹ * 0) • (1 : ZMod 2)
        = 0 - ((0 : ZMod 2)⁻¹ * 1) • (1 : ZMod 2)
    simp
  · intro hcontra
    -- with a zero inactive pivot coefficient the carried inactive claim
    -- is a deterministic function of the witness: the pad vanishes.
    have hlaw : ∀ mB : Fin 3 → ZMod 2,
        (egJointV2.map (egViewV2 0 ![0, 0, 1] mB 0)).map
            (fun v : CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2) =>
              v.2.1.2.1)
          = PMF.pure (mB 1) := by
      intro mB
      have hfun : ((fun v : CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2) =>
            v.2.1.2.1) ∘ egViewV2 0 ![0, 0, 1] mB 0)
          = fun _ => mB 1 := by
        funext s
        show mB 1 + s.2.1 * 0 = mB 1
        ring
      rw [PMF.map_comp, hfun, map_const_eq_pure]
    have hpp := (hlaw ![0, 0, 0]).symm.trans
      ((congrArg
          (fun q : PMF (CompleteViewType (ZMod 2) (ZMod 2) (ZMod 2)) =>
            q.map fun v => v.2.1.2.1) hcontra).trans
        (hlaw ![0, 1, 0]))
    have h0 := congrArg (fun q : PMF (ZMod 2) => q 0) hpp
    rw [PMF.pure_apply, PMF.pure_apply, if_pos (by decide),
      if_neg (by decide)] at h0
    exact one_ne_zero h0

end NonVacuityAndNegativeTests

/-! ## 8. What still blocks deployed applicability

The v2 capstone is an implication.  For the DEPLOYED v5 system the
following named obligations are open; nothing in this file or repository
discharges them.  Until they are closed, this file must be cited only as
"kernel-checked CONDITIONAL complete-view hiding" — never as "v5 is
zero-knowledge". -/

namespace UnmetDeployment

/-- **UNRESOLVED INTERFACE (not proved) — blocker (a): the deployed
released view satisfies the correlated invariant.**  The v2 capstone's
premise `hCarriedB`, stated as a named `Prop` for the deployed lane
layout: for the witness pairs the protocol quantifies over, the residual
released view minus the inactive-coordinate multiple of the pivot's
residual direction must agree.  No theorem in this repository establishes
this for the deployed Component-B serializer; it is exactly the
correspondence that would let `conditional_complete_view_hiding_v2` apply
to the deployed byte stream.  Not proved here. -/
def DeployedCarriedInvariantCorrespondence {K MB VB : Type*} [Field K]
    [AddCommGroup MB] [Module K MB] [AddCommGroup VB] [Module K VB]
    (inactiveB : MB →ₗ[K] K) (releasedB : MB →ₗ[K] VB)
    (kB mB₁ mB₂ : MB) : Prop :=
  releasedB mB₁ - ((inactiveB kB)⁻¹ * inactiveB mB₁) • releasedB kB
    = releasedB mB₂ - ((inactiveB kB)⁻¹ * inactiveB mB₂) • releasedB kB

/-- The named interface is definitionally the capstone premise: whoever
discharges `DeployedCarriedInvariantCorrespondence` for the deployed
artefacts has produced exactly the `hCarriedB` the v2 capstone consumes.
(This lemma is the naming bridge, not a hiding claim.) -/
theorem carried_invariant_of_correspondence {K MB VB : Type*} [Field K]
    [AddCommGroup MB] [Module K MB] [AddCommGroup VB] [Module K VB]
    {inactiveB : MB →ₗ[K] K} {releasedB : MB →ₗ[K] VB} {kB mB₁ mB₂ : MB}
    (h : DeployedCarriedInvariantCorrespondence inactiveB releasedB kB
      mB₁ mB₂) :
    releasedB mB₁ - ((inactiveB kB)⁻¹ * inactiveB mB₁) • releasedB kB
      = releasedB mB₂ - ((inactiveB kB)⁻¹ * inactiveB mB₂) • releasedB kB :=
  h

end UnmetDeployment

/-! ## 9. Honesty ledger (final restatement)

* **Tier (i) — kernel facts proved in this file**: the conditional
  composition `conditional_complete_view_hiding_v2` with Component B
  routed through the correlated-invariant law `sharedPivotView_pmf_indep`;
  the product/data-processing lemmas; the correspondence-extraction and
  model-serializer lemmas; the fresh-case implication and its fenced
  corollary; the non-vacuity instantiation (on data provably beyond the
  fresh route); and the two premise-deletion negative tests.  All check
  with axioms within `{propext, Classical.choice, Quot.sound}`.
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
  artefacts, every one of the correlated-invariant correspondence
  `UnmetDeployment.DeployedCarriedInvariantCorrespondence` (blocker (a)),
  the Component-C deployed map/certificate —
  `RustLeanRowCorrespondence332`, `CircleArityFourFoldTransport`,
  `CDecAudit` for the deployed matrices (blocker (b)) —
  `SamplerUniformOnKerEll` and the A/B sampler-uniformity equations,
  `DeployedTerminalMatchesModel`, the exact-serialization equations, the
  joint-sampler product structure, and the lane-coefficient interface
  `PivotCoefficientIsGammaB` remains an obligation.  This file discharges
  them only for the `ZMod 2` model.

Consequently: this file proves **conditional** complete-view hiding, with
the Component-B leg carried by the correlated invariant instead of pivot
freshness.  It does not prove, and must not be cited as, "v5 is
zero-knowledge". -/

/-! ## Axiom audit -/

#print axioms tripleProduct
#print axioms tripleProduct_map
#print axioms map_const_eq_pure
#print axioms map_encode_congr
#print axioms componentAView
#print axioms componentBViewV2
#print axioms rustConditionedRows
#print axioms componentCView
#print axioms completeViewV2
#print axioms completeViewV2_eq
#print axioms rustConditionedRows_eq_of_correspondence
#print axioms append_apply_pointwise
#print axioms rustRowOfMaps
#print axioms rustRowOfMaps_correspondence
#print axioms conditional_complete_view_hiding_v2
#print axioms carried_invariant_of_freshB
#print axioms conditional_complete_view_hiding_v2_fresh_corollary
#print axioms egF
#print axioms egSupp
#print axioms egJointV2
#print axioms egViewV2
#print axioms egLaneCoefficient
#print axioms egCarriedInvariant
#print axioms capstone_v2_hypotheses_instantiable
#print axioms capstone_v2_beyond_fresh
#print axioms carriedInvariantB_isLoadBearing
#print axioms pivotGammaB_nonzero_isLoadBearing
#print axioms UnmetDeployment.DeployedCarriedInvariantCorrespondence
#print axioms UnmetDeployment.carried_invariant_of_correspondence

end AspisV5ConditionalHidingCapstoneV2
