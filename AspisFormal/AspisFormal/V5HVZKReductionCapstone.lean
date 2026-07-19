import AspisFormal.CoreHidingPMF
import AspisFormal.V5SelectionHidingAbort
import AspisFormal.V5SaltedMerkleSimulator
import AspisFormal.V5ComponentARankCompletion
import AspisFormal.V5InactiveClaimHVZKReduction
import AspisFormal.V5ComponentCFoldTransport

/-!
# v5 conditional HVZK capstone: composing the five verified component legs

This file composes the five separately verified component witness-independence
laws — Component A (`im A = 𝒲` rank coverage), Component B (shared-pivot terminal
lane), Component C (arity-4 circle fold transport), the deployed selection /
cap-17 retry-abort device, and the salted Merkle simulator — into **one**
IOP-level released-view statement, and lifts it to an adaptive-ZK NARG conclusion
through the BCS / Chiesa–Yogev compilation carried as a **named external
interface**.  Every seam that the conclusion rests on is explicit.

## The exact ceiling (read this first)

What is proved is **HVZK modulo exactly the cited compiler / hash / code-model
assumptions**, never unconditional zero knowledge.  Concretely the composed
IOP-level released view is shown to be within statistical distance `ζ_IOP`
(here the single salted-Merkle placeholder term `zetaMT`) of a **witness-free
simulator** — a genuine honest-verifier-ZK simulator bound — *conditional on*:

* `CircleArity4Transport` (Component C): the four circle folds are the transport,
  through an explicit circle/GRS isomorphism, of the linear GRS folds the
  published binary Reed–Solomon lemma covers.  Carried as a hypothesis; the audit
  `scratchpad/v5-component-c-transport-audit.md` records it as **[UNPROVEN-BY-SOURCE]**
  for the circle/arity-4 case.
* `SaltHidingHash` (salted Merkle ζ_MT): a fixed-function leaf-hash hiding
  interface.  Never established for SHA-256; only the XOR/OTP toy discharges it.
* the **Component-A rank premise** (`Function.Surjective` of the released mask
  map, i.e. `im A = 𝒲`): proved elsewhere *conditionally* on schedule
  injectivity, nonzero aligned weights, the Rust encoder/layout correspondence,
  the concrete QM31-tower correspondence, and the eq-side coverage premise — see
  `V5ComponentARankCompletion` (which does **not** reduce it to a single residual).
* the **Component-B deployed interface** `DeployedBLaneReadsAreSharedPivotView`
  plus the per-run parameter equalities (equal authenticated terminal value,
  equal residual intercept): a code-transcription interface, not discharged here.
* the **selection `Good`-public predicate**: the branch selector reads only a
  public function of the schedule (never the witness); the per-good-schedule
  branch-view hiding hypothesis.
* the **Component-C C-DEC** containment `CDecAudit` for the transported linear
  model.
* the **BCS / Chiesa–Yogev Theorem 26.2.1** lifting itself, carried as the field
  `bcs` and cited — **not re-proved here**.

## The BCS / Chiesa–Yogev Theorem 26.2.1 interface (named, cited, not re-proved)

Per the audit (`scratchpad/v5-component-c-transport-audit.md`, §2), Theorem
26.2.1 of Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*,
states: *"In the BCS transformation, if the public-coin IOP satisfies
honest-verifier zero knowledge (and the privacy parameters `s_MT`, `s_FS` are
large enough) then the resulting non-interactive argument satisfies adaptive zero
knowledge,"* with `ζ_ARG ≤ ζ_IOP + Σ_i δ_MT + t / 2^{s_FS}`.  The audit confirms
from the book's own source that its **only** IOP hypotheses are *public-coin* and
*honest-verifier zero-knowledge* — there is **no** non-adaptive-query and **no**
round-by-round hypothesis (those belong to soundness, a different theorem) — and
that the lifting is **domain/arity/code-agnostic**.  The whole ZK burden is the
single object `(S_IOP, ζ_IOP)` for the specific IOP.

Accordingly `BCSAdaptiveZKLift ζ_IOP honestView simulator AdaptiveZK` carries
exactly "IOP-level HVZK (an explicit simulator within `ζ_IOP`, established below
by the composed component sims) + large-enough salts ⟹ adaptive-ZK NARG" as an
**assumption**, because the paper theorem is not formalized in this repository.
It is a `Prop` field of `HVZKReductionAssumptions`; the docstring is the citation.

## The substantive Lean content

`composed_iop_view_close_to_simulator` is the genuine composition: the five legs
are sampled from **independent** randomness and packaged as one product `PMF`
(`composedView`).  The four exact legs (A, B, C, selection) are *perfectly*
witness-free (equal `PMF`s across the legal witness difference), so they factor
as a common first stage; the only residual distance is the single salted-Merkle
`zetaMT` term, isolated by `composedView_merkle_close`.  Hence the honest composed
view is within `zetaMT` of the witness-free simulator, which is precisely the
IOP-level `ζ_IOP` that Theorem 26.2.1 consumes.

## What is NOT proved

`CircleArity4Transport`, `SaltHidingHash` for SHA-256, the A-rank premise for the
deployed schedule, the B interface for the deployed byte stream, the BCS theorem,
public-coin-ness / large-salt sizing, and any correspondence between these
abstract composed views and the deployed Rust transcript.  Every one of these is
a named seam or a cited external theorem, and the honest conclusion label is
**"HVZK modulo exactly the cited compiler/hash/code-model assumptions."**
-/

open scoped ENNReal
open AspisV5SaltedMerkleSimulator
open AspisV5SelectionHidingAbort
open AspisV5InactiveClaimHVZKReduction
open AspisV5InactiveClaimJointHiding
open AspisV5InactiveClaimDeployedCorrespondence
open AspisV5CompactTerminal
open AspisV5ComponentCFoldTransport
open AspisV5ComponentCConditionalDecoupling

namespace AspisV5HVZKReductionCapstone

/-! ## 1. The independent product of the five released-view legs -/

section Product

variable {ΩA ΩB ΩC ΩS ΩMT : Type*}

/-- **The composed IOP released view.**  The five component released views —
Component A's masked opening, Component B's shared-pivot terminal reads,
Component C's arity-4 circle fold view, the selection / cap-17 retry-abort
transcript, and the salted Merkle view — sampled from **independent** randomness
and packaged as one product distribution.  This is the single IOP-level released
object whose witness-independence the capstone establishes. -/
noncomputable def composedView (pA : PMF ΩA) (pB : PMF ΩB) (pC : PMF ΩC) (pS : PMF ΩS)
    (pMT : PMF ΩMT) : PMF (ΩA × ΩB × ΩC × ΩS × ΩMT) :=
  pA.bind fun a => pB.bind fun b => pC.bind fun c => pS.bind fun s =>
    pMT.map fun mt => (a, b, c, s, mt)

/-- **The four exact legs compose losslessly.**  If the A, B, C and selection
released laws each agree (they are all *perfectly* witness-free across a legal
witness difference), the composed product is unchanged when the Merkle leg is
held fixed.  Pure `PMF` equality — no error term. -/
theorem composedView_exact_congr {pA pA' : PMF ΩA} {pB pB' : PMF ΩB}
    {pC pC' : PMF ΩC} {pS pS' : PMF ΩS} (pMT : PMF ΩMT)
    (hA : pA = pA') (hB : pB = pB') (hC : pC = pC') (hS : pS = pS') :
    composedView pA pB pC pS pMT = composedView pA' pB' pC' pS' pMT := by
  rw [hA, hB, hC, hS]

/-- **The composed distance is carried entirely by the Merkle leg.**  With the
four exact legs shared as a common first stage, the statistical distance between
two composed views differing only in the Merkle leg is at most the Merkle leg's
own distance.  Four applications of the shared-first-stage conditioning bound
`statDist_bind_le` peel the exact legs; the data-processing inequality
`statDist_map_le` handles the final packaging map. -/
theorem composedView_merkle_close {pA : PMF ΩA} {pB : PMF ΩB} {pC : PMF ΩC}
    {pS : PMF ΩS} {pMT qMT : PMF ΩMT} {ε : ℝ≥0∞} (h : statDist pMT qMT ≤ ε) :
    statDist (composedView pA pB pC pS pMT) (composedView pA pB pC pS qMT) ≤ ε := by
  unfold composedView
  refine statDist_bind_le _ _ _ fun a => ?_
  refine statDist_bind_le _ _ _ fun b => ?_
  refine statDist_bind_le _ _ _ fun c => ?_
  refine statDist_bind_le _ _ _ fun s => ?_
  exact (statDist_map_le _ _ _).trans h

end Product

/-! ## 2. The IOP-level HVZK evidence and the carried BCS 26.2.1 interface -/

section BCS

variable {Ω : Type*}

/-- **IOP-level honest-verifier-ZK evidence.**  The honest composed released view
is within statistical distance `ζIOP` of a witness-free simulator.  This is the
object `(S_IOP, ζ_IOP)` of Definition `iop-hvzk` for the composed IOP: the
existence of a simulator whose output is `ζIOP`-close to the honest view. -/
def IOPLevelHVZK (honestView simulator : PMF Ω) (ζIOP : ℝ≥0∞) : Prop :=
  statDist honestView simulator ≤ ζIOP

/-- **Chiesa–Yogev Theorem 26.2.1, carried as a named external interface.**
`BCSAdaptiveZKLift ζIOP honestView simulator AdaptiveZK` is the implication
"IOP-level HVZK with error `ζIOP` (and large-enough salts `s_MT`, `s_FS`) ⟹ the
BCS-compiled NARG is adaptive zero-knowledge."  Per the audit, the theorem's IOP
hypotheses are exactly *public-coin* + *HVZK* (no non-adaptive-query, no
round-by-round), and the lifting is domain/arity/code-agnostic, giving
`ζ_ARG ≤ ζ_IOP + Σ_i δ_MT + t / 2^{s_FS}`.  It is **carried as an assumption**,
never re-proved here: `AdaptiveZK` is an opaque `Prop` standing for the
(unformalized) adaptive-ZK NARG conclusion, and the large-salt sizing is folded
into this interface's provenance. -/
def BCSAdaptiveZKLift (ζIOP : ℝ≥0∞) (honestView simulator : PMF Ω)
    (AdaptiveZK : Prop) : Prop :=
  IOPLevelHVZK honestView simulator ζIOP → AdaptiveZK

end BCS

/-! ## 3. The five per-leg released views and their witness-independence wirings

Each wiring lemma consumes **exactly one** named seam and produces the
corresponding leg's released-law equality (or the Merkle closeness).  The type
parameters of the five legs are fully independent: the composition never forces a
shared field. -/

section Legs

variable {KA : Type*} [Field KA] [Fintype KA] {mA bA : ℕ}
  {WA : Type*}
variable {KB : Type*} [Field KB] [Fintype KB] {VB : Type*} [AddCommGroup VB]
  [Module KB VB]
variable {KC : Type*} [Field KC] [DecidableEq KC]
  {MC AC BC VC UC : Type*}
  [AddCommGroup MC] [Module KC MC] [Fintype MC]
  [AddCommGroup AC] [Module KC AC] [AddCommGroup BC] [Module KC BC]
  [AddCommGroup VC] [Module KC VC] [AddCommGroup UC] [Module KC UC] [DecidableEq UC]
variable {Sched WS VS : Type*}
variable {ιm : Type*} [Fintype ιm] [DecidableEq ιm]
  {Sm : Type*} [Fintype Sm] [Nonempty Sm]
  {Vm Dm Tagm : Type*}

/-- **Component-A released view.**  The masked opening `R ↦ shift w + maskA R`
with `R` uniform on the mask space: an affine masked view over the finite field
`KA`. -/
noncomputable def aView (maskA : (Fin mA → KA) →ₗ[KA] (Fin bA → KA))
    (shiftA : WA → Fin bA → KA) (w : WA) : PMF (Fin bA → KA) :=
  (PMF.uniformOfFintype (Fin mA → KA)).map (fun R => shiftA w + maskA R)

/-- **Component-A witness-independence from the rank premise `im A = 𝒲`.**  A
surjective released mask map hides the witness shift: the released-view law is the
same for any two witnesses.  Consumes the named A seam `Function.Surjective maskA`
(i.e. `im A = 𝒲`), via `CoreHidingPMF.view_pmf_indep_of_witness`. -/
theorem aLeg_indep (maskA : (Fin mA → KA) →ₗ[KA] (Fin bA → KA))
    (hsurjA : Function.Surjective maskA) (shiftA : WA → Fin bA → KA) (w w₀ : WA) :
    aView maskA shiftA w = aView maskA shiftA w₀ := by
  haveI : DecidableEq KA := Classical.decEq _
  unfold aView
  exact view_pmf_indep_of_witness maskA hsurjA (shiftA w) (shiftA w₀)

/-- **Component-B released view.**  The uniform pivot scalar pushed through the
decoded (terminal opening, carried inactive claim, residual view) read triple. -/
noncomputable def bView (bReads : KB → KB × KB × VB) : PMF (KB × KB × VB) :=
  (PMF.uniformOfFintype KB).map bReads

/-- **Component-B witness-independence from the deployed interface.**  Two
deployed runs whose reads satisfy `DeployedBLaneReadsAreSharedPivotView`, whose
authenticated terminal values agree, and whose residual intercepts agree have
identical read laws.  Consumes the named B interface and the per-run parameter
equalities, via `deployed_bLane_reads_pmf_indep`. -/
theorem bLeg_indep (bReads bReads₀ : KB → KB × KB × VB) (point : Round → KB)
    (scale : KB) (inactive : (Row → KB) →ₗ[KB] KB) (released : (Row → KB) →ₗ[KB] VB)
    (mB mB₀ : Row → KB)
    (hIface : DeployedBLaneReadsAreSharedPivotView bReads point scale inactive
      released mB)
    (hIface₀ : DeployedBLaneReadsAreSharedPivotView bReads₀ point scale inactive
      released mB₀)
    (tB : KB) (hmB : terminalDotFunctional point scale mB = tB)
    (hmB₀ : terminalDotFunctional point scale mB₀ = tB)
    (hIntercept : released mB - inactive mB • released (basis pivotRow 1)
      = released mB₀ - inactive mB₀ • released (basis pivotRow 1)) :
    bView bReads = bView bReads₀ := by
  unfold bView
  exact deployed_bLane_reads_pmf_indep bReads bReads₀ point scale inactive released
    mB mB₀ hIface hIface₀ tB hmB hmB₀ hIntercept

/-- **Component-C released view.**  The uniform conditioned mask on the fibre
`{c : ker ℓ // E c = e}`, batched into the witness word `x + γ^18 · c` and read
through the concrete four-arity-four-fold circle pipeline. -/
noncomputable def cView (enc : MC →ₗ[KC] AC) (cf : Fin 4 → AC → AC)
    (ρ : Fin 5 → AC →ₗ[KC] VC)
    (ell : MC →ₗ[KC] KC) (E : MC →ₗ[KC] UC) (γ : KC) (x : MC) (e : UC)
    [Nonempty {c : LinearMap.ker ell // E.domRestrict (LinearMap.ker ell) c = e}] :
    PMF (Fin 5 → VC) :=
  (PMF.uniformOfFintype {c : LinearMap.ker ell //
      E.domRestrict (LinearMap.ker ell) c = e}).map
    (fun c : {c : LinearMap.ker ell // E.domRestrict (LinearMap.ker ell) c = e} =>
      circleFoldView enc cf ρ (x + γ ^ 18 • ((c : LinearMap.ker ell) : MC)))

/-- **Component-C witness-independence from transport + C-DEC.**  Under
`CircleArity4Transport` (the four circle folds transport to the linear GRS folds)
and `CDecAudit` (the C-DEC containment for the transported linear model), the
conditioned circle-fold released view is the same law for any two legal witnesses.
Consumes the named C transport seam and the C-DEC seam, via
`circleArity4_full_fold_conditional_decoupling`. -/
theorem cLeg_indep (enc : MC →ₗ[KC] AC) (Φ : AC ≃ₗ[KC] BC) (gf : Fin 4 → BC →ₗ[KC] BC)
    (cf : Fin 4 → AC → AC) (ρ : Fin 5 → AC →ₗ[KC] VC)
    (ell : MC →ₗ[KC] KC) (E : MC →ₗ[KC] UC) {γ : KC} (hγ : γ ≠ 0)
    {Δw : Submodule KC MC}
    (htr : CircleArity4Transport Φ gf cf)
    (hdec : CDecAudit ell E (foldLinearModel enc Φ gf ρ) Δw)
    {x x₀ : MC} (hlegal : x₀ - x ∈ Δw) (e : UC)
    [Nonempty {c : LinearMap.ker ell // E.domRestrict (LinearMap.ker ell) c = e}] :
    cView enc cf ρ ell E γ x e = cView enc cf ρ ell E γ x₀ e := by
  unfold cView
  exact circleArity4_full_fold_conditional_decoupling enc Φ gf cf ρ ell E hγ htr hdec
    hlegal e

/-- **Selection / cap-17 retry-abort released view.**  The full bounded-retry
transcript: retry count, least-good selector, selected schedule, selected branch
view, and the cap-17 abort symbol. -/
noncomputable def sView (Good : Sched → Bool) (schedLaw : PMF (Fin 3 → Sched))
    (branchView : Fin 3 → Sched → WS → PMF VS) (w : WS) :
    PMF (Option (ℕ × Fin 3 × Sched × VS)) :=
  spendComposedLaw Good schedLaw branchView w

/-- **Selection witness-independence from the `Good`-public predicate.**  When the
selector reads only the public schedule predicate `Good` and each branch view is
witness-independent on every *good* schedule, the entire cap-17 released
transcript is the same law for any two witnesses.  Consumes the selection seam
(the per-good-schedule branch-view hiding hypothesis), via
`spendComposedLaw_witness_indep`. -/
theorem sLeg_indep (Good : Sched → Bool) (schedLaw : PMF (Fin 3 → Sched))
    (branchView : Fin 3 → Sched → WS → PMF VS) (w w₀ : WS)
    (hSel : ∀ (sel : Fin 3) (σ : Sched), Good σ = true →
      branchView sel σ w = branchView sel σ w₀) :
    sView Good schedLaw branchView w = sView Good schedLaw branchView w₀ := by
  unfold sView
  exact spendComposedLaw_witness_indep Good schedLaw branchView w w₀ hSel

/-- **Salted Merkle leg closeness from `SaltHidingHash`.**  The real salted
commitment view is within `zetaMT` of the placeholder simulator, which reads only
the opened answers — the salted Merkle HVZK-simulator bound.  Consumes the named
hash seam `SaltHidingHash`, via `mtSimulate_close`. -/
theorem mtLeg_close (leafH : Tagm → Vm → Sm → Dm) {ζ : ℝ≥0∞}
    (hH : SaltHidingHash leafH ζ) (tagm : Tagm) (Q : Finset ιm) (a : ιm → Vm)
    (v₀ : Vm) :
    statDist (realMT leafH tagm Q a)
        (MTSimulate leafH tagm Q (fun i _ => a i) v₀)
      ≤ zetaMT (Fintype.card ιm) Q.card ζ := by
  haveI : DecidableEq Sm := Classical.decEq _
  exact mtSimulate_close hH tagm Q a v₀

end Legs

/-! ## 4. The composition theorem (explicit hypotheses, every one consumed)

The abstract composition: four *exact* leg equalities plus one Merkle closeness
bound compose to the composed-view / simulator distance bound.  Stated abstractly
over the five leg distributions so the mathlib linter machine-checks that no
hypothesis is idle. -/

section Composition

variable {ΩA ΩB ΩC ΩS ΩMT : Type*}

/-- **The IOP-level HVZK composition.**  Given
* `hA`, `hB`, `hC`, `hS`: the four exact legs (A, B, C, selection) are perfectly
  witness-free — their released laws at the honest witness equal those at the
  reference witness;
* `hMT`: the salted Merkle leg is within `ε` of its witness-free simulator,
the composed honest released view is within `ε` of the composed simulator (exact
legs at the reference witness, Merkle leg simulated).  Every hypothesis is used:
`hA`–`hS` fuse the exact legs into a common first stage; `hMT` supplies the sole
residual `ε = ζ_IOP`. -/
theorem composed_iop_view_close_to_simulator
    {pA pA' : PMF ΩA} {pB pB' : PMF ΩB} {pC pC' : PMF ΩC} {pS pS' : PMF ΩS}
    {pMT qMT : PMF ΩMT} {ε : ℝ≥0∞}
    (hA : pA = pA') (hB : pB = pB') (hC : pC = pC') (hS : pS = pS')
    (hMT : statDist pMT qMT ≤ ε) :
    statDist (composedView pA pB pC pS pMT) (composedView pA' pB' pC' pS' qMT)
      ≤ ε := by
  rw [composedView_exact_congr pMT hA hB hC hS]
  exact composedView_merkle_close hMT

/-- **The exact legs are perfectly witness-free.**  With the Merkle leg held at
one shared draw, the composed view at the honest witness *equals* the composed
view at the reference witness: the A ⊕ B ⊕ C ⊕ selection part leaks nothing, the
only statistical slack in the capstone is the salted-Merkle `zetaMT` term.  This
is the sharpened, error-free reading of the composition. -/
theorem composed_exact_legs_witness_free
    {pA pA' : PMF ΩA} {pB pB' : PMF ΩB} {pC pC' : PMF ΩC} {pS pS' : PMF ΩS}
    (pMT : PMF ΩMT)
    (hA : pA = pA') (hB : pB = pB') (hC : pC = pC') (hS : pS = pS') :
    composedView pA pB pC pS pMT = composedView pA' pB' pC' pS' pMT :=
  composedView_exact_congr pMT hA hB hC hS

end Composition

/-! ## 5. The bundled assumptions and the main theorem

`HVZKReductionAssumptions` bundles every named seam actually required, together
with the deployed data each acts on, and the carried BCS 26.2.1 interface.  Each
field is consumed by `capstone_adaptive_zk`. -/

section Bundle

variable {KA : Type*} [Field KA] [Fintype KA] {mA bA : ℕ}
  {WA : Type*}
variable {KB : Type*} [Field KB] [Fintype KB] {VB : Type*} [AddCommGroup VB]
  [Module KB VB]
variable {KC : Type*} [Field KC] [DecidableEq KC]
  {MC AC BC VC UC : Type*}
  [AddCommGroup MC] [Module KC MC] [Fintype MC]
  [AddCommGroup AC] [Module KC AC] [AddCommGroup BC] [Module KC BC]
  [AddCommGroup VC] [Module KC VC] [AddCommGroup UC] [Module KC UC] [DecidableEq UC]
variable {Sched WS VS : Type*}
variable {ιm : Type*} [Fintype ιm] [DecidableEq ιm]
  {Sm : Type*} [Fintype Sm] [Nonempty Sm]
  {Vm Dm Tagm : Type*}

/-- **Every seam the composed adaptive-ZK conclusion rests on.**  A structure
bundling the five component seams, their deployed data, the C-DEC and B parameter
equalities, and the carried external BCS 26.2.1 lifting.  See the module docstring
and the ledger below for each field's status. -/
structure HVZKReductionAssumptions where
  /-- Component-A released mask map (its surjectivity is `im A = 𝒲`). -/
  maskA : (Fin mA → KA) →ₗ[KA] (Fin bA → KA)
  /-- **A seam** — the rank premise `im A = 𝒲`; proved elsewhere conditionally. -/
  hsurjA : Function.Surjective maskA
  shiftA : WA → Fin bA → KA
  wA : WA
  wA₀ : WA
  bReads : KB → KB × KB × VB
  bReads₀ : KB → KB × KB × VB
  point : Round → KB
  scale : KB
  inactive : (Row → KB) →ₗ[KB] KB
  released : (Row → KB) →ₗ[KB] VB
  mB : Row → KB
  mB₀ : Row → KB
  /-- **B seam** — the deployed shared-pivot read interface (honest run). -/
  hIfaceB : DeployedBLaneReadsAreSharedPivotView bReads point scale inactive released mB
  /-- **B seam** — the deployed shared-pivot read interface (reference run). -/
  hIfaceB₀ : DeployedBLaneReadsAreSharedPivotView bReads₀ point scale inactive released mB₀
  tB : KB
  hmB : terminalDotFunctional point scale mB = tB
  hmB₀ : terminalDotFunctional point scale mB₀ = tB
  /-- **B seam** — the residual intercept parameter equality (the `hCarriedB` shape). -/
  hInterceptB : released mB - inactive mB • released (basis pivotRow 1)
    = released mB₀ - inactive mB₀ • released (basis pivotRow 1)
  enc : MC →ₗ[KC] AC
  Φ : AC ≃ₗ[KC] BC
  gf : Fin 4 → BC →ₗ[KC] BC
  cf : Fin 4 → AC → AC
  ρ : Fin 5 → AC →ₗ[KC] VC
  ell : MC →ₗ[KC] KC
  E : MC →ₗ[KC] UC
  γ : KC
  hγ : γ ≠ 0
  Δw : Submodule KC MC
  /-- **C seam** — the circle/arity-4 transport hypothesis (UNPROVEN-BY-SOURCE). -/
  htr : CircleArity4Transport Φ gf cf
  /-- **C seam** — the C-DEC containment for the transported linear model. -/
  hdec : CDecAudit ell E (foldLinearModel enc Φ gf ρ) Δw
  xC : MC
  xC₀ : MC
  /-- **C seam** — the legal witness difference. -/
  hlegalC : xC₀ - xC ∈ Δw
  eC : UC
  /-- The conditioning value lies in the image of `E` (nonempty fibre). -/
  [hneC : Nonempty {c : LinearMap.ker ell // E.domRestrict (LinearMap.ker ell) c = eC}]
  Good : Sched → Bool
  schedLaw : PMF (Fin 3 → Sched)
  branchView : Fin 3 → Sched → WS → PMF VS
  wS : WS
  wS₀ : WS
  /-- **Selection seam** — the per-good-schedule branch-view hiding hypothesis
  (the `Good`-public predicate reads no witness). -/
  hSel : ∀ (sel : Fin 3) (σ : Sched), Good σ = true →
    branchView sel σ wS = branchView sel σ wS₀
  leafH : Tagm → Vm → Sm → Dm
  ζ : ℝ≥0∞
  /-- **Merkle seam** — the fixed-function salted leaf-hash hiding interface
  (never established for SHA-256). -/
  hH : SaltHidingHash leafH ζ
  tagm : Tagm
  Q : Finset ιm
  aMT : ιm → Vm
  v₀ : Vm
  /-- The (unformalized) adaptive-ZK NARG conclusion. -/
  AdaptiveZK : Prop
  /-- **BCS seam** — Chiesa–Yogev Theorem 26.2.1, carried as an external
  interface: IOP-level HVZK (within `ζ_IOP = zetaMT`) + large salts ⟹ adaptive
  ZK.  Cited, not re-proved. -/
  bcs : BCSAdaptiveZKLift (zetaMT (Fintype.card ιm) Q.card ζ)
    (composedView (aView maskA shiftA wA) (bView bReads)
      (cView enc cf ρ ell E γ xC eC) (sView Good schedLaw branchView wS)
      (realMT leafH tagm Q aMT))
    (composedView (aView maskA shiftA wA₀) (bView bReads₀)
      (cView enc cf ρ ell E γ xC₀ eC) (sView Good schedLaw branchView wS₀)
      (MTSimulate leafH tagm Q (fun i _ => aMT i) v₀))
    AdaptiveZK

/-- **The capstone.**  From `HVZKReductionAssumptions` the composed IOP-level
released view is within `zetaMT` of the witness-free simulator (the substantive
composition, `composed_iop_view_close_to_simulator`, fed by the five per-leg
wirings, each consuming its seam), and the carried BCS 26.2.1 interface lifts that
to the adaptive-ZK NARG conclusion.  **Reading: HVZK modulo exactly the cited
compiler/hash/code-model assumptions — never unconditional ZK.**  Every field of
the bundle is consumed. -/
theorem capstone_adaptive_zk (H : HVZKReductionAssumptions
    (KA := KA) (mA := mA) (bA := bA) (WA := WA) (KB := KB) (VB := VB)
    (KC := KC) (MC := MC) (AC := AC) (BC := BC) (VC := VC) (UC := UC)
    (Sched := Sched) (WS := WS) (VS := VS)
    (ιm := ιm) (Sm := Sm) (Vm := Vm) (Dm := Dm) (Tagm := Tagm)) :
    H.AdaptiveZK := by
  haveI := H.hneC
  exact H.bcs
    (composed_iop_view_close_to_simulator
      (aLeg_indep H.maskA H.hsurjA H.shiftA H.wA H.wA₀)
      (bLeg_indep H.bReads H.bReads₀ H.point H.scale H.inactive H.released H.mB
        H.mB₀ H.hIfaceB H.hIfaceB₀ H.tB H.hmB H.hmB₀ H.hInterceptB)
      (cLeg_indep H.enc H.Φ H.gf H.cf H.ρ H.ell H.E H.hγ H.htr H.hdec H.hlegalC
        H.eC)
      (sLeg_indep H.Good H.schedLaw H.branchView H.wS H.wS₀ H.hSel)
      (mtLeg_close H.leafH H.hH H.tagm H.Q H.aMT H.v₀))

end Bundle

/-! ## 6. Assumption ledger

Every assumption the capstone conclusion rests on, and its status.  "Proved
elsewhere conditionally" means a named theorem exists but under its own residual
hypotheses; "named interface" means a `Prop` never discharged for the deployed
artefact; "external citation" means a paper theorem not formalized here.

* `hsurjA` : `Function.Surjective maskA` (`im A = 𝒲`) — **A rank premise**.
  Proved elsewhere *conditionally* (`V5ComponentARankCompletion`): needs schedule
  injectivity, nonzero weights, Rust encoder/layout correspondence, QM31-tower
  correspondence, and the eq-side coverage premise — *not* a single residual.
* `hIfaceB`, `hIfaceB₀` : `DeployedBLaneReadsAreSharedPivotView` — **B code-model
  interface**.  Named interface, not discharged for the deployed byte stream
  (`V5InactiveClaimHVZKReduction`).
* `hmB`, `hmB₀`, `hInterceptB` — **B parameter equalities**.  Assumed (equal
  authenticated terminal value + equal residual intercept); not derived from
  public simulatability.
* `htr` : `CircleArity4Transport` — **C transport interface**.  Named interface,
  [UNPROVEN-BY-SOURCE] for circle/arity-4 (`v5-component-c-transport-audit.md`).
* `hdec` : `CDecAudit` — **C C-DEC containment**.  Proved elsewhere conditionally
  (`V5ComponentCConditionalDecoupling`).
* `hSel` : per-good-schedule branch hiding — **selection `Good`-public predicate**.
  Proved elsewhere conditionally (`V5SelectionHidingAbort`); load-bearing
  (`selection_good_public_load_bearing`).
* `hH` : `SaltHidingHash` — **deployed-hash ζ_MT interface**.  Named interface,
  never established for SHA-256 (`V5SaltedMerkleSimulator`); only the XOR/OTP toy
  proves it.
* `bcs` : `BCSAdaptiveZKLift` — **BCS / Chiesa–Yogev Theorem 26.2.1**.  External
  citation, carried, not re-proved; load-bearing (`bcs_interface_load_bearing`).

Substantive (proved here, unconditionally in-kernel): the independent-product
composition `composedView`, its exact-leg losslessness `composed_exact_legs_witness_free`,
the Merkle-only residual bound `composedView_merkle_close`, and their fusion
`composed_iop_view_close_to_simulator` — the composed IOP released view is within
the single salted-Merkle `zetaMT` term of a witness-free simulator, given the
seams above. -/

section Ledger

#check @composed_iop_view_close_to_simulator
#check @composed_exact_legs_witness_free
#check @capstone_adaptive_zk
#check @BCSAdaptiveZKLift
#check @IOPLevelHVZK

end Ledger

/-! ## 7. Non-vacuity: a concrete bundle discharging every seam

A finite instantiation in which all five seams hold: Component A the identity
mask over `ZMod 5` (surjective); Component B the synthetic shared-pivot reads at
the transcribed terminal covector; Component C the positive circle/arity-4
transport model over `ZMod 5` with trivial (`⊥`) legal-difference space;
selection the `ZMod 3` least-good toy with genuinely distinct witnesses `0 ≠ 1`;
salted Merkle the one-time-pad `xorLeafHash` (ζ = 0, so `ζ_IOP = 0` — a
*perfect* IOP-level simulator here).  The full pipeline `capstone_adaptive_zk`
fires on it with the placeholder conclusion `AdaptiveZK := True`. -/

namespace Toy

open AspisV5ComponentCFoldTransport.PositiveModel

/-- Toy field for legs A, B, C. -/
abbrev F5 : Type := ZMod 5

/-- Toy A mask: the identity on a one-symbol mask space (surjective). -/
noncomputable def toyMaskA : (Fin 1 → F5) →ₗ[F5] (Fin 1 → F5) := LinearMap.id

theorem toyMaskA_surjective : Function.Surjective ⇑toyMaskA := by
  rw [toyMaskA, LinearMap.id_coe]; exact Function.surjective_id

/-- Toy B reads at the transcribed terminal covector (the interface's own
synthetic shared-pivot view), witness `m`. -/
noncomputable def toyBReads (m : Row → F5) : F5 → F5 × F5 × F5 :=
  sharedPivotView (terminalDotFunctional (0 : Round → F5) 0)
    (LinearMap.proj pivotRow) (LinearMap.proj padRow) (basis pivotRow 1) m

/-- The synthetic B interface holds for every witness (row-993 projection is the
binary-mask covector; row-994 pad projection is the residual view). -/
theorem toyBReads_iface (m : Row → F5) :
    DeployedBLaneReadsAreSharedPivotView (toyBReads m) (0 : Round → F5) 0
      (LinearMap.proj pivotRow) (LinearMap.proj padRow) m :=
  interface_nonvacuous (0 : Round → F5) 0 m

/-- Nonempty conditioning fibre for the toy C leg (`E = 0`, so the fibre is all
of `ker 0`). -/
instance : Nonempty {c : LinearMap.ker (0 : (Fin 4 → F5) →ₗ[F5] F5) //
    (0 : (Fin 4 → F5) →ₗ[F5] (Fin 1 → F5)).domRestrict
      (LinearMap.ker (0 : (Fin 4 → F5) →ₗ[F5] F5)) c = 0} :=
  ⟨⟨0, by simp⟩⟩

/-- Toy Merkle assignment: all leaves the false bit. -/
def toyAMT : Fin 1 → Bool := fun _ => false

/-- **The concrete bundle: every seam discharged.** -/
noncomputable def toyAssumptions : HVZKReductionAssumptions
    (KA := F5) (mA := 1) (bA := 1) (WA := Fin 1 → F5) (KB := F5) (VB := F5)
    (KC := F5) (MC := Fin 4 → F5) (AC := Fin 4 → F5) (BC := Fin 4 → F5)
    (VC := F5) (UC := Fin 1 → F5)
    (Sched := Bool) (WS := ZMod 3) (VS := Fin 1 → ZMod 3)
    (ιm := Fin 1) (Sm := Bool) (Vm := Bool) (Dm := Bool) (Tagm := Unit) where
  maskA := toyMaskA
  hsurjA := toyMaskA_surjective
  shiftA := id
  wA := 0
  wA₀ := 0
  bReads := toyBReads 0
  bReads₀ := toyBReads 0
  point := 0
  scale := 0
  inactive := LinearMap.proj pivotRow
  released := LinearMap.proj padRow
  mB := 0
  mB₀ := 0
  hIfaceB := toyBReads_iface 0
  hIfaceB₀ := toyBReads_iface 0
  tB := 0
  hmB := map_zero _
  hmB₀ := map_zero _
  hInterceptB := rfl
  enc := enc
  Φ := Φ
  gf := gf
  cf := cf
  ρ := ρ
  ell := 0
  E := 0
  γ := 1
  hγ := one_ne_zero
  Δw := ⊥
  htr := transport_holds
  hdec := (Submodule.map_bot _).le.trans bot_le
  xC := 0
  xC₀ := 0
  hlegalC := by simp
  eC := 0
  Good := toyGood
  schedLaw := toySchedLaw
  branchView := toyBranchView
  wS := 0
  wS₀ := 1
  hSel := fun sel σ hσ =>
    affineBranchView_witness_indep toyMaskMap toyWitnessShift sel σ
      (toy_surjective sel σ hσ) 0 1
  leafH := xorLeafHash
  ζ := 0
  hH := xorLeafHash_hiding
  tagm := ()
  Q := ∅
  aMT := toyAMT
  v₀ := false
  AdaptiveZK := True
  bcs := fun _ => trivial

/-- **The full pipeline fires non-vacuously.**  `capstone_adaptive_zk` runs
end-to-end on the concrete bundle — the composition, the five wirings, and the
carried BCS arrow — yielding the (placeholder `True`) conclusion. -/
theorem toy_capstone : True :=
  capstone_adaptive_zk toyAssumptions

/-- The toy honest composed IOP released view. -/
noncomputable def toyHonestView :=
  composedView (aView toyMaskA (id : (Fin 1 → F5) → Fin 1 → F5) 0) (bView (toyBReads 0))
    (cView enc cf ρ (0 : (Fin 4 → F5) →ₗ[F5] F5) (0 : (Fin 4 → F5) →ₗ[F5] (Fin 1 → F5))
      1 0 0)
    (sView toyGood toySchedLaw toyBranchView 0)
    (realMT xorLeafHash () (∅ : Finset (Fin 1)) toyAMT)

/-- The toy witness-free composed simulator (exact legs at the reference witness,
Merkle leg simulated). -/
noncomputable def toySimView :=
  composedView (aView toyMaskA (id : (Fin 1 → F5) → Fin 1 → F5) 0) (bView (toyBReads 0))
    (cView enc cf ρ (0 : (Fin 4 → F5) →ₗ[F5] F5) (0 : (Fin 4 → F5) →ₗ[F5] (Fin 1 → F5))
      1 0 0)
    (sView toyGood toySchedLaw toyBranchView 1)
    (MTSimulate xorLeafHash () (∅ : Finset (Fin 1)) (fun i _ => toyAMT i) false)

/-- Legal difference for the toy C leg (trivial `⊥` difference). -/
theorem toy_cLegal : (0 : Fin 4 → F5) - 0 ∈ (⊥ : Submodule F5 (Fin 4 → F5)) := by simp

/-- **The composed IOP-level HVZK bound is realised, with `ζ_IOP = 0`.**  On the
one-time-pad Merkle instance the composed honest view is within `zetaMT 1 0 0`
of the witness-free simulator — a *perfect* IOP-level simulator for the composed
released view of this instance, fusing all five per-leg wirings. -/
theorem toy_composed_bound :
    statDist toyHonestView toySimView
      ≤ zetaMT (Fintype.card (Fin 1)) (∅ : Finset (Fin 1)).card 0 :=
  composed_iop_view_close_to_simulator
    (aLeg_indep toyMaskA toyMaskA_surjective id 0 0)
    (bLeg_indep (toyBReads 0) (toyBReads 0) 0 0 (LinearMap.proj pivotRow)
      (LinearMap.proj padRow) 0 0 (toyBReads_iface 0) (toyBReads_iface 0) 0
      (map_zero _) (map_zero _) rfl)
    (cLeg_indep enc Φ gf cf ρ (0 : (Fin 4 → F5) →ₗ[F5] F5)
      (0 : (Fin 4 → F5) →ₗ[F5] (Fin 1 → F5)) one_ne_zero transport_holds
      ((Submodule.map_bot _).le.trans bot_le) toy_cLegal 0)
    (sLeg_indep toyGood toySchedLaw toyBranchView 0 1
      (fun sel σ hσ => affineBranchView_witness_indep toyMaskMap toyWitnessShift
        sel σ (toy_surjective sel σ hσ) 0 1))
    (mtLeg_close xorLeafHash xorLeafHash_hiding () ∅ toyAMT false)

end Toy

/-! ## 8. Negative / load-bearing tests

Each shows that a named seam is not decorative: dropping it breaks the composed
conclusion. -/

section LoadBearing

/-- **The C transport seam is load-bearing.**  In the negative circle model
(fold round 0 squares over `ZMod 3`): (i) the two legal witnesses' released
fold-view laws are genuinely **different** `PMF`s — so the Component-C leg
equality `hC` that the composition consumes *fails*; and (ii) **no** transport
isomorphism and linear GRS folds can satisfy `CircleArity4Transport` — so the
seam is unsatisfiable exactly where the conclusion fails.  Drop `htr` and the
composition has no `hC` to fuse. -/
theorem transport_seam_load_bearing :
    ((PMF.uniformOfFintype NegativeModel.A).map
          (fun c : NegativeModel.A => (0 : Fin 5 → NegativeModel.K)
            + circleFoldView NegativeModel.enc NegativeModel.cf NegativeModel.ρ c)
        ≠ (PMF.uniformOfFintype NegativeModel.A).map
          (fun c : NegativeModel.A => (Pi.single 1 1 : Fin 5 → NegativeModel.K)
            + circleFoldView NegativeModel.enc NegativeModel.cf NegativeModel.ρ c))
      ∧ (∀ (Φ : NegativeModel.A ≃ₗ[NegativeModel.K] NegativeModel.A)
            (gf : Fin 4 → NegativeModel.A →ₗ[NegativeModel.K] NegativeModel.A),
          ¬ CircleArity4Transport Φ gf NegativeModel.cf) :=
  ⟨NegativeModel.negative_model_laws_differ, NegativeModel.negative_model_no_transport⟩

/-- **The BCS interface is load-bearing.**  Take the toy bundle (every component
seam satisfiable) with `AdaptiveZK := False`.  The composed IOP-level HVZK bound
`Toy.toy_composed_bound` *is* provable from the seams, so `BCSAdaptiveZKLift …
False`, applied to it, would yield `False`.  Hence the adaptive-ZK conclusion
cannot be manufactured from the composition alone — it rests entirely on the
carried external Theorem 26.2.1.  (No such `bcs` arrow to `False` can exist.) -/
theorem bcs_interface_load_bearing
    (hbcs : BCSAdaptiveZKLift
      (zetaMT (Fintype.card (Fin 1)) (∅ : Finset (Fin 1)).card 0)
      Toy.toyHonestView Toy.toySimView False) :
    False :=
  hbcs Toy.toy_composed_bound

/-- **The selection `Good`-public predicate is load-bearing.**  With a
witness-*reading* predicate in the selector slot (and fully hiding branch views),
one witness never aborts and the other aborts with certainty, so the selection
leg's released laws differ — the selection leg equality `hS` fails.  This is
`V5SelectionHidingAbort.witness_dependent_good_breaks_composed_hiding`. -/
theorem selection_good_public_load_bearing :
    spendComposedLaw (leakGood true) leakSchedLaw leakBranchView true
      ≠ spendComposedLaw (leakGood false) leakSchedLaw leakBranchView false :=
  witness_dependent_good_breaks_composed_hiding

end LoadBearing

/-! ## 9. Component-A deployed rank certificate (citation)

The A seam `hsurjA : Function.Surjective maskA` (`im A = 𝒲`) that `aLeg_indep`
consumes is realised, for the deployed circle-matrix model, by
`AspisV5ComponentARankCompletion.width288_bundle_nonvacuous` — the width-288
coverage at the concrete identity schedule and split tower — under that file's own
residual hypotheses (schedule injectivity, nonzero weights, Rust encoder/layout
correspondence, QM31-tower correspondence, eq-side coverage premise).  That file
does **not** reduce the deployed A leg to a single residual; the coverage below is
cited, not re-derived here. -/

#check @AspisV5ComponentARankCompletion.width288_bundle_nonvacuous
#check @AspisV5ComponentARankCompletion.joint_coverage_nonvacuous

/-! ## Axiom audit -/

#print axioms composedView
#print axioms composedView_exact_congr
#print axioms composedView_merkle_close
#print axioms composed_iop_view_close_to_simulator
#print axioms composed_exact_legs_witness_free
#print axioms aLeg_indep
#print axioms bLeg_indep
#print axioms cLeg_indep
#print axioms sLeg_indep
#print axioms mtLeg_close
#print axioms capstone_adaptive_zk
#print axioms Toy.toyAssumptions
#print axioms Toy.toy_capstone
#print axioms Toy.toy_composed_bound
#print axioms transport_seam_load_bearing
#print axioms bcs_interface_load_bearing
#print axioms selection_good_public_load_bearing
#print axioms Toy.toyHonestView
#print axioms Toy.toySimView

end AspisV5HVZKReductionCapstone
