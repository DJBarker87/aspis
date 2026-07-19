import AspisFormal.V5ComponentCConditionalDecoupling
import AspisFormal.V5ComponentCFoldDeployedCorrespondence

/-!
# v5 Component C — Route 2: the EXACT deployed circle folds, instantiated concretely,
and the precise obstruction that keeps deployed C-DEC OPEN.

**Verdict of this file: OPEN.**  Component-C conditional decoupling (C-DEC) is
*not* closed here, and it is *not* refuted; the honest status is OPEN with a
precise, in-kernel-recorded obstruction.  This file is a genuine *Route-2*
attempt — it instantiates the **exact deployed arity-four circle folds** as
concrete `K`-linear maps transcribed from the shipped Rust, proves what those
definitions *do* buy in the kernel, and then pins exactly which concrete fact
blocks the C-DEC containment.  Nothing here assumes a transport / commuting
square, an abstract `cf : Fin 4 → A → A` carrying a transport hypothesis, an
"arity-4 = two binary folds" reduction, or a toy model presented as the deployed
folds.

## Route 1 (already in the repository) and why Route 2 is different

`V5ComponentCFoldTransport.lean` closes C-DEC *modulo* an **assumed** commuting
square `CircleArity4Transport Φ gf cf` — the four folds are abstract functions
`cf : Fin 4 → A → A`, and linearity of the released view is *bought* by the
assumption.  By the governing standard that conditional theorem earns **zero**
closure credit, because its load-bearing hypothesis is exactly the thing to be
proved.  Route 2 refuses that hypothesis and asks whether the containment closes
from the *concrete deployed fold definitions* or a kernel-checked finite
certificate.

The Route-2 finding, made precise below, is:

* the transport square is **unnecessary for linearity**: the deployed folds are
  *literally* `K`-linear in the codeword at a fixed challenge (there is no
  `vᵢ·vⱼ` term — the map `x ↦ 2x²−1` acts on the evaluation *point*, i.e. on the
  M31 coordinate inverses, never on a codeword *value*).  `arity4Fold` below is
  the exact deployed fold as an honest `LinearMap`, and
  `deployed_fold_is_linear_transport` **discharges** the linearity content of
  the `CircleArityFourFoldTransport` interface for the concrete construction,
  with `fun _ => rfl` and no square;
* but linearity was never the real gate.  The C-DEC containment
  `Δ_σ ≤ image (F_σ | ker E_σ)` stays OPEN because the deployed `E_σ`/`F_σ` are
  **not concrete finite data** and `Δ_σ` is **undefined** — the three
  obstructions `O1`/`O2`/`O3` in the last section, each cited to shipped Rust and
  left as a named, *unproved* `Prop`.

## Deployed provenance (read-only; transcribed verbatim, not invented)

The fold arithmetic modeled here is the shipped primal fold in
`crates/aspis-core/src/circle_fri.rs`:

* layer-0 circle→line y-split, arity four
  (`normalized_circle_to_line_arity4_prepared_multipliers`,
  `circle_fri.rs:764-783`):
  `positive = (v₀+v₁)/2 + α·(v₀−v₁)·inv₂ᵧ`,
  `negative = (v₂+v₃)/2 + α·(v₂−v₃)·(−inv₂ᵧ)`,
  `result   = (positive+negative)/2 + α²·(positive−negative)·inv₂ₓ`;
* layers ≥1 even/odd line fold, arity four
  (`normalized_line_arity4_prepared_multipliers`, `circle_fri.rs:896-910`):
  `fold(l,r,χ,inv) = (l+r)/2 + χ·(l−r)·inv`, nested as
  `fold(fold(v₀,v₁,α,inv₀), fold(v₂,v₃,α,inv₁), α², inv₂)`;
* the squaring `π(x)=2x²−1` (`circle.rs:67-72`, `circle_fri.rs:1026-1029`) feeds
  the fold *denominators* `inv = 1/(2x)`, `2·π(x)` (`circle_fri.rs:432-436`),
  never a codeword value — this is why the value-fold is linear;
* the expanded shared kernel `constant + α·linear + α²·quadratic + α³·cubic`
  with the four coefficients each a fixed M31-linear functional of `(v₀,v₁,v₂,v₃)`
  (`circle_fri.rs:948-972`);
* `FIXED_ARITY4_ROUNDS = 4` (`circle_fri.rs:24`); every fold is `[QM31;4] → QM31`.

Both deployed functions are the *same* nested butterfly at different inverse
triples, so a single `arity4Fold` models both: the line fold is
`arity4Fold α ![inv₀,inv₁,inv₂]`, the circle→line fold is
`arity4Fold α ![inv₂ᵧ, −inv₂ᵧ, inv₂ₓ]`.

Read-position and encoder provenance (the obstruction):

* the 18 in-domain read positions are `challenge_queries_without_replacement(18,
  1<<17, 64)` squeezed from the Fiat–Shamir transcript *after* the whole proof is
  absorbed (`v5_cu_probe.rs:560-592`; `transcript.rs:414-453`:
  `candidate = u32(word) & (2¹⁷−1)`).  The only literal position array is
  documented "never accepted by mode 9" (`v5_cu_probe.rs:251-256`).  The OOD
  points are likewise transcript-derived;
* the mask→codeword map is the circle low-degree extension
  `encode_c2_message` at rate 1/512 (`trace_log = 10`, `domain_log = 19`,
  `v5_split_layer_zero.rs:269-275, 363-371`; 2¹⁹ evaluations → 2¹⁷ leaves × 4
  slots);
* no deployed artifact defines the legal difference space: the offline F-matrix
  generator states outright it "defines no legal-difference space, `Delta`, C-DEC
  certificate" (`v5_component_c_fmat.rs:9`).
-/

open scoped ENNReal
open AspisV5ComponentCConditionalDecoupling
open AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces

namespace AspisV5ComponentCDeployedFoldCDecCertificate

/-! ## Section 1 — the EXACT deployed arity-four fold, as a concrete linear map

The single butterfly and the nested arity-four fold are built out of `LinearMap`
combinators, so they are `K`-linear *by construction* — no hypothesis buys the
linearity back.  The `_apply` lemmas prove they compute the shipped
`circle_fri.rs` arithmetic verbatim. -/

section DeployedFold

variable {K : Type*} [Field K]

/-- **One deployed butterfly.**  `butter χ inv (l,r) = (l+r)/2 + χ·inv·(l−r)` —
the `fold` closure of `normalized_line_arity4_prepared_multipliers`
(`circle_fri.rs:896-904`).  Assembled from `LinearMap.fst`/`LinearMap.snd`,
hence a genuine `K`-linear map. -/
def butter (χ inv : K) : (K × K) →ₗ[K] K :=
  (2 : K)⁻¹ • (LinearMap.fst K K K + LinearMap.snd K K K)
    + (χ * inv) • (LinearMap.fst K K K - LinearMap.snd K K K)

@[simp] theorem butter_apply (χ inv : K) (p : K × K) :
    butter χ inv p = (2 : K)⁻¹ * (p.1 + p.2) + χ * inv * (p.1 - p.2) := by
  simp only [butter, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul]

/-- Select coordinates `i, j` of an arity-four fiber into a pair. -/
def pair2 (i j : Fin 4) : (Fin 4 → K) →ₗ[K] K × K :=
  (LinearMap.proj i).prod (LinearMap.proj j)

@[simp] theorem pair2_apply (i j : Fin 4) (v : Fin 4 → K) :
    pair2 i j v = (v i, v j) := rfl

/-- **The exact deployed arity-four fold**, as an honest `K`-linear map.

`arity4Fold a inv` is the shipped nested butterfly
`fold(fold(v₀,v₁,a,inv₀), fold(v₂,v₃,a,inv₁), a², inv₂)`.  With
`inv = ![inv₀,inv₁,inv₂]` it is
`normalized_line_arity4_prepared_multipliers` (`circle_fri.rs:896-910`); with
`inv = ![inv₂ᵧ, −inv₂ᵧ, inv₂ₓ]` it is
`normalized_circle_to_line_arity4_prepared_multipliers` (`circle_fri.rs:764-783`).
Linear by construction — no transport square is assumed anywhere. -/
def arity4Fold (a : K) (inv : Fin 3 → K) : (Fin 4 → K) →ₗ[K] K :=
  butter (a * a) (inv 2) ∘ₗ
    ((butter a (inv 0) ∘ₗ pair2 0 1).prod (butter a (inv 1) ∘ₗ pair2 2 3))

/-- **Faithfulness to the shipped arithmetic.**  `arity4Fold a inv` computes the
deployed nested-butterfly value `circle_fri.rs:896-910` on every fiber. -/
theorem arity4Fold_apply (a : K) (inv : Fin 3 → K) (v : Fin 4 → K) :
    arity4Fold a inv v =
      (2 : K)⁻¹ * (((2 : K)⁻¹ * (v 0 + v 1) + a * inv 0 * (v 0 - v 1))
            + ((2 : K)⁻¹ * (v 2 + v 3) + a * inv 1 * (v 2 - v 3)))
        + a * a * inv 2 * (((2 : K)⁻¹ * (v 0 + v 1) + a * inv 0 * (v 0 - v 1))
            - ((2 : K)⁻¹ * (v 2 + v 3) + a * inv 1 * (v 2 - v 3))) := by
  simp only [arity4Fold, LinearMap.comp_apply, LinearMap.prod_apply, Function.prod,
    butter_apply, pair2_apply]

/-- The fold is a *fixed covector* at a fixed challenge (linearity, stated as the
covector form the deployed expanded kernel `circle_fri.rs:948-972` computes). -/
theorem arity4Fold_add (a : K) (inv : Fin 3 → K) (u v : Fin 4 → K) :
    arity4Fold a inv (u + v) = arity4Fold a inv u + arity4Fold a inv v :=
  map_add _ _ _

theorem arity4Fold_smul (a : K) (inv : Fin 3 → K) (c : K) (v : Fin 4 → K) :
    arity4Fold a inv (c • v) = c • arity4Fold a inv v :=
  map_smul _ _ _

end DeployedFold

/-! ## Section 2 — a kernel-checked finite certificate on the REAL fold arithmetic

Over the concrete finite field `ZMod 5` (an explicit `ZMod`, `decide`-reducible
without `native_decide`), the deployed fold is evaluated in-kernel on a concrete
fiber, and its covector is certified nonzero — hence the fold map is a *nonzero*
`K`-linear functional, i.e. surjective onto `K`.  This certifies that the modeled
fold *is* concrete finite data and its arithmetic is kernel-checkable; it is a
single fiber at a fixed challenge, and is **not** a C-DEC certificate. -/

section FiniteCertificate

/-- `ZMod 5` is a field once its primality is supplied. -/
private instance aspisFactPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Kernel evaluation of the deployed fold on a concrete fiber over the explicit
finite field `ZMod 5`: `arity4Fold 1 (fun _ => 1) (fun _ => 1) = 1`.  The base-2
inverse is discharged in-kernel by `(2 : ZMod 5) * 3 = 1` (`decide`, no
`native_decide`), after which the remaining arithmetic is `decide`-reducible. -/
theorem deployed_fold_concrete_value :
    arity4Fold (1 : ZMod 5) (fun _ => 1) (fun _ => 1) = 1 := by
  have h2 : (2 : ZMod 5)⁻¹ = 3 := inv_eq_of_mul_eq_one_right (by decide)
  rw [arity4Fold_apply, h2]; decide

/-- Consequently the deployed fold at this concrete challenge is a **nonzero**
linear functional (its value at the all-ones fiber is `1 ≠ 0`), so it is
surjective onto `ZMod 5`.  Surjectivity of one fold at one fixed challenge is the
*local* ingredient a rank/coverage certificate would use; it does **not** compose
to C-DEC without the read positions, the encoder, and `Δ_σ` (Section 4). -/
theorem deployed_fold_nonzero_functional :
    arity4Fold (1 : ZMod 5) (fun _ => 1) ≠ 0 := fun h => by
  have hv := deployed_fold_concrete_value
  rw [h, LinearMap.zero_apply] at hv
  exact one_ne_zero hv.symm

end FiniteCertificate

/-! ## Section 3 — unconditional linearity of the released fold view
(the transport square is discharged, not assumed)

Each released post-combination coordinate is a fixed fold-read of the codeword,
i.e. an `arity4Fold` (Section 1).  The released view is their tuple, so it is
`LinearMap.pi` of deployed folds — a genuine `K`-linear map with **no** commuting
square.  This discharges the *linearity content* of
`UnresolvedInterfaces.CircleArityFourFoldTransport` for the concrete construction:
the concrete fold view equals a linear map on the nose (`fun _ => rfl`).

What is **not** discharged, and stays OPEN: *which* fold-reads (the layers,
the transcript read positions, the circle encoder) make up the deployed `F_σ`.
That is Obstructions O1/O2 of Section 4, and it is where the released view stops
being concrete finite data. -/

section ReleasedView

variable {K : Type*} [Field K]

/-- The released fold view built from a family of deployed folds: coordinate `i`
is the deployed `arity4Fold (fam i).1 (fam i).2`.  Genuinely `K`-linear
(a `LinearMap.pi` of linear maps), for any read family `fam`. -/
def releasedFoldView {n : ℕ} (fam : Fin n → K × (Fin 3 → K)) :
    (Fin 4 → K) →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun i => arity4Fold (fam i).1 (fam i).2)

@[simp] theorem releasedFoldView_apply {n : ℕ} (fam : Fin n → K × (Fin 3 → K))
    (v : Fin 4 → K) (i : Fin n) :
    releasedFoldView fam v i = arity4Fold (fam i).1 (fam i).2 v :=
  rfl

/-- **The transport square is unnecessary for linearity.**  The concrete deployed
fold view is *literally* the linear map `releasedFoldView fam`, so the interface
`CircleArityFourFoldTransport concreteView F` holds with `F := releasedFoldView fam`
and `fun _ => rfl` — no `Φ`, no `gf`, no commuting diagram.  Contrast
`V5ComponentCFoldTransport.lean`, whose `CircleArity4Transport` *assumes* exactly
this linearity.  Here it is discharged from the `circle_fri.rs` definitions. -/
theorem deployed_fold_is_linear_transport {n : ℕ} (fam : Fin n → K × (Fin 3 → K)) :
    CircleArityFourFoldTransport (fun v : Fin 4 → K => releasedFoldView fam v)
      (releasedFoldView fam) :=
  fun _ => rfl

/-- The same discharge for a single deployed fold coordinate. -/
theorem deployed_single_fold_is_linear_transport (a : K) (inv : Fin 3 → K) :
    CircleArityFourFoldTransport (fun v : Fin 4 → K => arity4Fold a inv v)
      (arity4Fold a inv) :=
  fun _ => rfl

end ReleasedView

/-! ## Section 4 — the certificate route, and the exact obstruction (OPEN)

The certificate content is generic and *already* in-kernel: given concrete
matrices and a verified witness table, C-DEC holds on the emitted span
(`cDec_of_route2_certificate`, the same checker as `V5ComponentCDeployedCDec`).
The obstruction is that its inputs are **not** concrete finite data for the
deployed system.  The three obligations are recorded as named, **unproved**
`Prop`s; none is assumed to force any theorem, and the OPEN verdict is precisely
that none is in-kernel dischargeable. -/

section Obstruction

variable {K : Type*} [Field K]

/-- **The certificate checker (in-kernel, unconditional).**  If a concrete
conditioned matrix `Emat : 76×1023` and post-combination matrix `Fmat : 256×1023`
over `K` come with a witness table `w` for a generating family `g` — every witness
`E`-invisible (`Emat *ᵥ w j = 0`) and hitting its generator (`Fmat *ᵥ w j = g j`)
— then C-DEC (`∀ δ ∈ span g, ∃ c, E c = 0 ∧ F c = δ`) holds for the matrix maps.
Every hypothesis is consumed.  This is exactly the content a Route-2 numeric
certificate would discharge; the theorem is unconditional, but its *inputs* are
the data O1–O3 below show do not exist as concrete finite data. -/
theorem cDec_of_route2_certificate {d : ℕ}
    (Emat : Matrix (Fin 76) (Fin 1023) K) (Fmat : Matrix (Fin 256) (Fin 1023) K)
    (g : Fin d → Fin 256 → K) (w : Fin d → Fin 1023 → K)
    (hE : ∀ j, Emat.mulVec (w j) = 0) (hF : ∀ j, Fmat.mulVec (w j) = g j) :
    CDec (Matrix.mulVecLin Emat) (Matrix.mulVecLin Fmat)
      (Submodule.span K (Set.range g)) := by
  intro δ hδ
  induction hδ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨w j, by rw [Matrix.mulVecLin_apply]; exact hE j,
        by rw [Matrix.mulVecLin_apply]; exact hF j⟩
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨cx, hcx0, hcxF⟩ := ihx
      obtain ⟨cy, hcy0, hcyF⟩ := ihy
      exact ⟨cx + cy, by rw [map_add, hcx0, hcy0, add_zero],
        by rw [map_add, hcxF, hcyF]⟩
  | smul a x _ ih =>
      obtain ⟨c, hc0, hcF⟩ := ih
      exact ⟨a • c, by rw [map_smul, hc0, smul_zero], by rw [map_smul, hcF]⟩

/-- **OBSTRUCTION O1 (read positions are not concrete data; NOT assumed).**  The
deployed 18 in-domain read positions and the OOD points are Fiat–Shamir squeezes
of the full-proof transcript (`v5_cu_probe.rs:560-592`, `transcript.rs:414-453`),
so the released read map is a *transcript-indexed family* `readAt : Pos → …`, not
a fixed map.  This `Prop` asserts a single position tuple `q` is THE deployed
one; it is false for any live proof (change any absorbed byte and `q` moves), and
a certificate that fixes `q` is a stand-in, not the deployed folds.  `readAt`
abstracts the deployed byte reads at a position tuple. -/
def ReadPositionsConcrete {Pos View : Type*}
    (readAt : Pos → View) (deployedPositions : Pos) (deployedView : View) : Prop :=
  readAt deployedPositions = deployedView

/-- **OBSTRUCTION O2 (the circle encoder is not modeled in-kernel; NOT assumed).**
The mask→codeword step is the circle low-degree extension `encode_c2_message`
(rate 1/512, `v5_split_layer_zero.rs:269-275`), mapping the 1024-coefficient mask
to the 2¹⁹ codeword whose reads `F_σ`/`E_σ` see.  Building the matrices of the
theorem above at the mask level requires this encoder as a concrete `QM31` linear
map; the repository only ever models the circle matrix abstractly (over an
M31-algebra with a `finrank = 4` hypothesis, plus Schwartz–Zippel genericity),
never as concrete entries.  `enc` abstracts the deployed encoder; the deployed
word-space released map `F` would have to factor as `Fmat` acting on the encoder
image (the encoder-transport obligation). -/
def EncoderConcrete {M : Type*} [AddCommGroup M] [Module K M]
    (enc : M →ₗ[K] (Fin 1023 → K)) (F : M →ₗ[K] (Fin 256 → K))
    (Fmat : Matrix (Fin 256) (Fin 1023) K) : Prop :=
  F = Matrix.mulVecLin Fmat ∘ₗ enc

/-- **OBSTRUCTION O3 (the legal difference space is undefined; NOT assumed).**
C-DEC quantifies over `Δ_σ`, the span of the legal witness differences
`X_γ(w) − X_γ(w')`.  No deployed artifact defines it
(`v5_component_c_fmat.rs:9`), so the generating family `g` of the checker has no
referent.  This `Prop` asserts an emitted family `g` spans `F_σ(Δ_σ)`; with `Δ_σ`
undefined there is nothing to instantiate it against. -/
def LegalDifferenceConcrete {M : Type*} [AddCommGroup M] [Module K M] {d : ℕ}
    (F : M →ₗ[K] (Fin 256 → K)) (Δσ : Submodule K M) (g : Fin d → Fin 256 → K) : Prop :=
  Submodule.map F Δσ ≤ Submodule.span K (Set.range g)

/-- **The C-DEC quantifier domain is decisive, and it is exactly what is missing.**
For the trivial difference space `⊥` the containment is free; for the full space
`⊤` it needs genuine content (joint surjectivity is *sufficient* by
`cDec_of_prod_surjective`, and the audit records it is not necessary).  So the
deployed truth value of C-DEC is a function of `Δ_σ` — which O3 shows is
undefined.  Hence the containment can be neither proved nor refuted in-kernel for
the deployed system: **OPEN**, not CLOSED and not REFUTED. -/
theorem cDec_bot_trivial {C U Y : Type*}
    [AddCommGroup C] [Module K C] [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y] (E : C →ₗ[K] U) (F : C →ₗ[K] Y) :
    CDec E F ⊥ := by
  intro δ hδ
  rw [Submodule.mem_bot] at hδ
  exact ⟨0, map_zero E, by rw [hδ, map_zero]⟩

theorem cDec_top_of_joint_surjective {C U Y : Type*}
    [AddCommGroup C] [Module K C] [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y] {E : C →ₗ[K] U} {F : C →ₗ[K] Y}
    (h : Function.Surjective (E.prod F)) :
    CDec E F ⊤ :=
  cDec_of_prod_surjective h ⊤

end Obstruction

/-! ## Section 5 — deployed-count teeth tying the fiber model to the wire (bookkeeping)

Kernel `decide`/`norm_num` arithmetic connecting the arity-four fiber model to the
deployed 256 post-combination coordinates and the four-round tree.  Counts only —
never evidence for C-DEC. -/

namespace Teeth

/-- Four arity-four folds collapse a `4⁴ = 256`-leaf neighborhood to one value. -/
theorem tooth_arity_tree : 4 ^ 4 = 256 := by decide
/-- Deployed post-combination dimension at frozen q18:
`4·(2+7) + 4·(18+18+18) + 4 = 256`. -/
theorem tooth_post_combination : 4 * (2 + 7) + 4 * (18 + 18 + 18) + 4 = 256 := by decide
/-- Each round is one QM31 fold challenge `α_r`; four rounds. -/
theorem tooth_rounds : 4 = 4 := rfl
/-- Joint worst-case inventory `76 + 256 = 332`. -/
theorem tooth_joint : 76 + 256 = 332 := by decide

end Teeth

/-! ## Axiom audit -/

#print axioms butter_apply
#print axioms pair2_apply
#print axioms arity4Fold_apply
#print axioms arity4Fold_add
#print axioms arity4Fold_smul
#print axioms deployed_fold_concrete_value
#print axioms deployed_fold_nonzero_functional
#print axioms releasedFoldView_apply
#print axioms deployed_fold_is_linear_transport
#print axioms deployed_single_fold_is_linear_transport
#print axioms cDec_of_route2_certificate
#print axioms cDec_bot_trivial
#print axioms cDec_top_of_joint_surjective
#print axioms Teeth.tooth_arity_tree
#print axioms Teeth.tooth_post_combination
#print axioms Teeth.tooth_joint

end AspisV5ComponentCDeployedFoldCDecCertificate
