import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# v5 Component C, deployed C-DEC: blocker report and certificate checker

**Verdict: NOT CERTIFIED.**  No concrete deployed `E_σ`/`F_σ` map exists
against which the audit's `(C-DEC)` could be proved as a statement about the
shipped system, and Component C is explicitly marked rejected in the only
code paths that exercise it.  This file therefore certifies nothing about
Component C.  It records the exact blockers as named interface `Prop`s
(definitions, never assumptions) and proves the small in-kernel checker
theorems that will consume a future numeric certificate.  The hypothesis
used throughout is EXACTLY the audit's `(C-DEC)` —
`∀ δ ∈ Δ, ∃ c, E c = 0 ∧ F c = δ` — via `CDec`/`CDecAudit` from
`AspisFormal.V5ComponentCConditionalDecoupling`.  Nothing here weakens it
to, or replaces it by, surjectivity of `E`, of `F`, or of `(E, F)`; the
certificate shape below is proved *equivalent* to C-DEC on the emitted span
(`exists_frozenQ18_certificate_iff_cDec`), not stronger.

## Evidence for the verdict (repository state as read for this report)

Status markers, quoted from the sources this report is bound to:

* `crates/aspis-prover/src/v5_c_mask.rs:1` — "Provisional v5 component (C)";
  lines 9–12: the module "establishes only the row encoding and its four
  public linear claims", not complete-view hiding, Fiat–Shamir ordering, or
  Rust-to-Lean correspondence; it is feature-gated (`v5-mask`) and not
  called by the v4 prover.
* `crates/aspis-prover/Cargo.toml:13` — `v5-mask = []`, with lines 11–12:
  "Default OFF.  Gates a new module that is not referenced by any v4 code
  path."
* `programs/aspis-verifier/src/v5_cu_probe.rs:36–38` — the mode-9 composite
  path "remains a CU artefact, not a security-approved v5 proof: the
  relation payload is a transparent zero witness and Component C remains a
  rejected design."
* `crates/aspis-prover/src/v5_real_host_proof.rs:10–11` — "Component C
  remains the explicitly rejected full-kernel CU candidate, so an artefact
  from this module is an integration/measurement result only."
* `xtask/src/v5_cu_probe.rs:532–535` — the fixture generator itself labels
  the sample "provisional real v5 Component C".
* `programs/aspis-verifier/Cargo.toml:12` — the deployed program builds with
  `default = ["spend-production"]`, whose minimal dispatch accepts only the
  eight production wire tags (lines 22–24); the `v5-cu-probe` feature
  (line 33) is local-validator-only and "deliberately incompatible with
  `spend-production`" (line 31).  No Component-C code is reachable from the
  deployed entrypoint.
* `results/spend/v5_component_c_design_audit.md` — "Status: design/result
  note only" (line 3); Component C is a "conditional GO" (line 238) with
  five gate items open (lines 242–252); the closing status is "full-fold
  conditional decoupling remains open" (lines 254–256).  Gate item 1 —
  "instantiate the exact 332-row worst-case joint map and test `(C-DEC)` on
  the frozen q18 schedule" (lines 242–243) — has been executed nowhere: the
  string `C-DEC` occurs in no Rust source in the workspace, and no module
  instantiates the joint map.  The only nearby released-view rank fixture,
  `crates/aspis-prover/src/v5_b_structured_rank.rs:313–382`, measures the
  *alternative* "drop C, use B's 255 pads" map (released-view rank 75 of
  76 on the frozen schedule) — a different map, recorded by the audit
  (lines 224–231) as "not a universal replacement for C".

What DOES exist — executable pieces (host-side, feature-gated, CU
measurement only) from which a generator must assemble the certificate:

* Mask space and free-coordinate bijection: `ℓ` is the atomic-v3
  copy-inactive functional and `V5ComponentCLane::encode_free_coordinates`
  is the explicit linear bijection `K^1023 → ker ℓ` with derived pivot of
  coefficient one (`crates/aspis-prover/src/v5_c_mask.rs:44–53, 88–104`;
  round-trip tests at lines 155–166 and 193–206).
* `E_σ` rows 0–71 (never emitted as a matrix): the C helper codeword
  `CircleEncoder::encode_c2_message` of the mask word
  (`crates/aspis-prover/src/v5_split_layer_zero.rs:269–275`, packed at
  294–311) at the 72 layer-zero positions of the 18 transcript-derived q18
  fibres × 4 slots (`crates/aspis-prover/src/v5_real_host_proof.rs:766–768`),
  released through the five-section private openings (same file, 769–816).
* `E_σ` rows 72–74: the three MLE claims of C2 lane 18 at `z`,
  `successor(z)`, `xor12(z)` (`v5_split_layer_zero.rs:193–197`).
* `E_σ` row 75: the structured terminal claim
  `⟨v5_structured_terminal_covector(z), C⟩`
  (`v5_split_layer_zero.rs:153–171` and `198–205`).
* `F_σ` rows (never emitted as a matrix; the C mask enters every one of
  them with lane-batching coefficient `γ^18`: helper 2 of
  `gamma_combine_split_codewords`, `v5_real_host_proof.rs:493–506`,
  matching `prepare_generic16`,
  `programs/aspis-verifier/src/v5_cu_probe.rs:624–635`, and the audit's
  non-cancellation tooth, audit lines 187–213):
  rows 0–35 are the four rounds × (2 OOD + 7 relation-sumcheck
  coefficients) (`v5_real_host_proof.rs:665–712`); rows 36–251 are the
  opened later-layer values, `4·(n₁+n₂+n₃)` with `n₁ = n₂ = n₃ = 18` on the
  collision-free frozen q18 fixture (`v5_real_host_proof.rs:713–733`);
  rows 252–255 are the final four coefficients
  (`v5_real_host_proof.rs:735–742`).
* `Δ_σ` — the legal witness-difference space, the quantifier domain of
  C-DEC — has NO code artifact of any kind.  Until a generator pins a
  spanning family for `F_σ(Δ_σ)`, the deployed C-DEC statement cannot even
  be posed, let alone proved.

## Why this is a blocker report and not a proof

Deployed `(C-DEC)` is a statement about (i) two specific matrices over
`QM31` that no artifact emits, (ii) a legal-difference space that no
artifact defines, and (iii) a design whose own integration comments call it
rejected, gated off every production build.  Items (i) and (ii) are the
missing mathematical inputs; item (iii) means the numbers may still change
under review.  Proving the abstract theorems against stand-in maps and
calling the result "deployed C-DEC" would convert a CU fixture into a
security claim, which the audit forbids.  Accordingly, no theorem below
asserts C-DEC for any concrete map, and this file adds no axioms.

## The certificate a generator must emit (shape, field, size)

Field: `QM31`, the degree-four extension of `M31 = ℤ/(2³¹−1)`; one element
is 4 little-endian `u32` limbs in canonical (fully reduced) form, 16 bytes
(`QM31::from_le_bytes` rejects non-canonical limbs).  Row and column
enumerations are pinned to the serialization orders cited above; mask
coordinates are the 1023 free coordinates, transported into `ker ℓ` by the
deployed encoder bijection.  All data are for the FROZEN q18 schedule only;
universal or Fiat–Shamir high-probability statements additionally need the
audit's gate items 2 and 6 (adversarial schedules) and the parent file's
`UnresolvedInterfaces` (ordering, authentication, sampler uniformity,
serialization completeness, fold transport), none of which the certificate
replaces.

1. `Emat : 76 × 1023` over `QM31` — the conditioned rows on free
   coordinates, in the order: 72 layer-zero, 3 MLE, 1 terminal.
   `76·1023·16 = 1,243,968` bytes (`CertificateShape.e_matrix_bytes`).
2. `Fmat : 256 × 1023` over `QM31` — the frozen-q18 post-combination rows
   on free coordinates: 36 OOD/relation-sumcheck, 216 later-layer, 4 final.
   `256·1023·16 = 4,190,208` bytes (`CertificateShape.f_matrix_bytes`).
   The `γ^18` batching factor may be folded into `Fmat` or omitted, as long
   as the choice is pinned: for `γ ≠ 0` the parent file's `cDec_smul` and
   `cDec_iff_J` show C-DEC is invariant under that convention.
3. `g : d × 256` over `QM31` — a family whose span contains `F_σ(Δ_σ)`.
   `d ≤ 256` always suffices (`exists_spanning_family_card_le`);
   `4,096·d` bytes.
4. `w : d × 1023` over `QM31` — for each generator, a witness mask in free
   coordinates; `16,368·d` bytes (`CertificateShape.per_generator_bytes`).

Kernel-checkable content (`FrozenQ18Certificate`): `Emat *ᵥ w j = 0` and
`Fmat *ᵥ w j = g j` for every `j` — `d·(76+256)` dot products of length
1023.  Worst-case total certificate size ≈ 10.7 MB
(`CertificateShape.max_certificate_bytes`).

## The checker theorems proved below

* `cDec_anti`, `cDec_comp` — C-DEC transport: antitone in `Δ`, and pullback
  along any linear parametrisation (such as the free-coordinate encoder).
* `cDec_of_generator_witnesses` — certificate soundness: witnesses for a
  spanning family yield exactly `CDec` for the span.
* `exists_generator_witnesses_of_cDec` — certificate completeness: the
  certificate shape is equivalent to C-DEC on the span, so demanding it is
  not a covert full-rank strengthening.
* `frozenQ18_cDec_of_certificate`, `exists_frozenQ18_certificate_iff_cDec`
  — the matrix forms at the audit's dimensions (76 / 256 / 1023).
* `cDecAudit_of_frozen_certificate` — the assembled path: certificate plus
  the named blocker interfaces imply the audit's `CDecAudit` for the
  deployed word-space maps.
* `frozen_certificate_yields_full_fold_decoupling` — composition with the
  parent headline: the same inputs already give the exact
  witness-independent conditional law; no further Lean machinery is
  missing.  The ONLY missing inputs are the blocker artifacts.

## The named blockers (`DeployedBlockers`, definitions only, nowhere assumed)

* B1 `EMatrixFaithful` — the emitted `Emat` agrees row-by-row with the
  deployed Rust evaluation of the 76 conditioned coordinates on free
  coordinates.  UNMET: no artifact emits `Emat`.
* B2 `FMatrixFaithful` — the emitted `Fmat` agrees row-by-row with the
  deployed post-combination evaluation; this includes the claim that the
  fixed-schedule evaluation IS linear in the mask.  UNMET: no artifact
  emits `Fmat`, and the later-layer row count is transcript-dependent.
* B3 `DeltaImageCovered` — the emitted generators span at least
  `F_σ(Δ_σ)` for a pinned definition of the legal difference space.
  UNMET: `Δ_σ` has no code artifact at all.
* B4 `EncoderIntertwines` — the matrices are the word-space maps
  transported along the deployed free-coordinate encoder.  Surjectivity of
  the deployed encoder is true (`v5_c_mask.rs` round-trip tests) but is
  deliberately not required: witnesses found through any linear
  parametrisation are sound (`cDec_comp`).  UNMET: no cross-language
  correspondence exists (parent `UnresolvedInterfaces`).

Until a generator emits the certificate, B1–B4 are discharged against the
real artifacts, and the design stops being marked rejected, the honest
status of deployed Component-C decoupling remains the audit's: OPEN.
-/

open AspisV5ComponentCConditionalDecoupling

namespace AspisV5ComponentCDeployedCDec

/-! ## C-DEC transport lemmas

Small reusable steps for the checker.  Each conclusion is literally `CDec`;
none introduces or consumes any surjectivity hypothesis. -/

section CDecTransport

variable {K : Type*} [Field K] {C C' U Y : Type*}
  [AddCommGroup C] [Module K C] [AddCommGroup C'] [Module K C']
  [AddCommGroup U] [Module K U] [AddCommGroup Y] [Module K Y]

/-- C-DEC is antitone in the legal-difference space: witnesses for a larger
`Δ` restrict to any smaller one.  Used to pass from the emitted generator
span down to the pinned `F_σ(Δ_σ)`. -/
theorem cDec_anti {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {Δ Δ' : Submodule K Y}
    (hle : Δ' ≤ Δ) (h : CDec E F Δ) : CDec E F Δ' :=
  fun δ hδ => h δ (hle hδ)

/-- C-DEC transports along ANY linear parametrisation of (a subfamily of)
the mask space: a witness found in the parametrising space maps to a
witness in the mask space.  No surjectivity of `e` is needed — searching a
subfamily is only harder, never unsound.  This is the bridge from
free-coordinate matrices to the `ker ℓ` statement. -/
theorem cDec_comp {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {Δ : Submodule K Y}
    (e : C' →ₗ[K] C) (h : CDec (E ∘ₗ e) (F ∘ₗ e) Δ) : CDec E F Δ := by
  intro δ hδ
  obtain ⟨c', h0, hc⟩ := h δ hδ
  exact ⟨e c', h0, hc⟩

/-- **Certificate soundness.**  If every generator `g i` of the difference
space has a witness `w i` that is `E`-invisible (`E (w i) = 0`) and hits it
exactly (`F (w i) = g i`), then `CDec E F (span (range g))` holds — the
audit's C-DEC, verbatim, for the span.  The proof is the containment form
`cDec_iff_le_map_ker`: `{δ | ∃ c, E c = 0 ∧ F c = δ}` is the submodule
`map F (ker E)`, so it suffices that it contain the generators. -/
theorem cDec_of_generator_witnesses {ι : Type*}
    (E : C →ₗ[K] U) (F : C →ₗ[K] Y) (g : ι → Y) (w : ι → C)
    (hE : ∀ i, E (w i) = 0) (hF : ∀ i, F (w i) = g i) :
    CDec E F (Submodule.span K (Set.range g)) := by
  rw [cDec_iff_le_map_ker, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  show g i ∈ Submodule.map F (LinearMap.ker E)
  exact Submodule.mem_map.mpr ⟨w i, LinearMap.mem_ker.mpr (hE i), hF i⟩

/-- **Certificate completeness.**  Conversely, if C-DEC holds for the span
then a witness table for the generators exists.  Together with
`cDec_of_generator_witnesses` this shows the requested certificate shape is
*equivalent* to C-DEC on the span — demanding it does not smuggle in
independent surjectivity of `E`, `F`, or the joint map. -/
theorem exists_generator_witnesses_of_cDec {ι : Type*}
    {E : C →ₗ[K] U} {F : C →ₗ[K] Y} {g : ι → Y}
    (h : CDec E F (Submodule.span K (Set.range g))) :
    ∃ w : ι → C, (∀ i, E (w i) = 0) ∧ ∀ i, F (w i) = g i := by
  choose w h0 hFw using fun i => h (g i) (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨w, h0, hFw⟩

end CDecTransport

/-! ## The frozen-q18 certificate shape and its checker

The audit's dimensions: 1023 free mask coordinates, 76 conditioned rows,
256 post-combination rows on the collision-free frozen q18 fixture. -/

section FrozenQ18

variable {K : Type*} [Field K]

/-- **The exact numeric certificate a Rust/Python generator must emit** for
the frozen q18 schedule (row orders and serialization pinned in the module
docstring): matrices `Emat` (76×1023) and `Fmat` (256×1023), a generator
family `g` for (a superset of) `F_σ(Δ_σ)`, and one witness `w j` in free
coordinates per generator with `Emat *ᵥ w j = 0` and `Fmat *ᵥ w j = g j`.
This `Prop` is the kernel-checkable content: `d·(76+256)` dot products of
length 1023. -/
def FrozenQ18Certificate {d : ℕ}
    (Emat : Matrix (Fin 76) (Fin 1023) K) (Fmat : Matrix (Fin 256) (Fin 1023) K)
    (g : Fin d → Fin 256 → K) (w : Fin d → Fin 1023 → K) : Prop :=
  (∀ j, Emat.mulVec (w j) = 0) ∧ ∀ j, Fmat.mulVec (w j) = g j

/-- **The frozen-q18 checker.**  A verified certificate yields exactly
`CDec` — the audit's `∀ δ ∈ Δ, ∃ c, E c = 0 ∧ F c = δ` — for the matrix
maps on the emitted generator span. -/
theorem frozenQ18_cDec_of_certificate {d : ℕ}
    {Emat : Matrix (Fin 76) (Fin 1023) K} {Fmat : Matrix (Fin 256) (Fin 1023) K}
    {g : Fin d → Fin 256 → K} {w : Fin d → Fin 1023 → K}
    (hcert : FrozenQ18Certificate Emat Fmat g w) :
    CDec (Matrix.mulVecLin Emat) (Matrix.mulVecLin Fmat)
      (Submodule.span K (Set.range g)) :=
  cDec_of_generator_witnesses _ _ g w
    (fun j => by rw [Matrix.mulVecLin_apply]; exact hcert.1 j)
    (fun j => by rw [Matrix.mulVecLin_apply]; exact hcert.2 j)

/-- The certificate shape is exactly C-DEC on the span, in both directions:
a witness table exists iff `CDec` holds for the matrix maps.  This pins the
requested artifact as neither weaker nor stronger than the target. -/
theorem exists_frozenQ18_certificate_iff_cDec {d : ℕ}
    {Emat : Matrix (Fin 76) (Fin 1023) K} {Fmat : Matrix (Fin 256) (Fin 1023) K}
    {g : Fin d → Fin 256 → K} :
    (∃ w : Fin d → Fin 1023 → K, FrozenQ18Certificate Emat Fmat g w)
      ↔ CDec (Matrix.mulVecLin Emat) (Matrix.mulVecLin Fmat)
          (Submodule.span K (Set.range g)) := by
  constructor
  · rintro ⟨w, hcert⟩
    exact frozenQ18_cDec_of_certificate hcert
  · intro h
    obtain ⟨w, h0, hFw⟩ := exists_generator_witnesses_of_cDec h
    exact ⟨w, fun j => by rw [← Matrix.mulVecLin_apply]; exact h0 j,
      fun j => by rw [← Matrix.mulVecLin_apply]; exact hFw j⟩

/-- A generator family of size `d ≤ n` always suffices for any submodule of
`K^n` (in the certificate, `n = 256`): the generator is never forced to emit
more than 256 rows of `g`.  Bookkeeping for the certificate size bound; not
evidence for C-DEC. -/
theorem exists_spanning_family_card_le {n : ℕ} (W : Submodule K (Fin n → K)) :
    ∃ (d : ℕ) (g : Fin d → Fin n → K), d ≤ n ∧
      Submodule.span K (Set.range g) = W := by
  refine ⟨Module.finrank K W, fun i => (Module.finBasis K W i : Fin n → K), ?_, ?_⟩
  · have h := W.finrank_le
    rwa [Module.finrank_fin_fun] at h
  · show Submodule.span K (Set.range (W.subtype ∘ ⇑(Module.finBasis K W))) = W
    rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq,
      Submodule.map_top, Submodule.range_subtype]

end FrozenQ18

/-! ## The named blockers: interfaces that no artifact can currently satisfy

Definitions only.  None is assumed anywhere in this file; each names the
precise obligation a future artifact must discharge, in the style of the
parent file's `UnresolvedInterfaces`. -/

namespace DeployedBlockers

/-- **BLOCKER B1 (unmet): faithfulness of the emitted `E` matrix.**
`rustE i v` abstracts the deployed Rust evaluation of conditioned row `i`
(rows 0–71: `encode_c2_message` of the mask at the 72 frozen q18 layer-zero
positions; rows 72–74: the three MLE claims; row 75: the structured
terminal claim) on the mask with free coordinates `v`.  The obligation is
row-by-row agreement with the emitted matrix.  No artifact currently emits
`Emat`, so this `Prop` cannot yet be instantiated, let alone proved. -/
def EMatrixFaithful {K : Type*} [Field K]
    (rustE : Fin 76 → (Fin 1023 → K) → K)
    (Emat : Matrix (Fin 76) (Fin 1023) K) : Prop :=
  ∀ (i : Fin 76) (v : Fin 1023 → K), rustE i v = Emat.mulVec v i

/-- **BLOCKER B2 (unmet): faithfulness of the emitted `F` matrix.**
`rustF i v` abstracts the deployed evaluation of post-combination row `i`
(rows 0–35: four rounds' OOD and relation-sumcheck coefficients; rows
36–251: the opened later-layer values on the collision-free frozen q18
fixture; rows 252–255: the final coefficients) of the mask's contribution.
Agreement with a matrix simultaneously asserts that the fixed-schedule
evaluation is linear in the mask.  No artifact emits `Fmat`, and the
later-layer row count is transcript-dependent, so this `Prop` cannot yet be
instantiated. -/
def FMatrixFaithful {K : Type*} [Field K]
    (rustF : Fin 256 → (Fin 1023 → K) → K)
    (Fmat : Matrix (Fin 256) (Fin 1023) K) : Prop :=
  ∀ (i : Fin 256) (v : Fin 1023 → K), rustF i v = Fmat.mulVec v i

/-- **BLOCKER B3 (unmet): coverage of the legal difference space.**  The
emitted generators must span at least `F_σ(Δ_σ)` — the audit's legal
witness-difference space transported into the view space.  `Δ_σ` has no
code artifact of any kind today; until it is pinned, deployed C-DEC has no
quantifier domain. -/
def DeltaImageCovered {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {d : ℕ} (F : M →ₗ[K] (Fin 256 → K)) (Δw : Submodule K M)
    (g : Fin d → Fin 256 → K) : Prop :=
  Submodule.map F Δw ≤ Submodule.span K (Set.range g)

/-- **BLOCKER B4 (unmet): encoder transport.**  The matrix map must be the
word-space map restricted to the mask hyperplane `ker ℓ` and transported
along the deployed free-coordinate encoder
(`V5ComponentCLane::encode_free_coordinates`).  Instantiated once with the
`E` data and once with the `F` data.  Encoder surjectivity is deliberately
not required (`cDec_comp` is sound for any linear parametrisation); what is
missing is the cross-language correspondence itself, which is the parent
file's `UnresolvedInterfaces.RustLeanRowCorrespondence332` obligation. -/
def EncoderIntertwines {K M V' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup V'] [Module K V']
    (ell : M →ₗ[K] K) (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    (wordMap : M →ₗ[K] V') (mat : (Fin 1023 → K) →ₗ[K] V') : Prop :=
  (wordMap.domRestrict (LinearMap.ker ell)) ∘ₗ enc = mat

end DeployedBlockers

/-! ## The assembled verification path

Certificate + blocker interfaces ⟹ the audit's `CDecAudit`, and from there
the parent file's exact conditional-decoupling law.  These theorems are the
complete Lean side of the pipeline; their hypotheses are precisely the
artifacts that do not exist yet. -/

section Assembly

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- **Deployed C-DEC checker, word-space form.**  Given the (currently
non-existent) certificate and the (currently unprovable) blocker
interfaces B3/B4, the audit's `(C-DEC)` line — `CDecAudit ell E F Δw`,
i.e. `F(Δ_w) ≤ image (F | ker ℓ ⊓ ker E)` — follows in-kernel.  The proof
is transport only: `cDecAudit_iff_cDec`, antitonicity down from the
generator span, pullback along the encoder, and the matrix checker.  The
conclusion is exactly the audit hypothesis consumed by every theorem of the
parent file; no surjectivity appears anywhere. -/
theorem cDecAudit_of_frozen_certificate
    (ell : M →ₗ[K] K) (E : M →ₗ[K] (Fin 76 → K)) (F : M →ₗ[K] (Fin 256 → K))
    (Δw : Submodule K M)
    (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    {Emat : Matrix (Fin 76) (Fin 1023) K} {Fmat : Matrix (Fin 256) (Fin 1023) K}
    {d : ℕ} {g : Fin d → Fin 256 → K} {w : Fin d → Fin 1023 → K}
    (hEenc : DeployedBlockers.EncoderIntertwines ell enc E (Matrix.mulVecLin Emat))
    (hFenc : DeployedBlockers.EncoderIntertwines ell enc F (Matrix.mulVecLin Fmat))
    (hΔ : DeployedBlockers.DeltaImageCovered F Δw g)
    (hcert : FrozenQ18Certificate Emat Fmat g w) :
    CDecAudit ell E F Δw := by
  rw [cDecAudit_iff_cDec]
  refine cDec_anti hΔ (cDec_comp enc ?_)
  have hE' : (E.domRestrict (LinearMap.ker ell)) ∘ₗ enc = Matrix.mulVecLin Emat := hEenc
  have hF' : (F.domRestrict (LinearMap.ker ell)) ∘ₗ enc = Matrix.mulVecLin Fmat := hFenc
  rw [hE', hF']
  exact frozenQ18_cDec_of_certificate hcert

/-- **End-to-end: certificate to the audit headline.**  With the same
(currently non-existent) inputs, the exact witness-independent conditional
law of the parent file holds for the deployed word-space maps:

    Law(F(x₁ + γ^18 • c) | E c = e) = Law(F(x₂ + γ^18 • c) | E c = e)

for uniform `c` on the conditioned fibre of `ker ℓ` and any two legal
witnesses.  Pure composition with
`componentC_full_fold_conditional_decoupling`; nothing else is missing on
the Lean side.  The missing inputs are the blocker artifacts, and only
they. -/
theorem frozen_certificate_yields_full_fold_decoupling
    [DecidableEq K] [Fintype M]
    (ell : M →ₗ[K] K) (E : M →ₗ[K] (Fin 76 → K)) (F : M →ₗ[K] (Fin 256 → K))
    {Δw : Submodule K M}
    (enc : (Fin 1023 → K) →ₗ[K] LinearMap.ker ell)
    {Emat : Matrix (Fin 76) (Fin 1023) K} {Fmat : Matrix (Fin 256) (Fin 1023) K}
    {d : ℕ} {g : Fin d → Fin 256 → K} {w : Fin d → Fin 1023 → K}
    (hEenc : DeployedBlockers.EncoderIntertwines ell enc E (Matrix.mulVecLin Emat))
    (hFenc : DeployedBlockers.EncoderIntertwines ell enc F (Matrix.mulVecLin Fmat))
    (hΔ : DeployedBlockers.DeltaImageCovered F Δw g)
    (hcert : FrozenQ18Certificate Emat Fmat g w)
    {γ : K} (hγ : γ ≠ 0) {x₁ x₂ : M} (hlegal : x₂ - x₁ ∈ Δw) (e : Fin 76 → K)
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
            F (x₂ + γ ^ 18 • ((c : LinearMap.ker ell) : M))) :=
  componentC_full_fold_conditional_decoupling ell E F hγ
    (cDecAudit_of_frozen_certificate ell E F Δw enc hEenc hFenc hΔ hcert)
    hlegal e

end Assembly

/-! ## Certificate bookkeeping: kernel arithmetic, counts ONLY

Pinned sizes for the certificate the generator must emit.  These are
counts, not the decoupling theorem, and are not evidence for C-DEC. -/

namespace CertificateShape

/-- Bookkeeping only (NOT C-DEC): the conditioned row order is 72
layer-zero values, then 3 MLE claims, then 1 structured terminal claim. -/
theorem conditioned_rows : 72 + 3 + 1 = 76 := by norm_num

/-- Bookkeeping only (NOT C-DEC): the frozen-q18 post-combination row
grammar — four rounds × (2 OOD + 7 relation-sumcheck), `4·(18+18+18)`
later-layer values, four final coefficients. -/
theorem post_combination_rows : 4 * (2 + 7) + 4 * (18 + 18 + 18) + 4 = 256 := by
  norm_num

/-- Bookkeeping only (NOT C-DEC): the mask space has 1023 free coordinates
(1024 rows minus the derived pivot). -/
theorem free_coordinates : 1024 - 1 = 1023 := by norm_num

/-- Bookkeeping only (NOT C-DEC): the worst-case joint inventory is the
audit's 332 rows. -/
theorem joint_rows : 76 + 256 = 332 := by norm_num

/-- Bookkeeping only (NOT C-DEC): serialized `Emat` size in bytes at 16
bytes per canonical QM31 element. -/
theorem e_matrix_bytes : 76 * 1023 * 16 = 1243968 := by norm_num

/-- Bookkeeping only (NOT C-DEC): serialized `Fmat` size in bytes. -/
theorem f_matrix_bytes : 256 * 1023 * 16 = 4190208 := by norm_num

/-- Bookkeeping only (NOT C-DEC): serialized bytes per generator — one
`g`-row (256 QM31) plus one witness `w`-row (1023 QM31). -/
theorem per_generator_bytes : (256 + 1023) * 16 = 20464 := by norm_num

/-- Bookkeeping only (NOT C-DEC): worst-case total certificate size with
the maximal `d = 256` generator family. -/
theorem max_certificate_bytes : 1243968 + 4190208 + 256 * 20464 = 10672960 := by
  norm_num

end CertificateShape

/-! ## Axiom audit -/

#print axioms cDec_anti
#print axioms cDec_comp
#print axioms cDec_of_generator_witnesses
#print axioms exists_generator_witnesses_of_cDec
#print axioms FrozenQ18Certificate
#print axioms frozenQ18_cDec_of_certificate
#print axioms exists_frozenQ18_certificate_iff_cDec
#print axioms exists_spanning_family_card_le
#print axioms DeployedBlockers.EMatrixFaithful
#print axioms DeployedBlockers.FMatrixFaithful
#print axioms DeployedBlockers.DeltaImageCovered
#print axioms DeployedBlockers.EncoderIntertwines
#print axioms cDecAudit_of_frozen_certificate
#print axioms frozen_certificate_yields_full_fold_decoupling
#print axioms CertificateShape.conditioned_rows
#print axioms CertificateShape.post_combination_rows
#print axioms CertificateShape.free_coordinates
#print axioms CertificateShape.joint_rows
#print axioms CertificateShape.e_matrix_bytes
#print axioms CertificateShape.f_matrix_bytes
#print axioms CertificateShape.per_generator_bytes
#print axioms CertificateShape.max_certificate_bytes

end AspisV5ComponentCDeployedCDec
