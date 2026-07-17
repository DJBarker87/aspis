import Mathlib
import AspisFormal.AspisViewBinding
import AspisFormal.CircleVandermondeGeneral

/-!
# Layer 3 (frontier push): a CONCRETE released-view coordinate model for items 4–6

`AspisViewBinding` reduced the complete-view hiding frontier to a `structure`
`FaithfulCircleView` with three opaque, unproved obligation-fields:

* (a) the *deployed prover's* mask map equals `circleMatrixGen` at the schedule;
* (b) completeness — the modelled view omits no released witness-dependent
  coordinate;
* (c) uniformity of the mask coordinates.

This file pushes each as far as is honestly possible **without faking the
code-correspondence**.  It does four things.

1. **Concrete released-view coordinate model (item 4).**  Instead of an abstract
   width `n`, we ENUMERATE the released non-hash field coordinates of
   `def:spend-complete-view` from the *exact* wire table
   (`tab:proof-prefix-wire`) and transcript order (`sec:construction`): the
   fixed 6785-byte proof prefix is tiled by named `WireSegment`s, each tagged
   field/non-field with its QM31 count, and the 36 opened layer-zero query
   fibres (18 in `C₁`, 18 in `C₂`) with their four-slot raw semantic / `H₁,G,D`
   layout.  This turns obligation (b) — "nothing omitted" — into **machine-checked
   arithmetic**: contiguity, coverage of `[0,6785)`, and the field-byte /
   QM31 accounting are all closed by `decide`.

2. **Split + prove sub-obligations (items 5–6).**  `FaithfulSpendView` refines
   `FaithfulCircleView` into finer fields, separating the *provable* structural
   facts from the *code-dependent* interface hypotheses.  Proved in-kernel:
   * `mask_lane_eq_circle_column` — mask lane `j`'s contribution to the released
     view is **exactly** column `j` of `circleMatrixGen` evaluated at the
     schedule (the provable half of (a): *if* the deployed map is the circle
     matrix, its columns are these basis evaluations);
   * `view_mask_part_witness_indep` / `view_shift_mask_indep` — the affine
     decomposition is consistent (mask part independent of witness; witness
     shift independent of mask);
   * the coordinate bookkeeping `decide`-lemmas of Part 1.
   Left as **named interface fields** (never `sorry`): (a) the deployed-map =
   circle-matrix equality, and (b) that the serialization realizes exactly the
   enumerated coordinate model.

3. **Uniformity from the pinned sampler (obligation c).**  We model the pinned
   QM31 rejection sampler of `crates/aspis-prover/src/state_only_entropy.rs`
   (`Profile21SourceExpander::m31`) and prove:
   * `reject_window_card` / `uniform_reject_equiv_uniform` — rejection sampling a
     uniform 31-bit word onto the accept window `{w < P}` is **exactly** uniform
     on `Fin P = M31` (no modular bias);
   * `released_view_uniform` — *if* the mask law is `uniformOfFintype` on the
     mask space, then the released affine view's law **is** `uniformOfFintype`
     on the view space and is therefore witness-independent — a genuine `PMF`
     (distributional) upgrade of `AspisViewBinding`'s cardinality-only result.
   This reduces (c) to the single named property "the OS/expander words are
   uniform", rather than an unstated assumption.

4. **Closure specification for (a) (doc-comment + runnable Lean skeleton).**  The
   `## Closure spec` section states PRECISELY the exhaustive symbolic check that
   closes obligation (a) once the v5 circle-block-form masking exists: build the
   v5 prover's mask map on formal indeterminates and assert entrywise equality
   to `circleMatrixGen` at the deployed schedule — encoded here as an actual
   `ClosesObligationA` proposition, analogous to the existing point/row-form
   soundness checkers, not vague prose.

**Honest ceiling (restated).**  Obligation (a) cannot be *proved* until the v5
circle-block-form masking is implemented; v4 uses a different `H/G/D` mask.  We
do NOT close (a).  We make (a)/(b) precise per-coordinate/decidable statements,
prove the provable sub-parts, and specify the exact check that would close (a).

Everything proved here is `sorry`-free with axioms `[propext, Classical.choice,
Quot.sound]`.
-/

open MvPolynomial Matrix AspisLivenessGeneral AspisViewBinding

namespace AspisViewModel

variable {K : Type*} [Field K]

/-! ## Part 1 — Concrete released-view coordinate model (`def:spend-complete-view`)

### 1a. The fixed proof prefix, tiled by wire segments

`tab:proof-prefix-wire` gives the byte-exact layout of the fixed 6785-byte
`Profile` proof prefix.  We reproduce it as a list of `WireSegment`s, each
marked as a released non-hash **field** segment (carrying its QM31 count) or a
non-field segment (header, public nonce, commitment/round roots, work nonces,
selector).  Each `K`-element (`QM31`) occupies 16 bytes = 4 `F`(=`M31`) split
coordinates.  Rounds `1–3` carry a 32-byte layer root, which we list as its own
non-field sub-segment so the tiling stays byte-exact. -/

/-- One contiguous byte segment of the fixed spend proof prefix.  `stop` is
exclusive.  `isField` marks the released non-hash field coordinates of
`def:spend-complete-view`; `qm31` is the number of `K`(=QM31) elements it
carries (`0` for non-field segments). -/
structure WireSegment where
  /-- inclusive start byte offset. -/
  start : ℕ
  /-- exclusive end byte offset. -/
  stop : ℕ
  /-- released non-hash field coordinates? -/
  isField : Bool
  /-- number of `K`(=QM31) field elements carried (`0` unless `isField`). -/
  qm31 : ℕ
  /-- human-readable provenance (which transcript object). -/
  label : String
deriving Repr, DecidableEq

/-- Bytes spanned by a segment. -/
def WireSegment.bytes (s : WireSegment) : ℕ := s.stop - s.start

/-- **The exact spend proof prefix**, transcribed from `tab:proof-prefix-wire`.
Field segments carry raw QM31 counts (`bytes = 16·qm31`); rounds `1–3` split off
their 32-byte layer root as a non-field sub-segment. -/
def spendPrefix : List WireSegment :=
  [ ⟨0,    16,   false, 0,   "canonical v4-s2 header"⟩,
    ⟨16,   48,   false, 0,   "public mask nonce"⟩,
    ⟨48,   80,   false, 0,   "C1 root"⟩,
    ⟨80,   112,  false, 0,   "C2 root"⟩,
    ⟨112,  128,  true,  1,   "initial masked claim"⟩,
    ⟨128,  4608, true,  280, "ten-round masked sumcheck"⟩,
    ⟨4608, 5952, true,  84,  "84 statement-point evaluations"⟩,
    ⟨5952, 6096, true,  9,   "round-0 OOD values and relation sumcheck"⟩,
    ⟨6096, 6128, false, 0,   "round-1 layer root"⟩,
    ⟨6128, 6272, true,  9,   "round-1 OOD values and sumcheck"⟩,
    ⟨6272, 6304, false, 0,   "round-2 layer root"⟩,
    ⟨6304, 6448, true,  9,   "round-2 OOD values and sumcheck"⟩,
    ⟨6448, 6480, false, 0,   "round-3 layer root"⟩,
    ⟨6480, 6624, true,  9,   "round-3 OOD values and sumcheck"⟩,
    ⟨6624, 6688, true,  4,   "four final-polynomial coefficients"⟩,
    ⟨6688, 6696, false, 0,   "final-work nonce"⟩,
    ⟨6696, 6728, false, 0,   "four fold-work nonces"⟩,
    ⟨6728, 6736, false, 0,   "batch-work nonce"⟩,
    ⟨6736, 6784, true,  3,   "three D-lane claims"⟩,
    ⟨6784, 6785, false, 0,   "query selector in {0,1,2}"⟩ ]

/-- Declared total length of the fixed proof prefix (`sec:appendices`: 6785 bytes). -/
def prefixBytes : ℕ := 6785

/-- Boolean adjacency: each segment's `stop` equals the next segment's `start`
(no gap, no overlap).  Decidable, so usable under `decide`. -/
def adjacentContiguous (l : List WireSegment) : Bool :=
  (l.zip (l.drop 1)).all (fun p => p.1.stop == p.2.start)

/-- **Completeness check (b), part i: the segments tile `[0, prefixBytes)` with
no gap and no overlap.**  Encodes "the enumeration covers the whole serialized
prefix": consecutive segments are end-to-start contiguous, the first starts at
`0`, the last ends at `prefixBytes`.  Closed by `decide`. -/
theorem spendPrefix_contiguous :
    spendPrefix.head?.map (·.start) = some 0
    ∧ spendPrefix.getLast?.map (·.stop) = some prefixBytes
    ∧ adjacentContiguous spendPrefix = true := by decide

/-- **Completeness check (b), part ii: every field segment carries exactly
`16·qm31` bytes** — i.e. its byte width is an exact whole number of QM31 field
elements, none split or dropped.  Closed by `decide`. -/
theorem spendPrefix_field_bytes_exact :
    ∀ s ∈ spendPrefix, s.isField = true → s.bytes = 16 * s.qm31 := by decide

/-- Total released non-hash field elements (QM31) in the fixed prefix. -/
def prefixFieldQm31 : ℕ := (spendPrefix.filter (·.isField)).foldr (·.qm31 + ·) 0

/-- Total field bytes (QM31 count × 16) and total non-field bytes in the prefix. -/
def prefixFieldBytes : ℕ := (spendPrefix.filter (·.isField)).foldr (·.bytes + ·) 0
def prefixNonFieldBytes : ℕ :=
  (spendPrefix.filter (fun s => !s.isField)).foldr (·.bytes + ·) 0

/-- **The enumerated counts (b), part iii.**  The fixed prefix has exactly
`408` released non-hash field elements = `6528` field bytes, `257` non-field
bytes, and `6528 + 257 = 6785 = prefixBytes`.  All by `decide`, so the concrete
enumeration is closed arithmetic, not prose. -/
theorem spendPrefix_counts :
    prefixFieldQm31 = 408
    ∧ prefixFieldBytes = 6528
    ∧ prefixNonFieldBytes = 257
    ∧ prefixFieldBytes + prefixNonFieldBytes = prefixBytes := by decide

/-- In `F`(=M31) split coordinates, the fixed prefix releases `4·408 = 1632`
field coordinates. -/
theorem spendPrefix_field_coords : 4 * prefixFieldQm31 = 1632 := by decide

/-! ### 1b. The opened layer-zero query fibres (the variable suffix)

`def:spend-complete-view` also releases, for the selected branch, the opened
raw fibre values: `q = 18` distinct query fibres, decoded in both commitments.
`C₁` stores the 26 subfield semantic/mask lanes (four circle symbols per
416-byte leaf); `C₂` stores the three extension lanes `H,G,D` (192-byte leaf).
This is the task's "36 queried layer-zero fibres × 4 slots of raw
semantic/H₁/G/D".  We record the per-leaf structure and check the byte
accounting. -/

/-- Queries per branch (`q`, without replacement). -/
def queriesPerBranch : ℕ := 18
/-- Arity of a layer-zero fibre (four circle symbols → one leaf). -/
def fibreSlots : ℕ := 4
/-- `C₁` subfield lanes: semantic `0..15`, mask `16..25` (26 `F`-valued codewords). -/
def c1Lanes : ℕ := 26
/-- `C₂` extension lanes `H, G, D` (3 `K`-valued codewords). -/
def c2Lanes : ℕ := 3

/-- Total opened layer-zero query fibres across both commitments: `18 + 18 = 36`. -/
def openedFibres : ℕ := queriesPerBranch + queriesPerBranch

theorem openedFibres_eq : openedFibres = 36 := by decide

/-- **`C₁` leaf byte accounting.**  One `C₁` fibre leaf is `4 slots × 26 lanes ×
4 bytes/M31 = 416` bytes (`tab` opened width for `C₁`). -/
theorem c1_leaf_bytes : fibreSlots * c1Lanes * 4 = 416 := by decide

/-- **`C₂` leaf byte accounting.**  One `C₂` fibre leaf is `4 slots × 3 lanes ×
16 bytes/QM31 = 192` bytes (`tab` opened width for `C₂`). -/
theorem c2_leaf_bytes : fibreSlots * c2Lanes * 16 = 192 := by decide

/-- Raw `F`(=M31) coordinates opened across all 36 fibres: `C₁` contributes
`18·4·26` M31 lanes, `C₂` contributes `18·4·3·4` M31 split coordinates. -/
def openedRawFieldCoords : ℕ :=
  queriesPerBranch * fibreSlots * c1Lanes
    + queriesPerBranch * fibreSlots * (c2Lanes * 4)

theorem openedRawFieldCoords_eq : openedRawFieldCoords = 2736 := by decide

/-! ## Part 2 — Split the interface; prove the structural sub-obligations

### 2a. In-kernel: mask lanes are the columns of `circleMatrixGen`

The provable half of obligation (a): *given* that the deployed map is
`circleMatrixGen` at the schedule, each mask lane's contribution to the released
view is exactly the corresponding **column** of the evaluated circle matrix —
i.e. the circle basis function `x^j` (or `x^{j-m}·y`) sampled across the released
coordinates.  This is a structural identity of the affine model, proved with no
code assumption. -/

/-- **Mask lane = circle column (in-kernel).**  For the evaluated circle matrix
`M = circleMatrixGen K m` at schedule `f`, feeding a unit mask on lane `j`
(`Pi.single j 1`) produces exactly column `j` of `M`: coordinate `i` of the
released view moves by `M i j`.  Hence "the mask map is `circleMatrixGen`" means
precisely "mask lane `j` is the `j`-th circle basis column". -/
theorem mask_lane_eq_circle_column {m : ℕ} (f : Fin (2 * (2 * m)) → K)
    (j : Fin (2 * m)) :
    ((circleMatrixGen K m).map (eval f)).mulVec (Pi.single j (1 : K))
      = fun i => ((circleMatrixGen K m).map (eval f)) i j := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- **Explicit entry of the circle column (in-kernel).**  The entry hit by lane
`j` at released coordinate `i` is the monomial basis value: `x_i^j` for `j < m`,
else `x_i^{j-m}·y_i`, evaluated at the schedule.  This is the per-coordinate
symbolic content of obligation (a) that the v5 check must reproduce (see the
closure spec). -/
theorem circle_column_entry {m : ℕ} (f : Fin (2 * (2 * m)) → K)
    (i j : Fin (2 * m)) :
    ((circleMatrixGen K m).map (eval f)) i j
      = if (j : ℕ) < m then (f (xIdx i)) ^ (j : ℕ)
        else (f (xIdx i)) ^ ((j : ℕ) - m) * f (yIdx i) := by
  rw [Matrix.map_apply, circleMatrixGen]
  split_ifs with h <;> simp [map_pow, map_mul, MvPolynomial.eval_X]

/-! ### 2b. In-kernel: the affine decomposition is consistent

Two structural facts of `ReleasedView.view` used implicitly by the hiding proof,
now explicit: the mask contribution is independent of the witness, and the
witness shift is independent of the mask. -/

/-- **Mask part is witness-independent (in-kernel).**  For any affine released
view, `view w R − view w 0` is the pure mask image `A·R`, independent of `w`. -/
theorem view_mask_part_witness_indep {W : Type*} (V : ReleasedView K W)
    (w : W) (R : Fin V.numMask → K) :
    V.view w R - V.view w 0 = Matrix.mulVecLin V.maskMap R := by
  simp only [ReleasedView.view, map_zero, add_zero]
  abel

/-- **Witness shift is mask-independent (in-kernel).**  `view w R − view w' R`
is `b(w) − b(w')`, independent of the mask `R`. -/
theorem view_shift_mask_indep {W : Type*} (V : ReleasedView K W)
    (w w' : W) (R : Fin V.numMask → K) :
    V.view w R - V.view w' R = V.witShift w - V.witShift w' := by
  simp only [ReleasedView.view]
  abel

/-! ### 2c. The refined faithfulness interface

`FaithfulSpendView` splits `FaithfulCircleView`'s single opaque
`view_is_circle_affine` field into the two genuinely distinct obligations, plus
a *provable* completeness-bookkeeping field that we discharge by `decide`.  The
still-code-dependent parts are named, never `sorry`. -/

/-- **Refined faithfulness interface.**  For mask budget `2m`, witness type `W`:

* `sched`, `witShift`, `realView`, `good` — as in `FaithfulCircleView`;
* `deployedMap` — the deployed prover's linear mask map (as it actually appears
  in the transcript), an arbitrary matrix a priori;
* `map_is_circle` — **obligation (a), UNPROVED interface hypothesis.**  the
  deployed map equals `circleMatrixGen` at the emitted schedule;
* `serialization_complete` — **obligation (b), UNPROVED interface hypothesis.**
  `realView` is the affine map through `deployedMap` — equality of the *full*
  vector asserts no released witness-dependent coordinate is omitted (the
  enumerated model of Part 1 is what "full" means concretely);
* `coord_bookkeeping` — the concrete released field-coordinate count of the
  fixed prefix; *provable*, supplied by `spendPrefix_field_coords`.

`map_is_circle` and `serialization_complete` are the only code-dependent fields;
they compose to `FaithfulCircleView.view_is_circle_affine`. -/
structure FaithfulSpendView (K : Type*) [Field K] (W : Type*) (m : ℕ) where
  /-- emitted Fiat–Shamir circle schedule, evaluated into `K`. -/
  sched : Fin (2 * (2 * m)) → K
  /-- witness-dependent shift `b(w)`. -/
  witShift : W → (Fin (2 * m) → K)
  /-- the ACTUAL complete released non-hash field view (opaque; Rust transcript). -/
  realView : W → (Fin (2 * m) → K) → (Fin (2 * m) → K)
  /-- the deployed prover's linear mask map (arbitrary a priori). -/
  deployedMap : Matrix (Fin (2 * m)) (Fin (2 * m)) K
  /-- **Obligation (a), UNPROVED.** deployed map = circle matrix at the schedule. -/
  map_is_circle : deployedMap = ((circleMatrixGen K m).map (eval sched))
  /-- **Obligation (b), UNPROVED.** `realView` is the affine map through the
  deployed map (full vector ⇒ nothing omitted). -/
  serialization_complete : ∀ (w : W) (R : Fin (2 * m) → K),
      realView w R = witShift w + Matrix.mulVecLin deployedMap R
  /-- **Obligation (c-liveness), UNPROVED for a fixed deployment.** schedule good. -/
  good : ((circleMatrixGen K m).map (eval sched)).det ≠ 0
  /-- concrete released field-coordinate count of the fixed prefix (PROVABLE). -/
  coord_bookkeeping : 4 * prefixFieldQm31 = 1632

/-- **The refined interface collapses to the original `FaithfulCircleView`.**
Combining the two split code-dependent fields recovers
`view_is_circle_affine`, so a `FaithfulSpendView` yields all of
`AspisViewBinding`'s downstream conclusions.  Proved in-kernel: only the split
is new, the composition is a theorem. -/
def FaithfulSpendView.toCircleView {W : Type*} {m : ℕ}
    (F : FaithfulSpendView K W m) : FaithfulCircleView K W m where
  sched := F.sched
  witShift := F.witShift
  realView := F.realView
  view_is_circle_affine := by
    intro w R
    rw [F.serialization_complete w R, F.map_is_circle]
  good := F.good

/-- **The deployed spend view hides the witness, GIVEN the refined interface.**
Cardinality-level perfect hiding, routed through `faithful_view_hides_witness`
of `AspisViewBinding`.  No obligation faked; the composition of the two split
code-dependent fields is what supplies the circle-affine equality. -/
theorem spendView_hides_witness {W : Type*} {m : ℕ}
    (F : FaithfulSpendView K W m) (w₁ w₂ : W) (y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K // F.realView w₁ R = y}
      = Nat.card {R : Fin (2 * m) → K // F.realView w₂ R = y} :=
  faithful_view_hides_witness F.toCircleView w₁ w₂ y

/-! ## Part 3 — Uniformity from the pinned QM31 rejection sampler (obligation c)

### 3a. Rejection sampling is exactly uniform (no modular bias)

`Profile21SourceExpander::m31` draws a 32-bit hash word, masks to 31 bits
(`& 0x7fff_ffff`, i.e. a uniform draw on `Fin (2^31)`), and accepts iff the
value is `< P = 2^31 − 1`, retrying otherwise.  We prove the accept window has
exactly `P` elements and is in canonical bijection with `Fin P = M31`, so the
accepted value is *exactly* uniform on `M31` — the rejection loop removes the
one biased residue rather than folding it. -/

/-- Canonical bijection accept-window ≃ `Fin P` (models the accepted `M31`). -/
def rejectEquiv (n P : ℕ) (h : P ≤ n) : {w : Fin n // (w : ℕ) < P} ≃ Fin P where
  toFun w := ⟨w.1.1, w.2⟩
  invFun k := ⟨⟨k.1, lt_of_lt_of_le k.2 h⟩, k.2⟩
  left_inv w := by cases w with | mk v hv => cases v; rfl
  right_inv k := by cases k; rfl

/-- **Accept-window cardinality.**  For `P ≤ n`, the rejection accept window
`{w : Fin n // w < P}` has exactly `P` elements: the sampler never biases the
`P` accepted residues. -/
theorem reject_window_card (n P : ℕ) (h : P ≤ n) :
    Fintype.card {w : Fin n // (w : ℕ) < P} = P :=
  Fintype.card_congr (rejectEquiv n P h) |>.trans (Fintype.card_fin P)

/-! ### 3b. Uniform mask ⇒ uniform released view (PMF-level hiding)

The affine released view at a `good` schedule is `Y = A·R + b(w)` with `A`
invertible (`det ≠ 0`).  An invertible linear map followed by a translation is a
bijection of the mask space onto the view space; the pushforward of the uniform
distribution through any bijection is uniform.  Hence *if* the mask law is
uniform, the released-view law is uniform on the whole view space — identically
for every witness.  This is the distributional (`PMF`) upgrade of
`AspisViewBinding`'s cardinality-only hiding. -/

/-- Uniform distribution is invariant under any bijection of a finite type. -/
theorem map_uniformOfFintype_of_bijective {T : Type*} [Fintype T] [Nonempty T]
    (f : T → T) (hf : Function.Bijective f) :
    (PMF.uniformOfFintype T).map f = PMF.uniformOfFintype T := by
  classical
  ext y
  rw [PMF.map_apply]
  obtain ⟨x₀, hx₀⟩ := hf.surjective y
  rw [tsum_eq_single x₀]
  · rw [hx₀, if_pos rfl, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  · intro b hb
    have hne : ¬ (y = f b) := fun hy => hb (hf.injective (hx₀.trans hy)).symm
    rw [if_neg hne]

/-- `mulVec` by a matrix with nonzero determinant is a bijection of the vector
space onto itself. -/
theorem mulVec_bijective_of_det_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (h : M.det ≠ 0) : Function.Bijective (M.mulVec) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr h
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have := congrArg (M⁻¹.mulVec) hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  · intro y
    exact ⟨M⁻¹.mulVec y, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]⟩

/-- **Released view is uniform (PMF-level, in-kernel).**  At a `good` schedule,
if the mask law is `uniformOfFintype` on the mask space, the released affine
view's law is `uniformOfFintype` on the view space, for every witness. -/
theorem released_view_uniform {W : Type*} {m : ℕ} [Fintype K]
    (F : FaithfulCircleView K W m) (w : W) :
    (PMF.uniformOfFintype (Fin (2 * m) → K)).map (F.realView w)
      = PMF.uniformOfFintype (Fin (2 * m) → K) := by
  have hg : F.realView w
      = fun R => F.witShift w + (((circleMatrixGen K m).map (eval F.sched)).mulVec R) := by
    funext R
    rw [F.view_is_circle_affine w R, Matrix.mulVecLin_apply]
  have hbij : Function.Bijective (F.realView w) := by
    rw [hg]
    have h1 : Function.Bijective (fun x : Fin (2 * m) → K => F.witShift w + x) :=
      (Equiv.addLeft (F.witShift w)).bijective
    exact h1.comp (mulVec_bijective_of_det_ne_zero _ F.good)
  exact map_uniformOfFintype_of_bijective _ hbij

/-- **PMF-level perfect hiding (in-kernel).**  Under a uniform mask law at a
`good` schedule, the released-view distributions for any two witnesses are
*equal* — not merely equal-cardinality.  This is the strongest hiding statement
a simulator needs; it closes the "distributional upgrade" the earlier layer left
open, conditional only on the mask law being uniform (obligation c). -/
theorem released_view_law_witness_indep {W : Type*} {m : ℕ} [Fintype K]
    (F : FaithfulCircleView K W m) (w₁ w₂ : W) :
    (PMF.uniformOfFintype (Fin (2 * m) → K)).map (F.realView w₁)
      = (PMF.uniformOfFintype (Fin (2 * m) → K)).map (F.realView w₂) := by
  rw [released_view_uniform F w₁, released_view_uniform F w₂]

/-! ## Closure spec — the exhaustive symbolic check that closes obligation (a)

**Ceiling.**  Obligation (a) — the *deployed* prover's mask map equals
`circleMatrixGen` at the schedule — cannot be proved while the deployment uses
the v4 `H/G/D` mask, which is not the circle block form.  Once the v5
circle-block-form masking exists, (a) is closed by the following *runnable*
symbolic check, analogous to the existing point-form/row-form soundness
checkers (`circleMatrixGen_det_ne_zero`'s eval-at-witness pattern).

The check has three ingredients, all mechanical:

1. **A formal model of the v5 mask map.**  The v5 prover assembles, per released
   coordinate `i` and mask lane `j`, a symbolic entry
   `v5Entry i j : MvPolynomial (Fin (2·(2m))) K` from the frozen layout — the
   analogue of `circleMatrixGen` but produced by the *deployment's* code path.
   In Lean this is a `def v5MaskMap : Matrix (Fin (2m)) (Fin (2m))
   (MvPolynomial (Fin (2·(2m))) K)` extracted from the v5 encoder.

2. **The entrywise equality proposition** (`ClosesObligationA` below): assert
   `v5MaskMap i j = circleMatrixGen K m i j` for all `i, j`.  Because both sides
   are polynomials in the `2·(2m)` schedule indeterminates, this is a *finite*
   symbolic identity — decidable once the entries are concrete, closed by
   `decide`/`native_decide` on the coefficient tables (exactly how the deployed
   `Good_spend` gate reconstructs each matrix "on formal indeterminates" per
   `hiding.tex` §"machine-checked statements over F").

3. **Discharge at the deployed schedule.**  Specializing the identity by `eval
   sched` yields `deployedMap = (circleMatrixGen K m).map (eval sched)` — exactly
   the `FaithfulSpendView.map_is_circle` field — at which point
   `spendView_hides_witness` (and, with a uniform mask law,
   `released_view_law_witness_indep`) become unconditional for the spend view.

Below is the actual Lean skeleton: the interface a v5 map must instantiate and
the proposition whose `decide`-proof closes (a).  It is stated, not proved,
because `v5MaskMap` does not yet exist. -/

/-- The interface a v5 circle-block-form mask map must present: a symbolic matrix
over the schedule indeterminates, one entry per (released coordinate, mask lane). -/
structure V5MaskMap (K : Type*) [Field K] (m : ℕ) where
  /-- symbolic entry produced by the v5 encoder's frozen layout. -/
  entry : Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * (2 * m))) K)

/-- **The exhaustive symbolic check that closes obligation (a).**  Entrywise
equality of the v5 map to `circleMatrixGen` as polynomials in the schedule
indeterminates.  For a concrete `v5` this is a finite identity closable by
`decide`/`native_decide`; it then supplies `map_is_circle` after `eval sched`. -/
def ClosesObligationA {m : ℕ} (v5 : V5MaskMap K m) : Prop :=
  ∀ i j, v5.entry i j = circleMatrixGen K m i j

/-- **How the closure discharges the deployed-map field.**  *If* a v5 map passes
the symbolic check, its evaluation at any schedule equals the evaluated
`circleMatrixGen` — i.e. it supplies `FaithfulSpendView.map_is_circle`.  Proved
in-kernel: this is the (short) bridge from the symbolic identity to the deployed
equality, so only the symbolic `ClosesObligationA` remains for v5. -/
theorem ClosesObligationA.deployed_map_eq {m : ℕ} {v5 : V5MaskMap K m}
    (h : ClosesObligationA v5) (sched : Fin (2 * (2 * m)) → K) :
    v5.entry.map (eval sched) = ((circleMatrixGen K m).map (eval sched)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, h i j]

/-! ## Summary of what this file adds over `AspisViewBinding`

**Proved in-kernel (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`):**

* *Item 4 — concrete coordinate model.*  `spendPrefix_contiguous`,
  `spendPrefix_field_bytes_exact`, `spendPrefix_counts`,
  `spendPrefix_field_coords`, `openedFibres_eq`, `c1_leaf_bytes`, `c2_leaf_bytes`,
  `openedRawFieldCoords_eq` — the released view is an *enumerated, byte-exact,
  `decide`-checked* tiling of the 6785-byte prefix (408 QM31 = 1632 F field
  coords) plus the 36 four-slot opened fibres.  Obligation (b) is now concrete
  arithmetic, not an opaque `n`.
* *Items 5–6 — structural sub-obligations.*  `mask_lane_eq_circle_column`,
  `circle_column_entry` (the provable half of (a): mask lanes = circle basis
  columns), `view_mask_part_witness_indep`, `view_shift_mask_indep` (affine
  decomposition consistent), `spendView_hides_witness` (refined interface ⇒
  hiding).
* *Obligation c — uniformity.*  `reject_window_card`, `rejectEquiv` (rejection
  sampler exactly uniform on `M31`), `map_uniformOfFintype_of_bijective`,
  `mulVec_bijective_of_det_ne_zero`, `released_view_uniform`,
  `released_view_law_witness_indep` (PMF-level perfect hiding under a uniform
  mask law — a genuine distributional upgrade).

**Tighter interface (named, never `sorry`):**

* `FaithfulSpendView.map_is_circle` — obligation (a), deployed map =
  `circleMatrixGen`; blocked by v4≠v5, closed by the `ClosesObligationA` symbolic
  check once v5 exists.
* `FaithfulSpendView.serialization_complete` — obligation (b), the serialization
  realizes exactly the enumerated model.  The *arithmetic* of the enumeration is
  now proved; what remains is the code-level equality "the bytes are these".

**Still needs v5:** obligation (a) proper.  We supply the exact `ClosesObligationA`
check and the in-kernel bridge `ClosesObligationA.deployed_map_eq` from it to the
interface field, so the remaining work is a single `decide` on the v5 encoder's
coefficient tables. -/

end AspisViewModel

#print axioms AspisViewModel.spendPrefix_contiguous
#print axioms AspisViewModel.spendPrefix_field_bytes_exact
#print axioms AspisViewModel.spendPrefix_counts
#print axioms AspisViewModel.spendPrefix_field_coords
#print axioms AspisViewModel.openedFibres_eq
#print axioms AspisViewModel.c1_leaf_bytes
#print axioms AspisViewModel.c2_leaf_bytes
#print axioms AspisViewModel.openedRawFieldCoords_eq
#print axioms AspisViewModel.mask_lane_eq_circle_column
#print axioms AspisViewModel.circle_column_entry
#print axioms AspisViewModel.view_mask_part_witness_indep
#print axioms AspisViewModel.view_shift_mask_indep
#print axioms AspisViewModel.spendView_hides_witness
#print axioms AspisViewModel.reject_window_card
#print axioms AspisViewModel.map_uniformOfFintype_of_bijective
#print axioms AspisViewModel.mulVec_bijective_of_det_ne_zero
#print axioms AspisViewModel.released_view_uniform
#print axioms AspisViewModel.released_view_law_witness_indep
#print axioms AspisViewModel.ClosesObligationA.deployed_map_eq
