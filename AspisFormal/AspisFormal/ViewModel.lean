import Mathlib
import AspisFormal.AspisViewBinding
import AspisFormal.CircleVandermondeGeneral

/-!
# Fixed-prefix inventory and abstract square-view lemmas

`AspisViewBinding` reduced one square affine-view hiding argument to a
`FaithfulCircleView` interface with three opaque, unproved obligation fields:

* (a) a candidate square mask map equals `circleMatrixGen` at the schedule;
* (b) affine correctness of the chosen square `realView` (older prose called
  this completeness, but the type does not quantify over the whole wire);
* (c) uniformity and independence of the mask coordinates.

This file predates the concrete v5 encoder work.  Its scope is narrower than
its original title suggested: it checks the fixed v4 prefix and the two
layer-zero opening payloads, and proves generic facts about a square affine
masking map.  It does **not** enumerate the three later fold openings, their
salts or Merkle frontiers.  `SpendWireView.lean` now supplies a transcription
of all five suffix sections and their field-payload counts.

Within that corrected scope, this file does four things.

1. **Fixed-prefix and layer-zero inventory.**  The 6,785-byte proof prefix is
   tiled by named `WireSegment`s, each tagged field/non-field with its QM31
   count.  The 36 opened layer-zero query fibres (18 in `C₁`, 18 in `C₂`) are
   also counted.  Contiguity, coverage of `[0,6785)`, and the fixed-prefix
   field-byte accounting are closed by kernel `decide`.  These facts are
   necessary bookkeeping, not a proof that the complete view is covered.

2. **Split + prove sub-obligations (items 5–6).**  `FaithfulSpendView` refines
   `FaithfulCircleView` into finer fields, separating the *provable* structural
   facts from the *code-dependent* interface hypotheses.  Proved in-kernel:
   * `mask_lane_eq_circle_column` — mask lane `j`'s contribution to the released
     view is **exactly** column `j` of `circleMatrixGen` evaluated at the
     schedule (the provable half of (a): *if* the candidate map is the circle
     matrix, its columns are these basis evaluations);
   * `view_mask_part_witness_indep` / `view_shift_mask_indep` — the affine
     decomposition is consistent (mask part independent of witness; witness
     shift independent of mask);
   * the coordinate bookkeeping `decide`-lemmas of Part 1.
   Left as **named interface fields** (never `sorry`): (a) a candidate-map
   equality and (b) serialization faithfulness for whichever square projection
   an eventual instantiation supplies.

3. **Idealised uniformity lemmas.**  For the rejection window used by
   `Profile21SourceExpander::m31`, and for an abstract uniform mask law, we
   prove:
   * `rejectEquiv` / `reject_window_card` — the accepted 31-bit window
     `{w < P}` is in bijection with `Fin P = M31` and has cardinality `P`;
   * `released_view_uniform` — *if* the abstract square mask law is
     `uniformOfFintype`, its affine image is `uniformOfFintype` and therefore
     witness-independent.
   These lemmas do not prove that the OS, hash expander, retries, or successive
   coordinates provide independent uniform words.  The distribution theorem
   starts from an ideal uniform mask law; connecting the Rust sampler to that
   law remains a separate code-and-entropy obligation.

4. **A free-coordinate closure skeleton.**  `ClosesObligationA` records the
   entrywise equality needed for a `circleMatrixGen`-shaped model.  The actual
   component-(A) encoder map is instead a row-rescaled `circleTMatrix`; its
   corrected specification is `CircleTMatrixHiding.ClosesObligationA_T`, with
   the aligned encoder algebra in `CircleTensorBinding.lean`.

**Honest ceiling.**  No `FaithfulSpendView` is instantiated for deployed v4 or
provisional v5 here.  The square type has only `2m` output coordinates, whereas
the real wire has many more correlated field payloads.  A proof may use such a
square projection only after proving that it is sufficient for the complete
joint view; this file does not supply that proof.

Everything proved here is `sorry`-free with axioms `[propext, Classical.choice,
Quot.sound]`.
-/

open MvPolynomial Matrix AspisLivenessGeneral AspisViewBinding

namespace AspisViewModel

variable {K : Type*} [Field K]

/-! ## Part 1 — Fixed-prefix and layer-zero payload inventory

### 1a. The fixed proof prefix, tiled by wire segments

The Rust prefix table gives the intended layout of the fixed 6785-byte
`Profile` proof prefix.  We transcribe it as a list of `WireSegment`s, each
marked as a released non-hash **field** segment (carrying its QM31 count) or a
non-field segment (header, public nonce, commitment/round roots, work nonces,
selector).  Each `K`-element (`QM31`) occupies 16 bytes = 4 `F`(=`M31`) split
coordinates.  Rounds `1–3` carry a 32-byte layer root, which we list as its own
non-field sub-segment so the transcription has exact byte boundaries.  The
Lean checks below prove internal arithmetic of this list; they do not by
themselves prove correspondence with the Rust serializer. -/

/-- One contiguous byte segment of the fixed spend proof prefix.  `stop` is
exclusive.  `isField` marks a canonical field payload; `qm31` is the number of
`K`(=QM31) elements it carries (`0` for non-field segments). -/
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

/-- The spend proof prefix inventory transcribed from the Rust offset table.
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

/-- **Fixed-prefix coverage:** the segments tile `[0, prefixBytes)` with no gap
and no overlap.  This says nothing about the variable opening suffix. -/
theorem spendPrefix_contiguous :
    spendPrefix.head?.map (·.start) = some 0
    ∧ spendPrefix.getLast?.map (·.stop) = some prefixBytes
    ∧ adjacentContiguous spendPrefix = true := by decide

/-- **Fixed-prefix field framing:** every field segment carries exactly
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

/-- **The fixed-prefix counts.**  The prefix has exactly
`408` released non-hash field elements = `6528` field bytes, `257` non-field
bytes, and `6528 + 257 = 6785 = prefixBytes`.  `decide` closes the arithmetic
of the transcription, not its correspondence with executable code. -/
theorem spendPrefix_counts :
    prefixFieldQm31 = 408
    ∧ prefixFieldBytes = 6528
    ∧ prefixNonFieldBytes = 257
    ∧ prefixFieldBytes + prefixNonFieldBytes = prefixBytes := by decide

/-- In `F`(=M31) split coordinates, the fixed prefix releases `4·408 = 1632`
field coordinates. -/
theorem spendPrefix_field_coords : 4 * prefixFieldQm31 = 1632 := by decide

/-! ### 1b. The opened layer-zero query fibres (the variable suffix)

The selected branch releases `q = 18` distinct layer-zero query fibres, decoded
in both commitments.
`C₁` stores the 26 subfield semantic/mask lanes (four circle symbols per
416-byte leaf); `C₂` stores the three extension lanes `H,G,D` (192-byte leaf).
We record the per-leaf structure and check the byte accounting.  This subsection
does not count the three later fold layers, salts, framing or authentication
frontiers; `SpendWireView.lean` does. -/

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

The provable half of obligation (a): *given* that the candidate map is
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
symbolic content of the legacy free-coordinate model below.  The aligned
component-(A) encoder uses a different basis and row rescaling. -/
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
`view_is_circle_affine` field into two distinct hypotheses, plus a fixed-prefix
bookkeeping field discharged by `decide`.  It remains an abstract square-view
interface; no deployed serializer instantiates it in this file. -/

/-- **Refined faithfulness interface.**  For mask budget `2m`, witness type `W`:

* `sched`, `witShift`, `realView`, `good` — as in `FaithfulCircleView`;
* `deployedMap` — a candidate square linear mask map, arbitrary a priori;
* `map_is_circle` — **obligation (a), UNPROVED interface hypothesis.**  the
  the candidate map equals `circleMatrixGen` at the emitted schedule;
* `serialization_complete` — **obligation (b), UNPROVED interface hypothesis.**
  the chosen square projection is the affine map through `deployedMap`;
* `coord_bookkeeping` — the field-coordinate count of the transcribed fixed
  prefix; supplied by `spendPrefix_field_coords`.

`map_is_circle` and `serialization_complete` compose to
`FaithfulCircleView.view_is_circle_affine`.  A separate completeness theorem
would still be needed to transfer this projection result to the entire wire. -/
structure FaithfulSpendView (K : Type*) [Field K] (W : Type*) (m : ℕ) where
  /-- emitted Fiat–Shamir circle schedule, evaluated into `K`. -/
  sched : Fin (2 * (2 * m)) → K
  /-- witness-dependent shift `b(w)`. -/
  witShift : W → (Fin (2 * m) → K)
  /-- An abstract square projection of a released field view. -/
  realView : W → (Fin (2 * m) → K) → (Fin (2 * m) → K)
  /-- A candidate square linear mask map, arbitrary a priori. -/
  deployedMap : Matrix (Fin (2 * m)) (Fin (2 * m)) K
  /-- **Obligation (a), UNPROVED.** candidate map = circle matrix at the schedule. -/
  map_is_circle : deployedMap = ((circleMatrixGen K m).map (eval sched))
  /-- **Obligation (b), UNPROVED.** `realView` is affine through the candidate map. -/
  serialization_complete : ∀ (w : W) (R : Fin (2 * m) → K),
      realView w R = witShift w + Matrix.mulVecLin deployedMap R
  /-- **Obligation (c-liveness), UNPROVED for a fixed deployment.** schedule good. -/
  good : ((circleMatrixGen K m).map (eval sched)).det ≠ 0
  /-- field-coordinate count of the transcribed fixed prefix. -/
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

/-- **The abstract square view has witness-independent fibre cardinalities,
GIVEN the refined interface.**  This is routed through
`faithful_view_hides_witness` of `AspisViewBinding`.  It is not a theorem about
the complete spend wire unless a separate sufficiency theorem connects this
projection to that joint view. -/
theorem spendView_hides_witness {W : Type*} {m : ℕ}
    (F : FaithfulSpendView K W m) (w₁ w₂ : W) (y : Fin (2 * m) → K) :
    Nat.card {R : Fin (2 * m) → K // F.realView w₁ R = y}
      = Nat.card {R : Fin (2 * m) → K // F.realView w₂ R = y} :=
  faithful_view_hides_witness F.toCircleView w₁ w₂ y

/-! ## Part 3 — Idealised uniformity lemmas

### 3a. Cardinality of the rejection window

`Profile21SourceExpander::m31` masks a 32-bit hash word to 31 bits and accepts
iff the value is `< P = 2^31 − 1`, retrying otherwise.  We prove only that the
accept window has exactly `P` elements and is canonically bijective with
`Fin P = M31`.  Exact sampler uniformity additionally requires uniform source
words and the appropriate independence across retries and coordinates; those
properties are not formalised here. -/

/-- Canonical bijection accept-window ≃ `Fin P` (models the accepted `M31`). -/
def rejectEquiv (n P : ℕ) (h : P ≤ n) : {w : Fin n // (w : ℕ) < P} ≃ Fin P where
  toFun w := ⟨w.1.1, w.2⟩
  invFun k := ⟨⟨k.1, lt_of_lt_of_le k.2 h⟩, k.2⟩
  left_inv w := by cases w with | mk v hv => cases v; rfl
  right_inv k := by cases k; rfl

/-- **Accept-window cardinality.**  For `P ≤ n`, the rejection accept window
`{w : Fin n // w < P}` has exactly `P` elements.  This is a cardinality fact;
it does not assert a probability law for the source words. -/
theorem reject_window_card (n P : ℕ) (h : P ≤ n) :
    Fintype.card {w : Fin n // (w : ℕ) < P} = P :=
  Fintype.card_congr (rejectEquiv n P h) |>.trans (Fintype.card_fin P)

/-! ### 3b. Ideal uniform mask ⇒ uniform abstract square view

The affine released view at a `good` schedule is `Y = A·R + b(w)` with `A`
invertible (`det ≠ 0`).  An invertible linear map followed by a translation is a
bijection of the mask space onto the view space; the pushforward of the uniform
distribution through any bijection is uniform.  Hence *if* the input law is
the ideal uniform law, the abstract square view is uniform for every witness.
This does not establish that the implemented sampler has that law, or that the
square projection determines the complete spend view. -/

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

/-- **The abstract square view is uniform under an ideal uniform input law.**
At a `good` schedule, the affine square view's law is `uniformOfFintype` for
every witness. -/
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

/-- **Witness independence for the idealised square projection.**  Under an
ideal uniform mask law at a `good` schedule, the two projected distributions
are equal.  Sampler correspondence and sufficiency for the complete joint wire
remain outside this theorem. -/
theorem released_view_law_witness_indep {W : Type*} {m : ℕ} [Fintype K]
    (F : FaithfulCircleView K W m) (w₁ w₂ : W) :
    (PMF.uniformOfFintype (Fin (2 * m) → K)).map (F.realView w₁)
      = (PMF.uniformOfFintype (Fin (2 * m) → K)).map (F.realView w₂) := by
  rw [released_view_uniform F w₁, released_view_uniform F w₂]

/-! ## Legacy free-coordinate closure skeleton

The declarations below predate the aligned component-(A) encoder.  They express
a conditional fact for a square symbolic map whose entries are literally
`circleMatrixGen`.  The implemented component-(A) algebra instead uses a
row-rescaled `circleTMatrix`; its relevant specification is
`CircleTMatrixHiding.ClosesObligationA_T`, with the encoder-side identities in
`CircleTensorBinding`.

Nothing in this section constructs a map from Rust, proves an entry table, or
connects a square projection to the five-section spend wire.  The legacy
`V5MaskMap` name is retained for compatibility.  `ClosesObligationA.deployed_map_eq`
only says that a supplied polynomial identity remains true after evaluation. -/

/-- A legacy square symbolic-map interface over schedule indeterminates. -/
structure V5MaskMap (K : Type*) [Field K] (m : ℕ) where
  /-- One symbolic entry per abstract output coordinate and mask coordinate. -/
  entry : Matrix (Fin (2 * m)) (Fin (2 * m)) (MvPolynomial (Fin (2 * (2 * m))) K)

/-- Entrywise equality of an abstract square symbolic map to
`circleMatrixGen`.  This proposition contains no executable-code
correspondence. -/
def ClosesObligationA {m : ℕ} (v5 : V5MaskMap K m) : Prop :=
  ∀ i j, v5.entry i j = circleMatrixGen K m i j

/-- Evaluation preserves a supplied entrywise polynomial identity.  Calling
the left-hand side a deployed map requires an additional code-correspondence
theorem. -/
theorem ClosesObligationA.deployed_map_eq {m : ℕ} {v5 : V5MaskMap K m}
    (h : ClosesObligationA v5) (sched : Fin (2 * (2 * m)) → K) :
    v5.entry.map (eval sched) = ((circleMatrixGen K m).map (eval sched)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, h i j]

/-! ## Scope summary

**Proved in-kernel (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`):**

* `spendPrefix_contiguous`,
  `spendPrefix_field_bytes_exact`, `spendPrefix_counts`,
  `spendPrefix_field_coords`, `openedFibres_eq`, `c1_leaf_bytes`, `c2_leaf_bytes`,
  `openedRawFieldCoords_eq` check the internal arithmetic of a transcribed
  6,785-byte prefix and the two layer-zero payload widths.  They do not prove
  Rust correspondence or enumerate the later authenticated openings.
* `mask_lane_eq_circle_column`, `circle_column_entry`,
  `view_mask_part_witness_indep`, and `view_shift_mask_indep` are generic
  algebraic identities.
* `rejectEquiv` and `reject_window_card` establish only the accepted-window
  bijection and cardinality.  `map_uniformOfFintype_of_bijective`,
  `mulVec_bijective_of_det_ne_zero`, `released_view_uniform`,
  `released_view_law_witness_indep`, and `spendView_hides_witness` concern an
  idealised square affine view under their explicit hypotheses.

**Open obligations:**

* the legacy fields `FaithfulSpendView.map_is_circle` and
  `FaithfulSpendView.serialization_complete` have no deployed instantiation;
  despite its name, the latter only states affine correctness of a square
  projection;
* no theorem here makes that projection sufficient for the complete joint
  released view;
* no theorem derives ideal independent uniform masks from the Rust entropy
  path;
* no theorem here binds the aligned `circleTMatrix` encoder, the dynamic wire
  inventory, the sumcheck mask, and the remaining v5 masking components into
  one verifier theorem. -/

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
