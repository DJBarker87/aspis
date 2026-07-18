import Mathlib

/-!
# v5 Component C: the `Emat` mathematical-correspondence seam

This file kernel-proves the generic linear algebra that reduces the
Component-C obligation **B1 — matrix faithfulness of the conditioned-view
evaluator** — to *basis-column correspondence*, and nothing stronger.  It is
a standalone leaf: it imports Mathlib only and can be wired into the
project's root import file without importing any deployment artifact.

**What is proved (unconditional, kernel-checked).**

1. *Pivot encoder onto `ker ℓ`.*  For a linear functional
   `ℓ : (Fin 1024 → K) →ₗ[K] K` over a field `K` whose pivot coefficient is
   one (`ℓ (Pi.single p 1) = 1` — the only hypothesis; no support
   restriction on `ℓ` is needed), the encoder that places 1023 free
   coordinates off the pivot and inserts the unique pivot correction lands
   in `ker ℓ` (`ell_pivotEncoder`), recovers every free coordinate
   (`pivotEncoder_apply_succAbove`), and is a linear equivalence
   `(Fin 1023 → K) ≃ₗ[K] ker ℓ` (`pivotEncoderEquiv`).  Surjectivity onto
   the kernel is **derived from the pivot correction**
   (`pivotEncoder_surjective_onto_ker`, via the kernel-rigidity lemma
   `ker_ell_ext`), not assumed as a slogan.

2. *Row enumeration.*  The 76 conditioned-view rows are pinned as 72
   layer-zero rows, three MLE-claim rows and one structured-terminal row:
   the tagged type `ConditionedRow` is in bijection with `Fin 76`
   (`conditionedRowEquiv`), with the block layout `layerZero i ↦ i`
   (indices 0–71), `mle j ↦ 72 + j` (72–74), `terminal ↦ 75`.  The
   constructor images are pairwise disjoint (`toFin_layerZero_ne_mle`,
   `toFin_layerZero_ne_terminal`, `toFin_mle_ne_terminal`), jointly
   injective (`toFin_injective`), and exhaustive (`row_index_exhaustive`);
   `Fintype.card ConditionedRow = 76` (`card_conditionedRow`).  This pins
   the *model's* row indexing only; that the deployed serialisation uses
   the same order is part of the open correspondence recorded below.

3. *The seam.*  For any linear `E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)`,
   the matrix `ematOf E` is defined by evaluating `E` on every standard
   basis vector (`ematOf E r c = E (Pi.single c 1) r`), and
   `(ematOf E).mulVec v = E v` for every `v` (`ematOf_mulVec`).  This
   equality is **not definitional**: an explicit `rfl` proof attempt at
   exactly this statement is rejected (at the default recursion limit the
   definitional-unfolding attempt aborts with `maximum recursion depth has
   been reached` — the left side is a `Finset.sum` fold over the 1023
   columns, the right an application of the opaque `E`).  The converse
   (`eq_of_basis_columns`) states that two linear maps agreeing on all
   1023 basis vectors are equal — linearity plus basis columns determine
   the full evaluator.  Together these are the exact reduction of B1 to
   basis-column correspondence (`deployed_matrix_faithful_of_interfaces`).

4. *Sparsity.*  The encoder image of a scaled basis vector is supported on
   its own free row and (at most) the pivot row (`pivotEncoder_single`,
   `pivotEncoder_single_apply_of_ne`).

**The conditional ceiling.**  The strongest statement about the deployed
system in this file is conditional on two explicit named interface
`Prop`s, stated and **left unproved**:

* `RustEvaluatorLinear` — the deployed Rust conditioned-view evaluator is
  linear;
* `RustBasisColumnsMatch` — the deployed evaluator agrees with `E`
  (equivalently, with the columns of `ematOf E`) on each of the 1023
  standard basis vectors.

Under both — and only under both — the deployed evaluator equals the model
evaluator and the `Emat` matrix action on every input
(`deployed_eq_model_of_interfaces`,
`deployed_matrix_faithful_of_interfaces`).  Nothing in this file proves
either interface for any concrete evaluator, and in particular not for the
deployed Rust.

**Offline artifact status.**  The earlier `Emat` artifacts were generated
against a pre-salt transcript schedule and are stale after the public-salt
and Component-B pivot changes.  Their hashes are deliberately not recorded
here and they are not evidence for the current salted schedule.  No byte
string, hash, or artifact content is modelled, hypothesised, or ingested
anywhere in this file, and **no statement here asserts that any artifact,
its bytes, or its hashes satisfy `RustBasisColumnsMatch`,
`RustEvaluatorLinear`, or any other hypothesis.**

**What remains OPEN.**  The post-combination matrix `Fmat` and its
faithfulness; the legal witness-difference space `Δ`; the
conditional-decoupling containment (C-DEC) itself; and every
byte/hash-level ingestion step for the emitted artifact (parsing, hashing,
and the identification of its stored columns and row order with the maps
and enumeration here).  The two interface `Prop`s above are likewise left
unproved.  Until those close, nothing in this file upgrades the audit
status of Component C.
-/

namespace AspisV5ComponentCEmatModel

/-! ## Pointwise extensionality across a pivot split

`Fin.succAbove p : Fin 1023 → Fin 1024` is the monotone injection whose
image is exactly the 1023 non-pivot rows, so a coefficient word is
determined by its pivot entry together with its free entries. -/

/-- Two coefficient words agreeing at the pivot row and at every free row
are equal: `p` and the `p.succAbove i` exhaust `Fin 1024`. -/
theorem pivot_free_funext {K : Type*} [Field K] (p : Fin 1024) {f g : Fin 1024 → K}
    (hpiv : f p = g p)
    (hfree : ∀ i : Fin 1023, f (p.succAbove i) = g (p.succAbove i)) : f = g := by
  funext j
  rcases eq_or_ne j p with rfl | hj
  · exact hpiv
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
    exact hfree i

/-! ## The pivot encoder onto `ker ℓ`

The mask space of the audit is the hyperplane `ker ℓ` of the
1024-coordinate word space.  The deployed sampler is modelled as: choose
1023 free coordinates, then insert the unique pivot correction that puts
the word on the hyperplane.  Everything below is generic in the field `K`,
the functional `ℓ`, and the pivot position `p`; the only hypothesis ever
used is the unit pivot coefficient `ℓ (Pi.single p 1) = 1`. -/

section PivotEncoder

variable {K : Type*} [Field K]

/-- Free-coordinate placement: `freeInsert p v` puts `v i` at row
`p.succAbove i` and `0` at the pivot row.  This is the correction-free half
of the encoder, bundled as a linear map. -/
def freeInsert (p : Fin 1024) : (Fin 1023 → K) →ₗ[K] (Fin 1024 → K) where
  toFun v := p.insertNth 0 v
  map_add' v w := by
    refine pivot_free_funext p ?_ fun i => ?_ <;> simp
  map_smul' a v := by
    refine pivot_free_funext p ?_ fun i => ?_ <;> simp

/-- The placement leaves the pivot row at `0`. -/
@[simp] theorem freeInsert_apply_pivot (p : Fin 1024) (v : Fin 1023 → K) :
    freeInsert p v p = 0 := by
  simp [freeInsert]

/-- The placement stores free coordinate `i` at row `p.succAbove i`. -/
@[simp] theorem freeInsert_apply_succAbove (p : Fin 1024) (v : Fin 1023 → K)
    (i : Fin 1023) : freeInsert p v (p.succAbove i) = v i := by
  simp [freeInsert]

/-- Placement of the `i`-th free basis vector is the `p.succAbove i`-th
standard basis vector of the word space. -/
theorem freeInsert_single (p : Fin 1024) (i : Fin 1023) (x : K) :
    freeInsert p (Pi.single i x) = Pi.single (p.succAbove i) x := by
  refine pivot_free_funext p ?_ fun i' => ?_
  · rw [freeInsert_apply_pivot, Pi.single_eq_of_ne (Fin.succAbove_ne p i).symm]
  · rw [freeInsert_apply_succAbove]
    rcases eq_or_ne i' i with rfl | hii
    · rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hii, Pi.single_eq_of_ne (Fin.succAbove_right_injective.ne hii)]

variable (ell : (Fin 1024 → K) →ₗ[K] K) (p : Fin 1024)

/-- **The pivot encoder.**  `pivotEncoder ℓ p v` places the 1023 free
coordinates off the pivot and inserts the unique pivot correction
`-ℓ (freeInsert p v) • Pi.single p 1`.  The definition needs no hypothesis
on `ℓ`; the kernel membership below uses exactly the unit pivot
coefficient. -/
def pivotEncoder : (Fin 1023 → K) →ₗ[K] (Fin 1024 → K) :=
  freeInsert p - (ell ∘ₗ freeInsert p).smulRight (Pi.single p 1)

/-- The encoder's closed form: placement minus the pivot correction. -/
theorem pivotEncoder_apply (v : Fin 1023 → K) :
    pivotEncoder ell p v = freeInsert p v - ell (freeInsert p v) • Pi.single p 1 :=
  rfl

/-- **The encoder recovers every free coordinate** (for every `ℓ`, with no
pivot hypothesis): the correction only touches the pivot row. -/
@[simp] theorem pivotEncoder_apply_succAbove (v : Fin 1023 → K) (i : Fin 1023) :
    pivotEncoder ell p v (p.succAbove i) = v i := by
  simp [pivotEncoder_apply]

/-- The pivot row of an encoded word carries exactly the correction term. -/
theorem pivotEncoder_apply_pivot (v : Fin 1023 → K) :
    pivotEncoder ell p v p = -ell (freeInsert p v) := by
  simp [pivotEncoder_apply, Pi.single_eq_same]

/-- **The encoder lands in `ker ℓ`.**  The unit pivot coefficient makes the
correction cancel `ℓ` of the placement exactly. -/
theorem ell_pivotEncoder (hpiv : ell (Pi.single p 1) = 1) (v : Fin 1023 → K) :
    ell (pivotEncoder ell p v) = 0 := by
  rw [pivotEncoder_apply, map_sub, map_smul, hpiv, smul_eq_mul, mul_one, sub_self]

/-- Membership form of `ell_pivotEncoder`. -/
theorem pivotEncoder_mem_ker (hpiv : ell (Pi.single p 1) = 1) (v : Fin 1023 → K) :
    pivotEncoder ell p v ∈ LinearMap.ker ell :=
  LinearMap.mem_ker.mpr (ell_pivotEncoder ell p hpiv v)

/-- **Rigidity of `ker ℓ` across the pivot split**: two kernel words
agreeing on every free row are equal.  Their difference is supported at the
pivot row alone, and `ℓ` — with unit pivot coefficient — reads off exactly
that entry, which must therefore vanish. -/
theorem ker_ell_ext (hpiv : ell (Pi.single p 1) = 1) {c c' : Fin 1024 → K}
    (hc : ell c = 0) (hc' : ell c' = 0)
    (hfree : ∀ i : Fin 1023, c (p.succAbove i) = c' (p.succAbove i)) : c = c' := by
  have hsingle : c - c' = Pi.single p ((c - c') p) := by
    refine pivot_free_funext p ?_ fun i => ?_
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (Fin.succAbove_ne p i), Pi.sub_apply, hfree i, sub_self]
  have hp0 : (c - c') p = 0 := by
    have h0 : ell (c - c') = 0 := by rw [map_sub, hc, hc', sub_zero]
    rw [hsingle, show Pi.single p ((c - c') p) = ((c - c') p) • Pi.single p (1 : K) by
        rw [← Pi.single_smul, smul_eq_mul, mul_one],
      map_smul, hpiv, smul_eq_mul, mul_one] at h0
    exact h0
  have hzero : c - c' = 0 := by rw [hsingle, hp0, Pi.single_zero]
  exact sub_eq_zero.mp hzero

/-- **Surjectivity onto `ker ℓ` is derived from the pivot correction, not
assumed.**  The explicit preimage of a kernel word is its own
free-coordinate restriction: the encoder reproduces the free rows by
`pivotEncoder_apply_succAbove`, and `ker_ell_ext` closes the pivot row. -/
theorem pivotEncoder_surjective_onto_ker (hpiv : ell (Pi.single p 1) = 1)
    (c : Fin 1024 → K) (hc : c ∈ LinearMap.ker ell) :
    ∃ v : Fin 1023 → K, pivotEncoder ell p v = c :=
  ⟨fun i => c (p.succAbove i),
    ker_ell_ext ell p hpiv (ell_pivotEncoder ell p hpiv _) (LinearMap.mem_ker.mp hc)
      fun i => by simp⟩

/-- **The pivot encoder is a linear equivalence onto `ker ℓ`.**  Forward
map: the encoder, corestricted to the kernel.  Inverse: restriction to the
free coordinates.  Both composites are the identity — one by coordinate
recovery, the other by kernel rigidity — so this is a bundled `≃ₗ`, with
surjectivity coming from the pivot correction and not from any rank
assumption. -/
def pivotEncoderEquiv (hpiv : ell (Pi.single p 1) = 1) :
    (Fin 1023 → K) ≃ₗ[K] LinearMap.ker ell :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict (LinearMap.ker ell) (pivotEncoder ell p)
      (pivotEncoder_mem_ker ell p hpiv))
    ((LinearMap.funLeft K K p.succAbove) ∘ₗ (LinearMap.ker ell).subtype)
    (by
      apply LinearMap.ext
      rintro ⟨c, hc⟩
      apply Subtype.ext
      show pivotEncoder ell p (fun i => c (p.succAbove i)) = c
      exact ker_ell_ext ell p hpiv (ell_pivotEncoder ell p hpiv _)
        (LinearMap.mem_ker.mp hc) fun i => by simp)
    (by
      apply LinearMap.ext
      intro v
      funext i
      show pivotEncoder ell p v (p.succAbove i) = v i
      simp)

/-- The forward map of `pivotEncoderEquiv` is literally the pivot encoder. -/
@[simp] theorem pivotEncoderEquiv_apply_coe (hpiv : ell (Pi.single p 1) = 1)
    (v : Fin 1023 → K) :
    (pivotEncoderEquiv ell p hpiv v : Fin 1024 → K) = pivotEncoder ell p v :=
  rfl

/-- The inverse map of `pivotEncoderEquiv` is restriction to the free
coordinates. -/
@[simp] theorem pivotEncoderEquiv_symm_apply (hpiv : ell (Pi.single p 1) = 1)
    (c : LinearMap.ker ell) (i : Fin 1023) :
    (pivotEncoderEquiv ell p hpiv).symm c i = (c : Fin 1024 → K) (p.succAbove i) :=
  rfl

/-- Closed form of an encoded scaled basis vector: its own free row plus
(at most) a pivot-row correction.  No pivot hypothesis is needed. -/
theorem pivotEncoder_single (i : Fin 1023) (x : K) :
    pivotEncoder ell p (Pi.single i x)
      = Pi.single (p.succAbove i) x
        - ell (Pi.single (p.succAbove i) x) • Pi.single p 1 := by
  rw [pivotEncoder_apply, freeInsert_single]

/-- **Sparsity of encoded basis vectors**: away from its own free row
`p.succAbove i` and the pivot row `p`, an encoded scaled basis vector
vanishes. -/
theorem pivotEncoder_single_apply_of_ne (i : Fin 1023) (x : K) {j : Fin 1024}
    (hjp : j ≠ p) (hji : j ≠ p.succAbove i) :
    pivotEncoder ell p (Pi.single i x) j = 0 := by
  obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hjp
  have hii : i' ≠ i := fun h => hji (congrArg p.succAbove h)
  rw [pivotEncoder_apply_succAbove, Pi.single_eq_of_ne hii]

end PivotEncoder

/-! ## Row enumeration: 72 layer-zero + 3 MLE + 1 terminal = 76

The conditioned view has 76 rows.  `ConditionedRow` tags them by meaning
and `conditionedRowEquiv` pins the model's block layout: the layer-zero
block occupies indices 0–71, the three MLE claims 72–74, the structured
terminal claim 75.  This is the *model's* numbering convention; agreement
with the deployed serialisation order is part of the open correspondence
recorded at the end of the file. -/

/-- The 76 conditioned-view rows, tagged by meaning: 72 authenticated
layer-zero values, three MLE claims, one structured terminal claim. -/
inductive ConditionedRow : Type
  /-- One of the 72 authenticated layer-zero values. -/
  | layerZero (i : Fin 72)
  /-- One of the three MLE claims. -/
  | mle (j : Fin 3)
  /-- The structured terminal claim. -/
  | terminal
  deriving DecidableEq, Fintype

namespace ConditionedRow

/-- The model row numbering: layer-zero block first (0–71), then the MLE
block (72–74), then the terminal row (75). -/
def toFin : ConditionedRow → Fin 76
  | .layerZero i => i.castLE (by norm_num)
  | .mle j => ⟨72 + (j : ℕ), by omega⟩
  | .terminal => ⟨75, by norm_num⟩

/-- The inverse numbering, by block membership. -/
def ofFin (k : Fin 76) : ConditionedRow :=
  if h72 : (k : ℕ) < 72 then .layerZero ⟨k, h72⟩
  else if h75 : (k : ℕ) < 75 then .mle ⟨(k : ℕ) - 72, by omega⟩
  else .terminal

/-- Round trip on tags, checked by the kernel over all 76 rows: the
numbering has no collisions. -/
theorem ofFin_toFin : ∀ r : ConditionedRow, ofFin r.toFin = r := by decide

/-- Round trip on indices, checked by the kernel over all 76 indices: the
numbering has no gaps. -/
theorem toFin_ofFin : ∀ k : Fin 76, (ofFin k).toFin = k := by decide

/-- Layer-zero row `i` sits at index `i`. -/
@[simp] theorem toFin_layerZero_val (i : Fin 72) : (toFin (.layerZero i) : ℕ) = i := rfl

/-- MLE row `j` sits at index `72 + j`. -/
@[simp] theorem toFin_mle_val (j : Fin 3) : (toFin (.mle j) : ℕ) = 72 + j := rfl

/-- The terminal row sits at index `75`. -/
@[simp] theorem toFin_terminal_val : (toFin .terminal : ℕ) = 75 := rfl

end ConditionedRow

/-- **The tagged row sum is in bijection with `Fin 76`**: the row
constructors are jointly exhaustive and collision-free. -/
def conditionedRowEquiv : ConditionedRow ≃ Fin 76 :=
  ⟨ConditionedRow.toFin, ConditionedRow.ofFin, ConditionedRow.ofFin_toFin,
    ConditionedRow.toFin_ofFin⟩

/-- The row numbering is injective (no collisions, across all
constructors). -/
theorem toFin_injective : Function.Injective ConditionedRow.toFin :=
  conditionedRowEquiv.injective

/-- Disjointness: no layer-zero row shares an index with an MLE row. -/
theorem toFin_layerZero_ne_mle (i : Fin 72) (j : Fin 3) :
    ConditionedRow.toFin (.layerZero i) ≠ ConditionedRow.toFin (.mle j) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ConditionedRow.toFin_layerZero_val, ConditionedRow.toFin_mle_val] at hv
  omega

/-- Disjointness: no layer-zero row shares an index with the terminal row. -/
theorem toFin_layerZero_ne_terminal (i : Fin 72) :
    ConditionedRow.toFin (.layerZero i) ≠ ConditionedRow.toFin .terminal := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ConditionedRow.toFin_layerZero_val, ConditionedRow.toFin_terminal_val] at hv
  omega

/-- Disjointness: no MLE row shares an index with the terminal row. -/
theorem toFin_mle_ne_terminal (j : Fin 3) :
    ConditionedRow.toFin (.mle j) ≠ ConditionedRow.toFin .terminal := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ConditionedRow.toFin_mle_val, ConditionedRow.toFin_terminal_val] at hv
  omega

/-- Exhaustiveness: every index of `Fin 76` is a layer-zero row, an MLE
row, or the terminal row. -/
theorem row_index_exhaustive (k : Fin 76) :
    (∃ i : Fin 72, ConditionedRow.toFin (.layerZero i) = k) ∨
      (∃ j : Fin 3, ConditionedRow.toFin (.mle j) = k) ∨
        ConditionedRow.toFin .terminal = k := by
  have h := ConditionedRow.toFin_ofFin k
  rcases hr : ConditionedRow.ofFin k with i | j | _
  · rw [hr] at h; exact Or.inl ⟨i, h⟩
  · rw [hr] at h; exact Or.inr (Or.inl ⟨j, h⟩)
  · rw [hr] at h; exact Or.inr (Or.inr h)

/-- The tagged row type has exactly 76 elements. -/
theorem card_conditionedRow : Fintype.card ConditionedRow = 76 := by
  rw [Fintype.card_congr conditionedRowEquiv, Fintype.card_fin]

/-- Bookkeeping only: the block sizes sum to 76. -/
theorem row_partition_count : 72 + 3 + 1 = 76 := by decide

/-! ## The seam: `Emat` from basis columns

`ematOf E` is the 76×1023 matrix whose column `c` is the evaluator's image
of the `c`-th standard basis vector.  The two theorems that constitute the
B1 reduction are:

* forward (`ematOf_mulVec`): the matrix action of `ematOf E` agrees with
  `E` everywhere — **not** a definitional equality (see the docstring
  there);
* converse (`eq_of_basis_columns`): linearity plus agreement on all 1023
  basis columns determines the evaluator.

Nothing here mentions any concrete matrix entries, bytes, or hashes. -/

section Seam

variable {K : Type*} [Field K]

/-- Basis decomposition of an evaluator application: `E v` is the
`v`-weighted sum of the 1023 basis columns of `E`. -/
theorem linearMap_apply_eq_sum_basis (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K))
    (v : Fin 1023 → K) :
    E v = ∑ c : Fin 1023, v c • E (Pi.single c 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show Pi.single c (v c) = v c • Pi.single c (1 : K) by
      rw [← Pi.single_smul, smul_eq_mul, mul_one],
    map_smul]

/-- **The determination theorem (converse seam): equality on all 1023
basis columns plus linearity determines the full evaluator.**  Two linear
maps agreeing on every standard basis vector are equal. -/
theorem eq_of_basis_columns {E E' : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)}
    (h : ∀ c : Fin 1023, E (Pi.single c 1) = E' (Pi.single c 1)) : E = E' :=
  LinearMap.ext fun v => by
    rw [linearMap_apply_eq_sum_basis, linearMap_apply_eq_sum_basis]
    exact Finset.sum_congr rfl fun c _ => by rw [h c]

/-- Packaging of the determination theorem as an equivalence: two linear
evaluators are equal iff their 1023 basis columns agree. -/
theorem eq_iff_basis_columns (E E' : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) :
    E = E' ↔ ∀ c : Fin 1023, E (Pi.single c 1) = E' (Pi.single c 1) :=
  ⟨fun h c => by rw [h], eq_of_basis_columns⟩

/-- **`Emat` from basis columns**: entry `(r, c)` is the `r`-th coordinate
of the evaluator's image of the `c`-th standard basis vector, so column
`c` is exactly `E (Pi.single c 1)`. -/
def ematOf (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) : Matrix (Fin 76) (Fin 1023) K :=
  Matrix.of fun r c => E (Pi.single c 1) r

/-- Entry evaluation of `ematOf`. -/
@[simp] theorem ematOf_apply (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) (r : Fin 76)
    (c : Fin 1023) : ematOf E r c = E (Pi.single c 1) r :=
  rfl

/-- Column `c` of `ematOf E` is the evaluator's image of the `c`-th
standard basis vector. -/
theorem ematOf_col (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) (c : Fin 1023) :
    (ematOf E).col c = E (Pi.single c 1) :=
  rfl

/-- The matrix action of `ematOf E`, bundled as a linear map, is `E`
itself: both sides are linear and agree on every basis column
(`Matrix.mulVec_single_one`), so the determination theorem applies. -/
theorem mulVecLin_ematOf (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) :
    (ematOf E).mulVecLin = E :=
  eq_of_basis_columns fun c => by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, ematOf_col]

/-- **The seam, forward direction: `(ematOf E).mulVec v = E v` for every
`v`.**  This equality is **not definitional**: an explicit `rfl` proof
attempt at exactly this statement fails (at the default recursion limit
the definitional-unfolding attempt aborts with `maximum recursion depth
has been reached`, since the left side is a `dotProduct` `Finset.sum` over
the 1023 columns and the right an application of the opaque `E`).  It is
proved through the basis decomposition and the determination theorem, and
that is the content of the seam: matrix faithfulness is exactly
basis-column agreement plus linearity. -/
theorem ematOf_mulVec (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) (v : Fin 1023 → K) :
    (ematOf E).mulVec v = E v := by
  rw [← Matrix.mulVecLin_apply, mulVecLin_ematOf]

/-! ## Conditional ceiling: named, unproved deployment interfaces

The two `Prop`s below are the *only* bridge this file offers to the
deployed system, and both are **left unproved**.  No artifact, byte
string, or hash is accepted as evidence for either; in particular, the
stale pre-salt artifacts are not premises. -/

/-- **UNRESOLVED INTERFACE (not proved): linearity of the deployed
evaluator.**  `rustEval` abstracts the deployed Rust conditioned-view
evaluator on the 1023 free coordinates.  Nothing in this file discharges
this `Prop`, and no hash equality could. -/
def RustEvaluatorLinear (rustEval : (Fin 1023 → K) → Fin 76 → K) : Prop :=
  IsLinearMap K rustEval

/-- **UNRESOLVED INTERFACE (not proved): basis-column correspondence.**
The deployed evaluator agrees with the model evaluator `E` — equivalently,
with the columns of `ematOf E` (`ematOf_col`) — on each of the 1023
standard basis vectors.  Nothing in this file discharges this `Prop` for
any concrete evaluator, and in particular not for the deployed Rust. -/
def RustBasisColumnsMatch (rustEval : (Fin 1023 → K) → Fin 76 → K)
    (E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)) : Prop :=
  ∀ c : Fin 1023, rustEval (Pi.single c 1) = (ematOf E).col c

/-- **The B1 reduction, model form (conditional).**  If the deployed
evaluator is linear and matches the 1023 basis columns, it agrees with the
model evaluator `E` on *every* input.  Conditional on the two unproved
interfaces; asserts nothing about the deployed system unconditionally. -/
theorem deployed_eq_model_of_interfaces {rustEval : (Fin 1023 → K) → Fin 76 → K}
    {E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)} (hlin : RustEvaluatorLinear rustEval)
    (hcols : RustBasisColumnsMatch rustEval E) (v : Fin 1023 → K) :
    rustEval v = E v := by
  have hL : IsLinearMap.mk' rustEval hlin = E :=
    eq_of_basis_columns fun c => by
      rw [IsLinearMap.mk'_apply, hcols c, ematOf_col]
  calc rustEval v = IsLinearMap.mk' rustEval hlin v := (IsLinearMap.mk'_apply hlin v).symm
    _ = E v := by rw [hL]

/-- **The B1 reduction (conditional ceiling).**  Under
`RustEvaluatorLinear` and `RustBasisColumnsMatch` — and only under them —
the deployed evaluator's output is the `Emat` matrix action on every
input.  This is the exact theorem reducing B1 (matrix faithfulness) to
basis-column correspondence.  Neither interface is proved here, so this
theorem makes no unconditional claim about the deployed system, its
emitted artifact, or that artifact's hashes. -/
theorem deployed_matrix_faithful_of_interfaces {rustEval : (Fin 1023 → K) → Fin 76 → K}
    {E : (Fin 1023 → K) →ₗ[K] (Fin 76 → K)} (hlin : RustEvaluatorLinear rustEval)
    (hcols : RustBasisColumnsMatch rustEval E) (v : Fin 1023 → K) :
    rustEval v = (ematOf E).mulVec v := by
  rw [deployed_eq_model_of_interfaces hlin hcols v, ematOf_mulVec]

end Seam

/-! ## Non-vacuity: the pivot-encoder hypotheses are concretely instantiable

Two concrete instantiations of `ℓ (Pi.single p 1) = 1` over `K = ℚ`: the
sum-of-coordinates functional at pivot 0 (where the pivot correction is
genuinely nonzero on every encoded basis vector), and a coordinate
projection at pivot 1023.  These witness that the hypotheses of the
pivot-encoder theorems are satisfiable; they say nothing about the
deployed `ℓ`. -/

section NonVacuity

/-- The sum-of-coordinates functional on `ℚ^1024`. -/
def demoEll : (Fin 1024 → ℚ) →ₗ[ℚ] ℚ := ∑ j : Fin 1024, LinearMap.proj j

/-- Every standard basis vector has `demoEll`-value 1, so every pivot
satisfies the unit-pivot-coefficient hypothesis for `demoEll`. -/
theorem demoEll_single (j : Fin 1024) : demoEll (Pi.single j 1) = 1 := by
  rw [demoEll, LinearMap.sum_apply]
  simp only [LinearMap.proj_apply]
  rw [Finset.sum_pi_single']
  simp

/-- The demo pivot: row 0. -/
def demoPivot : Fin 1024 := ⟨0, by norm_num⟩

/-- The pivot correction is genuinely nonzero in the demo: every encoded
free basis vector carries pivot entry `-1`. -/
theorem demoEll_pivot_correction (i : Fin 1023) :
    pivotEncoder demoEll demoPivot (Pi.single i 1) demoPivot = -1 := by
  rw [pivotEncoder_apply_pivot, freeInsert_single, demoEll_single]

/- Elaboration hygiene only: stop the unifier from delta-unfolding the
1024-term sum `demoEll` while the equivalence below is instantiated (the
unfolding is a definitional-reduction blow-up, not a mathematical issue).
The attribute changes no statement, no proof, and no axiom. -/
attribute [irreducible] demoEll

/-- Concrete instantiation of the pivot-encoder equivalence at `K = ℚ`,
`ℓ = demoEll`, pivot 0: the hypotheses of `pivotEncoderEquiv` are
satisfiable. -/
def demoEncoderEquiv : (Fin 1023 → ℚ) ≃ₗ[ℚ] LinearMap.ker demoEll :=
  pivotEncoderEquiv demoEll demoPivot (demoEll_single demoPivot)

/-- A second demo functional: the coordinate projection at row 1023. -/
def demoProjEll : (Fin 1024 → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj ⟨1023, by norm_num⟩

/-- The projection has unit pivot coefficient at its own row. -/
theorem demoProjEll_pivot : demoProjEll (Pi.single ⟨1023, by norm_num⟩ 1) = 1 := by
  rw [demoProjEll, LinearMap.proj_apply, Pi.single_eq_same]

/-- Concrete instantiation of the pivot-encoder equivalence at a nonzero
pivot index (1023) with a different functional. -/
def demoProjEncoderEquiv : (Fin 1023 → ℚ) ≃ₗ[ℚ] LinearMap.ker demoProjEll :=
  pivotEncoderEquiv demoProjEll ⟨1023, by norm_num⟩ demoProjEll_pivot

end NonVacuity

/-! ## Axiom audit -/

#print axioms pivot_free_funext
#print axioms freeInsert
#print axioms freeInsert_apply_pivot
#print axioms freeInsert_apply_succAbove
#print axioms freeInsert_single
#print axioms pivotEncoder
#print axioms pivotEncoder_apply
#print axioms pivotEncoder_apply_succAbove
#print axioms pivotEncoder_apply_pivot
#print axioms ell_pivotEncoder
#print axioms pivotEncoder_mem_ker
#print axioms ker_ell_ext
#print axioms pivotEncoder_surjective_onto_ker
#print axioms pivotEncoderEquiv
#print axioms pivotEncoderEquiv_apply_coe
#print axioms pivotEncoderEquiv_symm_apply
#print axioms pivotEncoder_single
#print axioms pivotEncoder_single_apply_of_ne
#print axioms ConditionedRow.toFin
#print axioms ConditionedRow.ofFin
#print axioms ConditionedRow.ofFin_toFin
#print axioms ConditionedRow.toFin_ofFin
#print axioms ConditionedRow.toFin_layerZero_val
#print axioms ConditionedRow.toFin_mle_val
#print axioms ConditionedRow.toFin_terminal_val
#print axioms conditionedRowEquiv
#print axioms toFin_injective
#print axioms toFin_layerZero_ne_mle
#print axioms toFin_layerZero_ne_terminal
#print axioms toFin_mle_ne_terminal
#print axioms row_index_exhaustive
#print axioms card_conditionedRow
#print axioms row_partition_count
#print axioms linearMap_apply_eq_sum_basis
#print axioms eq_of_basis_columns
#print axioms eq_iff_basis_columns
#print axioms ematOf
#print axioms ematOf_apply
#print axioms ematOf_col
#print axioms mulVecLin_ematOf
#print axioms ematOf_mulVec
#print axioms RustEvaluatorLinear
#print axioms RustBasisColumnsMatch
#print axioms deployed_eq_model_of_interfaces
#print axioms deployed_matrix_faithful_of_interfaces
#print axioms demoEll
#print axioms demoEll_single
#print axioms demoPivot
#print axioms demoEncoderEquiv
#print axioms demoEll_pivot_correction
#print axioms demoProjEll
#print axioms demoProjEll_pivot
#print axioms demoProjEncoderEquiv

end AspisV5ComponentCEmatModel
