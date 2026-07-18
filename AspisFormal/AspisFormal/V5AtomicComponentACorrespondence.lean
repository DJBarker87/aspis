import AspisFormal.V5AtomicComponentA

/-!
# Rust ↔ Lean correspondence for v5 Component A (atomic-v3 hyperplane)

`V5AtomicComponentA.lean` proves the deployed 72-by-96 monomial-basis map,
restricted to the coefficient-sum-zero hyperplane `∑ i, c i = 0`, is surjective
onto every 72-coordinate view (`deployedAtomicV3ComponentA_surjective`).  That is
the *abstract* hiding fact.  This file builds the commuting diagram tying the
concrete Rust sampler / layout / encoder (`crates/aspis-prover/src/v5_mask.rs`)
to that theorem, and states — as minimal interfaces — the exact edges that cannot
be closed without importing Rust execution semantics.

## The five obligations (a)–(e)

The Rust path and the Lean path meet at the ordinary (monomial) `∑ = 0`
hyperplane, BEFORE the natural conversion:

```
Rust sample_atomic_m31_block_mask
  --(c) reindex p/q blocks → flat Fin 96 order; ∑_p+∑_q = coefficientSum
  --(b) pivot p[36] = −(∑ other 95) ⟹ coefficientSum = 0
  ⟶  ordinary vector c, coefficientSum c = 0
  --(a) monomialToNatural conversion (per 48-block) → natural coeffs n
  --  stored interleaved at rows 896+2k (p), 897+2k (q)   [layout]
  --(d) row-896 aligned encoder weight · natural eval = deployed monomial map
  ⟶  deployedFibreRectangularEval  (Lean, DONE: surjective on ∑=0)
  --(e) M31 → QM31 ring embedding φ  (∑=0 ↦ ∑=0, commutes with mulVec)
```

For each edge, this file records precisely: **[Lean]** proved here in-kernel,
**[Cert]** bound by a recomputed numeric certificate, **[Edge]** an irreducible
`code = model` obligation stated as a minimal theorem/interface.

* **(a) ordinary → natural conversion.**
  **[Lean]** `conversion_invertible` (= `naturalCoeffMatrix_det_ne_zero`) and
  `natural_after_conversion_eq_monomial` (= `naturalEval_mul_monomialToNatural`)
  give the invertibility and the *natural-eval ∘ conversion = monomial-eval*
  identity abstractly.  **[Cert]** `naturalLine_block_certificate` and
  `naturalCoeffMatrix_block_eq` kernel-check the leading 8×8 block of the table
  recomputed and emitted by `tools/v5_atomic_a_conversion_cert.rs` against the
  mechanised `naturalLinePoly`/`naturalCoeffMatrix` coefficients, entry by entry,
  at default settings and with `decide`/`norm_num` (no `native_decide`).  The
  Rust tool independently self-verifies the full 48×48 mutual-inverse; the
  in-kernel Chebyshev expansion cost is what caps the mechanised block (each
  higher block needs one more `T_{2^b}` and a higher-degree `ring`).  **[Edge]**
  `RustConversionIsMonomialToNatural`: the Rust `ordinary_monomials_in_natural_line_basis(48)`
  numeric table equals `monomialToNatural DeployedField 48` in every entry
  (the certificate closes the natural-basis half; that the applied conversion is
  its inverse is the tool's `verify_mutual_inverse` audit).

* **(b) coefficient-sum-zero preservation.**  **[Lean]** fully closed:
  `sampledVector_coefficientSum_zero` (pivot ⟹ ∑ = 0) and
  `sampledVector_surjects_hyperplane` (the 95-free-coordinate pivot construction
  parametrises the *entire* `coefficientSum = 0` hyperplane).  **[Edge]**
  `RustSamplerComputesSampledVector`: the Rust function `sample_atomic_m31_block_mask`
  returns the vector modelled by `sampledVector`.

* **(c) stored layout ↔ abstract Fin 96 order.**  **[Lean]** fully closed:
  `coefficientSum_ordinaryOfBlocks` (Rust's `p`-then-`q` fold = Lean
  `coefficientSum`), and `layoutRow` with `layoutRow_injective` /
  `layoutRow_image_reserved` (the interleaved rows `896+2k` / `897+2k` biject
  onto the reserved block `896..991`, and sums reindex through it).

* **(d) row-896 aligned encoder weight → deployed map.**  **[Lean]** the
  abstract algebra (a) plus `deployedFibre_selected_minor_eq` (imported).
  **[Edge]** `EncoderRowsAreNaturalEval` and `Weight896`: the deployed encoder's
  realised leakage rows equal `naturalEvalMatrix` at the deployed schedule with
  the aligned `B_896` row weight.  Bundled as the hypothesis `hcommute` of
  `deployed_encoder_transfers_surjectivity`.

* **(e) M31 → QM31 embedding.**  **[Lean]** fully closed for an arbitrary ring
  hom `φ : DeployedField →+* L` (instantiated by `algebraMap (ZMod P) QM31`,
  since QM31 is an M31-algebra and is not itself a Lean object here):
  `embed_coefficientSum` (∑=0 ↦ ∑=0) and `embed_mulVec` (φ commutes with the
  matrix action), assembled in `embeddedAtomicComponentA_hits_rational_views`.

## Assembly

`deployed_encoder_transfers_surjectivity` is the commuting square: given the
named edge `hcommute : NatEval * Conv = deployedFibreRectangularEval …`
(= edges (a)+(d)+layout as one interface), the encoder's natural-basis leakage
applied to the *converted* ordinary `∑=0` mask hits every view.
`atomic_sampler_encoder_hits_every_rational_view` feeds (b) into it: for every
view there is a choice of the 95 free sampler coordinates realising it.  Nothing
here re-proves the imported surjectivity; it is transported, not re-derived.
-/

open Matrix
open AspisCircleRectangularMasking
open AspisCircleDiscreteAvailability
open AspisCircleTensorBinding
open AspisV5AtomicComponentA

namespace AspisV5AtomicComponentACorrespondence

/-! ## Constants mirroring `v5_mask.rs` (read-only anchors) -/

/-- `V5_RESERVED_START`. -/
def reservedStart : ℕ := 896
/-- `V5_MASK_B` (total reserved coefficients) — pinned equal to `originalWidth`. -/
def maskB : ℕ := 96
/-- `V5_MASK_M` (per-block coefficient count) — pinned equal to `originalHalf`. -/
def maskM : ℕ := 48
/-- `V5_ATOMIC_A_PIVOT_COORDINATE`. -/
def pivotCoordinate : ℕ := 36
/-- `V5_ATOMIC_A_FREE_COORDINATES`. -/
def freeCoordinates : ℕ := 95

/-- The Rust layout constants match the Lean widths used by the imported
surjectivity theorem. -/
theorem layout_constants :
    reservedStart = 896 ∧ maskB = originalWidth ∧ maskM = originalHalf ∧
      pivotCoordinate < maskM ∧ freeCoordinates = maskB - 1 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [maskB, maskM, pivotCoordinate, freeCoordinates,
      originalWidth, originalHalf]

/-! ## Edge (c): stored layout ↔ abstract `Fin 96` order

### (c-sum) Rust's `atomic_m31_block_mask_coefficient_sum` = Lean `coefficientSum`

Rust folds `mask.p[0..48]` then `mask.q[0..48]`.  We model that vector in the
flat `Fin 96` order used by `coefficientSum`: flat index `k < 48` holds `p[k]`,
flat index `48 + k` holds `q[k]`. -/

/-- The flat 96-vector assembled from a `p`-block and a `q`-block, in the
`coefficientSum` index order. -/
def ordinaryOfBlocks (p q : Fin originalHalf → DeployedField) :
    Fin originalWidth → DeployedField :=
  fun i =>
    if h : (i : ℕ) < originalHalf then p ⟨(i : ℕ), h⟩
    else q ⟨(i : ℕ) - originalHalf, by
      have := i.isLt
      simp only [originalHalf, originalWidth] at this h ⊢
      omega⟩

/-- **(c-sum).**  Lean's `coefficientSum` of the flat vector equals Rust's
`p`-fold plus `q`-fold. -/
theorem coefficientSum_ordinaryOfBlocks (p q : Fin originalHalf → DeployedField) :
    coefficientSum (ordinaryOfBlocks p q) = (∑ k, p k) + (∑ k, q k) := by
  classical
  -- extend to a ℕ-indexed function and split range 96 = range 48 ⊕ (shifted) range 48
  set cExt : ℕ → DeployedField :=
    fun n => if h : n < originalWidth then ordinaryOfBlocks p q ⟨n, h⟩ else 0 with hcExt
  have hp : ∀ k : Fin originalHalf, cExt (k : ℕ) = p k := by
    intro k
    have hk : (k : ℕ) < originalWidth := by
      have := k.isLt; simp only [originalHalf, originalWidth] at this ⊢; omega
    simp only [hcExt, dif_pos hk, ordinaryOfBlocks, dif_pos k.isLt, Fin.eta]
  have hq : ∀ k : Fin originalHalf, cExt (originalHalf + (k : ℕ)) = q k := by
    intro k
    have hk : originalHalf + (k : ℕ) < originalWidth := by
      have := k.isLt; simp only [originalHalf, originalWidth] at this ⊢; omega
    have hnot : ¬ originalHalf + (k : ℕ) < originalHalf := by omega
    simp only [hcExt, dif_pos hk, ordinaryOfBlocks, dif_neg hnot]
    congr 1
    apply Fin.ext
    simp only [Nat.add_sub_cancel_left]
  have hval : ∀ i : Fin originalWidth, ordinaryOfBlocks p q i = cExt (i : ℕ) := by
    intro i; simp only [hcExt, dif_pos i.isLt, Fin.eta]
  rw [coefficientSum_apply, Finset.sum_congr rfl (fun i _ => hval i),
    Fin.sum_univ_eq_sum_range cExt originalWidth,
    show originalWidth = originalHalf + originalHalf from by
      simp [originalWidth, originalHalf],
    Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range cExt originalHalf,
    ← Fin.sum_univ_eq_sum_range (fun n => cExt (originalHalf + n)) originalHalf,
    Finset.sum_congr rfl (fun k _ => hp k), Finset.sum_congr rfl (fun k _ => hq k)]

/-! ### (c-layout) The interleaved reserved-row layout is a bijection

`v5_reserved_p_index k = 896 + 2k`, `v5_reserved_q_index k = 896 + 2k + 1`.  In
flat `Fin 96` order, natural `p`-coeff `k` (flat `k`) is stored at `896+2k`;
natural `q`-coeff `k` (flat `48+k`) is stored at `897+2k`. -/

/-- Stored message row of flat natural-coefficient index `i`. -/
def layoutRow (i : Fin originalWidth) : ℕ :=
  if (i : ℕ) < originalHalf then reservedStart + 2 * (i : ℕ)
  else reservedStart + 2 * ((i : ℕ) - originalHalf) + 1

theorem layoutRow_mem_reserved (i : Fin originalWidth) :
    reservedStart ≤ layoutRow i ∧ layoutRow i < reservedStart + maskB := by
  have hi := i.isLt
  simp only [originalWidth] at hi
  simp only [layoutRow, reservedStart, maskB, originalHalf]
  split_ifs with h <;> omega

theorem layoutRow_injective : Function.Injective layoutRow := by
  intro i j hij
  have hi := i.isLt; have hj := j.isLt
  simp only [originalWidth] at hi hj
  simp only [layoutRow, reservedStart, originalHalf] at hij
  apply Fin.ext
  split_ifs at hij with hI hJ hJ <;> omega

/-- The 96 stored rows are exactly the reserved block `896 .. 991`. -/
theorem layoutRow_image_reserved :
    Finset.image layoutRow Finset.univ =
      Finset.Ico reservedStart (reservedStart + maskB) := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨i, _, rfl⟩ := hr
    rw [Finset.mem_Ico]
    exact layoutRow_mem_reserved i
  · rw [Finset.card_image_of_injective _ layoutRow_injective, Finset.card_univ,
      Nat.card_Ico, Fintype.card_fin]
    simp [reservedStart, maskB, originalWidth]

/-! ## Edge (b): the pivot construction lands on — and fills — the hyperplane -/

/-- Flat index of the atomic pivot coordinate `p[36]`. -/
def pivotIndex : Fin originalWidth :=
  ⟨pivotCoordinate, by simp [pivotCoordinate, originalWidth]⟩

/-- The sampler's modelled output: 95 free coordinates, and the pivot set to the
negation of their sum (Rust `mask.p[36] = sum.neg()`). -/
def sampledVector (free : Fin originalWidth → DeployedField) :
    Fin originalWidth → DeployedField :=
  fun i => if i = pivotIndex then -(∑ j ∈ Finset.univ \ {pivotIndex}, free j) else free i

/-- There are exactly `V5_ATOMIC_A_FREE_COORDINATES = 95` free coordinates. -/
theorem free_coordinate_count :
    (Finset.univ \ {pivotIndex}).card = freeCoordinates := by
  have hcompl : Finset.univ \ {pivotIndex} = ({pivotIndex} : Finset (Fin originalWidth))ᶜ := by
    rw [Finset.compl_eq_univ_sdiff]
  rw [hcompl, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  simp [originalWidth, freeCoordinates]

/-- **(b).**  The pivot construction always lands on the atomic-v3 hyperplane. -/
theorem sampledVector_coefficientSum_zero (free : Fin originalWidth → DeployedField) :
    coefficientSum (sampledVector free) = 0 := by
  rw [coefficientSum_apply,
    ← Finset.add_sum_erase _ (sampledVector free) (Finset.mem_univ pivotIndex),
    Finset.erase_eq]
  have hp : sampledVector free pivotIndex =
      -(∑ j ∈ Finset.univ \ {pivotIndex}, free j) := if_pos rfl
  have hrest : ∀ j ∈ Finset.univ \ {pivotIndex}, sampledVector free j = free j := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact if_neg hj.2
  rw [hp, Finset.sum_congr rfl hrest, neg_add_cancel]

/-- On the hyperplane the construction is the identity: it therefore reaches
every `∑ = 0` vector.  Together with the previous lemma, the 95-free-coordinate
pivot map's image is *exactly* the hyperplane. -/
theorem sampledVector_eq_self_of_sum_zero
    (c : Fin originalWidth → DeployedField) (hc : coefficientSum c = 0) :
    sampledVector c = c := by
  funext i
  simp only [sampledVector]
  split_ifs with h
  · subst h
    have hsplit : coefficientSum c =
        c pivotIndex + ∑ j ∈ Finset.univ \ {pivotIndex}, c j := by
      rw [coefficientSum_apply,
        ← Finset.add_sum_erase _ c (Finset.mem_univ pivotIndex), Finset.erase_eq]
    have hzero : c pivotIndex + ∑ j ∈ Finset.univ \ {pivotIndex}, c j = 0 := by
      rw [← hsplit, hc]
    have hval : (∑ j ∈ Finset.univ \ {pivotIndex}, c j) = -c pivotIndex := by
      linear_combination hzero
    rw [hval, neg_neg]
  · rfl

/-- **(b), packaged.**  The pivot construction surjects onto the hyperplane. -/
theorem sampledVector_surjects_hyperplane
    (c : Fin originalWidth → DeployedField) (hc : coefficientSum c = 0) :
    ∃ free, sampledVector free = c :=
  ⟨c, sampledVector_eq_self_of_sum_zero c hc⟩

/-! ## Edges (a) and (d): the conversion / encoder algebra, referenced

The two facts below are the LEAN-PROVED core of the encoder path; they are
re-exported from `CircleTensorBinding` (not re-proved) so their axioms are
audited here too.  What they do NOT establish — the residual `code = model`
edges — is that the Rust `ordinary_monomials_in_natural_line_basis(48)` table is
`monomialToNatural` numerically, and that the deployed encoder's realised rows
are `naturalEvalMatrix` at the schedule with the aligned `B_896` row weight.
Those are the certificate and the `hcommute` interface below. -/

private theorem two_ne_zero_deployed : (2 : DeployedField) ≠ 0 := by
  have h : ((2 : ℕ) : DeployedField) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; decide
  simpa using h

/-- **(a), referenced.**  The 48×48 ordinary→natural conversion is invertible
(`= naturalCoeffMatrix_det_ne_zero`). -/
theorem conversion_invertible :
    (naturalCoeffMatrix DeployedField originalHalf).det ≠ 0 := by
  haveI : NeZero (2 : DeployedField) := ⟨two_ne_zero_deployed⟩
  exact naturalCoeffMatrix_det_ne_zero originalHalf

/-- **(a)+(d), referenced.**  Evaluating the natural line basis after the
canonical ordinary→natural conversion equals ordinary monomial Vandermonde
evaluation, at any point schedule (`= naturalEval_mul_monomialToNatural`). -/
theorem natural_after_conversion_eq_monomial {r : ℕ} (points : Fin r → DeployedField) :
    naturalEvalMatrix DeployedField originalHalf points *
        monomialToNatural DeployedField originalHalf
      = monomialEvalMatrix originalHalf points := by
  haveI : NeZero (2 : DeployedField) := ⟨two_ne_zero_deployed⟩
  exact naturalEval_mul_monomialToNatural_rect points

/-! ## The commuting square (assembly)

`hcommute` is the single named code edge bundling (a)+(d)+layout: the encoder's
realised natural-basis leakage `NatEval`, composed with the Rust ordinary→natural
conversion `Conv`, equals the deployed monomial-basis map `deployedFibreRectangularEval`.
Given it, the imported surjectivity transports to the encoder path — no re-derivation. -/

/-- **Commuting square.**  If the encoder's natural leakage composed with the
conversion is the deployed monomial map, then applying the encoder to the
*converted* ordinary `∑ = 0` mask hits every 72-coordinate view. -/
theorem deployed_encoder_transfers_surjectivity
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0)
    (Conv : Matrix (Fin originalWidth) (Fin originalWidth) DeployedField)
    (NatEval : Matrix FibreIndex (Fin originalWidth) DeployedField)
    (hcommute : NatEval * Conv = deployedFibreRectangularEval queries weight) :
    ∀ w : FibreIndex → DeployedField,
      ∃ c : Fin originalWidth → DeployedField,
        coefficientSum c = 0 ∧ NatEval.mulVec (Conv.mulVec c) = w := by
  intro w
  obtain ⟨c, hsum, hAc⟩ :=
    deployedAtomicV3ComponentA_surjective queries hqueries weight hweight w
  refine ⟨c, hsum, ?_⟩
  rw [Matrix.mulVec_mulVec, hcommute]
  exact hAc

/-- **Capstone (edges b + c + assembly).**  For every 72-coordinate view there is
a choice of the 95 free sampler coordinates whose sampled mask, converted and run
through the encoder, produces exactly that view. -/
theorem atomic_sampler_encoder_hits_every_rational_view
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0)
    (Conv : Matrix (Fin originalWidth) (Fin originalWidth) DeployedField)
    (NatEval : Matrix FibreIndex (Fin originalWidth) DeployedField)
    (hcommute : NatEval * Conv = deployedFibreRectangularEval queries weight) :
    ∀ w : FibreIndex → DeployedField,
      ∃ free : Fin originalWidth → DeployedField,
        NatEval.mulVec (Conv.mulVec (sampledVector free)) = w := by
  intro w
  obtain ⟨c, hsum, hEnc⟩ :=
    deployed_encoder_transfers_surjectivity queries hqueries weight hweight
      Conv NatEval hcommute w
  obtain ⟨free, hfree⟩ := sampledVector_surjects_hyperplane c hsum
  exact ⟨free, by rw [hfree]; exact hEnc⟩

/-! ## Edge (e): the M31 → QM31 ring embedding

QM31 is a 4-dimensional M31-algebra and is not a Lean object here, so the
embedding is modelled by an arbitrary ring hom `φ : DeployedField →+* L`
(instantiated in deployment by `algebraMap (ZMod P) QM31`).  Both lemmas hold for
any such `φ`; surjectivity onto M31-rational views therefore transfers. -/

variable {L : Type*} [CommRing L]

/-- **(e).**  A ring hom sends the atomic hyperplane into the atomic hyperplane:
`coefficientSum c = 0 ⟹ ∑ φ (c i) = 0`. -/
theorem embed_coefficientSum (φ : DeployedField →+* L)
    (c : Fin originalWidth → DeployedField) :
    ∑ i, φ (c i) = φ (coefficientSum c) := by
  rw [coefficientSum_apply, map_sum]

/-- **(e).**  A ring hom commutes with the matrix action:
`(M.map φ).mulVec (φ ∘ c) = φ ∘ (M.mulVec c)`. -/
theorem embed_mulVec (φ : DeployedField →+* L)
    (M : Matrix FibreIndex (Fin originalWidth) DeployedField)
    (c : Fin originalWidth → DeployedField) (r : FibreIndex) :
    (M.map φ).mulVec (fun i => φ (c i)) r = φ (M.mulVec c r) := by
  simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, map_sum, map_mul]

/-- **(e), assembled.**  The atomic hiding surjectivity transfers across the
embedding: for every M31-rational view `w`, there is a mask `c` whose φ-image
lies on the QM31 atomic hyperplane and whose φ-embedded encoder leakage equals
`φ ∘ w`. -/
theorem embeddedAtomicComponentA_hits_rational_views (φ : DeployedField →+* L)
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0) :
    ∀ w : FibreIndex → DeployedField,
      ∃ c : Fin originalWidth → DeployedField,
        (∑ i, φ (c i)) = 0 ∧
        ∀ r, ((deployedFibreRectangularEval queries weight).map φ).mulVec
              (fun i => φ (c i)) r = φ (w r) := by
  intro w
  obtain ⟨c, hsum, hAc⟩ :=
    deployedAtomicV3ComponentA_surjective queries hqueries weight hweight w
  refine ⟨c, ?_, ?_⟩
  · rw [embed_coefficientSum, hsum, map_zero]
  · intro r
    rw [embed_mulVec]
    exact congrArg φ (congrFun hAc r)

/-! ## Certificate for edge (a): emitted table = `naturalLinePoly` (leading 8×8)

`tools/v5_atomic_a_conversion_cert.rs` recomputes `natural_line_basis_polynomials(48)`
and `ordinary_monomials_in_natural_line_basis(48)` (mirroring `v5_mask.rs`,
mutating nothing), self-verifies their product is the identity, and emits the
leading block below (canonical residues shown here in signed form; `-1` is
`P-1` in `ZMod P`, etc.).  Each `nlp i` binds the Lean natural line basis `N_i`
to the emitted coefficient polynomial; the block certificate then reads that as
an entrywise match against `naturalLinePoly`/`naturalCoeffMatrix`. -/

section Certificate

open Polynomial Polynomial.Chebyshev

/-- The three-term Chebyshev recurrence, specialised to `DeployedField`. -/
private theorem Tstep (n : ℤ) :
    T DeployedField (n + 2) = 2 * X * T DeployedField (n + 1) - T DeployedField n :=
  T_add_two DeployedField n

private theorem T4e : T DeployedField 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  rw [show (4 : ℤ) = 2 + 2 by ring, Tstep, show (2 : ℤ) + 1 = 3 by ring,
      show (3 : ℤ) = 1 + 2 by ring, Tstep, show (1 : ℤ) + 1 = 2 by ring, T_two, T_one]
  ring

theorem nlp0 : naturalLinePoly DeployedField 0 = 1 := by
  rw [naturalLinePoly, show (0 : ℕ).bitIndices = [] from by decide]; simp
theorem nlp1 : naturalLinePoly DeployedField 1 = X := by
  rw [naturalLinePoly, show (1 : ℕ).bitIndices = [0] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_empty]; norm_num [T_one]
theorem nlp2 : naturalLinePoly DeployedField 2 = 2 * X ^ 2 - 1 := by
  rw [naturalLinePoly, show (2 : ℕ).bitIndices = [1] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_empty]; norm_num [T_two]
theorem nlp3 : naturalLinePoly DeployedField 3 = 2 * X ^ 3 - X := by
  rw [naturalLinePoly, show (3 : ℕ).bitIndices = [0, 1] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_empty]
  norm_num [T_one, T_two]; ring
theorem nlp4 : naturalLinePoly DeployedField 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  rw [naturalLinePoly, show (4 : ℕ).bitIndices = [2] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_empty]; norm_num [T4e]
theorem nlp5 : naturalLinePoly DeployedField 5 = 8 * X ^ 5 - 8 * X ^ 3 + X := by
  rw [naturalLinePoly, show (5 : ℕ).bitIndices = [0, 2] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_empty]
  norm_num [T_one, T4e]; ring
theorem nlp6 : naturalLinePoly DeployedField 6 = 16 * X ^ 6 - 24 * X ^ 4 + 10 * X ^ 2 - 1 := by
  rw [naturalLinePoly, show (6 : ℕ).bitIndices = [1, 2] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_empty]
  norm_num [T_two, T4e]; ring
theorem nlp7 : naturalLinePoly DeployedField 7 = 16 * X ^ 7 - 24 * X ^ 5 + 10 * X ^ 3 - X := by
  rw [naturalLinePoly, show (7 : ℕ).bitIndices = [0, 1, 2] from by decide]
  simp only [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_empty]
  norm_num [T_one, T_two, T4e]; ring

/-- The leading 8×8 block emitted by the recompute tool: `natLineSigned i j` is
the coefficient of `x^j` in the natural line basis `N_i`. -/
def natLineSigned : Matrix (Fin 8) (Fin 8) DeployedField :=
  !![ 1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
     -1, 0, 2, 0, 0, 0, 0, 0;
      0, -1, 0, 2, 0, 0, 0, 0;
      1, 0, -8, 0, 8, 0, 0, 0;
      0, 1, 0, -8, 0, 8, 0, 0;
     -1, 0, 10, 0, -24, 0, 16, 0;
      0, -1, 0, 10, 0, -24, 0, 16]

/-- **(a), certificate.**  Every entry of the recomputed 8×8 conversion block
equals the corresponding mechanised `naturalLinePoly` coefficient. -/
theorem naturalLine_block_certificate (i j : Fin 8) :
    (naturalLinePoly DeployedField (i : ℕ)).coeff (j : ℕ) = natLineSigned i j := by
  fin_cases i <;>
    simp only [nlp0, nlp1, nlp2, nlp3, nlp4, nlp5, nlp6, nlp7] <;>
    (fin_cases j <;>
      simp [natLineSigned, coeff_add, coeff_sub, coeff_one, coeff_X_pow, coeff_X,
        Polynomial.coeff_ofNat_mul])

/-- The same certificate read on the referenced Lean object `naturalCoeffMatrix`
(its leading 8×8 block equals the emitted table, transposed). -/
theorem naturalCoeffMatrix_block_eq (degree basis : Fin 8) :
    naturalCoeffMatrix DeployedField 8 degree basis = natLineSigned basis degree :=
  naturalLine_block_certificate basis degree

end Certificate

/-! ## The minimal remaining edges, as explicit interfaces

Each `Prop` below is the smallest statement that would close a residual
`code = model` edge.  They are stated, not proved: closing them requires
importing Rust execution semantics (a faithful model of the concrete functions),
which is outside a pure-Lean development.  The certificate above discharges the
leading 8×8 of the natural-basis half of `EncoderConversionIsMonomialToNatural`. -/

/-- **Edge (a), residual.**  The Rust `ordinary_monomials_in_natural_line_basis(48)`
table, read as a matrix over `DeployedField`, is exactly `monomialToNatural`.
`naturalCoeffMatrix_block_eq` certifies the leading 8×8 of its (invertible)
companion `naturalCoeffMatrix`; the tool's `verify_mutual_inverse` audits that
the applied table is that companion's inverse over M31. -/
def EncoderConversionIsMonomialToNatural
    (Conv : Matrix (Fin originalHalf) (Fin originalHalf) DeployedField) : Prop :=
  Conv = monomialToNatural DeployedField originalHalf

/-- **Edges (a)+(d)+layout, residual (= the `hcommute` hypothesis, named).**  The
deployed encoder's realised natural-basis leakage `NatEval` (from
`encode_c1_basis_value` at the interleaved reserved rows) composed with the Rust
conversion `Conv` is the deployed monomial map; `weight` is the row-896 factor
`encode_c1_basis_value(896, ·)`. -/
def EncoderNaturalLeakageFactorises
    (queries : Fin queryCount → Fin fibreCount) (weight : FibreIndex → DeployedField)
    (Conv : Matrix (Fin originalWidth) (Fin originalWidth) DeployedField)
    (NatEval : Matrix FibreIndex (Fin originalWidth) DeployedField) : Prop :=
  NatEval * Conv = deployedFibreRectangularEval queries weight

/-- **Edge (b), residual.**  The Rust function `sample_atomic_m31_block_mask`,
on the 95 drawn free coordinates `free`, returns the vector modelled by
`sampledVector` (in the flat `Fin 96` order of `ordinaryOfBlocks`). -/
def SamplerRealisesModel
    (rustOutput free : Fin originalWidth → DeployedField) : Prop :=
  rustOutput = sampledVector free

/-! ## Axiom audit -/

#print axioms layout_constants
#print axioms coefficientSum_ordinaryOfBlocks
#print axioms layoutRow_injective
#print axioms layoutRow_image_reserved
#print axioms free_coordinate_count
#print axioms sampledVector_coefficientSum_zero
#print axioms sampledVector_eq_self_of_sum_zero
#print axioms sampledVector_surjects_hyperplane
#print axioms conversion_invertible
#print axioms natural_after_conversion_eq_monomial
#print axioms deployed_encoder_transfers_surjectivity
#print axioms atomic_sampler_encoder_hits_every_rational_view
#print axioms embed_coefficientSum
#print axioms embed_mulVec
#print axioms embeddedAtomicComponentA_hits_rational_views
#print axioms nlp0
#print axioms nlp7
#print axioms naturalLine_block_certificate
#print axioms naturalCoeffMatrix_block_eq

end AspisV5AtomicComponentACorrespondence
