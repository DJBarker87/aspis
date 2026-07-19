import AspisFormal.V5AtomicComponentA

/-!
# Component A rank lemmas for the concrete circle-matrix model

`tools/verify_hiding_ranks.py` reproduces the eight-row affine-image rank
table behind the Component-A hiding premise (`im A = 𝒲`) at an independently
sampled generic schedule.  Its four root-neutral rows (ranks 1404 / 324 / 328
/ 1076) are reconstructed exactly from the construction.  Its four
raw-coverage rows — the two width-288 query maps and the two rank-12 terminal
Schur complements of the remaining-G/D and inactive-H1 blocks — are not: the
tool instantiates the layer-zero circle codeword as a generic distinct-point
Vandermonde and records a twiddle-irrelevance claim ("the circle-specific
twiddles are irrelevant to these column-rank and Schur-rank facts").  Those
four rows therefore rested on the prover's own GoodSpend gate plus that
modelling substitution, not on an independent kernel-checked certificate.

This file replaces part of the modelling substitution by kernel-checked theorems over
the concrete Lean circle-evaluation matrix named
`AspisCircleRectangularMasking.deployedFibreRectangularEval`, built from the
real M31 circle generator, the real signed fibre coordinates, an arbitrary
injective q18 schedule and arbitrary nowhere-zero aligned row weights, with
its scalars extended to an arbitrary commutative M31-algebra `L`
standing for a possible QM31 verifier-tower model.  The name `deployed` on
the Lean matrix is not a Rust correspondence theorem.

## What is proved

1. **The abstract width-288 query-map rank, under explicit hypotheses.**
   `extended_atomicV3_surjective_on_sum_zero` proves the concrete Lean
   circle map, restricted to the atomic-v3 hyperplane `∑ c = 0`, hits every
   72-coordinate `L`-view; `finrank_towerReads_eq_288` counts the M31
   dimension of that view space as `288 = 4 · 72` when `L` has M31-dimension
   four.  Its rank hypotheses are schedule injectivity and nowhere-zero
   weights.  Applying this theorem to either deployed raw-coverage row still
   requires the named Rust encoder/layout correspondence and the verifier-
   tower instantiation listed below; this file does not prove those rows are
   the matrix in the theorem.

2. **The abstract rank-12 Schur step, conditional on an eq-side premise.**
   `EqTerminalTripleCoversDeployedKernel` names the additional premise of this
   file's route: a supplied triple of terminal covectors covers
   the three-dimensional terminal target when restricted to the kernel of
   the CONCRETE circle query map on the hyperplane.  It is sufficient,
   jointly with the proved model query map, for joint coverage.  Given it,
   `deployed_joint_coverage_of_terminalTriple` proves the joint
   (query, terminal) map covers the full `288 + 12 = 300`-dimensional target
   (`finrank_jointTarget_eq_300`).  Identifying the supplied triple with the
   deployed eq-side reads is not proved here.
   `eqTerminalTripleCovers_of_tripleMatrix_isUnit` further reduces it to a
   single 3-by-3 determinant on the explicit concrete circle kernel triple
   `kernelPoly · (Xⁱ − 1)`, `i = 1, 2, 3`, whose kernel membership,
   hyperplane membership and staircase leading coefficients are all proved
   here from the circle structure.

3. **Model non-vacuity.**  At the concrete identity-embedding schedule, unit
   weights, and the concrete four-dimensional split algebra
   `SplitTower = Fin 4 → M31`, every hypothesis fires simultaneously:
   the width-288 bundle (`width288_bundle_nonvacuous`), the Schur premise
   through the determinant route on the circle-model kernel triple
   (`schur_premise_nonvacuous`, determinant proved equal to one), and the
   joint 300-coverage conclusion (`joint_coverage_nonvacuous`).

## What remains before a deployed Component-A conclusion

* Schedule injectivity and nonzero aligned weights for the runtime schedule
  are explicit hypotheses, not unconditional facts.
* The Rust encoder correspondence — bit-reversed stored indices, slot order,
  natural-basis conversion, row-896 aligned weights — between the deployed
  serializer and this monomial-coordinate presentation.  That boundary is
  recorded in `CircleRectangularMasking` and `V5AtomicComponentA` and is
  unchanged here: this file certifies ranks of the same matrices those files
  present.
* The identification of the deployed verifier field with a concrete
  commutative M31-algebra of M31-dimension four.  The QM31 tower
  `CM31[u]/(u² − (2+i))`, `CM31 = M31[i]/(i²+1)` satisfies this interface by
  construction; the tower itself is not built in this repository, so every
  theorem is stated over an arbitrary such algebra and the dimension-four
  fact enters as the explicit hypothesis `Module.finrank M31 L = 4`.
* The eq-side premise of the rank-12 rows,
  `EqTerminalTripleCoversDeployedKernel`, stated but not discharged for the
  deployed transcript's eq covectors: the deployed sumcheck point is a
  runtime Fiat–Shamir value, and the coverage fact is false at degenerate
  points, so a schedule premise is unavoidable.  This file makes it exact and
  explicit rather than leaving it inside a code-model substitution.
* The four root-neutral rows (1404 / 324 / 328 / 1076): outside this file's
  scope; the Python tool reconstructs them exactly, with no code-model
  substitution.

Thus the deployed A leg does **not** have only one residual after this file:
at minimum the runtime schedule/weight facts, Rust encoder/layout
correspondence, concrete QM31-tower correspondence, and eq-side premise remain
distinct obligations.
-/

open Matrix Polynomial

namespace AspisV5ComponentARankCompletion

open AspisCircleRectangularMasking
open AspisCircleDiscreteAvailability
open AspisV5AtomicComponentA

/-! ## Step 1.  Ring-homomorphism transport of full row rank

Surjectivity of a matrix action is witnessed by a right inverse, and a right
inverse transports entrywise through any ring homomorphism.  This is the exact
sense in which the M31 rank certificates of `CircleRectangularMasking` extend
to an arbitrary M31-algebra without recomputing rank after scalar extension.
Instantiating that algebra with deployed QM31 is a separate correspondence. -/

/-- A matrix whose action is surjective over the base ring stays surjective
after entrywise transport along a ring homomorphism: the right inverse maps
along. -/
theorem mulVec_map_surjective {R S : Type*} [CommRing R] [CommRing S]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (f : R →+* S) (M : Matrix m n R) (h : Function.Surjective M.mulVec) :
    Function.Surjective (M.map f).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  refine Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨B.map f, ?_⟩
  rw [← Matrix.map_mul, hB]
  exact Matrix.map_one f (map_zero f) (map_one f)

/-- Kernel-shift surjectivity over a commutative ring: if `A` is surjective
and some kernel vector `k` has a unit value under the functional `l`, then
`A` restricted to the hyperplane `l = 0` is still surjective.  Ring version of
`AspisV5AtomicComponentA.surjective_restrict_ker`; the unit hypothesis
replaces field division so the statement covers every commutative
M31-algebra at once. -/
theorem surjective_restrict_ker_of_isUnit {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : V →ₗ[R] W) (hA : Function.Surjective A) (l : V →ₗ[R] R) (k : V)
    (hAk : A k = 0) (hlk : IsUnit (l k)) :
    ∀ w, ∃ v, l v = 0 ∧ A v = w := by
  intro w
  obtain ⟨x, hx⟩ := hA w
  obtain ⟨u, hu⟩ := hlk
  refine ⟨x - (l x * (↑u⁻¹ : R)) • k, ?_, ?_⟩
  · rw [map_sub, map_smul, smul_eq_mul, ← hu, mul_assoc, Units.inv_mul, mul_one,
      sub_self]
  · rw [map_sub, map_smul, hAk, smul_zero, sub_zero, hx]

/-! ## Step 2.  The circle-evaluation model over an abstract tower -/

section TowerExtension

variable {L : Type*} [CommRing L]

/-- The 96-coordinate sum functional over `L`: the atomic-v3 constraint in
the extension. -/
def coefficientSumL : (Fin originalWidth → L) →ₗ[L] L where
  toFun c := ∑ i, c i
  map_add' c d := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] theorem coefficientSumL_apply (c : Fin originalWidth → L) :
    coefficientSumL c = ∑ i, c i := rfl

variable [Algebra DeployedField L]

/-- The concrete Lean 72-by-96 circle point-evaluation matrix, whose legacy
definition name contains `deployed`, transported into an M31-algebra `L`.
Correspondence with the Rust encoder and concrete QM31 tower is not proved by
this definition. -/
def extendedFibreEval (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    Matrix FibreIndex (Fin originalWidth) L :=
  (deployedFibreRectangularEval queries weight).map (algebraMap DeployedField L)

/-- Full row rank of the concrete Lean circle matrix survives the tower
extension: the `L`-linear extension is surjective for every injective q18
schedule and nowhere-zero aligned row weight. -/
theorem extendedFibreEval_mulVec_surjective
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective (extendedFibreEval (L := L) queries weight).mulVec :=
  mulVec_map_surjective (algebraMap DeployedField L) _
    (deployed_mulVec_surjective queries hqueries weight hweight)

/-- The atomic-v3 kernel witness of `V5AtomicComponentA`, transported into
the tower. -/
noncomputable def kernelWitnessL (queries : Fin queryCount → Fin fibreCount) :
    Fin originalWidth → L :=
  fun j => algebraMap DeployedField L (kernelWitness queries j)

/-- The transported witness still lies in the kernel of the extended map. -/
theorem kernelWitnessL_mulVec_zero (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    (extendedFibreEval (L := L) queries weight).mulVec (kernelWitnessL queries)
      = 0 := by
  funext row
  have h := RingHom.map_mulVec (algebraMap DeployedField L)
    (deployedFibreRectangularEval queries weight) (kernelWitness queries) row
  rw [kernel_mulVec_zero queries weight] at h
  simp only [Pi.zero_apply, map_zero] at h
  exact h.symm

/-- The transported witness keeps a unit coefficient sum: the image of a
nonzero M31 scalar under any M31-algebra map is a unit. -/
theorem kernelWitnessL_sum_isUnit (queries : Fin queryCount → Fin fibreCount) :
    IsUnit (coefficientSumL (kernelWitnessL (L := L) queries)) := by
  have hsum : coefficientSumL (kernelWitnessL (L := L) queries)
      = algebraMap DeployedField L (coefficientSum (kernelWitness queries)) := by
    simp only [coefficientSumL_apply, kernelWitnessL, coefficientSum_apply]
    exact (map_sum (algebraMap DeployedField L) (kernelWitness queries)
      Finset.univ).symm
  rw [hsum]
  exact (isUnit_iff_ne_zero.mpr (coefficientSum_kernel_ne_zero queries)).map
    (algebraMap DeployedField L)

/-! ## Step 3.  The width-288 query rows -/

/-- **Abstract query-map surjectivity.**  Over every commutative M31-algebra
`L`, the concrete Lean circle point-evaluation
map, restricted to the atomic-v3 hyperplane `∑ c = 0`, hits every
72-coordinate `L`-view.  Hypotheses are schedule injectivity and nonzero
weights.  The theorem does not identify its coefficient vector with Rust's
reserve-row layout or instantiate the concrete verifier tower. -/
theorem extended_atomicV3_surjective_on_sum_zero
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0) :
    ∀ w : FibreIndex → L, ∃ c : Fin originalWidth → L,
      (∑ i, c i) = 0 ∧ (extendedFibreEval queries weight).mulVec c = w := by
  intro w
  have hA : Function.Surjective
      ⇑(extendedFibreEval (L := L) queries weight).mulVecLin :=
    extendedFibreEval_mulVec_surjective queries hqueries weight hweight
  have hAk : (extendedFibreEval (L := L) queries weight).mulVecLin
      (kernelWitnessL queries) = 0 := by
    rw [Matrix.mulVecLin_apply]
    exact kernelWitnessL_mulVec_zero queries weight
  obtain ⟨v, hlv, hAv⟩ := surjective_restrict_ker_of_isUnit
    (extendedFibreEval (L := L) queries weight).mulVecLin hA coefficientSumL
    (kernelWitnessL queries) hAk (kernelWitnessL_sum_isUnit queries) w
  refine ⟨v, ?_, ?_⟩
  · simpa using hlv
  · rw [← Matrix.mulVecLin_apply]
    exact hAv

/-- **Width-288 query rows, dimension content.**  When the tower has
M31-dimension four, the 72 opened `L`-reads span an M31-space of dimension
exactly `288 = 4 · 72` — the width recorded by the certificate's
`remaining G/D query map` and `inactive-balanced H1 query map` rows. -/
theorem finrank_towerReads_eq_288 [Module.Finite DeployedField L]
    (hdim : Module.finrank DeployedField L = 4) :
    Module.finrank DeployedField (FibreIndex → L) = 288 := by
  rw [Module.finrank_pi_fintype DeployedField, Finset.sum_const,
    Finset.card_univ, hdim, smul_eq_mul]
  have hcard : Fintype.card FibreIndex = 72 := by
    norm_num [FibreIndex, FibreSign, queryCount]
  rw [hcard]

/-! ## Step 4.  The rank-12 Schur rows: joint coverage from one named premise -/

/-- Joint hyperplane surjectivity from component surjectivity plus coverage of
the second target on the constrained kernel.  Pure linear algebra: this is the
Schur-complement composition step of the raw-coverage blocks. -/
theorem joint_surjective_on_hyperplane {R V W₁ W₂ : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W₁] [Module R W₁]
    [AddCommGroup W₂] [Module R W₂]
    (A : V →ₗ[R] W₁) (B : V →ₗ[R] W₂) (l : V →ₗ[R] R)
    (hA : ∀ w, ∃ v, l v = 0 ∧ A v = w)
    (hB : ∀ t, ∃ v, l v = 0 ∧ A v = 0 ∧ B v = t) :
    ∀ w t, ∃ v, l v = 0 ∧ A v = w ∧ B v = t := by
  intro w t
  obtain ⟨v₀, hl₀, hA₀⟩ := hA w
  obtain ⟨d, hld, hAd, hBd⟩ := hB (t - B v₀)
  refine ⟨v₀ + d, ?_, ?_, ?_⟩
  · rw [map_add, hl₀, hld, add_zero]
  · rw [map_add, hA₀, hAd, add_zero]
  · rw [map_add, hBd]
    abel

/-- **The eq-side premise of the abstract rank-12 Schur route.**  A supplied
terminal covector triple, when restricted to the circle-model query kernel
and atomic-v3 hyperplane, covers the three-dimensional `L` target.  Relating
that supplied map to the deployed eq-weighted reads, including tower and
encoder conventions, is a separate obligation. -/
def EqTerminalTripleCoversDeployedKernel
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (terminalTriple : (Fin originalWidth → L) →ₗ[L] (Fin 3 → L)) : Prop :=
  ∀ t : Fin 3 → L, ∃ c : Fin originalWidth → L,
    (∑ i, c i) = 0 ∧ (extendedFibreEval queries weight).mulVec c = 0
      ∧ terminalTriple c = t

/-- **Conditional rank-12 Schur completion.**  Given the named premise, the
joint (query, terminal) map covers every pair of a 72-coordinate query view
and a 3-coordinate terminal view from hyperplane sources: the joint target of
M31-dimension `288 + 12 = 300` is fully covered in this model. -/
theorem deployed_joint_coverage_of_terminalTriple
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0)
    (terminalTriple : (Fin originalWidth → L) →ₗ[L] (Fin 3 → L))
    (hSchur : EqTerminalTripleCoversDeployedKernel queries weight terminalTriple) :
    ∀ (w : FibreIndex → L) (t : Fin 3 → L), ∃ c : Fin originalWidth → L,
      (∑ i, c i) = 0 ∧ (extendedFibreEval queries weight).mulVec c = w
        ∧ terminalTriple c = t := by
  intro w t
  have hA : ∀ w' : FibreIndex → L, ∃ v, coefficientSumL v = 0
      ∧ (extendedFibreEval (L := L) queries weight).mulVecLin v = w' := by
    intro w'
    obtain ⟨c, hc0, hcw⟩ :=
      extended_atomicV3_surjective_on_sum_zero queries hqueries weight hweight w'
    exact ⟨c, by simpa using hc0, by rw [Matrix.mulVecLin_apply]; exact hcw⟩
  have hB : ∀ t' : Fin 3 → L, ∃ v, coefficientSumL v = 0
      ∧ (extendedFibreEval (L := L) queries weight).mulVecLin v = 0
      ∧ terminalTriple v = t' := by
    intro t'
    obtain ⟨c, hc0, hck, hct⟩ := hSchur t'
    exact ⟨c, by simpa using hc0, by rw [Matrix.mulVecLin_apply]; exact hck, hct⟩
  obtain ⟨v, h1, h2, h3⟩ := joint_surjective_on_hyperplane
    (extendedFibreEval (L := L) queries weight).mulVecLin terminalTriple
    coefficientSumL hA hB w t
  refine ⟨v, by simpa using h1, ?_, h3⟩
  rw [← Matrix.mulVecLin_apply]
  exact h2

/-- The terminal target has M31-dimension `12 = 4 · 3` over a
dimension-four tower. -/
theorem finrank_terminalTarget_eq_12 [Module.Finite DeployedField L]
    (hdim : Module.finrank DeployedField L = 4) :
    Module.finrank DeployedField (Fin 3 → L) = 12 := by
  rw [Module.finrank_pi_fintype DeployedField, Finset.sum_const,
    Finset.card_univ, hdim, smul_eq_mul, Fintype.card_fin]

/-- The joint raw-coverage target has M31-dimension `300 = 288 + 12` over a
dimension-four tower: the query width plus the terminal Schur width. -/
theorem finrank_jointTarget_eq_300 [Module.Finite DeployedField L]
    (hdim : Module.finrank DeployedField L = 4) :
    Module.finrank DeployedField ((FibreIndex → L) × (Fin 3 → L)) = 300 := by
  rw [Module.finrank_prod, finrank_towerReads_eq_288 hdim,
    finrank_terminalTarget_eq_12 hdim]

/-! ## Step 5.  The concrete circle kernel triple

Three explicit directions in the kernel of the concrete deployed map, on the
atomic-v3 hyperplane, with a staircase of leading coefficients: the pure-x
embeddings of `kernelPoly · (Xⁱ − 1)` for `i = 1, 2, 3`.  Each factor
`Xⁱ − 1` kills the coefficient sum (evaluation at one) while the `kernelPoly`
factor keeps every released row at a root.  These reduce the named Schur
premise to a single 3-by-3 determinant. -/

/-- Pure-x block embedding of a polynomial's coefficient vector into the 96
natural-basis coordinates; the y-block is zero. -/
noncomputable def xBlockEmbed (P : DeployedField[X]) :
    Fin originalWidth → DeployedField :=
  fun j => if (j : ℕ) < originalHalf then P.coeff (j : ℕ) else 0

/-- The coefficient sum of a pure-x embedding is evaluation at one. -/
theorem xBlockEmbed_sum (P : DeployedField[X]) (hP : P.natDegree < originalHalf) :
    (∑ j, xBlockEmbed P j) = P.eval 1 := by
  have hrange : (∑ j : Fin originalWidth, xBlockEmbed P j)
      = ∑ n ∈ Finset.range originalWidth,
          (if n < originalHalf then P.coeff n else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun n => if n < originalHalf then P.coeff n else 0) originalWidth
  rw [hrange]
  have hsub : Finset.range originalHalf ⊆ Finset.range originalWidth := by
    intro n hn
    simp only [Finset.mem_range, originalHalf, originalWidth] at hn ⊢
    omega
  have htail : ∀ n ∈ Finset.range originalWidth, n ∉ Finset.range originalHalf →
      (if n < originalHalf then P.coeff n else 0) = 0 := by
    intro n _ hn'
    rw [Finset.mem_range] at hn'
    simp only [if_neg hn']
  rw [← Finset.sum_subset hsub htail]
  have hcongr : ∀ n ∈ Finset.range originalHalf,
      (if n < originalHalf then P.coeff n else 0) = P.coeff n := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos hn]
  rw [Finset.sum_congr rfl hcongr, eval_eq_sum_range' hP 1]
  simp only [one_pow, mul_one]

/-- `kernelPoly` is monic: it is a product of monic linear factors. -/
theorem kernelPoly_monic (queries : Fin queryCount → Fin fibreCount) :
    (kernelPoly queries).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- `kernelPoly` has degree exactly 36: one linear factor per signed x-node
of the q18 schedule. -/
theorem kernelPoly_natDegree (queries : Fin queryCount → Fin fibreCount) :
    (kernelPoly queries).natDegree = 36 := by
  rw [kernelPoly, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ]
  norm_num [queryCount]

/-- The kernel-shift polynomial `kernelPoly · (Xⁱ − 1)`: still vanishing at
every released node, additionally vanishing at one, monic of degree
`36 + i`. -/
noncomputable def kernelShift (queries : Fin queryCount → Fin fibreCount)
    (i : ℕ) : DeployedField[X] :=
  kernelPoly queries * (X ^ i - 1)

/-- `Xⁱ − 1` is monic for positive `i`. -/
theorem monic_X_pow_sub_one {i : ℕ} (hi : i ≠ 0) :
    (X ^ i - 1 : DeployedField[X]).Monic := by
  have h : (X ^ i - 1 : DeployedField[X]) = X ^ i - C 1 := by rw [map_one]
  rw [h]
  exact monic_X_pow_sub_C 1 hi

/-- The kernel shift is monic for positive `i`. -/
theorem kernelShift_monic (queries : Fin queryCount → Fin fibreCount) {i : ℕ}
    (hi : i ≠ 0) : (kernelShift queries i).Monic :=
  (kernelPoly_monic queries).mul (monic_X_pow_sub_one hi)

/-- The kernel shift has degree exactly `36 + i` for positive `i`. -/
theorem kernelShift_natDegree (queries : Fin queryCount → Fin fibreCount)
    {i : ℕ} (hi : i ≠ 0) : (kernelShift queries i).natDegree = 36 + i := by
  rw [kernelShift,
    Polynomial.Monic.natDegree_mul (kernelPoly_monic queries)
      (monic_X_pow_sub_one hi),
    kernelPoly_natDegree]
  congr 1
  have h : (X ^ i - 1 : DeployedField[X]) = X ^ i - C 1 := by rw [map_one]
  rw [h, natDegree_X_pow_sub_C]

/-- The kernel shift stays inside the pure-x block for `i ≤ 11`. -/
theorem kernelShift_natDegree_lt (queries : Fin queryCount → Fin fibreCount)
    {i : ℕ} (hi : i ≠ 0) (hi11 : i ≤ 11) :
    (kernelShift queries i).natDegree < originalHalf := by
  rw [kernelShift_natDegree queries hi]
  simp only [originalHalf]
  omega

/-- The kernel shift's leading coefficient is one, at index `36 + i`. -/
theorem kernelShift_coeff_top (queries : Fin queryCount → Fin fibreCount)
    {i : ℕ} (hi : i ≠ 0) : (kernelShift queries i).coeff (36 + i) = 1 := by
  have h := (kernelShift_monic queries hi).coeff_natDegree
  rwa [kernelShift_natDegree queries hi] at h

/-- The kernel shift's coefficients vanish above degree `36 + i`. -/
theorem kernelShift_coeff_zero_of_gt (queries : Fin queryCount → Fin fibreCount)
    {i n : ℕ} (hi : i ≠ 0) (hn : 36 + i < n) :
    (kernelShift queries i).coeff n = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  rw [kernelShift_natDegree queries hi]
  exact hn

/-- The kernel shift vanishes at every released signed x-node. -/
theorem kernelShift_eval_node_zero (queries : Fin queryCount → Fin fibreCount)
    (i : ℕ) (q : Fin queryCount) (s : Fin 2) :
    (kernelShift queries i).eval
      (signedCoordinate s (representativeX (queries q))) = 0 := by
  rw [kernelShift, eval_mul, kernelPoly_eval_node_zero queries q s, zero_mul]

/-- The kernel shift vanishes at one: the factor `Xⁱ − 1` does. -/
theorem kernelShift_eval_one (queries : Fin queryCount → Fin fibreCount)
    (i : ℕ) : (kernelShift queries i).eval 1 = 0 := by
  rw [kernelShift, eval_mul, eval_sub, eval_pow, eval_X, eval_one, one_pow,
    sub_self, mul_zero]

/-- The concrete circle kernel triple: pure-x embeddings of
`kernelPoly · (X^(i+1) − 1)` for `i = 0, 1, 2`. -/
noncomputable def kernelTripleVec (queries : Fin queryCount → Fin fibreCount)
    (i : Fin 3) : Fin originalWidth → DeployedField :=
  xBlockEmbed (kernelShift queries ((i : ℕ) + 1))

/-- Each triple direction lies on the atomic-v3 hyperplane. -/
theorem kernelTripleVec_sum_zero (queries : Fin queryCount → Fin fibreCount)
    (i : Fin 3) : (∑ j, kernelTripleVec queries i j) = 0 := by
  rw [kernelTripleVec,
    xBlockEmbed_sum _
      (kernelShift_natDegree_lt queries (by omega) (by omega : (i : ℕ) + 1 ≤ 11)),
    kernelShift_eval_one]

/-- Each triple direction lies in the kernel of the concrete deployed map:
every released row evaluates its polynomial at one of its roots. -/
theorem kernelTripleVec_mulVec_zero (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) (i : Fin 3) :
    (deployedFibreRectangularEval queries weight).mulVec
      (kernelTripleVec queries i) = 0 := by
  funext row
  rw [Pi.zero_apply]
  show (deployedFibreRectangularEval queries weight).mulVec
      (fun j => if (j : ℕ) < originalHalf
        then (kernelShift queries ((i : ℕ) + 1)).coeff (j : ℕ) else 0) row = 0
  rw [mulVec_kernelEmbed queries weight _
      (kernelShift_natDegree_lt queries (by omega) (by omega : (i : ℕ) + 1 ≤ 11))
      row,
    kernelShift_eval_node_zero, mul_zero]

/-- The kernel triple transported into the tower. -/
noncomputable def kernelTripleVecL (queries : Fin queryCount → Fin fibreCount)
    (i : Fin 3) : Fin originalWidth → L :=
  fun j => algebraMap DeployedField L (kernelTripleVec queries i j)

/-- The transported triple stays on the hyperplane. -/
theorem kernelTripleVecL_sum_zero (queries : Fin queryCount → Fin fibreCount)
    (i : Fin 3) : (∑ j, kernelTripleVecL (L := L) queries i j) = 0 := by
  have h : (∑ j, kernelTripleVecL (L := L) queries i j)
      = algebraMap DeployedField L (∑ j, kernelTripleVec queries i j) :=
    (map_sum (algebraMap DeployedField L) (kernelTripleVec queries i)
      Finset.univ).symm
  rw [h, kernelTripleVec_sum_zero, map_zero]

/-- The transported triple stays in the kernel of the extended map. -/
theorem kernelTripleVecL_mulVec_zero (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) (i : Fin 3) :
    (extendedFibreEval (L := L) queries weight).mulVec
      (kernelTripleVecL queries i) = 0 := by
  funext row
  have h := RingHom.map_mulVec (algebraMap DeployedField L)
    (deployedFibreRectangularEval queries weight) (kernelTripleVec queries i) row
  rw [kernelTripleVec_mulVec_zero queries weight i] at h
  simp only [Pi.zero_apply, map_zero] at h
  exact h.symm

/-- The 3-by-3 matrix of a terminal covector triple evaluated on the concrete
circle kernel triple. -/
noncomputable def tripleMatrix (queries : Fin queryCount → Fin fibreCount)
    (terminalTriple : (Fin originalWidth → L) →ₗ[L] (Fin 3 → L)) :
    Matrix (Fin 3) (Fin 3) L :=
  fun p i => terminalTriple (kernelTripleVecL queries i) p

/-- **The Schur premise from one explicit determinant.**  If the terminal
covector triple takes unit-determinant values on the concrete circle kernel
triple, the named coverage premise holds.  All circle-side content — kernel
membership and hyperplane membership — is proved.  The determinant concerns
the supplied terminal triple; correspondence to the deployed eq side remains
separate. -/
theorem eqTerminalTripleCovers_of_tripleMatrix_isUnit
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (terminalTriple : (Fin originalWidth → L) →ₗ[L] (Fin 3 → L))
    (hdet : IsUnit (tripleMatrix (L := L) queries terminalTriple).det) :
    EqTerminalTripleCoversDeployedKernel queries weight terminalTriple := by
  intro t
  have hsurj : Function.Surjective
      (tripleMatrix (L := L) queries terminalTriple).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  obtain ⟨a, ha⟩ := hsurj t
  refine ⟨∑ i : Fin 3, a i • kernelTripleVecL queries i, ?_, ?_, ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, kernelTripleVecL_sum_zero, mul_zero]
  · show (extendedFibreEval (L := L) queries weight).mulVecLin _ = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, Matrix.mulVecLin_apply, kernelTripleVecL_mulVec_zero,
      smul_zero]
  · rw [map_sum]
    funext p
    have hmv : (tripleMatrix (L := L) queries terminalTriple).mulVec a p = t p := by
      rw [ha]
    rw [← hmv]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, tripleMatrix]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end TowerExtension

/-! ## Step 6.  Model non-vacuity at a concrete schedule and abstract tower

The identity-embedding schedule, unit weights, and the split algebra
`Fin 4 → M31` instantiate every hypothesis simultaneously, including the
Schur determinant on the circle-model kernel triple.  The split algebra is not
the QM31 field; it is a concrete commutative M31-algebra of
M31-dimension four, which is the exact interface every theorem above
consumes, so the abstract implications are non-vacuous.  This section does not
instantiate the deployed QM31 field or Rust layout. -/

/-- A concrete injective q18 schedule: query `q` reads fibre `q`. -/
def sampleQueries : Fin queryCount → Fin fibreCount :=
  fun q => ⟨(q : ℕ), by
    have hq := q.isLt
    simp only [queryCount] at hq
    simp only [fibreCount]
    omega⟩

theorem sampleQueries_injective : Function.Injective sampleQueries := by
  intro a b h
  have hval : ((sampleQueries a : Fin fibreCount) : ℕ)
      = ((sampleQueries b : Fin fibreCount) : ℕ) := congrArg Fin.val h
  exact Fin.ext hval

/-- A concrete four-dimensional commutative M31-algebra: the split algebra
`Fin 4 → M31`.  It shares the QM31 tower's module interface (commutative,
M31-dimension four) without requiring the tower's field
structure, which no theorem above consumes. -/
abbrev SplitTower : Type := Fin 4 → DeployedField

theorem splitTower_finrank : Module.finrank DeployedField SplitTower = 4 := by
  rw [Module.finrank_pi]
  norm_num

/-- Probe column `37 + p` of the pure-x block. -/
def probeIndex (p : Fin 3) : Fin originalWidth :=
  ⟨37 + (p : ℕ), by
    have hp := p.isLt
    simp only [originalWidth]
    omega⟩

/-- The staircase probe triple: the three coordinate reads at pure-x columns
37, 38, 39.  It is not the deployed eq triple; it is a concrete terminal covector triple
demonstrating that the Schur premise and the joint conditional theorem are
satisfiable in the Lean circle-matrix model. -/
def probeTriple :
    (Fin originalWidth → SplitTower) →ₗ[SplitTower] (Fin 3 → SplitTower) :=
  LinearMap.pi fun p => LinearMap.proj (probeIndex p)

/-- The probe matrix entry is a coefficient of the concrete kernel-shift
polynomial. -/
theorem probe_tripleMatrix_apply (p i : Fin 3) :
    tripleMatrix (L := SplitTower) sampleQueries probeTriple p i
      = algebraMap DeployedField SplitTower
          ((kernelShift sampleQueries ((i : ℕ) + 1)).coeff (37 + (p : ℕ))) := by
  show probeTriple (kernelTripleVecL sampleQueries i) p = _
  simp only [probeTriple, LinearMap.pi_apply, LinearMap.proj_apply]
  have hlt : ((probeIndex p : Fin originalWidth) : ℕ) < originalHalf := by
    have hp := p.isLt
    simp only [probeIndex, originalHalf]
    omega
  simp only [kernelTripleVecL, kernelTripleVec, xBlockEmbed, hlt, if_pos]
  rfl

/-- The probe diagonal reads the staircase's leading coefficients: ones. -/
theorem probe_tripleMatrix_diag (p : Fin 3) :
    tripleMatrix (L := SplitTower) sampleQueries probeTriple p p = 1 := by
  have harith : 37 + (p : ℕ) = 36 + ((p : ℕ) + 1) := by omega
  rw [probe_tripleMatrix_apply, harith,
    kernelShift_coeff_top sampleQueries (by omega), map_one]

/-- Below the diagonal the probe reads coefficients above the staircase's
degrees: zeros. -/
theorem probe_tripleMatrix_lower (p i : Fin 3) (h : (i : ℕ) < (p : ℕ)) :
    tripleMatrix (L := SplitTower) sampleQueries probeTriple p i = 0 := by
  rw [probe_tripleMatrix_apply,
    kernelShift_coeff_zero_of_gt sampleQueries (by omega) (by omega), map_zero]

/-- The probe determinant on the concrete circle kernel triple is one. -/
theorem probe_tripleMatrix_det :
    (tripleMatrix (L := SplitTower) sampleQueries probeTriple).det = 1 := by
  rw [Matrix.det_fin_three, probe_tripleMatrix_diag 0, probe_tripleMatrix_diag 1,
    probe_tripleMatrix_diag 2, probe_tripleMatrix_lower 1 0 (by norm_num),
    probe_tripleMatrix_lower 2 0 (by norm_num),
    probe_tripleMatrix_lower 2 1 (by norm_num)]
  ring

/-- **Non-vacuity of the width-288 certificate**: at the concrete schedule,
unit weights, and the concrete four-dimensional tower, the hyperplane
surjectivity and the 288-dimension count hold together. -/
theorem width288_bundle_nonvacuous :
    (∀ w : FibreIndex → SplitTower, ∃ c : Fin originalWidth → SplitTower,
        (∑ i, c i) = 0
          ∧ (extendedFibreEval sampleQueries fun _ => 1).mulVec c = w)
      ∧ Module.finrank DeployedField (FibreIndex → SplitTower) = 288 :=
  ⟨extended_atomicV3_surjective_on_sum_zero sampleQueries sampleQueries_injective
      _ (fun _ => one_ne_zero),
    finrank_towerReads_eq_288 splitTower_finrank⟩

/-- **Non-vacuity of the Schur premise**: the probe triple satisfies the
named coverage premise at the circle-model kernel triple, through the
determinant route with determinant one. -/
theorem schur_premise_nonvacuous :
    EqTerminalTripleCoversDeployedKernel (L := SplitTower) sampleQueries
      (fun _ => 1) probeTriple :=
  eqTerminalTripleCovers_of_tripleMatrix_isUnit sampleQueries _ probeTriple
    (by rw [probe_tripleMatrix_det]; exact isUnit_one)

/-- **Model non-vacuity of the conditional joint theorem**: with the premise
discharged by the probe triple, the joint 300-dimensional coverage conclusion
fires at the concrete circle matrices. -/
theorem joint_coverage_nonvacuous :
    ∀ (w : FibreIndex → SplitTower) (t : Fin 3 → SplitTower),
      ∃ c : Fin originalWidth → SplitTower,
        (∑ i, c i) = 0
          ∧ (extendedFibreEval sampleQueries fun _ => 1).mulVec c = w
          ∧ probeTriple c = t :=
  deployed_joint_coverage_of_terminalTriple sampleQueries sampleQueries_injective
    _ (fun _ => one_ne_zero) probeTriple schur_premise_nonvacuous

/-- The joint target dimension count is realised at the concrete tower. -/
theorem finrank_bundle_nonvacuous :
    Module.finrank DeployedField
      ((FibreIndex → SplitTower) × (Fin 3 → SplitTower)) = 300 :=
  finrank_jointTarget_eq_300 splitTower_finrank

/-! ## Axiom audit -/

#print axioms mulVec_map_surjective
#print axioms surjective_restrict_ker_of_isUnit
#print axioms extendedFibreEval_mulVec_surjective
#print axioms kernelWitnessL_mulVec_zero
#print axioms kernelWitnessL_sum_isUnit
#print axioms extended_atomicV3_surjective_on_sum_zero
#print axioms finrank_towerReads_eq_288
#print axioms joint_surjective_on_hyperplane
#print axioms deployed_joint_coverage_of_terminalTriple
#print axioms finrank_terminalTarget_eq_12
#print axioms finrank_jointTarget_eq_300
#print axioms xBlockEmbed_sum
#print axioms kernelPoly_monic
#print axioms kernelPoly_natDegree
#print axioms kernelShift_natDegree
#print axioms kernelTripleVec_sum_zero
#print axioms kernelTripleVec_mulVec_zero
#print axioms kernelTripleVecL_sum_zero
#print axioms kernelTripleVecL_mulVec_zero
#print axioms eqTerminalTripleCovers_of_tripleMatrix_isUnit
#print axioms sampleQueries_injective
#print axioms splitTower_finrank
#print axioms probe_tripleMatrix_apply
#print axioms probe_tripleMatrix_det
#print axioms width288_bundle_nonvacuous
#print axioms schur_premise_nonvacuous
#print axioms joint_coverage_nonvacuous
#print axioms finrank_bundle_nonvacuous

end AspisV5ComponentARankCompletion
