import AspisFormal.CircleRectangularMasking

/-!
# Component A on the atomic-v3 coefficient hyperplane

`CircleRectangularMasking.lean` proves the deployed 72-by-96 point-evaluation
map `deployedFibreRectangularEval` has full row rank 72, hence its `mulVec` is
surjective onto every 72-coordinate view when the schedule is injective and the
aligned row weights are nonzero.

Atomic-v3 additionally constrains the 96 natural-basis coefficients by ONE
linear relation, `∑ i, c i = 0` (a 95-dimensional hyperplane).  This file proves
the restricted map is STILL surjective: on the `coefficientSum = 0` hyperplane
the deployed map hits every `w`.

The argument is a general kernel-shift lemma (`surjective_restrict_ker`) fed by
one explicit kernel witness.  The witness is the coefficient vector of the monic
degree-36 polynomial `∏ (X − node)` over the 36 signed x-nodes, placed in the
pure-x block.  It lies in the kernel because every released row evaluates that
polynomial at one of its own roots, and it is off the constraint hyperplane
because `∑ coeffs = P.eval 1 = ∏ (1 − node)`, which is nonzero: no deployed fibre
x-coordinate is `±1` (its square is not `1`, since the conjugate y-coordinate is
nonzero on the circle).

This proves surjectivity of the restricted map for the *abstract natural-basis
coefficient vector* over the real deployed M31 field.  Binding these coefficients
to the deployed Rust encoder's coefficient table remains a separate
cross-language obligation, exactly as recorded in `CircleRectangularMasking`.
-/

open Matrix Polynomial

namespace AspisV5AtomicComponentA

open AspisCircleRectangularMasking
open AspisCircleDiscreteAvailability

/-! ## Step 1. A generic kernel-shift surjectivity lemma -/

/-- If a linear map `A` is surjective and `l` is a linear functional not
vanishing on some `k ∈ ker A`, then `A` restricted to `ker l` is still
surjective: every `w` has a preimage on the hyperplane `l = 0`.  Constructive:
shift any preimage `x` by the multiple of `k` that cancels `l x`. -/
theorem surjective_restrict_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (A : V →ₗ[K] W) (hA : Function.Surjective A)
    (l : V →ₗ[K] K) (k : V) (hAk : A k = 0) (hlk : l k ≠ 0) :
    ∀ w, ∃ v, l v = 0 ∧ A v = w := by
  intro w
  obtain ⟨x, hx⟩ := hA w
  refine ⟨x - (l x / l k) • k, ?_, ?_⟩
  · rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ (l x) hlk, sub_self]
  · rw [map_sub, map_smul, hAk, smul_zero, sub_zero, hx]

/-! ## Step 2. The coefficient-sum functional -/

/-- The atomic-v3 constraint functional `c ↦ ∑ i, c i` as a linear map. -/
def coefficientSum : (Fin originalWidth → DeployedField) →ₗ[DeployedField] DeployedField where
  toFun c := ∑ i, c i
  map_add' c d := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] theorem coefficientSum_apply (c : Fin originalWidth → DeployedField) :
    coefficientSum c = ∑ i, c i := rfl

/-! ## Step 3a. The rank theorem upgraded to `mulVec` surjectivity -/

/-- The deployed 72-by-96 map's `mulVec` is surjective (full row rank ⟹
surjective), for every injective schedule and nonzero row weight. -/
theorem deployed_mulVec_surjective
    (queries : Fin queryCount → Fin fibreCount)
    (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField)
    (hweight : ∀ row, weight row ≠ 0) :
    Function.Surjective (deployedFibreRectangularEval queries weight).mulVec := by
  change Function.Surjective ⇑(deployedFibreRectangularEval queries weight).mulVecLin
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  change (deployedFibreRectangularEval queries weight).rank =
    Module.finrank DeployedField (FibreIndex → DeployedField)
  rw [deployedFibreRectangularEval_rank_eq_openedWidth queries hqueries weight hweight,
    Module.finrank_pi]
  have hcard : Fintype.card FibreIndex = openedWidth := by
    norm_num [FibreIndex, FibreSign, queryCount, openedWidth]
  exact hcard.symm

/-! ## Step 3b. The deployed x-coordinates avoid `±1` -/

/-- The x-coordinate of every deployed fibre representative squares to something
other than `1`.  If it were `1`, the on-circle relation would force the
conjugate y-coordinate to zero, contradicting `representative_y_ne_zero`. -/
theorem representative_x_sq_ne_one (j : ℕ) : representativeX j ^ 2 ≠ 1 := by
  intro hx2
  have hon := (AspisCircleGroupOrder.g ^ representativeExp j).2
  simp only [AspisCircleGroupOrder.OnCircle] at hon
  have hy2 : representativeY j ^ 2 = 0 := by
    show (AspisCircleGroupOrder.g ^ representativeExp j).1.2 ^ 2 = 0
    have hx2' : (AspisCircleGroupOrder.g ^ representativeExp j).1.1 ^ 2 = 1 := hx2
    linear_combination hon - hx2'
  exact pow_ne_zero 2 (representative_y_ne_zero j) hy2

/-- A signed deployed x-coordinate is never `1`: both `x` and `−x` would square
to `1`, which is impossible. -/
theorem signedCoordinate_ne_one {z : DeployedField} (h : z ^ 2 ≠ 1) (s : Fin 2) :
    signedCoordinate s z ≠ 1 := by
  intro heq
  apply h
  have h2 : signedCoordinate s z ^ 2 = z ^ 2 := by
    simpa using signedCoordinate_even_pow s z 1
  rw [heq, one_pow] at h2
  exact h2.symm

/-! ## Step 3c. Reading the deployed row as a polynomial evaluation

The `mulVec` of the deployed matrix on a pure-x coefficient vector (nonzero only
on the first 48 columns, holding the coefficients of a polynomial `P` of degree
`< 48`) evaluates `P` at that row's signed x-coordinate, up to the row weight. -/

/-- Abstract row-evaluation identity: summing the deployed row entries against a
degree-`<48` coefficient vector supported on the pure-x block gives
`w · P.eval x`.  The `y`-block coordinate is irrelevant because those columns are
multiplied by zero coefficients. -/
theorem rowEval_eq (w x y : DeployedField) (P : DeployedField[X])
    (hP : P.natDegree < originalHalf) :
    (∑ j : Fin originalWidth,
      (w * (if (j : ℕ) < originalHalf then x ^ (j : ℕ)
              else y * x ^ ((j : ℕ) - originalHalf))) *
        (if (j : ℕ) < originalHalf then P.coeff (j : ℕ) else 0))
      = w * P.eval x := by
  classical
  have hrange :
      (∑ j : Fin originalWidth,
        (w * (if (j : ℕ) < originalHalf then x ^ (j : ℕ)
                else y * x ^ ((j : ℕ) - originalHalf))) *
          (if (j : ℕ) < originalHalf then P.coeff (j : ℕ) else 0))
      = ∑ n ∈ Finset.range originalWidth,
          (w * (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
            (if n < originalHalf then P.coeff n else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun n => (w * (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
          (if n < originalHalf then P.coeff n else 0)) originalWidth
  rw [hrange]
  have hsub : Finset.range originalHalf ⊆ Finset.range originalWidth := by
    intro n hn
    simp only [Finset.mem_range, originalHalf, originalWidth] at hn ⊢
    omega
  have htail : ∀ n ∈ Finset.range originalWidth, n ∉ Finset.range originalHalf →
      (w * (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
        (if n < originalHalf then P.coeff n else 0) = 0 := by
    intro n _ hn'
    rw [Finset.mem_range] at hn'
    simp only [if_neg hn', mul_zero]
  rw [← Finset.sum_subset hsub htail]
  have hcongr : ∀ n ∈ Finset.range originalHalf,
      (w * (if n < originalHalf then x ^ n else y * x ^ (n - originalHalf))) *
        (if n < originalHalf then P.coeff n else 0)
      = w * (P.coeff n * x ^ n) := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos hn, if_pos hn]; ring
  rw [Finset.sum_congr rfl hcongr,
    ← Finset.mul_sum (Finset.range originalHalf) (fun n => P.coeff n * x ^ n) w,
    eval_eq_sum_range' hP x]

/-- The same identity, read off the deployed matrix directly: its `mulVec` on the
pure-x embedding of `P` returns `weight · P.eval (signed x-coordinate)`. -/
theorem mulVec_kernelEmbed
    (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField)
    (P : DeployedField[X]) (hP : P.natDegree < originalHalf)
    (row : FibreIndex) :
    (deployedFibreRectangularEval queries weight).mulVec
        (fun j => if (j : ℕ) < originalHalf then P.coeff (j : ℕ) else 0) row
      = weight row *
        P.eval (signedCoordinate row.2.1 (representativeX (queries row.1))) := by
  have hmv : (deployedFibreRectangularEval queries weight).mulVec
      (fun j => if (j : ℕ) < originalHalf then P.coeff (j : ℕ) else 0) row
      = ∑ j : Fin originalWidth,
          deployedFibreRectangularEval queries weight row j *
            (if (j : ℕ) < originalHalf then P.coeff (j : ℕ) else 0) := rfl
  rw [hmv]
  simp only [deployedFibreRectangularEval]
  exact rowEval_eq (weight row)
    (signedCoordinate row.2.1 (representativeX (queries row.1)))
    (signedCoordinate row.2.2 (representativeY (queries row.1))) P hP

/-! ## Step 3d. The explicit kernel witness -/

/-- The monic degree-36 polynomial vanishing exactly at the 36 signed x-nodes
`±representativeX (queries q)` of the deployed schedule. -/
noncomputable def kernelPoly (queries : Fin queryCount → Fin fibreCount) : DeployedField[X] :=
  ∏ fi : Fin queryCount × Fin 2,
    (X - C (signedCoordinate fi.2 (representativeX (queries fi.1))))

/-- Its coefficient vector, embedded in the pure-x block (first 48 columns) of
the 96 natural-basis coefficients; the y-block is zero. -/
noncomputable def kernelWitness (queries : Fin queryCount → Fin fibreCount) :
    Fin originalWidth → DeployedField :=
  fun j => if (j : ℕ) < originalHalf then (kernelPoly queries).coeff (j : ℕ) else 0

theorem kernelPoly_natDegree_lt (queries : Fin queryCount → Fin fibreCount) :
    (kernelPoly queries).natDegree < originalHalf := by
  rw [kernelPoly, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  norm_num [queryCount, originalHalf]

/-- Every released row evaluates `kernelPoly` at one of its own roots, so the
embedded coefficient vector lies in the kernel of the deployed map. -/
theorem kernelPoly_eval_node_zero (queries : Fin queryCount → Fin fibreCount)
    (q : Fin queryCount) (s : Fin 2) :
    (kernelPoly queries).eval (signedCoordinate s (representativeX (queries q))) = 0 := by
  rw [kernelPoly, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ (q, s)) ?_
  simp only [eval_sub, eval_X, eval_C, sub_self]

theorem kernel_mulVec_zero (queries : Fin queryCount → Fin fibreCount)
    (weight : FibreIndex → DeployedField) :
    (deployedFibreRectangularEval queries weight).mulVec (kernelWitness queries) = 0 := by
  funext row
  rw [Pi.zero_apply]
  show (deployedFibreRectangularEval queries weight).mulVec
      (fun j => if (j : ℕ) < originalHalf then (kernelPoly queries).coeff (j : ℕ) else 0) row = 0
  rw [mulVec_kernelEmbed queries weight (kernelPoly queries) (kernelPoly_natDegree_lt queries) row,
    kernelPoly_eval_node_zero queries row.1 row.2.1, mul_zero]

/-- The coefficient sum of the witness is `kernelPoly.eval 1 = ∏ (1 − node)`. -/
theorem coefficientSum_kernel (queries : Fin queryCount → Fin fibreCount) :
    coefficientSum (kernelWitness queries) = (kernelPoly queries).eval 1 := by
  rw [coefficientSum_apply]
  have hrange :
      (∑ j : Fin originalWidth, kernelWitness queries j)
      = ∑ n ∈ Finset.range originalWidth,
          (if n < originalHalf then (kernelPoly queries).coeff n else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun n => if n < originalHalf then (kernelPoly queries).coeff n else 0) originalWidth
  rw [hrange]
  have hsub : Finset.range originalHalf ⊆ Finset.range originalWidth := by
    intro n hn
    simp only [Finset.mem_range, originalHalf, originalWidth] at hn ⊢
    omega
  have htail : ∀ n ∈ Finset.range originalWidth, n ∉ Finset.range originalHalf →
      (if n < originalHalf then (kernelPoly queries).coeff n else 0) = 0 := by
    intro n _ hn'
    rw [Finset.mem_range] at hn'
    simp only [if_neg hn']
  rw [← Finset.sum_subset hsub htail]
  have hcongr : ∀ n ∈ Finset.range originalHalf,
      (if n < originalHalf then (kernelPoly queries).coeff n else 0)
      = (kernelPoly queries).coeff n := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos hn]
  rw [Finset.sum_congr rfl hcongr, eval_eq_sum_range' (kernelPoly_natDegree_lt queries) 1]
  simp only [one_pow, mul_one]

/-- The witness is off the atomic-v3 hyperplane: `∏ (1 − node) ≠ 0` because no
signed deployed x-coordinate equals `1`. -/
theorem coefficientSum_kernel_ne_zero (queries : Fin queryCount → Fin fibreCount) :
    coefficientSum (kernelWitness queries) ≠ 0 := by
  rw [coefficientSum_kernel, kernelPoly, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr (fun fi _ => ?_)
  rw [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr
    (Ne.symm (signedCoordinate_ne_one (representative_x_sq_ne_one (queries fi.1)) fi.2))

/-! ## The exported theorem -/

/-- **Component A stays surjective on the atomic-v3 hyperplane.**  For every
injective q18 fibre schedule and every nowhere-zero aligned row weight, the
deployed 72-by-96 point-evaluation map, restricted to the 95-dimensional
hyperplane `∑ i, c i = 0`, still hits every 72-coordinate view `w`. -/
theorem deployedAtomicV3ComponentA_surjective
    (queries : Fin queryCount → Fin fibreCount) (hqueries : Function.Injective queries)
    (weight : FibreIndex → DeployedField) (hweight : ∀ row, weight row ≠ 0) :
    ∀ w : FibreIndex → DeployedField, ∃ c : Fin originalWidth → DeployedField,
      coefficientSum c = 0 ∧ (deployedFibreRectangularEval queries weight).mulVec c = w := by
  have hA : Function.Surjective ⇑(deployedFibreRectangularEval queries weight).mulVecLin :=
    deployed_mulVec_surjective queries hqueries weight hweight
  have hAk : (deployedFibreRectangularEval queries weight).mulVecLin (kernelWitness queries) = 0 :=
    kernel_mulVec_zero queries weight
  have hlk : coefficientSum (kernelWitness queries) ≠ 0 :=
    coefficientSum_kernel_ne_zero queries
  intro w
  obtain ⟨v, hlv, hAv⟩ := surjective_restrict_ker
    (deployedFibreRectangularEval queries weight).mulVecLin hA
    coefficientSum (kernelWitness queries) hAk hlk w
  exact ⟨v, hlv, hAv⟩

#print axioms surjective_restrict_ker
#print axioms deployed_mulVec_surjective
#print axioms representative_x_sq_ne_one
#print axioms rowEval_eq
#print axioms mulVec_kernelEmbed
#print axioms kernel_mulVec_zero
#print axioms coefficientSum_kernel_ne_zero
#print axioms deployedAtomicV3ComponentA_surjective

end AspisV5AtomicComponentA
