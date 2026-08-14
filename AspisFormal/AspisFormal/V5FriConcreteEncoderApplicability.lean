import AspisFormal.CircleNaturalBasis
import AspisFormal.V5FunctionalBatching
import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriInitialListBound
import AspisFormal.V5FriNaturalBasisRadix4

/-!
# Concrete encoder distance: the exact remaining applicability boundary

The list-size proof needs pairwise overlap bounds for the four V5 encoders.
This file does not assume those overlap bounds directly.  Instead it proves a
generic root-counting theorem: an encoder whose outputs are evaluations of an
injective bounded-degree polynomial representation on distinct points has the
required overlap bound.

The final `4 -> 2048` tensor is discharged completely from its maintained
definition.  For the preceding line encoders, the remaining code-facing
obligation is reduced to explicit evaluation identities and distinctness of
the released domain points.  The initial circle encoder needs a different
stereographic root argument, supplied by `V5FriCircleEncoderDistance`.  These
interfaces are strictly smaller and more inspectable than assuming the four
distance claims as opaque facts.
-/

namespace AspisV5FriConcreteEncoderApplicability

open Polynomial
open Matrix
open AspisCircleTensorBinding
open AspisV5FunctionalBatching
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriInitialListBound
open AspisV5FriNaturalBasisRadix4

variable {K Message : Type*} {wordSize : Nat}
  [Field K]

/-! ## Distance from a polynomial-evaluation identity -/

/-- Exact data from which a codeword-overlap bound follows.

Unlike a distance premise, every field has a direct implementation meaning:
`encoder_eq_eval` identifies each output symbol, `points_injective` states the
domain has no duplicate evaluation points, and the two polynomial fields say
that different messages give different polynomials of bounded degree. -/
structure PolynomialEvaluationRealization
    (encoder : Message -> Fin wordSize -> K) (degreeCap : Nat) where
  polynomial : Message -> K[X]
  points : Fin wordSize -> K
  polynomial_injective : Function.Injective polynomial
  degree_le : ∀ message, (polynomial message).natDegree ≤ degreeCap
  complete : ∀ p : K[X], p.natDegree ≤ degreeCap ->
    ∃ message, polynomial message = p
  points_injective : Function.Injective points
  encoder_eq_eval : ∀ message x,
    encoder message x = (polynomial message).eval (points x)

/-- The finite-dimensional polynomial space represented by a realization. -/
abbrev DegreeBoundedPolynomial (K : Type*) [Field K] (degreeCap : Nat) :=
  {p : K[X] // p.natDegree ≤ degreeCap}

/-- A realization's message-to-polynomial map with its degree proof attached. -/
def PolynomialEvaluationRealization.toBoundedPolynomial
    {encoder : Message -> Fin wordSize -> K} {degreeCap : Nat}
    (realization : PolynomialEvaluationRealization encoder degreeCap) :
    Message -> DegreeBoundedPolynomial K degreeCap :=
  fun message => ⟨realization.polynomial message, realization.degree_le message⟩

/-- The realization represents exactly, and uniquely, all polynomials through
its degree cap.  This is the property needed to transport decoded RS
polynomials back to verifier messages. -/
theorem PolynomialEvaluationRealization.bijective_toBoundedPolynomial
    {encoder : Message -> Fin wordSize -> K} {degreeCap : Nat}
    (realization : PolynomialEvaluationRealization encoder degreeCap) :
    Function.Bijective realization.toBoundedPolynomial := by
  constructor
  · intro left right heq
    apply realization.polynomial_injective
    exact congrArg Subtype.val heq
  · intro p
    obtain ⟨message, hmessage⟩ := realization.complete p.1 p.2
    refine ⟨message, Subtype.ext ?_⟩
    exact hmessage

/-- Distinct messages in an exact bounded-degree evaluation code agree in at
most `degreeCap` coordinates. -/
theorem agreementSet_card_le_of_polynomialEvaluation
    [DecidableEq K]
    (encoder : Message -> Fin wordSize -> K) (degreeCap : Nat)
    (realization : PolynomialEvaluationRealization encoder degreeCap)
    (left right : Message) (hne : left ≠ right) :
    (agreementSet (encoder left) (encoder right)).card ≤ degreeCap := by
  classical
  let difference := realization.polynomial left - realization.polynomial right
  have hdifference : difference ≠ 0 := by
    intro hzero
    apply hne
    apply realization.polynomial_injective
    exact sub_eq_zero.mp hzero
  have hdegree : difference.natDegree ≤ degreeCap := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (realization.degree_le left) (realization.degree_le right))
  let rootsHit :=
    (agreementSet (encoder left) (encoder right)).image realization.points
  have hsubset : rootsHit.val ⊆ difference.roots := by
    intro point hpoint
    change point ∈
      (agreementSet (encoder left) (encoder right)).image realization.points at hpoint
    obtain ⟨x, hxagree, hpointEq⟩ := Finset.mem_image.mp hpoint
    rw [Polynomial.mem_roots hdifference]
    simp only [Polynomial.IsRoot, difference, Polynomial.eval_sub, sub_eq_zero]
    rw [← hpointEq, ← realization.encoder_eq_eval,
      ← realization.encoder_eq_eval]
    simpa [agreementSet] using hxagree
  calc
    (agreementSet (encoder left) (encoder right)).card = rootsHit.card := by
      exact (Finset.card_image_of_injective _ realization.points_injective).symm
    _ ≤ difference.natDegree :=
      Polynomial.card_le_degree_of_subset_roots hsubset
    _ ≤ degreeCap := hdegree

/-! ### Sharpness: the root-counting bound is exact -/

/-- A polynomial with exactly the first `degreeCap` released points as an
explicit list of roots. -/
noncomputable def exactOverlapPolynomial
    (points : Fin wordSize -> K) {degreeCap : Nat}
    (hcap : degreeCap < wordSize) : K[X] :=
  ∏ i : Fin degreeCap,
    (X - C (points ⟨i, lt_trans i.isLt hcap⟩))

theorem exactOverlapPolynomial_natDegree
    (points : Fin wordSize -> K) {degreeCap : Nat}
    (hcap : degreeCap < wordSize) :
    (exactOverlapPolynomial points hcap).natDegree = degreeCap := by
  rw [exactOverlapPolynomial, natDegree_prod]
  · simp only [natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul,
      Nat.cast_id, mul_one, Finset.card_univ, Fintype.card_fin]
  · intro i _hi
    exact X_sub_C_ne_zero _

theorem exactOverlapPolynomial_ne_zero
    (points : Fin wordSize -> K) {degreeCap : Nat}
    (hcap : degreeCap < wordSize) :
    exactOverlapPolynomial points hcap ≠ 0 := by
  rw [exactOverlapPolynomial]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro i _hi
    exact X_sub_C_ne_zero _)

theorem exactOverlapPolynomial_eval_chosen
    (points : Fin wordSize -> K) {degreeCap : Nat}
    (hcap : degreeCap < wordSize) (i : Fin degreeCap) :
    (exactOverlapPolynomial points hcap).eval
      (points ⟨i, lt_trans i.isLt hcap⟩) = 0 := by
  rw [exactOverlapPolynomial, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- The overlap upper bound is sharp whenever the degree cap is below the
word length: two represented messages agree on exactly `degreeCap` outputs.
Together with `agreementSet_card_le_of_polynomialEvaluation`, this is the
exact Reed--Solomon minimum-distance statement. -/
theorem exists_messages_with_exact_agreement [DecidableEq K]
    (encoder : Message -> Fin wordSize -> K) (degreeCap : Nat)
    (realization : PolynomialEvaluationRealization encoder degreeCap)
    (hcap : degreeCap < wordSize) :
    ∃ left right : Message, left ≠ right ∧
      (agreementSet (encoder left) (encoder right)).card = degreeCap := by
  classical
  let p := exactOverlapPolynomial realization.points hcap
  obtain ⟨left, hleft⟩ := realization.complete p (by
    rw [exactOverlapPolynomial_natDegree])
  obtain ⟨right, hright⟩ := realization.complete 0 (by simp)
  have hpzero : p ≠ 0 := exactOverlapPolynomial_ne_zero _ hcap
  have hlr : left ≠ right := by
    intro heq
    apply hpzero
    rw [← hleft, heq, hright]
  refine ⟨left, right, hlr, le_antisymm
    (agreementSet_card_le_of_polynomialEvaluation encoder degreeCap
      realization left right hlr) ?_⟩
  let chosen : Fin degreeCap -> Fin wordSize :=
    fun i => ⟨i, lt_trans i.isLt hcap⟩
  let chosenSet : Finset (Fin wordSize) := Finset.univ.image chosen
  have hchosenInjective : Function.Injective chosen := by
    intro i j hij
    apply Fin.ext
    simpa [chosen] using congrArg Fin.val hij
  have hcard : chosenSet.card = degreeCap := by
    rw [Finset.card_image_of_injective _ hchosenInjective,
      Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [realization.encoder_eq_eval, realization.encoder_eq_eval,
    hleft, hright]
  simp only [eval_zero]
  exact exactOverlapPolynomial_eval_chosen realization.points hcap i

/-! ## Complete bounded-degree line-polynomial representation -/

/-- Ordinary polynomial assembled from a fixed-width monomial coefficient
vector. -/
noncomputable def monomialPolynomial {n : Nat} (c : Fin n -> K) : K[X] :=
  ∑ i, C (c i) * X ^ (i : Nat)

@[simp] theorem monomialPolynomial_coeff {n : Nat} (c : Fin n -> K)
    (i : Fin n) :
    (monomialPolynomial c).coeff i = c i := by
  classical
  change (Polynomial.lcoeff K i) (∑ j, C (c j) * X ^ (j : Nat)) = c i
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    rw [if_neg]
    exact fun hij => hji (Fin.ext hij.symm)
  · simp

theorem monomialPolynomial_coeff_eq_zero_of_ge {n : Nat}
    (c : Fin n -> K) (degree : Nat) (hdegree : n ≤ degree) :
    (monomialPolynomial c).coeff degree = 0 := by
  classical
  change (Polynomial.lcoeff K degree) (∑ i, C (c i) * X ^ (i : Nat)) = 0
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [if_neg]
  omega

theorem monomialPolynomial_natDegree_le {n : Nat} (hn : 0 < n)
    (c : Fin n -> K) :
    (monomialPolynomial c).natDegree ≤ n - 1 := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    simp only [Polynomial.natDegree_X_pow]
    omega)

theorem monomialPolynomial_injective {n : Nat} :
    Function.Injective (monomialPolynomial (K := K) (n := n)) := by
  intro left right heq
  funext i
  have hcoeff := congrArg (fun p : K[X] => p.coeff i) heq
  simpa only [monomialPolynomial_coeff] using hcoeff

theorem monomialPolynomial_complete {n : Nat} (hn : 0 < n)
    (p : K[X]) (hdegree : p.natDegree ≤ n - 1) :
    ∃ c : Fin n -> K, monomialPolynomial c = p := by
  refine ⟨fun i => p.coeff i, ?_⟩
  ext degree
  by_cases hsmall : degree < n
  · let i : Fin n := ⟨degree, hsmall⟩
    change (monomialPolynomial (fun i : Fin n => p.coeff i)).coeff i = p.coeff i
    exact monomialPolynomial_coeff _ i
  · have hlarge : n ≤ degree := Nat.le_of_not_gt hsmall
    have hleft := monomialPolynomial_coeff_eq_zero_of_ge
      (fun i : Fin n => p.coeff i) degree hlarge
    have hpdegree : p.natDegree < degree := by omega
    rw [hleft, Polynomial.coeff_eq_zero_of_natDegree_lt hpdegree]

/-- Change natural line-basis coefficients into monomial coefficients using
the already-proved triangular change-of-basis matrix. -/
noncomputable def naturalToMonomialCoefficients {n : Nat}
    (c : Fin n -> K) : Fin n -> K :=
  naturalCoeffMatrix K n *ᵥ c

theorem naturalToMonomialCoefficients_bijective {n : Nat} [NeZero (2 : K)] :
    Function.Bijective (naturalToMonomialCoefficients (K := K) (n := n)) := by
  constructor
  · apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    exact isUnit_iff_ne_zero.mpr (naturalCoeffMatrix_det_ne_zero (K := K) n)
  · intro coefficients
    refine ⟨monomialToNatural K n *ᵥ coefficients, ?_⟩
    unfold naturalToMonomialCoefficients
    rw [Matrix.mulVec_mulVec, naturalCoeff_mul_monomialToNatural,
      Matrix.one_mulVec]

/-- Polynomial represented by a vector in the natural line basis used by the
circle FFT. -/
noncomputable def naturalCoefficientPolynomial {n : Nat}
    (c : Fin n -> K) : K[X] :=
  monomialPolynomial (naturalToMonomialCoefficients c)

theorem naturalCoefficientPolynomial_injective {n : Nat} [NeZero (2 : K)] :
    Function.Injective (naturalCoefficientPolynomial (K := K) (n := n)) :=
  monomialPolynomial_injective.comp
    (naturalToMonomialCoefficients_bijective (K := K) (n := n)).1

theorem naturalCoefficientPolynomial_natDegree_le {n : Nat} (hn : 0 < n)
    (c : Fin n -> K) :
    (naturalCoefficientPolynomial c).natDegree ≤ n - 1 :=
  monomialPolynomial_natDegree_le hn _

theorem naturalCoefficientPolynomial_complete {n : Nat} [NeZero (2 : K)]
    (hn : 0 < n) (p : K[X]) (hdegree : p.natDegree ≤ n - 1) :
    ∃ c : Fin n -> K, naturalCoefficientPolynomial c = p := by
  obtain ⟨monomialCoefficients, hpoly⟩ :=
    monomialPolynomial_complete hn p hdegree
  obtain ⟨naturalCoefficients, hcoefficients⟩ :=
    (naturalToMonomialCoefficients_bijective (K := K) (n := n)).2
      monomialCoefficients
  refine ⟨naturalCoefficients, ?_⟩
  rw [naturalCoefficientPolynomial, hcoefficients, hpoly]

/-! ### Exact evaluation in the maintained natural basis -/

/-- Below the message width, the coefficient of the assembled polynomial is
the corresponding coefficient of the maintained natural-basis sum. -/
theorem naturalCoefficientPolynomial_coeff_lt {n : Nat}
    (c : Fin n -> K) (degree : Fin n) :
    (naturalCoefficientPolynomial c).coeff degree =
      ∑ basis : Fin n,
        c basis * (naturalLinePoly K basis).coeff degree := by
  rw [naturalCoefficientPolynomial, monomialPolynomial_coeff]
  unfold naturalToMonomialCoefficients naturalCoeffMatrix Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro basis _hbasis
  ring

/-- The explicit natural-basis sum has degree below the message width. -/
theorem naturalBasisSum_natDegree_le {n : Nat} [NeZero (2 : K)] (hn : 0 < n)
    (c : Fin n -> K) :
    (∑ basis : Fin n, C (c basis) * naturalLinePoly K basis).natDegree ≤
      n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro basis _hbasis
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    have hdeg : (naturalLinePoly K (basis : Nat)).natDegree = (basis : Nat) :=
      naturalLinePoly_natDegree (K := K) (index := (basis : Nat))
    rw [hdeg]
    omega)

/-- The triangular coefficient construction is exactly the polynomial written
as a sum of the maintained natural basis polynomials. -/
theorem naturalCoefficientPolynomial_eq_basisSum {n : Nat} [NeZero (2 : K)]
    (hn : 0 < n)
    (c : Fin n -> K) :
    naturalCoefficientPolynomial c =
      ∑ basis : Fin n, C (c basis) * naturalLinePoly K basis := by
  ext degree
  by_cases hsmall : degree < n
  · let d : Fin n := ⟨degree, hsmall⟩
    change (naturalCoefficientPolynomial c).coeff d =
      (∑ basis : Fin n, C (c basis) * naturalLinePoly K basis).coeff d
    rw [naturalCoefficientPolynomial_coeff_lt]
    change (∑ basis : Fin n, c basis * (naturalLinePoly K basis).coeff d) =
      (Polynomial.lcoeff K d)
        (∑ basis : Fin n, C (c basis) * naturalLinePoly K basis)
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul]
  · have hlarge : n ≤ degree := Nat.le_of_not_gt hsmall
    have hleft : (naturalCoefficientPolynomial c).coeff degree = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by
        exact lt_of_le_of_lt (naturalCoefficientPolynomial_natDegree_le hn c)
          (by omega))
    have hright :
        (∑ basis : Fin n, C (c basis) * naturalLinePoly K basis).coeff degree = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by
        exact lt_of_le_of_lt (naturalBasisSum_natDegree_le hn c) (by omega))
    rw [hleft, hright]

/-- Evaluation of the represented polynomial is exactly the maintained
natural-basis dot product. -/
theorem naturalCoefficientPolynomial_eval_eq_sum {n : Nat} [NeZero (2 : K)]
    (hn : 0 < n)
    (c : Fin n -> K) (x : K) :
    (naturalCoefficientPolynomial c).eval x =
      ∑ basis : Fin n, c basis * naturalLineValue x basis := by
  rw [naturalCoefficientPolynomial_eq_basisSum hn]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro basis _hbasis
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    naturalLineValue_eq_eval]

/-- Fibre-major indices are equivalent to a parent index and a radix-four
slot. -/
def fibreIndexEquiv (n : Nat) : Fin n × Fin 4 ≃ Fin (4 * n) where
  toFun pair := childIndex pair.1 pair.2
  invFun k := (parentIndex k, slotIndex k)
  left_inv pair := by
    rcases pair with ⟨i, slot⟩
    simp
  right_inv k := childIndex_parentIndex_slotIndex k

@[simp] theorem fibreIndexEquiv_apply {n : Nat} (pair : Fin n × Fin 4) :
    fibreIndexEquiv n pair = childIndex pair.1 pair.2 := rfl

/-- A width-`4n` natural-basis polynomial splits into its four adjacent
coefficient lanes.  The low two basis bits give
`[1,x,T₂(x),x*T₂(x)]`, while the high bits are evaluated at `T₄(x)`. -/
theorem naturalCoefficientPolynomial_eval_radix4 {n : Nat} [NeZero (2 : K)]
    (hn : 0 < n)
    (c : Fin (4 * n) -> K) (x : K) :
    (naturalCoefficientPolynomial c).eval x =
      ∑ lane : Fin 4,
        ![1, x, doubledFactor x 1, x * doubledFactor x 1] lane *
          (naturalCoefficientPolynomial (coefficientLane n lane c)).eval
            (doubledFactor x 2) := by
  rw [naturalCoefficientPolynomial_eval_eq_sum (by omega)]
  rw [← (fibreIndexEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [fibreIndexEquiv_apply, childIndex_val,
    naturalLineValue_four_mul_add]
  simp_rw [naturalCoefficientPolynomial_eval_eq_sum hn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lane _hlane
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  change c (childIndex q lane) *
      (naturalLineValue (doubledFactor x 2) q *
        ![1, x, doubledFactor x 1, x * doubledFactor x 1] lane) =
    ![1, x, doubledFactor x 1, x * doubledFactor x 1] lane *
      (c (childIndex q lane) * naturalLineValue (doubledFactor x 2) q)
  ring

/-! ### One recursive radix-four evaluation layer -/

/-- The child-domain point in each of the four stored fibre slots. -/
def radix4ChildPoint (x0 x1 : K) : Fin 4 -> K :=
  ![x0, -x0, x1, -x1]

/-- The first doubling of the four child points has the signs used by the
maintained radix-four evaluator. -/
theorem radix4ChildPoint_t2 (x0 x1 x2 : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2) (slot : Fin 4) :
    doubledFactor (radix4ChildPoint x0 x1 slot) 1 =
      ![x2, x2, -x2, -x2] slot := by
  have h0' : 2 * x0 ^ 2 - 1 = x2 := by
    simpa [doubledFactor] using h0
  have h1' : 2 * x1 ^ 2 - 1 = -x2 := by
    simpa [doubledFactor] using h1
  fin_cases slot <;> simp [radix4ChildPoint, doubledFactor, h0', h1']

/-- Two doublings send every slot in a radix-four fibre to its parent point. -/
theorem radix4ChildPoint_t4 (x0 x1 x2 parent : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2)
    (h2 : doubledFactor x2 1 = parent) (slot : Fin 4) :
    doubledFactor (radix4ChildPoint x0 x1 slot) 2 = parent := by
  rw [show 2 = 1 + 1 by omega, doubledFactor_add]
  rw [radix4ChildPoint_t2 x0 x1 x2 h0 h1 slot]
  have h2' : 2 * x2 ^ 2 - 1 = parent := by
    simpa [doubledFactor] using h2
  fin_cases slot <;> simp [doubledFactor, h2']

/-- The maintained local radix-four evaluator is the natural-basis dot
product at the corresponding child point. -/
theorem radix4Evaluate_eq_natural_low (x0 x1 x2 : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2)
    (values : Fin 4 -> K) (slot : Fin 4) :
    radix4Evaluate x0 x1 x2 values slot =
      ∑ lane : Fin 4,
        ![1, radix4ChildPoint x0 x1 slot,
          doubledFactor (radix4ChildPoint x0 x1 slot) 1,
          radix4ChildPoint x0 x1 slot *
            doubledFactor (radix4ChildPoint x0 x1 slot) 1] lane *
          values lane := by
  have h0' : 2 * x0 ^ 2 - 1 = x2 := by
    simpa [doubledFactor] using h0
  have h1' : 2 * x1 ^ 2 - 1 = -x2 := by
    simpa [doubledFactor] using h1
  fin_cases slot <;>
    simp [radix4ChildPoint, radix4Evaluate, doubledFactor, h0', h1',
      Fin.sum_univ_four] <;>
    ring

/-- The geometric facts needed for one recursive line-code layer.  They say
which four points form a stored fibre and how their first and second doubling
coordinates meet the parent domain. -/
structure Radix4LineGeometry {m : Nat}
    (childPoint : Fin (4 * m) -> K) (parentPoint : Fin m -> K)
    (x0 x1 x2 : Fin m -> K) where
  child_slot : ∀ i slot,
    childPoint (childIndex i slot) = radix4ChildPoint (x0 i) (x1 i) slot
  t2_x0 : ∀ i, doubledFactor (x0 i) 1 = x2 i
  t2_x1 : ∀ i, doubledFactor (x1 i) 1 = -x2 i
  t2_x2 : ∀ i, doubledFactor (x2 i) 1 = parentPoint i

/-- If a smaller encoder evaluates natural-basis polynomials on a parent
domain, one explicit radix-four lift evaluates the four-times-wider natural
polynomial on the child domain. -/
theorem radix4LiftEncoder_eq_natural_eval {n m : Nat} [NeZero (2 : K)]
    (hn : 0 < n)
    (encoder : (Fin n -> K) →ₗ[K] (Fin m -> K))
    (parentPoint : Fin m -> K) (x0 x1 x2 : Fin m -> K)
    (childPoint : Fin (4 * m) -> K)
    (hencoder : ∀ message i, encoder message i =
      (naturalCoefficientPolynomial message).eval (parentPoint i))
    (geometry : Radix4LineGeometry childPoint parentPoint x0 x1 x2)
    (message : Fin (4 * n) -> K) (k : Fin (4 * m)) :
    radix4LiftEncoder encoder x0 x1 x2 message k =
      (naturalCoefficientPolynomial message).eval (childPoint k) := by
  suffices hchild : ∀ (i : Fin m) (slot : Fin 4),
      radix4LiftEncoder encoder x0 x1 x2 message (childIndex i slot) =
        (naturalCoefficientPolynomial message).eval
          (childPoint (childIndex i slot)) by
    simpa only [childIndex_parentIndex_slotIndex] using
      hchild (parentIndex k) (slotIndex k)
  intro i slot
  rw [radix4LiftEncoder_apply_child]
  rw [naturalCoefficientPolynomial_eval_radix4 hn]
  rw [geometry.child_slot]
  rw [radix4ChildPoint_t4 (x0 i) (x1 i) (x2 i) (parentPoint i)
    (geometry.t2_x0 i) (geometry.t2_x1 i) (geometry.t2_x2 i)]
  simp_rw [← hencoder]
  exact radix4Evaluate_eq_natural_low (x0 i) (x1 i) (x2 i)
    (geometry.t2_x0 i) (geometry.t2_x1 i)
    (fun lane => encoder (coefficientLane n lane message) i) slot

/-- What remains to identify a concrete line encoder with Reed--Solomon
evaluation: its exact output points and one pointwise natural-basis identity.
No distance, list size, or decoder theorem is included. -/
structure NaturalLineEvaluationIdentity {n m : Nat}
    (encoder : (Fin n -> K) -> Fin m -> K) where
  points : Fin m -> K
  points_injective : Function.Injective points
  encoder_eq_eval : ∀ message x,
    encoder message x = (naturalCoefficientPolynomial message).eval (points x)

/-- A natural-line evaluation identity gives the complete polynomial
realization required both for distance and for transporting decoded RS
polynomials back to verifier coefficient vectors. -/
noncomputable def naturalLinePolynomialRealization {n m : Nat}
    [NeZero (2 : K)] (hn : 0 < n)
    (encoder : (Fin n -> K) -> Fin m -> K)
    (identity : NaturalLineEvaluationIdentity encoder) :
    PolynomialEvaluationRealization encoder (n - 1) where
  polynomial := naturalCoefficientPolynomial
  points := identity.points
  polynomial_injective := naturalCoefficientPolynomial_injective
  degree_le := naturalCoefficientPolynomial_natDegree_le hn
  complete := naturalCoefficientPolynomial_complete hn
  points_injective := identity.points_injective
  encoder_eq_eval := identity.encoder_eq_eval

/-! ## The maintained final tensor is an ordinary cubic -/

/-- Monomial coefficients of
`c0 + c1*x + c2*(2*x^2-1) + c3*x*(2*x^2-1)`. -/
def finalTensorMonomialCoefficients (c : Fin 4 -> K) : Fin 4 -> K :=
  ![c 0 - c 2, c 1 - c 3, 2 * c 2, 2 * c 3]

/-- The polynomial represented by the maintained final tensor. -/
noncomputable def finalTensorPolynomial (c : Fin 4 -> K) : K[X] :=
  discrepancyPolynomial (finalTensorMonomialCoefficients c)

theorem finalTensorPolynomial_eval (c : Fin 4 -> K) (x : K) :
    (finalTensorPolynomial c).eval x = finalTensorValue x c := by
  simp [finalTensorPolynomial, eval_discrepancyPolynomial,
    finalTensorMonomialCoefficients, finalTensorValue, batchedDiscrepancy]
  ring

/-- The maintained final tensor is also exactly the first four terms of the
same natural-basis polynomial representation used by the recursive layers. -/
theorem finalTensorValue_eq_naturalCoefficientPolynomial_eval
    [NeZero (2 : K)] (c : Fin 4 -> K) (x : K) :
    finalTensorValue x c = (naturalCoefficientPolynomial c).eval x := by
  rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
  have hv0 : naturalLineValue x 0 = 1 := by
    simp [naturalLineValue]
  have hv1 : naturalLineValue x 1 = x := by
    simpa [naturalLineValue] using naturalLineValue_two_mul_add_one x 0
  have hv2 : naturalLineValue x 2 = doubledFactor x 1 := by
    rw [show 2 = 2 * 1 by omega, naturalLineValue_two_mul]
    simpa [naturalLineValue] using
      naturalLineValue_two_mul_add_one (doubledFactor x 1) 0
  have hv3 : naturalLineValue x 3 = x * doubledFactor x 1 := by
    rw [show 3 = 2 * 1 + 1 by omega, naturalLineValue_two_mul_add_one]
    congr 1
  rw [Fin.sum_univ_four]
  change finalTensorValue x c =
    c 0 * naturalLineValue x 0 + c 1 * naturalLineValue x 1 +
      c 2 * naturalLineValue x 2 + c 3 * naturalLineValue x 3
  rw [hv0, hv1, hv2, hv3]
  simp [finalTensorValue, doubledFactor]

theorem finalTensorPolynomial_natDegree_le_three (c : Fin 4 -> K) :
    (finalTensorPolynomial c).natDegree ≤ 3 :=
  natDegree_discrepancyPolynomial_le _

/-- The change of basis `[1,x,2x^2-1,x(2x^2-1)]` to the monomial basis is
invertible whenever two is nonzero. -/
theorem finalTensorMonomialCoefficients_injective [NeZero (2 : K)] :
    Function.Injective (finalTensorMonomialCoefficients (K := K)) := by
  intro left right heq
  have hcoord : ∀ i, finalTensorMonomialCoefficients left i =
      finalTensorMonomialCoefficients right i := fun i => congrFun heq i
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  have h2 : left 2 = right 2 := by
    apply mul_left_cancel₀ htwo
    simpa [finalTensorMonomialCoefficients] using hcoord 2
  have h3 : left 3 = right 3 := by
    apply mul_left_cancel₀ htwo
    simpa [finalTensorMonomialCoefficients] using hcoord 3
  funext i
  fin_cases i
  · have h0 := hcoord 0
    simp only [finalTensorMonomialCoefficients, Matrix.cons_val_zero] at h0
    rw [h2] at h0
    exact sub_left_inj.mp h0
  · have h1 := hcoord 1
    simp only [finalTensorMonomialCoefficients, Matrix.cons_val_one,
      Matrix.cons_val_zero] at h1
    rw [h3] at h1
    exact sub_left_inj.mp h1
  · exact h2
  · exact h3

theorem finalTensorPolynomial_injective [NeZero (2 : K)] :
    Function.Injective (finalTensorPolynomial (K := K)) := by
  intro left right heq
  apply finalTensorMonomialCoefficients_injective
  funext i
  have hcoeff := congrArg (fun p : K[X] => p.coeff i) heq
  simpa only [finalTensorPolynomial, coeff_discrepancyPolynomial] using hcoeff

/-- Inverse change of basis, read from the first four monomial coefficients. -/
def finalTensorMessageOfPolynomial (p : K[X]) : Fin 4 -> K :=
  ![p.coeff 0 + p.coeff 2 / 2,
    p.coeff 1 + p.coeff 3 / 2,
    p.coeff 2 / 2,
    p.coeff 3 / 2]

theorem finalTensorMonomialCoefficients_messageOfPolynomial
    [NeZero (2 : K)] (p : K[X]) :
    finalTensorMonomialCoefficients (finalTensorMessageOfPolynomial p) =
      fun i : Fin 4 => p.coeff i := by
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  funext i
  fin_cases i <;>
    simp [finalTensorMonomialCoefficients, finalTensorMessageOfPolynomial]
  all_goals field_simp

/-- Every polynomial of degree at most three has a unique maintained final
tensor representation. -/
theorem finalTensorPolynomial_complete [NeZero (2 : K)]
    (p : K[X]) (hdegree : p.natDegree ≤ 3) :
    ∃ c : Fin 4 -> K, finalTensorPolynomial c = p := by
  refine ⟨finalTensorMessageOfPolynomial p, ?_⟩
  ext n
  by_cases hn : n < 4
  · let i : Fin 4 := ⟨n, hn⟩
    have hcoordinates := congrFun
      (finalTensorMonomialCoefficients_messageOfPolynomial p) i
    change (finalTensorPolynomial (finalTensorMessageOfPolynomial p)).coeff i =
      p.coeff i
    simpa only [finalTensorPolynomial, coeff_discrepancyPolynomial] using hcoordinates
  · have hnlarge : 3 < n := by omega
    have hleft :
        (finalTensorPolynomial (finalTensorMessageOfPolynomial p)).coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt
          (finalTensorPolynomial_natDegree_le_three _) hnlarge)
    have hright : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hdegree hnlarge)
    rw [hleft, hright]

/-! ## Final V5 encoder -/

section FinalEncoder

variable {F : Type*} [Field F] [Algebra F K]

/-- The released final-domain `x` values are the only geometric fact needed
for the final tensor: they must be pairwise distinct. -/
def FinalDomainDistinct (schedule : FixedSchedule F K) : Prop :=
  Function.Injective schedule.finalX

/-- Exact polynomial-evaluation realization of `encoder4`.  No encoder or
distance statement is assumed here; the pointwise identity follows by
unfolding `finalTensorValue`. -/
noncomputable def encoder4PolynomialRealization [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (hdistinct : FinalDomainDistinct schedule) :
    PolynomialEvaluationRealization (encoder4 schedule) 3 where
  polynomial := finalTensorPolynomial
  points := fun i => algebraMap F K (schedule.finalX i)
  polynomial_injective := finalTensorPolynomial_injective
  degree_le := finalTensorPolynomial_natDegree_le_three
  complete := finalTensorPolynomial_complete
  points_injective := by
    intro i j hij
    apply hdistinct
    exact (FaithfulSMul.algebraMap_injective F K) hij
  encoder_eq_eval := by
    intro message i
    rw [encoder4_apply, finalTensorPolynomial_eval]

theorem encoder4_messagePolynomial_bijective [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (hdistinct : FinalDomainDistinct schedule) :
    Function.Bijective
      (encoder4PolynomialRealization schedule hdistinct).toBoundedPolynomial :=
  (encoder4PolynomialRealization schedule hdistinct).bijective_toBoundedPolynomial

/-- Two distinct published final tensors agree on at most three of the 2048
released final-domain points. -/
theorem encoder4_agreement_card_le_three [Fintype K] [DecidableEq K]
    [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (hdistinct : FinalDomainDistinct schedule)
    (left right : Coeff4 K) (hne : left ≠ right) :
    (agreementSet (encoder4 schedule left) (encoder4 schedule right)).card ≤ 3 :=
  agreementSet_card_le_of_polynomialEvaluation
    (encoder4 schedule) 3
    (encoder4PolynomialRealization schedule hdistinct) left right hne

/-- Distinct final tensors imply distinct final codewords. -/
theorem encoder4_injective_of_distinct [Fintype K] [DecidableEq K]
    [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (hdistinct : FinalDomainDistinct schedule) :
    Function.Injective (encoder4 schedule) := by
  intro left right hcode
  by_contra hne
  have hoverlap := encoder4_agreement_card_le_three schedule hdistinct
    left right hne
  have hall : agreementSet (encoder4 schedule left)
      (encoder4 schedule right) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrFun hcode i
  rw [hall] at hoverlap
  norm_num at hoverlap

/-- The final code's overlap bound is attained, so its minimum distance is
exactly `2048 - 3`. -/
theorem encoder4_exists_exact_agreement_three [DecidableEq K]
    [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (hdistinct : FinalDomainDistinct schedule) :
    ∃ left right : Coeff4 K, left ≠ right ∧
      (agreementSet (encoder4 schedule left)
        (encoder4 schedule right)).card = 3 :=
  exists_messages_with_exact_agreement (encoder4 schedule) 3
    (encoder4PolynomialRealization schedule hdistinct) (by norm_num)

end FinalEncoder

/-! ## The three committed line encoders -/

section LineEncoders

variable {F : Type*} [Field F] [Algebra F K]

/-- One geometric description of all four line domains used by the recursive
V5 encoder.  Its three layer fields contain only the fibre-coordinate and
doubling equations; evaluation of encoder outputs is derived below. -/
structure LineTowerGeometry
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) where
  node1 : Fin 131072 -> K
  node2 : Fin 32768 -> K
  node3 : Fin 8192 -> K
  node4 : Fin 2048 -> K
  node1_injective : Function.Injective node1
  node2_injective : Function.Injective node2
  node3_injective : Function.Injective node3
  node4_injective : Function.Injective node4
  layer1 : Radix4LineGeometry node1 node2
    (fun i => algebraMap F K (points.line1 i 0))
    (fun i => algebraMap F K (points.line1 i 1))
    (fun i => algebraMap F K (points.line1 i 2))
  layer2 : Radix4LineGeometry node2 node3
    (fun i => algebraMap F K (points.line2 i 0))
    (fun i => algebraMap F K (points.line2 i 1))
    (fun i => algebraMap F K (points.line2 i 2))
  layer3 : Radix4LineGeometry node3 node4
    (fun i => algebraMap F K (points.line3 i 0))
    (fun i => algebraMap F K (points.line3 i 1))
    (fun i => algebraMap F K (points.line3 i 2))
  final_point : ∀ i, node4 i = algebraMap F K (schedule.finalX i)

/-- Exact natural-basis evaluation identities for the three committed line
layers.  The domain points belong to each identity and must be distinct. -/
structure ConcreteLineEvaluationIdentities
    (schedule : FixedSchedule F K) (points : EvaluationPoints F) where
  layer1 : NaturalLineEvaluationIdentity (encoder1 schedule points)
  layer2 : NaturalLineEvaluationIdentity (encoder2 schedule points)
  layer3 : NaturalLineEvaluationIdentity (encoder3 schedule points)

/-- The three former pointwise evaluation obligations follow recursively from
one line-tower geometry.  Thus there is no separate encoder-evaluation premise
at each committed layer. -/
noncomputable def concreteLineEvaluationIdentities_of_geometry
    [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (geometry : LineTowerGeometry schedule points) :
    ConcreteLineEvaluationIdentities schedule points := by
  have hencoder4 : ∀ (message : Coeff4 K) (i : Fin 2048),
      encoder4 schedule message i =
        (naturalCoefficientPolynomial message).eval (geometry.node4 i) := by
    intro message i
    rw [encoder4_apply, geometry.final_point]
    exact finalTensorValue_eq_naturalCoefficientPolynomial_eval message _
  have hencoder3 : ∀ (message : Coeff3 K) (i : Fin 8192),
      encoder3 schedule points message i =
        (naturalCoefficientPolynomial message).eval (geometry.node3 i) := by
    intro message i
    simpa only [encoder3] using
      radix4LiftEncoder_eq_natural_eval (K := K) (by norm_num)
        (encoder4 schedule) geometry.node4
        (fun j => algebraMap F K (points.line3 j 0))
        (fun j => algebraMap F K (points.line3 j 1))
        (fun j => algebraMap F K (points.line3 j 2))
        geometry.node3 hencoder4 geometry.layer3 message i
  have hencoder2 : ∀ (message : Coeff2 K) (i : Fin 32768),
      encoder2 schedule points message i =
        (naturalCoefficientPolynomial message).eval (geometry.node2 i) := by
    intro message i
    simpa only [encoder2] using
      radix4LiftEncoder_eq_natural_eval (K := K) (by norm_num)
        (encoder3 schedule points) geometry.node3
        (fun j => algebraMap F K (points.line2 j 0))
        (fun j => algebraMap F K (points.line2 j 1))
        (fun j => algebraMap F K (points.line2 j 2))
        geometry.node2 hencoder3 geometry.layer2 message i
  have hencoder1 : ∀ (message : Coeff1 K) (i : Fin 131072),
      encoder1 schedule points message i =
        (naturalCoefficientPolynomial message).eval (geometry.node1 i) := by
    intro message i
    simpa only [encoder1] using
      radix4LiftEncoder_eq_natural_eval (K := K) (by norm_num)
        (encoder2 schedule points) geometry.node2
        (fun j => algebraMap F K (points.line1 j 0))
        (fun j => algebraMap F K (points.line1 j 1))
        (fun j => algebraMap F K (points.line1 j 2))
        geometry.node1 hencoder2 geometry.layer1 message i
  exact {
    layer1 := {
      points := geometry.node1
      points_injective := geometry.node1_injective
      encoder_eq_eval := hencoder1 }
    layer2 := {
      points := geometry.node2
      points_injective := geometry.node2_injective
      encoder_eq_eval := hencoder2 }
    layer3 := {
      points := geometry.node3
      points_injective := geometry.node3_injective
      encoder_eq_eval := hencoder3 } }

noncomputable def encoder1PolynomialRealization [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder1 schedule points)) :
    PolynomialEvaluationRealization (encoder1 schedule points) 255 := by
  simpa using naturalLinePolynomialRealization (K := K)
    (n := 256) (m := 131072) (by norm_num)
      (encoder1 schedule points) identity

theorem encoder1_messagePolynomial_bijective [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder1 schedule points)) :
    Function.Bijective
      (encoder1PolynomialRealization schedule points identity).toBoundedPolynomial :=
  (encoder1PolynomialRealization schedule points identity).bijective_toBoundedPolynomial

noncomputable def encoder2PolynomialRealization [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder2 schedule points)) :
    PolynomialEvaluationRealization (encoder2 schedule points) 63 := by
  simpa using naturalLinePolynomialRealization (K := K)
    (n := 64) (m := 32768) (by norm_num)
      (encoder2 schedule points) identity

theorem encoder2_messagePolynomial_bijective [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder2 schedule points)) :
    Function.Bijective
      (encoder2PolynomialRealization schedule points identity).toBoundedPolynomial :=
  (encoder2PolynomialRealization schedule points identity).bijective_toBoundedPolynomial

noncomputable def encoder3PolynomialRealization [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder3 schedule points)) :
    PolynomialEvaluationRealization (encoder3 schedule points) 15 := by
  simpa using naturalLinePolynomialRealization (K := K)
    (n := 16) (m := 8192) (by norm_num)
      (encoder3 schedule points) identity

theorem encoder3_messagePolynomial_bijective [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder3 schedule points)) :
    Function.Bijective
      (encoder3PolynomialRealization schedule points identity).toBoundedPolynomial :=
  (encoder3PolynomialRealization schedule points identity).bijective_toBoundedPolynomial

theorem encoder1_agreement_card_le_255
    [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder1 schedule points))
    (left right : Coeff1 K) (hne : left ≠ right) :
    (agreementSet (encoder1 schedule points left)
      (encoder1 schedule points right)).card ≤ 255 :=
  agreementSet_card_le_of_polynomialEvaluation
    (encoder1 schedule points) 255
    (encoder1PolynomialRealization schedule points identity) left right hne

theorem encoder2_agreement_card_le_63
    [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder2 schedule points))
    (left right : Coeff2 K) (hne : left ≠ right) :
    (agreementSet (encoder2 schedule points left)
      (encoder2 schedule points right)).card ≤ 63 :=
  agreementSet_card_le_of_polynomialEvaluation
    (encoder2 schedule points) 63
    (encoder2PolynomialRealization schedule points identity) left right hne

theorem encoder3_agreement_card_le_15
    [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identity : NaturalLineEvaluationIdentity (encoder3 schedule points))
    (left right : Coeff3 K) (hne : left ≠ right) :
    (agreementSet (encoder3 schedule points left)
      (encoder3 schedule points right)).card ≤ 15 :=
  agreementSet_card_le_of_polynomialEvaluation
    (encoder3 schedule points) 15
    (encoder3PolynomialRealization schedule points identity) left right hne

/-- All three line-code distance statements follow from the exact evaluation
identities. -/
theorem concrete_line_encoder_distances
    [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identities : ConcreteLineEvaluationIdentities schedule points) :
    Layer1EncoderDistance (concreteCodeEncoders schedule points) ∧
      Layer2EncoderDistance (concreteCodeEncoders schedule points) ∧
      Layer3EncoderDistance (concreteCodeEncoders schedule points) := by
  exact ⟨
    fun left right hne =>
      encoder1_agreement_card_le_255 schedule points identities.layer1
        left right hne,
    fun left right hne =>
      encoder2_agreement_card_le_63 schedule points identities.layer2
        left right hne,
    fun left right hne =>
      encoder3_agreement_card_le_15 schedule points identities.layer3
        left right hne⟩

/-- Each committed line encoder attains its root-counting overlap bound.
Consequently their minimum distances are exactly
`131072-255`, `32768-63`, and `8192-15`. -/
theorem concrete_line_encoder_exact_overlap_witnesses
    [DecidableEq K] [NeZero (2 : K)]
    (schedule : FixedSchedule F K) (points : EvaluationPoints F)
    (identities : ConcreteLineEvaluationIdentities schedule points) :
    (∃ left right : Coeff1 K, left ≠ right ∧
      (agreementSet (encoder1 schedule points left)
        (encoder1 schedule points right)).card = 255) ∧
    (∃ left right : Coeff2 K, left ≠ right ∧
      (agreementSet (encoder2 schedule points left)
        (encoder2 schedule points right)).card = 63) ∧
    (∃ left right : Coeff3 K, left ≠ right ∧
      (agreementSet (encoder3 schedule points left)
        (encoder3 schedule points right)).card = 15) := by
  exact ⟨
    exists_messages_with_exact_agreement (encoder1 schedule points) 255
      (encoder1PolynomialRealization schedule points identities.layer1)
      (by norm_num),
    exists_messages_with_exact_agreement (encoder2 schedule points) 63
      (encoder2PolynomialRealization schedule points identities.layer2)
      (by norm_num),
    exists_messages_with_exact_agreement (encoder3 schedule points) 15
      (encoder3PolynomialRealization schedule points identities.layer3)
      (by norm_num)⟩

end LineEncoders

/-! ## Axiom audit -/

#print axioms agreementSet_card_le_of_polynomialEvaluation
#print axioms exists_messages_with_exact_agreement
#print axioms PolynomialEvaluationRealization.bijective_toBoundedPolynomial
#print axioms naturalCoefficientPolynomial_complete
#print axioms naturalCoefficientPolynomial_eval_radix4
#print axioms radix4LiftEncoder_eq_natural_eval
#print axioms finalTensorPolynomial_eval
#print axioms finalTensorPolynomial_injective
#print axioms concreteLineEvaluationIdentities_of_geometry
#print axioms encoder1_messagePolynomial_bijective
#print axioms encoder2_messagePolynomial_bijective
#print axioms encoder3_messagePolynomial_bijective
#print axioms encoder4_messagePolynomial_bijective
#print axioms encoder1_agreement_card_le_255
#print axioms encoder2_agreement_card_le_63
#print axioms encoder3_agreement_card_le_15
#print axioms encoder4_agreement_card_le_three
#print axioms encoder4_injective_of_distinct
#print axioms concrete_line_encoder_distances
#print axioms encoder4_exists_exact_agreement_three
#print axioms concrete_line_encoder_exact_overlap_witnesses

end AspisV5FriConcreteEncoderApplicability
