import AspisFormal.Pool.V7DeployedCopyLogUpAliasClosure
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Wronskian

set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

namespace AspisPool.V7DeployedCopyLogUpCollisionBounds

noncomputable section

open Polynomial
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisV5ComponentCQM31TowerExact

/-! ## Generic small-characteristic Wronskian facts -/

/-- Below the characteristic, a zero derivative forces a polynomial to be
constant.  This is the exact positive-characteristic guard needed by the
183-link LogUp argument. -/
theorem natDegree_eq_zero_of_derivative_eq_zero_of_lt_char
    {K : Type*} [Field K]
    {f : K[X]} (derivativeZero : f.derivative = 0)
    (smallNatCasts : ∀ n : Nat, 0 < n → n ≤ f.natDegree → (n : K) ≠ 0) :
    f.natDegree = 0 := by
  by_contra degreeNonzero
  have degreePositive : 0 < f.natDegree := Nat.pos_of_ne_zero degreeNonzero
  have coefficientZero := congrArg
    (fun polynomial : K[X] => polynomial.coeff (f.natDegree - 1))
    derivativeZero
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at coefficientZero
  have predecessor : f.natDegree - 1 + 1 = f.natDegree := by omega
  rw [predecessor] at coefficientZero
  have castPredecessor :
      ((f.natDegree - 1 : Nat) : K) + 1 = (f.natDegree : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun value : Nat => (value : K)) predecessor
  rw [castPredecessor] at coefficientZero
  change f.leadingCoeff * (f.natDegree : K) = 0 at coefficientZero
  have castNonzero : (f.natDegree : K) ≠ 0 :=
    smallNatCasts f.natDegree degreePositive le_rfl
  have polynomialNonzero : f ≠ 0 := by
    intro polynomialZero
    apply degreeNonzero
    rw [polynomialZero]
    rfl
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
    polynomialNonzero) castNonzero)
    coefficientZero

/-- Two distinct monic polynomials of the same degree below the
characteristic have a nonzero Wronskian.  The proof cancels their gcd and uses
the kernel characterization of a coprime zero-Wronskian pair. -/
theorem wronskian_ne_zero_of_distinct_monic_same_small_degree
    {K : Type*} [Field K] [DecidableEq K]
    {p q : K[X]} (pMonic : p.Monic) (qMonic : q.Monic)
    (sameDegree : p.natDegree = q.natDegree)
    (smallNatCasts : ∀ n : Nat, 0 < n → n ≤ p.natDegree → (n : K) ≠ 0)
    (different : p ≠ q) :
    p.wronskian q ≠ 0 := by
  intro wronskianZero
  let g : K[X] := GCDMonoid.gcd p q
  let a : K[X] := p / g
  let b : K[X] := q / g
  have pNonzero : p ≠ 0 := pMonic.ne_zero
  have qNonzero : q ≠ 0 := qMonic.ne_zero
  have gNonzero : g ≠ 0 := gcd_ne_zero_of_right qNonzero
  have gp : g ∣ p := GCDMonoid.gcd_dvd_left p q
  have gq : g ∣ q := GCDMonoid.gcd_dvd_right p q
  have pFactor : g * a = p := EuclideanDomain.mul_div_cancel' gNonzero gp
  have qFactor : g * b = q := EuclideanDomain.mul_div_cancel' gNonzero gq
  have aNonzero : a ≠ 0 := left_div_gcd_ne_zero pNonzero
  have bNonzero : b ≠ 0 := right_div_gcd_ne_zero qNonzero
  have reducedCoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd qNonzero
  have reducedWronskianZero : a.wronskian b = 0 := by
    have factored : p.wronskian q = g ^ 2 * a.wronskian b := by
      rw [← pFactor, ← qFactor]
      simp only [Polynomial.wronskian, Polynomial.derivative_mul]
      ring
    rw [factored] at wronskianZero
    exact (mul_eq_zero.mp wronskianZero).resolve_left (pow_ne_zero 2 gNonzero)
  have derivativeZeros : a.derivative = 0 ∧ b.derivative = 0 :=
    reducedCoprime.wronskian_eq_zero_iff.mp reducedWronskianZero
  have aDvdP : a ∣ p := ⟨g, by simpa [mul_comm] using pFactor.symm⟩
  have bDvdQ : b ∣ q := ⟨g, by simpa [mul_comm] using qFactor.symm⟩
  have aDegreeBound : a.natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd aDvdP pNonzero
  have bDegreeBound : b.natDegree ≤ p.natDegree := by
    rw [sameDegree]
    exact Polynomial.natDegree_le_of_dvd bDvdQ qNonzero
  have aDegreeZero :=
    natDegree_eq_zero_of_derivative_eq_zero_of_lt_char derivativeZeros.1
      (fun n positive bounded =>
        smallNatCasts n positive (bounded.trans aDegreeBound))
  have bDegreeZero :=
    natDegree_eq_zero_of_derivative_eq_zero_of_lt_char derivativeZeros.2
      (fun n positive bounded =>
        smallNatCasts n positive (bounded.trans bDegreeBound))
  have aUnit : IsUnit a := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    rw [Polynomial.degree_eq_natDegree aNonzero, aDegreeZero]
    rfl
  have bUnit : IsUnit b := by
    rw [Polynomial.isUnit_iff_degree_eq_zero]
    rw [Polynomial.degree_eq_natDegree bNonzero, bDegreeZero]
    rfl
  have pDvdQ : p ∣ q := by
    rw [← pFactor, ← qFactor]
    exact mul_dvd_mul_left g (aUnit.dvd)
  have qDvdP : q ∣ p := by
    rw [← pFactor, ← qFactor]
    exact mul_dvd_mul_left g (bUnit.dvd)
  exact different (Polynomial.eq_of_monic_of_associated pMonic qMonic
    (associated_of_dvd_dvd pDvdQ qDvdP))

/-! ## Characteristic polynomials for the two 183-element multisets -/

noncomputable def multisetCharacteristicPolynomial
    {K : Type*} [CommRing K] (values : Multiset K) : K[X] :=
  (values.map fun value => X - C value).prod

@[simp] theorem multisetCharacteristicPolynomial_roots
    {K : Type*} [CommRing K] [IsDomain K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).roots = values := by
  exact Polynomial.roots_multiset_prod_X_sub_C values

theorem multisetCharacteristicPolynomial_monic
    {K : Type*} [CommRing K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).Monic := by
  exact Polynomial.monic_multisetProd_X_sub_C values

@[simp] theorem multisetCharacteristicPolynomial_natDegree
    {K : Type*} [CommRing K] [Nontrivial K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).natDegree = values.card := by
  exact Polynomial.natDegree_multiset_prod_X_sub_C_eq_card values

theorem multisetCharacteristicPolynomial_injective
    {K : Type*} [CommRing K] [IsDomain K] :
    Function.Injective (multisetCharacteristicPolynomial (K := K)) := by
  intro left right equal
  rw [← multisetCharacteristicPolynomial_roots left,
    ← multisetCharacteristicPolynomial_roots right, equal]

theorem multisetCharacteristicPolynomial_splits
    {K : Type*} [Field K] (values : Multiset K) :
    (multisetCharacteristicPolynomial values).Splits := by
  rw [Polynomial.splits_iff_card_roots,
    multisetCharacteristicPolynomial_roots,
    multisetCharacteristicPolynomial_natDegree]

theorem eval_multisetCharacteristicPolynomial_ne_zero
    {K : Type*} [Field K] (values : Multiset K) (challenge : K)
    (notPole : challenge ∉ values) :
    (multisetCharacteristicPolynomial values).eval challenge ≠ 0 := by
  rw [multisetCharacteristicPolynomial, Polynomial.eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply]
  apply Multiset.prod_ne_zero
  intro zeroMember
  simp only [Multiset.mem_map] at zeroMember
  obtain ⟨value, valueMember, factorZero⟩ := zeroMember
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at factorZero
  have challengeEqual : challenge = value := sub_eq_zero.mp factorZero
  exact notPole (challengeEqual.symm ▸ valueMember)

/-- Away from the explicitly listed poles, the characteristic polynomial's
logarithmic derivative is the exact multiset sum used by LogUp. -/
theorem eval_derivative_div_eval_multisetCharacteristicPolynomial
    {K : Type*} [Field K] (values : Multiset K) (challenge : K)
    (notPole : challenge ∉ values) :
    (multisetCharacteristicPolynomial values).derivative.eval challenge /
        (multisetCharacteristicPolynomial values).eval challenge =
      (values.map fun value => (challenge - value)⁻¹).sum := by
  have split := multisetCharacteristicPolynomial_splits values
  have nonzero :=
    eval_multisetCharacteristicPolynomial_ne_zero values challenge notPole
  simpa [multisetCharacteristicPolynomial_roots, one_div] using
    split.eval_derivative_div_eval_of_ne_zero nonzero

/-! ## Fixed-`lambda` chi collision polynomial -/

noncomputable def producerChiPolynomial
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) : K[X] :=
  multisetCharacteristicPolynomial (producerCompressedMultiset source lambda)

noncomputable def consumerChiPolynomial
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) : K[X] :=
  multisetCharacteristicPolynomial (consumerCompressedMultiset source lambda)

noncomputable def copyChiWronskian
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) : K[X] :=
  (producerChiPolynomial source lambda).wronskian
    (consumerChiPolynomial source lambda)

@[simp] theorem producerCompressedMultiset_card
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) :
    (producerCompressedMultiset source lambda).card = 183 := by
  simp [producerCompressedMultiset, deployedCopyLink_card]

@[simp] theorem consumerCompressedMultiset_card
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) :
    (consumerCompressedMultiset source lambda).card = 183 := by
  simp [consumerCompressedMultiset, deployedCopyLink_card]

@[simp] theorem producerChiPolynomial_natDegree
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) :
    (producerChiPolynomial source lambda).natDegree = 183 := by
  simp [producerChiPolynomial]

@[simp] theorem consumerChiPolynomial_natDegree
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda : K) :
    (consumerChiPolynomial source lambda).natDegree = 183 := by
  simp [consumerChiPolynomial]

theorem copyChiWronskian_ne_zero
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact)
    (different : producerCompressedMultiset source lambda ≠
      consumerCompressedMultiset source lambda) :
    copyChiWronskian source lambda ≠ 0 := by
  apply wronskian_ne_zero_of_distinct_monic_same_small_degree
    (multisetCharacteristicPolynomial_monic _)
    (multisetCharacteristicPolynomial_monic _)
  · simp
  · intro n positive bounded
    rw [multisetCharacteristicPolynomial_natDegree,
      producerCompressedMultiset_card] at bounded
    have nSmall : n < P := by
      exact bounded.trans_lt (by norm_num [P])
    have baseNonzero : (n : M31Exact) ≠ 0 := by
      intro castZero
      have divides := (CharP.cast_eq_zero_iff M31Exact P n).mp castZero
      exact (Nat.not_dvd_of_pos_of_lt positive nSmall) divides
    intro towerZero
    apply baseNonzero
    apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
    calc
      algebraMap M31Exact QM31Exact (n : M31Exact) =
          (n : QM31Exact) := map_natCast _ n
      _ = 0 := towerZero
      _ = algebraMap M31Exact QM31Exact (0 : M31Exact) :=
        (map_zero _).symm
  · intro equal
    apply different
    exact multisetCharacteristicPolynomial_injective equal

noncomputable def multisetRationalBalance
    {K : Type*} [Field K] (producer consumer : Multiset K)
    (chi : K) : K :=
  (producer.map fun value => (chi - value)⁻¹).sum -
    (consumer.map fun value => (chi - value)⁻¹).sum

theorem copyRationalBalance_eq_multisetRationalBalance
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) :
    copyRationalBalance source lambda chi =
      multisetRationalBalance
        (producerCompressedMultiset source lambda)
        (consumerCompressedMultiset source lambda) chi := by
  simp [copyRationalBalance, multisetRationalBalance,
    producerCompressedMultiset, consumerCompressedMultiset]

/-- A zero deployed rational balance away from all totalized-inverse poles is
a root of the exact Wronskian polynomial. -/
theorem copyChiWronskian_eval_eq_zero_of_balance_of_not_pole
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K)
    (balance : copyRationalBalance source lambda chi = 0)
    (producerNotPole : chi ∉ producerCompressedMultiset source lambda)
    (consumerNotPole : chi ∉ consumerCompressedMultiset source lambda) :
    (copyChiWronskian source lambda).eval chi = 0 := by
  let producer := producerCompressedMultiset source lambda
  let consumer := consumerCompressedMultiset source lambda
  let p := producerChiPolynomial source lambda
  let q := consumerChiPolynomial source lambda
  have pNonzero : p.eval chi ≠ 0 := by
    exact eval_multisetCharacteristicPolynomial_ne_zero producer chi
      producerNotPole
  have qNonzero : q.eval chi ≠ 0 := by
    exact eval_multisetCharacteristicPolynomial_ne_zero consumer chi
      consumerNotPole
  have producerLog :=
    eval_derivative_div_eval_multisetCharacteristicPolynomial producer chi
      producerNotPole
  have consumerLog :=
    eval_derivative_div_eval_multisetCharacteristicPolynomial consumer chi
      consumerNotPole
  have sumEqual :
      (producer.map fun value => (chi - value)⁻¹).sum =
        (consumer.map fun value => (chi - value)⁻¹).sum := by
    rw [copyRationalBalance_eq_multisetRationalBalance source lambda chi,
      multisetRationalBalance, sub_eq_zero] at balance
    exact balance
  have ratioEqual : p.derivative.eval chi / p.eval chi =
      q.derivative.eval chi / q.eval chi := by
    calc
      p.derivative.eval chi / p.eval chi =
          (producer.map fun value => (chi - value)⁻¹).sum := by
        simpa [p, producer, producerChiPolynomial] using producerLog
      _ = (consumer.map fun value => (chi - value)⁻¹).sum := sumEqual
      _ = q.derivative.eval chi / q.eval chi := by
        simpa [q, consumer, consumerChiPolynomial] using consumerLog.symm
  have crossEqual : p.derivative.eval chi * q.eval chi =
      q.derivative.eval chi * p.eval chi :=
    (div_eq_div_iff pNonzero qNonzero).mp ratioEqual
  simp only [copyChiWronskian, Polynomial.wronskian,
    Polynomial.eval_sub, Polynomial.eval_mul]
  rw [show producerChiPolynomial source lambda = p by rfl,
    show consumerChiPolynomial source lambda = q by rfl]
  rw [mul_comm (p.eval chi) (q.derivative.eval chi), crossEqual, sub_self]

section FiniteChi

variable [Fintype QM31Exact]

noncomputable def copyChiPoleSet
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) : Finset QM31Exact := by
  classical
  exact Finset.univ.filter fun chi =>
    chi ∈ producerCompressedMultiset source lambda ∨
      chi ∈ consumerCompressedMultiset source lambda

noncomputable def copyChiNonPoleCollisionSet
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) : Finset QM31Exact := by
  classical
  exact Finset.univ.filter fun chi =>
    CopyChiCollision source lambda chi ∧
      chi ∉ producerCompressedMultiset source lambda ∧
      chi ∉ consumerCompressedMultiset source lambda

noncomputable def copyChiCollisionSet
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) : Finset QM31Exact := by
  classical
  exact Finset.univ.filter fun chi => CopyChiCollision source lambda chi

/-- There are at most `183 + 183 = 366` distinct producer/consumer poles.
This theorem is kept separate so the effect of totalized inversion is visible
in the final accounting. -/
theorem copyChiPoleSet_card_le_366
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (copyChiPoleSet source lambda).card ≤ 366 := by
  have subset : copyChiPoleSet source lambda ⊆
      (producerCompressedMultiset source lambda).toFinset ∪
        (consumerCompressedMultiset source lambda).toFinset := by
    intro chi member
    simp only [copyChiPoleSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at member
    simpa using member
  calc
    (copyChiPoleSet source lambda).card ≤
        ((producerCompressedMultiset source lambda).toFinset ∪
          (consumerCompressedMultiset source lambda).toFinset).card :=
      Finset.card_le_card subset
    _ ≤ (producerCompressedMultiset source lambda).toFinset.card +
        (consumerCompressedMultiset source lambda).toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ (producerCompressedMultiset source lambda).card +
        (consumerCompressedMultiset source lambda).card :=
      Nat.add_le_add (Multiset.toFinset_card_le _) (Multiset.toFinset_card_le _)
    _ = 366 := by simp

/-- Outside poles, a false fixed multiset equality can pass for at most 365
values of `chi`, the strict Wronskian degree bound `2*183-1`. -/
theorem copyChiNonPoleCollisionSet_card_le_365
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (copyChiNonPoleCollisionSet source lambda).card ≤ 365 := by
  by_cases different : producerCompressedMultiset source lambda ≠
      consumerCompressedMultiset source lambda
  · have witnessNonzero := copyChiWronskian_ne_zero source lambda different
    have subset : (copyChiNonPoleCollisionSet source lambda).val ⊆
        (copyChiWronskian source lambda).roots := by
      intro chi member
      have memberFinset : chi ∈ copyChiNonPoleCollisionSet source lambda := by
        simpa using member
      simp only [copyChiNonPoleCollisionSet, Finset.mem_filter,
        Finset.mem_univ, true_and] at memberFinset
      rw [Polynomial.mem_roots witnessNonzero]
      exact copyChiWronskian_eval_eq_zero_of_balance_of_not_pole source
        lambda chi memberFinset.1.1 memberFinset.2.1 memberFinset.2.2
    exact (Polynomial.card_le_degree_of_subset_roots subset).trans
      (Nat.le_of_lt_succ (by
        simpa [copyChiWronskian] using
          Polynomial.natDegree_wronskian_lt_add witnessNonzero))
  · have equal := not_ne_iff.mp different
    have emptySet : copyChiNonPoleCollisionSet source lambda = ∅ := by
      ext chi
      simp only [copyChiNonPoleCollisionSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro collision
      exact collision.1.2 equal
    rw [emptySet]
    norm_num

theorem copyChiCollisionSet_subset_nonPole_union_poles
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    copyChiCollisionSet source lambda ⊆
      copyChiNonPoleCollisionSet source lambda ∪ copyChiPoleSet source lambda := by
  intro chi member
  simp only [copyChiCollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at member
  by_cases producerPole : chi ∈ producerCompressedMultiset source lambda
  · simp [copyChiPoleSet, producerPole]
  by_cases consumerPole : chi ∈ consumerCompressedMultiset source lambda
  · simp [copyChiPoleSet, consumerPole]
  simp [copyChiNonPoleCollisionSet, member, producerPole, consumerPole]

/-- Complete fixed-source chi bound for the deployed 183-link registry under
the field's totalized inverse semantics: 365 non-pole Wronskian roots plus at
most 366 explicit poles. -/
theorem copyChiCollisionSet_card_le_731
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (copyChiCollisionSet source lambda).card ≤ 731 := by
  calc
    (copyChiCollisionSet source lambda).card ≤
        (copyChiNonPoleCollisionSet source lambda ∪
          copyChiPoleSet source lambda).card :=
      Finset.card_le_card
        (copyChiCollisionSet_subset_nonPole_union_poles source lambda)
    _ ≤ (copyChiNonPoleCollisionSet source lambda).card +
        (copyChiPoleSet source lambda).card := Finset.card_union_le _ _
    _ ≤ 365 + 366 := Nat.add_le_add
      (copyChiNonPoleCollisionSet_card_le_365 source lambda)
      (copyChiPoleSet_card_le_366 source lambda)
    _ = 731 := by norm_num

end FiniteChi

/-! ## Fixed-source lambda collision polynomial -/

/-- The deployed 16-limb compression regarded as a polynomial in `lambda`. -/
noncomputable def tupleCompressionPolynomial
    {K : Type*} [Field K] (tuple : TaggedCopyTuple K) : K[X] :=
  C (tuple.tag : K) + ∑ limb : Fin 16,
    C (tuple.limbs limb) * X ^ (limb.val + 1)

@[simp] theorem eval_tupleCompressionPolynomial
    {K : Type*} [Field K] (tuple : TaggedCopyTuple K) (lambda : K) :
    (tupleCompressionPolynomial tuple).eval lambda =
      compressTaggedTuple lambda tuple := by
  unfold tupleCompressionPolynomial compressTaggedTuple
  rw [Polynomial.eval_add, Polynomial.eval_C]
  change (tuple.tag : K) +
      (Polynomial.evalRingHom lambda) (∑ limb : Fin 16,
        C (tuple.limbs limb) * X ^ (limb.val + 1)) = _
  rw [map_sum]
  simp only [map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    map_pow, Polynomial.eval_X]
  congr 1
  apply Finset.sum_congr rfl
  intro limb _
  rw [mul_comm]

theorem tupleCompressionPolynomial_natDegree_le_16
    {K : Type*} [Field K] (tuple : TaggedCopyTuple K) :
    (tupleCompressionPolynomial tuple).natDegree ≤ 16 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · rw [Polynomial.natDegree_C]
    omega
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro limb _
    exact (Polynomial.natDegree_C_mul_X_pow_le
      (tuple.limbs limb) (limb.val + 1)).trans (by omega)

@[simp] theorem tupleCompressionPolynomial_coeff_zero
    {K : Type*} [Field K] (tuple : TaggedCopyTuple K) :
    (tupleCompressionPolynomial tuple).coeff 0 = (tuple.tag : K) := by
  simp [tupleCompressionPolynomial]

@[simp] theorem tupleCompressionPolynomial_coeff_limb
    {K : Type*} [Field K] (tuple : TaggedCopyTuple K) (limb : Fin 16) :
    (tupleCompressionPolynomial tuple).coeff (limb.val + 1) =
      tuple.limbs limb := by
  classical
  rw [tupleCompressionPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C]
  rw [if_neg (by omega), zero_add, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single limb]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro other _ different
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro sameExponent
    apply different
    apply Fin.ext
    omega
  · simp

/-- Injectivity on the actual deployed tag range.  The explicit tag-cast
hypothesis is necessary over a finite field; it will be discharged below from
all registry tags being strictly below `P`. -/
theorem tupleCompressionPolynomial_eq_implies_tuple_eq
    {K : Type*} [Field K] {left right : TaggedCopyTuple K}
    (tagCastInjective : (left.tag : K) = (right.tag : K) →
      left.tag = right.tag)
    (equal : tupleCompressionPolynomial left =
      tupleCompressionPolynomial right) :
    left = right := by
  cases left with
  | mk leftTag leftLimbs =>
      cases right with
      | mk rightTag rightLimbs =>
          congr
          · apply tagCastInjective
            simpa only [tupleCompressionPolynomial_coeff_zero] using
              congrArg (fun polynomial : K[X] => polynomial.coeff 0) equal
          · funext limb
            simpa only [tupleCompressionPolynomial_coeff_limb] using
              congrArg
                (fun polynomial : K[X] => polynomial.coeff (limb.val + 1)) equal

theorem deployedCopyTag_lt_P (link : DeployedCopyLink) :
    deployedCopyTag link < P := by
  cases link with
  | retained index =>
      simp [deployedCopyTag, P]
      omega
  | pathCurrent level output =>
      cases output <;> simp [deployedCopyTag, P] <;> omega
  | pathSelect level output item =>
      cases output <;> simp [deployedCopyTag, P] <;> omega
  | pathAlias level hop =>
      simp [deployedCopyTag, P]
      omega

theorem qm31Exact_natCast_injective_below_P
    {left right : Nat} (leftSmall : left < P) (rightSmall : right < P)
    (equal : (left : QM31Exact) = (right : QM31Exact)) :
    left = right := by
  have baseEqual : (left : M31Exact) = (right : M31Exact) := by
    apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
    calc
      algebraMap M31Exact QM31Exact (left : M31Exact) =
          (left : QM31Exact) := map_natCast _ left
      _ = (right : QM31Exact) := equal
      _ = algebraMap M31Exact QM31Exact (right : M31Exact) :=
        (map_natCast _ right).symm
  exact CharP.natCast_injOn_Iio M31Exact P leftSmall rightSmall baseEqual

abbrev SmallDeployedTaggedTuple :=
  { tuple : TaggedCopyTuple QM31Exact // tuple.tag < P }

noncomputable def producerSmallTaggedMultiset
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : Multiset SmallDeployedTaggedTuple :=
  (Finset.univ : Finset DeployedCopyLink).1.map fun link =>
    ⟨source.producer link, by
      rw [source.producerTag link]
      exact deployedCopyTag_lt_P link⟩

noncomputable def consumerSmallTaggedMultiset
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : Multiset SmallDeployedTaggedTuple :=
  (Finset.univ : Finset DeployedCopyLink).1.map fun link =>
    ⟨source.consumer link, by
      rw [source.consumerTag link]
      exact deployedCopyTag_lt_P link⟩

def smallTupleCompressionPolynomial
    (tuple : SmallDeployedTaggedTuple) : QM31Exact[X] :=
  tupleCompressionPolynomial tuple.1

theorem smallTupleCompressionPolynomial_injective :
    Function.Injective smallTupleCompressionPolynomial := by
  intro left right equal
  apply Subtype.ext
  exact tupleCompressionPolynomial_eq_implies_tuple_eq
    (fun castEqual => qm31Exact_natCast_injective_below_P
      left.2 right.2 castEqual) equal

theorem producerSmallTaggedMultiset_map_value
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (producerSmallTaggedMultiset source).map Subtype.val =
      producerTaggedMultiset source := by
  simp [producerSmallTaggedMultiset, producerTaggedMultiset]

theorem consumerSmallTaggedMultiset_map_value
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (consumerSmallTaggedMultiset source).map Subtype.val =
      consumerTaggedMultiset source := by
  simp [consumerSmallTaggedMultiset, consumerTaggedMultiset]

noncomputable def producerTuplePolynomialMultiset
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : Multiset QM31Exact[X] :=
  (producerSmallTaggedMultiset source).map smallTupleCompressionPolynomial

noncomputable def consumerTuplePolynomialMultiset
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : Multiset QM31Exact[X] :=
  (consumerSmallTaggedMultiset source).map smallTupleCompressionPolynomial

noncomputable def producerLambdaCharacteristic
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : QM31Exact[X][X] :=
  multisetCharacteristicPolynomial (producerTuplePolynomialMultiset source)

noncomputable def consumerLambdaCharacteristic
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : QM31Exact[X][X] :=
  multisetCharacteristicPolynomial (consumerTuplePolynomialMultiset source)

noncomputable def copyLambdaCharacteristicDifference
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : QM31Exact[X][X] :=
  producerLambdaCharacteristic source - consumerLambdaCharacteristic source

noncomputable def copyLambdaWitnessPolynomial
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : QM31Exact[X] :=
  (copyLambdaCharacteristicDifference source).leadingCoeff

theorem map_multisetCharacteristicPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (values : Multiset R) :
    (multisetCharacteristicPolynomial values).map hom =
      multisetCharacteristicPolynomial (values.map hom) := by
  simp [multisetCharacteristicPolynomial, Polynomial.map_multiset_prod]

/-- Every coefficient of a characteristic polynomial built from degree-`d`
roots has degree at most `d * card`.  This is the non-factorial core of the
lambda analysis. -/
theorem multisetCharacteristicPolynomial_coeff_natDegree_le
    {K : Type*} [Field K] (values : Multiset K[X]) (degreeBound : Nat)
    (bounded : ∀ value ∈ values, value.natDegree ≤ degreeBound)
    (coefficient : Nat) :
    ((multisetCharacteristicPolynomial values).coeff coefficient).natDegree ≤
      degreeBound * values.card := by
  induction values using Multiset.induction_on generalizing coefficient with
  | empty =>
      rw [multisetCharacteristicPolynomial]
      simp only [Multiset.map_zero, Multiset.prod_zero]
      by_cases coefficientZero : coefficient = 0
      · subst coefficient
        simp
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        · rfl
        · simp
          omega
  | @cons value rest induction =>
      have valueBound : value.natDegree ≤ degreeBound :=
        bounded value (by simp)
      have restBound : ∀ other ∈ rest, other.natDegree ≤ degreeBound := by
        intro other member
        exact bounded other (Multiset.mem_cons_of_mem member)
      rw [multisetCharacteristicPolynomial, Multiset.map_cons,
        Multiset.prod_cons, Polynomial.coeff_mul]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro pair _
      refine Polynomial.natDegree_mul_le.trans ?_
      have factorBound :
          (((X - C value : K[X][X]).coeff pair.1).natDegree ≤
            degreeBound) := by
        rcases pair.1 with _ | index
        · simpa using valueBound
        · rcases index with _ | index
          · simp
          · rw [Polynomial.coeff_sub, Polynomial.coeff_X,
              Polynomial.coeff_C]
            simp
      have restCoefficientBound :
          ((multisetCharacteristicPolynomial rest).coeff pair.2).natDegree ≤
            degreeBound * rest.card :=
        induction restBound pair.2
      calc
        ((X - C value : K[X][X]).coeff pair.1).natDegree +
            ((multisetCharacteristicPolynomial rest).coeff pair.2).natDegree ≤
          degreeBound + degreeBound * rest.card :=
            Nat.add_le_add factorBound restCoefficientBound
        _ = degreeBound * (value ::ₘ rest).card := by
          simp
          ring

@[simp] theorem producerSmallTaggedMultiset_card
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (producerSmallTaggedMultiset source).card = 183 := by
  simp [producerSmallTaggedMultiset, deployedCopyLink_card]

@[simp] theorem consumerSmallTaggedMultiset_card
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (consumerSmallTaggedMultiset source).card = 183 := by
  simp [consumerSmallTaggedMultiset, deployedCopyLink_card]

@[simp] theorem producerTuplePolynomialMultiset_card
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (producerTuplePolynomialMultiset source).card = 183 := by
  simp [producerTuplePolynomialMultiset]

@[simp] theorem consumerTuplePolynomialMultiset_card
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (consumerTuplePolynomialMultiset source).card = 183 := by
  simp [consumerTuplePolynomialMultiset]

theorem copyLambdaCharacteristicDifference_ne_zero
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (different : producerTaggedMultiset source ≠
      consumerTaggedMultiset source) :
    copyLambdaCharacteristicDifference source ≠ 0 := by
  intro differenceZero
  have characteristicEqual : producerLambdaCharacteristic source =
      consumerLambdaCharacteristic source := sub_eq_zero.mp differenceZero
  have polynomialMultisetsEqual : producerTuplePolynomialMultiset source =
      consumerTuplePolynomialMultiset source :=
    multisetCharacteristicPolynomial_injective characteristicEqual
  have smallMultisetsEqual : producerSmallTaggedMultiset source =
      consumerSmallTaggedMultiset source := by
    exact (Multiset.map_eq_map smallTupleCompressionPolynomial_injective).mp
      polynomialMultisetsEqual
  apply different
  rw [← producerSmallTaggedMultiset_map_value source,
    ← consumerSmallTaggedMultiset_map_value source, smallMultisetsEqual]

theorem copyLambdaWitnessPolynomial_ne_zero
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (different : producerTaggedMultiset source ≠
      consumerTaggedMultiset source) :
    copyLambdaWitnessPolynomial source ≠ 0 := by
  exact Polynomial.leadingCoeff_ne_zero.mpr
    (copyLambdaCharacteristicDifference_ne_zero source different)

theorem copyLambdaWitnessPolynomial_natDegree_le_2928
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (copyLambdaWitnessPolynomial source).natDegree ≤ 2928 := by
  let difference := copyLambdaCharacteristicDifference source
  have producerBound :
      ((producerLambdaCharacteristic source).coeff difference.natDegree).natDegree ≤
        2928 := by
    have allBound : ∀ polynomial ∈ producerTuplePolynomialMultiset source,
        polynomial.natDegree ≤ 16 := by
      intro polynomial member
      simp only [producerTuplePolynomialMultiset, Multiset.mem_map] at member
      obtain ⟨tuple, _, rfl⟩ := member
      exact tupleCompressionPolynomial_natDegree_le_16 tuple.1
    calc
      ((producerLambdaCharacteristic source).coeff difference.natDegree).natDegree ≤
          16 * (producerTuplePolynomialMultiset source).card :=
        multisetCharacteristicPolynomial_coeff_natDegree_le
          (producerTuplePolynomialMultiset source) 16 allBound
          difference.natDegree
      _ = 2928 := by simp
  have consumerBound :
      ((consumerLambdaCharacteristic source).coeff difference.natDegree).natDegree ≤
        2928 := by
    have allBound : ∀ polynomial ∈ consumerTuplePolynomialMultiset source,
        polynomial.natDegree ≤ 16 := by
      intro polynomial member
      simp only [consumerTuplePolynomialMultiset, Multiset.mem_map] at member
      obtain ⟨tuple, _, rfl⟩ := member
      exact tupleCompressionPolynomial_natDegree_le_16 tuple.1
    calc
      ((consumerLambdaCharacteristic source).coeff difference.natDegree).natDegree ≤
          16 * (consumerTuplePolynomialMultiset source).card :=
        multisetCharacteristicPolynomial_coeff_natDegree_le
          (consumerTuplePolynomialMultiset source) 16 allBound
          difference.natDegree
      _ = 2928 := by simp
  change (difference.leadingCoeff).natDegree ≤ 2928
  rw [Polynomial.leadingCoeff, show difference.natDegree = difference.natDegree by rfl]
  change ((producerLambdaCharacteristic source -
    consumerLambdaCharacteristic source).coeff difference.natDegree).natDegree ≤ 2928
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le producerBound consumerBound)

theorem producerTuplePolynomialMultiset_map_eval
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (producerTuplePolynomialMultiset source).map
        (Polynomial.evalRingHom lambda) =
      producerCompressedMultiset source lambda := by
  simp [producerTuplePolynomialMultiset, producerSmallTaggedMultiset,
    producerCompressedMultiset, smallTupleCompressionPolynomial,
    Polynomial.coe_evalRingHom]

theorem consumerTuplePolynomialMultiset_map_eval
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (consumerTuplePolynomialMultiset source).map
        (Polynomial.evalRingHom lambda) =
      consumerCompressedMultiset source lambda := by
  simp [consumerTuplePolynomialMultiset, consumerSmallTaggedMultiset,
    consumerCompressedMultiset, smallTupleCompressionPolynomial,
    Polynomial.coe_evalRingHom]

theorem map_producerLambdaCharacteristic
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (producerLambdaCharacteristic source).map
        (Polynomial.evalRingHom lambda) =
      multisetCharacteristicPolynomial
        (producerCompressedMultiset source lambda) := by
  rw [producerLambdaCharacteristic,
    map_multisetCharacteristicPolynomial,
    producerTuplePolynomialMultiset_map_eval]

theorem map_consumerLambdaCharacteristic
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact) :
    (consumerLambdaCharacteristic source).map
        (Polynomial.evalRingHom lambda) =
      multisetCharacteristicPolynomial
        (consumerCompressedMultiset source lambda) := by
  rw [consumerLambdaCharacteristic,
    map_multisetCharacteristicPolynomial,
    consumerTuplePolynomialMultiset_map_eval]

/-- A deployed compression collision makes the selected nonzero coefficient
witness vanish at that exact `lambda`. -/
theorem copyLambdaWitnessPolynomial_eval_eq_zero_of_collision
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue)
    (lambda : QM31Exact)
    (collision : CopyTupleCompressionCollision source lambda) :
    (copyLambdaWitnessPolynomial source).eval lambda = 0 := by
  let difference := copyLambdaCharacteristicDifference source
  have mappedDifferenceZero : difference.map
      (Polynomial.evalRingHom lambda) = 0 := by
    change (copyLambdaCharacteristicDifference source).map
      (Polynomial.evalRingHom lambda) = 0
    rw [copyLambdaCharacteristicDifference,
      Polynomial.map_sub, map_producerLambdaCharacteristic,
      map_consumerLambdaCharacteristic, collision.1, sub_self]
  have coefficientZero := congrArg
    (fun polynomial : QM31Exact[X] => polynomial.coeff difference.natDegree)
    mappedDifferenceZero
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
    Polynomial.coe_evalRingHom, copyLambdaWitnessPolynomial,
    Polynomial.leadingCoeff] using coefficientZero

section FiniteLambda

noncomputable def copyLambdaCollisionSet
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) : Finset QM31Exact := by
  classical
  exact Finset.univ.filter fun lambda =>
    CopyTupleCompressionCollision source lambda

/-- Complete fixed-source lambda bound.  It uses one nonzero coefficient of
the characteristic polynomial over `QM31[lambda]`, of degree at most
`16 * 183 = 2928`; no permutation enumeration or factorial union appears. -/
theorem copyLambdaCollisionSet_card_le_2928
    {producerValue consumerValue : RequiredScalarLink → QM31Exact}
    (source : DeployedCopyRegistryProjection QM31Exact
      producerValue consumerValue) :
    (copyLambdaCollisionSet source).card ≤ 2928 := by
  by_cases different : producerTaggedMultiset source ≠
      consumerTaggedMultiset source
  · have witnessNonzero := copyLambdaWitnessPolynomial_ne_zero source different
    have subset : copyLambdaCollisionSet source ⊆
        (copyLambdaWitnessPolynomial source).roots.toFinset := by
      intro lambda member
      simp only [copyLambdaCollisionSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at member
      rw [Multiset.mem_toFinset, Polynomial.mem_roots witnessNonzero]
      exact copyLambdaWitnessPolynomial_eval_eq_zero_of_collision source
        lambda member
    calc
      (copyLambdaCollisionSet source).card ≤
          (copyLambdaWitnessPolynomial source).roots.toFinset.card :=
        Finset.card_le_card subset
      _ ≤ (copyLambdaWitnessPolynomial source).roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ (copyLambdaWitnessPolynomial source).natDegree :=
        Polynomial.card_roots' _
      _ ≤ 2928 := copyLambdaWitnessPolynomial_natDegree_le_2928 source
  · have equal := not_ne_iff.mp different
    have emptySet : copyLambdaCollisionSet source = ∅ := by
      ext lambda
      simp only [copyLambdaCollisionSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro collision
      exact collision.2 equal
    rw [emptySet]
    norm_num

end FiniteLambda

/-! ## Kernel audit -/

#print axioms natDegree_eq_zero_of_derivative_eq_zero_of_lt_char
#print axioms wronskian_ne_zero_of_distinct_monic_same_small_degree
#print axioms copyChiWronskian_ne_zero
#print axioms copyChiPoleSet_card_le_366
#print axioms copyChiNonPoleCollisionSet_card_le_365
#print axioms copyChiCollisionSet_card_le_731
#print axioms tupleCompressionPolynomial_eq_implies_tuple_eq
#print axioms copyLambdaCharacteristicDifference_ne_zero
#print axioms copyLambdaWitnessPolynomial_eval_eq_zero_of_collision
#print axioms copyLambdaCollisionSet_card_le_2928

end

end AspisPool.V7DeployedCopyLogUpCollisionBounds
