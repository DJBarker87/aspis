import Mathlib
import AspisFormal.CoreHidingPMF

/-!
# Sumcheck masking by a precommitted low-degree oracle

This file separates two facts that must not be conflated.

The first section models a finite vector `F : Fin n → K`, a uniformly random
vector `R` of the same dimension, and the challenge mixture

`Q = R + η F`.

This is the elementary additive self-reduction. Its distribution theorem only
applies when `R` is uniform over the *entire represented vector*. In particular,
a uniform 1024-value multilinear table does not mask the degree-2 through
degree-27 coefficients released by the Aspis sumcheck. No such application is
claimed here.

The second section models the actual degree-`d` round messages. A mask round is
a fresh uniform polynomial whose endpoint sum is zero, plus a constant carrier
equal to half the previous mask claim. The carrier makes consecutive rounds
chain, while the zero-boundary polynomial supplies all `d` free coefficients
of a degree-`d` message. The construction is globally consistent: recursively
summing its terminal values over the Boolean tree returns the initial mask
claim exactly.

The results below establish the following facts in the Lean kernel.

* If `F` sums to zero, then the joint distribution of `sum R` and any
  deterministic observation of `Q` is independent of `F`.
* If the honest mask-sum claim is used and `η ≠ 0`, acceptance of the mixed sum
  forces `F` to sum to zero.
* More generally, for fixed `F`, `R`, and a claimed sum, a false original sum
  can satisfy the mixed sum equation for at most one value of `η`.

For the degree-`d` construction, the kernel proves the conditional distribution
of each complete round message is independent of the real round polynomial,
given its visible incoming claim. It also proves that sampling the `d` tail
coefficients independently and solving for the constant coefficient is exactly
uniform over the zero-boundary subspace. Composition into the adaptive
Fiat--Shamir transcript, and the joint view containing the mask commitment root
and correlated PCS openings, remain named v5 wire obligations.
-/

open scoped BigOperators ENNReal

namespace AspisSumcheckMasking

variable {K : Type*} [Field K] {n : ℕ}

/-- Sum of a table over its finite index set. -/
def tableSum (f : Fin n → K) : K := ∑ i, f i

/-- The challenge mixture of a real summand and a precommitted mask oracle. -/
def maskedOracle (eta : K) (real mask : Fin n → K) : Fin n → K :=
  mask + eta • real

/-- The mixed table sums to `sum(mask) + eta * sum(real)`. -/
theorem tableSum_maskedOracle (eta : K) (real mask : Fin n → K) :
    tableSum (maskedOracle eta real mask)
      = tableSum mask + eta * tableSum real := by
  simp [tableSum, maskedOracle, Finset.sum_add_distrib, Finset.mul_sum]

/-- With the honest mask-sum claim and a nonzero challenge, an accepted mixed
sum implies that the original summand has sum zero. -/
theorem original_sum_eq_zero_of_mixed_sum
    (eta : K) (real mask : Fin n → K) (heta : eta ≠ 0)
    (hclaim : tableSum (maskedOracle eta real mask) = tableSum mask) :
    tableSum real = 0 := by
  rw [tableSum_maskedOracle] at hclaim
  have hzero : eta * tableSum real = 0 := by
    linear_combination hclaim
  exact (mul_eq_zero.mp hzero).resolve_left heta

/-- For fixed pre-challenge data, a false original sum can make the mixed sum
equal a claimed value for at most one challenge. -/
theorem accepting_challenge_unique
    (real mask : Fin n → K) (beta eta₁ eta₂ : K)
    (hreal : tableSum real ≠ 0)
    (h₁ : tableSum (maskedOracle eta₁ real mask) = beta)
    (h₂ : tableSum (maskedOracle eta₂ real mask) = beta) :
    eta₁ = eta₂ := by
  rw [tableSum_maskedOracle] at h₁ h₂
  have hzero : (eta₁ - eta₂) * tableSum real = 0 := by
    linear_combination h₁ - h₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hreal)

section Distribution

variable [Fintype K]

/-- A full uniform mask makes the entire mixed oracle independent of the real
summand. This is the identity-map instance of `CoreHidingPMF`. -/
theorem maskedOracle_pmf_indep
    (eta : K) (real₁ real₂ : Fin n → K) :
    (PMF.uniformOfFintype (Fin n → K)).map (fun mask => maskedOracle eta real₁ mask)
      = (PMF.uniformOfFintype (Fin n → K)).map
          (fun mask => maskedOracle eta real₂ mask) := by
  classical
  simpa [maskedOracle, add_comm] using
    (view_pmf_indep_of_witness (LinearMap.id)
      (Function.surjective_id : Function.Surjective (LinearMap.id :
        (Fin n → K) →ₗ[K] (Fin n → K)))
      (eta • real₁) (eta • real₂))

/-- Applying any deterministic transcript or observation function preserves
the witness-independent distribution. -/
theorem observed_maskedOracle_pmf_indep
    {View : Type*} (observe : (Fin n → K) → View)
    (eta : K) (real₁ real₂ : Fin n → K) :
    (PMF.uniformOfFintype (Fin n → K)).map
        (fun mask => observe (maskedOracle eta real₁ mask))
      = (PMF.uniformOfFintype (Fin n → K)).map
          (fun mask => observe (maskedOracle eta real₂ mask)) := by
  classical
  have h := congrArg (fun distribution : PMF (Fin n → K) => distribution.map observe)
    (maskedOracle_pmf_indep eta real₁ real₂)
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- The public mask-sum claim together with any deterministic transcript of the
mixed oracle is witness-independent when the real summand sums to zero.

For a valid summand, `sum(mask) = sum(mask + eta * real)`, so the whole pair is
a deterministic observation of the uniformly shifted mixed oracle. -/
theorem maskSum_and_observation_pmf_indep
    {View : Type*} (observe : (Fin n → K) → View)
    (eta : K) (real₁ real₂ : Fin n → K)
    (hreal₁ : tableSum real₁ = 0) (hreal₂ : tableSum real₂ = 0) :
    (PMF.uniformOfFintype (Fin n → K)).map
        (fun mask => (tableSum mask, observe (maskedOracle eta real₁ mask)))
      = (PMF.uniformOfFintype (Fin n → K)).map
          (fun mask => (tableSum mask, observe (maskedOracle eta real₂ mask))) := by
  classical
  let view : (Fin n → K) → K × View := fun mixed => (tableSum mixed, observe mixed)
  have h₁ : (fun mask => (tableSum mask, observe (maskedOracle eta real₁ mask)))
      = (fun mask => view (maskedOracle eta real₁ mask)) := by
    funext mask
    simp [view, tableSum_maskedOracle, hreal₁]
  have h₂ : (fun mask => (tableSum mask, observe (maskedOracle eta real₂ mask)))
      = (fun mask => view (maskedOracle eta real₂ mask)) := by
    funext mask
    simp [view, tableSum_maskedOracle, hreal₂]
  rw [h₁, h₂]
  exact observed_maskedOracle_pmf_indep view eta real₁ real₂

end Distribution

/-! ## Degree-preserving, chained round masks

The deployed state-only sumcheck sends a complete degree-27 polynomial in each
round. A multilinear mask has only one nonconstant coefficient and therefore
cannot hide that message. The construction below instead samples a fresh
degree-`d` polynomial in the kernel of `p ↦ p(0) + p(1)` for every round.

If the incoming mask claim is `s`, the released mask polynomial is
`s / 2 + p(X)`. Its endpoint sum is `s`, and evaluation at the round challenge
becomes the next mask claim. Thus the masks chain without the invalid step of
adding unrelated zero-sum polynomials directly to consecutive messages.
-/

section RoundTranscript

variable {d : ℕ}

/-- Coefficient vector of a univariate polynomial of degree at most `d`. -/
abbrev RoundCoeff (K : Type*) (d : ℕ) := Fin (d + 1) → K

/-- `p(0) + p(1)`, written directly in coefficients. -/
def roundBoundary (coeff : RoundCoeff K d) : K :=
  coeff 0 + ∑ i, coeff i

/-- The endpoint-sum functional as a linear map. -/
def roundBoundaryLinear : RoundCoeff K d →ₗ[K] K where
  toFun := roundBoundary
  map_add' := by
    intro a b
    simp only [Pi.add_apply, roundBoundary, Finset.sum_add_distrib]
    abel
  map_smul' := by
    intro scalar coeff
    simp only [Pi.smul_apply, smul_eq_mul, roundBoundary]
    change scalar * coeff 0 + ∑ x, scalar * coeff x =
      scalar * (coeff 0 + ∑ i, coeff i)
    rw [mul_add, Finset.mul_sum]

/-- Degree-`d` coefficient vectors with endpoint sum zero. -/
abbrev ZeroBoundaryCoeff (K : Type*) [Field K] (d : ℕ) :=
  LinearMap.ker (roundBoundaryLinear (K := K) (d := d))

noncomputable instance [Fintype K] : Fintype (ZeroBoundaryCoeff K d) :=
  Fintype.ofFinite _

instance : Nonempty (ZeroBoundaryCoeff K d) := ⟨0⟩

/-- Build a zero-boundary polynomial from its `d` freely sampled nonconstant
coefficients. The constant coefficient is forced to `-∑ tail / 2`. -/
def zeroBoundaryFromTail (h2 : (2 : K) ≠ 0) (tail : Fin d → K) :
    ZeroBoundaryCoeff K d :=
  ⟨Fin.cons (-(∑ i, tail i) / 2) tail, by
    change roundBoundary (Fin.cons (-(∑ i, tail i) / 2) tail) = 0
    simp [roundBoundary, Fin.sum_univ_succ]
    field_simp
    ring⟩

/-- Recover the freely sampled nonconstant coefficients. -/
def zeroBoundaryTail (coeff : ZeroBoundaryCoeff K d) : Fin d → K :=
  fun i => coeff.1 i.succ

theorem zeroBoundaryTail_fromTail (h2 : (2 : K) ≠ 0) (tail : Fin d → K) :
    zeroBoundaryTail (zeroBoundaryFromTail h2 tail) = tail := by
  funext i
  simp [zeroBoundaryTail, zeroBoundaryFromTail]

theorem zeroBoundaryFromTail_tail (h2 : (2 : K) ≠ 0)
    (coeff : ZeroBoundaryCoeff K d) :
    zeroBoundaryFromTail h2 (zeroBoundaryTail coeff) = coeff := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change -(∑ j : Fin d, coeff.1 j.succ) / 2 = coeff.1 0
    have hzero : coeff.1 0 + ∑ i, coeff.1 i = 0 := coeff.2
    rw [Fin.sum_univ_succ] at hzero
    apply (div_eq_iff h2).2
    linear_combination -hzero
  · simp [zeroBoundaryFromTail, zeroBoundaryTail]

/-- The `d` field elements requested for one Rust round are algebraically in
bijection with the whole zero-boundary coefficient subspace.  This does not
model the word source or rejection sampler. -/
def zeroBoundaryEquiv (h2 : (2 : K) ≠ 0) :
    (Fin d → K) ≃ ZeroBoundaryCoeff K d where
  toFun := zeroBoundaryFromTail h2
  invFun := zeroBoundaryTail
  left_inv := zeroBoundaryTail_fromTail h2
  right_inv := zeroBoundaryFromTail_tail h2

/-- Mapping a uniform finite type through an equivalence gives the uniform law
on the target finite type. -/
theorem map_uniformOfFintype_equiv
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  ext y
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · rw [e.apply_symm_apply, if_pos rfl,
      PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
      Fintype.card_congr e]
  · intro b hb
    have hne : ¬ (y = e b) := fun hy =>
      hb (e.injective (e.apply_symm_apply y |>.trans hy)).symm
    rw [if_neg hne]

/-- Independent uniform tail coefficients induce the exact uniform law on
zero-boundary degree-`d` polynomials. -/
theorem sampledZeroBoundary_uniform [Fintype K] (h2 : (2 : K) ≠ 0) :
    (PMF.uniformOfFintype (Fin d → K)).map (zeroBoundaryFromTail h2)
      = PMF.uniformOfFintype (ZeroBoundaryCoeff K d) :=
  map_uniformOfFintype_equiv (zeroBoundaryEquiv h2)

/-! The Rust sampler requests one initial field element followed by `d` tail
elements for every round.  Under the ideal input law in which those elements
are independent and uniform, the next definitions package the single-round
bijection above into the corresponding finite product.  They do not model the
word source, rejection sampler, Rust representation, commitment, transcript
order, or opening scheme. -/

/-- A family of freely sampled polynomial tails, one for each round. -/
abbrev RoundTailFamily (K : Type*) (rounds d : ℕ) :=
  Fin rounds → Fin d → K

/-- A family of zero-boundary coefficient vectors, one for each round. -/
abbrev RoundMaskFamily (K : Type*) [Field K] (rounds d : ℕ) :=
  Fin rounds → ZeroBoundaryCoeff K d

/-- Applying the exact single-round sampler independently in every coordinate
is a bijection from all tail words to all round-mask families. -/
def zeroBoundaryFamilyEquiv (h2 : (2 : K) ≠ 0) (rounds : ℕ) :
    RoundTailFamily K rounds d ≃ RoundMaskFamily K rounds d where
  toFun tails round := zeroBoundaryFromTail h2 (tails round)
  invFun masks round := zeroBoundaryTail (masks round)
  left_inv tails := by
    funext round
    exact zeroBoundaryTail_fromTail h2 (tails round)
  right_inv masks := by
    funext round
    exact zeroBoundaryFromTail_tail h2 (masks round)

/-- The algebraic state shape used by the Rust primitive: one initial claim and
one zero-boundary polynomial for every round. -/
def sumcheckMaskStateEquiv (h2 : (2 : K) ≠ 0) (rounds : ℕ) :
    (K × RoundTailFamily K rounds d) ≃
      (K × RoundMaskFamily K rounds d) :=
  Equiv.prodCongr (Equiv.refl K) (zeroBoundaryFamilyEquiv h2 rounds)

/-- Ideal uniform independent field draws induce the exact uniform law on the
complete finite-dimensional algebraic state.  This is not a theorem about the
Rust word source or rejection sampler.  A binding commitment and verifier wire
are also outside the model. -/
theorem sampledSumcheckMaskState_uniform [Fintype K]
    (h2 : (2 : K) ≠ 0) (rounds : ℕ) :
    (PMF.uniformOfFintype (K × RoundTailFamily K rounds d)).map
        (sumcheckMaskStateEquiv h2 rounds)
      = PMF.uniformOfFintype (K × RoundMaskFamily K rounds d) :=
  map_uniformOfFintype_equiv (sumcheckMaskStateEquiv h2 rounds)

/-- Constant polynomial with endpoint sum equal to `claim`. -/
def roundCarrier (claim : K) : RoundCoeff K d := fun i =>
  if i = 0 then claim / 2 else 0

theorem roundBoundary_roundCarrier (h2 : (2 : K) ≠ 0) (claim : K) :
    roundBoundary (roundCarrier (d := d) claim) = claim := by
  simp [roundBoundary, roundCarrier]
  field_simp
  ring

/-- Evaluate a round coefficient vector at a field point. -/
def coeffEval (coeff : RoundCoeff K d) (x : K) : K :=
  ∑ i, coeff i * x ^ (i : ℕ)

theorem coeffEval_zero (coeff : RoundCoeff K d) : coeffEval coeff 0 = coeff 0 := by
  simp [coeffEval, Fin.sum_univ_succ]

theorem coeffEval_one (coeff : RoundCoeff K d) : coeffEval coeff 1 = ∑ i, coeff i := by
  simp [coeffEval]

theorem roundBoundary_eq_endpoint_sum (coeff : RoundCoeff K d) :
    roundBoundary coeff = coeffEval coeff 0 + coeffEval coeff 1 := by
  rw [coeffEval_zero, coeffEval_one]
  rfl

/-! ## Endpoint data do not authenticate a non-Boolean evaluation

For one univariate sumcheck round, the Boolean data are the two endpoint
values.  Once degree two is available, those values do not determine an
evaluation at a non-Boolean Fiat--Shamir point: adding `X * (X - 1)` preserves
both endpoints and changes every evaluation away from `0` and `1`.

This is a precise obstruction to the proposed independent B-table production
design if that table supplies only Boolean endpoint data for a degree-27 round.
It is not an impossibility result for authenticated constructions which bind
the full round polynomial, or which authenticate the challenged evaluation by
some other commitment and opening argument.
-/

/-- A coefficient vector for `X^2 - X`, embedded in every round degree at
least two. -/
def endpointKernelQuadratic (hd : 2 ≤ d) : RoundCoeff K d :=
  Pi.single ⟨2, by omega⟩ 1 - Pi.single ⟨1, by omega⟩ 1

/-- Evaluation of a single coefficient coordinate. -/
theorem coeffEval_single (j : Fin (d + 1)) (a x : K) :
    coeffEval (Pi.single j a) x = a * x ^ (j : ℕ) := by
  classical
  rw [coeffEval, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem coeffEval_sub (a b : RoundCoeff K d) (x : K) :
    coeffEval (a - b) x = coeffEval a x - coeffEval b x := by
  simp [coeffEval, sub_mul, Finset.sum_sub_distrib]

theorem coeffEval_endpointKernelQuadratic (hd : 2 ≤ d) (x : K) :
    coeffEval (endpointKernelQuadratic (K := K) hd) x = x ^ 2 - x := by
  rw [endpointKernelQuadratic, coeffEval_sub, coeffEval_single,
    coeffEval_single]
  norm_num

/-- Two degree-at-most-`d` coefficient vectors can have identical Boolean
endpoint data but different evaluations at every non-Boolean field point.
The collision is explicit: zero and `X^2 - X`. -/
theorem booleanEndpoints_do_not_determine_eval (hd : 2 ≤ d) (x : K)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ p q : RoundCoeff K d,
      coeffEval p 0 = coeffEval q 0 ∧
      coeffEval p 1 = coeffEval q 1 ∧
      coeffEval p x ≠ coeffEval q x := by
  refine ⟨0, endpointKernelQuadratic (K := K) hd, ?_, ?_, ?_⟩
  · rw [coeffEval_endpointKernelQuadratic]
    simp [coeffEval]
  · rw [coeffEval_endpointKernelQuadratic]
    simp [coeffEval]
  · rw [coeffEval_endpointKernelQuadratic]
    simp only [coeffEval, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    apply Ne.symm
    rw [show x ^ 2 - x = x * (x - 1) by ring]
    exact mul_ne_zero hx0 (sub_ne_zero.mpr hx1)

/-- The degree-27 instance at challenge `2`.  The sole extra assumption is
that `2` is nonzero, which holds in M31 and excludes only characteristic two.
Thus the witness does not depend on an unsafe characteristic-specific
coefficient calculation. -/
theorem degree27_booleanEndpoints_do_not_determine_eval_at_two
    (h2 : (2 : K) ≠ 0) :
    ∃ p q : RoundCoeff K 27,
      coeffEval p 0 = coeffEval q 0 ∧
      coeffEval p 1 = coeffEval q 1 ∧
      coeffEval p 2 ≠ coeffEval q 2 := by
  apply booleanEndpoints_do_not_determine_eval (K := K) (d := 27)
  · omega
  · exact h2
  · intro h21
    have h10 : (1 : K) = 0 := by
      linear_combination h21
    exact one_ne_zero h10

/-- An exact-degree-27 endpoint collision.  Unlike the quadratic witness above,
this pins the obstruction to a polynomial whose deployed leading coefficient is
nonzero: `X^27 - X^26`. -/
def endpointKernelDegree27 : RoundCoeff K 27 :=
  Pi.single ⟨27, by omega⟩ 1 - Pi.single ⟨26, by omega⟩ 1

theorem coeffEval_endpointKernelDegree27 (x : K) :
    coeffEval (endpointKernelDegree27 (K := K)) x = x ^ 27 - x ^ 26 := by
  rw [endpointKernelDegree27, coeffEval_sub, coeffEval_single,
    coeffEval_single]
  norm_num

theorem endpointKernelDegree27_leadingCoefficient :
    endpointKernelDegree27 (K := K) ⟨27, by omega⟩ = 1 := by
  classical
  simp [endpointKernelDegree27]

/-- Boundary-only authentication fails at the deployed maximum degree itself,
not merely because the degree-27 message type also contains quadratics. -/
theorem exactDegree27_booleanEndpoints_do_not_determine_eval_at_two
    (h2 : (2 : K) ≠ 0) :
    ∃ p q : RoundCoeff K 27,
      coeffEval p 0 = coeffEval q 0 ∧
      coeffEval p 1 = coeffEval q 1 ∧
      coeffEval p 2 ≠ coeffEval q 2 ∧
      q ⟨27, by omega⟩ ≠ 0 := by
  refine ⟨0, endpointKernelDegree27 (K := K), ?_, ?_, ?_, ?_⟩
  · rw [coeffEval_endpointKernelDegree27]
    simp [coeffEval]
  · rw [coeffEval_endpointKernelDegree27]
    simp [coeffEval]
  · rw [coeffEval_endpointKernelDegree27]
    simp only [coeffEval, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    apply Ne.symm
    rw [show (2 : K) ^ 27 - 2 ^ 26 = 2 ^ 26 * (2 - 1) by ring]
    exact mul_ne_zero (pow_ne_zero 26 h2) (by norm_num)
  · rw [endpointKernelDegree27_leadingCoefficient]
    exact one_ne_zero

/-- The preceding degree-27 collision instantiated in the deployed M31 base
field.  Both primality and the fact that `2` is nonzero are discharged in the
kernel; no characteristic assumption remains in the theorem statement. -/
theorem m31_degree27_booleanEndpoints_do_not_determine_eval_at_two :
    letI : Fact (Nat.Prime 2147483647) := ⟨by norm_num⟩
    ∃ p q : RoundCoeff (ZMod 2147483647) 27,
      coeffEval p 0 = coeffEval q 0 ∧
      coeffEval p 1 = coeffEval q 1 ∧
      coeffEval p 2 ≠ coeffEval q 2 := by
  letI : Fact (Nat.Prime 2147483647) := ⟨by norm_num⟩
  apply degree27_booleanEndpoints_do_not_determine_eval_at_two
  have h : ((2 : ℕ) : ZMod 2147483647) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    decide
  simpa using h

/-- The exact-degree-27 witness specialised to M31, including its nonzero
leading coefficient. -/
theorem m31_exactDegree27_booleanEndpoints_do_not_determine_eval_at_two :
    letI : Fact (Nat.Prime 2147483647) := ⟨by norm_num⟩
    ∃ p q : RoundCoeff (ZMod 2147483647) 27,
      coeffEval p 0 = coeffEval q 0 ∧
      coeffEval p 1 = coeffEval q 1 ∧
      coeffEval p 2 ≠ coeffEval q 2 ∧
      q ⟨27, by omega⟩ ≠ 0 := by
  letI : Fact (Nat.Prime 2147483647) := ⟨by norm_num⟩
  apply exactDegree27_booleanEndpoints_do_not_determine_eval_at_two
  have h : ((2 : ℕ) : ZMod 2147483647) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    decide
  simpa using h

/-- A chained mask round: half the incoming state plus a fresh zero-boundary
degree-`d` polynomial. -/
def maskRoundCoeff (state : K) (mask : ZeroBoundaryCoeff K d) : RoundCoeff K d :=
  fun i => roundCarrier state i + mask.1 i

theorem roundBoundary_maskRoundCoeff (h2 : (2 : K) ≠ 0) (state : K)
    (mask : ZeroBoundaryCoeff K d) :
    roundBoundary (maskRoundCoeff state mask) = state := by
  rw [show maskRoundCoeff state mask = roundCarrier state + mask.1 by rfl]
  rw [show roundBoundary (roundCarrier state + mask.1) =
      roundBoundary (roundCarrier state) + roundBoundary mask.1 by
        change roundBoundaryLinear (roundCarrier state + mask.1) = _
        rw [map_add]
        rfl]
  rw [roundBoundary_roundCarrier h2]
  change state + roundBoundaryLinear mask.1 = state
  rw [mask.2, add_zero]

theorem maskRoundCoeff_endpoint_sum (h2 : (2 : K) ≠ 0) (state : K)
    (mask : ZeroBoundaryCoeff K d) :
    coeffEval (maskRoundCoeff state mask) 0 +
      coeffEval (maskRoundCoeff state mask) 1 = state := by
  rw [← roundBoundary_eq_endpoint_sum]
  exact roundBoundary_maskRoundCoeff h2 state mask

/-- Sum of the terminal values over the Boolean tree generated by a fixed
sequence of zero-boundary round masks. -/
def telescopingMaskBooleanSum (state : K) :
    List (ZeroBoundaryCoeff K d) → K
  | [] => state
  | mask :: remaining =>
      telescopingMaskBooleanSum
          (coeffEval (maskRoundCoeff state mask) 0) remaining
        + telescopingMaskBooleanSum
          (coeffEval (maskRoundCoeff state mask) 1) remaining

/-- The globally chained mask oracle sums to its initial claim on the Boolean
cube, for every fixed sequence of round masks. -/
theorem telescopingMaskBooleanSum_eq (h2 : (2 : K) ≠ 0)
    (masks : List (ZeroBoundaryCoeff K d)) (state : K) :
    telescopingMaskBooleanSum state masks = state := by
  induction masks generalizing state with
  | nil => rfl
  | cons mask remaining ih =>
      rw [telescopingMaskBooleanSum, ih, ih,
        maskRoundCoeff_endpoint_sum h2]

/-- Remove a round polynomial's endpoint sum, leaving a zero-boundary vector. -/
def normalisedRound (h2 : (2 : K) ≠ 0) (coeff : RoundCoeff K d) :
    ZeroBoundaryCoeff K d :=
  ⟨coeff - roundCarrier (roundBoundary coeff), by
    change roundBoundary (coeff - roundCarrier (roundBoundary coeff)) = 0
    rw [show roundBoundary (coeff - roundCarrier (roundBoundary coeff)) =
      roundBoundary coeff - roundBoundary (roundCarrier (roundBoundary coeff)) by
        change roundBoundaryLinear (coeff - roundCarrier (roundBoundary coeff)) = _
        rw [map_sub]
        rfl]
    rw [roundBoundary_roundCarrier h2]
    exact sub_self _⟩

/-- Complete mixed round, expressed at its visible incoming claim. -/
def maskedRound (h2 : (2 : K) ≠ 0) (claim eta : K)
    (real : RoundCoeff K d) (mask : ZeroBoundaryCoeff K d) : RoundCoeff K d :=
  fun i => roundCarrier claim i + (mask + eta • normalisedRound h2 real :
    ZeroBoundaryCoeff K d).1 i

/-- The conditional form above equals the operational form: the mask's
incoming state plus `eta` times the real round polynomial. -/
theorem maskedRound_eq_mask_plus_real (h2 : (2 : K) ≠ 0) (claim eta : K)
    (real : RoundCoeff K d) (mask : ZeroBoundaryCoeff K d) :
    maskedRound h2 claim eta real mask =
      maskRoundCoeff (claim - eta * roundBoundary real) mask + eta • real := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [maskedRound, normalisedRound, maskRoundCoeff, roundCarrier]
    field_simp
    ring
  · simp [maskedRound, normalisedRound, maskRoundCoeff, roundCarrier, hi]

theorem roundBoundary_maskedRound (h2 : (2 : K) ≠ 0) (claim eta : K)
    (real : RoundCoeff K d) (mask : ZeroBoundaryCoeff K d) :
    roundBoundary (maskedRound h2 claim eta real mask) = claim := by
  rw [show maskedRound h2 claim eta real mask =
      roundCarrier claim + (mask + eta • normalisedRound h2 real).1 by rfl]
  rw [show roundBoundary
      (roundCarrier claim + (mask + eta • normalisedRound h2 real).1) =
      roundBoundary (roundCarrier claim) +
        roundBoundary (mask + eta • normalisedRound h2 real).1 by
        change roundBoundaryLinear
          (roundCarrier claim + (mask + eta • normalisedRound h2 real).1) = _
        rw [map_add]
        rfl]
  rw [roundBoundary_roundCarrier h2]
  change claim + roundBoundaryLinear
    (mask + eta • normalisedRound h2 real).1 = claim
  rw [(mask + eta • normalisedRound h2 real).2, add_zero]

section RoundDistribution

variable [Fintype K]

/-- Given the visible incoming claim, a complete masked degree-`d` round has
the same distribution for every real round polynomial. This is the exact
`d`-dimensional affine hyperplane of coefficient vectors with that boundary. -/
theorem maskedRound_pmf_indep (h2 : (2 : K) ≠ 0) (claim eta : K)
    (real₁ real₂ : RoundCoeff K d) :
    (PMF.uniformOfFintype (ZeroBoundaryCoeff K d)).map
        (maskedRound h2 claim eta real₁)
      = (PMF.uniformOfFintype (ZeroBoundaryCoeff K d)).map
          (maskedRound h2 claim eta real₂) := by
  classical
  let output : ZeroBoundaryCoeff K d → RoundCoeff K d := fun zero i =>
    roundCarrier claim i + zero.1 i
  have hreal : ∀ real : RoundCoeff K d,
      (PMF.uniformOfFintype (ZeroBoundaryCoeff K d)).map
          (maskedRound h2 claim eta real)
        = (PMF.uniformOfFintype (ZeroBoundaryCoeff K d)).map output := by
    intro real
    let shift : ZeroBoundaryCoeff K d := eta • normalisedRound h2 real
    have hshift := map_uniformOfFintype_equiv (Equiv.addRight shift)
    have hmap := congrArg (fun distribution : PMF (ZeroBoundaryCoeff K d) =>
      distribution.map output) hshift
    rw [PMF.map_comp] at hmap
    have heq : output ∘ (Equiv.addRight shift :
        ZeroBoundaryCoeff K d → ZeroBoundaryCoeff K d) =
        maskedRound h2 claim eta real := by
      funext mask i
      rfl
    rw [heq] at hmap
    exact hmap
  exact (hreal real₁).trans (hreal real₂).symm

/-! A finite-dimensional batch statement is possible without modelling
Fiat--Shamir: after supplying an external boundary label for every coordinate,
all round messages are jointly independent of the corresponding real
polynomial vector.  This is not the conditional law of the coherent protocol
transcript: later protocol claims are evaluations of earlier messages, whereas
the labels below are unconstrained external inputs. -/

/-- Apply `maskedRound` coordinatewise to a fixed finite collection of rounds. -/
def maskedRoundFamily {rounds : ℕ} (h2 : (2 : K) ≠ 0)
    (claims : Fin rounds → K) (eta : K)
    (real : Fin rounds → RoundCoeff K d)
    (masks : RoundMaskFamily K rounds d) :
    Fin rounds → RoundCoeff K d :=
  fun round => maskedRound h2 (claims round) eta (real round) (masks round)

/-- With all external boundary labels fixed, fresh independent full-dimensional
round masks hide a finite vector of real degree-`d` round polynomials jointly.

This batch affine statement does not model a coherent or adaptive transcript.
In particular it makes no statement about a mask commitment preceding `eta`,
Fiat--Shamir challenge composition, or authentication of the terminal oracle
evaluation. -/
theorem maskedRoundFamily_pmf_indep {rounds : ℕ} (h2 : (2 : K) ≠ 0)
    (claims : Fin rounds → K) (eta : K)
    (real₁ real₂ : Fin rounds → RoundCoeff K d) :
    (PMF.uniformOfFintype (RoundMaskFamily K rounds d)).map
        (maskedRoundFamily h2 claims eta real₁)
      = (PMF.uniformOfFintype (RoundMaskFamily K rounds d)).map
          (maskedRoundFamily h2 claims eta real₂) := by
  classical
  let output : RoundMaskFamily K rounds d →
      (Fin rounds → RoundCoeff K d) := fun masks round i =>
    roundCarrier (claims round) i + (masks round).1 i
  have hreal : ∀ real : Fin rounds → RoundCoeff K d,
      (PMF.uniformOfFintype (RoundMaskFamily K rounds d)).map
          (maskedRoundFamily h2 claims eta real)
        = (PMF.uniformOfFintype (RoundMaskFamily K rounds d)).map output := by
    intro real
    let shift : RoundMaskFamily K rounds d := fun round =>
      eta • normalisedRound h2 (real round)
    have hshift := map_uniformOfFintype_equiv (Equiv.addRight shift)
    have hmap := congrArg
      (fun distribution : PMF (RoundMaskFamily K rounds d) =>
        distribution.map output) hshift
    rw [PMF.map_comp] at hmap
    have heq : output ∘
        (Equiv.addRight shift :
          RoundMaskFamily K rounds d → RoundMaskFamily K rounds d) =
        maskedRoundFamily h2 claims eta real := by
      funext masks round i
      rfl
    rw [heq] at hmap
    exact hmap
  exact (hreal real₁).trans (hreal real₂).symm

/-- Any deterministic observation of the externally labelled round vector preserves
the joint witness-independent distribution.  The observer is not a model of
Fiat--Shamir unless a separate adaptive-composition theorem establishes that
correspondence. -/
theorem observed_maskedRoundFamily_pmf_indep {rounds : ℕ}
    {View : Type*} (observe : (Fin rounds → RoundCoeff K d) → View)
    (h2 : (2 : K) ≠ 0) (claims : Fin rounds → K) (eta : K)
    (real₁ real₂ : Fin rounds → RoundCoeff K d) :
    (PMF.uniformOfFintype (RoundMaskFamily K rounds d)).map
        (fun masks => observe (maskedRoundFamily h2 claims eta real₁ masks))
      = (PMF.uniformOfFintype (RoundMaskFamily K rounds d)).map
          (fun masks => observe
            (maskedRoundFamily h2 claims eta real₂ masks)) := by
  classical
  have h := congrArg
    (fun distribution : PMF (Fin rounds → RoundCoeff K d) =>
      distribution.map observe)
    (maskedRoundFamily_pmf_indep h2 claims eta real₁ real₂)
  simpa only [PMF.map_comp, Function.comp_def] using h

end RoundDistribution

end RoundTranscript

end AspisSumcheckMasking

#print axioms AspisSumcheckMasking.tableSum_maskedOracle
#print axioms AspisSumcheckMasking.original_sum_eq_zero_of_mixed_sum
#print axioms AspisSumcheckMasking.accepting_challenge_unique
#print axioms AspisSumcheckMasking.maskedOracle_pmf_indep
#print axioms AspisSumcheckMasking.observed_maskedOracle_pmf_indep
#print axioms AspisSumcheckMasking.maskSum_and_observation_pmf_indep
#print axioms AspisSumcheckMasking.sampledZeroBoundary_uniform
#print axioms AspisSumcheckMasking.sampledSumcheckMaskState_uniform
#print axioms AspisSumcheckMasking.booleanEndpoints_do_not_determine_eval
#print axioms AspisSumcheckMasking.degree27_booleanEndpoints_do_not_determine_eval_at_two
#print axioms AspisSumcheckMasking.exactDegree27_booleanEndpoints_do_not_determine_eval_at_two
#print axioms AspisSumcheckMasking.m31_degree27_booleanEndpoints_do_not_determine_eval_at_two
#print axioms AspisSumcheckMasking.m31_exactDegree27_booleanEndpoints_do_not_determine_eval_at_two
#print axioms AspisSumcheckMasking.maskRoundCoeff_endpoint_sum
#print axioms AspisSumcheckMasking.telescopingMaskBooleanSum_eq
#print axioms AspisSumcheckMasking.maskedRound_eq_mask_plus_real
#print axioms AspisSumcheckMasking.roundBoundary_maskedRound
#print axioms AspisSumcheckMasking.maskedRound_pmf_indep
#print axioms AspisSumcheckMasking.maskedRoundFamily_pmf_indep
#print axioms AspisSumcheckMasking.observed_maskedRoundFamily_pmf_indep
