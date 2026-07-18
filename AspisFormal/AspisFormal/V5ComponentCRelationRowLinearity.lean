import AspisFormal.V5ComponentCConcreteFoldLinearity

/-!
# v5 Component C: exact fixed-schedule relation-row linearity

This leaf constructs the `36 = 4 * (2 + 7)` witness-dependent relation rows
that precede the later-FRI rows in Component C's fixed-schedule `F_sigma`.
Unlike a seam that accepts an arbitrary bundled `relationRows` linear map, the
two OOD reads and the seven sumcheck coefficients of every round are assembled
here from their exact deployed arithmetic.

The load-bearing Rust sources are:

* `crates/aspis-core/src/sumcheck.rs`, `accumulate_chunk` and
  `polynomial_for_extension`: if `A = [a0,a1,a2,a3]` and public weights are
  `[w0,w1,w2,w3]`, the dual polynomial has coefficients
  `[w0,w3,w2,w1] / 4`; the two degree-three polynomials are convolved into
  degrees `0..6`;
* `crates/aspis-prover/src/v5_relation_prover.rs`: two OOD evaluations are
  released before each round polynomial, then coefficients are folded by
  `[1,alpha,alpha^2,alpha^3]`;
* `crates/aspis-prover/src/v5_component_c_fmat.rs`: the fixed public OOD
  covectors and post-OOD polynomial-weight tables are materialized for lengths
  `1024,256,64,16`, and the packed row order is round-major with two OOD rows
  followed by seven polynomial rows.

The public OOD covectors and public polynomial-weight tables are fields of
`FixedRelationSchedule`; their derivation by Rust's `WeightAccumulator`, their
transcript provenance, and their byte/table correspondence remain explicitly
unproved deployment seams.  The polynomial arithmetic, dual order, division by
four, coefficient folding, linearity, and 2+7 enumeration are constructed in
Lean rather than assumed.

This file proves no C-DEC statement, transport theorem, or deployed-ZK claim.
-/

namespace AspisV5ComponentCRelationRowLinearity

open AspisV5ComponentCConcreteFoldLinearity

/-! ## One exact `accumulate_chunk` -/

section Chunk

variable {K : Type*} [Field K]

/-- Linear convolution of two degree-three coefficient vectors, with a fixed
public normalization scalar.  `b` is already in polynomial coefficient order. -/
def convolutionChunkLinear (quarter : K) (b : Fin 4 → K) :
    (Fin 4 → K) →ₗ[K] (Fin 7 → K) :=
  LinearMap.pi ![
    (quarter * b 0) • LinearMap.proj 0,
    (quarter * b 1) • LinearMap.proj 0 +
      (quarter * b 0) • LinearMap.proj 1,
    (quarter * b 2) • LinearMap.proj 0 +
      (quarter * b 1) • LinearMap.proj 1 +
      (quarter * b 0) • LinearMap.proj 2,
    (quarter * b 3) • LinearMap.proj 0 +
      (quarter * b 2) • LinearMap.proj 1 +
      (quarter * b 1) • LinearMap.proj 2 +
      (quarter * b 0) • LinearMap.proj 3,
    (quarter * b 3) • LinearMap.proj 1 +
      (quarter * b 2) • LinearMap.proj 2 +
      (quarter * b 1) • LinearMap.proj 3,
    (quarter * b 3) • LinearMap.proj 2 +
      (quarter * b 2) • LinearMap.proj 3,
    (quarter * b 3) • LinearMap.proj 3]

/-- Rust's exact B-dual order `[w0,w3,w2,w1]`. -/
def dualWeights (weights : Fin 4 → K) : Fin 4 → K :=
  ![weights 0, weights 3, weights 2, weights 1]

/-- Exact `accumulate_chunk`: convolution against `[w0,w3,w2,w1]/4`. -/
def accumulateChunkLinear (weights : Fin 4 → K) :
    (Fin 4 → K) →ₗ[K] (Fin 7 → K) :=
  convolutionChunkLinear (4 : K)⁻¹ (dualWeights weights)

/-- Closed coefficient vector for a generic degree-three convolution. -/
theorem convolutionChunkLinear_apply (quarter : K) (b values : Fin 4 → K) :
    convolutionChunkLinear quarter b values =
      ![
        quarter * values 0 * b 0,
        quarter * (values 0 * b 1 + values 1 * b 0),
        quarter * (values 0 * b 2 + values 1 * b 1 + values 2 * b 0),
        quarter * (values 0 * b 3 + values 1 * b 2 +
          values 2 * b 1 + values 3 * b 0),
        quarter * (values 1 * b 3 + values 2 * b 2 + values 3 * b 1),
        quarter * (values 2 * b 3 + values 3 * b 2),
        quarter * values 3 * b 3] := by
  funext d
  fin_cases d <;>
    simp [convolutionChunkLinear, smul_eq_mul] <;> ring

/-- Closed coefficient vector for the exact nested Rust loops. -/
theorem accumulateChunkLinear_apply (weights values : Fin 4 → K) :
    accumulateChunkLinear weights values =
      ![
        values 0 * weights 0 / 4,
        (values 0 * weights 3 + values 1 * weights 0) / 4,
        (values 0 * weights 2 + values 1 * weights 3 + values 2 * weights 0) / 4,
        (values 0 * weights 1 + values 1 * weights 2 +
          values 2 * weights 3 + values 3 * weights 0) / 4,
        (values 1 * weights 1 + values 2 * weights 2 + values 3 * weights 3) / 4,
        (values 2 * weights 1 + values 3 * weights 2) / 4,
        values 3 * weights 1 / 4] := by
  funext d
  fin_cases d <;>
    simp [accumulateChunkLinear, convolutionChunkLinear, dualWeights,
      smul_eq_mul, div_eq_mul_inv] <;> ring

/-- One public dot-product covector, bundled as a linear map. -/
def dotLinear {n : Nat} (weights : Fin n → K) : (Fin n → K) →ₗ[K] K :=
  ∑ i : Fin n, (weights i) • LinearMap.proj i

theorem dotLinear_apply {n : Nat} (weights values : Fin n → K) :
    dotLinear weights values = ∑ i, values i * weights i := by
  simp only [dotLinear, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact `polynomial_for_extension`: apply `accumulate_chunk` to every
consecutive fibre and add the seven coefficient vectors. -/
def polynomialForExtension (n : Nat) (weights : Fin (4 * n) → K) :
    (Fin (4 * n) → K) →ₗ[K] (Fin 7 → K) :=
  ∑ i : Fin n,
    accumulateChunkLinear (fun s => weights (childIndex i s)) ∘ₗ gatherFibre n i

theorem polynomialForExtension_apply (n : Nat) (weights values : Fin (4 * n) → K) :
    polynomialForExtension n weights values =
      ∑ i : Fin n, accumulateChunkLinear
        (fun s => weights (childIndex i s)) (fun s => values (childIndex i s)) := by
  simp only [polynomialForExtension, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-! ### Boundary and evaluation are themselves fixed linear read-offs -/

/-- Rust `boundary_sum`: four times coefficients zero plus four. -/
def boundaryLinear : (Fin 7 → K) →ₗ[K] K where
  toFun p := 4 * (p 0 + p 4)
  map_add' p q := by
    simp only [Pi.add_apply]
    ring
  map_smul' a p := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem boundaryLinear_apply (p : Fin 7 → K) :
    boundaryLinear p = 4 * (p 0 + p 4) :=
  rfl

/-- Evaluation of the degree-at-most-six polynomial at a fixed public point. -/
def polynomialEvaluationLinear (z : K) : (Fin 7 → K) →ₗ[K] K :=
  ∑ d : Fin 7, (z ^ d.val) • LinearMap.proj d

theorem polynomialEvaluationLinear_apply (z : K) (p : Fin 7 → K) :
    polynomialEvaluationLinear z p = ∑ d : Fin 7, p d * z ^ d.val := by
  simp only [polynomialEvaluationLinear, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

end Chunk

/-! ## Four exact relation rounds -/

section Rounds

variable (K : Type*) [Field K]

abbrev Coefficients := Fin coefficientCount → K

/-- Fixed public data after transcript derivation.  The weight tables are the
values returned by `WeightAccumulator.weight_at` immediately before each OOD
read (for `ood*`) or after the two OOD terms have been mixed in (for `poly*`). -/
structure FixedRelationSchedule where
  alpha : Fin 4 → K
  ood0 : Fin 2 → Fin 1024 → K
  ood1 : Fin 2 → Fin 256 → K
  ood2 : Fin 2 → Fin 64 → K
  ood3 : Fin 2 → Fin 16 → K
  poly0 : Fin 1024 → K
  poly1 : Fin 256 → K
  poly2 : Fin 64 → K
  poly3 : Fin 16 → K

variable {K}

def round1Coefficients (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 256 → K) :=
  coefficientFoldLayer 256 (schedule.alpha 0)

def round2Coefficients (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 64 → K) :=
  coefficientFoldLayer 64 (schedule.alpha 1) ∘ₗ round1Coefficients schedule

def round3Coefficients (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 16 → K) :=
  coefficientFoldLayer 16 (schedule.alpha 2) ∘ₗ round2Coefficients schedule

def ood0Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi fun sample => dotLinear (schedule.ood0 sample)

def ood1Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi fun sample =>
    dotLinear (schedule.ood1 sample) ∘ₗ round1Coefficients schedule

def ood2Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi fun sample =>
    dotLinear (schedule.ood2 sample) ∘ₗ round2Coefficients schedule

def ood3Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi fun sample =>
    dotLinear (schedule.ood3 sample) ∘ₗ round3Coefficients schedule

def polynomial0Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 7 → K) :=
  polynomialForExtension 256 schedule.poly0

def polynomial1Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 7 → K) :=
  polynomialForExtension 64 schedule.poly1 ∘ₗ round1Coefficients schedule

def polynomial2Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 7 → K) :=
  polynomialForExtension 16 schedule.poly2 ∘ₗ round2Coefficients schedule

def polynomial3Rows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (Fin 7 → K) :=
  polynomialForExtension 4 schedule.poly3 ∘ₗ round3Coefficients schedule

def roundOodRows (schedule : FixedRelationSchedule K) :
    Fin 4 → Coefficients K →ₗ[K] (Fin 2 → K) :=
  ![ood0Rows schedule, ood1Rows schedule, ood2Rows schedule, ood3Rows schedule]

def roundPolynomialRows (schedule : FixedRelationSchedule K) :
    Fin 4 → Coefficients K →ₗ[K] (Fin 7 → K) :=
  ![polynomial0Rows schedule, polynomial1Rows schedule,
    polynomial2Rows schedule, polynomial3Rows schedule]

abbrev RelationTaggedIndex := Fin 4 × (Fin 2 ⊕ Fin 7)

/-- Within each round, `inl` is OOD rows 0,1 and `inr` is polynomial rows
0..6. -/
def relationTaggedRows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (RelationTaggedIndex → K) :=
  LinearMap.pi fun index =>
    match index.2 with
    | .inl sample => LinearMap.proj sample ∘ₗ roundOodRows schedule index.1
    | .inr degree => LinearMap.proj degree ∘ₗ roundPolynomialRows schedule index.1

/-- Exact round-major `4 * 9 = 36` row enumeration. -/
def relationTaggedIndexEquiv : RelationTaggedIndex ≃ RelationIndex :=
  Equiv.prodCongr (Equiv.refl (Fin 4)) finSumFinEquiv

/-- The concrete 36-row map accepted by `concreteF` in the preceding leaf. -/
def relationRows (schedule : FixedRelationSchedule K) :
    Coefficients K →ₗ[K] (RelationIndex → K) :=
  (LinearEquiv.funCongrLeft K K relationTaggedIndexEquiv.symm).toLinearMap ∘ₗ
    relationTaggedRows schedule

theorem relationRows_at_ood (schedule : FixedRelationSchedule K)
    (c : Coefficients K) (round : Fin 4) (sample : Fin 2) :
    relationRows schedule c
        (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)) =
      roundOodRows schedule round c sample := by
  have hindex :
      relationTaggedIndexEquiv.symm
        (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample)) =
        (round, .inl sample) := by
    unfold relationTaggedIndexEquiv
    apply Prod.ext
    · rfl
    · exact (finSumFinEquiv (m := 2) (n := 7)).symm_apply_apply _
  change relationTaggedRows schedule c
      (relationTaggedIndexEquiv.symm
        (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))) = _
  rw [hindex]
  rfl

theorem relationRows_at_polynomial (schedule : FixedRelationSchedule K)
    (c : Coefficients K) (round : Fin 4) (degree : Fin 7) :
    relationRows schedule c
        (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)) =
      roundPolynomialRows schedule round c degree := by
  have hindex :
      relationTaggedIndexEquiv.symm
        (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree)) =
        (round, .inr degree) := by
    unfold relationTaggedIndexEquiv
    apply Prod.ext
    · rfl
    · exact (finSumFinEquiv (m := 2) (n := 7)).symm_apply_apply _
  change relationTaggedRows schedule c
      (relationTaggedIndexEquiv.symm
        (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))) = _
  rw [hindex]
  rfl

theorem relationRows_add (schedule : FixedRelationSchedule K)
    (c d : Coefficients K) :
    relationRows schedule (c + d) =
      relationRows schedule c + relationRows schedule d :=
  map_add _ _ _

theorem relationRows_smul (schedule : FixedRelationSchedule K)
    (a : K) (c : Coefficients K) :
    relationRows schedule (a • c) = a • relationRows schedule c :=
  map_smul _ _ _

/-! ### Honest deployment seams -/

namespace UnmetDeployment

/-- Rust `WeightAccumulator` and the fixed transcript produce exactly these
eight OOD tables and four post-OOD polynomial tables, in the same natural
coefficient order. -/
def RustWeightTablesCorrespond
    (schedule : FixedRelationSchedule K)
    (rustOod0 : Fin 2 → Fin 1024 → K)
    (rustOod1 : Fin 2 → Fin 256 → K)
    (rustOod2 : Fin 2 → Fin 64 → K)
    (rustOod3 : Fin 2 → Fin 16 → K)
    (rustPoly0 : Fin 1024 → K)
    (rustPoly1 : Fin 256 → K)
    (rustPoly2 : Fin 64 → K)
    (rustPoly3 : Fin 16 → K) : Prop :=
  rustOod0 = schedule.ood0 ∧ rustOod1 = schedule.ood1 ∧
  rustOod2 = schedule.ood2 ∧ rustOod3 = schedule.ood3 ∧
  rustPoly0 = schedule.poly0 ∧ rustPoly1 = schedule.poly1 ∧
  rustPoly2 = schedule.poly2 ∧ rustPoly3 = schedule.poly3

/-- The Rust serializer's 36 witness-dependent values equal this concrete map
after canonical QM31 decoding. -/
def RustRelationRowsCorrespond
    (schedule : FixedRelationSchedule K)
    (rustRows : Coefficients K → RelationIndex → K) : Prop :=
  ∀ c, rustRows c = relationRows schedule c

/-- The alphas used by the relation coefficient folds are the transcript
alphas used by the concrete FRI fold schedule. -/
def RelationAndFriAlphasAgree
    {F : Type*} [Field F] [Algebra F K]
    (relationSchedule : FixedRelationSchedule K)
    (friSchedule : FixedSchedule F K) : Prop :=
  relationSchedule.alpha = friSchedule.alpha

end UnmetDeployment

end Rounds

/-! ## Mutation teeth -/

section MutationTeeth

def dualMutationValues : Fin 4 → Rat := ![0, 1, 0, 0]
def dualMutationWeights : Fin 4 → Rat := ![0, 1, 0, 0]
def quarterMutationValues : Fin 4 → Rat := ![1, 0, 0, 0]
def quarterMutationWeights : Fin 4 → Rat := ![1, 0, 0, 0]

@[simp] theorem dualMutationValues_zero : dualMutationValues 0 = 0 := rfl
@[simp] theorem dualMutationValues_one : dualMutationValues 1 = 1 := rfl
@[simp] theorem dualMutationValues_two : dualMutationValues 2 = 0 := rfl
@[simp] theorem dualMutationValues_three : dualMutationValues 3 = 0 := rfl
@[simp] theorem dualMutationWeights_zero : dualMutationWeights 0 = 0 := rfl
@[simp] theorem dualMutationWeights_one : dualMutationWeights 1 = 1 := rfl
@[simp] theorem dualMutationWeights_two : dualMutationWeights 2 = 0 := rfl
@[simp] theorem dualMutationWeights_three : dualMutationWeights 3 = 0 := rfl
@[simp] theorem quarterMutationValues_zero : quarterMutationValues 0 = 1 := rfl
@[simp] theorem quarterMutationValues_one : quarterMutationValues 1 = 0 := rfl
@[simp] theorem quarterMutationValues_two : quarterMutationValues 2 = 0 := rfl
@[simp] theorem quarterMutationValues_three : quarterMutationValues 3 = 0 := rfl
@[simp] theorem quarterMutationWeights_zero : quarterMutationWeights 0 = 1 := rfl
@[simp] theorem quarterMutationWeights_one : quarterMutationWeights 1 = 0 := rfl
@[simp] theorem quarterMutationWeights_two : quarterMutationWeights 2 = 0 := rfl
@[simp] theorem quarterMutationWeights_three : quarterMutationWeights 3 = 0 := rfl

/-- Replacing `[w0,w3,w2,w1]` with the tempting natural order changes the
polynomial: `X * X` has degree two naturally but degree four under the dual. -/
theorem dual_order_is_load_bearing :
    accumulateChunkLinear dualMutationWeights dualMutationValues ≠
      convolutionChunkLinear (4 : Rat)⁻¹ dualMutationWeights dualMutationValues := by
  intro h
  have h4 := congrFun h (4 : Fin 7)
  have hl := congrFun
    (accumulateChunkLinear_apply dualMutationWeights dualMutationValues) (4 : Fin 7)
  have hr := congrFun
    (convolutionChunkLinear_apply (4 : Rat)⁻¹ dualMutationWeights dualMutationValues)
      (4 : Fin 7)
  rw [hl, hr] at h4
  norm_num [dualWeights, Matrix.cons_val_four] at h4

/-- Omitting `/4` changes even the constant-basis chunk. -/
theorem quarter_normalization_is_load_bearing :
    accumulateChunkLinear quarterMutationWeights quarterMutationValues ≠
      convolutionChunkLinear (1 : Rat) (dualWeights quarterMutationWeights)
        quarterMutationValues := by
  intro h
  have h0 := congrFun h (0 : Fin 7)
  have hl := congrFun
    (accumulateChunkLinear_apply quarterMutationWeights quarterMutationValues) (0 : Fin 7)
  have hr := congrFun
    (convolutionChunkLinear_apply (1 : Rat) (dualWeights quarterMutationWeights)
      quarterMutationValues) (0 : Fin 7)
  rw [hl, hr] at h0
  norm_num [dualWeights] at h0

end MutationTeeth

/-! ## Axiom audit -/

#print axioms accumulateChunkLinear_apply
#print axioms dotLinear_apply
#print axioms polynomialForExtension_apply
#print axioms boundaryLinear_apply
#print axioms polynomialEvaluationLinear_apply
#print axioms relationRows_at_ood
#print axioms relationRows_at_polynomial
#print axioms relationRows_add
#print axioms relationRows_smul
#print axioms dual_order_is_load_bearing
#print axioms quarter_normalization_is_load_bearing

end AspisV5ComponentCRelationRowLinearity
