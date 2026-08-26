import AspisFormal.Pool.V7DeployedCopyEvaluatorBalanceBridge

/-!
# Tag-73 inactive-helper aggregate strengthening

The Tag-73 terminal adds one wire-neutral term to the frozen V5/V6 terminal:

`mu^2 * inactiveIndicator(z) * H1(z)`.

On the Boolean cube this authenticates the *sum* of inactive helper padding;
it does not force any inactive helper cell to zero.  This is the intended
boundary because inactive cells may contain random padding whose aggregate is
zero.  The resulting aggregate in `mu` has coefficients

* the constraint MLE;
* the total helper sum; and
* the inactive helper sum.

This file proves the exact Boolean-cube sum identity, the deterministic
coefficient accounting, the at-most-two-roots sampled-challenge boundary, and
the deployed-copy rational-balance closure using only the inactive aggregate.
The original pointwise `DeployedCopyHelperInactiveZero` theorem remains
available to frozen callers but is not used here.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisPool.V7Tag73InactiveHelperAggregate

open Module Polynomial
open AspisFormal.ArithmetizationCore
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7DeployedCopyEvaluatorBalanceBridge
open AspisPool.V7DeployedCopyLogUpAliasClosure
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7PointClaimBatchBinding
open AspisSumcheckMasking
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5ConstraintLaneBatching
open AspisV5FriConcreteEncoderApplicability
open AspisV5TowerPackedResidualExtraction
open AspisV6OneFoldCandidateExtraction

/-! ## Boolean active/inactive partition -/

noncomputable def deployedCopyInactiveIndicator
    {K : Type*} [Field K] (row : Fin 1024) : K := by
  classical
  exact if deployedCopyRowActive row then 0 else 1

noncomputable def inactiveHelperPart
    {K : Type*} [Field K] (helper : Fin 1024 → K) (row : Fin 1024) : K :=
  deployedCopyInactiveIndicator row * helper row

noncomputable def activeHelperPart
    {K : Type*} [Field K] (helper : Fin 1024 → K) (row : Fin 1024) : K := by
  classical
  exact if deployedCopyRowActive row then helper row else 0

noncomputable def deployedCopyInactiveRows : Finset (Fin 1024) := by
  classical
  exact Finset.univ.filter fun row => ¬ deployedCopyRowActive row

noncomputable def inactiveHelperSum
    {K : Type*} [Field K] (helper : Fin 1024 → K) : K :=
  tableSum (inactiveHelperPart helper)

noncomputable def activeHelperSum
    {K : Type*} [Field K] (helper : Fin 1024 → K) : K :=
  tableSum (activeHelperPart helper)

def DeployedCopyHelperInactiveSumZero
    {K : Type*} [Field K] (helper : Fin 1024 → K) : Prop :=
  inactiveHelperSum helper = 0

theorem inactiveHelperPart_eq_zero_of_active
    {K : Type*} [Field K] (helper : Fin 1024 → K) (row : Fin 1024)
    (active : deployedCopyRowActive row) :
    inactiveHelperPart helper row = 0 := by
  classical
  simp [inactiveHelperPart, deployedCopyInactiveIndicator, active]

theorem inactiveHelperPart_eq_helper_of_inactive
    {K : Type*} [Field K] (helper : Fin 1024 → K) (row : Fin 1024)
    (inactive : ¬ deployedCopyRowActive row) :
    inactiveHelperPart helper row = helper row := by
  classical
  simp [inactiveHelperPart, deployedCopyInactiveIndicator, inactive]

theorem helper_eq_active_add_inactive
    {K : Type*} [Field K] (helper : Fin 1024 → K) (row : Fin 1024) :
    helper row = activeHelperPart helper row + inactiveHelperPart helper row := by
  classical
  by_cases active : deployedCopyRowActive row
  · simp [activeHelperPart, inactiveHelperPart_eq_zero_of_active helper row active,
      active]
  · simp [activeHelperPart,
      inactiveHelperPart_eq_helper_of_inactive helper row active, active]

theorem helper_sum_eq_active_add_inactive
    {K : Type*} [Field K] (helper : Fin 1024 → K) :
    tableSum helper = activeHelperSum helper + inactiveHelperSum helper := by
  classical
  unfold tableSum activeHelperSum inactiveHelperSum
  calc
    (∑ row, helper row) =
        ∑ row, (activeHelperPart helper row + inactiveHelperPart helper row) := by
      apply Finset.sum_congr rfl
      intro row _
      exact helper_eq_active_add_inactive helper row
    _ = (∑ row, activeHelperPart helper row) +
        ∑ row, inactiveHelperPart helper row := Finset.sum_add_distrib

/-- The indicator spelling is exactly the finite sum over inactive Boolean
rows.  This makes clear that the new terminal authenticates an aggregate, not
the individual padding cells. -/
theorem inactiveHelperSum_eq_inactiveRows_sum
    {K : Type*} [Field K] (helper : Fin 1024 → K) :
    inactiveHelperSum helper =
      ∑ row ∈ deployedCopyInactiveRows, helper row := by
  classical
  simp only [inactiveHelperSum, tableSum, inactiveHelperPart,
    deployedCopyInactiveRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  by_cases active : deployedCopyRowActive row
  · simp [deployedCopyInactiveIndicator, active]
  · simp [deployedCopyInactiveIndicator, active]

theorem activeHelperSum_zero_of_total_and_inactive
    {K : Type*} [Field K] (helper : Fin 1024 → K)
    (totalZero : tableSum helper = 0)
    (inactiveZero : inactiveHelperSum helper = 0) :
    activeHelperSum helper = 0 := by
  have partition := helper_sum_eq_active_add_inactive helper
  rw [totalZero, inactiveZero, add_zero] at partition
  exact partition.symm

/-! ## Exact Tag-73 Boolean oracle -/

noncomputable def tag73StrengthenedUnmaskedTable
    {K : Type*} [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 → ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K) : Fin 1024 → K := fun row =>
  sourceUnmaskedZerocheckTable basis constraintRows theta zerocheckPoint
      mu helper row +
    mu ^ 2 * deployedCopyInactiveIndicator row * helper row

/-- Boolean-cube identity for precisely the new quadratic terminal term. -/
theorem tableSum_tag73_inactive_quadratic_term
    {K : Type*} [Field K]
    (mu : K) (helper : Fin 1024 → K) :
    tableSum (fun row =>
      mu ^ 2 * deployedCopyInactiveIndicator row * helper row) =
      mu ^ 2 * inactiveHelperSum helper := by
  classical
  simp only [tableSum, inactiveHelperSum, inactiveHelperPart]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- Summing the strengthened Boolean oracle exposes the three exact
coefficients of the degree-two aggregate in `mu`. -/
theorem tableSum_tag73StrengthenedUnmaskedTable
    {K : Type*} [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 → ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K) :
    tableSum (tag73StrengthenedUnmaskedTable basis constraintRows theta
      zerocheckPoint mu helper) =
      constraintMLE basis constraintRows theta zerocheckPoint +
        mu * tableSum helper + mu ^ 2 * inactiveHelperSum helper := by
  classical
  calc
    tableSum (tag73StrengthenedUnmaskedTable basis constraintRows theta
        zerocheckPoint mu helper) =
      tableSum (sourceUnmaskedZerocheckTable basis constraintRows theta
        zerocheckPoint mu helper) +
        tableSum (fun row =>
          mu ^ 2 * deployedCopyInactiveIndicator row * helper row) := by
            simp [tableSum, tag73StrengthenedUnmaskedTable,
              Finset.sum_add_distrib, mul_assoc]
    _ = (constraintMLE basis constraintRows theta zerocheckPoint +
          mu * tableSum helper) +
        mu ^ 2 * inactiveHelperSum helper := by
          rw [tableSum_sourceUnmaskedZerocheckTable,
            tableSum_tag73_inactive_quadratic_term]
    _ = _ := by ring

/-! ## Degree-two aggregate polynomial and collision boundary -/

noncomputable def tag73MuAggregatePolynomial
    {K : Type*} [Field K] (constraintValue totalHelper inactiveHelper : K) :
    Polynomial K :=
  monomialPolynomial ![constraintValue, totalHelper, inactiveHelper]

@[simp] theorem eval_tag73MuAggregatePolynomial
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper mu : K) :
    (tag73MuAggregatePolynomial constraintValue totalHelper inactiveHelper).eval mu =
      constraintValue + mu * totalHelper + mu ^ 2 * inactiveHelper := by
  rw [tag73MuAggregatePolynomial, eval_monomialPolynomial_threeRow]
  simp [threeRowBatch, Fin.sum_univ_succ]
  ring

theorem tag73MuAggregatePolynomial_eq_zero_iff
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper : K) :
    tag73MuAggregatePolynomial constraintValue totalHelper inactiveHelper = 0 ↔
      constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0 := by
  classical
  constructor
  · intro polynomialZero
    have coefficient0 := congrArg (fun polynomial : Polynomial K =>
      polynomial.coeff ((0 : Fin 3) : Nat)) polynomialZero
    have coefficient1 := congrArg (fun polynomial : Polynomial K =>
      polynomial.coeff ((1 : Fin 3) : Nat)) polynomialZero
    have coefficient2 := congrArg (fun polynomial : Polynomial K =>
      polynomial.coeff ((2 : Fin 3) : Nat)) polynomialZero
    exact ⟨by simpa only [tag73MuAggregatePolynomial,
        monomialPolynomial_coeff, Polynomial.coeff_zero, Matrix.cons_val_zero]
        using coefficient0,
      by simpa only [tag73MuAggregatePolynomial,
        monomialPolynomial_coeff, Polynomial.coeff_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero] using coefficient1,
      by
        have coefficient2' :
            (![constraintValue, totalHelper, inactiveHelper] : Fin 3 → K)
              (2 : Fin 3) = 0 := by
          simpa only [tag73MuAggregatePolynomial, monomialPolynomial_coeff,
            Polynomial.coeff_zero] using coefficient2
        exact coefficient2'⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have zeroPolynomial :
        monomialPolynomial (fun _ : Fin 3 => (0 : K)) = 0 := by
      simp [monomialPolynomial]
    rw [tag73MuAggregatePolynomial, ← zeroPolynomial]
    congr 1
    funext index
    fin_cases index <;> rfl

theorem tag73MuAggregatePolynomial_natDegree_le_two
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper : K) :
    (tag73MuAggregatePolynomial constraintValue totalHelper inactiveHelper).natDegree ≤ 2 := by
  simpa [tag73MuAggregatePolynomial] using
    (monomialPolynomial_natDegree_le (K := K) (n := 3) (by decide)
      ![constraintValue, totalHelper, inactiveHelper])

def Tag73MuAggregateCollision
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper mu : K) : Prop :=
  ¬ (constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0) ∧
    (tag73MuAggregatePolynomial constraintValue totalHelper inactiveHelper).eval mu = 0

theorem aggregate_coefficients_zero_outside_collision
    {K : Type*} [Field K]
    (constraintValue totalHelper inactiveHelper mu : K)
    (acceptedAggregate : constraintValue + mu * totalHelper +
      mu ^ 2 * inactiveHelper = 0)
    (outsideCollision : ¬ Tag73MuAggregateCollision
      constraintValue totalHelper inactiveHelper mu) :
    constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0 := by
  by_contra coefficientsNonzero
  apply outsideCollision
  exact ⟨coefficientsNonzero, by
    simpa using acceptedAggregate⟩

section FiniteField

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

noncomputable def tag73MuAggregateCollisionSet
    (constraintValue totalHelper inactiveHelper : K) : Finset K :=
  Finset.univ.filter fun mu =>
    (tag73MuAggregatePolynomial constraintValue totalHelper inactiveHelper).eval mu = 0

theorem tag73_mu_aggregate_collision_card_le_two
    (constraintValue totalHelper inactiveHelper : K)
    (coefficientsNonzero :
      ¬ (constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0)) :
    (tag73MuAggregateCollisionSet constraintValue totalHelper inactiveHelper).card ≤ 2 := by
  let polynomial := tag73MuAggregatePolynomial constraintValue totalHelper inactiveHelper
  have polynomialNonzero : polynomial ≠ 0 := by
    intro polynomialZero
    exact coefficientsNonzero
      ((tag73MuAggregatePolynomial_eq_zero_iff constraintValue totalHelper
        inactiveHelper).mp polynomialZero)
  have subsetRoots :
      (tag73MuAggregateCollisionSet constraintValue totalHelper inactiveHelper).val ⊆
        polynomial.roots := by
    intro mu member
    have evaluationZero := (Finset.mem_filter.mp member).2
    rw [Polynomial.mem_roots polynomialNonzero]
    simpa [Polynomial.IsRoot, polynomial] using evaluationZero
  exact (Polynomial.card_le_degree_of_subset_roots subsetRoots).trans
    (tag73MuAggregatePolynomial_natDegree_le_two constraintValue totalHelper
      inactiveHelper)

noncomputable def uniformTag73MuAggregateCollisionProbability
    (constraintValue totalHelper inactiveHelper : K) : Rat :=
  (tag73MuAggregateCollisionSet constraintValue totalHelper inactiveHelper).card /
    (Fintype.card K : Rat)

theorem uniform_tag73_mu_aggregate_collision_probability_le_two
    (constraintValue totalHelper inactiveHelper : K)
    (coefficientsNonzero :
      ¬ (constraintValue = 0 ∧ totalHelper = 0 ∧ inactiveHelper = 0)) :
    uniformTag73MuAggregateCollisionProbability constraintValue totalHelper
        inactiveHelper ≤
      (2 : Rat) / (Fintype.card K : Rat) := by
  have cardPositive : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  have denominatorPositive : (0 : Rat) < (Fintype.card K : Rat) := by
    exact_mod_cast cardPositive
  rw [uniformTag73MuAggregateCollisionProbability,
    div_le_div_iff_of_pos_right denominatorPositive]
  exact_mod_cast tag73_mu_aggregate_collision_card_le_two
    constraintValue totalHelper inactiveHelper coefficientsNonzero

end FiniteField

/-- Polynomial identity form: all three authenticated aggregate coefficients
are zero, and therefore so is the active helper sum. -/
theorem accepted_aggregate_polynomial_implies_helper_sums_zero
    {K : Type*} [Field K] (constraintValue : K)
    (helper : Fin 1024 → K)
    (acceptedPolynomial : tag73MuAggregatePolynomial constraintValue
      (tableSum helper) (inactiveHelperSum helper) = 0) :
    constraintValue = 0 ∧ tableSum helper = 0 ∧
      inactiveHelperSum helper = 0 ∧ activeHelperSum helper = 0 := by
  have coefficients :=
    (tag73MuAggregatePolynomial_eq_zero_iff constraintValue
      (tableSum helper) (inactiveHelperSum helper)).mp acceptedPolynomial
  exact ⟨coefficients.1, coefficients.2.1, coefficients.2.2,
    activeHelperSum_zero_of_total_and_inactive helper coefficients.2.1
      coefficients.2.2⟩

/-- A verifier-accepted strengthened Boolean-cube sum at sampled `mu` binds
all three aggregate coefficients except on the explicitly named degree-two
collision event.  In particular, random inactive padding remains permitted
cellwise: only its sum is authenticated as zero. -/
theorem strengthened_sum_zero_outside_collision_implies_all_sums_zero
    {K : Type*} [Field K] [Algebra F K]
    (basis : Basis (Fin 4) F K)
    (constraintRows : Fin 1024 → ConstraintRowResiduals (F := F) (K := K))
    (theta : K) (zerocheckPoint : Fin 10 → K)
    (mu : K) (helper : Fin 1024 → K)
    (strengthenedSumZero :
      tableSum (tag73StrengthenedUnmaskedTable basis constraintRows theta
        zerocheckPoint mu helper) = 0)
    (outsideCollision : ¬ Tag73MuAggregateCollision
      (constraintMLE basis constraintRows theta zerocheckPoint)
      (tableSum helper) (inactiveHelperSum helper) mu) :
    constraintMLE basis constraintRows theta zerocheckPoint = 0 ∧
      tableSum helper = 0 ∧ inactiveHelperSum helper = 0 ∧
      activeHelperSum helper = 0 := by
  have aggregateZero :
      constraintMLE basis constraintRows theta zerocheckPoint +
        mu * tableSum helper + mu ^ 2 * inactiveHelperSum helper = 0 := by
    rw [← tableSum_tag73StrengthenedUnmaskedTable]
    exact strengthenedSumZero
  have coefficients := aggregate_coefficients_zero_outside_collision
    (constraintMLE basis constraintRows theta zerocheckPoint)
    (tableSum helper) (inactiveHelperSum helper) mu aggregateZero
    outsideCollision
  exact ⟨coefficients.1, coefficients.2.1, coefficients.2.2,
    activeHelperSum_zero_of_total_and_inactive helper coefficients.2.1
      coefficients.2.2⟩

/-! ## Rational balance with random zero-sum inactive padding -/

theorem copyRationalBalance_zero_of_local_residuals_aggregate
    {K : Type*} [Field K]
    {producerValue consumerValue : RequiredScalarLink → K}
    (source : DeployedCopyRegistryProjection K producerValue consumerValue)
    (lambda chi : K) (helper : Fin 1024 → K)
    (localZero : ∀ row,
      deployedCompiledCopyLane source lambda chi helper row = 0)
    (helperSumZero : tableSum helper = 0)
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole source lambda chi) :
    copyRationalBalance source lambda chi = 0 := by
  classical
  have activePointwise : ∀ row,
      activeHelperPart helper row =
        copyRowRationalContribution (deployedCopyRows source lambda row) chi := by
    intro row
    by_cases active : deployedCopyRowActive row
    · have residualZero :
          copyLocalResidual (deployedCopyRows source lambda row)
            (helper row) chi = 0 := by
        simpa [deployedCompiledCopyLane, active] using localZero row
      have denominators := deployed_row_denominators_ne_zero source lambda chi
        chiNonzero noPole row
      have helperExact := helper_eq_copyRowRationalContribution_of_residual_zero
        (deployedCopyRows source lambda row) (helper row) chi
        (denominators.1 0) (denominators.1 1)
        (denominators.2 0) (denominators.2 1) residualZero
      simpa [activeHelperPart, active] using helperExact
    · rw [copyRowRationalContribution_zero_of_inactive source lambda chi row active]
      simp [activeHelperPart, active]
  have activeSumZero := activeHelperSum_zero_of_total_and_inactive helper
    helperSumZero inactiveSumZero
  rw [← tableSum_copyRowRationalContribution_eq_balance source lambda chi]
  calc
    tableSum (fun row =>
        copyRowRationalContribution (deployedCopyRows source lambda row) chi) =
      activeHelperSum helper := by
        unfold tableSum activeHelperSum
        apply Finset.sum_congr rfl
        intro row _
        exact (activePointwise row).symm
    _ = 0 := activeSumZero

theorem copyRationalBalance_zero_of_accepted_copy_rows_aggregate
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (acceptedRows : ExtractedConstraintRowsVanish statement extraction
      poseidonRows
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper))
    (helperSumZero : tableSum helper = 0)
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi) :
    copyRationalBalance (concreteDeployedCopyRegistryProjection extraction)
      lambda chi = 0 := by
  exact copyRationalBalance_zero_of_local_residuals_aggregate
    (concreteDeployedCopyRegistryProjection extraction) lambda chi helper
    acceptedRows.copy helperSumZero inactiveSumZero chiNonzero noPole

theorem requiredTraceAliases_of_accepted_copy_rows_aggregate
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (statement : V5PublicStatement)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (poseidonRows : Fin 1024 → Fin 4 → Fin 4 → F)
    (lambda chi : QM31Exact) (helper : Fin 1024 → QM31Exact)
    (acceptedRows : ExtractedConstraintRowsVanish statement extraction
      poseidonRows
      (deployedCompiledCopyLane
        (concreteDeployedCopyRegistryProjection extraction)
        lambda chi helper))
    (helperSumZero : tableSum helper = 0)
    (inactiveSumZero : DeployedCopyHelperInactiveSumZero helper)
    (chiNonzero : ¬ DeployedCopyInactiveSlotCollision chi)
    (noPole : ¬ DeployedCopyActivePole
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noChiCollision : ¬ CopyChiCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda chi)
    (noCompressionCollision : ¬ CopyTupleCompressionCollision
      (concreteDeployedCopyRegistryProjection extraction) lambda) :
    RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) := by
  apply requiredTraceAliases_of_deployed_copy_logup extraction
    (concreteDeployedCopyRegistryProjection extraction) lambda chi
  · exact copyRationalBalance_zero_of_accepted_copy_rows_aggregate statement
      extraction poseidonRows lambda chi helper acceptedRows helperSumZero
      inactiveSumZero chiNonzero noPole
  · exact noChiCollision
  · exact noCompressionCollision

#print axioms inactiveHelperPart_eq_zero_of_active
#print axioms inactiveHelperPart_eq_helper_of_inactive
#print axioms helper_sum_eq_active_add_inactive
#print axioms inactiveHelperSum_eq_inactiveRows_sum
#print axioms activeHelperSum_zero_of_total_and_inactive
#print axioms tableSum_tag73_inactive_quadratic_term
#print axioms tableSum_tag73StrengthenedUnmaskedTable
#print axioms eval_tag73MuAggregatePolynomial
#print axioms tag73MuAggregatePolynomial_eq_zero_iff
#print axioms tag73MuAggregatePolynomial_natDegree_le_two
#print axioms aggregate_coefficients_zero_outside_collision
#print axioms tag73_mu_aggregate_collision_card_le_two
#print axioms uniform_tag73_mu_aggregate_collision_probability_le_two
#print axioms accepted_aggregate_polynomial_implies_helper_sums_zero
#print axioms strengthened_sum_zero_outside_collision_implies_all_sums_zero
#print axioms copyRationalBalance_zero_of_local_residuals_aggregate
#print axioms copyRationalBalance_zero_of_accepted_copy_rows_aggregate
#print axioms requiredTraceAliases_of_accepted_copy_rows_aggregate

end AspisPool.V7Tag73InactiveHelperAggregate
