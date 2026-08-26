import AspisFormal.Pool.V7SelectedSemanticPointClaims
import AspisFormal.Pool.V7StatementPointCompatibility
import AspisFormal.V6AcceptedPathObligations

/-!
# Exact V7 point-claim batching boundary

The Tag-73 relation carries three rows of twenty-nine point claims.  Each row
is batched with powers of `gamma`, and the three resulting scalars are batched
with `1, kappa, kappa^2`.  This file proves the exact deterministic converse:
outside the named degree-two and degree-twenty-eight collision events, equality
of the two-level aggregate forces all eighty-seven claims to be the literal
multilinear evaluations of the selected width-29 component messages.

The separately carried copy-inactive claim is deliberately absent from the
aggregate defined here.  It has the same coefficient as point row zero in the
production relation.  Consequently, an upstream relation bridge must first
authenticate that inactive functional exactly; otherwise an incorrect
inactive claim could cancel an incorrect row-zero claim without any random
collision.  This module does not hide that requirement in a proposition.

The component tuple may have been selected after `gamma`.  The fixed-vector
root counts below therefore become probability bounds only after the K1
extractor supplies the corresponding pre-challenge/fork consistency.  The
deterministic all-claims theorem itself has no such ordering assumption.
-/

set_option autoImplicit false

namespace AspisPool.V7PointClaimBatchBinding

open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7SelectedSemanticPointClaims
open AspisPool.V7StatementPointCompatibility
open AspisV5ComponentADeployedTerminalApplicability
open AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderApplicability
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29CorrelatedAgreement

/-! ## Generic three-row batching -/

variable {K : Type*} [Field K]

/-- The production three-row scalar-power batch `d0 + kappa*d1 + kappa^2*d2`. -/
def threeRowBatch (values : Fin 3 → K) (kappa : K) : K :=
  ∑ row, values row * kappa ^ row.val

@[simp] theorem eval_monomialPolynomial_threeRow
    (values : Fin 3 → K) (kappa : K) :
    (monomialPolynomial values).eval kappa = threeRowBatch values kappa := by
  simp [monomialPolynomial, threeRowBatch, Polynomial.eval_finsetSum]

theorem threeRowPolynomial_ne_zero
    (values : Fin 3 → K) (nonzero : values ≠ 0) :
    monomialPolynomial values ≠ 0 := by
  intro polynomialZero
  apply nonzero
  apply monomialPolynomial_injective
  simpa [monomialPolynomial] using polynomialZero

theorem threeRowPolynomial_natDegree_le (values : Fin 3 → K) :
    (monomialPolynomial values).natDegree ≤ 2 := by
  simpa using
    (monomialPolynomial_natDegree_le (K := K) (n := 3) (by decide) values)

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- Nonzero challenges at which one fixed nonzero three-row vector cancels. -/
def threeRowNonzeroCollisionSet (values : Fin 3 → K) : Finset K :=
  (Finset.univ.erase 0).filter fun kappa => threeRowBatch values kappa = 0

/-- A fixed nonzero three-row discrepancy has at most two nonzero roots. -/
theorem threeRow_nonzero_collision_card_le_two
    (values : Fin 3 → K) (nonzero : values ≠ 0) :
    (threeRowNonzeroCollisionSet values).card ≤ 2 := by
  let polynomial := monomialPolynomial values
  have polynomialNonzero : polynomial ≠ 0 :=
    threeRowPolynomial_ne_zero values nonzero
  have subsetRoots : (threeRowNonzeroCollisionSet values).val ⊆
      polynomial.roots := by
    intro kappa member
    have batchZero : threeRowBatch values kappa = 0 :=
      (Finset.mem_filter.mp member).2
    rw [Polynomial.mem_roots polynomialNonzero]
    simpa [Polynomial.IsRoot, polynomial] using batchZero
  exact (Polynomial.card_le_degree_of_subset_roots subsetRoots).trans
    (threeRowPolynomial_natDegree_le values)

end FiniteField

/-! ## Exact extracted component evaluations -/

/-- Evaluation of one selected component message at one of the exact three
statement points used by the accepted relation. -/
noncomputable def componentPointClaim
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (row : Fin 3) (lane : Fin 29) :
    QM31Exact :=
  multilinearEvalValue (statementPoint point row)
    (extraction.components lane)

/-- Difference between one serialized point claim and the selected
component's exact multilinear evaluation. -/
noncomputable def pointClaimDiscrepancy
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (row : Fin 3) : Fin 29 → QM31Exact :=
  fun lane => fields.pointClaim row lane -
    componentPointClaim extraction point row lane

/-- One row's twenty-nine discrepancies after production gamma batching. -/
noncomputable def rowGammaDiscrepancy
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (row : Fin 3) : QM31Exact :=
  width29Batch (pointClaimDiscrepancy fields extraction point row) gamma

set_option maxRecDepth 100000 in
/-- A zero row discrepancy is exactly equality between the serialized and
extracted twenty-nine-lane gamma batches. -/
theorem rowGammaDiscrepancy_eq_zero_iff
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (row : Fin 3) :
    rowGammaDiscrepancy fields extraction point row = 0 ↔
      width29Batch (fields.pointClaim row) gamma =
        width29Batch
          (fun lane => componentPointClaim extraction point row lane) gamma := by
  unfold rowGammaDiscrepancy pointClaimDiscrepancy width29Batch
  have difference :
      (∑ lane : Fin 29,
        (fields.pointClaim row lane -
          componentPointClaim extraction point row lane) * gamma ^ lane.val) =
        (∑ lane : Fin 29, fields.pointClaim row lane * gamma ^ lane.val) -
          ∑ lane : Fin 29,
            componentPointClaim extraction point row lane * gamma ^ lane.val := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro lane _
    ring
  rw [difference]
  exact sub_eq_zero

/-- The point-claim part of the initial relation claim as serialized.  The
copy-inactive claim is intentionally excluded and must be authenticated by
the caller before using this equality. -/
def claimedPointBatch
    (fields : FixedFieldView QM31Exact) (gamma kappa : QM31Exact) : QM31Exact :=
  ∑ row : Fin 3,
    pointScale kappa row * gammaCombinedPointClaim fields gamma row

/-- The same two-level aggregate evaluated on the extracted components. -/
noncomputable def extractedPointBatch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact) : QM31Exact :=
  ∑ row : Fin 3, pointScale kappa row *
    width29Batch (fun lane => componentPointClaim extraction point row lane)
      gamma

theorem pointScale_eq_pow (kappa : QM31Exact) (row : Fin 3) :
    pointScale kappa row = kappa ^ row.val := by
  fin_cases row <;> simp [pointScale]

/-- Subtracting the two exact initial point aggregates is precisely the
`kappa` batch of the three row-wise `gamma` discrepancies. -/
theorem claimedPointBatch_sub_extractedPointBatch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact) :
    claimedPointBatch fields gamma kappa -
        extractedPointBatch extraction point kappa =
      threeRowBatch
        (fun row => rowGammaDiscrepancy fields extraction point row) kappa := by
  classical
  unfold claimedPointBatch extractedPointBatch threeRowBatch
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro row _
  have rowDifference :
      rowGammaDiscrepancy fields extraction point row =
        gammaCombinedPointClaim fields gamma row -
          width29Batch
            (fun lane => componentPointClaim extraction point row lane)
            gamma := by
    unfold rowGammaDiscrepancy gammaCombinedPointClaim
      pointClaimDiscrepancy width29Batch
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro lane _
    ring
  rw [pointScale_eq_pow]
  change kappa ^ row.val * gammaCombinedPointClaim fields gamma row -
      kappa ^ row.val *
        width29Batch
          (fun lane => componentPointClaim extraction point row lane) gamma =
    rowGammaDiscrepancy fields extraction point row * kappa ^ row.val
  rw [rowDifference]
  ring

/-! ## The two exact collision events -/

/-- The three row-wise gamma batches are not all zero, but their degree-two
batch vanishes at the sampled `kappa`. -/
def KappaPointRowCollision
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact) : Prop :=
  (fun row => rowGammaDiscrepancy fields extraction point row) ≠ 0 ∧
    threeRowBatch
      (fun row => rowGammaDiscrepancy fields extraction point row) kappa = 0

/-- At least one nonzero twenty-nine-lane discrepancy vector vanishes under
the sampled gamma. -/
def GammaPointLaneCollision
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) : Prop :=
  ∃ row : Fin 3,
    pointClaimDiscrepancy fields extraction point row ≠ 0 ∧
      rowGammaDiscrepancy fields extraction point row = 0

/-- A K1.4 certificate that already fixes all 87 point claims makes the local
post-selected gamma-collision branch impossible. -/
theorem gamma_point_lane_collision_impossible_of_all_claims_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact)
    (allExact : ∀ row lane,
      fields.pointClaim row lane =
        componentPointClaim extraction point row lane) :
    ¬ GammaPointLaneCollision fields extraction point := by
  rintro ⟨row, discrepancyNonzero, _batchZero⟩
  apply discrepancyNonzero
  funext lane
  exact sub_eq_zero.mpr (allExact row lane)

/-- Exact aggregate equality and absence of the degree-two `kappa` collision
force all three row-wise gamma batches to zero.  This is the information a
restoration-wide point-compatible response needs; it does not yet assert that
the twenty-nine claims inside each row are individually exact. -/
theorem every_row_gamma_discrepancy_zero_of_aggregate_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (aggregateExact : claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa)
    (noKappaCollision : ¬ KappaPointRowCollision fields extraction point kappa) :
    (fun row => rowGammaDiscrepancy fields extraction point row) = 0 := by
  have rowBatchZero :
      threeRowBatch
        (fun row => rowGammaDiscrepancy fields extraction point row) kappa = 0 := by
    rw [← claimedPointBatch_sub_extractedPointBatch]
    exact sub_eq_zero.mpr aggregateExact
  by_contra nonzero
  exact noKappaCollision ⟨nonzero, rowBatchZero⟩

/-- Outside the exact degree-two and degree-twenty-eight collision events,
one aggregate equality fixes every serialized point claim individually. -/
theorem all_point_claims_exact_outside_collisions
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (aggregateExact : claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa)
    (noKappaCollision : ¬ KappaPointRowCollision fields extraction point kappa)
    (noGammaCollision : ¬ GammaPointLaneCollision fields extraction point) :
    ∀ row lane,
      fields.pointClaim row lane =
        componentPointClaim extraction point row lane := by
  have everyRowBatchZero :
      (fun row => rowGammaDiscrepancy fields extraction point row) = 0 := by
    exact every_row_gamma_discrepancy_zero_of_aggregate_exact fields extraction
      point kappa aggregateExact noKappaCollision
  intro row lane
  have thisRowBatchZero :
      rowGammaDiscrepancy fields extraction point row = 0 := by
    exact congrFun everyRowBatchZero row
  have thisRowExact :
      pointClaimDiscrepancy fields extraction point row = 0 := by
    by_contra nonzero
    exact noGammaCollision ⟨row, nonzero, thisRowBatchZero⟩
  have laneZero := congrFun thisRowExact lane
  exact sub_eq_zero.mp laneZero

/-- In particular, the first sixteen terminal lanes are the MLEs of the
literal extracted M31 semantic trace at the deployed three points. -/
theorem semantic_point_claims_exact_outside_collisions
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (aggregateExact : claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa)
    (noKappaCollision : ¬ KappaPointRowCollision fields extraction point kappa)
    (noGammaCollision : ¬ GammaPointLaneCollision fields extraction point) :
    ∀ row : Fin 3, ∀ lane : Fin 16,
      fields.pointClaim row
          (c1LaneIndex (semanticColumnIndex lane)) =
        selectedSemanticPointClaim extraction point row lane := by
  intro row lane
  rw [all_point_claims_exact_outside_collisions fields extraction point kappa
    aggregateExact noKappaCollision noGammaCollision]
  unfold componentPointClaim
  rw [statementPoint_eq_deployedRelationPoint]
  exact (selectedSemanticPointClaim_eq_componentEvaluation
    extraction point row lane).symm

/-! ## Fixed-vector root-count surfaces -/

theorem fixed_kappa_collision_set_card_le_two
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact)
    (nonzero : (fun row =>
      rowGammaDiscrepancy fields extraction point row) ≠ 0) :
    (threeRowNonzeroCollisionSet (fun row =>
      rowGammaDiscrepancy fields extraction point row)).card ≤ 2 :=
  threeRow_nonzero_collision_card_le_two _ nonzero

theorem fixed_gamma_collision_set_card_le_twenty_eight
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (row : Fin 3)
    (nonzero : pointClaimDiscrepancy fields extraction point row ≠ 0) :
    (width29NonzeroCollisionSet
      (pointClaimDiscrepancy fields extraction point row)).card ≤ 28 :=
  width29_nonzero_collision_card_le _ nonzero

#print axioms threeRow_nonzero_collision_card_le_two
#print axioms claimedPointBatch_sub_extractedPointBatch
#print axioms rowGammaDiscrepancy_eq_zero_iff
#print axioms gamma_point_lane_collision_impossible_of_all_claims_exact
#print axioms every_row_gamma_discrepancy_zero_of_aggregate_exact
#print axioms all_point_claims_exact_outside_collisions
#print axioms semantic_point_claims_exact_outside_collisions
#print axioms fixed_kappa_collision_set_card_le_two
#print axioms fixed_gamma_collision_set_card_le_twenty_eight

end AspisPool.V7PointClaimBatchBinding
