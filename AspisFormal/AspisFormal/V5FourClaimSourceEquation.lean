import AspisFormal.V5RelationStressSourceBridge
import AspisFormal.V5Tag67CandidateTraceExtraction
import AspisFormal.V5PreparedPointClaimsSourceBridge

/-!
# Exact source-shaped four-claim equation

The production relation caller starts with one separately carried inactive
claim and four point claims scaled by `1`, `kappa`, `kappa^2`, and `kappa^3`.
This file proves the corresponding discrepancy equation.  It then states the
small source projection needed to rule out `FourClaimBatchEquationFailure`.

The theorem is deterministic.  It does not assume that `kappa` is random and
does not use the cubic collision bound.
-/

namespace AspisV5FourClaimSourceEquation

open AspisV5RelationStressSourceBridge
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion
open AspisV5FriRelationCandidateBridge
open AspisV5FunctionalBatching
open AspisV5RelationSumcheckSoundness

variable {K : Type*} [Field K]

/-! ## The two maintained point-claim presentations agree -/

/-- The point-claim model used by the extracted decoder package is the same
nineteen-lane dot used by the relation caller model. -/
theorem prepared_bridge_point_claim_eq_relation_bridge
    (gamma : K) (claims : Fin 76 → K)
    (point : AspisV5ComponentCPreProjectionDeployed.PointClaimRow) :
    AspisV5PreparedPointClaimsSourceBridge.sourcePreparedPointClaim
        gamma claims point =
      AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
        gamma claims point := by
  rw [AspisV5PreparedPointClaimsSourceBridge.sourcePreparedPointClaim_eq_sourcePointClaim,
    AspisV5RelationStressSourceBridge.sourcePreparedPointClaim_eq_sourcePointClaim]
  rfl

theorem prepared_bridge_all_point_claims_eq_relation_bridge
    (gamma : K) (claims : Fin 76 → K) :
    AspisV5PreparedPointClaimsSourceBridge.sourcePreparedPointClaims
        gamma claims =
      AspisV5RelationStressSourceBridge.sourcePreparedPointClaims
        gamma claims := by
  funext point
  exact prepared_bridge_point_claim_eq_relation_bridge gamma claims point

/-- The exact initial covector assembled from the inactive functional and the
four point-opening functionals. -/
def sourceFourClaimInitialWeights
    (kappa : K)
    (inactiveWeights : Fin 1024 → K)
    (pointWeights : Fin 4 → Fin 1024 → K) : Fin 1024 → K :=
  fun row =>
    inactiveWeights row + pointWeights 0 row +
      kappa * pointWeights 1 row +
      kappa ^ 2 * pointWeights 2 row +
      kappa ^ 3 * pointWeights 3 row

theorem candidateClaim_scale_weights
    (scale : K) (weights values : Fin 1024 → K) :
    candidateClaim (fun row => scale * weights row) values =
      scale * candidateClaim weights values := by
  simp only [candidateClaim, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  ring

theorem candidateClaim_sourceFourClaimInitialWeights
    (kappa : K)
    (inactiveWeights : Fin 1024 → K)
    (pointWeights : Fin 4 → Fin 1024 → K)
    (values : Fin 1024 → K) :
    candidateClaim
        (sourceFourClaimInitialWeights kappa inactiveWeights pointWeights)
        values =
      candidateClaim inactiveWeights values +
      candidateClaim (pointWeights 0) values +
        kappa * candidateClaim (pointWeights 1) values +
        kappa ^ 2 * candidateClaim (pointWeights 2) values +
        kappa ^ 3 * candidateClaim (pointWeights 3) values := by
  simp only [sourceFourClaimInitialWeights, candidateClaim, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  have h1 :
      (∑ row, values row * (kappa * pointWeights 1 row)) =
        ∑ row, kappa * (values row * pointWeights 1 row) := by
    apply Finset.sum_congr rfl
    intro row _
    ring
  have h2 :
      (∑ row, values row * (kappa ^ 2 * pointWeights 2 row)) =
        ∑ row, kappa ^ 2 * (values row * pointWeights 2 row) := by
    apply Finset.sum_congr rfl
    intro row _
    ring
  have h3 :
      (∑ row, values row * (kappa ^ 3 * pointWeights 3 row)) =
        ∑ row, kappa ^ 3 * (values row * pointWeights 3 row) := by
    apply Finset.sum_congr rfl
    intro row _
    ring
  rw [h1, h2, h3]

/-- Once the inactive scalar is the dot product of its functional, the initial
relation discrepancy is exactly the scalar-power batch of the four point
claim discrepancies. -/
theorem source_initial_discrepancy_eq_four_claim_batch
    (inactiveClaim kappa gamma : K)
    (claims : Fin 76 → K)
    (inactiveWeights : Fin 1024 → K)
    (pointWeights : Fin 4 → Fin 1024 → K)
    (values : Fin 1024 → K)
    (hinactive : inactiveClaim = candidateClaim inactiveWeights values) :
    sourceCallerInitialClaim inactiveClaim kappa gamma claims -
        candidateClaim
          (sourceFourClaimInitialWeights kappa inactiveWeights pointWeights)
          values =
      batchedDiscrepancy
        (fun point =>
          sourcePreparedPointClaim gamma claims point -
            candidateClaim (pointWeights point) values)
        kappa := by
  rw [candidateClaim_sourceFourClaimInitialWeights, hinactive]
  have hpoint0 : sourcePoint0 = (0 : Fin 4) := by rfl
  have hpoint1 : sourcePoint1 = (1 : Fin 4) := by rfl
  have hpoint2 : sourcePoint2 = (2 : Fin 4) := by rfl
  have hpoint3 : sourcePoint3 = (3 : Fin 4) := by rfl
  simp only [sourceCallerInitialClaim, batchedDiscrepancy, hpoint0, hpoint1,
    hpoint2, hpoint3]
  ring

/-- The smallest field-level projection needed from the production initial
claim and covector construction.  Byte decoding and Rust equality are kept
outside this structure. -/
structure SourceFourClaimProjection
    (data : SourceMode9CallerData K)
    (execution : AcceptedCandidateExecution K)
    (record : CandidateSemanticRecord K) where
  inactiveWeights : Fin 1024 → K
  pointWeights : Fin 4 → Fin 1024 → K
  initialClaim : execution.initialClaim =
    sourceCallerInitialClaim data.inactiveClaim data.kappa data.gamma
      data.pointMajorClaims
  initialWeights : execution.initialWeights =
    sourceFourClaimInitialWeights data.kappa inactiveWeights pointWeights
  inactiveClaim : data.inactiveClaim =
    candidateClaim inactiveWeights execution.initialValues
  recordKappa : record.kappa = data.kappa
  recordDiscrepancy : ∀ point,
    record.fourClaimDiscrepancy point =
      sourcePreparedPointClaim data.gamma data.pointMajorClaims point -
        candidateClaim (pointWeights point) execution.initialValues

/-- The source projection makes the candidate's initial discrepancy exactly
the maintained four-claim batch. -/
theorem initial_discrepancy_eq_batch_of_source_projection
    (data : SourceMode9CallerData K)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (record : CandidateSemanticRecord K)
    (projection : SourceFourClaimProjection data execution record) :
    (execution.discrepancyTrace challenges).before 0 =
      batchedDiscrepancy record.fourClaimDiscrepancy record.kappa := by
  have hsource := source_initial_discrepancy_eq_four_claim_batch
    data.inactiveClaim data.kappa data.gamma data.pointMajorClaims
    projection.inactiveWeights projection.pointWeights execution.initialValues
    projection.inactiveClaim
  rw [← projection.initialClaim, ← projection.initialWeights] at hsource
  rw [projection.recordKappa]
  convert hsource using 1
  · simp [AcceptedCandidateExecution.discrepancyTrace]
  · congr 1
    funext point
    exact projection.recordDiscrepancy point

/-- Therefore the separately named batch-equation failure is impossible once
the exact source projection is available. -/
theorem no_four_claim_batch_equation_failure_of_source_projection
    (data : SourceMode9CallerData K)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (record : CandidateSemanticRecord K)
    (projection : SourceFourClaimProjection data execution record) :
    ¬ FourClaimBatchEquationFailure execution challenges record := by
  intro failure
  exact failure.2
    (initial_discrepancy_eq_batch_of_source_projection data execution
      challenges record projection)

/-- Once the source projection is supplied, the earlier-failure list no
longer needs a separate batch-equation branch. -/
def CandidateFailureAfterSourceProjection
    (rc : AspisFormal.HashMerkleModel.RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : AspisV5AcceptedSpendRelation.V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  FourClaimBatchCollision record ∨
    CombinedLaneBindingFailure execution record ∨
    PublicStatementBindingFailure execution challenges statement record ∨
    ArithmeticResidualFailure execution challenges statement record ∨
    HashMerkleResidualFailure rc execution challenges statement record

theorem candidate_earlier_failure_iff_after_source_projection
    (rc : AspisFormal.HashMerkleModel.RoundConstants)
    (data : SourceMode9CallerData K)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : AspisV5AcceptedSpendRelation.V5PublicStatement)
    (record : CandidateSemanticRecord K)
    (projection : SourceFourClaimProjection data execution record) :
    CandidateEarlierFailure rc execution challenges statement record ↔
      CandidateFailureAfterSourceProjection rc execution challenges statement
        record := by
  have hequation := no_four_claim_batch_equation_failure_of_source_projection
    data execution challenges record projection
  simp only [CandidateEarlierFailure, CandidateFailureAfterSourceProjection]
  tauto

#print axioms candidateClaim_scale_weights
#print axioms prepared_bridge_point_claim_eq_relation_bridge
#print axioms prepared_bridge_all_point_claims_eq_relation_bridge
#print axioms candidateClaim_sourceFourClaimInitialWeights
#print axioms source_initial_discrepancy_eq_four_claim_batch
#print axioms initial_discrepancy_eq_batch_of_source_projection
#print axioms no_four_claim_batch_equation_failure_of_source_projection
#print axioms candidate_earlier_failure_iff_after_source_projection

end AspisV5FourClaimSourceEquation
