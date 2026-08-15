import AspisFormal.V5FourClaimSourceEquation
import AspisFormal.V5Width19LaneBatchBinding

/-!
# Removing two candidate failures under exact source projections

`V5Tag67CandidateTraceExtraction` deliberately listed six possible failures.
Two are deterministic connection questions rather than new mathematical
soundness events:

* whether the production initial claim/weights use the exact four-claim
  `1,kappa,kappa^2,kappa^3` equation; and
* whether the extracted candidate is the exact degree-eighteen combination of
  the nineteen committed columns.

The first equality is proved by `V5FourClaimSourceEquation` once its source
projection is supplied.  The second is exactly the PCS/MCA projection isolated
by `V5Width19LaneBatchBinding`.  This file composes the two and proves that the
remaining candidate list contains only four alternatives: the cubic
four-claim collision, public-statement binding, arithmetic residual
extraction, or hash/Merkle residual extraction.

No probability is assigned to the source or PCS projections here.
-/

namespace AspisV5CandidateFailureProjection

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5FourClaimSourceEquation
open AspisV5RelationStressSourceBridge
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67RelationListInclusion
open AspisV5Width19LaneBatchBinding

variable {K : Type*} [Field K]

/-- The four candidate-relative failures left after exact source scheduling
and width-nineteen PCS projection. -/
def CandidateFailureAfterSourceAndWidth19
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  FourClaimBatchCollision record ∨
    PublicStatementBindingFailure execution challenges statement record ∨
    ArithmeticResidualFailure execution challenges statement record ∨
    HashMerkleResidualFailure rc execution challenges statement record

/-- Both deterministic projections for one candidate, sharing the exact gamma
decoded by the source-shaped relation caller. -/
structure ExactCandidateSourceProjection
    (data : SourceMode9CallerData K)
    (columns : Width19Coefficients K)
    (execution : AcceptedCandidateExecution K)
    (record : CandidateSemanticRecord K) where
  fourClaim : SourceFourClaimProjection data execution record
  width19 : Width19CandidateProjection data.gamma columns execution record

/-- Under both exact projections, the original six-way list is equivalent to
the four genuine residual/collision alternatives above. -/
theorem candidateEarlierFailure_iff_after_exact_projections
    (rc : RoundConstants)
    (data : SourceMode9CallerData K)
    (columns : Width19Coefficients K)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K)
    (projection : ExactCandidateSourceProjection data columns execution record) :
    CandidateEarlierFailure rc execution challenges statement record ↔
      CandidateFailureAfterSourceAndWidth19 rc execution challenges statement
        record := by
  rw [candidate_earlier_failure_iff_after_source_projection rc data execution
    challenges statement record projection.fourClaim]
  have hlanes : ¬ CombinedLaneBindingFailure execution record :=
    no_combinedLaneBindingFailure_of_width19_projection data.gamma columns
      execution record projection.width19
  simp only [CandidateFailureAfterSourceProjection,
    CandidateFailureAfterSourceAndWidth19]
  tauto

/-- Exact projections can be supplied for every member of the single initial
FRI decoder list.  The source caller data and committed columns are shared;
only the candidate execution and its record vary. -/
structure ExactCandidateFamilySourceProjection
    {Candidate : Type*}
    (data : SourceMode9CallerData K)
    (columns : Width19Coefficients K)
    (family : CoherentCandidateFamily K Candidate)
    (records : CandidateRecords Candidate K) where
  candidate : ∀ member,
    ExactCandidateSourceProjection data columns (family.execution member)
      (records member)

/-- A false public spend makes every list member false once the four remaining
candidate failures are excluded.  The proof reuses the complete spend witness
construction; it does not assume candidate falsity. -/
theorem false_statement_outside_projected_failures
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    {Candidate : Type*}
    (data : SourceMode9CallerData K)
    (columns : Width19Coefficients K)
    (family : CoherentCandidateFamily K Candidate)
    (records : CandidateRecords Candidate K)
    (projection : ExactCandidateFamilySourceProjection data columns family
      records)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode)
    (houtside : ∀ candidate,
      ¬ CandidateFailureAfterSourceAndWidth19 rc
        (family.execution candidate) challenges statement (records candidate)) :
    AllCandidatesFalse family challenges := by
  apply false_statement_outside_all_candidate_failures rc poseidon family
    records challenges statement noWitness
  intro candidate hfailure
  exact houtside candidate
    ((candidateEarlierFailure_iff_after_exact_projections rc data columns
      (family.execution candidate) challenges statement (records candidate)
      (projection.candidate candidate)).mp hfailure)

#print axioms candidateEarlierFailure_iff_after_exact_projections
#print axioms false_statement_outside_projected_failures

end AspisV5CandidateFailureProjection
