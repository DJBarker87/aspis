import AspisFormal.Pool.V7CombinedCandidateExact
import AspisFormal.Pool.V7PointClaimBatchBinding

/-!
# V7 copy-inactive claim and point-batch separation

The production relation starts with

`inactiveClaim + row0 + kappa * row1 + kappa^2 * row2`.

The inactive term and row zero both have coefficient one.  Random batching
therefore cannot prevent them from cancelling each other.  This file gives
the carried inactive functional its exact binary-mask semantics, proves that
it commutes with the literal twenty-nine-lane gamma batch, and shows that an
authenticated total initial relation claim plus an authenticated inactive
claim yields the standalone point aggregate required by
`V7PointClaimBatchBinding`.

This is deterministic algebra.  Identifying `compiledInactiveMasks` with the
generated Rust row-group table and proving that the successful parser's
`inactiveClaim` was computed from the selected candidate remain explicit
source/Aeneas obligations; neither is disguised as a collision event.
-/

set_option autoImplicit false

namespace AspisPool.V7InactiveClaimBinding

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7CombinedCandidateExact
open AspisPool.V7PointClaimBatchBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6AcceptedPathObligations
open AspisV6OneFoldCandidateExtraction
open AspisV6TranscriptRelationGrammar
open AspisV6Width29CorrelatedAgreement

/-- High six bits of one physical 1,024-row index. -/
def inactiveHigh (row : Fin 1024) : Fin 64 :=
  ⟨row.val / 16, by omega⟩

/-- Low four bits of one physical 1,024-row index. -/
def inactiveLow (row : Fin 1024) : Fin 16 :=
  ⟨row.val % 16, Nat.mod_lt _ (by omega)⟩

/-- Field-valued spelling of the generated binary inactive-row mask. -/
def inactiveWeight {K : Type*} [Zero K] [One K]
    (masks : InactiveMasks) (row : Fin 1024) : K :=
  if masks (inactiveHigh row) (inactiveLow row) then 1 else 0

/-- Exact copy-inactive functional used by the initial relation accumulator. -/
def inactiveClaim {K : Type*} [Semiring K]
    (masks : InactiveMasks) (message : Fin 1024 → K) : K :=
  ∑ row, inactiveWeight masks row * message row

private theorem inactiveClaim_width29Batch
    {K : Type*} [Field K]
    (masks : InactiveMasks)
    (components : Fin 29 → Fin 1024 → K)
    (gamma : K) :
    inactiveClaim masks
        (fun row => width29Batch (fun lane => components lane row) gamma) =
      width29Batch (fun lane => inactiveClaim masks (components lane)) gamma := by
  classical
  calc
    inactiveClaim masks
        (fun row => width29Batch (fun lane => components lane row) gamma) =
        ∑ row : Fin 1024,
        inactiveWeight masks row *
          ∑ lane : Fin 29, components lane row * gamma ^ lane.val := by
      rfl
    _ =
        ∑ row : Fin 1024, ∑ lane : Fin 29,
          inactiveWeight masks row *
            (components lane row * gamma ^ lane.val) := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
    _ = ∑ lane : Fin 29, ∑ row : Fin 1024,
          inactiveWeight masks row *
            (components lane row * gamma ^ lane.val) := by
      rw [Finset.sum_comm]
    _ = ∑ lane : Fin 29,
          (∑ row : Fin 1024,
            inactiveWeight masks row * components lane row) *
              gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = width29Batch
        (fun lane => inactiveClaim masks (components lane)) gamma := by
      rfl

/-- The binary-mask functional is linear over the exact coefficient-level
twenty-nine-lane gamma batch. -/
theorem inactiveClaim_batchInitialMessages
    (masks : InactiveMasks)
    (components : Fin 29 → Fin 1024 → QM31Exact)
    (gamma : QM31Exact) :
    inactiveClaim masks (batchInitialMessages components gamma) =
      width29Batch (fun lane => inactiveClaim masks (components lane)) gamma := by
  unfold batchInitialMessages
  exact inactiveClaim_width29Batch masks components gamma

/-- Under the concrete encoder equality, applying the inactive functional to
the selected combined candidate is exactly the gamma batch of the twenty-nine
component inactive functionals. -/
theorem CoherentTraceExtraction.inactiveClaim_combined_eq_componentBatch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (initialEncoderEq : decoder.initialEncoder = exactInitialEncoder)
    (masks : InactiveMasks) :
    inactiveClaim masks extraction.combined.1 =
      width29Batch
        (fun lane => inactiveClaim masks (extraction.components lane)) gamma := by
  rw [CoherentTraceExtraction.combined_eq_batchInitialMessages extraction
    initialEncoderEq]
  exact inactiveClaim_batchInitialMessages masks extraction.components gamma

/-- The accepted-path initial relation claim decomposes definitionally into
the separately carried inactive scalar and the serialized point aggregate. -/
theorem relationClaimBeforeOod_eq_inactive_add_claimedPointBatch
    (fields : FixedFieldView QM31Exact) (gamma kappa : QM31Exact) :
    relationClaimBeforeOod fields gamma kappa =
      fields.inactiveClaim + claimedPointBatch fields gamma kappa := by
  rfl

/-- Candidate-side value of the same initial relation functional. -/
noncomputable def extractedRelationClaimBeforeOod
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact) : QM31Exact :=
  inactiveClaim masks extraction.combined.1 +
    extractedPointBatch extraction point kappa

/-- Once the total initial relation functional and the inactive functional
are both exact, row zero cannot be cancelled by a forged inactive scalar and
the standalone two-level point aggregate is exact. -/
theorem point_aggregate_exact_of_relation_and_inactive_exact
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (relationExact : relationClaimBeforeOod fields gamma kappa =
      extractedRelationClaimBeforeOod masks extraction point kappa)
    (inactiveExact : fields.inactiveClaim =
      inactiveClaim masks extraction.combined.1) :
    claimedPointBatch fields gamma kappa =
      extractedPointBatch extraction point kappa := by
  rw [relationClaimBeforeOod_eq_inactive_add_claimedPointBatch,
    extractedRelationClaimBeforeOod, inactiveExact] at relationExact
  exact add_left_cancel relationExact

/-- Full deterministic composition: exact initial-relation and inactive
claims plus exclusion of the two explicit batching collisions fix all 87
serialized point claims to the selected component evaluations. -/
theorem all_point_claims_exact_of_relation_and_inactive
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (masks : InactiveMasks)
    (fields : FixedFieldView QM31Exact)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (point : Fin 10 → QM31Exact) (kappa : QM31Exact)
    (relationExact : relationClaimBeforeOod fields gamma kappa =
      extractedRelationClaimBeforeOod masks extraction point kappa)
    (inactiveExact : fields.inactiveClaim =
      inactiveClaim masks extraction.combined.1)
    (noKappaCollision :
      ¬ KappaPointRowCollision fields extraction point kappa)
    (noGammaCollision :
      ¬ GammaPointLaneCollision fields extraction point) :
    ∀ row lane,
      fields.pointClaim row lane =
        componentPointClaim extraction point row lane := by
  apply all_point_claims_exact_outside_collisions fields extraction point kappa
  · exact point_aggregate_exact_of_relation_and_inactive_exact masks fields
      extraction point kappa relationExact inactiveExact
  · exact noKappaCollision
  · exact noGammaCollision

#print axioms inactiveClaim_batchInitialMessages
#print axioms CoherentTraceExtraction.inactiveClaim_combined_eq_componentBatch
#print axioms point_aggregate_exact_of_relation_and_inactive_exact
#print axioms all_point_claims_exact_of_relation_and_inactive

end AspisPool.V7InactiveClaimBinding
