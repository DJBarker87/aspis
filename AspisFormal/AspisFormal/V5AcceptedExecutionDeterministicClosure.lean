import AspisFormal.V5AcceptedExecutionReleasedSecurity

/-!
# Remove proved implementation branches from released acceptance

The released accepted-execution theorem reports every possible failure as a
separate branch.  This file provides the final, deliberately small case split
used once the source relation, transcript, work checks, Merkle opening, and
FRI arithmetic have each been connected to the production verifier.

It does not assume that those connections hold.  Instead, each positive
connection is supplied explicitly and removes exactly its corresponding
negative branch.  Hash collisions and the genuine probabilistic soundness
events remain in the result.
-/

namespace AspisV5AcceptedExecutionDeterministicClosure

open AspisV5AcceptedExecutionReleasedSecurity

/-- Remove exactly the deterministic implementation failures that have been
proved impossible.  Failed reference-forest projection and FRI-arithmetic
branches are not discarded: their bridges may send them to the existing
SHA-256 collision branch.  The remaining outcomes are that collision event
and the mathematical query, FRI, candidate, repair, and Poseidon2 events. -/
theorem remove_proved_implementation_failures_into_collision
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (hsource : ¬ sourceRelationProjectionFailure)
    (hfamily : ¬ familyProjectionFailure)
    (htranscript : ¬ transcriptProjectionFailure)
    (hworkProjection : ¬ workProjectionFailure)
    (hreference : referenceForestFailure → hashCollision)
    (hopening : ¬ rustOpeningCorrespondenceFailure)
    (hworkCheck : ¬ workFailure)
    (hfriArithmetic : friArithmeticFailure → hashCollision)
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      False False False False False False hashCollision False False queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure := by
  cases event with
  | sourceRelationProjection failure => exact (hsource failure).elim
  | familyProjection failure => exact (hfamily failure).elim
  | transcriptProjection failure => exact (htranscript failure).elim
  | workProjection failure => exact (hworkProjection failure).elim
  | releasedFinalDomain failure => exact failure.elim
  | releasedInverseTable failure => exact failure.elim
  | referenceForest failure => exact .merkleHashCollision (hreference failure)
  | globalCausalSelection failure => exact failure.elim
  | rustOpeningCorrespondence failure => exact (hopening failure).elim
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact (hworkCheck failure).elim
  | friArithmetic failure =>
      exact .merkleHashCollision (hfriArithmetic failure)
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact failure.elim

/-- Convenience form when the FRI-arithmetic branch has been proved
impossible outright. -/
theorem remove_proved_implementation_failures
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (hsource : ¬ sourceRelationProjectionFailure)
    (hfamily : ¬ familyProjectionFailure)
    (htranscript : ¬ transcriptProjectionFailure)
    (hworkProjection : ¬ workProjectionFailure)
    (hreference : referenceForestFailure → hashCollision)
    (hopening : ¬ rustOpeningCorrespondenceFailure)
    (hworkCheck : ¬ workFailure)
    (hfriArithmetic : ¬ friArithmeticFailure)
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      False False False False False False hashCollision False False queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure := by
  exact remove_proved_implementation_failures_into_collision
    hsource hfamily htranscript hworkProjection hreference hopening hworkCheck
    (fun failure => (hfriArithmetic failure).elim) event

#print axioms remove_proved_implementation_failures_into_collision
#print axioms remove_proved_implementation_failures

end AspisV5AcceptedExecutionDeterministicClosure
