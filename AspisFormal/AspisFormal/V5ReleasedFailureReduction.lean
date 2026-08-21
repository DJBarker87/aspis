import AspisFormal.V5AcceptedExecutionReleasedSecurity

/-!
# Removing proved implementation failures from the released event

The released accepted-execution theorem deliberately exposes both real
cryptographic failure events and unfinished code-to-model connections.  Once
the latter have been proved, they should disappear from the theorem rather
than receive an arbitrary probability allowance.

This file provides that final, purely logical step.  It removes exactly the
seven implementation failures supplied as impossible and keeps the seven
cryptographic or protocol events unchanged:

* a Merkle hash collision;
* failure of the work/check relation;
* a query-phase miss;
* the counted FRI bad event;
* an earlier candidate failure;
* the bounded relation-repair event; and
* failure of the stated Poseidon2 connection.

The work/check event is retained separately because a caller may choose to
discharge either its execution projection alone or the complete acceptance
fact.  The theorem below therefore removes seven code/model branches, not the
work-check branch itself.
-/

namespace AspisV5ReleasedFailureReduction

open AspisV5AcceptedExecutionReleasedSecurity

/-- The released event after the seven deterministic implementation
connections have been proved.  No source, transcript, opening, or FRI-value
correspondence failure remains. -/
abbrev ReleasedCryptographicAndProtocolEvent
    (hashCollision : Prop)
    (workFailure : Prop)
    (queryMiss : Prop)
    (countedFriFibre : Prop)
    (candidateTraceFailure : Prop)
    (relationRepair : Prop)
    (poseidonFailure : Prop) : Prop :=
  ReleasedAcceptedExecutionSecurityEvent
    False False False False False False hashCollision workFailure False
      queryMiss countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure

/-- Remove just the source-input and candidate-family projection failures.
This intermediate form is useful before the transcript, opening, and FRI
source proofs have all been composed. -/
theorem remove_released_source_and_family_failures
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure : Prop}
    (hsource : ¬ sourceRelationProjectionFailure)
    (hfamily : ¬ familyProjectionFailure)
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      False False transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure hashCollision
      workFailure friArithmeticFailure queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure := by
  cases event with
  | sourceRelationProjection failure => exact (hsource failure).elim
  | familyProjection failure => exact (hfamily failure).elim
  | transcriptProjection failure => exact .transcriptProjection failure
  | workProjection failure => exact .workProjection failure
  | releasedFinalDomain failure => exact failure.elim
  | releasedInverseTable failure => exact failure.elim
  | referenceForest failure => exact .referenceForest failure
  | globalCausalSelection failure => exact failure.elim
  | rustOpeningCorrespondence failure =>
      exact .rustOpeningCorrespondence failure
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact .workCheck failure
  | friArithmetic failure => exact .friArithmetic failure
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact failure.elim

/-- Eliminate the implementation branches which have exact proofs, preserving
every cryptographic and protocol event without changing its meaning. -/
theorem keep_only_cryptographic_and_protocol_failures
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
    (hreference : ¬ referenceForestFailure)
    (hopening : ¬ rustOpeningCorrespondenceFailure)
    (hfriArithmetic : ¬ friArithmeticFailure)
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      hashCollision workFailure friArithmeticFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure) :
    ReleasedCryptographicAndProtocolEvent hashCollision workFailure queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure := by
  cases event with
  | sourceRelationProjection failure => exact (hsource failure).elim
  | familyProjection failure => exact (hfamily failure).elim
  | transcriptProjection failure => exact (htranscript failure).elim
  | workProjection failure => exact (hworkProjection failure).elim
  | releasedFinalDomain failure => exact failure.elim
  | releasedInverseTable failure => exact failure.elim
  | referenceForest failure => exact (hreference failure).elim
  | globalCausalSelection failure => exact failure.elim
  | rustOpeningCorrespondence failure => exact (hopening failure).elim
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact .workCheck failure
  | friArithmetic failure => exact (hfriArithmetic failure).elim
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact failure.elim

/-- If accepted Rust execution also proves all six work checks, the work
branch disappears as well. -/
theorem keep_only_cryptographic_failures_of_work_acceptance
    {hashCollision workFailure queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure : Prop}
    (hwork : ¬ workFailure)
    (event : ReleasedCryptographicAndProtocolEvent hashCollision workFailure
      queryMiss countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      False False False False False False hashCollision False False queryMiss
      countedFriFibre candidateTraceFailure relationRepair poseidonFailure := by
  cases event with
  | sourceRelationProjection failure => exact failure.elim
  | familyProjection failure => exact failure.elim
  | transcriptProjection failure => exact failure.elim
  | workProjection failure => exact failure.elim
  | releasedFinalDomain failure => exact failure.elim
  | releasedInverseTable failure => exact failure.elim
  | referenceForest failure => exact failure.elim
  | globalCausalSelection failure => exact failure.elim
  | rustOpeningCorrespondence failure => exact failure.elim
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact (hwork failure).elim
  | friArithmetic failure => exact failure.elim
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact failure.elim

#print axioms keep_only_cryptographic_and_protocol_failures
#print axioms keep_only_cryptographic_failures_of_work_acceptance
#print axioms remove_released_source_and_family_failures

end AspisV5ReleasedFailureReduction
