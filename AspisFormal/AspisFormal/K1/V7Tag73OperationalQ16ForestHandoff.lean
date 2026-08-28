import AspisFormal.K1.V7Tag73Q16SuccessfulForestBridge
import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Operational first-cap-203 search to the successful q16 forest

The finite q16 theorem is phrased over a complete `64 × 8` digest forest,
whereas the literal verifier stores a `FirstCap203Search` and stops after its
first compact candidate.  This module proves the deterministic handoff.

The only codec/source input is `OperationalQ16ForestRealization`: each
actually decoded candidate is identified with the low-18 ideal output of its
routed digest blocks, and the literal frontier recurrence is identified with
the semantic binary-frontier recurrence on those positions.  These are value
equalities, not probability or soundness conclusions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73OperationalQ16ForestHandoff

open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16SuccessfulForestBridge
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Forget only the operational block-count certificate.  The ordered
position injection is byte-for-byte the same semantic schedule used by the
finite probability theorem. -/
def semanticScheduleOfOperational (schedule : QuerySchedule) : Q16Schedule :=
  schedule.positions

/-- Exact deterministic facts supplied by the routed production q16 trace.
The verifier need only realize candidates up to and including the selected
counter; the unused forest suffix is irrelevant. -/
structure OperationalQ16ForestRealization
    (frontierNodes : QuerySchedule → Nat)
    (search : FirstCap203Search frontierNodes)
    (forest : Q16CandidateDigestForest) : Prop where
  decodedExact : ∀ counter schedule,
    counter.val ≤ search.selectedCounter.val →
    search.outcome counter = .schedule schedule →
    q16CandidateOutput (deployedQ16DrawForest forest counter) =
      some (semanticScheduleOfOperational schedule)
  frontierExact : ∀ counter schedule,
    counter.val ≤ search.selectedCounter.val →
    search.outcome counter = .schedule schedule →
    semanticFrontierNodes (semanticScheduleOfOperational schedule) =
      frontierNodes schedule

/-- The operationally selected schedule is semantically admitted. -/
theorem selected_semantic_schedule_admitted
    {frontierNodes : QuerySchedule → Nat}
    {search : FirstCap203Search frontierNodes}
    {forest : Q16CandidateDigestForest}
    (realized : OperationalQ16ForestRealization frontierNodes search forest) :
    SemanticCap203Admitted
      (semanticScheduleOfOperational search.selectedSchedule) := by
  rw [SemanticCap203Admitted,
    realized.frontierExact search.selectedCounter search.selectedSchedule
      (Nat.le_refl _) search.selectedOutcome]
  exact search.selectedCompact

/-- Every earlier operational candidate rejects every semantically admitted
schedule.  This is the exact first-success property needed by
`FirstAdmittedAt`. -/
theorem earlier_operational_candidate_rejects_every_admitted
    {frontierNodes : QuerySchedule → Nat}
    {search : FirstCap203Search frontierNodes}
    {forest : Q16CandidateDigestForest}
    (realized : OperationalQ16ForestRealization frontierNodes search forest)
    (counter : Fin 64) (earlier : counter.val < search.selectedCounter.val) :
    RejectsEveryAdmitted q16CandidateOutput SemanticCap203Admitted
      (deployedQ16DrawForest forest counter) := by
  obtain ⟨schedule, decoded, noncompact⟩ :=
    search.everyEarlierSampledAndNoncompact counter earlier
  have outputExact := realized.decodedExact counter schedule
    (Nat.le_of_lt earlier) decoded
  have frontierExact := realized.frontierExact counter schedule
    (Nat.le_of_lt earlier) decoded
  intro result admitted outputResult
  have resultEq : result = semanticScheduleOfOperational schedule := by
    rw [outputExact] at outputResult
    exact (Option.some.inj outputResult).symm
  rw [resultEq, SemanticCap203Admitted, frontierExact] at admitted
  omega

/-- Construct the literal first-admitted sample represented by one accepted
operational search and the causal router's complete digest forest. -/
def operationalFirstAdmittedSample
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes)
    (forest : Q16CandidateDigestForest)
    (realized : OperationalQ16ForestRealization frontierNodes search forest) :
    FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64 :=
  ⟨⟨semanticScheduleOfOperational search.selectedSchedule,
      selected_semantic_schedule_admitted realized⟩,
    ⟨(search.selectedCounter, deployedQ16DrawForest forest), by
      constructor
      · intro counter earlier
        exact earlier_operational_candidate_rejects_every_admitted realized
          counter earlier
      · exact realized.decodedExact search.selectedCounter
          search.selectedSchedule (Nat.le_refl _) search.selectedOutcome⟩⟩

/-- Therefore the complete routed digest forest is in the successful
conditioning subtype even though the production verifier never executes the
unused suffix after its first compact candidate. -/
theorem operational_realization_implies_q16_digest_forest_succeeds
    {frontierNodes : QuerySchedule → Nat}
    {search : FirstCap203Search frontierNodes}
    {forest : Q16CandidateDigestForest}
    (realized : OperationalQ16ForestRealization frontierNodes search forest) :
    q16DigestForestSucceeds forest := by
  exact ⟨operationalFirstAdmittedSample search forest realized, rfl⟩

/-- The selected first-admitted sample recovered by the canonical successful
forest equivalence is exactly the operational one. -/
theorem successful_forest_equiv_selected_exact
    {frontierNodes : QuerySchedule → Nat}
    {search : FirstCap203Search frontierNodes}
    {forest : Q16CandidateDigestForest}
    (realized : OperationalQ16ForestRealization frontierNodes search forest) :
    (successfulQ16DigestForestEquiv
      ⟨forest,
        operational_realization_implies_q16_digest_forest_succeeds
          realized⟩).2 =
      operationalFirstAdmittedSample search forest realized := by
  apply firstAdmittedSample_eq_of_forest_eq q16CandidateOutput
    SemanticCap203Admitted 64
  change
    (Classical.choose
      (operational_realization_implies_q16_digest_forest_succeeds
        realized)).2.1.2 = deployedQ16DrawForest forest
  exact Classical.choose_spec
    (operational_realization_implies_q16_digest_forest_succeeds realized)

/-- Final deterministic event handoff: if the literal selected operational
schedule lies wholly in a fixed pre-q16 bad set, the successful coordinates
returned by the finite conditioning equivalence lie in its exact bad event. -/
theorem operational_all_in_bad_implies_successful_coordinate_bad
    {frontierNodes : QuerySchedule → Nat}
    {search : FirstCap203Search frontierNodes}
    {forest : Q16CandidateDigestForest}
    (realized : OperationalQ16ForestRealization frontierNodes search forest)
    (bad : Finset (Fin 262144))
    (allBad : AllInBad bad
      (semanticScheduleOfOperational search.selectedSchedule)) :
    successfulQ16DigestForestEquiv
        ⟨forest,
          operational_realization_implies_q16_digest_forest_succeeds
            realized⟩ ∈
      q16SuccessfulCoordinatesBadEvent bad := by
  rw [q16SuccessfulCoordinatesBadEvent, Set.mem_setOf_eq,
    successful_forest_equiv_selected_exact realized]
  exact allBad

end

#print axioms selected_semantic_schedule_admitted
#print axioms earlier_operational_candidate_rejects_every_admitted
#print axioms operationalFirstAdmittedSample
#print axioms operational_realization_implies_q16_digest_forest_succeeds
#print axioms successful_forest_equiv_selected_exact
#print axioms operational_all_in_bad_implies_successful_coordinate_bad

end AspisK1.V7Tag73OperationalQ16ForestHandoff
