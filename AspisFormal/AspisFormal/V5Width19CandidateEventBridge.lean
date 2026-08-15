import AspisFormal.V5Width19LaneBatchBinding

/-!
# Connecting the width-nineteen event to candidate extraction

`V5Width19LaneBatchBinding` identifies the concrete mismatch bounded by the
published PCS/MCA argument.  This file proves the small event bridge needed by
the accepted-candidate reduction: once a semantic record contains the exact
nineteen source columns, its `CombinedLaneBindingFailure` is precisely that
named event.  Outside the event, the exact candidate projection follows.

This is a deterministic connection theorem.  It does not prove or assume a
numerical PCS/MCA bound.
-/

namespace AspisV5Width19CandidateEventBridge

open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion
open AspisV5Width19LaneBatchBinding

variable {K : Type*} [Field K]

/-- With the exact nineteen source columns in the semantic record, the
candidate's combined-lane failure is exactly the event named by the PCS/MCA
deployment premise. -/
theorem combinedLaneBindingFailure_iff_exact_width19_event
    {Schedule : Type*}
    (event : Schedule -> Prop)
    (gamma : Schedule -> K)
    (columns : Schedule -> Width19Coefficients K)
    (execution : Schedule -> AcceptedCandidateExecution K)
    (record : Schedule -> CandidateSemanticRecord K)
    (exactEvent : ExactWidth19BatchEvent event gamma columns execution)
    (recordLanes : ∀ schedule,
      (record schedule).lanes =
        ensembleOfWidth19Coefficients (gamma schedule) (columns schedule))
    (schedule : Schedule) :
    CombinedLaneBindingFailure (execution schedule) (record schedule) ↔
      event schedule := by
  calc
    CombinedLaneBindingFailure (execution schedule) (record schedule) ↔
        combineWidth19Coefficients (gamma schedule) (columns schedule) ≠
          (execution schedule).initialValues :=
      combinedLaneBindingFailure_iff_width19_candidate_mismatch
        (gamma schedule) (columns schedule) (execution schedule)
        (record schedule) (recordLanes schedule)
    _ ↔ event schedule := (exactEvent schedule).symm

/-- Outside the named PCS/MCA mismatch event, the candidate is exactly the
scalar-power combination of the nineteen source columns. -/
theorem width19CandidateProjection_of_not_event
    {Schedule : Type*}
    (event : Schedule -> Prop)
    (gamma : Schedule -> K)
    (columns : Schedule -> Width19Coefficients K)
    (execution : Schedule -> AcceptedCandidateExecution K)
    (record : Schedule -> CandidateSemanticRecord K)
    (exactEvent : ExactWidth19BatchEvent event gamma columns execution)
    (recordLanes : ∀ schedule,
      (record schedule).lanes =
        ensembleOfWidth19Coefficients (gamma schedule) (columns schedule))
    (schedule : Schedule)
    (outside : ¬ event schedule) :
    Width19CandidateProjection (gamma schedule) (columns schedule)
      (execution schedule) (record schedule) := by
  refine ⟨recordLanes schedule, ?_⟩
  apply Eq.symm
  apply not_ne_iff.mp
  intro mismatch
  exact outside ((exactEvent schedule).mpr mismatch)

/-- Equivalently, excluding the named event rules out the candidate-relative
combined-lane failure without hiding the PCS/MCA premise in the proof. -/
theorem no_combinedLaneBindingFailure_of_not_exact_width19_event
    {Schedule : Type*}
    (event : Schedule -> Prop)
    (gamma : Schedule -> K)
    (columns : Schedule -> Width19Coefficients K)
    (execution : Schedule -> AcceptedCandidateExecution K)
    (record : Schedule -> CandidateSemanticRecord K)
    (exactEvent : ExactWidth19BatchEvent event gamma columns execution)
    (recordLanes : ∀ schedule,
      (record schedule).lanes =
        ensembleOfWidth19Coefficients (gamma schedule) (columns schedule))
    (schedule : Schedule)
    (outside : ¬ event schedule) :
    ¬ CombinedLaneBindingFailure (execution schedule) (record schedule) := by
  rw [combinedLaneBindingFailure_iff_exact_width19_event event gamma columns
    execution record exactEvent recordLanes schedule]
  exact outside

#print axioms combinedLaneBindingFailure_iff_exact_width19_event
#print axioms width19CandidateProjection_of_not_event
#print axioms no_combinedLaneBindingFailure_of_not_exact_width19_event

end AspisV5Width19CandidateEventBridge
