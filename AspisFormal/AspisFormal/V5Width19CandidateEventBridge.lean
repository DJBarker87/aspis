import AspisFormal.V5Width19CorrelatedAgreement

/-!
# Connecting the width-nineteen family event to candidate extraction

The elementary fixed-candidate equality below is useful algebra, but its
existential union over a decoder list is not a rare event.  If the list
contains two different candidates, one fixed combined word must disagree with
at least one of them for every batching challenge.

The accepted-false accounting therefore uses a different interface:
`Width19ProjectionOutsideFamilyFailure`.  Its event is the correlated family
failure from `V5Width19CorrelatedAgreement`: some eligible nearby response has
no matching decomposition into the nineteen committed words on its own
agreement support.  Outside that one family event, every candidate used by the
reduction must have the exact source projection.

This file proves only the deterministic implication from that projection to
the absence of `CombinedLaneBindingFailure`.  The curve-decoding cardinality
bound and its prefix-conditioned sampling connection are applied separately in
`V5RefinedWidth19DeploymentBridge`.  The sole remaining released-code seam in
this module is `encodedMessageEqualityOutsideFailure`: the extractor must show
that the accepted candidate codeword equals the encoding of the extracted
nineteen-message combination outside the same CAT family event.
-/

namespace AspisV5Width19CandidateEventBridge

open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion
open AspisV5FriCoherentCandidateExtraction
open AspisV5Width19CorrelatedAgreement
open AspisV5Width19LaneBatchBinding

variable {K : Type*} [Field K]

/-- Fixed-candidate algebra only.  This theorem must not be existentially
unioned over a decoder list and then treated as the correlated-agreement rare
event. -/
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

/-- Fixed-candidate algebra only: outside an event defined to be that one
candidate's mismatch, the candidate is the scalar-power combination. -/
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

/-- Fixed-candidate form of the same implication. -/
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

/-! ## The event interface used by accepted-false accounting -/

/-- Coefficient message represented by one degree-below-1024 polynomial. -/
abbrev Width19CoefficientMessage (K : Type*) := Fin 1024 → K

/-- The initial committed words are evaluated on the full `2^19` circle-code
domain.  This must not be identified definitionally with the coefficient
message above. -/
abbrev Width19ReceivedCoordinate := Fin 524288

/-- Explicit map from a 1024-coefficient message to its `2^19` received-word
codeword. -/
abbrev Width19LinearEncoder (K : Type*) [Field K] :=
  Width19CoefficientMessage K →ₗ[K] (Width19ReceivedCoordinate → K)

/-- The generic message-space scalar combination is the same nineteen-lane
combination used by the release's coefficient representation. -/
theorem combineWidth19Messages_eq_combineWidth19Coefficients
    (gamma : K) (columns : Width19Coefficients K) :
    combineWidth19Messages gamma columns =
      combineWidth19Coefficients gamma columns := by
  funext row
  rw [combineWidth19Coefficients_apply]
  simp [combineWidth19Messages, Fin.sum_univ_succ]
  ring

/-- A matching CAT decomposition yields actual coefficient messages.  The
step from equality of `2^19`-coordinate codewords to equality of
`Fin 1024` messages is exactly the encoder-injectivity argument inside
`candidate_eq_combineWidth19Messages_of_matching`; it is not a definitional
identification of the two domains. -/
theorem matching_decomposition_extracts_coefficient_messages
    [Fintype K] [DecidableEq K]
    (encoder : Width19LinearEncoder K)
    (encoderInjective : Function.Injective encoder)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (strategy : Width19ProximateStrategy K Width19ReceivedCoordinate
      (Width19CoefficientMessage K))
    (gamma : K)
    (execution : AcceptedCandidateExecution K)
    (candidateMessage : strategy.candidate gamma = execution.initialValues)
    (matching : HasMatchingWidth19Decomposition encoder receivedLanes strategy
      gamma) :
    ∃ components : Fin 19 → Width19CoefficientMessage K,
      strategy.support gamma ⊆
          width19JointAgreementSet encoder receivedLanes components ∧
      execution.initialValues = combineWidth19Messages gamma components := by
  obtain ⟨components, support, candidate⟩ :=
    candidate_eq_combineWidth19Messages_of_matching encoder encoderInjective
      receivedLanes strategy gamma matching
  refine ⟨components, support, ?_⟩
  exact candidateMessage.symm.trans candidate

/-- Outside the actual candidate-family bad event, any eligible valid member
has a matching decomposition and therefore yields nineteen coefficient
messages whose scalar combination is the accepted initial message. -/
theorem candidate_family_member_extracts_coefficient_messages_outside_failure
    [Fintype K] [DecidableEq K]
    {Candidate : Type*} [Nonempty Candidate]
    (encoder : Width19LinearEncoder K)
    (encoderInjective : Function.Injective encoder)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (eligible : K → Candidate → Prop)
    (candidateMessage : Candidate → Width19CoefficientMessage K)
    (support : K → Candidate → Finset Width19ReceivedCoordinate)
    (gamma : K) (candidate : Candidate)
    (execution : AcceptedCandidateExecution K)
    (messageMatches : candidateMessage candidate = execution.initialValues)
    (outside : ¬ Width19CandidateFamilyBadAt encoder agreementCap0
      receivedLanes eligible candidateMessage support gamma)
    (isEligible : eligible gamma candidate)
    (isValid : Width19CandidateValid encoder agreementCap0 receivedLanes
      candidateMessage support gamma candidate) :
    ∃ components : Width19Coefficients K,
      support gamma candidate ⊆
          width19JointAgreementSet encoder receivedLanes components ∧
      execution.initialValues =
        combineWidth19Coefficients gamma components := by
  have matching : Width19CandidateHasMatchingDecomposition encoder
      receivedLanes candidateMessage support gamma candidate := by
    by_contra missing
    exact outside ⟨candidate, isEligible, isValid, missing⟩
  let strategy : Width19ProximateStrategy K Width19ReceivedCoordinate
      (Width19CoefficientMessage K) := {
    candidate := fun challenge ↦ candidateMessage candidate
    support := fun challenge ↦ support challenge candidate
  }
  have matchingStrategy : HasMatchingWidth19Decomposition encoder receivedLanes
      strategy gamma := by
    exact matching
  obtain ⟨components, joint, combined⟩ :=
    matching_decomposition_extracts_coefficient_messages encoder
      encoderInjective receivedLanes strategy gamma execution messageMatches
      matchingStrategy
  refine ⟨components, joint, ?_⟩
  exact combined.trans
    (combineWidth19Messages_eq_combineWidth19Coefficients gamma components)

/-- Outside one correlated decoder-family failure event, every candidate used
by the reduction has the exact nineteen-column projection.  The structure
stores the codeword equation first and derives coefficient-message equality
only through the supplied injective linear encoder.

The event is intentionally supplied on the experiment outcomes rather than
defined as an existential fixed-vector mismatch.  A constructor for a release
must obtain `encodedMessageEqualityOutsideFailure` from a valid-response and
matching-decomposition theorem for the same CAT event. -/
structure Width19ProjectionOutsideFamilyFailure
    {Schedule : Type*}
    (familyFailure : Schedule → Prop)
    (gamma : Schedule → K)
    (columns : Schedule → Width19Coefficients K)
    (execution : Schedule → AcceptedCandidateExecution K)
    (record : Schedule → CandidateSemanticRecord K) where
  encoder : Schedule → Width19LinearEncoder K
  encoderInjective : ∀ schedule, Function.Injective (encoder schedule)
  recordLanes : ∀ schedule,
    (record schedule).lanes =
      ensembleOfWidth19Coefficients (gamma schedule) (columns schedule)
  encodedMessageEqualityOutsideFailure : ∀ schedule,
    ¬ familyFailure schedule →
      encoder schedule (execution schedule).initialValues =
        encoder schedule
          (combineWidth19Coefficients (gamma schedule) (columns schedule))

/-- The explicit encoder step produces the coefficient-level projection used
by the semantic extraction proof. -/
theorem Width19ProjectionOutsideFamilyFailure.projection
    {Schedule : Type*}
    {familyFailure : Schedule → Prop}
    {gamma : Schedule → K}
    {columns : Schedule → Width19Coefficients K}
    {execution : Schedule → AcceptedCandidateExecution K}
    {record : Schedule → CandidateSemanticRecord K}
    (connection : Width19ProjectionOutsideFamilyFailure familyFailure gamma
      columns execution record)
    (schedule : Schedule) (outside : ¬ familyFailure schedule) :
    Width19CandidateProjection (gamma schedule) (columns schedule)
      (execution schedule) (record schedule) := by
  refine ⟨connection.recordLanes schedule, ?_⟩
  exact connection.encoderInjective schedule
    (connection.encodedMessageEqualityOutsideFailure schedule outside)

/-- Once the correlated family event is connected to exact projections,
candidate-relative combined-lane failure can occur only inside that event. -/
theorem combinedLaneBindingFailure_implies_familyFailure
    {Schedule : Type*}
    (familyFailure : Schedule → Prop)
    (gamma : Schedule → K)
    (columns : Schedule → Width19Coefficients K)
    (execution : Schedule → AcceptedCandidateExecution K)
    (record : Schedule → CandidateSemanticRecord K)
    (projection : Width19ProjectionOutsideFamilyFailure familyFailure gamma
      columns execution record)
    (schedule : Schedule)
    (failure : CombinedLaneBindingFailure
      (execution schedule) (record schedule)) :
    familyFailure schedule := by
  by_contra outside
  exact (no_combinedLaneBindingFailure_of_width19_projection
    (gamma schedule) (columns schedule) (execution schedule) (record schedule)
    (projection.projection schedule outside)) failure

#print axioms combinedLaneBindingFailure_iff_exact_width19_event
#print axioms width19CandidateProjection_of_not_event
#print axioms no_combinedLaneBindingFailure_of_not_exact_width19_event
#print axioms combineWidth19Messages_eq_combineWidth19Coefficients
#print axioms matching_decomposition_extracts_coefficient_messages
#print axioms
  candidate_family_member_extracts_coefficient_messages_outside_failure
#print axioms Width19ProjectionOutsideFamilyFailure.projection
#print axioms combinedLaneBindingFailure_implies_familyFailure

end AspisV5Width19CandidateEventBridge
