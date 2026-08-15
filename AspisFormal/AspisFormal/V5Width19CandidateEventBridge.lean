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
  change (∑ lane : Fin 19, gamma ^ lane.val * columns lane row) = _
  simp [Fin.sum_univ_succ]
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

/-! ## Exact candidate data used by the production reduction

The verifier does not construct a decoder list at runtime.  Candidate
eligibility, messages and agreement supports are mathematical objects derived
from the authenticated initial word.  The definitions below make that
derivation deterministic, instead of leaving four unrelated functions to a
release instantiation. -/

/-- Exact agreement support of one coefficient message against the
gamma-combined nineteen received words. -/
noncomputable def productionCandidateSupport
    (encoder : Width19LinearEncoder K)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (gamma : K) (candidate : Width19CoefficientMessage K) :
    Finset Width19ReceivedCoordinate := by
  classical
  exact Finset.univ.filter fun coordinate ↦
    width19CurveValue receivedLanes gamma coordinate =
      encoder candidate coordinate

/-- A candidate is eligible exactly when its exact agreement support exceeds
the released layer-zero threshold. -/
def productionCandidateEligible
    (encoder : Width19LinearEncoder K)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (gamma : K) (candidate : Width19CoefficientMessage K) : Prop :=
  agreementCap0 <
    (productionCandidateSupport encoder receivedLanes gamma candidate).card

/-- The candidate message supplied to correlated agreement is the candidate
coefficient vector itself; no Rust-side candidate record is invented. -/
def productionCandidateMessage
    (candidate : Width19CoefficientMessage K) :
    Width19CoefficientMessage K := candidate

/-- With the exact support above, validity is precisely eligibility: the
pointwise agreement half follows from membership in that support. -/
theorem production_candidate_valid_iff_eligible
    (encoder : Width19LinearEncoder K)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (gamma : K) (candidate : Width19CoefficientMessage K) :
    Width19CandidateValid encoder agreementCap0 receivedLanes
        productionCandidateMessage
        (fun challenge message ↦
          productionCandidateSupport encoder receivedLanes challenge message)
        gamma candidate ↔
      productionCandidateEligible encoder receivedLanes gamma candidate := by
  classical
  constructor
  · intro valid
    exact valid.1
  · intro eligible
    refine ⟨eligible, ?_⟩
    intro coordinate hcoordinate
    simpa [productionCandidateSupport, productionCandidateMessage] using
      (Finset.mem_filter.mp hcoordinate).2

/-- Replace only the initial word of an ideal transcript by the exact
gamma-combination of the nineteen authenticated words. -/
def transcriptAtWidth19Challenge
    (template : IdealTranscript K)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (gamma : K) : IdealTranscript K :=
  { template with layer0 := width19CurveValue receivedLanes gamma }

/-- Replace only the initial encoder by the exact released linear encoder. -/
def encodersWithWidth19Layer0
    (template : CodeEncoders K) (encoder : Width19LinearEncoder K) :
    CodeEncoders K :=
  { template with layer0 := encoder }

/-- Membership in the actual initial decoder list is exactly the eligibility
predicate above.  This closes the former independent choices of eligibility,
message and support at the ideal-transcript boundary. -/
theorem mem_initialCandidateList_iff_productionCandidateEligible
    [Fintype K] [DecidableEq K]
    (encoder : Width19LinearEncoder K)
    (encoderTemplate : CodeEncoders K)
    (transcriptTemplate : IdealTranscript K)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (gamma : K) (candidate : Width19CoefficientMessage K) :
    candidate ∈ initialCandidateList
        (encodersWithWidth19Layer0 encoderTemplate encoder)
        (transcriptAtWidth19Challenge transcriptTemplate receivedLanes gamma) ↔
      productionCandidateEligible encoder receivedLanes gamma candidate := by
  classical
  have supportEquality :
      agreementSet (width19CurveValue receivedLanes gamma)
          (encoder candidate) =
        productionCandidateSupport encoder receivedLanes gamma candidate := by
    apply Finset.ext
    intro coordinate
    simp [agreementSet, productionCandidateSupport]
  rw [mem_initialCandidateList_iff]
  change agreementCap0 <
      (agreementSet (width19CurveValue receivedLanes gamma)
        (encoder candidate)).card ↔
    productionCandidateEligible encoder receivedLanes gamma candidate
  rw [supportEquality]
  rfl

/-- Assemble the semantic record once correlated agreement has supplied the
nineteen coefficient messages.  The opened statement fields and four claim
discrepancies come from the separate relation/source projection. -/
def productionCandidateRecord
    (gamma : K) (columns : Width19Coefficients K)
    (opened : AspisFormal.ArithmetizationCore.OpenedColumns)
    (fourClaimDiscrepancy : Fin 4 → K) (kappa : K) :
    CandidateSemanticRecord K where
  lanes := ensembleOfWidth19Coefficients gamma columns
  opened := opened
  fourClaimDiscrepancy := fourClaimDiscrepancy
  kappa := kappa

@[simp] theorem productionCandidateRecord_lanes
    (gamma : K) (columns : Width19Coefficients K)
    (opened : AspisFormal.ArithmetizationCore.OpenedColumns)
    (fourClaimDiscrepancy : Fin 4 → K) (kappa : K) :
    (productionCandidateRecord gamma columns opened fourClaimDiscrepancy
      kappa).lanes = ensembleOfWidth19Coefficients gamma columns := rfl

/-- Outside the one correlated-family event, an eligible valid candidate
constructs the exact record lanes and combined initial message.  No runtime
decoder-list object is required. -/
theorem production_candidate_constructs_exact_record_outside_failure
    [Fintype K] [DecidableEq K]
    (encoder : Width19LinearEncoder K)
    (encoderInjective : Function.Injective encoder)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    {Candidate : Type*} [Nonempty Candidate]
    (eligible : K → Candidate → Prop)
    (candidateMessage : Candidate → Width19CoefficientMessage K)
    (support : K → Candidate → Finset Width19ReceivedCoordinate)
    (gamma : K) (candidate : Candidate)
    (execution : AcceptedCandidateExecution K)
    (opened : AspisFormal.ArithmetizationCore.OpenedColumns)
    (fourClaimDiscrepancy : Fin 4 → K) (kappa : K)
    (messageMatches : candidateMessage candidate = execution.initialValues)
    (outside : ¬ Width19CandidateFamilyBadAt encoder agreementCap0
      receivedLanes eligible candidateMessage support gamma)
    (isEligible : eligible gamma candidate)
    (isValid : Width19CandidateValid encoder agreementCap0 receivedLanes
      candidateMessage support gamma candidate) :
    ∃ columns : Width19Coefficients K,
      support gamma candidate ⊆
          width19JointAgreementSet encoder receivedLanes columns ∧
      (productionCandidateRecord gamma columns opened fourClaimDiscrepancy
          kappa).lanes = ensembleOfWidth19Coefficients gamma columns ∧
      execution.initialValues = combineWidth19Coefficients gamma columns := by
  obtain ⟨columns, joint, combined⟩ :=
    candidate_family_member_extracts_coefficient_messages_outside_failure
      encoder encoderInjective receivedLanes eligible candidateMessage support
      gamma candidate execution messageMatches outside isEligible isValid
  exact ⟨columns, joint, rfl, combined⟩

set_option maxRecDepth 10000 in
/-- The exact initial-list specialization.  Once ideal FRI supplies a member
of the decoder list fixed by the authenticated initial word, no independent
eligibility, message, or support premise remains: all three are the concrete
objects defined above. -/
theorem initial_candidate_constructs_exact_record_outside_failure
    [Fintype K] [DecidableEq K]
    (encoder : Width19LinearEncoder K)
    (encoderInjective : Function.Injective encoder)
    (encoderTemplate : CodeEncoders K)
    (transcriptTemplate : IdealTranscript K)
    (receivedLanes : Fin 19 → Width19ReceivedCoordinate → K)
    (gamma : K) (candidate : Width19CoefficientMessage K)
    (execution : AcceptedCandidateExecution K)
    (opened : AspisFormal.ArithmetizationCore.OpenedColumns)
    (fourClaimDiscrepancy : Fin 4 → K) (kappa : K)
    (member : candidate ∈ initialCandidateList
      (encodersWithWidth19Layer0 encoderTemplate encoder)
      (transcriptAtWidth19Challenge transcriptTemplate receivedLanes gamma))
    (messageMatches : candidate = execution.initialValues)
    (outside : ¬ Width19CandidateFamilyBadAt encoder agreementCap0
      receivedLanes
      (productionCandidateEligible encoder receivedLanes)
      productionCandidateMessage
      (productionCandidateSupport encoder receivedLanes)
      gamma) :
    ∃ columns : Width19Coefficients K,
      productionCandidateSupport encoder receivedLanes gamma candidate ⊆
          width19JointAgreementSet encoder receivedLanes columns ∧
      (productionCandidateRecord gamma columns opened fourClaimDiscrepancy
          kappa).lanes = ensembleOfWidth19Coefficients gamma columns ∧
      execution.initialValues = combineWidth19Coefficients gamma columns := by
  have eligible :
      productionCandidateEligible encoder receivedLanes gamma candidate :=
    (mem_initialCandidateList_iff_productionCandidateEligible encoder
      encoderTemplate transcriptTemplate receivedLanes gamma candidate).mp
      member
  have valid : Width19CandidateValid encoder agreementCap0 receivedLanes
      productionCandidateMessage
      (productionCandidateSupport encoder receivedLanes)
      gamma candidate :=
    (production_candidate_valid_iff_eligible encoder receivedLanes gamma
      candidate).mpr eligible
  exact production_candidate_constructs_exact_record_outside_failure
    encoder encoderInjective receivedLanes
    (productionCandidateEligible encoder receivedLanes)
    productionCandidateMessage
    (productionCandidateSupport encoder receivedLanes)
    gamma candidate execution opened fourClaimDiscrepancy kappa messageMatches
    outside eligible valid

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
#print axioms production_candidate_valid_iff_eligible
#print axioms mem_initialCandidateList_iff_productionCandidateEligible
#print axioms production_candidate_constructs_exact_record_outside_failure
#print axioms initial_candidate_constructs_exact_record_outside_failure
#print axioms Width19ProjectionOutsideFamilyFailure.projection
#print axioms combinedLaneBindingFailure_implies_familyFailure

end AspisV5Width19CandidateEventBridge
