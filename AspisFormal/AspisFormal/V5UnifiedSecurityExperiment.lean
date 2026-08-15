import Mathlib.Probability.ProbabilityMassFunction.Basic
import AspisFormal.V5AcceptedExecutionReleasedFinalAccounting
import AspisFormal.V5HundredBitSecurityMargin

/-!
# One V5 adversarial experiment and one final failure ledger

This file gives the V5 security endpoint the same useful shape as a standard
probabilistic soundness theorem: one finite probability law, one accepted-false
event, one pointwise failure classification, and one union bound.

The old final ledger has twenty-four entries.  Its first six entries are the
proof-system events that are replaced by the corrected work-normalized core
calculation.  The other eighteen entries are source, transcript, primitive,
credential, Merkle, and runtime failures.  The unified ledger groups the first
six entries into one protocol-core event and leaves each external entry
separate.  The set equality below proves that this regrouping neither drops nor
adds an event.

The probability law in `WorkNormalizedV5AdversarialExperiment` is explicitly a
work-normalized law.  It is not the raw distribution of an attempt after the
attacker has completed the proof-of-work grind.  Connecting a production
attacker and its work cost to this law remains the named
`WorkNormalizedCoreEventConnection` premise.  The raw completed-attempt
theorems remain separate.

No cryptographic property is proved here.  The eighteen external event bounds
remain explicit assumptions, and their total must fit the thirty-percent
external margin retained by `V5HundredBitSecurityMargin`.
-/

namespace AspisV5UnifiedSecurityExperiment

open MeasureTheory
open AspisV5AcceptedExecutionReleasedFinalAccounting
open AspisV5CryptographicAssumptions
open AspisV5FinalSecurityAccounting
open AspisV5HundredBitSecurityMargin
open AspisV5ImplementedWorkNormalizedEndpoint
open AspisV5NonceWorkAuthentication
open AspisV5SelectedGoodVerifierRelation
open AspisV5WorkNormalizedApplicabilityRepair
open AspisWorkNormalizedEndpoint
open AspisFormal.V5ExactRuntimeWireRepair

/-! ## Exact regrouping of the final ledger -/

/-- The six proof-system entries replaced by the corrected work-normalized
core calculation. -/
def protocolCoreFinalFailureKinds : List FinalFailureKind :=
  [.queryAndFinalWorkMiss,
    .friRound0,
    .friRound1,
    .friRound2,
    .friRound3,
    .relationRepair]

/-- The eighteen entries whose probabilities still require source,
cryptographic, credential, Merkle, or runtime bounds. -/
def externalFinalFailureKinds : List FinalFailureKind :=
  [.transcriptRustToLean,
    .sha256ImplementationDivergence,
    .sha256Collision,
    .sha256Preimage,
    .sha256RandomOracle,
    .poseidon2ImplementationDivergence,
    .poseidon2Collision,
    .poseidon2Preimage,
    .acceptedRunRelationBridge,
    .proofMerkleOpeningBridge,
    .victimCredentialRecovery,
    .rustStateModelMismatch,
    .systemProgramOrPdaMismatch,
    .writableAccountLockFailure,
    .rejectedTransactionRollbackFailure,
    .committedMarkerPersistenceFailure,
    .finalizedStateObservationFailure,
    .closeOrRefundModelMismatch]

/-- The two lists are disjoint, contain no duplicate, and concatenate to the
existing released order. -/
theorem final_failure_partition_is_exact :
    protocolCoreFinalFailureKinds.Nodup /\
      externalFinalFailureKinds.Nodup /\
      List.Disjoint protocolCoreFinalFailureKinds externalFinalFailureKinds /\
      protocolCoreFinalFailureKinds ++ externalFinalFailureKinds =
        orderedFinalFailureKinds := by
  simp [protocolCoreFinalFailureKinds, externalFinalFailureKinds,
    orderedFinalFailureKinds]

/-- One unified core branch followed by all eighteen external branches. -/
inductive UnifiedFailureKind where
  | workNormalizedProtocolCore
  | transcriptRustToLean
  | sha256ImplementationDivergence
  | sha256Collision
  | sha256Preimage
  | sha256RandomOracle
  | poseidon2ImplementationDivergence
  | poseidon2Collision
  | poseidon2Preimage
  | acceptedRunRelationBridge
  | proofMerkleOpeningBridge
  | victimCredentialRecovery
  | rustStateModelMismatch
  | systemProgramOrPdaMismatch
  | writableAccountLockFailure
  | rejectedTransactionRollbackFailure
  | committedMarkerPersistenceFailure
  | finalizedStateObservationFailure
  | closeOrRefundModelMismatch
  deriving DecidableEq, Fintype

def orderedUnifiedFailureKinds : List UnifiedFailureKind :=
  [.workNormalizedProtocolCore,
    .transcriptRustToLean,
    .sha256ImplementationDivergence,
    .sha256Collision,
    .sha256Preimage,
    .sha256RandomOracle,
    .poseidon2ImplementationDivergence,
    .poseidon2Collision,
    .poseidon2Preimage,
    .acceptedRunRelationBridge,
    .proofMerkleOpeningBridge,
    .victimCredentialRecovery,
    .rustStateModelMismatch,
    .systemProgramOrPdaMismatch,
    .writableAccountLockFailure,
    .rejectedTransactionRollbackFailure,
    .committedMarkerPersistenceFailure,
    .finalizedStateObservationFailure,
    .closeOrRefundModelMismatch]

theorem unified_failure_kind_count_is_nineteen :
    Fintype.card UnifiedFailureKind = 19 := by
  decide

theorem ordered_unified_failure_kinds_are_exactly_once :
    orderedUnifiedFailureKinds.Nodup /\
      forall kind : UnifiedFailureKind,
        kind ∈ orderedUnifiedFailureKinds := by
  decide

/-- The union of the six old ideal proof-system events.  This is one event in
the unified ledger, so its corrected core budget is charged once. -/
def workNormalizedProtocolCoreFailure
    {Coins : Type*} (events : FinalSecurityEvents Coins) : Set Coins :=
  (protocolCoreFinalFailureKinds.map events.event).foldr (· ∪ ·) ∅

/-- Interpret one unified branch using the existing event definitions. -/
def unifiedFailureEvent
    {Coins : Type*} (events : FinalSecurityEvents Coins) :
    UnifiedFailureKind -> Set Coins
  | .workNormalizedProtocolCore => workNormalizedProtocolCoreFailure events
  | .transcriptRustToLean => events.event .transcriptRustToLean
  | .sha256ImplementationDivergence =>
      events.event .sha256ImplementationDivergence
  | .sha256Collision => events.event .sha256Collision
  | .sha256Preimage => events.event .sha256Preimage
  | .sha256RandomOracle => events.event .sha256RandomOracle
  | .poseidon2ImplementationDivergence =>
      events.event .poseidon2ImplementationDivergence
  | .poseidon2Collision => events.event .poseidon2Collision
  | .poseidon2Preimage => events.event .poseidon2Preimage
  | .acceptedRunRelationBridge => events.event .acceptedRunRelationBridge
  | .proofMerkleOpeningBridge => events.event .proofMerkleOpeningBridge
  | .victimCredentialRecovery => events.event .victimCredentialRecovery
  | .rustStateModelMismatch => events.event .rustStateModelMismatch
  | .systemProgramOrPdaMismatch => events.event .systemProgramOrPdaMismatch
  | .writableAccountLockFailure => events.event .writableAccountLockFailure
  | .rejectedTransactionRollbackFailure =>
      events.event .rejectedTransactionRollbackFailure
  | .committedMarkerPersistenceFailure =>
      events.event .committedMarkerPersistenceFailure
  | .finalizedStateObservationFailure =>
      events.event .finalizedStateObservationFailure
  | .closeOrRefundModelMismatch => events.event .closeOrRefundModelMismatch

def totalUnifiedFailure
    {Coins : Type*} (events : FinalSecurityEvents Coins) : Set Coins :=
  (orderedUnifiedFailureKinds.map (unifiedFailureEvent events)).foldr
    (· ∪ ·) ∅

/-- Regrouping the six proof-system branches into one core branch preserves
the old final failure event exactly. -/
theorem total_unified_failure_eq_total_final_failure
    {Coins : Type*} (events : FinalSecurityEvents Coins) :
    totalUnifiedFailure events = totalFinalFailure events := by
  ext coins
  simp [totalUnifiedFailure, orderedUnifiedFailureKinds, unifiedFailureEvent,
    workNormalizedProtocolCoreFailure, protocolCoreFinalFailureKinds,
    totalFinalFailure, orderedFinalFailureKinds, or_assoc]

/-! ## One finite work-normalized adversarial experiment -/

/-- A single finite V5 adversarial experiment.  The law samples the complete
work-normalized experiment coins; every event below is evaluated on that same
sample. -/
structure WorkNormalizedV5AdversarialExperiment
    (Coins : Type*) [Fintype Coins] [MeasurableSpace Coins] where
  law : PMF Coins
  acceptedFalse : Set Coins
  failures : FinalSecurityEvents Coins
  acceptedFalseClassified :
    acceptedFalse ⊆ totalUnifiedFailure failures

noncomputable def WorkNormalizedV5AdversarialExperiment.probability
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins)
    (event : Set Coins) : Real :=
  experiment.law.toMeasure.real event

/-- Any existing pointwise reduction to the final ledger constructs the
unified experiment without another probabilistic assumption. -/
def WorkNormalizedV5AdversarialExperiment.ofFinalClassification
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (law : PMF Coins) (acceptedFalse : Set Coins)
    (failures : FinalSecurityEvents Coins)
    (classified : acceptedFalse ⊆ totalFinalFailure failures) :
    WorkNormalizedV5AdversarialExperiment Coins where
  law := law
  acceptedFalse := acceptedFalse
  failures := failures
  acceptedFalseClassified := by
    rw [total_unified_failure_eq_total_final_failure]
    exact classified

/-- In particular, the released fourteen-way accepted-execution reduction
constructs the pointwise-classified experiment.  The production theorem that
reduces accepted false executions to `failure.Occurs` supplies
`acceptedFalseReduces`. -/
def WorkNormalizedV5AdversarialExperiment.ofReleasedAcceptedExecution
    {Coins K : Type*} [Fintype Coins] [MeasurableSpace Coins]
    [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]
    (law : PMF Coins) (acceptedFalse : Set Coins)
    (failures : FinalSecurityEvents Coins)
    (released : ReleasedAcceptedExecutionFailurePredicates Coins K)
    (acceptedFalseReduces :
      acceptedFalse ⊆ {coins | released.Occurs coins})
    (coverage : ReleasedAcceptedExecutionFailureCoverage failures released) :
    WorkNormalizedV5AdversarialExperiment Coins :=
  .ofFinalClassification law acceptedFalse failures
    (Set.Subset.trans acceptedFalseReduces
      (released_accepted_execution_failure_subset_total failures released
        coverage))

/-! ## Symbolic union bound -/

/-- The sum of the eighteen external event probabilities under the one
experiment law. -/
noncomputable def externalFailureProbabilitySum
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins) : Real :=
  (externalFinalFailureKinds.map (fun kind =>
    experiment.law.toMeasure.real (experiment.failures.event kind))).sum

/-- The accepted-false probability is at most one corrected core probability
plus each external branch probability exactly once. -/
theorem accepted_false_probability_le_core_plus_external_sum
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins) :
    experiment.probability experiment.acceptedFalse ≤
      experiment.probability
          (workNormalizedProtocolCoreFailure experiment.failures) +
        externalFailureProbabilitySum experiment := by
  haveI : IsProbabilityMeasure experiment.law.toMeasure := inferInstance
  calc
    experiment.probability experiment.acceptedFalse ≤
        experiment.law.toMeasure.real
          (totalUnifiedFailure experiment.failures) :=
      MeasureTheory.measureReal_mono experiment.acceptedFalseClassified
    _ ≤ (orderedUnifiedFailureKinds.map (fun kind =>
          experiment.law.toMeasure.real
            (unifiedFailureEvent experiment.failures kind))).sum :=
      measureReal_foldr_union_le_sum experiment.law.toMeasure
        (orderedUnifiedFailureKinds.map
          (unifiedFailureEvent experiment.failures))
    _ = experiment.probability
          (workNormalizedProtocolCoreFailure experiment.failures) +
        externalFailureProbabilitySum experiment := by
      simp [WorkNormalizedV5AdversarialExperiment.probability,
        externalFailureProbabilitySum, externalFinalFailureKinds,
        orderedUnifiedFailureKinds, unifiedFailureEvent]

/-! ## Explicit external assumptions -/

/-- Exactly the external assumptions used below.  No field concerns one of
the six protocol-core events. -/
structure AssumedExternalSecurityBounds
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget) : Prop where
  transcriptAndPrimitives : AssumedConcreteSecurityBounds measure
    events.transcriptAndPrimitives budget.transcriptAndPrimitives
  acceptedRunRelationBridge :
    measure.real events.acceptedRunRelationBridge ≤
      budget.acceptedRunRelationBridge
  proofMerkleOpeningBridge :
    measure.real events.proofMerkleOpeningBridge ≤
      budget.proofMerkleOpeningBridge
  victimCredentialRecovery :
    measure.real events.victimCredentialRecovery ≤
      budget.victimCredentialRecovery
  rustStateModelMismatch :
    measure.real {coins | events.runtime.rustStateModelMismatch coins} ≤
      budget.runtime.rustStateModelMismatch
  systemProgramOrPdaMismatch :
    measure.real {coins | events.runtime.systemProgramOrPdaMismatch coins} ≤
      budget.runtime.systemProgramOrPdaMismatch
  writableAccountLockFailure :
    measure.real {coins | events.runtime.writableAccountLockFailure coins} ≤
      budget.runtime.writableAccountLockFailure
  rejectedTransactionRollbackFailure :
    measure.real
      {coins | events.runtime.rejectedTransactionRollbackFailure coins} ≤
      budget.runtime.rejectedTransactionRollbackFailure
  committedMarkerPersistenceFailure :
    measure.real
      {coins | events.runtime.committedMarkerPersistenceFailure coins} ≤
      budget.runtime.committedMarkerPersistenceFailure
  finalizedStateObservationFailure :
    measure.real
      {coins | events.runtime.finalizedStateObservationFailure coins} ≤
      budget.runtime.finalizedStateObservationFailure
  closeOrRefundModelMismatch :
    measure.real {coins | events.runtime.closeOrRefundModelMismatch coins} ≤
      budget.runtime.closeOrRefundModelMismatch

/-- Existing full-ledger assumptions can be restricted to the external
portion without changing any event or budget. -/
theorem AssumedExternalSecurityBounds.ofFinal
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedFinalSecurityBounds measure events budget) :
    AssumedExternalSecurityBounds measure events budget where
  transcriptAndPrimitives := assumed.transcriptAndPrimitives
  acceptedRunRelationBridge := assumed.acceptedRunRelationBridge
  proofMerkleOpeningBridge := assumed.proofMerkleOpeningBridge
  victimCredentialRecovery := assumed.victimCredentialRecovery
  rustStateModelMismatch := assumed.rustStateModelMismatch
  systemProgramOrPdaMismatch := assumed.systemProgramOrPdaMismatch
  writableAccountLockFailure := assumed.writableAccountLockFailure
  rejectedTransactionRollbackFailure :=
    assumed.rejectedTransactionRollbackFailure
  committedMarkerPersistenceFailure :=
    assumed.committedMarkerPersistenceFailure
  finalizedStateObservationFailure := assumed.finalizedStateObservationFailure
  closeOrRefundModelMismatch := assumed.closeOrRefundModelMismatch

theorem assumed_external_bound_for_kind
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedExternalSecurityBounds measure events budget)
    (kind : FinalFailureKind) (external : kind ∈ externalFinalFailureKinds) :
    measure.real (events.event kind) ≤ finalBudgetBound budget kind := by
  cases kind with
  | queryAndFinalWorkMiss => simp [externalFinalFailureKinds] at external
  | friRound0 => simp [externalFinalFailureKinds] at external
  | friRound1 => simp [externalFinalFailureKinds] at external
  | friRound2 => simp [externalFinalFailureKinds] at external
  | friRound3 => simp [externalFinalFailureKinds] at external
  | relationRepair => simp [externalFinalFailureKinds] at external
  | transcriptRustToLean =>
      exact assumed.transcriptAndPrimitives.eventBound .rustToLean
  | sha256ImplementationDivergence =>
      exact assumed.transcriptAndPrimitives.eventBound
        .sha256ImplementationDivergence
  | sha256Collision =>
      exact assumed.transcriptAndPrimitives.eventBound .sha256Collision
  | sha256Preimage =>
      exact assumed.transcriptAndPrimitives.eventBound .sha256Preimage
  | sha256RandomOracle =>
      exact assumed.transcriptAndPrimitives.eventBound .sha256RandomOracle
  | poseidon2ImplementationDivergence =>
      exact assumed.transcriptAndPrimitives.eventBound
        .poseidon2ImplementationDivergence
  | poseidon2Collision =>
      exact assumed.transcriptAndPrimitives.eventBound .poseidon2Collision
  | poseidon2Preimage =>
      exact assumed.transcriptAndPrimitives.eventBound .poseidon2Preimage
  | acceptedRunRelationBridge => exact assumed.acceptedRunRelationBridge
  | proofMerkleOpeningBridge => exact assumed.proofMerkleOpeningBridge
  | victimCredentialRecovery => exact assumed.victimCredentialRecovery
  | rustStateModelMismatch => exact assumed.rustStateModelMismatch
  | systemProgramOrPdaMismatch => exact assumed.systemProgramOrPdaMismatch
  | writableAccountLockFailure => exact assumed.writableAccountLockFailure
  | rejectedTransactionRollbackFailure =>
      exact assumed.rejectedTransactionRollbackFailure
  | committedMarkerPersistenceFailure =>
      exact assumed.committedMarkerPersistenceFailure
  | finalizedStateObservationFailure =>
      exact assumed.finalizedStateObservationFailure
  | closeOrRefundModelMismatch => exact assumed.closeOrRefundModelMismatch

/-- The external portion of `finalBudgetBound` is exactly
`ExternalSecurityBudget.total`; no proof-system term remains in this sum. -/
theorem external_budget_sum_eq_total (budget : ExternalSecurityBudget) :
    (externalFinalFailureKinds.map (finalBudgetBound budget)).sum =
      budget.total := by
  simp [externalFinalFailureKinds, finalBudgetBound,
    ExternalSecurityBudget.total, RuntimeSecurityBudget.total,
    ConcreteSecurityBudget.total, orderedFailureKinds,
    ConcreteSecurityBudget.bound]
  ring

theorem external_failure_probability_sum_le_budget
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins)
    (budget : ExternalSecurityBudget)
    (assumed : AssumedExternalSecurityBounds experiment.law.toMeasure
      experiment.failures budget) :
    externalFailureProbabilitySum experiment ≤ budget.total := by
  calc
    externalFailureProbabilitySum experiment ≤
        (externalFinalFailureKinds.map (finalBudgetBound budget)).sum := by
      unfold externalFailureProbabilitySum
      apply List.sum_le_sum
      intro kind member
      exact assumed_external_bound_for_kind experiment.law.toMeasure
        experiment.failures budget assumed kind member
    _ = budget.total := external_budget_sum_eq_total budget

/-! ## Corrected core connection and 100-bit endpoint -/

/-- The one remaining event-level equality needed to apply the corrected
work-normalized arithmetic to the unified experiment.  A source proof must
show that the probability of the six-event protocol core under this exact law
is bounded by the selected-release `unionError`; the arithmetic theorem alone
does not establish this connection. -/
structure WorkNormalizedCoreEventConnection
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins)
    (unionError : Real) : Prop where
  protocolCoreProbability :
    experiment.probability
        (workNormalizedProtocolCoreFailure experiment.failures) ≤
      unionError

/-- The unified endpoint.  Every outcome is sampled by one PMF, the corrected
protocol core is charged once, all eighteen external branches are charged
once, and the existing 70/30 margin gives the final work-normalized target. -/
theorem work_normalized_accepted_false_probability_le_two_pow_neg_100
    {Coins : Type*} [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins)
    (unionError : Real)
    (coreConnection : WorkNormalizedCoreEventConnection experiment unionError)
    (correctedCoreBound :
      unionError ≤ (7 : Real) / (10 * 2 ^ 100))
    (budget : ExternalSecurityBudget)
    (externalAssumed : AssumedExternalSecurityBounds
      experiment.law.toMeasure experiment.failures budget)
    (externalBudgetFits :
      budget.total ≤ (3 : Real) / (10 * 2 ^ 100)) :
    experiment.probability experiment.acceptedFalse ≤
      (1 : Real) / 2 ^ 100 := by
  have symbolic :=
    accepted_false_probability_le_core_plus_external_sum experiment
  have external :=
    external_failure_probability_sum_le_budget experiment budget
      externalAssumed
  calc
    experiment.probability experiment.acceptedFalse ≤
        experiment.probability
            (workNormalizedProtocolCoreFailure experiment.failures) +
          externalFailureProbabilitySum experiment := symbolic
    _ ≤ unionError + budget.total :=
      add_le_add coreConnection.protocolCoreProbability external
    _ ≤ (1 : Real) / 2 ^ 100 :=
      core_plus_external_budget_le_two_pow_neg_100 unionError budget.total
        correctedCoreBound externalBudgetFits

/-- Direct composition with the maintained selected-release arithmetic.  This
wrapper deliberately retains every applicability premise of
`corrected_selected_release_core_le_seven_tenths`; the unified experiment does
not make a decoding, transcript, grinding, Merkle, or source correspondence
premise disappear. -/
theorem work_normalized_accepted_false_probability_le_two_pow_neg_100_of_released_core
    {Coins Schedule RustBoundary : Type*}
    [Fintype Coins] [MeasurableSpace Coins]
    (experiment : WorkNormalizedV5AdversarialExperiment Coins)
    (acceptedSchedule citedMCAHypotheses : Schedule -> Prop)
    (virtualOracleAndCodeMembership : Schedule -> Prop)
    (separateGrindingOutputReduction : Schedule -> Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule -> Prop)
    (actualBatchEventProbability : Schedule -> Real)
    (widthDeployment : Width19FStarDeploymentPremises acceptedSchedule
      citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability)
    (schedule : Schedule) (accepted : acceptedSchedule schedule)
    (epsRound : Real) (epsRoundNonnegative : 0 ≤ epsRound)
    (decomposition : epsRound ≤
      actualBatchEventProbability schedule + correctedNonBatchRoundError)
    (R : Real) (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary -> V5PublicMessageBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustRoundTrace)
    (rustInitialEnsembleM0Correspondence : Prop)
    (randomOracleAndFiatShamirApplicability : Prop)
    (pcsAndMerkleAuthenticationApplicability : Prop)
    (citedBCSAndCMSApplicability : Prop)
    (bcsDeployment : M0ExcludedBCSDeploymentPremises
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability)
    (unionError branch0 branch1 branch2 capErr T : Real)
    (unionDecomposition : unionError ≤ branch0 + branch1 + branch2)
    (branch0Bound : branch0 ≤ bcsError epsRound T R capErr)
    (branch1Bound : branch1 ≤ bcsError epsRound T R capErr)
    (branch2Bound : branch2 ≤ bcsError epsRound T R capErr)
    (capNonnegative : 0 ≤ capErr) (capBound : capErr ≤ roCapErr)
    (oneLeT : 1 ≤ T) (TBound : T ≤ 2 ^ 128)
    (coreConnection : WorkNormalizedCoreEventConnection experiment unionError)
    (budget : ExternalSecurityBudget)
    (externalAssumed : AssumedExternalSecurityBounds
      experiment.law.toMeasure experiment.failures budget)
    (externalBudgetFits :
      budget.total ≤ (3 : Real) / (10 * 2 ^ 100)) :
    experiment.probability experiment.acceptedFalse ≤
      (1 : Real) / 2 ^ 100 := by
  have correctedCoreBound :
      unionError ≤ (7 : Real) / (10 * 2 ^ 100) :=
    corrected_selected_release_core_le_seven_tenths
      acceptedSchedule citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability widthDeployment schedule accepted epsRound
      epsRoundNonnegative decomposition R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability citedBCSAndCMSApplicability
      bcsDeployment unionError branch0 branch1 branch2 capErr T
      unionDecomposition branch0Bound branch1Bound branch2Bound capNonnegative
      capBound oneLeT TBound
  exact work_normalized_accepted_false_probability_le_two_pow_neg_100
    experiment unionError coreConnection correctedCoreBound budget
    externalAssumed externalBudgetFits

/-! ## Axiom audit -/

#print axioms final_failure_partition_is_exact
#print axioms unified_failure_kind_count_is_nineteen
#print axioms ordered_unified_failure_kinds_are_exactly_once
#print axioms total_unified_failure_eq_total_final_failure
#print axioms accepted_false_probability_le_core_plus_external_sum
#print axioms assumed_external_bound_for_kind
#print axioms external_budget_sum_eq_total
#print axioms external_failure_probability_sum_le_budget
#print axioms work_normalized_accepted_false_probability_le_two_pow_neg_100
#print axioms
  work_normalized_accepted_false_probability_le_two_pow_neg_100_of_released_core

end AspisV5UnifiedSecurityExperiment
