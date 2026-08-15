import AspisFormal.V5AcceptedTerminalResidualExtraction
import AspisFormal.V5ProjectedAcceptedFalseComponentAccounting

/-!
# Splitting the production statement-binding failure

The accepted-false accounting previously retained one broad
`statementBindingFailure` event.  The accepted terminal theorem now gives a
more useful deterministic inclusion.  For one fixed accepted run, failure to
bind the six public spend fields must be caused by one of seven named events:

* the accepted trace was not projected to the opened columns;
* the production residual map did not match the maintained model;
* the accepted masked sumcheck did not yield its boundary equation;
* the arithmetic residuals were not extracted;
* helper cancellation at `mu`;
* a nonzero Boolean table vanished at the equality point; or
* a nonzero row polynomial vanished at `theta`.

This file lifts that pointwise disjunction to experiment sets and a union
bound.  It deliberately assigns no numerical probability to the source,
authentication, or transcript-ordering events.  The existing `1`, `10`, and
`24` root counts become probability bounds only after the corresponding
values have been proved fixed before their challenges are sampled.
-/

namespace AspisV5StatementBindingFailureAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5CryptographicAssumptions
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5ProjectedAcceptedFalseComponentAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5Tag67CandidateTraceExtraction
open Module

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
-- The dependent candidate schedule expands the complete accepted-false family.
/-- The exact connection between each candidate record in the accepted-false
experiment and the fixed accepted terminal run to which the source theorem is
applied.  In particular, `opened` prevents choosing a different terminal view
after observing the failure. -/
structure StatementBindingProjectionData
    (Run Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) where
  accepts : V5PublicStatement → Run → Prop
  viewOf : Run → AcceptedTerminalRunView K
  runAt : CandidateSchedule data.base → Run
  basis : Basis (Fin 4) F K
  accepted : ∀ schedule,
    accepts (data.base.statement schedule.1) (runAt schedule)
  opened : ∀ schedule,
    (viewOf (runAt schedule)).opened =
      (data.base.records schedule.1 schedule.2).opened

def traceProjectionFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    AcceptedTraceProjectionFailure projection.accepts projection.viewOf
      (data.base.statement coins) (projection.runAt ⟨coins, candidate⟩)}

def residualMapFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    AcceptedResidualMapFailure projection.accepts projection.viewOf
      (data.base.statement coins) (projection.runAt ⟨coins, candidate⟩)}

def maskedBoundaryFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    AcceptedMaskedBoundaryExtractionFailure projection.accepts
      projection.viewOf projection.basis (data.base.statement coins)
      (projection.runAt ⟨coins, candidate⟩)}

def arithmeticExtractionFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    AcceptedArithmeticResidualExtractionFailure projection.accepts
      projection.viewOf (data.base.statement coins)
      (projection.runAt ⟨coins, candidate⟩)}

def helperCancellationFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    let view := projection.viewOf (projection.runAt ⟨coins, candidate⟩)
    HelperCancellation projection.basis view.constraintRows view.theta
      view.zerocheckPoint view.mu view.helper}

def zerocheckCollisionFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    let view := projection.viewOf (projection.runAt ⟨coins, candidate⟩)
    ZerocheckEvaluationCollision projection.basis view.constraintRows
      view.theta view.zerocheckPoint}

def thetaCollisionFailureSet
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  {coins | ∃ candidate,
    let view := projection.viewOf (projection.runAt ⟨coins, candidate⟩)
    ThetaLaneCollision projection.basis view.constraintRows view.theta}

def statementBindingComponentUnion
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) : Set Coins :=
  ((((((traceProjectionFailureSet projection ∪
      residualMapFailureSet projection) ∪
      maskedBoundaryFailureSet projection) ∪
      arithmeticExtractionFailureSet projection) ∪
      helperCancellationFailureSet projection) ∪
      zerocheckCollisionFailureSet projection) ∪
      thetaCollisionFailureSet projection)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
-- Applying the terminal split elaborates all seven dependent event witnesses.
/-- The old broad statement-binding event is contained in exactly the seven
events exposed by the accepted terminal theorem. -/
theorem statementBindingFailure_subset_componentUnion
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) :
    data.base.toEvents.statementBindingFailure ⊆
      statementBindingComponentUnion projection := by
  intro coins failure
  rcases failure with ⟨candidate, candidateFailure⟩
  let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
  have accepted := projection.accepted schedule
  have split := accepted_run_binds_statement_or_named_failure
    projection.accepts projection.viewOf projection.basis
    (data.base.statement coins) (projection.runAt schedule) accepted
  rcases split with matched | trace | residual | boundary | arithmetic |
      helper | zerocheck | theta
  · exfalso
    apply candidateFailure.2.2.2
    rw [← projection.opened schedule]
    exact matched
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨candidate, trace⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨candidate, residual⟩)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨candidate, boundary⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr
      ⟨candidate, arithmetic⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨candidate, helper⟩))
  · exact Or.inl (Or.inr ⟨candidate, zerocheck⟩)
  · exact Or.inr ⟨candidate, theta⟩

def statementBindingComponentProbabilitySum
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (measure : Measure Coins)
    (projection : StatementBindingProjectionData Run Coins K data) : Real :=
  ((((((measure.real (traceProjectionFailureSet projection) +
      measure.real (residualMapFailureSet projection)) +
      measure.real (maskedBoundaryFailureSet projection)) +
      measure.real (arithmeticExtractionFailureSet projection)) +
      measure.real (helperCancellationFailureSet projection)) +
      measure.real (zerocheckCollisionFailureSet projection)) +
      measure.real (thetaCollisionFailureSet projection))

theorem statementBindingFailure_probability_le_componentSum
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (measure : Measure Coins) [IsFiniteMeasure measure]
    (projection : StatementBindingProjectionData Run Coins K data) :
    measure.real data.base.toEvents.statementBindingFailure ≤
      statementBindingComponentProbabilitySum measure projection := by
  calc
    measure.real data.base.toEvents.statementBindingFailure ≤
        measure.real (statementBindingComponentUnion projection) :=
      MeasureTheory.measureReal_mono
        (statementBindingFailure_subset_componentUnion projection)
    _ ≤ statementBindingComponentProbabilitySum measure projection := by
      unfold statementBindingComponentUnion
        statementBindingComponentProbabilitySum
      calc
        measure.real ((((((traceProjectionFailureSet projection ∪
            residualMapFailureSet projection) ∪
            maskedBoundaryFailureSet projection) ∪
            arithmeticExtractionFailureSet projection) ∪
            helperCancellationFailureSet projection) ∪
            zerocheckCollisionFailureSet projection) ∪
            thetaCollisionFailureSet projection) ≤
          measure.real (((((traceProjectionFailureSet projection ∪
            residualMapFailureSet projection) ∪
            maskedBoundaryFailureSet projection) ∪
            arithmeticExtractionFailureSet projection) ∪
            helperCancellationFailureSet projection) ∪
            zerocheckCollisionFailureSet projection) +
          measure.real (thetaCollisionFailureSet projection) :=
            MeasureTheory.measureReal_union_le _ _
        _ ≤ (measure.real ((((traceProjectionFailureSet projection ∪
            residualMapFailureSet projection) ∪
            maskedBoundaryFailureSet projection) ∪
            arithmeticExtractionFailureSet projection) ∪
            helperCancellationFailureSet projection) +
            measure.real (zerocheckCollisionFailureSet projection)) +
            measure.real (thetaCollisionFailureSet projection) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _
        _ ≤ ((measure.real (((traceProjectionFailureSet projection ∪
            residualMapFailureSet projection) ∪
            maskedBoundaryFailureSet projection) ∪
            arithmeticExtractionFailureSet projection) +
            measure.real (helperCancellationFailureSet projection)) +
            measure.real (zerocheckCollisionFailureSet projection)) +
            measure.real (thetaCollisionFailureSet projection) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _
        _ ≤ (((measure.real ((traceProjectionFailureSet projection ∪
            residualMapFailureSet projection) ∪
            maskedBoundaryFailureSet projection) +
            measure.real (arithmeticExtractionFailureSet projection)) +
            measure.real (helperCancellationFailureSet projection)) +
            measure.real (zerocheckCollisionFailureSet projection)) +
            measure.real (thetaCollisionFailureSet projection) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _
        _ ≤ ((((measure.real (traceProjectionFailureSet projection ∪
            residualMapFailureSet projection) +
            measure.real (maskedBoundaryFailureSet projection)) +
            measure.real (arithmeticExtractionFailureSet projection)) +
            measure.real (helperCancellationFailureSet projection)) +
            measure.real (zerocheckCollisionFailureSet projection)) +
            measure.real (thetaCollisionFailureSet projection) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _
        _ ≤ (((((measure.real (traceProjectionFailureSet projection) +
            measure.real (residualMapFailureSet projection)) +
            measure.real (maskedBoundaryFailureSet projection)) +
            measure.real (arithmeticExtractionFailureSet projection)) +
            measure.real (helperCancellationFailureSet projection)) +
            measure.real (zerocheckCollisionFailureSet projection)) +
            measure.real (thetaCollisionFailureSet projection) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _

/-- The accepted-false theorem with the public-field mismatch split into its
seven actual residual events. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_split_statement
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data) :
    measure.real data.base.acceptedFalse ≤
      ((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        statementBindingComponentProbabilitySum measure projection) +
        measure.real data.arithmeticResidualFailure) +
        hashMerkleComponentProbabilitySum measure data := by
  exact
    (acceptedFalse_probability_le_two_pow_neg_75_plus_components
      measure data connections).trans (by
        gcongr
        exact statementBindingFailure_probability_le_componentSum
          measure projection)

/-- Production transfer with the transcript/hash divergence term retained
separately from all seven statement-binding events. -/
theorem productionFalseSpend_probability_le_two_pow_neg_75_plus_split_statement
    {Run Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data) :
    measure.real production.productionFalseSpend ≤
      (((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        statementBindingComponentProbabilitySum measure projection) +
        measure.real data.arithmeticResidualFailure) +
        hashMerkleComponentProbabilitySum measure data) +
        measure.real (totalFailure production.transcriptAndHashFailures) := by
  calc
    measure.real production.productionFalseSpend ≤
        measure.real (data.base.acceptedFalse ∪
          totalFailure production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_mono production.production_subset_ideal_or_hash
    _ ≤ measure.real data.base.acceptedFalse +
          measure.real (totalFailure production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
          statementBindingComponentProbabilitySum measure projection) +
          measure.real data.arithmeticResidualFailure) +
          hashMerkleComponentProbabilitySum measure data) +
          measure.real (totalFailure production.transcriptAndHashFailures) := by
      gcongr
      exact acceptedFalse_probability_le_two_pow_neg_75_plus_split_statement
        measure data connections projection

#print axioms statementBindingFailure_subset_componentUnion
#print axioms statementBindingFailure_probability_le_componentSum
#print axioms acceptedFalse_probability_le_two_pow_neg_75_plus_split_statement
#print axioms productionFalseSpend_probability_le_two_pow_neg_75_plus_split_statement

end AspisV5StatementBindingFailureAccounting
