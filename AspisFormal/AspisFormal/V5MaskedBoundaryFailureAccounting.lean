import AspisFormal.V5AdaptiveSumcheckChallengeBound
import AspisFormal.V5StatementBindingFailureAccounting

/-!
# Splitting the accepted masked-boundary failure

The statement-binding ledger used to retain one broad event saying that an
accepted ten-round sumcheck did not yield the masked Boolean-sum equation.
The deterministic sumcheck theorem already identifies the smaller causes.
This file lifts that result to the accepted-false experiment.

For every selected accepted run, the caller supplies the accepted ten-round
wire and one reference trace for the polynomial fixed by the commitment.  A
failure of the masked-boundary equation is then contained in exactly four
events:

* the wire's `eta` is not the `eta` used by the terminal model;
* the initial claim is not the authenticated sum of the mask table;
* the final claim is not the authenticated opening of the fixed polynomial;
* one of the ten adaptive degree-27 rounds repairs a wrong claim.

The first three are source/commitment authentication obligations.  The fourth
is the event bounded by `V5AdaptiveSumcheckChallengeBound`, once its explicit
Fiat--Shamir connection is supplied.  This file assigns no probability to the
authentication obligations and does not infer a production source bridge.
-/

namespace AspisV5MaskedBoundaryFailureAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisSumcheckMasking
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5CryptographicAssumptions
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5ProjectedAcceptedFalseComponentAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open AspisV5Tag67CandidateTraceExtraction
open Module

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- A fixed projection from each accepted source run to the ten-round wire and
the reference polynomial trace used for authentication.

Constructing this record for production is a real proof obligation.  In
particular, `wireOf` must be the wire read by that run, and `referenceOf` must
come from the polynomial bound by its authenticated openings; neither fact is
manufactured by this structure.  The four event containments below make the
consequences of those obligations precise. -/
structure MaskedBoundaryProjectionData
    (Run Coins K Public Root : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    (projection : StatementBindingProjectionData Run Coins K data) where
  wireOf : Run → AcceptedProductionTenRoundWire scheme
  referenceOf : (run : Run) →
    let view := projection.viewOf run
    FixedOracleTenRoundTrace
      (maskedOracle view.eta
        (sourceUnmaskedZerocheckTable projection.basis view.constraintRows
          view.theta view.zerocheckPoint view.mu view.helper)
        view.mask)
      (wireOf run).transcript.point

def wireEtaProjectionFailureSet
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Set Coins :=
  {coins | ∃ candidate,
    let run := projection.runAt ⟨coins, candidate⟩
    (boundary.wireOf run).transcript.eta ≠ (projection.viewOf run).eta}

def maskInitialAuthenticationFailureSet
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Set Coins :=
  {coins | ∃ candidate,
    let run := projection.runAt ⟨coins, candidate⟩
    MaskInitialClaimAuthenticationFailure (boundary.wireOf run)
      (projection.viewOf run).mask}

def terminalOpeningAuthenticationFailureSet
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Set Coins :=
  {coins | ∃ candidate,
    let run := projection.runAt ⟨coins, candidate⟩
    FixedTerminalOpeningAuthenticationFailure (boundary.wireOf run)
      (boundary.referenceOf run)}

def tenRoundRepairFailureSet
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Set Coins :=
  {coins | ∃ candidate,
    let run := projection.runAt ⟨coins, candidate⟩
    TenRoundRepair (boundary.wireOf run) (boundary.referenceOf run)}

def maskedBoundaryComponentUnion
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Set Coins :=
  ((wireEtaProjectionFailureSet boundary ∪
      maskInitialAuthenticationFailureSet boundary) ∪
      terminalOpeningAuthenticationFailureSet boundary) ∪
      tenRoundRepairFailureSet boundary

/-- The old broad boundary failure has only the four named causes above once
one fixed source-wire and reference-trace projection is supplied. -/
theorem maskedBoundaryFailure_subset_componentUnion
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) :
    maskedBoundaryFailureSet projection ⊆
      maskedBoundaryComponentUnion boundary := by
  intro coins failure
  rcases failure with ⟨candidate, accepted, missingBoundary⟩
  let run := projection.runAt ⟨coins, candidate⟩
  let view := projection.viewOf run
  let wire := boundary.wireOf run
  let reference := boundary.referenceOf run
  by_cases etaMismatch : wire.transcript.eta ≠ view.eta
  · exact Or.inl (Or.inl (Or.inl ⟨candidate, etaMismatch⟩))
  have split := accepted_wire_boundary_or_three_named_failures
    wire view.eta
    (sourceUnmaskedZerocheckTable projection.basis view.constraintRows
      view.theta view.zerocheckPoint view.mu view.helper)
    view.mask (not_ne_iff.mp etaMismatch) reference
  rcases split with extracted | maskFailure | terminalFailure | repair
  · exact False.elim (missingBoundary extracted)
  · exact Or.inl (Or.inl (Or.inr ⟨candidate, maskFailure⟩))
  · exact Or.inl (Or.inr ⟨candidate, terminalFailure⟩)
  · exact Or.inr ⟨candidate, repair⟩

def maskedBoundaryComponentProbabilitySum
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (measure : Measure Coins)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Real :=
  ((measure.real (wireEtaProjectionFailureSet boundary) +
      measure.real (maskInitialAuthenticationFailureSet boundary)) +
      measure.real (terminalOpeningAuthenticationFailureSet boundary)) +
      measure.real (tenRoundRepairFailureSet boundary)

/-- Probability form of the four-way split.  This is only a union bound; the
four summands still need their own source, commitment, and fresh-challenge
arguments. -/
theorem maskedBoundaryFailure_probability_le_componentSum
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (measure : Measure Coins) [IsFiniteMeasure measure]
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) :
    measure.real (maskedBoundaryFailureSet projection) ≤
      maskedBoundaryComponentProbabilitySum measure boundary := by
  calc
    measure.real (maskedBoundaryFailureSet projection) ≤
        measure.real (maskedBoundaryComponentUnion boundary) :=
      MeasureTheory.measureReal_mono
        (maskedBoundaryFailure_subset_componentUnion boundary)
    _ ≤ maskedBoundaryComponentProbabilitySum measure boundary := by
      unfold maskedBoundaryComponentUnion
        maskedBoundaryComponentProbabilitySum
      calc
        measure.real (((wireEtaProjectionFailureSet boundary ∪
            maskInitialAuthenticationFailureSet boundary) ∪
            terminalOpeningAuthenticationFailureSet boundary) ∪
            tenRoundRepairFailureSet boundary) ≤
          measure.real ((wireEtaProjectionFailureSet boundary ∪
            maskInitialAuthenticationFailureSet boundary) ∪
            terminalOpeningAuthenticationFailureSet boundary) +
          measure.real (tenRoundRepairFailureSet boundary) :=
            MeasureTheory.measureReal_union_le _ _
        _ ≤ (measure.real (wireEtaProjectionFailureSet boundary ∪
            maskInitialAuthenticationFailureSet boundary) +
            measure.real (terminalOpeningAuthenticationFailureSet boundary)) +
            measure.real (tenRoundRepairFailureSet boundary) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _
        _ ≤ ((measure.real (wireEtaProjectionFailureSet boundary) +
            measure.real (maskInitialAuthenticationFailureSet boundary)) +
            measure.real (terminalOpeningAuthenticationFailureSet boundary)) +
            measure.real (tenRoundRepairFailureSet boundary) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _

/-! ## Replacing the broad event in the accepted-false ledger -/

/-- The statement-binding probability sum with the old masked-boundary term
replaced by its four precise causes. -/
def refinedStatementBindingProbabilitySum
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (measure : Measure Coins)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) : Real :=
  (((((measure.real (traceProjectionFailureSet projection) +
      measure.real (residualMapFailureSet projection)) +
      maskedBoundaryComponentProbabilitySum measure boundary) +
      measure.real (arithmeticExtractionFailureSet projection)) +
      measure.real (helperCancellationFailureSet projection)) +
      measure.real (zerocheckCollisionFailureSet projection)) +
      measure.real (thetaCollisionFailureSet projection)

/-- Replacing the broad masked-boundary summand by its proved four-way union
can only increase the displayed upper bound. -/
theorem statementBindingComponentProbabilitySum_le_refinedSum
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (measure : Measure Coins) [IsFiniteMeasure measure]
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) :
    statementBindingComponentProbabilitySum measure projection ≤
      refinedStatementBindingProbabilitySum measure boundary := by
  unfold statementBindingComponentProbabilitySum
    refinedStatementBindingProbabilitySum
  gcongr
  exact maskedBoundaryFailure_probability_le_componentSum measure boundary

/-- The seven-way statement split now exposes ten actual terms: the six
non-boundary terms and the four boundary causes. -/
theorem statementBindingFailure_probability_le_refinedSum
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    {data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode}
    {projection : StatementBindingProjectionData Run Coins K data}
    (measure : Measure Coins) [IsFiniteMeasure measure]
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) :
    measure.real data.base.toEvents.statementBindingFailure ≤
      refinedStatementBindingProbabilitySum measure boundary := by
  exact (statementBindingFailure_probability_le_componentSum
    measure projection).trans
      (statementBindingComponentProbabilitySum_le_refinedSum measure boundary)

/-- The raw accepted-false result with all four masked-boundary causes shown
separately.  Only the ten-round repair term has a finite-field bound in the
present ideal challenge model. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_refined_statement
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) :
    measure.real data.base.acceptedFalse ≤
      ((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        refinedStatementBindingProbabilitySum measure boundary) +
        measure.real data.arithmeticResidualFailure) +
        hashMerkleComponentProbabilitySum measure data := by
  exact (acceptedFalse_probability_le_two_pow_neg_75_plus_split_statement
    measure data connections projection).trans (by
      gcongr
      exact statementBindingComponentProbabilitySum_le_refinedSum
        measure boundary)

/-- Production transfer with the refined boundary failures and the existing
transcript/hash union kept as separate summands. -/
theorem productionFalseSpend_probability_le_two_pow_neg_75_plus_refined_statement
    {Run Coins K Public Root : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {scheme : FiatShamirSchedule Public Root K}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents)
    (projection : StatementBindingProjectionData Run Coins K data)
    (boundary : MaskedBoundaryProjectionData Run Coins K Public Root
      (scheme := scheme) projection) :
    measure.real production.productionFalseSpend ≤
      (((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        refinedStatementBindingProbabilitySum measure boundary) +
        measure.real data.arithmeticResidualFailure) +
        hashMerkleComponentProbabilitySum measure data) +
        measure.real (totalFailure production.transcriptAndHashFailures) := by
  exact (productionFalseSpend_probability_le_two_pow_neg_75_plus_split_statement
    measure data connections production projection).trans (by
      gcongr
      exact statementBindingComponentProbabilitySum_le_refinedSum
        measure boundary)

#print axioms maskedBoundaryFailure_subset_componentUnion
#print axioms maskedBoundaryFailure_probability_le_componentSum
#print axioms statementBindingComponentProbabilitySum_le_refinedSum
#print axioms statementBindingFailure_probability_le_refinedSum
#print axioms acceptedFalse_probability_le_two_pow_neg_75_plus_refined_statement
#print axioms productionFalseSpend_probability_le_two_pow_neg_75_plus_refined_statement

end AspisV5MaskedBoundaryFailureAccounting
