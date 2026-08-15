import AspisFormal.V5MaskedBoundaryFailureAccounting
import AspisFormal.V5RefinedRawCoreAccounting

/-!
# Accepted-false accounting with terminal events counted once

The statement-binding split exposes ten terms.  Four of them are the terminal
challenge events now covered by the cap-240 ideal subtotal:

* a degree-27 repair in one of ten sumcheck rounds;
* helper cancellation at `mu`;
* a nonzero table vanishing at the ten-coordinate equality point;
* a nonzero lane polynomial vanishing at `theta`.

This file groups those four into one supplied terminal-candidate event, so its
probability is counted once.  The other six statement failures remain
explicit: trace projection, residual-map equality, wire-`eta` equality, mask
sum authentication, final-opening authentication, and arithmetic extraction.

The resulting theorem keeps the raw ideal proof-system subtotal at `2^-75`.
That number still excludes all six unresolved statement/source/authentication
events, the width-19 binding event, hash/Merkle extraction, transcript and
primitive failures, and runtime behavior.
-/

namespace AspisV5RefinedAcceptedFalseAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5CryptographicAssumptions
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5FourClaimBatchUnion
open AspisV5MaskedBoundaryFailureAccounting
open AspisV5ProjectedAcceptedFalseComponentAccounting
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5RefinedRawCoreAccounting
open AspisV5RawFinalSecurityAccounting
open AspisV5StatementBindingFailureAccounting
open AspisV5SumcheckTranscriptBinding
open Module

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- Exact coverage needed to count all four terminal events in one candidate
union rather than four times.  Proving these containments for production is
separate from the finite-field cardinality theorem. -/
structure TerminalCandidateFailureCoverage
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
      (scheme := scheme) projection)
    (terminalCandidateFailure : Set Coins) : Prop where
  tenRoundRepair :
    tenRoundRepairFailureSet boundary ⊆ terminalCandidateFailure
  helperCancellation :
    helperCancellationFailureSet projection ⊆ terminalCandidateFailure
  zerocheckCollision :
    zerocheckCollisionFailureSet projection ⊆ terminalCandidateFailure
  thetaCollision :
    thetaCollisionFailureSet projection ⊆ terminalCandidateFailure

/-- The six statement-binding failures that are not part of the terminal
finite-field candidate union. -/
def nonterminalStatementFailureEvents
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
      (scheme := scheme) projection) : List (Set Coins) :=
  [traceProjectionFailureSet projection,
    residualMapFailureSet projection,
    wireEtaProjectionFailureSet boundary,
    maskInitialAuthenticationFailureSet boundary,
    terminalOpeningAuthenticationFailureSet boundary,
    arithmeticExtractionFailureSet projection]

def nonterminalStatementFailureUnion
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
  (nonterminalStatementFailureEvents boundary).foldr (· ∪ ·) ∅

def nonterminalStatementFailureProbabilitySum
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
  ((nonterminalStatementFailureEvents boundary).map measure.real).sum

/-- Every statement-binding failure is either one of the six unbounded
nonterminal failures or the single cap-240 terminal-candidate event. -/
theorem statementBindingFailure_subset_nonterminal_or_terminal
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
      (scheme := scheme) projection)
    (terminalCandidateFailure : Set Coins)
    (coverage : TerminalCandidateFailureCoverage boundary
      terminalCandidateFailure) :
    data.base.toEvents.statementBindingFailure ⊆
      nonterminalStatementFailureUnion boundary ∪
        terminalCandidateFailure := by
  intro coins failure
  have components :=
    statementBindingFailure_subset_componentUnion projection failure
  simp only [statementBindingComponentUnion, Set.mem_union] at components
  rcases components with ((((((trace | residual) | masked) | arithmetic) |
      helper) | zerocheck) | theta)
  · apply Or.inl
    simp [nonterminalStatementFailureUnion,
      nonterminalStatementFailureEvents, trace]
  · apply Or.inl
    simp [nonterminalStatementFailureUnion,
      nonterminalStatementFailureEvents, residual]
  · have split := maskedBoundaryFailure_subset_componentUnion boundary masked
    simp only [maskedBoundaryComponentUnion, Set.mem_union] at split
    rcases split with ((eta | mask) | terminal) | repair
    · apply Or.inl
      simp [nonterminalStatementFailureUnion,
        nonterminalStatementFailureEvents, eta]
    · apply Or.inl
      simp [nonterminalStatementFailureUnion,
        nonterminalStatementFailureEvents, mask]
    · apply Or.inl
      simp [nonterminalStatementFailureUnion,
        nonterminalStatementFailureEvents, terminal]
    · exact Or.inr (coverage.tenRoundRepair repair)
  · apply Or.inl
    simp [nonterminalStatementFailureUnion,
      nonterminalStatementFailureEvents, arithmetic]
  · exact Or.inr (coverage.helperCancellation helper)
  · exact Or.inr (coverage.zerocheckCollision zerocheck)
  · exact Or.inr (coverage.thetaCollision theta)

/-- Probability form of the non-duplicated statement split. -/
theorem statementBindingFailure_probability_le_nonterminal_plus_terminal
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
      (scheme := scheme) projection)
    (terminalCandidateFailure : Set Coins)
    (coverage : TerminalCandidateFailureCoverage boundary
      terminalCandidateFailure) :
    measure.real data.base.toEvents.statementBindingFailure ≤
      nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real terminalCandidateFailure := by
  calc
    measure.real data.base.toEvents.statementBindingFailure ≤
        measure.real (nonterminalStatementFailureUnion boundary ∪
          terminalCandidateFailure) :=
      MeasureTheory.measureReal_mono
        (statementBindingFailure_subset_nonterminal_or_terminal boundary
          terminalCandidateFailure coverage)
    _ ≤ measure.real (nonterminalStatementFailureUnion boundary) +
          measure.real terminalCandidateFailure :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ nonterminalStatementFailureProbabilitySum measure boundary +
          measure.real terminalCandidateFailure := by
      gcongr
      exact measureReal_foldr_union_le_sum measure
        (nonterminalStatementFailureEvents boundary)

/-- Accepted-false accounting after moving all four terminal events into one
cap-240 event.  The seven checked ideal terms and four-claim batching still
fit below `2^-75`; every unproved connection remains displayed. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_remaining_failures
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
      (scheme := scheme) projection)
    (terminalCandidateFailure : Set Coins)
    (coverage : TerminalCandidateFailureCoverage boundary
      terminalCandidateFailure)
    (terminalBound : measure.real terminalCandidateFailure ≤
      rawCandidateTerminalBound) :
    measure.real data.base.acceptedFalse ≤
      (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.arithmeticResidualFailure +
        measure.real data.hashMerkleResidualFailure := by
  have statementBound :=
    statementBindingFailure_probability_le_nonterminal_plus_terminal
      measure boundary terminalCandidateFailure coverage
  have projected :=
    acceptedFalse_probability_le_raw_core_plus_projected_failures
      measure data connections
  calc
    measure.real data.base.acceptedFalse ≤
        rawCoreSubtotal + rawFourClaimBatchCollisionBound +
          measure.real data.width19Failure +
          measure.real data.base.toEvents.statementBindingFailure +
          measure.real data.arithmeticResidualFailure +
          measure.real data.hashMerkleResidualFailure := projected
    _ ≤ refinedRawCorePlusFourClaimSubtotal +
          measure.real data.width19Failure +
          nonterminalStatementFailureProbabilitySum measure boundary +
          measure.real data.arithmeticResidualFailure +
          measure.real data.hashMerkleResidualFailure := by
      unfold refinedRawCorePlusFourClaimSubtotal refinedRawCoreSubtotal
      linarith
    _ ≤ (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
          nonterminalStatementFailureProbabilitySum measure boundary +
          measure.real data.arithmeticResidualFailure +
          measure.real data.hashMerkleResidualFailure := by
      gcongr
      exact refined_raw_core_plus_four_claim_le_two_pow_neg_75

/-- Production transfer adds the existing transcript/primitive failure union
without absorbing it into the `2^-75` arithmetic. -/
theorem productionFalseSpend_probability_le_two_pow_neg_75_plus_remaining
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
      (scheme := scheme) projection)
    (terminalCandidateFailure : Set Coins)
    (coverage : TerminalCandidateFailureCoverage boundary
      terminalCandidateFailure)
    (terminalBound : measure.real terminalCandidateFailure ≤
      rawCandidateTerminalBound) :
    measure.real production.productionFalseSpend ≤
      (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
        nonterminalStatementFailureProbabilitySum measure boundary +
        measure.real data.arithmeticResidualFailure +
        measure.real data.hashMerkleResidualFailure +
        measure.real (totalFailure production.transcriptAndHashFailures) := by
  calc
    measure.real production.productionFalseSpend ≤
        measure.real (data.base.acceptedFalse ∪
          totalFailure production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_mono production.production_subset_ideal_or_hash
    _ ≤ measure.real data.base.acceptedFalse +
          measure.real (totalFailure production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (1 : Real) / 2 ^ 75 + measure.real data.width19Failure +
          nonterminalStatementFailureProbabilitySum measure boundary +
          measure.real data.arithmeticResidualFailure +
          measure.real data.hashMerkleResidualFailure +
          measure.real (totalFailure production.transcriptAndHashFailures) := by
      gcongr
      exact acceptedFalse_probability_le_two_pow_neg_75_plus_remaining_failures
        measure data connections projection boundary terminalCandidateFailure
        coverage terminalBound

#print axioms statementBindingFailure_subset_nonterminal_or_terminal
#print axioms statementBindingFailure_probability_le_nonterminal_plus_terminal
#print axioms acceptedFalse_probability_le_two_pow_neg_75_plus_remaining_failures
#print axioms productionFalseSpend_probability_le_two_pow_neg_75_plus_remaining

end AspisV5RefinedAcceptedFalseAccounting
