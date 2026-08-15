import AspisFormal.V5ForwardAcceptedFalseRawAccounting
import AspisFormal.V5FourClaimSourceEquation
import AspisFormal.V5Width19CandidateEventBridge

/-!
# Raw accounting after the source and width-nineteen projections

The earlier accepted-false theorem left one broad
`relationOrExtractionFailure` set.  This file narrows that set using two exact
connections:

* the production-shaped initial claim and weights satisfy the maintained
  four-claim equation; and
* the candidate's combined-lane mismatch is the named width-nineteen PCS/MCA
  event.

After those connections, the broad set contains only the width-nineteen
event, an arithmetic-residual extraction failure, or a hash/Merkle-residual
extraction failure.  Public-statement binding remains separate.  The final
probability theorem keeps all four terms explicit; it does not assign a
numerical bound to any unproved cryptographic connection.
-/

namespace AspisV5ProjectedAcceptedFalseRawAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5FourClaimBatchUnion
open AspisV5FourClaimSourceEquation
open AspisV5RawFinalSecurityAccounting
open AspisV5RelationStressSourceBridge
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion
open AspisV5Width19CandidateEventBridge
open AspisV5Width19LaneBatchBinding

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-- A candidate together with the experiment outcome that selected it. -/
abbrev CandidateSchedule
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (base : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :=
  Σ coins, base.fri.CandidateAt coins

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
-- Elaborating the dependent candidate schedule traverses the full FRI family.
/-- Exact per-candidate source data needed to split the former broad
relation/extraction event. -/
structure ProjectedAcceptedFalseExperimentData
    (Coins K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (rc : RoundConstants)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest) where
  base : ReleasedIdealAcceptedFalseExperimentData Coins K rc deployedOwner
    deployedNote deployedNullifier deployedNode
  sourceAt : Coins → SourceMode9CallerData K
  columnsAt : Coins → Width19Coefficients K
  widthEvent : CandidateSchedule base → Prop
  exactWidthEvent : ExactWidth19BatchEvent widthEvent
    (fun (schedule : CandidateSchedule base) ↦
      (sourceAt schedule.1).gamma)
    (fun (schedule : CandidateSchedule base) ↦ columnsAt schedule.1)
    (fun (schedule : CandidateSchedule base) ↦
      (base.relationFamily schedule.1).execution schedule.2)
  recordLanes : ∀ (schedule : CandidateSchedule base),
    (base.records schedule.1 schedule.2).lanes =
      ensembleOfWidth19Coefficients (sourceAt schedule.1).gamma
        (columnsAt schedule.1)
  fourClaim : ∀ (schedule : CandidateSchedule base),
    SourceFourClaimProjection (sourceAt schedule.1)
      ((base.relationFamily schedule.1).execution schedule.2)
      (base.records schedule.1 schedule.2)

def ProjectedAcceptedFalseExperimentData.width19Failure
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | ∃ candidate, data.widthEvent ⟨coins, candidate⟩}

def ProjectedAcceptedFalseExperimentData.arithmeticResidualFailure
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | ∃ candidate,
    ArithmeticResidualFailure
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def ProjectedAcceptedFalseExperimentData.hashMerkleResidualFailure
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  {coins | ∃ candidate,
    HashMerkleResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

/-- The old relation/extraction set has exactly three remaining destinations
after the source equation and width-nineteen event are connected. -/
theorem relationOrExtractionFailure_subset_projected
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :
    data.base.toEvents.relationOrExtractionFailure ⊆
      (data.width19Failure ∪ data.arithmeticResidualFailure) ∪
        data.hashMerkleResidualFailure := by
  intro coins failure
  rcases failure with ⟨candidate, failure⟩
  let schedule : CandidateSchedule data.base := ⟨coins, candidate⟩
  rcases failure with equation | combined | arithmetic | hashMerkle
  · exact False.elim
      ((no_four_claim_batch_equation_failure_of_source_projection
        (data.sourceAt coins)
        ((data.base.relationFamily coins).execution candidate)
        (data.base.challenges coins) (data.base.records coins candidate)
        (data.fourClaim schedule)) equation)
  · apply Or.inl
    apply Or.inl
    exact ⟨candidate,
      (combinedLaneBindingFailure_iff_exact_width19_event data.widthEvent
        (fun item ↦ (data.sourceAt item.1).gamma)
        (fun item ↦ data.columnsAt item.1)
        (fun item ↦
          (data.base.relationFamily item.1).execution item.2)
        (fun item ↦ data.base.records item.1 item.2)
        data.exactWidthEvent data.recordLanes schedule).mp combined⟩
  · exact Or.inl (Or.inr ⟨candidate, arithmetic⟩)
  · exact Or.inr ⟨candidate, hashMerkle⟩

/-- The final explicit union after removing the two deterministic connection
branches from the earlier accounting theorem. -/
def ProjectedAcceptedFalseExperimentData.projectedFailureUnion
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Set Coins :=
  (((((rawOneProofCoreFailure data.base.toEvents.coreLedger ∪
      data.base.toEvents.fourClaimBatchCollision) ∪ data.width19Failure) ∪
      data.base.toEvents.statementBindingFailure) ∪
      data.arithmeticResidualFailure) ∪ data.hashMerkleResidualFailure)

/-- Every ideal accepted false spend lies in the checked raw core, the
four-claim collision, or one of the four explicitly unbounded connection
events. -/
theorem acceptedFalse_subset_projectedFailureUnion
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :
    data.base.acceptedFalse ⊆ data.projectedFailureUnion := by
  intro coins accepted
  have earlier :=
    (released_ideal_accepted_false_subset_core_plus_explicit
      data.base.toEvents data.base.toEvents_coverage) accepted
  rcases earlier with ((core | batch) | relation) | statement
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl core))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr batch))))
  · rcases relationOrExtractionFailure_subset_projected data relation with
      (width19 | arithmetic) | hashMerkle
    · exact Or.inl (Or.inl (Or.inl (Or.inr width19)))
    · exact Or.inl (Or.inr arithmetic)
    · exact Or.inr hashMerkle
  · exact Or.inl (Or.inl (Or.inr statement))

/-- Honest raw one-proof accounting after the exact projections.  The first
two terms are proved numerical bounds; the following four measures are
displayed because their production/cryptographic bounds remain premises. -/
theorem acceptedFalse_probability_le_raw_core_plus_projected_failures
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents) :
    measure.real data.base.acceptedFalse ≤
      ((((rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
        measure.real data.width19Failure) +
        measure.real data.base.toEvents.statementBindingFailure) +
        measure.real data.arithmeticResidualFailure) +
        measure.real data.hashMerkleResidualFailure := by
  have coreBound :
      measure.real (rawOneProofCoreFailure data.base.toEvents.coreLedger) ≤
        rawCoreSubtotal :=
    raw_one_proof_core_probability_le_subtotal measure
      data.base.toEvents.coreLedger
      (connections.toCoreBounds measure data.base.toEvents)
  calc
    measure.real data.base.acceptedFalse ≤
        measure.real data.projectedFailureUnion :=
      MeasureTheory.measureReal_mono
        (acceptedFalse_subset_projectedFailureUnion data)
    _ ≤ measure.real
          (((rawOneProofCoreFailure data.base.toEvents.coreLedger ∪
            data.base.toEvents.fourClaimBatchCollision) ∪
            data.width19Failure) ∪
            data.base.toEvents.statementBindingFailure ∪
            data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (measure.real
          (((rawOneProofCoreFailure data.base.toEvents.coreLedger ∪
            data.base.toEvents.fourClaimBatchCollision) ∪
            data.width19Failure) ∪
            data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((measure.real
          ((rawOneProofCoreFailure data.base.toEvents.coreLedger ∪
            data.base.toEvents.fourClaimBatchCollision) ∪
            data.width19Failure) +
          measure.real data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ (((measure.real
          (rawOneProofCoreFailure data.base.toEvents.coreLedger ∪
            data.base.toEvents.fourClaimBatchCollision) +
          measure.real data.width19Failure) +
          measure.real data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((measure.real
          (rawOneProofCoreFailure data.base.toEvents.coreLedger) +
          measure.real data.base.toEvents.fourClaimBatchCollision) +
          measure.real data.width19Failure) +
          measure.real data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((rawCoreSubtotal + rawFourClaimBatchCollisionBound) +
          measure.real data.width19Failure) +
          measure.real data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure := by
      gcongr
      exact connections.fourClaimBatchCollision

/-- The same result with the checked ideal-core and four-claim terms replaced
by the conservative `2^-75` one-proof endpoint. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_projected_failures
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents) :
    measure.real data.base.acceptedFalse ≤
      (((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        measure.real data.base.toEvents.statementBindingFailure) +
        measure.real data.arithmeticResidualFailure) +
        measure.real data.hashMerkleResidualFailure) := by
  exact
    (acceptedFalse_probability_le_raw_core_plus_projected_failures measure data
      connections).trans (by
        gcongr
        exact raw_core_plus_four_claim_batch_le_two_pow_neg_75)

/-- Production transfer.  Rust transcript/hash divergence is added as one
further explicit term; it is not folded into the `2^-75` ideal-core number. -/
theorem productionFalseSpend_probability_le_two_pow_neg_75_plus_projected
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins) [IsProbabilityMeasure measure]
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode)
    (connections : ReleasedIdealAcceptedFalseRawConnections measure
      data.base.toEvents)
    (production : ReleasedProductionFalseSpendConnection data.base.toEvents) :
    measure.real production.productionFalseSpend ≤
      (((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        measure.real data.base.toEvents.statementBindingFailure) +
        measure.real data.arithmeticResidualFailure) +
        measure.real data.hashMerkleResidualFailure) +
        measure.real (AspisV5CryptographicAssumptions.totalFailure
          production.transcriptAndHashFailures) := by
  calc
    measure.real production.productionFalseSpend ≤
        measure.real (data.base.acceptedFalse ∪
          AspisV5CryptographicAssumptions.totalFailure
            production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_mono
        production.production_subset_ideal_or_hash
    _ ≤ measure.real data.base.acceptedFalse +
          measure.real (AspisV5CryptographicAssumptions.totalFailure
            production.transcriptAndHashFailures) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
          measure.real data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          measure.real data.hashMerkleResidualFailure) +
          measure.real (AspisV5CryptographicAssumptions.totalFailure
            production.transcriptAndHashFailures) := by
      gcongr
      exact
        acceptedFalse_probability_le_two_pow_neg_75_plus_projected_failures
          measure data connections

#print axioms relationOrExtractionFailure_subset_projected
#print axioms acceptedFalse_subset_projectedFailureUnion
#print axioms acceptedFalse_probability_le_raw_core_plus_projected_failures
#print axioms acceptedFalse_probability_le_two_pow_neg_75_plus_projected_failures
#print axioms productionFalseSpend_probability_le_two_pow_neg_75_plus_projected

end AspisV5ProjectedAcceptedFalseRawAccounting
