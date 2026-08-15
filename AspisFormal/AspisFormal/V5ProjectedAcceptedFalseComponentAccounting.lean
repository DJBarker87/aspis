import AspisFormal.V5ProjectedAcceptedFalseRawAccounting
import AspisFormal.V5HashMerkleResidualDecomposition

/-!
# Accepted-false accounting with six application-residual events

This file replaces the last grouped hash/Merkle event in the projected V5
accounting theorem by six exact event sets.  It is still intentionally silent
about their numerical probability: a source/extraction proof must bound each
set.  The contribution here is that those obligations are now exhaustive,
separate, and visible in the final inequality.
-/

namespace AspisV5ProjectedAcceptedFalseComponentAccounting

open MeasureTheory
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5CryptographicAssumptions
open AspisV5ForwardAcceptedFalseRawAccounting
open AspisV5HashMerkleResidualDecomposition
open AspisV5ProjectedAcceptedFalseRawAccounting
open AspisV5RawFinalSecurityAccounting
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

def ownerHashResidualFailureSet
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
    OwnerHashResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def nullifierHashResidualFailureSet
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
    NullifierHashResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def inputNoteHashResidualFailureSet
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
    InputNoteHashResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def outputNoteHashResidualFailureSet
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
    OutputNoteHashResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def inputPathResidualFailureSet
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
    InputPathResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def outputPathResidualFailureSet
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
    OutputPathResidualFailure rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)}

def hashMerkleComponentFailureUnion
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
  (((((ownerHashResidualFailureSet data ∪
      nullifierHashResidualFailureSet data) ∪
      inputNoteHashResidualFailureSet data) ∪
      outputNoteHashResidualFailureSet data) ∪
      inputPathResidualFailureSet data) ∪
      outputPathResidualFailureSet data)

/-- The old grouped event is exactly the union of the six named events. -/
theorem hashMerkleResidualFailure_eq_component_union
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
    data.hashMerkleResidualFailure = hashMerkleComponentFailureUnion data := by
  apply Set.ext
  intro coins
  simp only [ProjectedAcceptedFalseExperimentData.hashMerkleResidualFailure,
    hashMerkleComponentFailureUnion, ownerHashResidualFailureSet,
    nullifierHashResidualFailureSet, inputNoteHashResidualFailureSet,
    outputNoteHashResidualFailureSet, inputPathResidualFailureSet,
    outputPathResidualFailureSet, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨candidate, failure⟩
    rcases (hashMerkleResidualFailure_iff_six_components rc
      ((data.base.relationFamily coins).execution candidate)
      (data.base.challenges coins) (data.base.statement coins)
      (data.base.records coins candidate)).mp failure with
        owner | nullifier | inputNote | outputNote | inputPath | outputPath
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨candidate, owner⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
        ⟨candidate, nullifier⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨candidate, inputNote⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨candidate, outputNote⟩))
    · exact Or.inl (Or.inr ⟨candidate, inputPath⟩)
    · exact Or.inr ⟨candidate, outputPath⟩
  · intro failure
    rcases failure with beforeOutputPath | outputPath
    · rcases beforeOutputPath with beforeInputPath | inputPath
      · rcases beforeInputPath with beforeOutputNote | outputNote
        · rcases beforeOutputNote with beforeInputNote | inputNote
          · rcases beforeInputNote with owner | nullifier
            · rcases owner with ⟨candidate, owner⟩
              exact ⟨candidate,
                (hashMerkleResidualFailure_iff_six_components rc
                  ((data.base.relationFamily coins).execution candidate)
                  (data.base.challenges coins) (data.base.statement coins)
                  (data.base.records coins candidate)).mpr (Or.inl owner)⟩
            · rcases nullifier with ⟨candidate, nullifier⟩
              exact ⟨candidate,
                (hashMerkleResidualFailure_iff_six_components rc
                  ((data.base.relationFamily coins).execution candidate)
                  (data.base.challenges coins) (data.base.statement coins)
                  (data.base.records coins candidate)).mpr
                    (Or.inr (Or.inl nullifier))⟩
          · rcases inputNote with ⟨candidate, inputNote⟩
            exact ⟨candidate,
              (hashMerkleResidualFailure_iff_six_components rc
                ((data.base.relationFamily coins).execution candidate)
                (data.base.challenges coins) (data.base.statement coins)
                (data.base.records coins candidate)).mpr
                  (Or.inr (Or.inr (Or.inl inputNote)))⟩
        · rcases outputNote with ⟨candidate, outputNote⟩
          exact ⟨candidate,
            (hashMerkleResidualFailure_iff_six_components rc
              ((data.base.relationFamily coins).execution candidate)
              (data.base.challenges coins) (data.base.statement coins)
              (data.base.records coins candidate)).mpr
                (Or.inr (Or.inr (Or.inr (Or.inl outputNote))))⟩
      · rcases inputPath with ⟨candidate, inputPath⟩
        exact ⟨candidate,
          (hashMerkleResidualFailure_iff_six_components rc
            ((data.base.relationFamily coins).execution candidate)
            (data.base.challenges coins) (data.base.statement coins)
            (data.base.records coins candidate)).mpr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl inputPath)))))⟩
    · rcases outputPath with ⟨candidate, outputPath⟩
      exact ⟨candidate,
        (hashMerkleResidualFailure_iff_six_components rc
          ((data.base.relationFamily coins).execution candidate)
          (data.base.challenges coins) (data.base.statement coins)
          (data.base.records coins candidate)).mpr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr outputPath)))))⟩

/-- A convenient explicit sum of the six application-residual event
probabilities. -/
def hashMerkleComponentProbabilitySum
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins)
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) : Real :=
  ((((measure.real (ownerHashResidualFailureSet data) +
      measure.real (nullifierHashResidualFailureSet data)) +
      measure.real (inputNoteHashResidualFailureSet data)) +
      measure.real (outputNoteHashResidualFailureSet data)) +
      measure.real (inputPathResidualFailureSet data)) +
      measure.real (outputPathResidualFailureSet data)

theorem hashMerkleResidualFailure_probability_le_component_sum
    {Coins K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)] [MeasurableSpace Coins]
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → AspisFormal.ArithmetizationCore.F →
      AspisFormal.ArithmetizationCore.F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (measure : Measure Coins)
    (data : ProjectedAcceptedFalseExperimentData Coins K rc deployedOwner
      deployedNote deployedNullifier deployedNode) :
    measure.real data.hashMerkleResidualFailure ≤
      hashMerkleComponentProbabilitySum measure data := by
  rw [hashMerkleResidualFailure_eq_component_union data]
  unfold hashMerkleComponentFailureUnion
  unfold hashMerkleComponentProbabilitySum
  calc
    measure.real (((((ownerHashResidualFailureSet data ∪
        nullifierHashResidualFailureSet data) ∪
        inputNoteHashResidualFailureSet data) ∪
        outputNoteHashResidualFailureSet data) ∪
        inputPathResidualFailureSet data) ∪
        outputPathResidualFailureSet data) ≤
      measure.real ((((ownerHashResidualFailureSet data ∪
        nullifierHashResidualFailureSet data) ∪
        inputNoteHashResidualFailureSet data) ∪
        outputNoteHashResidualFailureSet data) ∪
        inputPathResidualFailureSet data) +
        measure.real (outputPathResidualFailureSet data) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (measure.real (((ownerHashResidualFailureSet data ∪
        nullifierHashResidualFailureSet data) ∪
        inputNoteHashResidualFailureSet data) ∪
        outputNoteHashResidualFailureSet data) +
        measure.real (inputPathResidualFailureSet data)) +
        measure.real (outputPathResidualFailureSet data) := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((measure.real ((ownerHashResidualFailureSet data ∪
        nullifierHashResidualFailureSet data) ∪
        inputNoteHashResidualFailureSet data) +
        measure.real (outputNoteHashResidualFailureSet data)) +
        measure.real (inputPathResidualFailureSet data)) +
        measure.real (outputPathResidualFailureSet data) := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ (((measure.real (ownerHashResidualFailureSet data ∪
        nullifierHashResidualFailureSet data) +
        measure.real (inputNoteHashResidualFailureSet data)) +
        measure.real (outputNoteHashResidualFailureSet data)) +
        measure.real (inputPathResidualFailureSet data)) +
        measure.real (outputPathResidualFailureSet data) := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ ((((measure.real (ownerHashResidualFailureSet data) +
        measure.real (nullifierHashResidualFailureSet data)) +
        measure.real (inputNoteHashResidualFailureSet data)) +
        measure.real (outputNoteHashResidualFailureSet data)) +
        measure.real (inputPathResidualFailureSet data)) +
        measure.real (outputPathResidualFailureSet data) := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _

/-- The conservative ideal one-proof endpoint with every remaining
application residual named separately. -/
theorem acceptedFalse_probability_le_two_pow_neg_75_plus_components
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
      ((((1 : Real) / 2 ^ 75 + measure.real data.width19Failure) +
        measure.real data.base.toEvents.statementBindingFailure) +
        measure.real data.arithmeticResidualFailure) +
        hashMerkleComponentProbabilitySum measure data := by
  exact
    (acceptedFalse_probability_le_two_pow_neg_75_plus_projected_failures
      measure data connections).trans (by
        gcongr
        exact hashMerkleResidualFailure_probability_le_component_sum
          measure data)

/-- Production transfer with the six application residuals and the separate
Rust/transcript/hash divergence term all visible. -/
theorem productionFalseSpend_probability_le_two_pow_neg_75_plus_components
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
          measure.real data.base.toEvents.statementBindingFailure) +
          measure.real data.arithmeticResidualFailure) +
          hashMerkleComponentProbabilitySum measure data) +
          measure.real (totalFailure production.transcriptAndHashFailures) := by
      gcongr
      exact acceptedFalse_probability_le_two_pow_neg_75_plus_components
        measure data connections

#print axioms hashMerkleResidualFailure_eq_component_union
#print axioms hashMerkleResidualFailure_probability_le_component_sum
#print axioms acceptedFalse_probability_le_two_pow_neg_75_plus_components
#print axioms productionFalseSpend_probability_le_two_pow_neg_75_plus_components

end AspisV5ProjectedAcceptedFalseComponentAccounting
