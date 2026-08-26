import AspisFormal.Pool.V7AcceptedSpendK15FailureLedger
import AspisFormal.V5CryptographicAssumptions

/-!
# V7 K1.5 failure-event probability composition

The deterministic K1.5 capstone returns one of thirteen typed failure kinds.
This module turns that indexed witness into one exact finite event union and
proves the corresponding measure bound.  It assigns no numerical probability
to an event: fixed-vector root counts, transcript causality and the random-
oracle compiler remain separate inputs to the eventual security ledger.
-/

set_option autoImplicit false

namespace AspisPool.V7K15FailureProbabilityComposition

open AspisPool.V7AcceptedSpendK15FailureLedger

/-- Stable order used by the release probability ledger. -/
def orderedFailureKinds : List FailureKind :=
  [.tenRoundRepair, .helperCancellation, .zerocheckEvaluation, .thetaLane,
    .muZero, .inactiveChi, .activePole, .copyChi, .tupleCompression,
    .oodMix, .relationAlpha, .kappaPointRow, .gammaPointLane]

theorem orderedFailureKinds_length : orderedFailureKinds.length = 13 := by
  decide

theorem mem_orderedFailureKinds (kind : FailureKind) :
    kind ∈ orderedFailureKinds := by
  cases kind <;> simp [orderedFailureKinds]

theorem orderedFailureKinds_exactly_once :
    orderedFailureKinds.Nodup ∧
      ∀ kind : FailureKind, kind ∈ orderedFailureKinds := by
  decide

variable {Coins : Type*} [MeasurableSpace Coins]

/-- One context-dependent K1.5 event as a set of experiment coins. -/
def indexedFailureSet
    (event : Coins → FailureKind → Prop) (kind : FailureKind) : Set Coins :=
  { coins | event coins kind }

/-- Exact finite union of all thirteen deterministic failure branches. -/
def totalK15Failure (event : Coins → FailureKind → Prop) : Set Coins :=
  (orderedFailureKinds.map (indexedFailureSet event)).foldr (· ∪ ·) ∅

omit [MeasurableSpace Coins] in
theorem failureEvidence_implies_mem_totalK15Failure
    (event : Coins → FailureKind → Prop) (coins : Coins) :
    FailureEvidence (event coins) → coins ∈ totalK15Failure event := by
  rintro ⟨kind, holds⟩
  have inSets : indexedFailureSet event kind ∈
      orderedFailureKinds.map (indexedFailureSet event) :=
    List.mem_map.mpr ⟨kind, mem_orderedFailureKinds kind, rfl⟩
  exact AspisV5CryptographicAssumptions.member_subset_foldr_union
    (orderedFailureKinds.map (indexedFailureSet event))
    (indexedFailureSet event kind) inSets holds

/-- Symbolic thirteen-event union bound.  Every failure kind appears exactly
once on the right-hand side. -/
theorem totalK15Failure_probability_le_branch_sum
    (measure : MeasureTheory.Measure Coins)
    (event : Coins → FailureKind → Prop) :
    measure.real (totalK15Failure event) ≤
      (orderedFailureKinds.map
        (fun kind => measure.real (indexedFailureSet event kind))).sum := by
  exact AspisV5CryptographicAssumptions.measureReal_foldr_union_le_sum measure
    (orderedFailureKinds.map (indexedFailureSet event))

/-- Any concrete false-acceptance set covered by the deterministic ledger is
bounded by the same non-duplicated branch sum. -/
theorem covered_attack_probability_le_k15_branch_sum
    (measure : MeasureTheory.Measure Coins)
    [MeasureTheory.IsFiniteMeasure measure]
    (event : Coins → FailureKind → Prop) (attack : Set Coins)
    (covered : ∀ coins, coins ∈ attack → FailureEvidence (event coins)) :
    measure.real attack ≤
      (orderedFailureKinds.map
        (fun kind => measure.real (indexedFailureSet event kind))).sum := by
  have subset : attack ⊆ totalK15Failure event := by
    intro coins member
    exact failureEvidence_implies_mem_totalK15Failure event coins
      (covered coins member)
  exact (MeasureTheory.measureReal_mono subset).trans
    (totalK15Failure_probability_le_branch_sum measure event)

#print axioms orderedFailureKinds_length
#print axioms mem_orderedFailureKinds
#print axioms orderedFailureKinds_exactly_once
#print axioms failureEvidence_implies_mem_totalK15Failure
#print axioms totalK15Failure_probability_le_branch_sum
#print axioms covered_attack_probability_le_k15_branch_sum

end AspisPool.V7K15FailureProbabilityComposition
