import AspisFormal.CircleDiscreteAvailability
import AspisFormal.V5AcceptedExecutionSecurityBridge
import AspisFormal.V5FriReleasedEncoderApplicability

set_option maxRecDepth 20000

/-!
# The released V5 FRI tables in the accepted-execution theorem

This file keeps two facts separate.

* Lean constructs the exact released evaluation and inverse tables and proves
  the equations required by the accepted-execution theorem.
* Equality between those mathematical tables and the arrays used by the
  production Rust verifier is the explicitly named
  `ProductionUsesReleasedFriTables` source boundary.  The exhaustive Rust
  tests check that boundary entry by entry; this file does not pretend that a
  Rust test is a Lean theorem about the source.

The only external coding-theory statement used below remains
`PublishedOrdinaryPolynomialCurveDecoding`.
-/

namespace AspisV5AcceptedExecutionReleasedSchedule

open AspisCircleDiscreteAvailability
open AspisCircleGroupOrder
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriBitReverse
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriExactLineDomains
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriPublishedOutputEncoderDecoding
open AspisV5FriRelationCandidateBridge
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5FriReleasedLineGeometry
open AspisV5MerkleAuthenticationBinding
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5Tag67AcceptedFalseInclusion
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67ModeledRelationAcceptanceBridge
open AspisV5Tag67RelationListInclusion
open AspisV5TranscriptConnection
open AspisV5WithoutReplacementQuerySoundness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K] [NeZero (2 : K)]

/-! ## Nonzero released coordinates -/

private theorem storedInitialFibrePoint_eq_representative
    (i : Fin layer1Symbols) :
    storedInitialFibrePoint i =
      g ^ representativeExp (reverseFin 17 i) := by
  rw [storedInitialFibrePoint_eq_zpow]
  apply congrArg (fun exponent : Int => g ^ exponent)
  simp only [storedInitialNaturalIndex_child_zero]
  unfold AspisV5FriCircleEncoderDistance.initialCircleExponent representativeExp
  push_cast
  ring

theorem released_circle_x_ne_zero (i : Fin layer1Symbols) :
    releasedEvaluationPoints.circleX i ≠ 0 := by
  change X (storedInitialFibrePoint i) ≠ 0
  rw [storedInitialFibrePoint_eq_representative]
  exact representative_x_ne_zero (reverseFin 17 i)

theorem released_circle_y_ne_zero (i : Fin layer1Symbols) :
    releasedEvaluationPoints.circleY i ≠ 0 := by
  change (storedInitialFibrePoint i).1.2 ≠ 0
  rw [storedInitialFibrePoint_eq_representative]
  exact representative_y_ne_zero (reverseFin 17 i)

private theorem line17_x_ne_zero (i : Nat) :
    X (g ^ (4096 + 16384 * (i : Int))) ≠ 0 := by
  intro hz
  have hx : X (g ^ (4096 + 16384 * (i : Int))) =
      X (g ^ (2 ^ 29 : Int)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp
    (4096 + 16384 * (i : Int)) (2 ^ 29 : Int)).mp hx
  unfold Int.ModEq at hm
  rcases hm with hm | hm <;> omega

private theorem line16_x_ne_zero (i : Nat) :
    X (g ^ (8192 + 32768 * (i : Int))) ≠ 0 := by
  intro hz
  have hx : X (g ^ (8192 + 32768 * (i : Int))) =
      X (g ^ (2 ^ 29 : Int)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp
    (8192 + 32768 * (i : Int)) (2 ^ 29 : Int)).mp hx
  unfold Int.ModEq at hm
  rcases hm with hm | hm <;> omega

private theorem line15_x_ne_zero (i : Nat) :
    X (g ^ (16384 + 65536 * (i : Int))) ≠ 0 := by
  intro hz
  have hx : X (g ^ (16384 + 65536 * (i : Int))) =
      X (g ^ (2 ^ 29 : Int)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp
    (16384 + 65536 * (i : Int)) (2 ^ 29 : Int)).mp hx
  unfold Int.ModEq at hm
  rcases hm with hm | hm <;> omega

private theorem line14_x_ne_zero (i : Nat) :
    X (g ^ (32768 + 131072 * (i : Int))) ≠ 0 := by
  intro hz
  have hx : X (g ^ (32768 + 131072 * (i : Int))) =
      X (g ^ (2 ^ 29 : Int)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp
    (32768 + 131072 * (i : Int)) (2 ^ 29 : Int)).mp hx
  unfold Int.ModEq at hm
  rcases hm with hm | hm <;> omega

private theorem line13_x_ne_zero (i : Nat) :
    X (g ^ (65536 + 262144 * (i : Int))) ≠ 0 := by
  intro hz
  have hx : X (g ^ (65536 + 262144 * (i : Int))) =
      X (g ^ (2 ^ 29 : Int)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp
    (65536 + 262144 * (i : Int)) (2 ^ 29 : Int)).mp hx
  unfold Int.ModEq at hm
  rcases hm with hm | hm <;> omega

private theorem line12_x_ne_zero (i : Nat) :
    X (g ^ (131072 + 524288 * (i : Int))) ≠ 0 := by
  intro hz
  have hx : X (g ^ (131072 + 524288 * (i : Int))) =
      X (g ^ (2 ^ 29 : Int)) := by
    rw [hz, quarterTurn_x_zero]
  have hm := (sameXCoord_exp
    (131072 + 524288 * (i : Int)) (2 ^ 29 : Int)).mp hx
  unfold Int.ModEq at hm
  rcases hm with hm | hm <;> omega

private theorem storedLine17X_ne_zero (i : Fin layer1Symbols) :
    storedLine17X i ≠ 0 := by
  exact line17_x_ne_zero (reverseFin 17 i)

private theorem storedLine16X_ne_zero (i : Fin (2 * layer2Symbols)) :
    storedLine16X i ≠ 0 := by
  exact line16_x_ne_zero (reverseFin 16 i)

private theorem storedLine15X_ne_zero (i : Fin layer2Symbols) :
    storedLine15X i ≠ 0 := by
  exact line15_x_ne_zero (reverseFin 15 i)

private theorem storedLine14X_ne_zero (i : Fin (2 * layer3Symbols)) :
    storedLine14X i ≠ 0 := by
  exact line14_x_ne_zero (reverseFin 14 i)

private theorem storedLine13X_ne_zero (i : Fin layer3Symbols) :
    storedLine13X i ≠ 0 := by
  exact line13_x_ne_zero (reverseFin 13 i)

private theorem storedLine12X_ne_zero (i : Fin (2 * layer4Symbols)) :
    storedLine12X i ≠ 0 := by
  exact line12_x_ne_zero (reverseFin 12 i)

private theorem releasedLine1_zero_local (i : Fin layer2Symbols) :
    releasedEvaluationPoints.line1 i 0 =
      storedLine17X (childIndex i 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine1_one_local (i : Fin layer2Symbols) :
    releasedEvaluationPoints.line1 i 1 =
      storedLine17X (childIndex i 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine1_two_local (i : Fin layer2Symbols) :
    releasedEvaluationPoints.line1 i 2 =
      storedLine16X (binaryChildIndex i) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine2_zero_local (i : Fin layer3Symbols) :
    releasedEvaluationPoints.line2 i 0 =
      storedLine15X (childIndex i 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine2_one_local (i : Fin layer3Symbols) :
    releasedEvaluationPoints.line2 i 1 =
      storedLine15X (childIndex i 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine2_two_local (i : Fin layer3Symbols) :
    releasedEvaluationPoints.line2 i 2 =
      storedLine14X (binaryChildIndex i) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine3_zero_local (i : Fin layer4Symbols) :
    releasedEvaluationPoints.line3 i 0 =
      storedLine13X (childIndex i 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine3_one_local (i : Fin layer4Symbols) :
    releasedEvaluationPoints.line3 i 1 =
      storedLine13X (childIndex i 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

private theorem releasedLine3_two_local (i : Fin layer4Symbols) :
    releasedEvaluationPoints.line3 i 2 =
      storedLine12X (binaryChildIndex i) := by
  simp [releasedEvaluationPoints, releasedLinePoints]

theorem released_line1_ne_zero (i : Fin layer2Symbols) (slot : Fin 3) :
    releasedEvaluationPoints.line1 i slot ≠ 0 := by
  by_cases hzero : slot = 0
  · subst slot
    rw [releasedLine1_zero_local]
    exact storedLine17X_ne_zero (childIndex i 0)
  by_cases hone : slot = 1
  · subst slot
    rw [releasedLine1_one_local]
    exact storedLine17X_ne_zero (childIndex i 2)
  have htwo : slot = 2 := by
    apply Fin.ext
    have hlt := slot.isLt
    omega
  subst slot
  rw [releasedLine1_two_local]
  exact storedLine16X_ne_zero (binaryChildIndex i)

theorem released_line2_ne_zero (i : Fin layer3Symbols) (slot : Fin 3) :
    releasedEvaluationPoints.line2 i slot ≠ 0 := by
  by_cases hzero : slot = 0
  · subst slot
    rw [releasedLine2_zero_local]
    exact storedLine15X_ne_zero (childIndex i 0)
  by_cases hone : slot = 1
  · subst slot
    rw [releasedLine2_one_local]
    exact storedLine15X_ne_zero (childIndex i 2)
  have htwo : slot = 2 := by
    apply Fin.ext
    have hlt := slot.isLt
    omega
  subst slot
  rw [releasedLine2_two_local]
  exact storedLine14X_ne_zero (binaryChildIndex i)

theorem released_line3_ne_zero (i : Fin layer4Symbols) (slot : Fin 3) :
    releasedEvaluationPoints.line3 i slot ≠ 0 := by
  by_cases hzero : slot = 0
  · subst slot
    rw [releasedLine3_zero_local]
    exact storedLine13X_ne_zero (childIndex i 0)
  by_cases hone : slot = 1
  · subst slot
    rw [releasedLine3_one_local]
    exact storedLine13X_ne_zero (childIndex i 2)
  have htwo : slot = 2 := by
    apply Fin.ext
    have hlt := slot.isLt
    omega
  subst slot
  rw [releasedLine3_two_local]
  exact storedLine12X_ne_zero (binaryChildIndex i)

/-! ## Exact mathematical schedule and explicit Rust boundary -/

/-- Replace the inverse and final-domain fields by their exact mathematical
released values.  Challenges and query scheduling fields are unchanged. -/
def exactReleasedFriTables
    (schedule : FixedSchedule (ZMod P) K) : FixedSchedule (ZMod P) K :=
  { schedule with
    circleInv2x := fun i =>
      (2 * releasedEvaluationPoints.circleX i)⁻¹
    circleInv2y := fun i =>
      (2 * releasedEvaluationPoints.circleY i)⁻¹
    line1Inverse := fun i slot =>
      (2 * releasedEvaluationPoints.line1 i slot)⁻¹
    line2Inverse := fun i slot =>
      (2 * releasedEvaluationPoints.line2 i slot)⁻¹
    line3Inverse := fun i slot =>
      (2 * releasedEvaluationPoints.line3 i slot)⁻¹
    finalX := storedLine11X }

/-- This is the precise source-correspondence statement checked entry by entry
by the exhaustive Rust tests.  It remains named rather than being folded into
the mathematical theorem. -/
structure ProductionUsesReleasedFriTables
    (schedule : FixedSchedule (ZMod P) K) : Prop where
  finalX : forall i, schedule.finalX i = storedLine11X i
  circleInv2x : forall i, schedule.circleInv2x i =
    (2 * releasedEvaluationPoints.circleX i)⁻¹
  circleInv2y : forall i, schedule.circleInv2y i =
    (2 * releasedEvaluationPoints.circleY i)⁻¹
  line1Inverse : forall i slot, schedule.line1Inverse i slot =
    (2 * releasedEvaluationPoints.line1 i slot)⁻¹
  line2Inverse : forall i slot, schedule.line2Inverse i slot =
    (2 * releasedEvaluationPoints.line2 i slot)⁻¹
  line3Inverse : forall i slot, schedule.line3Inverse i slot =
    (2 * releasedEvaluationPoints.line3 i slot)⁻¹

set_option maxHeartbeats 1000000 in
-- Elaborating all six function-valued record equalities needs the larger cap.
theorem exactReleasedFriTables_source_shape
    (schedule : FixedSchedule (ZMod P) K) :
    ProductionUsesReleasedFriTables (exactReleasedFriTables schedule) where
  finalX _ := rfl
  circleInv2x _ := rfl
  circleInv2y _ := rfl
  line1Inverse _ _ := rfl
  line2Inverse _ _ := rfl
  line3Inverse _ _ := rfl

theorem finalXMatches_of_production_tables
    {schedule : FixedSchedule (ZMod P) K}
    (hsource : ProductionUsesReleasedFriTables schedule) :
    FinalXMatchesReleasedDomain schedule := hsource.finalX

theorem inverseTablesComputed_of_production_tables
    {schedule : FixedSchedule (ZMod P) K}
    (hsource : ProductionUsesReleasedFriTables schedule) :
    InverseTablesComputed schedule releasedEvaluationPoints where
  circleXNonzero i := mul_ne_zero two_ne_zero_ZModP
    (released_circle_x_ne_zero i)
  circleYNonzero i := mul_ne_zero two_ne_zero_ZModP
    (released_circle_y_ne_zero i)
  line1Nonzero i slot := mul_ne_zero two_ne_zero_ZModP
    (released_line1_ne_zero i slot)
  line2Nonzero i slot := mul_ne_zero two_ne_zero_ZModP
    (released_line2_ne_zero i slot)
  line3Nonzero i slot := mul_ne_zero two_ne_zero_ZModP
    (released_line3_ne_zero i slot)
  circleX := hsource.circleInv2x
  circleY := hsource.circleInv2y
  line1 := hsource.line1Inverse
  line2 := hsource.line2Inverse
  line3 := hsource.line3Inverse

theorem inverseTablesMatch_of_production_tables
    {schedule : FixedSchedule (ZMod P) K}
    (hsource : ProductionUsesReleasedFriTables schedule) :
    InverseTablesMatch schedule releasedEvaluationPoints :=
  inverseTablesMatch_of_computed schedule releasedEvaluationPoints
    (inverseTablesComputed_of_production_tables hsource)

theorem exactReleasedFriTables_match
    (schedule : FixedSchedule (ZMod P) K) :
    FinalXMatchesReleasedDomain (exactReleasedFriTables schedule) /\
      InverseTablesMatch (exactReleasedFriTables schedule)
        releasedEvaluationPoints := by
  let hsource := exactReleasedFriTables_source_shape schedule
  exact ⟨finalXMatches_of_production_tables hsource,
    inverseTablesMatch_of_production_tables hsource⟩

/-! ## Removing the impossible schedule branches -/

/-- Remove the two released-table failure constructors and the failure of the
published decoding premise from an accepted-execution result once their
positive facts are available.  Every other constructor is preserved exactly.
-/
theorem remove_released_table_and_published_failures
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      releasedFinalDomainFailure releasedInverseTableFailure
      referenceForestFailure globalCausalSelectionFailure
      rustOpeningCorrespondenceFailure hashCollision workFailure
      friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure publishedDecodingFailure : Prop}
    (hfinal : ¬ releasedFinalDomainFailure)
    (htables : ¬ releasedInverseTableFailure)
    (hpublished : ¬ publishedDecodingFailure)
    (event : AcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      releasedFinalDomainFailure releasedInverseTableFailure
      referenceForestFailure globalCausalSelectionFailure
      rustOpeningCorrespondenceFailure hashCollision workFailure
      friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure publishedDecodingFailure) :
    AcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      False False
      referenceForestFailure globalCausalSelectionFailure
      rustOpeningCorrespondenceFailure hashCollision workFailure
      friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure False := by
  cases event with
  | sourceRelationProjection failure =>
      exact .sourceRelationProjection failure
  | familyProjection failure => exact .familyProjection failure
  | transcriptProjection failure => exact .transcriptProjection failure
  | workProjection failure => exact .workProjection failure
  | releasedFinalDomain failure => exact (hfinal failure).elim
  | releasedInverseTable failure => exact (htables failure).elim
  | referenceForest failure => exact .referenceForest failure
  | globalCausalSelection failure => exact .globalCausalSelection failure
  | rustOpeningCorrespondence failure =>
      exact .rustOpeningCorrespondence failure
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact .workCheck failure
  | friArithmetic failure => exact .friArithmetic failure
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact (hpublished failure).elim

/-- Apply the previous elimination directly to the result type of
`accepted_false_source_execution_event`.

`hsource` is the explicitly named production-table correspondence checked by
the exhaustive Rust tests.  `hpublished` is the sole external mathematical
premise in this wrapper.  The conclusion leaves every other implementation,
authentication, transcript, primitive, and extraction failure unchanged. -/
theorem accepted_event_with_released_tables
    {schedule : FixedSchedule (ZMod P) K}
    (hsource : ProductionUsesReleasedFriTables schedule)
    (hpublished : PublishedOrdinaryPolynomialCurveDecoding (K := K))
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure globalCausalSelectionFailure
      rustOpeningCorrespondenceFailure hashCollision workFailure
      friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure : Prop}
    (event : AcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      (¬ FinalXMatchesReleasedDomain schedule)
      (¬ InverseTablesMatch schedule releasedEvaluationPoints)
      referenceForestFailure globalCausalSelectionFailure
      rustOpeningCorrespondenceFailure hashCollision workFailure
      friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure
      (¬ PublishedOrdinaryPolynomialCurveDecoding (K := K))) :
    AcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      False False
      referenceForestFailure globalCausalSelectionFailure
      rustOpeningCorrespondenceFailure hashCollision workFailure
      friArithmeticFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure False := by
  apply remove_released_table_and_published_failures
    (event := event)
  · intro failure
    exact failure (finalXMatches_of_production_tables hsource)
  · intro failure
    exact failure (inverseTablesMatch_of_production_tables hsource)
  · intro failure
    exact failure hpublished

/-! ## Audit -/

#print axioms released_circle_x_ne_zero
#print axioms released_circle_y_ne_zero
#print axioms released_line1_ne_zero
#print axioms released_line2_ne_zero
#print axioms released_line3_ne_zero
#print axioms exactReleasedFriTables_match
#print axioms finalXMatches_of_production_tables
#print axioms inverseTablesMatch_of_production_tables
#print axioms remove_released_table_and_published_failures
#print axioms accepted_event_with_released_tables

end AspisV5AcceptedExecutionReleasedSchedule
