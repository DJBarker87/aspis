import AspisFormal.V5AcceptedExecutionReleasedSchedule

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-!
# Mathematical semantics of the release coordinate algorithm

This file proves the group identities used by the focused Aeneas extraction
of `derive_query_fold_inverses_for_circle`.  It deliberately does not mention
the generated Rust definitions: the source-level proof imports these lemmas
and separately proves that the translated loops implement the operations
described here.
-/

namespace AspisV5FriCoordinateMathematics

open AspisCircleGroupOrder
open AspisCircleDiscreteAvailability
open AspisV5FriBitReverse
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriExactLineDomains
open AspisV5FriReleasedLineGeometry
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation

/-! ## Exact split-window reconstruction -/

def lowWindowPoint (index : Nat) : C :=
  g ^ ((2 : Int) ^ 11 + (2 : Int) ^ 13 * index)

def highWindowPoint (index : Nat) : C :=
  g ^ ((2 : Int) ^ 21 * index)

theorem split_17_bit_index (index : Nat) :
    index % 256 + 256 * (index / 256) = index := by
  omega

/-- The two fixed release windows reconstruct the same group point as one
ordinary exponentiation.  The result is valid for every natural index; the
17-bit bound is needed only to index the finite literal arrays. -/
theorem low_mul_high_eq_representative (index : Nat) :
    lowWindowPoint (index % 256) * highWindowPoint (index / 256) =
      g ^ representativeExp index := by
  rw [lowWindowPoint, highWindowPoint, ← zpow_add]
  apply congrArg (fun exponent : Int => g ^ exponent)
  unfold representativeExp
  have hsplit := split_17_bit_index index
  push_cast at hsplit ⊢
  omega

theorem low_index_lt_256 (index : Nat) : index % 256 < 256 := by
  omega

theorem high_index_lt_512 (index : Nat) (hindex : index < 2 ^ 17) :
    index / 256 < 512 := by
  norm_num at hindex ⊢
  omega

private theorem storedInitialFibrePoint_eq_representative
    (index : Fin 131072) :
    storedInitialFibrePoint index =
      g ^ representativeExp (reverseFin 17 index) := by
  rw [storedInitialFibrePoint_eq_zpow]
  apply congrArg (fun exponent : Int => g ^ exponent)
  simp only [storedInitialNaturalIndex_child_zero]
  unfold AspisV5FriCircleEncoderDistance.initialCircleExponent
    representativeExp
  push_cast
  ring

/-- Applying the split windows to the bit-reversed source fibre gives exactly
the maintained slot-zero circle point. -/
theorem windows_reconstruct_storedInitialFibrePoint
    (index : Fin 131072) :
    lowWindowPoint ((reverseFin 17 index).val % 256) *
        highWindowPoint ((reverseFin 17 index).val / 256) =
      storedInitialFibrePoint index := by
  rw [low_mul_high_eq_representative,
    storedInitialFibrePoint_eq_representative]

/-! ## The source slot-normalization operation -/

/-- The deployed quarter turn.  Multiplication by this point maps `(x,y)` to
`(y,-x)`. -/
def quarterTurn : C :=
  ⟨(0, -1), by show (0 : ZMod P) ^ 2 + (-1 : ZMod P) ^ 2 = 1; ring⟩

theorem deployed_quarterTurn : g ^ ((2 : Int) ^ 29) = quarterTurn := by
  rw [show (2 : Int) ^ 29 = ((2 ^ 29 : Nat) : Int) by norm_num,
    zpow_natCast]
  rw [← sq_iterate 29 g]
  decide

/-- Coordinate spelling of `remove_line_slot_rotation` from the production
Rust. -/
def removeLineSlotRotation (point : C) (slot : Fin 4) : C :=
  match slot.val with
  | 0 => point
  | 1 => ⟨(-point.1.1, -point.1.2), by
      have h := point.2
      unfold OnCircle at h ⊢
      show (-point.1.1) ^ 2 + (-point.1.2) ^ 2 = 1
      calc
        (-point.1.1) ^ 2 + (-point.1.2) ^ 2 =
            point.1.1 ^ 2 + point.1.2 ^ 2 := by ring
        _ = 1 := h⟩
  | 2 => ⟨(-point.1.2, point.1.1), by
      have h := point.2
      unfold OnCircle at h ⊢
      show (-point.1.2) ^ 2 + point.1.1 ^ 2 = 1
      calc
        (-point.1.2) ^ 2 + point.1.1 ^ 2 =
            point.1.1 ^ 2 + point.1.2 ^ 2 := by ring
        _ = 1 := h⟩
  | _ => ⟨(point.1.2, -point.1.1), by
      have h := point.2
      unfold OnCircle at h ⊢
      show point.1.2 ^ 2 + (-point.1.1) ^ 2 = 1
      calc
        point.1.2 ^ 2 + (-point.1.1) ^ 2 =
            point.1.1 ^ 2 + point.1.2 ^ 2 := by ring
        _ = 1 := h⟩

private theorem reverseBits2_zero : reverseBits 2 (0 : Nat) = 0 := by decide
private theorem reverseBits2_one : reverseBits 2 (1 : Nat) = 2 := by decide
private theorem reverseBits2_two : reverseBits 2 (2 : Nat) = 1 := by decide
private theorem reverseBits2_three : reverseBits 2 (3 : Nat) = 3 := by decide

private theorem quarterTurn_sq :
    quarterTurn ^ 2 =
      ⟨(-1, 0), by show (-1 : ZMod P) ^ 2 + (0 : ZMod P) ^ 2 = 1; ring⟩ := by
  apply Subtype.ext
  change ((0 : ZMod P) * 0 - (-1) * (-1),
    (0 : ZMod P) * (-1) + (-1) * 0) = (-1, 0)
  norm_num

private theorem quarterTurn_cube :
    quarterTurn ^ 3 =
      ⟨(0, 1), by show (0 : ZMod P) ^ 2 + (1 : ZMod P) ^ 2 = 1; ring⟩ := by
  rw [show 3 = 2 + 1 by omega, pow_add, pow_one, quarterTurn_sq]
  apply Subtype.ext
  change ((-1 : ZMod P) * 0 - 0 * (-1),
    (-1 : ZMod P) * (-1) + 0 * 0) = (0, 1)
  norm_num

/-- The Rust swap/sign table cancels the bit-reversed order-four rotation. -/
theorem removeLineSlotRotation_mul_quarterTurn
    (point : C) (slot : Fin 4) :
    removeLineSlotRotation
        (point * quarterTurn ^ reverseBits 2 slot.val) slot = point := by
  fin_cases slot <;>
    apply Subtype.ext
  · simp [removeLineSlotRotation, reverseBits]
  · rw [reverseBits2_one, quarterTurn_sq]
    simp [removeLineSlotRotation]
  · rw [reverseBits2_two]
    simp [removeLineSlotRotation, quarterTurn]
  · rw [reverseBits2_three, quarterTurn_cube]
    simp [removeLineSlotRotation]

/-! ## Parent routing in the three line layers -/

private theorem storedLine17_child_as_rotation
    (parent : Fin 32768) (slot : Fin 4) :
    storedLine17Point (childIndex parent slot) =
      storedLine17Point (childIndex parent 0) *
        quarterTurn ^ reverseBits 2 slot.val := by
  unfold storedLine17Point line17Point reverseFin
  simp only [childIndex_val]
  rw [← deployed_quarterTurn, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  rw [reverseBits_childIndex 15 parent slot,
    reverseBits_childIndex 15 parent 0]
  simp only [Fin.val_zero, reverseBits2_zero]
  apply congrArg (fun exponent : Int => g ^ exponent)
  push_cast
  ring

theorem normalize_storedLine17_child
    (parent : Fin 32768) (slot : Fin 4) :
    removeLineSlotRotation (storedLine17Point (childIndex parent slot)) slot =
      storedLine17Point (childIndex parent 0) := by
  rw [storedLine17_child_as_rotation]
  exact removeLineSlotRotation_mul_quarterTurn _ _

private theorem storedLine15_child_as_rotation
    (parent : Fin 8192) (slot : Fin 4) :
    storedLine15Point (childIndex parent slot) =
      storedLine15Point (childIndex parent 0) *
        quarterTurn ^ reverseBits 2 slot.val := by
  unfold storedLine15Point line15Point reverseFin
  simp only [childIndex_val]
  rw [← deployed_quarterTurn, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  rw [reverseBits_childIndex 13 parent slot,
    reverseBits_childIndex 13 parent 0]
  simp only [Fin.val_zero, reverseBits2_zero]
  apply congrArg (fun exponent : Int => g ^ exponent)
  push_cast
  ring

theorem normalize_storedLine15_child
    (parent : Fin 8192) (slot : Fin 4) :
    removeLineSlotRotation (storedLine15Point (childIndex parent slot)) slot =
      storedLine15Point (childIndex parent 0) := by
  rw [storedLine15_child_as_rotation]
  exact removeLineSlotRotation_mul_quarterTurn _ _

private theorem storedLine13_child_as_rotation
    (parent : Fin 2048) (slot : Fin 4) :
    storedLine13Point (childIndex parent slot) =
      storedLine13Point (childIndex parent 0) *
        quarterTurn ^ reverseBits 2 slot.val := by
  unfold storedLine13Point line13Point reverseFin
  simp only [childIndex_val]
  rw [← deployed_quarterTurn, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  rw [reverseBits_childIndex 11 parent slot,
    reverseBits_childIndex 11 parent 0]
  simp only [Fin.val_zero, reverseBits2_zero]
  apply congrArg (fun exponent : Int => g ^ exponent)
  push_cast
  ring

theorem normalize_storedLine13_child
    (parent : Fin 2048) (slot : Fin 4) :
    removeLineSlotRotation (storedLine13Point (childIndex parent slot)) slot =
      storedLine13Point (childIndex parent 0) := by
  rw [storedLine13_child_as_rotation]
  exact removeLineSlotRotation_mul_quarterTurn _ _

/-! ## Exact source point sequence -/

/-- The first source derivation (one doubling followed by slot
normalization) produces the slot-zero point of the selected line-1 fibre. -/
theorem circle_child_to_line1_parent (query : Fin 131072) :
    removeLineSlotRotation (storedInitialFibrePoint query ^ 2)
        (slotIndex (n := 32768) query) =
      storedLine17Point
        (childIndex (parentIndex (n := 32768) query) 0) := by
  rw [storedInitialFibrePoint_sq]
  conv_lhs =>
    congr
    · rw [← childIndex_parentIndex_slotIndex (n := 32768) query]
  exact normalize_storedLine17_child _ _

/-- Four group doublings of the selected slot-zero line-1 point, followed by
the source slot normalization, produce the selected line-2 point. -/
theorem line1_child_to_line2_parent (query : Fin 32768) :
    removeLineSlotRotation
        ((storedLine17Point (childIndex query 0)) ^ 4)
        (slotIndex (n := 8192) query) =
      storedLine15Point
        (childIndex (parentIndex (n := 8192) query) 0) := by
  let parent := parentIndex (n := 8192) query
  let slot := slotIndex (n := 8192) query
  have hquery : query = childIndex parent slot := by
    exact (childIndex_parentIndex_slotIndex (n := 8192) query).symm
  rw [hquery]
  simp only [parentIndex_childIndex, slotIndex_childIndex]
  change removeLineSlotRotation
      ((storedLine17Point (childIndex (childIndex parent slot) 0)) ^ 4) slot = _
  have hfirst :
      storedLine17Point (childIndex (childIndex parent slot) 0) ^ 2 =
        storedLine16Point
          (AspisV5FriReleasedLineGeometry.binaryChildIndex
            (childIndex parent slot)) :=
    storedLine17_sq_slot0 (childIndex parent slot)
  have hsecond :
      storedLine16Point
          (AspisV5FriReleasedLineGeometry.binaryChildIndex
            (childIndex parent slot)) ^ 2 =
        storedLine15Point (childIndex parent slot) :=
    storedLine16_sq (childIndex parent slot)
  rw [show (storedLine17Point (childIndex (childIndex parent slot) 0)) ^ 4 =
      (storedLine17Point (childIndex (childIndex parent slot) 0) ^ 2) ^ 2 by
        rw [← pow_mul]]
  rw [hfirst, hsecond]
  exact normalize_storedLine15_child parent slot

/-- The identical relation for the next radix-four line fold. -/
theorem line2_child_to_line3_parent (query : Fin 8192) :
    removeLineSlotRotation
        ((storedLine15Point (childIndex query 0)) ^ 4)
        (slotIndex (n := 2048) query) =
      storedLine13Point
        (childIndex (parentIndex (n := 2048) query) 0) := by
  let parent := parentIndex (n := 2048) query
  let slot := slotIndex (n := 2048) query
  have hquery : query = childIndex parent slot := by
    exact (childIndex_parentIndex_slotIndex (n := 2048) query).symm
  rw [hquery]
  simp only [parentIndex_childIndex, slotIndex_childIndex]
  change removeLineSlotRotation
      ((storedLine15Point (childIndex (childIndex parent slot) 0)) ^ 4) slot = _
  have hfirst :
      storedLine15Point (childIndex (childIndex parent slot) 0) ^ 2 =
        storedLine14Point
          (AspisV5FriReleasedLineGeometry.binaryChildIndex
            (childIndex parent slot)) :=
    storedLine15_sq_slot0 (childIndex parent slot)
  have hsecond :
      storedLine14Point
          (AspisV5FriReleasedLineGeometry.binaryChildIndex
            (childIndex parent slot)) ^ 2 =
        storedLine13Point (childIndex parent slot) :=
    storedLine14_sq (childIndex parent slot)
  rw [show (storedLine15Point (childIndex (childIndex parent slot) 0)) ^ 4 =
      (storedLine15Point (childIndex (childIndex parent slot) 0) ^ 2) ^ 2 by
        rw [← pow_mul]]
  rw [hfirst, hsecond]
  exact normalize_storedLine13_child parent slot

/-! ## Coordinate identities used by the source-output proof -/

/-- The second stored radix-four child carries the y-coordinate of the
slot-zero line-1 circle point as its x-coordinate. -/
theorem storedLine17_slot0_y_eq_slot2_x (index : Fin 32768) :
    (storedLine17Point (childIndex index 0)).1.2 =
      storedLine17X (childIndex index 2) := by
  have hrotation := storedLine17_child_as_rotation index 2
  have hreverse : reverseBits 2 ((2 : Fin 4) : Nat) = 1 := by
    norm_num [reverseBits]
  rw [hreverse, pow_one] at hrotation
  have hx := congrArg X hrotation
  simpa [storedLine17X, X, quarterTurn] using hx.symm

/-- The same y-as-rotated-x identity for the released line-2 domain. -/
theorem storedLine15_slot0_y_eq_slot2_x (index : Fin 8192) :
    (storedLine15Point (childIndex index 0)).1.2 =
      storedLine15X (childIndex index 2) := by
  have hrotation := storedLine15_child_as_rotation index 2
  have hreverse : reverseBits 2 ((2 : Fin 4) : Nat) = 1 := by
    norm_num [reverseBits]
  rw [hreverse, pow_one] at hrotation
  have hx := congrArg X hrotation
  simpa [storedLine15X, X, quarterTurn] using hx.symm

/-- The same y-as-rotated-x identity for the released line-3 domain. -/
theorem storedLine13_slot0_y_eq_slot2_x (index : Fin 2048) :
    (storedLine13Point (childIndex index 0)).1.2 =
      storedLine13X (childIndex index 2) := by
  have hrotation := storedLine13_child_as_rotation index 2
  have hreverse : reverseBits 2 ((2 : Fin 4) : Nat) = 1 := by
    norm_num [reverseBits]
  rw [hreverse, pow_one] at hrotation
  have hx := congrArg X hrotation
  simpa [storedLine13X, X, quarterTurn] using hx.symm

/-! ## Public release-table slot identities -/

theorem released_line1_slot0 (index : Fin 32768) :
    releasedEvaluationPoints.line1 index 0 =
      storedLine17X (childIndex index 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line1_slot1 (index : Fin 32768) :
    releasedEvaluationPoints.line1 index 1 =
      storedLine17X (childIndex index 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line1_slot2 (index : Fin 32768) :
    releasedEvaluationPoints.line1 index 2 =
      storedLine16X (AspisV5FriReleasedLineGeometry.binaryChildIndex index) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line2_slot0 (index : Fin 8192) :
    releasedEvaluationPoints.line2 index 0 =
      storedLine15X (childIndex index 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line2_slot1 (index : Fin 8192) :
    releasedEvaluationPoints.line2 index 1 =
      storedLine15X (childIndex index 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line2_slot2 (index : Fin 8192) :
    releasedEvaluationPoints.line2 index 2 =
      storedLine14X (AspisV5FriReleasedLineGeometry.binaryChildIndex index) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line3_slot0 (index : Fin 2048) :
    releasedEvaluationPoints.line3 index 0 =
      storedLine13X (childIndex index 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line3_slot1 (index : Fin 2048) :
    releasedEvaluationPoints.line3 index 1 =
      storedLine13X (childIndex index 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem released_line3_slot2 (index : Fin 2048) :
    releasedEvaluationPoints.line3 index 2 =
      storedLine12X (AspisV5FriReleasedLineGeometry.binaryChildIndex index) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

theorem storedLine17_point_coordinates (index : Fin 32768) :
    (storedLine17Point (childIndex index 0)).1.1 =
        releasedEvaluationPoints.line1 index 0 ∧
    (storedLine17Point (childIndex index 0)).1.2 =
        releasedEvaluationPoints.line1 index 1 ∧
    2 * (storedLine17Point (childIndex index 0)).1.1 ^ 2 - 1 =
        releasedEvaluationPoints.line1 index 2 := by
  constructor
  · calc
      (storedLine17Point (childIndex index 0)).1.1 =
          storedLine17X (childIndex index 0) := by
        simp only [storedLine17X, X]
      _ = releasedEvaluationPoints.line1 index 0 :=
        (released_line1_slot0 index).symm
  · constructor
    · exact (storedLine17_slot0_y_eq_slot2_x index).trans
        (released_line1_slot1 index).symm
    · calc
        2 * (storedLine17Point (childIndex index 0)).1.1 ^ 2 - 1 =
            AspisCircleTensorBinding.doubledFactor
              (storedLine17X (childIndex index 0)) 1 := by
          simp only [AspisCircleTensorBinding.doubledFactor, storedLine17X, X]
        _ = storedLine16X
              (AspisV5FriReleasedLineGeometry.binaryChildIndex index) :=
          storedLine17_t2_slot0 index
        _ = releasedEvaluationPoints.line1 index 2 :=
          (released_line1_slot2 index).symm

theorem storedLine15_point_coordinates (index : Fin 8192) :
    (storedLine15Point (childIndex index 0)).1.1 =
        releasedEvaluationPoints.line2 index 0 ∧
    (storedLine15Point (childIndex index 0)).1.2 =
        releasedEvaluationPoints.line2 index 1 ∧
    2 * (storedLine15Point (childIndex index 0)).1.1 ^ 2 - 1 =
        releasedEvaluationPoints.line2 index 2 := by
  constructor
  · calc
      (storedLine15Point (childIndex index 0)).1.1 =
          storedLine15X (childIndex index 0) := by
        simp only [storedLine15X, X]
      _ = releasedEvaluationPoints.line2 index 0 :=
        (released_line2_slot0 index).symm
  · constructor
    · exact (storedLine15_slot0_y_eq_slot2_x index).trans
        (released_line2_slot1 index).symm
    · calc
        2 * (storedLine15Point (childIndex index 0)).1.1 ^ 2 - 1 =
            AspisCircleTensorBinding.doubledFactor
              (storedLine15X (childIndex index 0)) 1 := by
          simp only [AspisCircleTensorBinding.doubledFactor, storedLine15X, X]
        _ = storedLine14X
              (AspisV5FriReleasedLineGeometry.binaryChildIndex index) :=
          storedLine15_t2_slot0 index
        _ = releasedEvaluationPoints.line2 index 2 :=
          (released_line2_slot2 index).symm

theorem storedLine13_point_coordinates (index : Fin 2048) :
    (storedLine13Point (childIndex index 0)).1.1 =
        releasedEvaluationPoints.line3 index 0 ∧
    (storedLine13Point (childIndex index 0)).1.2 =
        releasedEvaluationPoints.line3 index 1 ∧
    2 * (storedLine13Point (childIndex index 0)).1.1 ^ 2 - 1 =
        releasedEvaluationPoints.line3 index 2 := by
  constructor
  · calc
      (storedLine13Point (childIndex index 0)).1.1 =
          storedLine13X (childIndex index 0) := by
        simp only [storedLine13X, X]
      _ = releasedEvaluationPoints.line3 index 0 :=
        (released_line3_slot0 index).symm
  · constructor
    · exact (storedLine13_slot0_y_eq_slot2_x index).trans
        (released_line3_slot1 index).symm
    · calc
        2 * (storedLine13Point (childIndex index 0)).1.1 ^ 2 - 1 =
            AspisCircleTensorBinding.doubledFactor
              (storedLine13X (childIndex index 0)) 1 := by
          simp only [AspisCircleTensorBinding.doubledFactor, storedLine13X, X]
        _ = storedLine12X
              (AspisV5FriReleasedLineGeometry.binaryChildIndex index) :=
          storedLine13_t2_slot0 index
        _ = releasedEvaluationPoints.line3 index 2 :=
          (released_line3_slot2 index).symm

#print axioms windows_reconstruct_storedInitialFibrePoint
#print axioms circle_child_to_line1_parent
#print axioms line1_child_to_line2_parent
#print axioms line2_child_to_line3_parent
#print axioms storedLine17_slot0_y_eq_slot2_x
#print axioms storedLine15_slot0_y_eq_slot2_x
#print axioms storedLine13_slot0_y_eq_slot2_x
#print axioms released_line1_slot0
#print axioms released_line1_slot1
#print axioms released_line1_slot2
#print axioms released_line2_slot0
#print axioms released_line2_slot1
#print axioms released_line2_slot2
#print axioms released_line3_slot0
#print axioms released_line3_slot1
#print axioms released_line3_slot2
#print axioms storedLine17_point_coordinates
#print axioms storedLine15_point_coordinates
#print axioms storedLine13_point_coordinates

end AspisV5FriCoordinateMathematics
