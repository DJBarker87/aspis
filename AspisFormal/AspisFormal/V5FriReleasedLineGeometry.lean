import AspisFormal.V5FriBitReverse
import AspisFormal.V5FriExactLineDomains
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V5FriInitialCircleEncoderIdentity

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

/-!
# Released V5 line-domain geometry

The V5 line words are stored in bit-reversed order.  This file constructs
their exact M31 evaluation points and proves the radix-four fibre identities
used by the recursive encoders.  In particular, this removes the abstract
line-geometry premise from the Reed--Solomon realization of the four released
output encoders.
-/

namespace AspisV5FriReleasedLineGeometry

open AspisCircleGroupOrder
open AspisV5FriBitReverse
open AspisV5FriExactLineDomains
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisCircleTensorBinding
open AspisV5FriInitialListBound

/-! ## Stored, bit-reversed line domains -/

def line16Point (i : Fin 65536) : C :=
  g ^ (8192 + 32768 * (i : Int))

def line14Point (i : Fin 16384) : C :=
  g ^ (32768 + 131072 * (i : Int))

def line12Point (i : Fin 4096) : C :=
  g ^ (131072 + 524288 * (i : Int))

def storedLine17Point (i : Fin 131072) : C :=
  line17Point (reverseFin 17 i)

def storedLine16Point (i : Fin 65536) : C :=
  line16Point (reverseFin 16 i)

def storedLine15Point (i : Fin 32768) : C :=
  line15Point (reverseFin 15 i)

def storedLine14Point (i : Fin 16384) : C :=
  line14Point (reverseFin 14 i)

def storedLine13Point (i : Fin 8192) : C :=
  line13Point (reverseFin 13 i)

def storedLine12Point (i : Fin 4096) : C :=
  line12Point (reverseFin 12 i)

def storedLine11Point (i : Fin 2048) : C :=
  line11Point (reverseFin 11 i)

def storedLine17X (i : Fin 131072) : ZMod P := X (storedLine17Point i)
def storedLine16X (i : Fin 65536) : ZMod P := X (storedLine16Point i)
def storedLine15X (i : Fin 32768) : ZMod P := X (storedLine15Point i)
def storedLine14X (i : Fin 16384) : ZMod P := X (storedLine14Point i)
def storedLine13X (i : Fin 8192) : ZMod P := X (storedLine13Point i)
def storedLine12X (i : Fin 4096) : ZMod P := X (storedLine12Point i)
def storedLine11X (i : Fin 2048) : ZMod P := X (storedLine11Point i)

theorem storedLine17X_injective : Function.Injective storedLine17X := by
  intro i j hij
  apply reverseFin_injective 17
  apply line17X_injective
  exact hij

theorem storedLine15X_injective : Function.Injective storedLine15X := by
  intro i j hij
  apply reverseFin_injective 15
  apply line15X_injective
  exact hij

theorem storedLine13X_injective : Function.Injective storedLine13X := by
  intro i j hij
  apply reverseFin_injective 13
  apply line13X_injective
  exact hij

theorem storedLine11X_injective : Function.Injective storedLine11X := by
  intro i j hij
  apply reverseFin_injective 11
  apply line11X_injective
  exact hij

/-! ## The released radix-four coordinates -/

/-- Index `2*i` in the intermediate line domain used by the second binary
fold inside one radix-four fibre. -/
def binaryChildIndex {n : Nat} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i, by omega⟩

private theorem reverseBits17_child (i : Fin 32768) (slot : Fin 4) :
    reverseBits 17 (4 * (i : Nat) + slot) =
      reverseBits 15 i + 32768 * reverseBits 2 slot := by
  simpa using reverseBits_childIndex 15 (i : Nat) slot

private theorem reverseBits15_child (i : Fin 8192) (slot : Fin 4) :
    reverseBits 15 (4 * (i : Nat) + slot) =
      reverseBits 13 i + 8192 * reverseBits 2 slot := by
  simpa using reverseBits_childIndex 13 (i : Nat) slot

private theorem reverseBits13_child (i : Fin 2048) (slot : Fin 4) :
    reverseBits 13 (4 * (i : Nat) + slot) =
      reverseBits 11 i + 2048 * reverseBits 2 slot := by
  simpa using reverseBits_childIndex 11 (i : Nat) slot

private theorem reverseBits16_binary (i : Fin 32768) :
    reverseBits 16 (2 * (i : Nat)) = reverseBits 15 i := by
  simpa using reverseBits_two_mul 15 (i : Nat)

private theorem reverseBits14_binary (i : Fin 8192) :
    reverseBits 14 (2 * (i : Nat)) = reverseBits 13 i := by
  simpa using reverseBits_two_mul 13 (i : Nat)

private theorem reverseBits12_binary (i : Fin 2048) :
    reverseBits 12 (2 * (i : Nat)) = reverseBits 11 i := by
  simpa using reverseBits_two_mul 11 (i : Nat)

private theorem reverseBits16_binary_int (i : Fin 32768) :
    ((reverseBits 16 (2 * (i : Nat)) : Nat) : Int) =
      reverseBits 15 i :=
  congrArg (fun n : Nat => (n : Int)) (reverseBits16_binary i)

private theorem reverseBits14_binary_int (i : Fin 8192) :
    ((reverseBits 14 (2 * (i : Nat)) : Nat) : Int) =
      reverseBits 13 i :=
  congrArg (fun n : Nat => (n : Int)) (reverseBits14_binary i)

private theorem reverseBits12_binary_int (i : Fin 2048) :
    ((reverseBits 12 (2 * (i : Nat)) : Nat) : Int) =
      reverseBits 11 i :=
  congrArg (fun n : Nat => (n : Int)) (reverseBits12_binary i)

private theorem reverseBits2_zero :
    reverseBits 2 ((0 : Fin 4) : Nat) = 0 := by
  norm_num [reverseBits]

private theorem reverseBits2_one :
    reverseBits 2 ((1 : Fin 4) : Nat) = 2 := by
  norm_num [reverseBits]

private theorem reverseBits2_two :
    reverseBits 2 ((2 : Fin 4) : Nat) = 1 := by
  norm_num [reverseBits]

private theorem reverseBits2_three :
    reverseBits 2 ((3 : Fin 4) : Nat) = 3 := by
  norm_num [reverseBits]

theorem storedLine17_slot1 (i : Fin 32768) :
    storedLine17X (childIndex i 1) =
      -storedLine17X (childIndex i 0) := by
  unfold storedLine17X storedLine17Point line17Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits17_child i 1, reverseBits17_child i 0]
  rw [reverseBits2_one, reverseBits2_zero]
  push_cast
  simp only [add_zero]
  rw [show (4096 : Int) + 16384 *
        (reverseBits 15 i + 65536) =
      (4096 + 16384 * reverseBits 15 i) + (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact AspisV5FriExactLineDomains.X_zpow_add_halfTurn _

theorem storedLine17_slot3 (i : Fin 32768) :
    storedLine17X (childIndex i 3) =
      -storedLine17X (childIndex i 2) := by
  unfold storedLine17X storedLine17Point line17Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits17_child i 3, reverseBits17_child i 2]
  rw [reverseBits2_three, reverseBits2_two]
  push_cast
  rw [show (4096 : Int) + 16384 *
        (reverseBits 15 i + 98304) =
      (4096 + 16384 * (reverseBits 15 i + 32768)) +
        (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact AspisV5FriExactLineDomains.X_zpow_add_halfTurn _

theorem storedLine17_child_slot (i : Fin 32768) (slot : Fin 4) :
    storedLine17X (childIndex i slot) =
      radix4ChildPoint
        (storedLine17X (childIndex i 0))
        (storedLine17X (childIndex i 2)) slot := by
  fin_cases slot <;>
    simp [radix4ChildPoint, storedLine17_slot1, storedLine17_slot3]

/-! ## Exact squaring relations between adjacent stored domains -/

theorem storedLine17_sq_slot0 (i : Fin 32768) :
    storedLine17Point (childIndex i 0) ^ 2 =
      storedLine16Point (binaryChildIndex i) := by
  unfold storedLine17Point storedLine16Point line17Point line16Point
  rw [← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  unfold Int.ModEq reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [reverseBits17_child i 0, reverseBits16_binary i]
  rw [reverseBits2_zero]
  norm_num
  ring

theorem storedLine16_sq (i : Fin 32768) :
    storedLine16Point (binaryChildIndex i) ^ 2 = storedLine15Point i := by
  unfold storedLine16Point storedLine15Point line16Point line15Point
  rw [← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  unfold Int.ModEq reverseFin binaryChildIndex
  rw [reverseBits16_binary_int i]
  norm_num
  ring

theorem storedLine15_sq_slot0 (i : Fin 8192) :
    storedLine15Point (childIndex i 0) ^ 2 =
      storedLine14Point (binaryChildIndex i) := by
  unfold storedLine15Point storedLine14Point line15Point line14Point
  rw [← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  unfold Int.ModEq reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [reverseBits15_child i 0, reverseBits14_binary i]
  rw [reverseBits2_zero]
  norm_num
  ring

theorem storedLine14_sq (i : Fin 8192) :
    storedLine14Point (binaryChildIndex i) ^ 2 = storedLine13Point i := by
  unfold storedLine14Point storedLine13Point line14Point line13Point
  rw [← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  unfold Int.ModEq reverseFin binaryChildIndex
  rw [reverseBits14_binary_int i]
  norm_num
  ring

theorem storedLine13_sq_slot0 (i : Fin 2048) :
    storedLine13Point (childIndex i 0) ^ 2 =
      storedLine12Point (binaryChildIndex i) := by
  unfold storedLine13Point storedLine12Point line13Point line12Point
  rw [← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  unfold Int.ModEq reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [reverseBits13_child i 0, reverseBits12_binary i]
  rw [reverseBits2_zero]
  norm_num
  ring

theorem storedLine12_sq (i : Fin 2048) :
    storedLine12Point (binaryChildIndex i) ^ 2 = storedLine11Point i := by
  unfold storedLine12Point storedLine11Point line12Point line11Point
  rw [← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  unfold Int.ModEq reverseFin binaryChildIndex
  rw [reverseBits12_binary_int i]
  norm_num
  ring

theorem storedLine15_slot1 (i : Fin 8192) :
    storedLine15X (childIndex i 1) =
      -storedLine15X (childIndex i 0) := by
  unfold storedLine15X storedLine15Point line15Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits15_child i 1, reverseBits15_child i 0]
  rw [reverseBits2_one, reverseBits2_zero]
  push_cast
  simp only [add_zero]
  rw [show (16384 : Int) + 65536 *
        (reverseBits 13 i + 16384) =
      (16384 + 65536 * reverseBits 13 i) + (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine15_slot3 (i : Fin 8192) :
    storedLine15X (childIndex i 3) =
      -storedLine15X (childIndex i 2) := by
  unfold storedLine15X storedLine15Point line15Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits15_child i 3, reverseBits15_child i 2]
  rw [reverseBits2_three, reverseBits2_two]
  push_cast
  rw [show (16384 : Int) + 65536 *
        (reverseBits 13 i + 24576) =
      (16384 + 65536 * (reverseBits 13 i + 8192)) +
        (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine15_child_slot (i : Fin 8192) (slot : Fin 4) :
    storedLine15X (childIndex i slot) =
      radix4ChildPoint
        (storedLine15X (childIndex i 0))
        (storedLine15X (childIndex i 2)) slot := by
  fin_cases slot <;>
    simp [radix4ChildPoint, storedLine15_slot1, storedLine15_slot3]

theorem storedLine13_slot1 (i : Fin 2048) :
    storedLine13X (childIndex i 1) =
      -storedLine13X (childIndex i 0) := by
  unfold storedLine13X storedLine13Point line13Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits13_child i 1, reverseBits13_child i 0]
  rw [reverseBits2_one, reverseBits2_zero]
  push_cast
  simp only [add_zero]
  rw [show (65536 : Int) + 262144 *
        (reverseBits 11 i + 4096) =
      (65536 + 262144 * reverseBits 11 i) + (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine13_slot3 (i : Fin 2048) :
    storedLine13X (childIndex i 3) =
      -storedLine13X (childIndex i 2) := by
  unfold storedLine13X storedLine13Point line13Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits13_child i 3, reverseBits13_child i 2]
  rw [reverseBits2_three, reverseBits2_two]
  push_cast
  rw [show (65536 : Int) + 262144 *
        (reverseBits 11 i + 6144) =
      (65536 + 262144 * (reverseBits 11 i + 2048)) +
        (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine13_child_slot (i : Fin 2048) (slot : Fin 4) :
    storedLine13X (childIndex i slot) =
      radix4ChildPoint
        (storedLine13X (childIndex i 0))
        (storedLine13X (childIndex i 2)) slot := by
  fin_cases slot <;>
    simp [radix4ChildPoint, storedLine13_slot1, storedLine13_slot3]

/-! ## Coordinate form of the squaring relations -/

theorem storedLine17_t2_slot0 (i : Fin 32768) :
    doubledFactor (storedLine17X (childIndex i 0)) 1 =
      storedLine16X (binaryChildIndex i) := by
  rw [show doubledFactor (storedLine17X (childIndex i 0)) 1 =
      X (storedLine17Point (childIndex i 0) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine17_sq_slot0]
  rfl

theorem storedLine17_t2_slot2 (i : Fin 32768) :
    doubledFactor (storedLine17X (childIndex i 2)) 1 =
      -storedLine16X (binaryChildIndex i) := by
  rw [show doubledFactor (storedLine17X (childIndex i 2)) 1 =
      X (storedLine17Point (childIndex i 2) ^ 2) by
    rw [X_sq]
    rfl]
  unfold storedLine17Point storedLine16X storedLine16Point
  unfold line17Point line16Point reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [← zpow_natCast, ← zpow_mul,
    reverseBits17_child i 2, reverseBits16_binary i]
  rw [reverseBits2_two]
  push_cast
  rw [show ((4096 : Int) + 16384 *
        (reverseBits 15 i + 32768)) * 2 =
      (8192 + 32768 * reverseBits 15 i) + (2 : Int) ^ 30 by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine16_t2 (i : Fin 32768) :
    doubledFactor (storedLine16X (binaryChildIndex i)) 1 =
      storedLine15X i := by
  rw [show doubledFactor (storedLine16X (binaryChildIndex i)) 1 =
      X (storedLine16Point (binaryChildIndex i) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine16_sq]
  rfl

theorem storedLine15_t2_slot0 (i : Fin 8192) :
    doubledFactor (storedLine15X (childIndex i 0)) 1 =
      storedLine14X (binaryChildIndex i) := by
  rw [show doubledFactor (storedLine15X (childIndex i 0)) 1 =
      X (storedLine15Point (childIndex i 0) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine15_sq_slot0]
  rfl

theorem storedLine15_t2_slot2 (i : Fin 8192) :
    doubledFactor (storedLine15X (childIndex i 2)) 1 =
      -storedLine14X (binaryChildIndex i) := by
  rw [show doubledFactor (storedLine15X (childIndex i 2)) 1 =
      X (storedLine15Point (childIndex i 2) ^ 2) by
    rw [X_sq]
    rfl]
  unfold storedLine15Point storedLine14X storedLine14Point
  unfold line15Point line14Point reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [← zpow_natCast, ← zpow_mul,
    reverseBits15_child i 2, reverseBits14_binary i]
  rw [reverseBits2_two]
  push_cast
  rw [show ((16384 : Int) + 65536 *
        (reverseBits 13 i + 8192)) * 2 =
      (32768 + 131072 * reverseBits 13 i) + (2 : Int) ^ 30 by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine14_t2 (i : Fin 8192) :
    doubledFactor (storedLine14X (binaryChildIndex i)) 1 =
      storedLine13X i := by
  rw [show doubledFactor (storedLine14X (binaryChildIndex i)) 1 =
      X (storedLine14Point (binaryChildIndex i) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine14_sq]
  rfl

theorem storedLine13_t2_slot0 (i : Fin 2048) :
    doubledFactor (storedLine13X (childIndex i 0)) 1 =
      storedLine12X (binaryChildIndex i) := by
  rw [show doubledFactor (storedLine13X (childIndex i 0)) 1 =
      X (storedLine13Point (childIndex i 0) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine13_sq_slot0]
  rfl

theorem storedLine13_t2_slot2 (i : Fin 2048) :
    doubledFactor (storedLine13X (childIndex i 2)) 1 =
      -storedLine12X (binaryChildIndex i) := by
  rw [show doubledFactor (storedLine13X (childIndex i 2)) 1 =
      X (storedLine13Point (childIndex i 2) ^ 2) by
    rw [X_sq]
    rfl]
  unfold storedLine13Point storedLine12X storedLine12Point
  unfold line13Point line12Point reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [← zpow_natCast, ← zpow_mul,
    reverseBits13_child i 2, reverseBits12_binary i]
  rw [reverseBits2_two]
  push_cast
  rw [show ((65536 : Int) + 262144 *
        (reverseBits 11 i + 2048)) * 2 =
      (131072 + 524288 * reverseBits 11 i) + (2 : Int) ^ 30 by
    push_cast
    ring]
  exact X_zpow_add_halfTurn _

theorem storedLine12_t2 (i : Fin 2048) :
    doubledFactor (storedLine12X (binaryChildIndex i)) 1 =
      storedLine11X i := by
  rw [show doubledFactor (storedLine12X (binaryChildIndex i)) 1 =
      X (storedLine12Point (binaryChildIndex i) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine12_sq]
  rfl

def releasedLinePoints
    (circleX circleY : Fin 131072 -> ZMod P) : EvaluationPoints (ZMod P) where
  circleX := circleX
  circleY := circleY
  line1 := fun i slot => ![
    storedLine17X (childIndex i 0),
    storedLine17X (childIndex i 2),
    storedLine16X (binaryChildIndex i)] slot
  line2 := fun i slot => ![
    storedLine15X (childIndex i 0),
    storedLine15X (childIndex i 2),
    storedLine14X (binaryChildIndex i)] slot
  line3 := fun i slot => ![
    storedLine13X (childIndex i 0),
    storedLine13X (childIndex i 2),
    storedLine12X (binaryChildIndex i)] slot

/-! ## The complete released line tower -/

/-- Exact V5 evaluation points, including the slot-zero coordinates of the
initial stored circle fibres. -/
def releasedEvaluationPoints : EvaluationPoints (ZMod P) :=
  releasedLinePoints
    (fun i => X (storedInitialFibrePoint i))
    (fun i => (storedInitialFibrePoint i).1.2)

@[simp] private theorem releasedLine1_zero (i : Fin 32768) :
    releasedEvaluationPoints.line1 i 0 =
      storedLine17X (childIndex i 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine1_one (i : Fin 32768) :
    releasedEvaluationPoints.line1 i 1 =
      storedLine17X (childIndex i 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine1_two (i : Fin 32768) :
    releasedEvaluationPoints.line1 i 2 =
      storedLine16X (binaryChildIndex i) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine2_zero (i : Fin 8192) :
    releasedEvaluationPoints.line2 i 0 =
      storedLine15X (childIndex i 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine2_one (i : Fin 8192) :
    releasedEvaluationPoints.line2 i 1 =
      storedLine15X (childIndex i 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine2_two (i : Fin 8192) :
    releasedEvaluationPoints.line2 i 2 =
      storedLine14X (binaryChildIndex i) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine3_zero (i : Fin 2048) :
    releasedEvaluationPoints.line3 i 0 =
      storedLine13X (childIndex i 0) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine3_one (i : Fin 2048) :
    releasedEvaluationPoints.line3 i 1 =
      storedLine13X (childIndex i 2) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

@[simp] private theorem releasedLine3_two (i : Fin 2048) :
    releasedEvaluationPoints.line3 i 2 =
      storedLine12X (binaryChildIndex i) := by
  simp [releasedEvaluationPoints, releasedLinePoints]
  rfl

private theorem map_radix4ChildPoint {K : Type*} [Field K]
    [Algebra (ZMod P) K] (x0 x1 : ZMod P) (slot : Fin 4) :
    algebraMap (ZMod P) K (radix4ChildPoint x0 x1 slot) =
      radix4ChildPoint
        (algebraMap (ZMod P) K x0) (algebraMap (ZMod P) K x1) slot := by
  fin_cases slot <;> simp [radix4ChildPoint, map_neg]

private theorem map_doubledFactor {K : Type*} [Field K]
    [Algebra (ZMod P) K] (x y : ZMod P)
    (h : doubledFactor x 1 = y) :
    doubledFactor (algebraMap (ZMod P) K x) 1 =
      algebraMap (ZMod P) K y := by
  have hm := congrArg (algebraMap (ZMod P) K) h
  simpa [doubledFactor, map_sub, map_mul, map_pow, map_one, map_ofNat] using hm

/-- The only schedule field used by line-code evaluation is the final domain.
This predicate says that it is the exact released bit-reversed `2^11` domain. -/
def FinalXMatchesReleasedDomain {K : Type*} [Field K]
    (schedule : FixedSchedule (ZMod P) K) : Prop :=
  ∀ i, schedule.finalX i = storedLine11X i

/-- Exact line geometry of all three recursive layers.  Every child-slot and
doubling equation is proved above from the released generator and bit order. -/
noncomputable def releasedLineTowerGeometry
    {K : Type*} [Field K] [Algebra (ZMod P) K]
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    LineTowerGeometry schedule releasedEvaluationPoints where
  node1 := fun i => algebraMap (ZMod P) K (storedLine17X i)
  node2 := fun i => algebraMap (ZMod P) K (storedLine15X i)
  node3 := fun i => algebraMap (ZMod P) K (storedLine13X i)
  node4 := fun i => algebraMap (ZMod P) K (storedLine11X i)
  node1_injective := (FaithfulSMul.algebraMap_injective (ZMod P) K).comp
    storedLine17X_injective
  node2_injective := (FaithfulSMul.algebraMap_injective (ZMod P) K).comp
    storedLine15X_injective
  node3_injective := (FaithfulSMul.algebraMap_injective (ZMod P) K).comp
    storedLine13X_injective
  node4_injective := (FaithfulSMul.algebraMap_injective (ZMod P) K).comp
    storedLine11X_injective
  layer1 := {
    child_slot := by
      intro i slot
      have h := congrArg (algebraMap (ZMod P) K)
        (storedLine17_child_slot i slot)
      simpa only [releasedLine1_zero, releasedLine1_one,
        map_radix4ChildPoint] using h
    t2_x0 := by
      intro i
      simpa only [releasedLine1_zero, releasedLine1_two] using
        map_doubledFactor (K := K)
          (storedLine17X (childIndex i 0))
          (storedLine16X (binaryChildIndex i))
          (storedLine17_t2_slot0 i)
    t2_x1 := by
      intro i
      have h := map_doubledFactor (K := K)
        (storedLine17X (childIndex i 2))
        (-storedLine16X (binaryChildIndex i))
        (storedLine17_t2_slot2 i)
      simpa only [releasedLine1_one, releasedLine1_two, map_neg] using h
    t2_x2 := by
      intro i
      simpa only [releasedLine1_two] using
        map_doubledFactor (K := K)
          (storedLine16X (binaryChildIndex i)) (storedLine15X i)
          (storedLine16_t2 i) }
  layer2 := {
    child_slot := by
      intro i slot
      have h := congrArg (algebraMap (ZMod P) K)
        (storedLine15_child_slot i slot)
      simpa only [releasedLine2_zero, releasedLine2_one,
        map_radix4ChildPoint] using h
    t2_x0 := by
      intro i
      simpa only [releasedLine2_zero, releasedLine2_two] using
        map_doubledFactor (K := K)
          (storedLine15X (childIndex i 0))
          (storedLine14X (binaryChildIndex i))
          (storedLine15_t2_slot0 i)
    t2_x1 := by
      intro i
      have h := map_doubledFactor (K := K)
        (storedLine15X (childIndex i 2))
        (-storedLine14X (binaryChildIndex i))
        (storedLine15_t2_slot2 i)
      simpa only [releasedLine2_one, releasedLine2_two, map_neg] using h
    t2_x2 := by
      intro i
      simpa only [releasedLine2_two] using
        map_doubledFactor (K := K)
          (storedLine14X (binaryChildIndex i)) (storedLine13X i)
          (storedLine14_t2 i) }
  layer3 := {
    child_slot := by
      intro i slot
      have h := congrArg (algebraMap (ZMod P) K)
        (storedLine13_child_slot i slot)
      simpa only [releasedLine3_zero, releasedLine3_one,
        map_radix4ChildPoint] using h
    t2_x0 := by
      intro i
      simpa only [releasedLine3_zero, releasedLine3_two] using
        map_doubledFactor (K := K)
          (storedLine13X (childIndex i 0))
          (storedLine12X (binaryChildIndex i))
          (storedLine13_t2_slot0 i)
    t2_x1 := by
      intro i
      have h := map_doubledFactor (K := K)
        (storedLine13X (childIndex i 2))
        (-storedLine12X (binaryChildIndex i))
        (storedLine13_t2_slot2 i)
      simpa only [releasedLine3_one, releasedLine3_two, map_neg] using h
    t2_x2 := by
      intro i
      simpa only [releasedLine3_two] using
        map_doubledFactor (K := K)
          (storedLine12X (binaryChildIndex i)) (storedLine11X i)
          (storedLine12_t2 i) }
  final_point := by
    intro i
    rw [hfinal i]

/-- Exact natural-polynomial identities for all three committed line
encoders. -/
noncomputable def releasedLineEvaluationIdentities
    {K : Type*} [Field K] [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    ConcreteLineEvaluationIdentities schedule releasedEvaluationPoints :=
  concreteLineEvaluationIdentities_of_geometry schedule
    releasedEvaluationPoints (releasedLineTowerGeometry schedule hfinal)

@[simp] private theorem releasedLineEvaluationIdentities_layer1_points
    {K : Type*} [Field K] [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule) (i : Fin 131072) :
    (releasedLineEvaluationIdentities schedule hfinal).layer1.points i =
      algebraMap (ZMod P) K (storedLine17X i) := by
  rfl

/-- The schedule's final domain is pairwise distinct because it is exactly the
released half-odd domain. -/
theorem releasedFinalDomainDistinct
    {K : Type*} [Field K]
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    FinalDomainDistinct schedule := by
  intro i j hij
  apply storedLine11X_injective
  rw [← hfinal i, ← hfinal j]
  exact hij

/-- Exact initial circle-code distance with no initial evaluation premise.
All polynomial and point-order facts are derived; only the schedule's final
public x-table must be identified with its released domain. -/
theorem releasedInitialEncoderDistance
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    InitialEncoderDistance
      (concreteCodeEncoders schedule releasedEvaluationPoints) := by
  let identities := releasedLineEvaluationIdentities schedule hfinal
  apply initialEncoderDistance_of_exact_line_identity schedule
    releasedEvaluationPoints
  · intro i
    rfl
  · intro i
    rfl
  · intro message i
    have h := identities.layer1.encoder_eq_eval message i
    rw [show identities.layer1.points i =
        algebraMap (ZMod P) K (storedLine17X i) by
      simpa only [identities,
        releasedLineEvaluationIdentities_layer1_points]] at h
    simpa only [storedFirstLineX, storedLine17X, storedLine17Point,
      line17X] using h

/-- All four committed-word distance bounds used by the V5 list-size proof. -/
theorem releasedCommittedEncoderDistances
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (hfinal : FinalXMatchesReleasedDomain schedule) :
    InitialEncoderDistance
        (concreteCodeEncoders schedule releasedEvaluationPoints) ∧
      Layer1EncoderDistance
        (concreteCodeEncoders schedule releasedEvaluationPoints) ∧
      Layer2EncoderDistance
        (concreteCodeEncoders schedule releasedEvaluationPoints) ∧
      Layer3EncoderDistance
        (concreteCodeEncoders schedule releasedEvaluationPoints) := by
  refine ⟨releasedInitialEncoderDistance schedule hfinal, ?_⟩
  exact concrete_line_encoder_distances schedule releasedEvaluationPoints
    (releasedLineEvaluationIdentities schedule hfinal)

/-! ## Audit -/

#print axioms releasedLineTowerGeometry
#print axioms releasedLineEvaluationIdentities
#print axioms releasedInitialEncoderDistance
#print axioms releasedCommittedEncoderDistances

end AspisV5FriReleasedLineGeometry
