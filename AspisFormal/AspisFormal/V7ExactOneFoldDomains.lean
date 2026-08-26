import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V6EncoderDistance

/-!
# Exact bit-reversed log-20/log-18 domains for the V7 one-fold PCS

The production circle encoder stores its `2^20` symbols in bit-reversed,
four-symbol-fibre order.  The old `V6EncoderDistance.initialCirclePoint`
enumerates the same half-odd coset in natural order, so using that function
directly at a stored word index is not the deployed encoder.

This module gives the exact permutation and proves the four consecutive stored
symbols are `(x,y)`, `(x,-y)`, `(-x,-y)`, and `(-x,y)`.  Squaring the slot-zero
point gives the exact bit-reversed log-18 line point consumed after the sole
circle fold.  All statements are structural group/field arithmetic; there is
no decoding or soundness assumption here.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace AspisV7ExactOneFoldDomains

open AspisCircleGroupOrder
open AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriBitReverse
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriExactLineDomains
open AspisV5FriInitialCircleEncoderIdentity

/-! ## Exact stored log-20 circle order -/

/-- Natural half-odd-domain index represented by one stored log-20 position.
If `r` is the 18-bit reversal of the fibre index, the four stored slots are

`2r`, `2^20-1-2r`, `2^19+2r`, `2^19-1-2r`.
-/
def storedInitialNaturalIndex20 (index : Fin (2 ^ 20)) : Fin (2 ^ 20) :=
  let reversed := (reverseFin 18 (parentIndex (n := 262144) index)).val
  match (slotIndex (n := 262144) index).val with
  | 0 => ⟨2 * reversed, by
      have bound := (reverseFin 18 (parentIndex (n := 262144) index)).isLt
      norm_num at bound ⊢
      omega⟩
  | 1 => ⟨2 ^ 20 - 1 - 2 * reversed, by
      have bound := (reverseFin 18 (parentIndex (n := 262144) index)).isLt
      norm_num at bound ⊢
      omega⟩
  | 2 => ⟨2 ^ 19 + 2 * reversed, by
      have bound := (reverseFin 18 (parentIndex (n := 262144) index)).isLt
      norm_num at bound ⊢
      omega⟩
  | _ => ⟨2 ^ 19 - 1 - 2 * reversed, by
      have bound := (reverseFin 18 (parentIndex (n := 262144) index)).isLt
      norm_num at bound ⊢
      omega⟩

@[simp] theorem storedInitialNaturalIndex20_child_zero (index : Fin 262144) :
    (storedInitialNaturalIndex20 (childIndex index 0)).val =
      2 * (reverseFin 18 index).val := by
  simp [storedInitialNaturalIndex20]

@[simp] theorem storedInitialNaturalIndex20_child_one (index : Fin 262144) :
    (storedInitialNaturalIndex20 (childIndex index 1)).val =
      2 ^ 20 - 1 - 2 * (reverseFin 18 index).val := by
  simp [storedInitialNaturalIndex20]

@[simp] theorem storedInitialNaturalIndex20_child_two (index : Fin 262144) :
    (storedInitialNaturalIndex20 (childIndex index 2)).val =
      2 ^ 19 + 2 * (reverseFin 18 index).val := by
  simp [storedInitialNaturalIndex20]

@[simp] theorem storedInitialNaturalIndex20_child_three (index : Fin 262144) :
    (storedInitialNaturalIndex20 (childIndex index 3)).val =
      2 ^ 19 - 1 - 2 * (reverseFin 18 index).val := by
  simp [storedInitialNaturalIndex20]

theorem storedInitialNaturalIndex20_injective :
    Function.Injective storedInitialNaturalIndex20 := by
  intro left right equal
  rw [← childIndex_parentIndex_slotIndex (n := 262144) left,
    ← childIndex_parentIndex_slotIndex (n := 262144) right] at equal ⊢
  let leftParent := parentIndex (n := 262144) left
  let rightParent := parentIndex (n := 262144) right
  let leftSlot := slotIndex (n := 262144) left
  let rightSlot := slotIndex (n := 262144) right
  change childIndex leftParent leftSlot = childIndex rightParent rightSlot
  change storedInitialNaturalIndex20 (childIndex leftParent leftSlot) =
    storedInitialNaturalIndex20 (childIndex rightParent rightSlot) at equal
  have valuesEqual := congrArg Fin.val equal
  have leftBound := (reverseFin 18 leftParent).isLt
  have rightBound := (reverseFin 18 rightParent).isLt
  have parentsEqual
      (reversedEqual : (reverseFin 18 leftParent).val =
        (reverseFin 18 rightParent).val) : leftParent = rightParent := by
    apply reverseFin_injective 18
    apply Fin.ext
    exact reversedEqual
  have fourCases (slot : Fin 4) :
      slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
    fin_cases slot <;> simp
  rcases fourCases leftSlot with hs | hs | hs | hs <;>
    rcases fourCases rightSlot with ht | ht | ht | ht <;>
    rw [hs, ht] at valuesEqual ⊢ <;>
    simp only [storedInitialNaturalIndex20_child_zero,
      storedInitialNaturalIndex20_child_one,
      storedInitialNaturalIndex20_child_two,
      storedInitialNaturalIndex20_child_three] at valuesEqual
  all_goals norm_num at leftBound rightBound valuesEqual ⊢
  all_goals try omega
  all_goals
    have parentEqual : leftParent = rightParent := parentsEqual (by omega)
    simpa only using congrArg (fun parent => childIndex parent _) parentEqual

/-- Exact stored, fibre-major circle point. -/
def storedInitialCirclePoint20 (index : Fin (2 ^ 20)) : C :=
  AspisV6EncoderDistance.initialCirclePoint (storedInitialNaturalIndex20 index)

@[simp] theorem storedInitialCirclePoint20_eq_zpow (index : Fin (2 ^ 20)) :
    storedInitialCirclePoint20 index =
      g ^ AspisV6EncoderDistance.initialCircleExponent
        (storedInitialNaturalIndex20 index) := rfl

theorem storedInitialCirclePoint20_injective :
    Function.Injective storedInitialCirclePoint20 :=
  AspisV6EncoderDistance.initialCirclePoint_injective.comp
    storedInitialNaturalIndex20_injective

theorem storedInitialCirclePoint20_x_ne_neg_one (index : Fin (2 ^ 20)) :
    X (storedInitialCirclePoint20 index) ≠ -1 :=
  AspisV6EncoderDistance.initialCirclePoint_x_ne_neg_one
    (storedInitialNaturalIndex20 index)

/-- Slot-zero point for one of the `2^18` stored circle fibres. -/
def storedInitialFibrePoint20 (index : Fin 262144) : C :=
  storedInitialCirclePoint20 (childIndex index 0)

@[simp] theorem storedInitialFibrePoint20_eq_zpow (index : Fin 262144) :
    storedInitialFibrePoint20 index =
      g ^ AspisV6EncoderDistance.initialCircleExponent
        (storedInitialNaturalIndex20 (childIndex index 0)) := rfl

private theorem slotOneModEq20 (reversed : Nat) (bound : reversed < 2 ^ 18) :
    (2 : Int) ^ 10 *
        (2 * ((2 ^ 20 - 1 - 2 * reversed : Nat) : Int) + 1) ≡
      -((2 : Int) ^ 10 * (2 * ((2 * reversed : Nat) : Int) + 1))
        [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  have subtractable : 2 * reversed ≤ 2 ^ 20 - 1 := by
    norm_num at bound ⊢
    omega
  rw [Nat.cast_sub subtractable]
  push_cast
  norm_num at bound ⊢
  omega

private theorem slotTwoModEq20 (reversed : Nat) :
    (2 : Int) ^ 10 *
        (2 * ((2 ^ 19 + 2 * reversed : Nat) : Int) + 1) ≡
      (2 : Int) ^ 30 +
        (2 : Int) ^ 10 * (2 * ((2 * reversed : Nat) : Int) + 1)
        [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨0, ?_⟩
  push_cast
  ring

private theorem slotThreeModEq20
    (reversed : Nat) (bound : reversed < 2 ^ 18) :
    (2 : Int) ^ 10 *
        (2 * ((2 ^ 19 - 1 - 2 * reversed : Nat) : Int) + 1) ≡
      -(2 : Int) ^ 30 +
        -((2 : Int) ^ 10 * (2 * ((2 * reversed : Nat) : Int) + 1))
        [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  have subtractable : 2 * reversed ≤ 2 ^ 19 - 1 := by
    norm_num at bound ⊢
    omega
  rw [Nat.cast_sub subtractable]
  push_cast
  norm_num at bound ⊢
  omega

private theorem slotZeroSquareModEq20 (reversed : Nat) :
    (2 : Int) ^ 10 * (2 * ((2 * reversed : Nat) : Int) + 1) * 2 ≡
      2048 + 8192 * (reversed : Int) [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨0, ?_⟩
  push_cast
  ring

theorem storedInitialCirclePoint20_child_zero (index : Fin 262144) :
    storedInitialCirclePoint20 (childIndex index 0) =
      storedInitialFibrePoint20 index := rfl

/-- Slot one is the conjugate/inverse of slot zero. -/
theorem storedInitialCirclePoint20_child_one (index : Fin 262144) :
    storedInitialCirclePoint20 (childIndex index 1) =
      (storedInitialFibrePoint20 index)⁻¹ := by
  have groupEqual :
      g ^ AspisV6EncoderDistance.initialCircleExponent
          (storedInitialNaturalIndex20 (childIndex index 1)) =
        (g ^ AspisV6EncoderDistance.initialCircleExponent
          (storedInitialNaturalIndex20 (childIndex index 0)))⁻¹ := by
    rw [← zpow_neg]
    apply (g_zpow_eq_iff _ _).2
    have bound := (reverseFin 18 index).isLt
    simp only [storedInitialNaturalIndex20_child_one,
      storedInitialNaturalIndex20_child_zero]
    unfold AspisV6EncoderDistance.initialCircleExponent
    exact slotOneModEq20 (reverseFin 18 index).val bound
  rw [storedInitialCirclePoint20_eq_zpow,
    storedInitialFibrePoint20_eq_zpow]
  exact groupEqual

/-- Slot two is the half-turn rotation of slot zero. -/
theorem storedInitialCirclePoint20_child_two (index : Fin 262144) :
    storedInitialCirclePoint20 (childIndex index 2) =
      g ^ ((2 : Int) ^ 30) * storedInitialFibrePoint20 index := by
  have groupEqual :
      g ^ AspisV6EncoderDistance.initialCircleExponent
          (storedInitialNaturalIndex20 (childIndex index 2)) =
        g ^ ((2 : Int) ^ 30) *
          g ^ AspisV6EncoderDistance.initialCircleExponent
            (storedInitialNaturalIndex20 (childIndex index 0)) := by
    rw [← zpow_add]
    apply (g_zpow_eq_iff _ _).2
    simp only [storedInitialNaturalIndex20_child_two,
      storedInitialNaturalIndex20_child_zero]
    unfold AspisV6EncoderDistance.initialCircleExponent
    exact slotTwoModEq20 (reverseFin 18 index).val
  rw [storedInitialCirclePoint20_eq_zpow,
    storedInitialFibrePoint20_eq_zpow]
  exact groupEqual

/-- Slot three is the inverse of the half-turn slot. -/
theorem storedInitialCirclePoint20_child_three (index : Fin 262144) :
    storedInitialCirclePoint20 (childIndex index 3) =
      (g ^ ((2 : Int) ^ 30) * storedInitialFibrePoint20 index)⁻¹ := by
  have groupEqual :
      g ^ AspisV6EncoderDistance.initialCircleExponent
          (storedInitialNaturalIndex20 (childIndex index 3)) =
        (g ^ ((2 : Int) ^ 30) *
          g ^ AspisV6EncoderDistance.initialCircleExponent
            (storedInitialNaturalIndex20 (childIndex index 0)))⁻¹ := by
    rw [mul_inv, ← zpow_neg, ← zpow_neg, ← zpow_add]
    apply (g_zpow_eq_iff _ _).2
    have bound := (reverseFin 18 index).isLt
    simp only [storedInitialNaturalIndex20_child_three,
      storedInitialNaturalIndex20_child_zero]
    unfold AspisV6EncoderDistance.initialCircleExponent
    exact slotThreeModEq20 (reverseFin 18 index).val bound
  rw [storedInitialCirclePoint20_eq_zpow,
    storedInitialFibrePoint20_eq_zpow]
  exact groupEqual

private theorem fourCases (slot : Fin 4) :
    slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
  fin_cases slot <;> simp

def storedCircleSlotX20 (point : C) (slot : Fin 4) : ZMod P :=
  match slot.val with
  | 0 => X point
  | 1 => X point
  | 2 => -(X point)
  | _ => -(X point)

def storedCircleSlotY20 (point : C) (slot : Fin 4) : ZMod P :=
  match slot.val with
  | 0 => point.1.2
  | 1 => -point.1.2
  | 2 => -point.1.2
  | _ => point.1.2

theorem storedInitialCirclePoint20_x_slots
    (index : Fin 262144) (slot : Fin 4) :
    X (storedInitialCirclePoint20 (childIndex index slot)) =
      storedCircleSlotX20 (storedInitialFibrePoint20 index) slot := by
  rcases fourCases slot with hs | hs | hs | hs
  · rw [hs, storedInitialCirclePoint20_child_zero]
    rfl
  · rw [hs, storedInitialCirclePoint20_child_one]
    change (storedInitialFibrePoint20 index).1.1 =
      (storedInitialFibrePoint20 index).1.1
    rfl
  · rw [hs, storedInitialCirclePoint20_child_two,
      AspisV5FriInitialCircleEncoderIdentity.halfTurn_point]
    change (-1 : ZMod P) * (storedInitialFibrePoint20 index).1.1 -
        0 * (storedInitialFibrePoint20 index).1.2 =
      -(storedInitialFibrePoint20 index).1.1
    ring
  · rw [hs, storedInitialCirclePoint20_child_three,
      AspisV5FriInitialCircleEncoderIdentity.halfTurn_point]
    change (-1 : ZMod P) * (storedInitialFibrePoint20 index).1.1 -
        0 * (storedInitialFibrePoint20 index).1.2 =
      -(storedInitialFibrePoint20 index).1.1
    ring

theorem storedInitialCirclePoint20_y_slots
    (index : Fin 262144) (slot : Fin 4) :
    (storedInitialCirclePoint20 (childIndex index slot)).1.2 =
      storedCircleSlotY20 (storedInitialFibrePoint20 index) slot := by
  rcases fourCases slot with hs | hs | hs | hs
  · rw [hs, storedInitialCirclePoint20_child_zero]
    rfl
  · rw [hs, storedInitialCirclePoint20_child_one]
    change -(storedInitialFibrePoint20 index).1.2 =
      -(storedInitialFibrePoint20 index).1.2
    rfl
  · rw [hs, storedInitialCirclePoint20_child_two,
      AspisV5FriInitialCircleEncoderIdentity.halfTurn_point]
    change (-1 : ZMod P) * (storedInitialFibrePoint20 index).1.2 +
        0 * (storedInitialFibrePoint20 index).1.1 =
      -(storedInitialFibrePoint20 index).1.2
    ring
  · rw [hs, storedInitialCirclePoint20_child_three,
      AspisV5FriInitialCircleEncoderIdentity.halfTurn_point]
    change -((-1 : ZMod P) * (storedInitialFibrePoint20 index).1.2 +
        0 * (storedInitialFibrePoint20 index).1.1) =
      (storedInitialFibrePoint20 index).1.2
    ring

/-! ## Exact stored log-18 line order -/

def line18Point (index : Fin 262144) : C :=
  g ^ (2048 + 8192 * (index : Int))

def line18X (index : Fin 262144) : ZMod P := X (line18Point index)

theorem line18X_injective : Function.Injective line18X := by
  intro left right equal
  have modular := (sameXCoord_exp
    (2048 + 8192 * (left : Int))
    (2048 + 8192 * (right : Int))).mp equal
  apply Fin.ext
  unfold Int.ModEq at modular
  have leftBound := left.isLt
  have rightBound := right.isLt
  norm_num at leftBound rightBound modular ⊢
  rcases modular with modular | modular <;> omega

/-- First line coordinate in the same stored order as the output codeword. -/
def storedFirstLineX18 (index : Fin 262144) : ZMod P :=
  line18X (reverseFin 18 index)

theorem storedFirstLineX18_injective : Function.Injective storedFirstLineX18 :=
  line18X_injective.comp (reverseFin_injective 18)

theorem storedInitialFibrePoint20_sq (index : Fin 262144) :
    storedInitialFibrePoint20 index ^ 2 =
      line18Point (reverseFin 18 index) := by
  have groupEqual :
      (g ^ AspisV6EncoderDistance.initialCircleExponent
        (storedInitialNaturalIndex20 (childIndex index 0))) ^ 2 =
        line18Point (reverseFin 18 index) := by
    rw [line18Point, ← zpow_natCast, ← zpow_mul]
    apply (g_zpow_eq_iff _ _).2
    simp only [storedInitialNaturalIndex20_child_zero]
    unfold AspisV6EncoderDistance.initialCircleExponent
    exact slotZeroSquareModEq20 (reverseFin 18 index).val
  rw [storedInitialFibrePoint20_eq_zpow]
  exact groupEqual

theorem storedFirstLineX18_eq_doubled (index : Fin 262144) :
    storedFirstLineX18 index =
      doubledFactor (X (storedInitialFibrePoint20 index)) 1 := by
  rw [storedFirstLineX18, line18X, ← storedInitialFibrePoint20_sq,
    AspisV5FriExactLineDomains.X_sq]
  rfl

theorem storedFirstLineX18_eq_doubled_algebraMap
    {K : Type*} [Field K] [Algebra (ZMod P) K] (index : Fin 262144) :
    algebraMap (ZMod P) K (storedFirstLineX18 index) =
      doubledFactor
        (algebraMap (ZMod P) K (X (storedInitialFibrePoint20 index))) 1 := by
  have mapped := congrArg (algebraMap (ZMod P) K)
    (storedFirstLineX18_eq_doubled index)
  simpa [doubledFactor, map_sub, map_mul, map_pow, map_one, map_ofNat] using
    mapped

#print axioms storedInitialNaturalIndex20_injective
#print axioms storedInitialCirclePoint20_injective
#print axioms storedInitialCirclePoint20_child_one
#print axioms storedInitialCirclePoint20_child_two
#print axioms storedInitialCirclePoint20_child_three
#print axioms storedInitialCirclePoint20_x_slots
#print axioms storedInitialCirclePoint20_y_slots
#print axioms line18X_injective
#print axioms storedInitialFibrePoint20_sq
#print axioms storedFirstLineX18_eq_doubled

end AspisV7ExactOneFoldDomains
