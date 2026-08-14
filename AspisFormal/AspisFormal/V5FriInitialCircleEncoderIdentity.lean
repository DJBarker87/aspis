import AspisFormal.V5FriCircleEncoderDistance
import AspisFormal.V5FriBitReverse
import AspisFormal.V5FriExactLineDomains
import AspisFormal.V5FriConcreteEncoderApplicability

set_option maxRecDepth 20000
set_option maxHeartbeats 100000

/-!
# Exact polynomial identity for the initial V5 circle encoder

This file connects the maintained recursive `encoder0` definition to an
ordinary circle polynomial.  The connection is derived from the already
proved natural-basis identity for `encoder1`; no initial-encoder evaluation or
distance statement is assumed.

The two circle polynomials are obtained by splitting the 1024 coefficients
into their even and odd positions.  Their natural-basis evaluations split
again into the four lanes consumed by `circleLiftEncoder`:

* `p0(x) = A0(T2(x)) + x * A2(T2(x))`;
* `p1(x) = A1(T2(x)) + x * A3(T2(x))`.

The exact bit-reversed circle domain is then related to the exact released
line domain by squaring each slot-zero circle point.
-/

namespace AspisV5FriInitialCircleEncoderIdentity

open Polynomial
open AspisCircleGroupOrder
open AspisV5FriBitReverse
open AspisV5FriExactLineDomains
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriCircleEncoderDistance
open AspisV5FriNaturalBasisRadix4
open AspisV5ComponentCConcreteFoldLinearity
open AspisCircleTensorBinding
open AspisV5FriInitialListBound

variable {K : Type*} [Field K]

/-! ## Even/odd coefficient splitting -/

/-- The even positions of a width-`2n` vector. -/
def evenCoefficients {n : Nat} (c : Fin (2 * n) -> K) : Fin n -> K :=
  fun i => c ⟨2 * i, by omega⟩

/-- The odd positions of a width-`2n` vector. -/
def oddCoefficients {n : Nat} (c : Fin (2 * n) -> K) : Fin n -> K :=
  fun i => c ⟨2 * i + 1, by omega⟩

/-- A binary fibre-major index. -/
def binaryChildIndex {n : Nat} (i : Fin n) (slot : Fin 2) : Fin (2 * n) :=
  ⟨2 * i + slot, by omega⟩

/-- Parent of a binary fibre-major index. -/
def binaryParentIndex {n : Nat} (k : Fin (2 * n)) : Fin n :=
  ⟨k / 2, by omega⟩

/-- Slot of a binary fibre-major index. -/
def binarySlotIndex {n : Nat} (k : Fin (2 * n)) : Fin 2 :=
  ⟨k % 2, Nat.mod_lt _ (by decide)⟩

@[simp] theorem binaryParentIndex_childIndex {n : Nat}
    (i : Fin n) (slot : Fin 2) :
    binaryParentIndex (binaryChildIndex i slot) = i := by
  apply Fin.ext
  simp only [binaryParentIndex, binaryChildIndex]
  omega

@[simp] theorem binarySlotIndex_childIndex {n : Nat}
    (i : Fin n) (slot : Fin 2) :
    binarySlotIndex (binaryChildIndex i slot) = slot := by
  apply Fin.ext
  simp only [binarySlotIndex, binaryChildIndex]
  omega

@[simp] theorem binaryChildIndex_parent_slot {n : Nat}
    (k : Fin (2 * n)) :
    binaryChildIndex (binaryParentIndex k) (binarySlotIndex k) = k := by
  apply Fin.ext
  simp only [binaryChildIndex, binaryParentIndex, binarySlotIndex]
  omega

/-- Binary fibre indices are equivalent to a parent and one low bit. -/
def binaryIndexEquiv (n : Nat) : Fin n × Fin 2 ≃ Fin (2 * n) where
  toFun pair := binaryChildIndex pair.1 pair.2
  invFun k := (binaryParentIndex k, binarySlotIndex k)
  left_inv pair := by rcases pair with ⟨i, slot⟩; simp
  right_inv := binaryChildIndex_parent_slot

@[simp] theorem binaryIndexEquiv_apply {n : Nat} (pair : Fin n × Fin 2) :
    binaryIndexEquiv n pair = binaryChildIndex pair.1 pair.2 := rfl

/-- The natural polynomial of a width-`2n` vector is the even-lane
polynomial at `T2(x)` plus `x` times the odd-lane polynomial there. -/
theorem naturalCoefficientPolynomial_eval_binary {n : Nat} [NeZero (2 : K)]
    (hn : 0 < n) (c : Fin (2 * n) -> K) (x : K) :
    (naturalCoefficientPolynomial c).eval x =
      (naturalCoefficientPolynomial (evenCoefficients c)).eval
          (doubledFactor x 1) +
        x * (naturalCoefficientPolynomial (oddCoefficients c)).eval
          (doubledFactor x 1) := by
  rw [naturalCoefficientPolynomial_eval_eq_sum (by omega)]
  rw [← (binaryIndexEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  rw [naturalCoefficientPolynomial_eval_eq_sum hn,
    naturalCoefficientPolynomial_eval_eq_sum hn]
  simp only [Fin.sum_univ_two, binaryIndexEquiv_apply, binaryChildIndex,
    evenCoefficients, oddCoefficients, Fin.val_zero, Fin.val_one, add_zero]
  simp_rw [naturalLineValue_two_mul, naturalLineValue_two_mul_add_one]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ## The two degree-511 circle polynomials -/

/-- The `y`-free half of the initial circle polynomial. -/
noncomputable def initialP0 (c : Coeff0 K) : K[X] :=
  naturalCoefficientPolynomial (evenCoefficients (n := 512) c)

/-- The coefficient of `y` in the initial circle polynomial. -/
noncomputable def initialP1 (c : Coeff0 K) : K[X] :=
  naturalCoefficientPolynomial (oddCoefficients (n := 512) c)

theorem initialP0_degree_lt [NeZero (2 : K)] (c : Coeff0 K) :
    (initialP0 c).natDegree < 512 := by
  exact lt_of_le_of_lt (naturalCoefficientPolynomial_natDegree_le
    (K := K) (n := 512) (by norm_num) _) (by norm_num)

theorem initialP1_degree_lt [NeZero (2 : K)] (c : Coeff0 K) :
    (initialP1 c).natDegree < 512 := by
  exact lt_of_le_of_lt (naturalCoefficientPolynomial_natDegree_le
    (K := K) (n := 512) (by norm_num) _) (by norm_num)

/-- Evaluation of `p0` in the two even radix-four lanes. -/
theorem initialP0_eval_lanes [NeZero (2 : K)] (c : Coeff0 K) (x : K) :
    (initialP0 c).eval x =
      (naturalCoefficientPolynomial (coefficientLane 256 0 c)).eval
          (doubledFactor x 1) +
        x *
          (naturalCoefficientPolynomial (coefficientLane 256 2 c)).eval
            (doubledFactor x 1) := by
  rw [initialP0, naturalCoefficientPolynomial_eval_binary
    (K := K) (n := 256) (by norm_num)]
  congr 2

/-- Evaluation of `p1` in the two odd radix-four lanes. -/
theorem initialP1_eval_lanes [NeZero (2 : K)] (c : Coeff0 K) (x : K) :
    (initialP1 c).eval x =
      (naturalCoefficientPolynomial (coefficientLane 256 1 c)).eval
          (doubledFactor x 1) +
        x *
          (naturalCoefficientPolynomial (coefficientLane 256 3 c)).eval
            (doubledFactor x 1) := by
  rw [initialP1, naturalCoefficientPolynomial_eval_binary
    (K := K) (n := 256) (by norm_num)]
  congr 2

/-- Splitting a vector into even and odd entries loses no information. -/
theorem evenOddCoefficients_injective :
    Function.Injective (fun c : Coeff0 K =>
      (evenCoefficients (n := 512) c, oddCoefficients (n := 512) c)) := by
  intro left right h
  have heven := congrArg Prod.fst h
  have hodd := congrArg Prod.snd h
  funext k
  by_cases hk : k.val % 2 = 0
  · let i : Fin 512 := ⟨k.val / 2, by omega⟩
    have hi := congrFun heven i
    change left ⟨2 * i, by omega⟩ = right ⟨2 * i, by omega⟩ at hi
    have hindex : k = ⟨2 * i, by omega⟩ := by
      apply Fin.ext
      simp only [i]
      omega
    rw [hindex]
    exact hi
  · let i : Fin 512 := ⟨k.val / 2, by omega⟩
    have hi := congrFun hodd i
    change left ⟨2 * i + 1, by omega⟩ = right ⟨2 * i + 1, by omega⟩ at hi
    have hindex : k = ⟨2 * i + 1, by omega⟩ := by
      apply Fin.ext
      simp only [i]
      have hkmod : k.val % 2 = 1 := by omega
      omega
    rw [hindex]
    exact hi

/-- The conversion from the 1024 maintained coefficients to `(p0,p1)` is
injective. -/
theorem initialPolynomialPair_injective [NeZero (2 : K)] :
    Function.Injective (fun c : Coeff0 K => (initialP0 c, initialP1 c)) := by
  intro left right h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  apply evenOddCoefficients_injective
  apply Prod.ext
  · exact naturalCoefficientPolynomial_injective (K := K) (n := 512)
      (by simpa only [initialP0] using h0)
  · exact naturalCoefficientPolynomial_injective (K := K) (n := 512)
      (by simpa only [initialP1] using h1)

/-! ## Exact stored circle order -/

/-- Natural half-odd-domain index represented by one stored initial-codeword
position.  If `r` is the 17-bit reversal of the fibre index, the four stored
slots are the points numbered

`2r`, `2^19-1-2r`, `2^18+2r`, `2^18-1-2r`.

These are respectively `(x,y)`, `(x,-y)`, `(-x,-y)`, and `(-x,y)`. -/
def storedInitialNaturalIndex (k : Fin (2 ^ 19)) : Fin (2 ^ 19) :=
  let r := (reverseFin 17 (parentIndex (n := 131072) k)).val
  match (slotIndex (n := 131072) k).val with
  | 0 => ⟨2 * r, by have := (reverseFin 17 (parentIndex (n := 131072) k)).isLt; norm_num at this ⊢; omega⟩
  | 1 => ⟨2 ^ 19 - 1 - 2 * r, by
      have := (reverseFin 17 (parentIndex (n := 131072) k)).isLt
      norm_num at this ⊢
      omega⟩
  | 2 => ⟨2 ^ 18 + 2 * r, by
      have := (reverseFin 17 (parentIndex (n := 131072) k)).isLt
      norm_num at this ⊢
      omega⟩
  | _ => ⟨2 ^ 18 - 1 - 2 * r, by
      have := (reverseFin 17 (parentIndex (n := 131072) k)).isLt
      norm_num at this ⊢
      omega⟩

@[simp] theorem storedInitialNaturalIndex_child_zero (i : Fin 131072) :
    (storedInitialNaturalIndex (childIndex i 0)).val =
      2 * (reverseFin 17 i).val := by
  simp [storedInitialNaturalIndex]

@[simp] theorem storedInitialNaturalIndex_child_one (i : Fin 131072) :
    (storedInitialNaturalIndex (childIndex i 1)).val =
      2 ^ 19 - 1 - 2 * (reverseFin 17 i).val := by
  simp [storedInitialNaturalIndex]

@[simp] theorem storedInitialNaturalIndex_child_two (i : Fin 131072) :
    (storedInitialNaturalIndex (childIndex i 2)).val =
      2 ^ 18 + 2 * (reverseFin 17 i).val := by
  simp [storedInitialNaturalIndex]

@[simp] theorem storedInitialNaturalIndex_child_three (i : Fin 131072) :
    (storedInitialNaturalIndex (childIndex i 3)).val =
      2 ^ 18 - 1 - 2 * (reverseFin 17 i).val := by
  simp [storedInitialNaturalIndex]

theorem storedInitialNaturalIndex_injective :
    Function.Injective storedInitialNaturalIndex := by
  intro k l h
  rw [← childIndex_parentIndex_slotIndex (n := 131072) k,
    ← childIndex_parentIndex_slotIndex (n := 131072) l] at h ⊢
  let i := parentIndex (n := 131072) k
  let j := parentIndex (n := 131072) l
  let s := slotIndex (n := 131072) k
  let t := slotIndex (n := 131072) l
  change childIndex i s = childIndex j t
  change storedInitialNaturalIndex (childIndex i s) =
    storedInitialNaturalIndex (childIndex j t) at h
  have hv := congrArg Fin.val h
  have hi := (reverseFin 17 i).isLt
  have hj := (reverseFin 17 j).isLt
  have sameParent (hr : (reverseFin 17 i).val = (reverseFin 17 j).val) :
      i = j := by
    apply reverseFin_injective 17
    apply Fin.ext
    exact hr
  have finFourCases (u : Fin 4) :
      u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by
    fin_cases u <;> simp
  rcases finFourCases s with hs | hs | hs | hs <;>
    rcases finFourCases t with ht | ht | ht | ht <;>
    rw [hs, ht] at hv ⊢ <;>
    simp only [storedInitialNaturalIndex_child_zero,
      storedInitialNaturalIndex_child_one,
      storedInitialNaturalIndex_child_two,
      storedInitialNaturalIndex_child_three] at hv
  all_goals norm_num at hi hj hv ⊢
  all_goals try omega
  all_goals
    have hij : i = j := sameParent (by omega)
    simpa only using congrArg (fun q => childIndex q _) hij

/-- The exact full initial circle domain in stored, fibre-major order. -/
def storedInitialCirclePoint (k : Fin (2 ^ 19)) : C :=
  initialCirclePoint (storedInitialNaturalIndex k)

@[simp] theorem storedInitialCirclePoint_eq_zpow (k : Fin (2 ^ 19)) :
    storedInitialCirclePoint k =
      g ^ initialCircleExponent (storedInitialNaturalIndex k) := rfl

theorem storedInitialCirclePoint_injective :
    Function.Injective storedInitialCirclePoint :=
  initialCirclePoint_injective.comp storedInitialNaturalIndex_injective

theorem storedInitialCirclePoint_x_ne_neg_one (k : Fin (2 ^ 19)) :
    X (storedInitialCirclePoint k) ≠ -1 :=
  initialCirclePoint_x_ne_neg_one (storedInitialNaturalIndex k)

/-- Slot zero of one stored circle fibre. -/
def storedInitialFibrePoint (i : Fin 131072) : C :=
  storedInitialCirclePoint (childIndex i 0)

@[simp] theorem storedInitialFibrePoint_eq_zpow (i : Fin 131072) :
    storedInitialFibrePoint i =
      g ^ initialCircleExponent
        (storedInitialNaturalIndex (childIndex i 0)) := rfl

theorem storedInitialCirclePoint_child_zero (i : Fin 131072) :
    storedInitialCirclePoint (childIndex i 0) = storedInitialFibrePoint i := rfl

private theorem initialSlotOneModEq (r : Nat) (hr : r < 2 ^ 17) :
    (2 : Int) ^ 11 * (2 * ((2 ^ 19 - 1 - 2 * r : Nat) : Int) + 1) ≡
      -((2 : Int) ^ 11 * (2 * ((2 * r : Nat) : Int) + 1))
        [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  have hle : 2 * r ≤ 2 ^ 19 - 1 := by
    norm_num at hr ⊢
    omega
  rw [Nat.cast_sub hle]
  push_cast
  norm_num at hr ⊢
  omega

private theorem initialSlotTwoModEq (r : Nat) :
    (2 : Int) ^ 11 * (2 * ((2 ^ 18 + 2 * r : Nat) : Int) + 1) ≡
      (2 : Int) ^ 30 +
        (2 : Int) ^ 11 * (2 * ((2 * r : Nat) : Int) + 1)
        [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨0, ?_⟩
  push_cast
  ring

private theorem initialSlotThreeModEq (r : Nat) (hr : r < 2 ^ 17) :
    (2 : Int) ^ 11 * (2 * ((2 ^ 18 - 1 - 2 * r : Nat) : Int) + 1) ≡
      -(2 : Int) ^ 30 +
        -((2 : Int) ^ 11 * (2 * ((2 * r : Nat) : Int) + 1))
        [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-1, ?_⟩
  have hle : 2 * r ≤ 2 ^ 18 - 1 := by
    norm_num at hr ⊢
    omega
  rw [Nat.cast_sub hle]
  push_cast
  norm_num at hr ⊢
  omega

private theorem initialSlotZeroSquareModEq (r : Nat) :
    (2 : Int) ^ 11 * (2 * ((2 * r : Nat) : Int) + 1) * 2 ≡
      4096 + 16384 * (r : Int) [ZMOD (2 : Int) ^ 31] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨0, ?_⟩
  push_cast
  ring

/-- Slot one is the inverse (complex conjugate) of slot zero. -/
theorem storedInitialCirclePoint_child_one (i : Fin 131072) :
    storedInitialCirclePoint (childIndex i 1) =
      (storedInitialFibrePoint i)⁻¹ := by
  have hgroup :
      g ^ initialCircleExponent (storedInitialNaturalIndex (childIndex i 1)) =
        (g ^ initialCircleExponent
          (storedInitialNaturalIndex (childIndex i 0)))⁻¹ := by
    rw [← zpow_neg]
    apply (g_zpow_eq_iff _ _).2
    have hi := (reverseFin 17 i).isLt
    simp only [storedInitialNaturalIndex_child_one,
      storedInitialNaturalIndex_child_zero]
    unfold initialCircleExponent
    exact initialSlotOneModEq (reverseFin 17 i).val hi
  rw [storedInitialCirclePoint_eq_zpow, storedInitialFibrePoint_eq_zpow]
  exact hgroup

/-- The exact half turn is the point `(-1,0)`. -/
theorem halfTurn_point :
    g ^ ((2 : Int) ^ 30) =
      ⟨(-1, 0), by show (-1 : ZMod P) ^ 2 + (0 : ZMod P) ^ 2 = 1; ring⟩ := by
  rw [show (2 : Int) ^ 30 = ((2 ^ 30 : Nat) : Int) by norm_num, zpow_natCast]
  rw [← sq_iterate 30 g]
  decide

/-- Slot two is the half-turn rotation of slot zero. -/
theorem storedInitialCirclePoint_child_two (i : Fin 131072) :
    storedInitialCirclePoint (childIndex i 2) =
      g ^ ((2 : Int) ^ 30) * storedInitialFibrePoint i := by
  have hgroup :
      g ^ initialCircleExponent (storedInitialNaturalIndex (childIndex i 2)) =
        g ^ ((2 : Int) ^ 30) *
          g ^ initialCircleExponent (storedInitialNaturalIndex (childIndex i 0)) := by
    rw [← zpow_add]
    apply (g_zpow_eq_iff _ _).2
    have hi := (reverseFin 17 i).isLt
    simp only [storedInitialNaturalIndex_child_two,
      storedInitialNaturalIndex_child_zero]
    unfold initialCircleExponent
    exact initialSlotTwoModEq (reverseFin 17 i).val
  rw [storedInitialCirclePoint_eq_zpow, storedInitialFibrePoint_eq_zpow]
  exact hgroup

/-- Slot three is the inverse of slot two. -/
theorem storedInitialCirclePoint_child_three (i : Fin 131072) :
    storedInitialCirclePoint (childIndex i 3) =
      (g ^ ((2 : Int) ^ 30) * storedInitialFibrePoint i)⁻¹ := by
  have hgroup :
      g ^ initialCircleExponent (storedInitialNaturalIndex (childIndex i 3)) =
        (g ^ ((2 : Int) ^ 30) *
          g ^ initialCircleExponent (storedInitialNaturalIndex (childIndex i 0)))⁻¹ := by
    rw [mul_inv, ← zpow_neg, ← zpow_neg, ← zpow_add]
    apply (g_zpow_eq_iff _ _).2
    have hi := (reverseFin 17 i).isLt
    simp only [storedInitialNaturalIndex_child_three,
      storedInitialNaturalIndex_child_zero]
    unfold initialCircleExponent
    exact initialSlotThreeModEq (reverseFin 17 i).val hi
  rw [storedInitialCirclePoint_eq_zpow, storedInitialFibrePoint_eq_zpow]
  exact hgroup

private theorem finFourCases (slot : Fin 4) :
    slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
  fin_cases slot <;> simp

/-- X-coordinate pattern generated by one circle radix-four fibre. -/
def storedCircleSlotX (z : C) (slot : Fin 4) : ZMod P :=
  match slot.val with
  | 0 => AspisCircleGroupOrder.X z
  | 1 => AspisCircleGroupOrder.X z
  | 2 => -(AspisCircleGroupOrder.X z)
  | _ => -(AspisCircleGroupOrder.X z)

/-- Named y-coordinate projection.  Keeping the projection behind this typed
definition avoids elaborator transparency problems when `C` is unfolded. -/
def circleYCoordinate (z : C) : ZMod P := z.1.2

/-- Y-coordinate pattern generated by one circle radix-four fibre. -/
def storedCircleSlotY (z : C) (slot : Fin 4) : ZMod P :=
  match slot.val with
  | 0 => circleYCoordinate z
  | 1 => -(circleYCoordinate z)
  | 2 => -(circleYCoordinate z)
  | _ => circleYCoordinate z

/-- Exact x-coordinate pattern of the four stored circle points. -/
theorem storedInitialCirclePoint_x_slots (i : Fin 131072) (slot : Fin 4) :
    AspisCircleGroupOrder.X (storedInitialCirclePoint (childIndex i slot)) =
      storedCircleSlotX (storedInitialFibrePoint i) slot := by
  rcases finFourCases slot with hs | hs | hs | hs
  · rw [hs, storedInitialCirclePoint_child_zero]
    rfl
  · rw [hs, storedInitialCirclePoint_child_one]
    change (storedInitialFibrePoint i).1.1 =
      (storedInitialFibrePoint i).1.1
    rfl
  · rw [hs, storedInitialCirclePoint_child_two, halfTurn_point]
    change (-1 : ZMod P) * (storedInitialFibrePoint i).1.1 -
        0 * (storedInitialFibrePoint i).1.2 =
      -(storedInitialFibrePoint i).1.1
    ring
  · rw [hs, storedInitialCirclePoint_child_three, halfTurn_point]
    change (-1 : ZMod P) * (storedInitialFibrePoint i).1.1 -
        0 * (storedInitialFibrePoint i).1.2 =
      -(storedInitialFibrePoint i).1.1
    ring

/-- Exact y-coordinate pattern of the four stored circle points. -/
theorem storedInitialCirclePoint_y_slots (i : Fin 131072) (slot : Fin 4) :
    circleYCoordinate (storedInitialCirclePoint (childIndex i slot)) =
      storedCircleSlotY (storedInitialFibrePoint i) slot := by
  rcases finFourCases slot with hs | hs | hs | hs
  · rw [hs, storedInitialCirclePoint_child_zero]
    rfl
  · rw [hs, storedInitialCirclePoint_child_one]
    change -(storedInitialFibrePoint i).1.2 =
      -(storedInitialFibrePoint i).1.2
    rfl
  · rw [hs, storedInitialCirclePoint_child_two, halfTurn_point]
    change (-1 : ZMod P) * (storedInitialFibrePoint i).1.2 +
        0 * (storedInitialFibrePoint i).1.1 =
      -(storedInitialFibrePoint i).1.2
    ring
  · rw [hs, storedInitialCirclePoint_child_three, halfTurn_point]
    change -((-1 : ZMod P) * (storedInitialFibrePoint i).1.2 +
        0 * (storedInitialFibrePoint i).1.1) =
      (storedInitialFibrePoint i).1.2
    ring

/-! ## Squaring into the first released line domain -/

/-- First line-domain x-coordinate in the same stored order as `encoder1`. -/
def storedFirstLineX (i : Fin 131072) : ZMod P :=
  line17X (reverseFin 17 i)

theorem storedFirstLineX_injective : Function.Injective storedFirstLineX :=
  line17X_injective.comp (reverseFin_injective 17)

/-- Squaring the slot-zero point of a stored circle fibre gives the
corresponding first-line point. -/
theorem storedInitialFibrePoint_sq (i : Fin 131072) :
    storedInitialFibrePoint i ^ 2 = line17Point (reverseFin 17 i) := by
  have hgroup :
      (g ^ initialCircleExponent
        (storedInitialNaturalIndex (childIndex i 0))) ^ 2 =
          line17Point (reverseFin 17 i) := by
    rw [line17Point, ← zpow_natCast, ← zpow_mul]
    apply (g_zpow_eq_iff _ _).2
    have hi := (reverseFin 17 i).isLt
    simp only [storedInitialNaturalIndex_child_zero]
    unfold initialCircleExponent
    exact initialSlotZeroSquareModEq (reverseFin 17 i).val
  rw [storedInitialFibrePoint_eq_zpow]
  exact hgroup

/-- In field coordinates, the first line node is exactly `T2(x)` of the
slot-zero circle point. -/
theorem storedFirstLineX_eq_doubled (i : Fin 131072) :
    storedFirstLineX i =
      doubledFactor (X (storedInitialFibrePoint i)) 1 := by
  rw [storedFirstLineX, line17X, ← storedInitialFibrePoint_sq, X_sq]
  rfl

/-- The same squaring identity after embedding M31 into the evaluation
field. -/
theorem storedFirstLineX_eq_doubled_algebraMap
    [Algebra (ZMod P) K] (i : Fin 131072) :
    algebraMap (ZMod P) K (storedFirstLineX i) =
      doubledFactor
        (algebraMap (ZMod P) K (X (storedInitialFibrePoint i))) 1 := by
  have h := congrArg (algebraMap (ZMod P) K)
    (storedFirstLineX_eq_doubled i)
  simpa [doubledFactor, map_sub, map_mul, map_pow, map_one, map_ofNat] using h

/-! ## Exact initial-encoder evaluation identity -/

/-- Once `encoder1` has been proved to evaluate its natural polynomial on the
exact first line domain, the maintained `circleLiftEncoder` definition itself
implies evaluation of `p0(x) + y*p1(x)` on every exact stored circle point.
The initial evaluation identity is a conclusion here, not a premise. -/
theorem encoder0_eq_stored_circle_eval
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (points : EvaluationPoints (ZMod P))
    (hcircleX : ∀ i, points.circleX i = X (storedInitialFibrePoint i))
    (hcircleY : ∀ i, points.circleY i = circleYCoordinate (storedInitialFibrePoint i))
    (hencoder1 : ∀ (message : Coeff1 K) (i : Fin 131072),
      encoder1 schedule points message i =
        (naturalCoefficientPolynomial message).eval
          (algebraMap (ZMod P) K (storedFirstLineX i)))
    (message : Coeff0 K) (k : Fin (2 ^ 19)) :
    encoder0 schedule points message k =
      (initialP0 message).eval
          (algebraMap (ZMod P) K (X (storedInitialCirclePoint k))) +
        algebraMap (ZMod P) K (circleYCoordinate (storedInitialCirclePoint k)) *
          (initialP1 message).eval
            (algebraMap (ZMod P) K (X (storedInitialCirclePoint k))) := by
  suffices hchild : ∀ (i : Fin 131072) (slot : Fin 4),
      encoder0 schedule points message (childIndex i slot) =
        (initialP0 message).eval
            (algebraMap (ZMod P) K
              (X (storedInitialCirclePoint (childIndex i slot)))) +
          algebraMap (ZMod P) K
              (circleYCoordinate
                (storedInitialCirclePoint (childIndex i slot))) *
            (initialP1 message).eval
              (algebraMap (ZMod P) K
                (X (storedInitialCirclePoint (childIndex i slot)))) by
    have h := hchild (parentIndex (n := 131072) k)
      (slotIndex (n := 131072) k)
    rw [childIndex_parentIndex_slotIndex (n := 131072) k] at h
    exact h
  intro i slot
  rw [encoder0, circleLiftEncoder, radix4LiftEncoder_apply_child]
  simp only [extend1, Pi.neg_apply, hcircleX, hcircleY]
  have hnode := storedFirstLineX_eq_doubled_algebraMap (K := K) i
  have h0 := hencoder1 (coefficientLane 256 0 message) i
  have h1 := hencoder1 (coefficientLane 256 1 message) i
  have h2 := hencoder1 (coefficientLane 256 2 message) i
  have h3 := hencoder1 (coefficientLane 256 3 message) i
  have hfibre :
      storedInitialFibrePoint i =
        g ^ initialCircleExponent (2 * (reverseFin 17 i).val) := by
    simpa only [storedInitialFibrePoint_eq_zpow,
      storedInitialNaturalIndex_child_zero]
  have hnegNode :
      doubledFactor
          (-(algebraMap (ZMod P) K
            (X (storedInitialFibrePoint i)))) 1 =
        doubledFactor
          (algebraMap (ZMod P) K
            (X (storedInitialFibrePoint i))) 1 := by
    simp only [doubledFactor]
    ring
  rw [storedInitialCirclePoint_x_slots,
    storedInitialCirclePoint_y_slots]
  rcases finFourCases slot with hs | hs | hs | hs
  all_goals subst slot
  all_goals simp [storedCircleSlotX, storedCircleSlotY, radix4Evaluate]
  all_goals rw [← hfibre]
  all_goals
    rw [initialP0_eval_lanes, initialP1_eval_lanes]
    try rw [hnegNode]
    rw [← hnode]
    simp only [← h0, ← h1, ← h2, ← h3]
  all_goals ring

/-! ## Distance endpoint -/

/-- The maintained initial encoder, its exact stored domain, and the two
explicit degree-511 polynomials packaged for the generic circle root proof. -/
noncomputable def initialCirclePolynomialRealization
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (points : EvaluationPoints (ZMod P))
    (hcircleX : ∀ i, points.circleX i = X (storedInitialFibrePoint i))
    (hcircleY : ∀ i, points.circleY i = circleYCoordinate (storedInitialFibrePoint i))
    (hencoder1 : ∀ (message : Coeff1 K) (i : Fin 131072),
      encoder1 schedule points message i =
        (naturalCoefficientPolynomial message).eval
          (algebraMap (ZMod P) K (storedFirstLineX i))) :
    CirclePolynomialRealization (encoder0 schedule points) where
  point := storedInitialCirclePoint
  point_injective := storedInitialCirclePoint_injective
  avoids_west_pole := storedInitialCirclePoint_x_ne_neg_one
  p0 := initialP0
  p1 := initialP1
  p0_degree_lt := initialP0_degree_lt
  p1_degree_lt := initialP1_degree_lt
  coefficient_pair_injective := initialPolynomialPair_injective
  encoder_eq_circle_eval := encoder0_eq_stored_circle_eval schedule points
    hcircleX hcircleY hencoder1

/-- Exact distance statement for the initial released circle encoder.  The
only input is the already-derived first-line evaluation theorem; the initial
encoder's polynomial identity and distance are conclusions. -/
theorem initialEncoderDistance_of_exact_line_identity
    [Fintype K] [DecidableEq K]
    [Algebra (ZMod P) K] [NeZero (2 : K)]
    (schedule : FixedSchedule (ZMod P) K)
    (points : EvaluationPoints (ZMod P))
    (hcircleX : ∀ i, points.circleX i = X (storedInitialFibrePoint i))
    (hcircleY : ∀ i, points.circleY i = circleYCoordinate (storedInitialFibrePoint i))
    (hencoder1 : ∀ (message : Coeff1 K) (i : Fin 131072),
      encoder1 schedule points message i =
        (naturalCoefficientPolynomial message).eval
          (algebraMap (ZMod P) K (storedFirstLineX i))) :
    InitialEncoderDistance (concreteCodeEncoders schedule points) := by
  intro left right hne
  exact agreementSet_card_le_1024 (K := K)
    (fun message => encoder0 schedule points message)
    (initialCirclePolynomialRealization schedule points
      hcircleX hcircleY hencoder1) left right hne

/-! ## Audit -/

#print axioms naturalCoefficientPolynomial_eval_binary
#print axioms initialPolynomialPair_injective
#print axioms encoder0_eq_stored_circle_eval
#print axioms initialEncoderDistance_of_exact_line_identity

end AspisV5FriInitialCircleEncoderIdentity
