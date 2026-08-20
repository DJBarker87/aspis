import Coordinates.Funs
import V5FriCoordinateFieldSemantics
import V5FriCoordinateMathematics
import V5FriCoordinateTableSemantics

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000

/-!
# Exact point sequences produced by the extracted FRI coordinate loops

This file follows the two translated Rust helpers which choose the initial
circle points and derive the three parent point lists.  Successful executions
preserve caller order and return exactly one mathematically identified point
per requested index.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinatePointLoops

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev Point := aspis_core.circle_fri.BaseCirclePoint
abbrev PointVec := alloc.vec.Vec Point

end Coordinate

open AspisCircleGroupOrder
open AspisCircleDiscreteAvailability
open AspisV5FriBitReverse
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriReleasedLineGeometry
open AspisV5FriArithmeticSemantics
open AspisV5FriCoordinateFieldSemantics
open AspisV5FriCoordinateMathematics

instance : Inhabited Coordinate.Point :=
  ⟨{ x := 0#u32, y := 0#u32 }⟩

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

/-- The exact 64-bit reversal and right shift performed by the extracted
domain-19 fast path. -/
def sourceNatural (fiber : Std.U32) : Std.Usize :=
  let widened : Std.Usize := UScalar.cast .Usize fiber
  let reversed : Std.Usize := ⟨widened.bv.reverse⟩
  let shift := Std.U32.wrapping_sub core.num.Usize.BITS 17#u32
  Std.Usize.wrapping_shr reversed shift

def sourceLowIndex (fiber : Std.U32) : Std.Usize :=
  sourceNatural fiber &&& 255#usize

def sourceHighIndex (fiber : Std.U32) : Std.Usize :=
  Std.Usize.wrapping_shr (sourceNatural fiber) 8#u32

theorem sourceNatural_lt (fiber : Std.U32) :
    (sourceNatural fiber).val < 131072 := by
  rcases System.Platform.numBits_eq with hbits | hbits
  · have hreverse :=
    (BitVec.reverse (UScalar.cast .Usize fiber).bv).isLt
    simp [sourceNatural, core.num.Usize.BITS, hbits,
      Std.Usize.wrapping_shr, UScalar.wrapping_shr,
      Std.U32.wrapping_sub, UScalar.wrapping_sub,
      UScalar.val, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow] at hreverse ⊢
    omega
  · have hreverse :=
    (BitVec.reverse (UScalar.cast .Usize fiber).bv).isLt
    simp [sourceNatural, core.num.Usize.BITS, hbits,
      Std.Usize.wrapping_shr, UScalar.wrapping_shr,
      Std.U32.wrapping_sub, UScalar.wrapping_sub,
      UScalar.val, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow] at hreverse ⊢
    omega

theorem sourceLowIndex_lt (fiber : Std.U32) :
    (sourceLowIndex fiber).val < 256 := by
  unfold sourceLowIndex
  rw [UScalar.val_and]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem sourceHighIndex_lt (fiber : Std.U32) :
    (sourceHighIndex fiber).val < 512 := by
  have h := sourceNatural_lt fiber
  unfold sourceHighIndex Std.Usize.wrapping_shr UScalar.wrapping_shr
  change
    ((sourceNatural fiber).bv.ushiftRight
      ((8 : Nat) % UScalarTy.Usize.numBits)).toNat < 512
  have hvalue :
      ((sourceNatural fiber).bv.ushiftRight
          ((8 : Nat) % UScalarTy.Usize.numBits)).toNat =
        (sourceNatural fiber).val >>>
          ((8 : Nat) % UScalarTy.Usize.numBits) := by
    exact BitVec.toNat_ushiftRight _ _
  rw [hvalue]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [hbits, Nat.shiftRight_eq_div_pow] <;>
    omega

theorem sourceLowIndex_val (fiber : Std.U32) :
    (sourceLowIndex fiber).val = (sourceNatural fiber).val % 256 := by
  unfold sourceLowIndex
  rw [UScalar.val_and]
  change (sourceNatural fiber).val &&& 255 =
    (sourceNatural fiber).val % 256
  rw [show 255 = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

theorem sourceHighIndex_val (fiber : Std.U32) :
    (sourceHighIndex fiber).val = (sourceNatural fiber).val / 256 := by
  unfold sourceHighIndex Std.Usize.wrapping_shr UScalar.wrapping_shr
  change
    ((sourceNatural fiber).bv.ushiftRight
      ((8 : Nat) % UScalarTy.Usize.numBits)).toNat =
        (sourceNatural fiber).val / 256
  have hvalue :
      ((sourceNatural fiber).bv.ushiftRight
          ((8 : Nat) % UScalarTy.Usize.numBits)).toNat =
        (sourceNatural fiber).val >>>
          ((8 : Nat) % UScalarTy.Usize.numBits) := by
    exact BitVec.toNat_ushiftRight _ _
  rw [hvalue]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [hbits, Nat.shiftRight_eq_div_pow]

/-- A translated point represents the stated mathematical circle point. -/
def Represents (point : Coordinate.Point) (expected : C) : Prop :=
  pointCanonical point ∧
    AspisV5FriCoordinateFieldSemantics.pointValue point = expected.1

private theorem circle_mul_value (left right : C) :
    (left * right).1 =
      (left.1.1 * right.1.1 - left.1.2 * right.1.2,
        left.1.1 * right.1.2 + left.1.2 * right.1.1) := by
  rfl

def lowEntry (index : Fin 256) : Coordinate.Point :=
  let entry :=
    V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW.val[index.val]
  { x := entry.val[0]!, y := entry.val[1]! }

def highEntry (index : Fin 512) : Coordinate.Point :=
  let entry :=
    V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW.val[index.val]
  { x := entry.val[0]!, y := entry.val[1]! }

set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
theorem lowEntry_canonical (index : Fin 256) :
    pointCanonical (lowEntry index) := by
  revert index
  simp [pointCanonical,
    AspisV5FriCoordinateFieldSemantics.canonicalM31,
    AspisV5FriArithmeticSemantics.canonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus, lowEntry]
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 80000000 in
theorem highEntry_canonical (index : Fin 512) :
    pointCanonical (highEntry index) := by
  revert index
  simp [pointCanonical,
    AspisV5FriCoordinateFieldSemantics.canonicalM31,
    AspisV5FriArithmeticSemantics.canonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus, highEntry]
  decide

theorem lowEntry_value (index : Fin 256) :
    AspisV5FriCoordinateFieldSemantics.pointValue (lowEntry index) =
      (lowWindowPoint (index : Nat)).1 := by
  have h := AspisV5FriCoordinateTableSemantics.low_window_exact index
  unfold AspisV5FriCoordinateTableSemantics.tablePoint at h
  rw [getElemBang_eq_getElem _ _ index.isLt] at h
  unfold lowEntry AspisV5FriCoordinateFieldSemantics.pointValue
    AspisV5FriCoordinateFieldSemantics.m31Value lowWindowPoint
  convert h using 1 <;> rfl

theorem highEntry_value (index : Fin 512) :
    AspisV5FriCoordinateFieldSemantics.pointValue (highEntry index) =
      (highWindowPoint (index : Nat)).1 := by
  have h := AspisV5FriCoordinateTableSemantics.high_window_exact index
  unfold AspisV5FriCoordinateTableSemantics.tablePoint at h
  rw [getElemBang_eq_getElem _ _ index.isLt] at h
  unfold highEntry AspisV5FriCoordinateFieldSemantics.pointValue
    AspisV5FriCoordinateFieldSemantics.m31Value highWindowPoint
  convert h using 1 <;> rfl

private theorem coordinate_P_eq_arithmetic :
    V5FriCoordinateAdapter.aspis_core.field.P =
      V5FriArithmeticExact.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5FriCoordinateAdapter.aspis_core.field.P
    V5FriArithmeticExact.field.P
  rfl

private theorem coordinate_reduce_call_eq_arithmetic (value : Std.U64) :
    V5FriCoordinateAdapter.aspis_core.field.reduce_u64 value =
      V5FriArithmeticExact.field.reduce_u64 value := by
  unfold V5FriCoordinateAdapter.aspis_core.field.reduce_u64
    V5FriArithmeticExact.field.reduce_u64
  rw [coordinate_P_eq_arithmetic]

private theorem coordinate_mul_call_eq_arithmetic
    (left right : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.mul left right =
      V5FriArithmeticExact.field.M31.mul left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.mul
    V5FriArithmeticExact.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [coordinate_reduce_call_eq_arithmetic]

private theorem coordinate_add_call_eq_arithmetic
    (left right : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.add left right =
      V5FriArithmeticExact.field.M31.add left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.add
    V5FriArithmeticExact.field.M31.add
  rw [coordinate_P_eq_arithmetic]

private theorem coordinate_sub_call_eq_arithmetic
    (left right : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.sub left right =
      V5FriArithmeticExact.field.M31.sub left right := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.sub
    V5FriArithmeticExact.field.M31.sub
  rw [coordinate_P_eq_arithmetic]

private theorem coordinate_neg_call_eq_arithmetic
    (input : Coordinate.M31) :
    V5FriCoordinateAdapter.aspis_core.field.M31.neg input =
      V5FriArithmeticExact.field.M31.neg input := by
  unfold V5FriCoordinateAdapter.aspis_core.field.M31.neg
    V5FriArithmeticExact.field.M31.neg
  rw [coordinate_P_eq_arithmetic]

/-- One extracted fast-path iteration, factored out only to state its
postcondition.  This is the expression appearing verbatim in loop body 1. -/
def selectedPointCall (fiber : Std.U32) : Result Coordinate.Point := do
  let lowArray ←
    Array.index_usize
      V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
      (sourceLowIndex fiber)
  let lowX ← Array.index_usize lowArray 0#usize
  let lowY ← Array.index_usize lowArray 1#usize
  let low : Coordinate.Point := { x := lowX, y := lowY }
  if sourceHighIndex fiber != 0#usize then
    let highArray ←
      Array.index_usize
        V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
        (sourceHighIndex fiber)
    let highX ← Array.index_usize highArray 0#usize
    let highY ← Array.index_usize highArray 1#usize
    V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add low
      { x := highX, y := highY }
  else
    ok low

def selectedExpectedPoint (fiber : Std.U32) : C :=
  g ^ representativeExp (sourceNatural fiber).val

/-- Point addition is total on the canonical table values and implements the
circle group product. -/
theorem point_add_produces_product
    (left right : Coordinate.Point)
    (hleft : pointCanonical left)
    (hright : pointCanonical right) :
    ∃ output : Coordinate.Point,
      V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add
          left right = .ok output ∧
      pointCanonical output ∧
      AspisV5FriCoordinateFieldSemantics.pointValue output =
        (m31Value left.x * m31Value right.x -
            m31Value left.y * m31Value right.y,
          m31Value left.x * m31Value right.y +
            m31Value left.y * m31Value right.x) := by
  obtain ⟨xx, hxxRun, hxxCanonical, hxxValue⟩ :=
    m31_mul_corresponds left.x right.x hleft.1 hright.1
  obtain ⟨yy, hyyRun, hyyCanonical, hyyValue⟩ :=
    m31_mul_corresponds left.y right.y hleft.2 hright.2
  obtain ⟨x, hxRun, hxCanonical, hxValue⟩ :=
    m31_sub_corresponds xx yy hxxCanonical hyyCanonical
  obtain ⟨xy, hxyRun, hxyCanonical, hxyValue⟩ :=
    m31_mul_corresponds left.x right.y hleft.1 hright.2
  obtain ⟨yx, hyxRun, hyxCanonical, hyxValue⟩ :=
    m31_mul_corresponds left.y right.x hleft.2 hright.1
  obtain ⟨y, hyRun, hyCanonical, hyValue⟩ :=
    m31_add_corresponds xy yx hxyCanonical hyxCanonical
  have hxxCoordinate :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.x right.x =
        .ok xx := by
    rw [coordinate_mul_call_eq_arithmetic]
    exact hxxRun
  have hyyCoordinate :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.y right.y =
        .ok yy := by
    rw [coordinate_mul_call_eq_arithmetic]
    exact hyyRun
  have hxCoordinate :
      V5FriCoordinateAdapter.aspis_core.field.M31.sub xx yy = .ok x := by
    rw [coordinate_sub_call_eq_arithmetic]
    exact hxRun
  have hxyCoordinate :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.x right.y =
        .ok xy := by
    rw [coordinate_mul_call_eq_arithmetic]
    exact hxyRun
  have hyxCoordinate :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul left.y right.x =
        .ok yx := by
    rw [coordinate_mul_call_eq_arithmetic]
    exact hyxRun
  have hyCoordinate :
      V5FriCoordinateAdapter.aspis_core.field.M31.add xy yx = .ok y := by
    rw [coordinate_add_call_eq_arithmetic]
    exact hyRun
  let output : Coordinate.Point := { x := x, y := y }
  refine ⟨output, ?_, ⟨hxCanonical, hyCanonical⟩, ?_⟩
  · simp [V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add,
      hxxCoordinate, hyyCoordinate, hxCoordinate, hxyCoordinate,
      hyxCoordinate, hyCoordinate, output]
  · apply Prod.ext
    · change AspisV5FriCoordinateFieldSemantics.m31Value x =
        m31Value left.x * m31Value right.x -
          m31Value left.y * m31Value right.y
      unfold AspisV5FriCoordinateFieldSemantics.m31Value
      rw [hxValue, hxxValue, hyyValue]
    · change AspisV5FriCoordinateFieldSemantics.m31Value y =
        m31Value left.x * m31Value right.y +
          m31Value left.y * m31Value right.x
      unfold AspisV5FriCoordinateFieldSemantics.m31Value
      rw [hyValue, hxyValue, hyxValue]

/-- One translated fast-path iteration returns the exact split-window circle
point.  Both table reads and the optional group addition are accounted for. -/
theorem selectedPointCall_exact (fiber : Std.U32) :
    ∃ output : Coordinate.Point,
      selectedPointCall fiber = .ok output ∧
      Represents output (selectedExpectedPoint fiber) := by
  let lowIndex : Fin 256 :=
    ⟨(sourceLowIndex fiber).val, sourceLowIndex_lt fiber⟩
  obtain ⟨lowArray, hlowArrayRun, hlowArrayValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec
        V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
        (sourceLowIndex fiber) (sourceLowIndex_lt fiber))
  obtain ⟨lowX, hlowXRun, hlowXValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec lowArray 0#usize (by simp))
  obtain ⟨lowY, hlowYRun, hlowYValue⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Array.index_usize_spec lowArray 1#usize (by simp))
  let low : Coordinate.Point := { x := lowX, y := lowY }
  have hlowEq : low = lowEntry lowIndex := by
    simp [low, lowEntry, lowIndex, hlowArrayValue, hlowXValue, hlowYValue]
  have hlowRep : Represents low (lowWindowPoint lowIndex.val) := by
    rw [hlowEq]
    exact ⟨lowEntry_canonical lowIndex, lowEntry_value lowIndex⟩
  by_cases hhighZero : sourceHighIndex fiber = 0#usize
  · refine ⟨low, ?_, ?_⟩
    · simp [selectedPointCall, hlowArrayRun, hlowXRun, hlowYRun,
        hhighZero, low]
    · have hdiv : (sourceNatural fiber).val / 256 = 0 := by
        rw [← sourceHighIndex_val fiber]
        exact congrArg UScalar.val hhighZero
      have hlowValue : lowIndex.val =
          (sourceNatural fiber).val % 256 := by
        exact sourceLowIndex_val fiber
      have hproduct :=
        low_mul_high_eq_representative (sourceNatural fiber).val
      have hmath :
          lowWindowPoint lowIndex.val = selectedExpectedPoint fiber := by
        unfold selectedExpectedPoint
        simpa [hlowValue, hdiv, highWindowPoint] using hproduct
      exact ⟨hlowRep.1, hlowRep.2.trans (congrArg Subtype.val hmath)⟩
  · let highIndex : Fin 512 :=
      ⟨(sourceHighIndex fiber).val, sourceHighIndex_lt fiber⟩
    obtain ⟨highArray, hhighArrayRun, hhighArrayValue⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec
          V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
          (sourceHighIndex fiber) (sourceHighIndex_lt fiber))
    obtain ⟨highX, hhighXRun, hhighXValue⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec highArray 0#usize (by simp))
    obtain ⟨highY, hhighYRun, hhighYValue⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Array.index_usize_spec highArray 1#usize (by simp))
    let high : Coordinate.Point := { x := highX, y := highY }
    have hhighEq : high = highEntry highIndex := by
      simp [high, highEntry, highIndex, hhighArrayValue, hhighXValue,
        hhighYValue]
    have hhighRep : Represents high (highWindowPoint highIndex.val) := by
      rw [hhighEq]
      exact ⟨highEntry_canonical highIndex, highEntry_value highIndex⟩
    obtain ⟨output, haddRun, houtputCanonical, houtputPair⟩ :=
      point_add_produces_product low high hlowRep.1 hhighRep.1
    refine ⟨output, ?_, ⟨houtputCanonical, ?_⟩⟩
    · simp [selectedPointCall, hlowArrayRun, hlowXRun, hlowYRun,
        hhighZero, hhighArrayRun, hhighXRun, hhighYRun, low, high, haddRun]
    · have houtputValue :
          AspisV5FriCoordinateFieldSemantics.pointValue output =
            (lowWindowPoint lowIndex.val *
              highWindowPoint highIndex.val).1 := by
        calc
          AspisV5FriCoordinateFieldSemantics.pointValue output =
              (m31Value low.x * m31Value high.x -
                  m31Value low.y * m31Value high.y,
                m31Value low.x * m31Value high.y +
                  m31Value low.y * m31Value high.x) := houtputPair
          _ = (
              (lowWindowPoint lowIndex.val).1.1 *
                  (highWindowPoint highIndex.val).1.1 -
                (lowWindowPoint lowIndex.val).1.2 *
                  (highWindowPoint highIndex.val).1.2,
              (lowWindowPoint lowIndex.val).1.1 *
                  (highWindowPoint highIndex.val).1.2 +
                (lowWindowPoint lowIndex.val).1.2 *
                  (highWindowPoint highIndex.val).1.1) := by
                    rw [← hlowRep.2, ← hhighRep.2]
                    rfl
          _ = (lowWindowPoint lowIndex.val *
              highWindowPoint highIndex.val).1 := by
                symm
                exact circle_mul_value _ _
      have hlowValue : lowIndex.val =
          (sourceNatural fiber).val % 256 := sourceLowIndex_val fiber
      have hhighValue : highIndex.val =
          (sourceNatural fiber).val / 256 := sourceHighIndex_val fiber
      have hmath :
          lowWindowPoint lowIndex.val * highWindowPoint highIndex.val =
            selectedExpectedPoint fiber := by
        unfold selectedExpectedPoint
        simpa [hlowValue, hhighValue] using
          low_mul_high_eq_representative (sourceNatural fiber).val
      exact houtputValue.trans (congrArg Subtype.val hmath)

/-- The expression emitted by Aeneas inside the production loop is exactly
`selectedPointCall`; the factoring above does not change the computation. -/
private theorem generated_selectedPointCall_eq (fiber : Std.U32) :
    (do
      let widened ← lift (UScalar.cast .Usize fiber)
      let reversed ← core.num.Usize.reverse_bits widened
      let shift ← lift (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32)
      let natural ← lift (Std.Usize.wrapping_shr reversed shift)
      let lowIndex ← lift (natural &&& 255#usize)
      let lowArray ←
        Array.index_usize
          V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
          lowIndex
      let lowX ← Array.index_usize lowArray 0#usize
      let lowY ← Array.index_usize lowArray 1#usize
      let highIndex ← lift (Std.Usize.wrapping_shr natural 8#u32)
      if highIndex != 0#usize then
        let highArray ←
          Array.index_usize
            V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
            highIndex
        let highX ← Array.index_usize highArray 0#usize
        let highY ← Array.index_usize highArray 1#usize
        V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add
          { x := lowX, y := lowY } { x := highX, y := highY }
      else
        ok ({ x := lowX, y := lowY } : Coordinate.Point)) =
      selectedPointCall fiber := by
  simp [selectedPointCall, sourceNatural, sourceLowIndex, sourceHighIndex,
    core.num.Usize.reverse_bits, Std.lift]

private theorem result_bind_ite {T U : Type} (condition : Prop)
    [Decidable condition] (yes no : Result T) (next : T → Result U) :
    (if condition then yes else no) >>= next =
      if condition then yes >>= next else no >>= next := by
  by_cases hcondition : condition <;> simp [hcondition]

private theorem generated_selectedContinuation_eq
    (fiber : Std.U32) (points : Coordinate.PointVec)
    (ordinal : Std.Usize) :
    (do
      let widened ← lift (UScalar.cast .Usize fiber)
      let reversed ← core.num.Usize.reverse_bits widened
      let shift ← lift (Std.U32.wrapping_sub core.num.Usize.BITS 17#u32)
      let natural ← lift (Std.Usize.wrapping_shr reversed shift)
      let lowIndex ← lift (natural &&& 255#usize)
      let lowArray ←
        Array.index_usize
          V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
          lowIndex
      let lowX ← Array.index_usize lowArray 0#usize
      let lowY ← Array.index_usize lowArray 1#usize
      let highIndex ← lift (Std.Usize.wrapping_shr natural 8#u32)
      if highIndex != 0#usize then
        let highArray ←
          Array.index_usize
            V5FriCoordinateAdapter.aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
            highIndex
        let highX ← Array.index_usize highArray 0#usize
        let highY ← Array.index_usize highArray 1#usize
        let point ←
          V5FriCoordinateAdapter.aspis_core.circle_fri.BaseCirclePoint.add
            { x := lowX, y := lowY } { x := highX, y := highY }
        let nextPoints ← alloc.vec.Vec.push points point
        let nextOrdinal ←
          lift (Std.Usize.wrapping_add ordinal 1#usize)
        ok (cont (nextPoints, nextOrdinal) :
          ControlFlow (Coordinate.PointVec × Std.Usize)
            Coordinate.PointVec)
      else
        let nextPoints ← alloc.vec.Vec.push points
          ({ x := lowX, y := lowY } : Coordinate.Point)
        let nextOrdinal ←
          lift (Std.Usize.wrapping_add ordinal 1#usize)
        ok (cont (nextPoints, nextOrdinal) :
          ControlFlow (Coordinate.PointVec × Std.Usize)
            Coordinate.PointVec)) =
      (do
        let point ← selectedPointCall fiber
        let nextPoints ← alloc.vec.Vec.push points point
        let nextOrdinal ←
          lift (Std.Usize.wrapping_add ordinal 1#usize)
        ok (cont (nextPoints, nextOrdinal) :
          ControlFlow (Coordinate.PointVec × Std.Usize)
            Coordinate.PointVec)) := by
  simp [selectedPointCall, sourceNatural, sourceLowIndex, sourceHighIndex,
    core.num.Usize.reverse_bits, Std.lift, bind_assoc, result_bind_ite]

private theorem wrapping_add_one_exact (value : Std.Usize)
    (hsmall : value.val + 1 < UScalar.size .Usize) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using hsmall)

/-- Exact pointwise meaning of a returned initial-circle point list. -/
def SelectedPointsPost (fibers : Slice Std.U32)
    (points : Coordinate.PointVec) : Prop :=
  points.val.length = fibers.val.length ∧
    ∀ (index : Nat) (hindex : index < fibers.val.length),
      Represents points.val[index]!
        (selectedExpectedPoint fibers.val[index]!)

private def SelectedPointsInvariant (fibers : Slice Std.U32)
    (state : Coordinate.PointVec × Std.Usize) : Prop :=
  state.2.val ≤ fibers.val.length ∧
    state.1.val.length = state.2.val ∧
    ∀ (index : Nat) (hindex : index < state.2.val),
      Represents state.1.val[index]!
        (selectedExpectedPoint fibers.val[index]!)

/-- The translated point-building loop preserves caller order and emits one
exact split-window circle point for every requested fiber. -/
theorem selected_points_loop_exact
    (fibers : Slice Std.U32) (points : Coordinate.PointVec)
    (hpoints : points.val = []) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1
        fibers points 0#usize
      ⦃ output => SelectedPointsPost fibers output ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1
  apply loop.spec_decr_nat
    (fun state => fibers.val.length - state.2.val)
    (SelectedPointsInvariant fibers)
    (SelectedPointsPost fibers)
  · rintro ⟨currentPoints, currentOrdinal⟩ hstate
    rcases hstate with ⟨hordinalLe, hlength, hrepresents⟩
    simp only at hordinalLe hlength hrepresents
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop1.body
    by_cases hactive : currentOrdinal.val < fibers.val.length
    · have hcondition : currentOrdinal < Slice.len fibers := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      obtain ⟨fiber, hfiberRun, hfiberValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.index_usize_spec fibers currentOrdinal hactive)
      obtain ⟨point, hpointRun, hpointRep⟩ :=
        selectedPointCall_exact fiber
      have hcapacity : currentPoints.val.length < Std.Usize.max := by
        have hfibersMax := fibers.property
        omega
      obtain ⟨nextPoints, hpushRun, hnextPoints⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (alloc.vec.Vec.push_spec currentPoints point hcapacity)
      have hordinalSmall :
          currentOrdinal.val + 1 < UScalar.size .Usize := by
        have hfibersMax := fibers.property
        have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
          simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
        rw [hsize]
        omega
      let nextOrdinal :=
        Std.Usize.wrapping_add currentOrdinal 1#usize
      have hnextOrdinal : nextOrdinal.val = currentOrdinal.val + 1 := by
        unfold nextOrdinal
        exact wrapping_add_one_exact currentOrdinal hordinalSmall
      simp only [if_pos hcondition]
      rw [hfiberRun]
      simp only [bind_tc_ok]
      rw [generated_selectedContinuation_eq fiber currentPoints currentOrdinal,
        hpointRun]
      simp only [bind_tc_ok]
      rw [hpushRun]
      simp only [bind_tc_ok, WP.spec_ok]
      change SelectedPointsInvariant fibers (nextPoints, nextOrdinal) ∧
        fibers.val.length - nextOrdinal.val <
          fibers.val.length - currentOrdinal.val
      refine ⟨?_, by rw [hnextOrdinal]; omega⟩
      unfold SelectedPointsInvariant
      simp only
      refine ⟨by rw [hnextOrdinal]; omega, ?_, ?_⟩
      · rw [hnextPoints, List.length_append, hlength, hnextOrdinal]
        simp
      · intro index hindex
        rw [hnextOrdinal] at hindex
        by_cases hprior : index < currentOrdinal.val
        · have hleft : index < currentPoints.val.length := by
            simpa [hlength] using hprior
          have happendBang :
              (currentPoints.val ++ [point])[index]! =
                currentPoints.val[index]! := by
            rw [getElemBang_eq_getElem _ _
                (by simp only [List.length_append, List.length_singleton];
                    omega),
              getElemBang_eq_getElem _ _ hleft,
              List.getElem_append_left hleft]
          rw [hnextPoints, happendBang]
          exact hrepresents index hprior
        · have hlast : index = currentOrdinal.val := by omega
          subst index
          have happendBang :
              (currentPoints.val ++ [point])[currentOrdinal.val]! = point := by
            rw [getElemBang_eq_getElem _ _ (by simp [hlength])]
            simp [hlength]
          have hfiberBang :
              fibers.val[currentOrdinal.val]! = fiber := by
            rw [getElemBang_eq_getElem _ _ hactive]
            exact hfiberValue.symm
          rw [hnextPoints, happendBang, hfiberBang]
          exact hpointRep
    · have hdone : currentOrdinal.val = fibers.val.length := by omega
      have hcondition : ¬ currentOrdinal < Slice.len fibers := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      unfold SelectedPointsPost
      rw [← hdone]
      exact ⟨hlength, hrepresents⟩
  · unfold SelectedPointsInvariant
    simp only
    exact ⟨by simp, by simp [hpoints], by simp⟩

/-- Every successful call of the translated public helper returns precisely
the points described above.  This conclusion is independent of the validity
flag; callers separately require that flag to be true. -/
theorem selected_circle_fiber_points_shared_success
    (domainLogSize : Std.U32) (fibers : Slice Std.U32)
    (output : Coordinate.PointVec) (valid : Bool)
    (hrun :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
          domainLogSize fibers = .ok (output, valid)) :
    SelectedPointsPost fibers output := by
  let initial : Coordinate.PointVec :=
    alloc.vec.Vec.with_capacity Coordinate.Point (Slice.len fibers)
  have hinitial : initial.val = [] := by
    rfl
  obtain ⟨built, hbuiltRun, hbuiltPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (selected_points_loop_exact fibers initial hinitial)
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared
    at hrun
  simp only [Std.lift, bind_tc_ok] at hrun
  cases hvalidation :
      V5FriCoordinateAdapter.aspis_core.circle_fri.selected_circle_fiber_points_shared_loop0
        fibers (Std.Usize.wrapping_shl 1#usize 17#u32)
          (domainLogSize = 19#u32) 0#usize <;>
    simp [hvalidation, initial, hbuiltRun] at hrun
  rcases hrun with ⟨rfl, rfl⟩
  exact hbuiltPost

/-! ## Point operations used by the parent-layer loop -/

/-- The optimized translated doubling helper is total on represented circle
points and returns the mathematical group square. -/
theorem double_point_produces_square
    (input : Coordinate.Point) (expected : C)
    (hinput : Represents input expected) :
    ∃ output : Coordinate.Point,
      V5FriCoordinateAdapter.aspis_core.circle_fri.double_point input =
          .ok output ∧
      Represents output (expected ^ 2) := by
  obtain ⟨added, haddRunArithmetic, haddCanonical, haddValue⟩ :=
    m31_add_corresponds input.x input.y hinput.1.1 hinput.1.2
  obtain ⟨subtracted, hsubRunArithmetic, hsubCanonical, hsubValue⟩ :=
    m31_sub_corresponds input.x input.y hinput.1.1 hinput.1.2
  obtain ⟨x, hxRunArithmetic, hxCanonical, hxValue⟩ :=
    m31_mul_corresponds added subtracted haddCanonical hsubCanonical
  obtain ⟨product, hproductRunArithmetic, hproductCanonical,
      hproductValue⟩ :=
    m31_mul_corresponds input.x input.y hinput.1.1 hinput.1.2
  obtain ⟨y, hyRun, hyCanonical, hyValue⟩ :=
    AspisV5FriCoordinateFieldSemantics.double_produces_canonical
      product hproductCanonical
  have haddRun :
      V5FriCoordinateAdapter.aspis_core.field.M31.add input.x input.y =
        .ok added := by
    rw [coordinate_add_call_eq_arithmetic]
    exact haddRunArithmetic
  have hsubRun :
      V5FriCoordinateAdapter.aspis_core.field.M31.sub input.x input.y =
        .ok subtracted := by
    rw [coordinate_sub_call_eq_arithmetic]
    exact hsubRunArithmetic
  have hxRun :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul added subtracted =
        .ok x := by
    rw [coordinate_mul_call_eq_arithmetic]
    exact hxRunArithmetic
  have hproductRun :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul input.x input.y =
        .ok product := by
    rw [coordinate_mul_call_eq_arithmetic]
    exact hproductRunArithmetic
  let output : Coordinate.Point := { x := x, y := y }
  refine ⟨output, ?_, ⟨⟨hxCanonical, hyCanonical⟩, ?_⟩⟩
  · simp [V5FriCoordinateAdapter.aspis_core.circle_fri.double_point,
      haddRun, hsubRun, hxRun, hproductRun, hyRun, output]
  · have houtputValue :
        AspisV5FriCoordinateFieldSemantics.pointValue output =
          (m31Value input.x ^ 2 - m31Value input.y ^ 2,
            2 * m31Value input.x * m31Value input.y) := by
      apply Prod.ext
      · change AspisV5FriCoordinateFieldSemantics.m31Value x = _
        unfold AspisV5FriCoordinateFieldSemantics.m31Value
        rw [hxValue, haddValue, hsubValue]
        ring
      · change AspisV5FriCoordinateFieldSemantics.m31Value y = _
        rw [hyValue]
        unfold AspisV5FriCoordinateFieldSemantics.m31Value
        rw [hproductValue]
        simp only [Prod.snd]
    calc
      AspisV5FriCoordinateFieldSemantics.pointValue output =
          (m31Value input.x ^ 2 - m31Value input.y ^ 2,
            2 * m31Value input.x * m31Value input.y) := houtputValue
      _ = (expected ^ 2).1 := by
        have hsquare :
            (expected ^ 2).1 =
              (expected.1.1 * expected.1.1 -
                  expected.1.2 * expected.1.2,
                expected.1.1 * expected.1.2 +
                  expected.1.2 * expected.1.1) := by
          simpa [pow_two] using (circle_mul_value expected expected)
        rw [hsquare]
        rw [← hinput.2]
        unfold AspisV5FriCoordinateFieldSemantics.pointValue
        ring

private theorem neg_produces
    (input : Coordinate.M31)
    (hinput : AspisV5FriCoordinateFieldSemantics.canonicalM31 input) :
    ∃ output : Coordinate.M31,
      V5FriCoordinateAdapter.aspis_core.field.M31.neg input = .ok output ∧
      AspisV5FriCoordinateFieldSemantics.canonicalM31 output ∧
      m31Value output = -m31Value input := by
  obtain ⟨output, hrunArithmetic, hcanonical, hvalue⟩ :=
    m31_neg_corresponds input hinput
  refine ⟨output, ?_, hcanonical, hvalue⟩
  rw [coordinate_neg_call_eq_arithmetic]
  exact hrunArithmetic

/-- The translated four-way sign/swap helper exactly implements the
mathematical slot-normalization operation. -/
theorem remove_line_slot_rotation_produces
    (input : Coordinate.Point) (expected : C)
    (sourceSlot : Std.U32) (hslot : sourceSlot.val < 4)
    (hinput : Represents input expected) :
    ∃ output : Coordinate.Point,
      V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation
          input sourceSlot = .ok output ∧
      Represents output
        (removeLineSlotRotation expected ⟨sourceSlot.val, hslot⟩) := by
  have hcases : sourceSlot.val = 0 ∨ sourceSlot.val = 1 ∨
      sourceSlot.val = 2 ∨ sourceSlot.val = 3 := by
    omega
  rcases hcases with hzero | hone | htwo | hthree
  · have hsource : sourceSlot = (0#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by simp [hzero, UScalar.val])
    refine ⟨input, ?_, ?_⟩
    · rw [hsource]
      exact
        V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation.eq_1
          input
    · simpa [removeLineSlotRotation, hzero] using hinput
  · have hsource : sourceSlot = (1#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by simp [hone, UScalar.val])
    obtain ⟨negativeX, hxRun, hxCanonical, hxValue⟩ :=
      neg_produces input.x hinput.1.1
    obtain ⟨negativeY, hyRun, hyCanonical, hyValue⟩ :=
      neg_produces input.y hinput.1.2
    let output : Coordinate.Point := { x := negativeX, y := negativeY }
    refine ⟨output, ?_, ⟨⟨hxCanonical, hyCanonical⟩, ?_⟩⟩
    · rw [hsource]
      have hoperation :=
        V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation.eq_2
          input
      rw [hxRun, hyRun] at hoperation
      simpa [output] using hoperation
    · unfold AspisV5FriCoordinateFieldSemantics.pointValue output
      simp only [removeLineSlotRotation, hone]
      apply Prod.ext
      · change m31Value negativeX = -expected.1.1
        rw [hxValue, ← hinput.2]
        rfl
      · change m31Value negativeY = -expected.1.2
        rw [hyValue, ← hinput.2]
        rfl
  · have hsource : sourceSlot = (2#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by simp [htwo, UScalar.val])
    obtain ⟨negativeY, hyRun, hyCanonical, hyValue⟩ :=
      neg_produces input.y hinput.1.2
    let output : Coordinate.Point := { x := negativeY, y := input.x }
    refine ⟨output, ?_, ⟨⟨hyCanonical, hinput.1.1⟩, ?_⟩⟩
    · rw [hsource]
      have hoperation :=
        V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation.eq_3
          input
      rw [hyRun] at hoperation
      simpa [output] using hoperation
    · unfold AspisV5FriCoordinateFieldSemantics.pointValue output
      simp only [removeLineSlotRotation, htwo]
      apply Prod.ext
      · change m31Value negativeY = -expected.1.2
        rw [hyValue, ← hinput.2]
        rfl
      · change m31Value input.x = expected.1.1
        rw [← hinput.2]
        rfl
  · have hsource : sourceSlot = (3#32#uscalar : Std.U32) :=
      UScalar.eq_of_val_eq (by simp [hthree, UScalar.val])
    obtain ⟨negativeX, hxRun, hxCanonical, hxValue⟩ :=
      neg_produces input.x hinput.1.1
    let output : Coordinate.Point := { x := input.y, y := negativeX }
    refine ⟨output, ?_, ⟨⟨hinput.1.2, hxCanonical⟩, ?_⟩⟩
    · rw [hsource]
      have hoperation :=
        V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation.eq_4
          input
      rw [hxRun] at hoperation
      simpa [output] using hoperation
    · unfold AspisV5FriCoordinateFieldSemantics.pointValue output
      simp only [removeLineSlotRotation, hthree]
      apply Prod.ext
      · change m31Value input.y = expected.1.2
        rw [← hinput.2]
        rfl
      · change m31Value negativeX = -expected.1.1
        rw [hxValue, ← hinput.2]
        rfl

/-! ## Exact parent-point generation -/

theorem shifted_parent_value (child : Std.U32) :
    (Std.U32.wrapping_shr child 2#u32).val = child.val / 4 := by
  unfold Std.U32.wrapping_shr UScalar.wrapping_shr
  change (child.bv.ushiftRight (2 % UScalarTy.U32.numBits)).toNat = _
  rw [BitVec.toNat_ushiftRight]
  norm_num [Nat.shiftRight_eq_div_pow]

theorem source_slot_value (child : Std.U32) :
    (child &&& 3#u32).val = child.val % 4 := by
  rw [UScalar.val_and]
  change child.val &&& 3 = child.val % 4
  rw [show 3 = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

def parentTransform (doublings : Std.U8) (expected : C)
    (childIndex : Std.U32) : C :=
  let doubled := expected ^ 2
  let fullyDoubled := if doublings = 2#u8 then doubled ^ 2 else doubled
  removeLineSlotRotation fullyDoubled
    ⟨childIndex.val % 4, Nat.mod_lt _ (by norm_num)⟩

def parentPointCall (input : Coordinate.Point) (childIndex : Std.U32)
    (doublings : Std.U8) : Result Coordinate.Point := do
  let point ←
    V5FriCoordinateAdapter.aspis_core.circle_fri.double_point input
  let point1 ←
    if doublings = 2#u8 then
      V5FriCoordinateAdapter.aspis_core.circle_fri.double_point point
    else ok point
  let slot ← lift (childIndex &&& 3#u32)
  V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation
    point1 slot

/-- The exact sequence in one accepted parent iteration: one mandatory
doubling, the optional second doubling, then slot normalization. -/
theorem parent_point_call_exact
    (input : Coordinate.Point) (expected : C)
    (childIndex : Std.U32) (doublings : Std.U8)
    (hinput : Represents input expected) :
    ∃ output : Coordinate.Point,
      parentPointCall input childIndex doublings = .ok output ∧
      Represents output (parentTransform doublings expected childIndex) := by
  obtain ⟨first, hfirstRun, hfirstRep⟩ :=
    double_point_produces_square input expected hinput
  by_cases htwo : doublings = 2#u8
  · obtain ⟨second, hsecondRun, hsecondRep⟩ :=
      double_point_produces_square first (expected ^ 2) hfirstRep
    have hslotBound : (childIndex &&& 3#u32).val < 4 := by
      rw [source_slot_value]
      exact Nat.mod_lt _ (by norm_num)
    obtain ⟨output, hrotationRun, hrotationRep⟩ :=
      remove_line_slot_rotation_produces second ((expected ^ 2) ^ 2)
        (childIndex &&& 3#u32) hslotBound hsecondRep
    refine ⟨output, ?_, ?_⟩
    · simp [parentPointCall, hfirstRun, htwo, hsecondRun,
        hrotationRun, Std.lift]
    · unfold parentTransform
      simp only [htwo, if_pos]
      have hfin :
          (⟨(childIndex &&& 3#u32).val, hslotBound⟩ : Fin 4) =
            ⟨childIndex.val % 4, Nat.mod_lt _ (by norm_num)⟩ := by
        apply Fin.ext
        exact source_slot_value childIndex
      simpa [hfin] using hrotationRep
  · have hslotBound : (childIndex &&& 3#u32).val < 4 := by
      rw [source_slot_value]
      exact Nat.mod_lt _ (by norm_num)
    obtain ⟨output, hrotationRun, hrotationRep⟩ :=
      remove_line_slot_rotation_produces first (expected ^ 2)
        (childIndex &&& 3#u32) hslotBound hfirstRep
    refine ⟨output, ?_, ?_⟩
    · simp [parentPointCall, hfirstRun, htwo, hrotationRun, Std.lift]
    · unfold parentTransform
      simp only [htwo, if_neg]
      have hfin :
          (⟨(childIndex &&& 3#u32).val, hslotBound⟩ : Fin 4) =
            ⟨childIndex.val % 4, Nat.mod_lt _ (by norm_num)⟩ := by
        apply Fin.ext
        exact source_slot_value childIndex
      simpa [hfin] using hrotationRep

private theorem generated_parentContinuation_eq
    (input : Coordinate.Point) (childIndex : Std.U32)
    (doublings : Std.U8) (parents : Coordinate.PointVec)
    (childOrdinal parentOrdinal : Std.Usize) :
    (do
      let point ←
        V5FriCoordinateAdapter.aspis_core.circle_fri.double_point input
      let point1 ←
        if doublings = 2#u8 then
          V5FriCoordinateAdapter.aspis_core.circle_fri.double_point point
        else ok point
      let slot ← lift (childIndex &&& 3#u32)
      let parentPoint ←
        V5FriCoordinateAdapter.aspis_core.circle_fri.remove_line_slot_rotation
          point1 slot
      let nextParents ← alloc.vec.Vec.push parents parentPoint
      let nextParentOrdinal ←
        lift (Std.Usize.wrapping_add parentOrdinal 1#usize)
      ok (cont (nextParents, childOrdinal, nextParentOrdinal, true) :
        ControlFlow
          (Coordinate.PointVec × Std.Usize × Std.Usize × Bool)
          (Coordinate.PointVec × Bool))) =
      (do
        let parentPoint ← parentPointCall input childIndex doublings
        let nextParents ← alloc.vec.Vec.push parents parentPoint
        let nextParentOrdinal ←
          lift (Std.Usize.wrapping_add parentOrdinal 1#usize)
        ok (cont (nextParents, childOrdinal, nextParentOrdinal, true) :
          ControlFlow
            (Coordinate.PointVec × Std.Usize × Std.Usize × Bool)
            (Coordinate.PointVec × Bool))) := by
  simp [parentPointCall, Std.lift, bind_assoc, result_bind_ite]

private def SearchInvariant (childIndices : Slice Std.U32)
    (ordinal : Std.Usize) : Prop :=
  ordinal.val ≤ childIndices.val.length

def SearchPost (childIndices : Slice Std.U32)
    (ordinal : Std.Usize) : Prop :=
  ordinal.val ≤ childIndices.val.length

/-- The inner scan never escapes the child list.  This is the only property
the outer accepted-path proof needs; the outer source rechecks equality with
the requested parent before using the selected child. -/
theorem parent_search_bounded
    (childIndices : Slice Std.U32) (start : Std.Usize)
    (parent : Std.U32) (hstart : start.val ≤ childIndices.val.length) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0_loop0
        childIndices start parent
      ⦃ output => SearchPost childIndices output ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0_loop0
  apply loop.spec_decr_nat
    (fun ordinal => childIndices.val.length - ordinal.val)
    (SearchInvariant childIndices)
    (SearchPost childIndices)
  · intro ordinal hordinal
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0_loop0.body
    by_cases hactive : ordinal.val < childIndices.val.length
    · have hcondition : ordinal < Slice.len childIndices := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      obtain ⟨child, hchildRun, _hchildValue⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Slice.index_usize_spec childIndices ordinal hactive)
      let shifted := Std.U32.wrapping_shr child 2#u32
      by_cases hless : shifted < parent
      · have hsmall : ordinal.val + 1 < UScalar.size .Usize := by
          have hmax := childIndices.property
          have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
            simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
          rw [hsize]
          omega
        let next := Std.Usize.wrapping_add ordinal 1#usize
        have hnext : next.val = ordinal.val + 1 := by
          unfold next
          exact wrapping_add_one_exact ordinal hsmall
        simp only [if_pos hcondition]
        rw [hchildRun]
        simp only [Std.lift, bind_tc_ok, if_pos hless, WP.spec_ok]
        change SearchInvariant childIndices next ∧
          childIndices.val.length - next.val <
            childIndices.val.length - ordinal.val
        exact ⟨by unfold SearchInvariant; rw [hnext]; omega,
          by rw [hnext]; omega⟩
      · simp only [if_pos hcondition]
        rw [hchildRun]
        simp only [Std.lift, bind_tc_ok, if_neg hless, WP.spec_ok]
        exact hordinal
    · have hdone : ordinal.val = childIndices.val.length := by omega
      have hcondition : ¬ ordinal < Slice.len childIndices := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      unfold SearchPost
      omega
  · exact hstart

def ParentWitness (childIndices : Slice Std.U32)
    (childExpected : Nat → C) (doublings : Std.U8)
    (parentIndex : Std.U32) (point : Coordinate.Point) : Prop :=
  ∃ childOrdinal : Nat,
    childOrdinal < childIndices.val.length ∧
    childIndices.val[childOrdinal]!.val / 4 = parentIndex.val ∧
    Represents point
      (parentTransform doublings (childExpected childOrdinal)
        childIndices.val[childOrdinal]!)

def ParentPointsPost (childIndices parentIndices : Slice Std.U32)
    (childExpected : Nat → C) (doublings : Std.U8)
    (output : Coordinate.PointVec × Bool) : Prop :=
  output.2 = true →
    output.1.val.length = parentIndices.val.length ∧
    ∀ (parentOrdinal : Nat)
      (hparent : parentOrdinal < parentIndices.val.length),
      ParentWitness childIndices childExpected doublings
        parentIndices.val[parentOrdinal]! output.1.val[parentOrdinal]!

private def ParentPointsInvariant
    (childIndices childPoints parentIndices : Slice Std.U32)
    (childExpected : Nat → C) (doublings : Std.U8) :
    (Coordinate.PointVec × Std.Usize × Std.Usize × Bool) → Prop
  | (parents, childOrdinal, parentOrdinal, valid) =>
      childOrdinal.val ≤ childIndices.val.length ∧
      parentOrdinal.val ≤ parentIndices.val.length ∧
      parents.val.length = parentOrdinal.val ∧
      (∀ (ordinal : Nat) (hordinal : ordinal < parentOrdinal.val),
        ParentWitness childIndices childExpected doublings
          parentIndices.val[ordinal]! parents.val[ordinal]!) ∧
      (valid = true → childPoints.val.length = childIndices.val.length)

private def ParentPointsMeasure (parentIndices : Slice Std.U32) :
    Coordinate.PointVec × Std.Usize × Std.Usize × Bool → Nat
  | (_, _, parentOrdinal, valid) =>
      2 * (parentIndices.val.length - parentOrdinal.val) +
        if valid then 1 else 0

/-- The translated outer parent loop has exact accepted semantics.  If it
returns `true`, every requested parent has exactly one output, in caller
order, authenticated by a child whose source index maps to that parent. -/
theorem parent_points_loop_exact
    (childIndices : Slice Std.U32) (childPoints : Slice Coordinate.Point)
    (parentIndices : Slice Std.U32) (doublings : Std.U8)
    (parents : Coordinate.PointVec) (initialValid : Bool)
    (childExpected : Nat → C)
    (hparents : parents.val = [])
    (hinitialValid : initialValid = true →
      childPoints.val.length = childIndices.val.length)
    (hchildren : ∀ (ordinal : Nat)
      (hordinal : ordinal < childPoints.val.length),
      Represents childPoints.val[ordinal]! (childExpected ordinal)) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0
        childIndices childPoints parentIndices doublings parents
          0#usize 0#usize initialValid
      ⦃ output => ParentPointsPost childIndices parentIndices
        childExpected doublings output ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0
  apply loop.spec_decr_nat
    (ParentPointsMeasure parentIndices)
    (ParentPointsInvariant childIndices childPoints parentIndices
      childExpected doublings)
    (ParentPointsPost childIndices parentIndices childExpected doublings)
  · rintro ⟨currentParents, childOrdinal, parentOrdinal, currentValid⟩
      hstate
    rcases hstate with
      ⟨hchildOrdinal, hparentOrdinal, hparentsLength, hparentWitness,
        hvalidLengths⟩
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0.body
    by_cases hparentActive : parentOrdinal.val < parentIndices.val.length
    · have hparentCondition : parentOrdinal < Slice.len parentIndices := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hparentActive
      by_cases hvalid : currentValid = true
      · have hlengths := hvalidLengths hvalid
        obtain ⟨parent, hparentRun, hparentValue⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (Slice.index_usize_spec parentIndices parentOrdinal hparentActive)
        obtain ⟨selectedChild, hsearchRun, hsearchBound⟩ :=
          Aeneas.Std.WP.spec_imp_exists
            (parent_search_bounded childIndices childOrdinal parent
              hchildOrdinal)
        by_cases hmissing : selectedChild ≥ Slice.len childIndices
        · simp only [if_pos hparentCondition, if_pos hvalid]
          rw [hparentRun, hsearchRun]
          simp only [bind_tc_ok, if_pos hmissing, WP.spec_ok]
          change
            ParentPointsInvariant childIndices childPoints parentIndices
                childExpected doublings
                (currentParents, selectedChild, parentOrdinal, false) ∧
              ParentPointsMeasure parentIndices
                  (currentParents, selectedChild, parentOrdinal, false) <
                ParentPointsMeasure parentIndices
                  (currentParents, childOrdinal, parentOrdinal, currentValid)
          refine ⟨⟨hsearchBound, hparentOrdinal, hparentsLength,
            hparentWitness, by simp⟩, ?_⟩
          unfold ParentPointsMeasure
          simp [hvalid]
        · have hchildActive :
            selectedChild.val < childIndices.val.length := by
            scalar_tac
          obtain ⟨childIndex, hchildIndexRun, hchildIndexValue⟩ :=
            Aeneas.Std.WP.spec_imp_exists
              (Slice.index_usize_spec childIndices selectedChild hchildActive)
          let shifted := Std.U32.wrapping_shr childIndex 2#u32
          by_cases hmatched : shifted = parent
          · have hchildPointActive :
                selectedChild.val < childPoints.val.length := by
                omega
            obtain ⟨childPoint, hchildPointRun, hchildPointValue⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (Slice.index_usize_spec childPoints selectedChild
                  hchildPointActive)
            have hchildBang :
                childPoints.val[selectedChild.val]! = childPoint := by
              rw [getElemBang_eq_getElem _ _ hchildPointActive]
              exact hchildPointValue.symm
            have hinputRep :
                Represents childPoint (childExpected selectedChild.val) := by
              rw [← hchildBang]
              exact hchildren selectedChild.val hchildPointActive
            obtain ⟨parentPoint, hpointRun, hpointRep⟩ :=
              parent_point_call_exact childPoint
                (childExpected selectedChild.val) childIndex doublings
                hinputRep
            have hcapacity :
                currentParents.val.length < Std.Usize.max := by
              have hmax := parentIndices.property
              omega
            obtain ⟨nextParents, hpushRun, hnextParents⟩ :=
              Aeneas.Std.WP.spec_imp_exists
                (alloc.vec.Vec.push_spec currentParents parentPoint hcapacity)
            have hordinalSmall :
                parentOrdinal.val + 1 < UScalar.size .Usize := by
              have hmax := parentIndices.property
              have hsize : UScalar.size .Usize = Std.Usize.max + 1 := by
                simp [Std.Usize.size, Std.Usize.max, Std.Usize.numBits]
              rw [hsize]
              omega
            let nextParentOrdinal :=
              Std.Usize.wrapping_add parentOrdinal 1#usize
            have hnextParentOrdinal :
                nextParentOrdinal.val = parentOrdinal.val + 1 := by
              unfold nextParentOrdinal
              exact wrapping_add_one_exact parentOrdinal hordinalSmall
            simp only [if_pos hparentCondition, if_pos hvalid]
            rw [hparentRun, hsearchRun]
            simp only [bind_tc_ok, if_neg hmissing]
            rw [hchildIndexRun]
            simp only [Std.lift, bind_tc_ok]
            simp only [hmatched, bne_self, Bool.false_eq_true, if_false]
            rw [hchildPointRun]
            simp only [bind_tc_ok]
            rw [generated_parentContinuation_eq childPoint childIndex
                doublings currentParents selectedChild parentOrdinal,
              hpointRun, hpushRun]
            simp only [bind_tc_ok, WP.spec_ok]
            change
              ParentPointsInvariant childIndices childPoints parentIndices
                  childExpected doublings
                  (nextParents, selectedChild, nextParentOrdinal, true) ∧
                ParentPointsMeasure parentIndices
                    (nextParents, selectedChild, nextParentOrdinal, true) <
                  ParentPointsMeasure parentIndices
                    (currentParents, childOrdinal, parentOrdinal, currentValid)
            refine ⟨?_, ?_⟩
            · refine ⟨hsearchBound, by rw [hnextParentOrdinal]; omega,
                ?_, ?_, by simpa using hlengths⟩
              · rw [hnextParents, List.length_append, hparentsLength,
                  hnextParentOrdinal]
                simp
              · intro ordinal hordinal
                rw [hnextParentOrdinal] at hordinal
                by_cases hprior : ordinal < parentOrdinal.val
                · have hleft : ordinal < currentParents.val.length := by
                    simpa [hparentsLength] using hprior
                  have happendBang :
                      (currentParents.val ++ [parentPoint])[ordinal]! =
                        currentParents.val[ordinal]! := by
                    rw [getElemBang_eq_getElem _ _
                        (by simp only [List.length_append,
                            List.length_singleton]; omega),
                      getElemBang_eq_getElem _ _ hleft,
                      List.getElem_append_left hleft]
                  rw [hnextParents, happendBang]
                  exact hparentWitness ordinal hprior
                · have hlast : ordinal = parentOrdinal.val := by omega
                  subst ordinal
                  have happendBang :
                      (currentParents.val ++ [parentPoint])
                          [parentOrdinal.val]! = parentPoint := by
                    rw [getElemBang_eq_getElem _ _
                        (by simp [hparentsLength])]
                    simp [hparentsLength]
                  have hparentBang :
                      parentIndices.val[parentOrdinal.val]! = parent := by
                    rw [getElemBang_eq_getElem _ _ hparentActive]
                    exact hparentValue.symm
                  have hchildIndexBang :
                      childIndices.val[selectedChild.val]! = childIndex := by
                    rw [getElemBang_eq_getElem _ _ hchildActive]
                    exact hchildIndexValue.symm
                  rw [hnextParents, happendBang, hparentBang]
                  refine ⟨selectedChild.val, hchildActive, ?_, ?_⟩
                  · rw [hchildIndexBang]
                    have hvalues := congrArg UScalar.val hmatched
                    simpa [shifted, shifted_parent_value] using hvalues
                  · rw [hchildIndexBang]
                    exact hpointRep
            · unfold ParentPointsMeasure
              rw [hnextParentOrdinal]
              simp [hvalid]
              omega
          · have hmismatch : shifted != parent = true := by
              simp [hmatched]
            simp only [if_pos hparentCondition, if_pos hvalid]
            rw [hparentRun, hsearchRun]
            simp only [bind_tc_ok, if_neg hmissing]
            rw [hchildIndexRun]
            simp only [Std.lift, bind_tc_ok, if_pos hmismatch, WP.spec_ok]
            change
              ParentPointsInvariant childIndices childPoints parentIndices
                  childExpected doublings
                  (currentParents, selectedChild, parentOrdinal, false) ∧
                ParentPointsMeasure parentIndices
                    (currentParents, selectedChild, parentOrdinal, false) <
                  ParentPointsMeasure parentIndices
                    (currentParents, childOrdinal, parentOrdinal, currentValid)
            refine ⟨⟨hsearchBound, hparentOrdinal, hparentsLength,
              hparentWitness, by simp⟩, ?_⟩
            unfold ParentPointsMeasure
            simp [hvalid]
      · have hcondition : ¬ currentValid = true := hvalid
        simp only [if_pos hparentCondition, if_neg hcondition, WP.spec_ok]
        unfold ParentPointsPost
        simp
    · have hparentDone :
          parentOrdinal.val = parentIndices.val.length := by omega
      have hparentCondition : ¬ parentOrdinal < Slice.len parentIndices := by
        simpa [UScalar.lt_equiv, Slice.len_val] using hparentActive
      simp only [if_neg hparentCondition, WP.spec_ok]
      unfold ParentPointsPost
      intro hvalid
      refine ⟨by rw [hparentsLength, hparentDone], ?_⟩
      intro ordinal hordinal
      rw [← hparentDone] at hordinal
      exact hparentWitness ordinal hordinal
  · unfold ParentPointsInvariant
    simp only
    refine ⟨by simp, by simp, by simp [hparents], by simp, ?_⟩
    exact hinitialValid

/-- Exact accepted semantics of the translated public parent helper. -/
theorem derive_parent_line_points_success
    (childIndices : Slice Std.U32) (childPoints : Slice Coordinate.Point)
    (parentIndices : Slice Std.U32) (doublings : Std.U8)
    (childExpected : Nat → C) (output : Coordinate.PointVec)
    (hchildren : ∀ (ordinal : Nat)
      (hordinal : ordinal < childPoints.val.length),
      Represents childPoints.val[ordinal]! (childExpected ordinal))
    (hrun :
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
          childIndices childPoints parentIndices doublings =
        .ok (output, true)) :
    output.val.length = parentIndices.val.length ∧
      ∀ (parentOrdinal : Nat)
        (hparent : parentOrdinal < parentIndices.val.length),
        ParentWitness childIndices childExpected doublings
          parentIndices.val[parentOrdinal]! output.val[parentOrdinal]! := by
  let initial : Coordinate.PointVec :=
    alloc.vec.Vec.with_capacity Coordinate.Point (Slice.len parentIndices)
  let initialValid : Bool :=
    Slice.len childIndices = Slice.len childPoints
  have hinitial : initial.val = [] := by rfl
  have hinitialValid : initialValid = true →
      childPoints.val.length = childIndices.val.length := by
    intro hvalid
    have hlengths : Slice.len childIndices = Slice.len childPoints := by
      simpa [initialValid] using hvalid
    have hvalues := congrArg UScalar.val hlengths
    simpa [Slice.len_val] using hvalues.symm
  obtain ⟨built, hbuiltRun, hbuiltPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (parent_points_loop_exact childIndices childPoints parentIndices
        doublings initial initialValid childExpected hinitial hinitialValid
        hchildren)
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points
    at hrun
  change
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_parent_line_points_loop0
        childIndices childPoints parentIndices doublings initial
          0#usize 0#usize initialValid = .ok (output, true)
    at hrun
  rw [hbuiltRun] at hrun
  have heq : built = (output, true) := Result.ok.inj hrun
  rw [heq] at hbuiltPost
  exact hbuiltPost rfl

#print axioms selected_circle_fiber_points_shared_success
#print axioms derive_parent_line_points_success

end AspisV5FriCoordinatePointLoops
