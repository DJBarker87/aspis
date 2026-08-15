import V5RowExpand.Funs
import V5RowAccess.Funs
import V5RowCallSite.Funs
import QM31MulProof
import AspisFormal.V5ProductionRowSelector

/-!
# Extracted Rust row-selector proof

This file connects the Charon/Aeneas output for the production selector-table
builder and row lookup to the exact row-selector formula proved in
`AspisFormal.V5ProductionRowSelector`.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RowSelectorImplementationProof

namespace Expand

open V5RowExpandGenerated
open AspisAeneasQM31Mul

abbrev RustM31 := V5RowExpandGenerated.aspis_core.field.M31
abbrev RustCM31 := V5RowExpandGenerated.aspis_core.field.CM31
abbrev RustQM31 := V5RowExpandGenerated.aspis_core.field.QM31
abbrev RustPrepared :=
  V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev ExactQM31 := AspisAeneasQM31Mul.QM31Exact

def toReferenceCM31 (value : RustCM31) :
    AspisCoreCM31Multiplicative.field.CM31 :=
  { a := value.a, b := value.b }

def toReferenceQM31 (value : RustQM31) :
    AspisCoreCM31Multiplicative.field.QM31 :=
  { c0 := toReferenceCM31 value.c0, c1 := toReferenceCM31 value.c1 }

def fromReferenceCM31 (value : AspisCoreCM31Multiplicative.field.CM31) :
    RustCM31 :=
  { a := value.a, b := value.b }

def fromReferenceQM31 (value : AspisCoreCM31Multiplicative.field.QM31) :
    RustQM31 :=
  { c0 := fromReferenceCM31 value.c0,
    c1 := fromReferenceCM31 value.c1 }

def toReferencePrepared (value : RustPrepared) :
    AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier :=
  { components := value.components }

def fromReferencePrepared
    (value : AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier) :
    RustPrepared :=
  { components := value.components }

def ValidQM31 (value : RustQM31) : Prop :=
  AspisAeneasQM31Mul.CanonicalQM31 (toReferenceQM31 value)

def ValidM31 (value : RustM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val

def ValidCM31 (value : RustCM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalCM31
    (toReferenceCM31 value)

def cm31ToExact (value : RustCM31) :
    AspisAeneasQM31Mul.CM31Exact :=
  AspisAeneasQM31Mul.cm31ToExact (toReferenceCM31 value)

def toExact (value : RustQM31) : ExactQM31 :=
  AspisAeneasQM31Mul.qm31ToExact (toReferenceQM31 value)

@[simp] theorem toReferenceCM31_fromReferenceCM31
    (value : AspisCoreCM31Multiplicative.field.CM31) :
    toReferenceCM31 (fromReferenceCM31 value) = value := by
  cases value
  rfl

@[simp] theorem toReferenceQM31_fromReferenceQM31
    (value : AspisCoreCM31Multiplicative.field.QM31) :
    toReferenceQM31 (fromReferenceQM31 value) = value := by
  cases value
  rfl

@[simp] theorem fromReferenceQM31_toReferenceQM31 (value : RustQM31) :
    fromReferenceQM31 (toReferenceQM31 value) = value := by
  cases value
  rfl

@[simp] theorem toReferencePrepared_fromReferencePrepared
    (value : AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier) :
    toReferencePrepared (fromReferencePrepared value) = value := by
  cases value
  rfl

theorem m31_add_call_eq_reference (left right : RustM31) :
    V5RowExpandGenerated.aspis_core.field.M31.add left right =
      AspisCoreCM31Multiplicative.field.M31.add left right := by
  unfold V5RowExpandGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [V5RowExpandGenerated.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.P]

theorem m31_sub_call_eq_reference (left right : RustM31) :
    V5RowExpandGenerated.aspis_core.field.M31.sub left right =
      AspisCoreCM31Multiplicative.field.M31.sub left right := by
  unfold V5RowExpandGenerated.aspis_core.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [V5RowExpandGenerated.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.P]

theorem m31_mul_call_eq_reference (left right : RustM31) :
    V5RowExpandGenerated.aspis_core.field.M31.mul left right =
      AspisCoreCM31Multiplicative.field.M31.mul left right := by
  unfold V5RowExpandGenerated.aspis_core.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
    V5RowExpandGenerated.aspis_core.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [V5RowExpandGenerated.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.P]

theorem cm31_add_corresponds (left right : RustCM31)
    (hleft : ValidCM31 left) (hright : ValidCM31 right) :
    ∃ output : RustCM31,
      V5RowExpandGenerated.aspis_core.field.CM31.add left right = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output = cm31ToExact left + cm31ToExact right := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hvalidA, hexactA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hvalidB, hexactB⟩
  let output : RustCM31 := { a := oa, b := ob }
  refine ⟨output, ?_, ⟨hvalidA, hvalidB⟩, ?_⟩
  · simp [V5RowExpandGenerated.aspis_core.field.CM31.add,
      m31_add_call_eq_reference, hcallA, hcallB, output]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem cm31_sub_corresponds (left right : RustCM31)
    (hleft : ValidCM31 left) (hright : ValidCM31 right) :
    ∃ output : RustCM31,
      V5RowExpandGenerated.aspis_core.field.CM31.sub left right = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output = cm31ToExact left - cm31ToExact right := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hvalidA, hexactA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hvalidB, hexactB⟩
  let output : RustCM31 := { a := oa, b := ob }
  refine ⟨output, ?_, ⟨hvalidA, hvalidB⟩, ?_⟩
  · simp [V5RowExpandGenerated.aspis_core.field.CM31.sub,
      m31_sub_call_eq_reference, hcallA, hcallB, output]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem mul_by_r_corresponds (value : RustCM31)
    (hvalue : ValidCM31 value) :
    ∃ output : RustCM31,
      V5RowExpandGenerated.aspis_core.field.mul_by_r value = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output =
        cm31ToExact value * AspisAeneasQM31Mul.qm31R := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_double_corresponds
      value.a hvalue.1 with
    ⟨twiceA, htwiceA, hvalidTwiceA, hexactTwiceA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      twiceA value.b hvalidTwiceA hvalue.2 with
    ⟨real, hreal, hvalidReal, hexactReal⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_double_corresponds
      value.b hvalue.2 with
    ⟨twiceB, htwiceB, hvalidTwiceB, hexactTwiceB⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      value.a twiceB hvalue.1 hvalidTwiceB with
    ⟨imag, himag, hvalidImag, hexactImag⟩
  let output : RustCM31 := { a := real, b := imag }
  refine ⟨output, ?_, ⟨hvalidReal, hvalidImag⟩, ?_⟩
  · have htwiceA' :
        V5RowExpandGenerated.aspis_core.field.M31.double value.a =
          .ok twiceA := by
      simpa [V5RowExpandGenerated.aspis_core.field.M31.double,
        AspisCoreCM31Multiplicative.field.M31.double,
        m31_add_call_eq_reference] using htwiceA
    have hreal' :
        V5RowExpandGenerated.aspis_core.field.M31.sub twiceA value.b =
          .ok real := by
      simpa [m31_sub_call_eq_reference] using hreal
    have htwiceB' :
        V5RowExpandGenerated.aspis_core.field.M31.double value.b =
          .ok twiceB := by
      simpa [V5RowExpandGenerated.aspis_core.field.M31.double,
        AspisCoreCM31Multiplicative.field.M31.double,
        m31_add_call_eq_reference] using htwiceB
    have himag' :
        V5RowExpandGenerated.aspis_core.field.M31.add value.a twiceB =
          .ok imag := by
      simpa [m31_add_call_eq_reference] using himag
    simp [V5RowExpandGenerated.aspis_core.field.mul_by_r,
      htwiceA', hreal', htwiceB', himag', output]
  · apply QuadraticAlgebra.ext
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        QuadraticAlgebra.re_mul, AspisAeneasQM31Mul.qm31R]
      simp only [output, toReferenceCM31]
      rw [hexactReal, hexactTwiceA]
      ring
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        QuadraticAlgebra.im_mul, AspisAeneasQM31Mul.qm31R]
      simp only [output, toReferenceCM31]
      rw [hexactImag, hexactTwiceB]
      ring

theorem qm31_sub_corresponds (left right : RustQM31)
    (hleft : ValidQM31 left) (hright : ValidQM31 right) :
    ∃ output : RustQM31,
      V5RowExpandGenerated.aspis_core.field.QM31.sub left right = .ok output ∧
      ValidQM31 output ∧
      toExact output = toExact left - toExact right := by
  rcases cm31_sub_corresponds left.c0 right.c0 hleft.1 hright.1 with
    ⟨out0, hcall0, hvalid0, hexact0⟩
  rcases cm31_sub_corresponds left.c1 right.c1 hleft.2 hright.2 with
    ⟨out1, hcall1, hvalid1, hexact1⟩
  let output : RustQM31 := { c0 := out0, c1 := out1 }
  refine ⟨output, ?_, ⟨hvalid0, hvalid1⟩, ?_⟩
  · simp [V5RowExpandGenerated.aspis_core.field.QM31.sub,
      hcall0, hcall1, output]
  · apply QuadraticAlgebra.ext
    · exact hexact0
    · exact hexact1

def preparedRow (a b sum : RustM31) : Array RustM31 3#usize :=
  Array.make 3#usize [a, b, sum]

def RepresentsCM31Row (row : Array RustM31 3#usize)
    (value : RustCM31) : Prop :=
  ∃ sum : RustM31,
    V5RowExpandGenerated.aspis_core.field.M31.add value.a value.b = .ok sum ∧
    ValidM31 sum ∧
    ((sum.val : Nat) : AspisAeneasQM31Mul.M31Exact) =
      (value.a.val : AspisAeneasQM31Mul.M31Exact) +
        (value.b.val : AspisAeneasQM31Mul.M31Exact) ∧
    row.val = [value.a, value.b, sum]

def RepresentsPrepared (prepared : RustPrepared) (left : RustQM31) : Prop :=
  ∃ leftSum : RustCM31,
  ∃ row0 row1 row2 : Array RustM31 3#usize,
    V5RowExpandGenerated.aspis_core.field.CM31.add left.c0 left.c1 =
      .ok leftSum ∧
    ValidCM31 leftSum ∧
    cm31ToExact leftSum = cm31ToExact left.c0 + cm31ToExact left.c1 ∧
    RepresentsCM31Row row0 left.c0 ∧
    RepresentsCM31Row row1 left.c1 ∧
    RepresentsCM31Row row2 leftSum ∧
    prepared.components.val = [row0, row1, row2]

private theorem index_zero_of_val {α : Type*}
    (values : Array α 3#usize) (x0 x1 x2 : α)
    (hvalues : values.val = [x0, x1, x2]) :
    Array.index_usize values 0#usize = .ok x0 := by
  simp [Array.index_usize, hvalues]

private theorem index_one_of_val {α : Type*}
    (values : Array α 3#usize) (x0 x1 x2 : α)
    (hvalues : values.val = [x0, x1, x2]) :
    Array.index_usize values 1#usize = .ok x1 := by
  simp [Array.index_usize, hvalues]

private theorem index_two_of_val {α : Type*}
    (values : Array α 3#usize) (x0 x1 x2 : α)
    (hvalues : values.val = [x0, x1, x2]) :
    Array.index_usize values 2#usize = .ok x2 := by
  simp [Array.index_usize, hvalues]

private theorem prepare_closure_establishes_row
    (value : RustCM31) (hvalue : ValidCM31 value) :
    ∃ row : Array RustM31 3#usize,
      V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
          () value = .ok row ∧
      RepresentsCM31Row row value := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      value.a value.b hvalue.1 hvalue.2 with
    ⟨sum, hsumReference, hsumValid, hsumExact⟩
  have hsum : V5RowExpandGenerated.aspis_core.field.M31.add
      value.a value.b = .ok sum := by
    simpa [m31_add_call_eq_reference] using hsumReference
  let row : Array RustM31 3#usize := preparedRow value.a value.b sum
  refine ⟨row, ?_, ⟨sum, hsum, hsumValid, hsumExact, ?_⟩⟩
  · simp [V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
      hsum, preparedRow, row]
  · rfl

theorem prepared_new_establishes (left : RustQM31)
    (hleft : ValidQM31 left) :
    ∃ prepared : RustPrepared,
      V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.new left =
        .ok prepared ∧
      RepresentsPrepared prepared left := by
  rcases prepare_closure_establishes_row left.c0 hleft.1 with
    ⟨row0, hrow0Call, hrow0⟩
  rcases prepare_closure_establishes_row left.c1 hleft.2 with
    ⟨row1, hrow1Call, hrow1⟩
  rcases cm31_add_corresponds left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSumCall, hleftSumValid, hleftSumExact⟩
  rcases prepare_closure_establishes_row leftSum hleftSumValid with
    ⟨row2, hrow2Call, hrow2⟩
  let prepared : RustPrepared := {
    components := Array.make 3#usize [row0, row1, row2]
  }
  refine ⟨prepared, ?_, ?_⟩
  · simp [V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.new,
      hrow0Call, hrow1Call, hleftSumCall, hrow2Call, prepared]
  · exact ⟨leftSum, row0, row1, row2,
      hleftSumCall, hleftSumValid, hleftSumExact,
      hrow0, hrow1, hrow2, rfl⟩

private theorem prepared_row_mul_corresponds
    (row : Array RustM31 3#usize) (left right : RustCM31)
    (hrow : RepresentsCM31Row row left)
    (hleft : ValidCM31 left) (hright : ValidCM31 right) :
    ∃ output : RustCM31,
      V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
          () (row, right) = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output = cm31ToExact left * cm31ToExact right := by
  rcases hrow with ⟨leftSum, hleftSumCall, hleftSumValid,
    hleftSumExact, hrowValues⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      left.a right.a hleft.1 hright.1 with
    ⟨m0, hm0Reference, hm0Valid, hm0Exact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      left.b right.b hleft.2 hright.2 with
    ⟨m1, hm1Reference, hm1Valid, hm1Exact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      right.a right.b hright.1 hright.2 with
    ⟨rightSum, hrightSumReference, hrightSumValid, hrightSumExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      leftSum rightSum hleftSumValid hrightSumValid with
    ⟨m2, hm2Reference, hm2Valid, hm2Exact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      m0 m1 hm0Valid hm1Valid with
    ⟨real, hrealReference, hrealValid, hrealExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      m2 m0 hm2Valid hm0Valid with
    ⟨imagPartial, himagPartialReference,
      himagPartialValid, himagPartialExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      imagPartial m1 himagPartialValid hm1Valid with
    ⟨imag, himagReference, himagValid, himagExact⟩
  have hm0 : V5RowExpandGenerated.aspis_core.field.M31.mul
      left.a right.a = .ok m0 := by
    simpa [m31_mul_call_eq_reference] using hm0Reference
  have hm1 : V5RowExpandGenerated.aspis_core.field.M31.mul
      left.b right.b = .ok m1 := by
    simpa [m31_mul_call_eq_reference] using hm1Reference
  have hrightSum : V5RowExpandGenerated.aspis_core.field.M31.add
      right.a right.b = .ok rightSum := by
    simpa [m31_add_call_eq_reference] using hrightSumReference
  have hm2 : V5RowExpandGenerated.aspis_core.field.M31.mul
      leftSum rightSum = .ok m2 := by
    simpa [m31_mul_call_eq_reference] using hm2Reference
  have hreal : V5RowExpandGenerated.aspis_core.field.M31.sub
      m0 m1 = .ok real := by
    simpa [m31_sub_call_eq_reference] using hrealReference
  have himagPartial : V5RowExpandGenerated.aspis_core.field.M31.sub
      m2 m0 = .ok imagPartial := by
    simpa [m31_sub_call_eq_reference] using himagPartialReference
  have himag : V5RowExpandGenerated.aspis_core.field.M31.sub
      imagPartial m1 = .ok imag := by
    simpa [m31_sub_call_eq_reference] using himagReference
  let output : RustCM31 := { a := real, b := imag }
  refine ⟨output, ?_, ⟨hrealValid, himagValid⟩, ?_⟩
  · simp [V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
      Array.index_usize, hrowValues,
      hm0, hm1, hrightSum, hm2, hreal, himagPartial, himag,
      output]
  · apply QuadraticAlgebra.ext
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        output, toReferenceCM31, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        output, toReferenceCM31, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

theorem prepared_mul_corresponds
    (prepared : RustPrepared) (left right : RustQM31)
    (hprepared : RepresentsPrepared prepared left)
    (hleft : ValidQM31 left) (hright : ValidQM31 right) :
    ∃ output : RustQM31,
      V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.mul
          prepared right = .ok output ∧
      ValidQM31 output ∧
      toExact output = toExact left * toExact right := by
  rcases hprepared with
    ⟨leftSum, row0, row1, row2,
      hleftSumCall, hleftSumValid, hleftSumExact,
      hrow0, hrow1, hrow2, hcomponents⟩
  rcases prepared_row_mul_corresponds row0 left.c0 right.c0
      hrow0 hleft.1 hright.1 with
    ⟨m0, hm0, hm0Valid, hm0Exact⟩
  rcases prepared_row_mul_corresponds row1 left.c1 right.c1
      hrow1 hleft.2 hright.2 with
    ⟨m1, hm1, hm1Valid, hm1Exact⟩
  rcases cm31_add_corresponds right.c0 right.c1 hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumValid, hrightSumExact⟩
  rcases prepared_row_mul_corresponds row2 leftSum rightSum
      hrow2 hleftSumValid hrightSumValid with
    ⟨m2, hm2, hm2Valid, hm2Exact⟩
  rcases mul_by_r_corresponds m1 hm1Valid with
    ⟨rM1, hrM1, hrM1Valid, hrM1Exact⟩
  rcases cm31_add_corresponds m0 rM1 hm0Valid hrM1Valid with
    ⟨low, hlow, hlowValid, hlowExact⟩
  rcases cm31_sub_corresponds m2 m0 hm2Valid hm0Valid with
    ⟨highPartial, hhighPartial, hhighPartialValid, hhighPartialExact⟩
  rcases cm31_sub_corresponds highPartial m1
      hhighPartialValid hm1Valid with
    ⟨high, hhigh, hhighValid, hhighExact⟩
  have hcomponent0 := index_zero_of_val
    prepared.components row0 row1 row2 hcomponents
  have hcomponent1 := index_one_of_val
    prepared.components row0 row1 row2 hcomponents
  have hcomponent2 := index_two_of_val
    prepared.components row0 row1 row2 hcomponents
  have hlowTower : cm31ToExact low =
      cm31ToExact left.c0 * cm31ToExact right.c0 +
        AspisAeneasQM31Mul.qm31R *
          (cm31ToExact left.c1 * cm31ToExact right.c1) := by
    rw [hlowExact, hm0Exact, hrM1Exact, hm1Exact]
    ring
  have hhighTower : cm31ToExact high =
      cm31ToExact left.c0 * cm31ToExact right.c1 +
        cm31ToExact left.c1 * cm31ToExact right.c0 := by
    calc
      cm31ToExact high = cm31ToExact highPartial - cm31ToExact m1 :=
        hhighExact
      _ = (cm31ToExact m2 - cm31ToExact m0) - cm31ToExact m1 := by
        rw [hhighPartialExact]
      _ = ((cm31ToExact left.c0 + cm31ToExact left.c1) *
            (cm31ToExact right.c0 + cm31ToExact right.c1) -
            cm31ToExact left.c0 * cm31ToExact right.c0) -
            cm31ToExact left.c1 * cm31ToExact right.c1 := by
        rw [hm2Exact, hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      _ = cm31ToExact left.c0 * cm31ToExact right.c1 +
            cm31ToExact left.c1 * cm31ToExact right.c0 := by ring
  let output : RustQM31 := { c0 := low, c1 := high }
  refine ⟨output, ?_, ⟨hlowValid, hhighValid⟩, ?_⟩
  · simp [V5RowExpandGenerated.aspis_core.field.PreparedQm31Multiplier.mul,
      hcomponent0, hcomponent1, hcomponent2,
      hm0, hm1, hrightSum, hm2, hrM1, hlow,
      hhighPartial, hhigh, output]
  · apply QuadraticAlgebra.ext
    · change cm31ToExact low =
        cm31ToExact left.c0 * cm31ToExact right.c0 +
          AspisAeneasQM31Mul.qm31R * cm31ToExact left.c1 *
            cm31ToExact right.c1
      rw [hlowTower]
      ring
    · simpa [toExact, cm31ToExact, AspisAeneasQM31Mul.qm31ToExact,
        toReferenceQM31, output] using hhighTower

abbrev ReverseUsizeRange :=
  core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)

def reverseRange (upper : Std.Usize) : ReverseUsizeRange :=
  ⟨{ start := 0#usize, «end» := upper }⟩

theorem reverseRange_next_positive (upper : Std.Usize)
    (hpositive : 0 < upper.val) :
    ∃ previous : Std.Usize,
      previous.val = upper.val - 1 ∧
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize)
          (reverseRange upper) =
        .ok (some previous, reverseRange previous) := by
  let previous : Std.Usize :=
    Std.Usize.ofNatCore (upper.val - 1) (by scalar_tac)
  refine ⟨previous, by simp [previous], ?_⟩
  simp [reverseRange,
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,
    core.cmp.impls.PartialOrdUsize.lt, hpositive,
    show 1 ≤ upper.val by omega, previous]
  apply UScalar.eq_of_val_eq
  simp

theorem reverseRange_next_zero :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize)
        (reverseRange 0#usize) =
      .ok (none, reverseRange 0#usize) := by
  simp [reverseRange,
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt]

def weightEntry {N : Std.Usize} (weights : Array RustQM31 N)
    (index : Fin N.val) : RustQM31 :=
  weights.val[index.val]'(by rw [weights.property]; exact index.isLt)

def weightsToExact {N : Std.Usize} (weights : Array RustQM31 N)
    (index : Fin N.val) : ExactQM31 :=
  toExact (weightEntry weights index)

def ValidWeights {N : Std.Usize} (weights : Array RustQM31 N) : Prop :=
  ∀ index : Fin N.val, ValidQM31 (weightEntry weights index)

@[simp] theorem weightEntry_set_same {N : Std.Usize}
    (weights : Array RustQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : RustQM31) :
    weightEntry (weights.set index value) ⟨index.val, hindex⟩ = value := by
  unfold weightEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [weights.property]
    exact hindex)

@[simp] theorem weightEntry_set_other {N : Std.Usize}
    (weights : Array RustQM31 N) (index : Std.Usize)
    (value : RustQM31) (output : Fin N.val)
    (hne : index.val ≠ output.val) :
    weightEntry (weights.set index value) output =
      weightEntry weights output := by
  unfold weightEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [weights.property]
    exact output.isLt)

theorem valid_weights_set {N : Std.Usize}
    (weights : Array RustQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : RustQM31)
    (hweights : ValidWeights weights) (hvalue : ValidQM31 value) :
    ValidWeights (weights.set index value) := by
  intro output
  by_cases heq : index.val = output.val
  · have hout : output = ⟨index.val, hindex⟩ := Fin.ext heq.symm
    subst output
    simpa using hvalue
  · rw [weightEntry_set_other weights index value output heq]
    exact hweights output

theorem weight_index_call {N : Std.Usize}
    (weights : Array RustQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) :
    Array.index_usize weights index =
      .ok (weightEntry weights ⟨index.val, hindex⟩) := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [weights.property]; exact hindex)]
  rfl

theorem weight_update_call {N : Std.Usize}
    (weights : Array RustQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) (value : RustQM31) :
    Array.update weights index value = .ok (weights.set index value) := by
  unfold Array.update
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [weights.property]; exact hindex)]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

def prefixWeightRec (coordinates : Nat → ExactQM31) :
    Nat → Nat → ExactQM31
  | 0, index => if index = 0 then 1 else 0
  | count + 1, index =>
      prefixWeightRec coordinates count (index / 2) *
        (if index % 2 = 0 then 1 - coordinates count
          else coordinates count)

@[simp] theorem prefixWeightRec_succ (coordinates : Nat → ExactQM31)
    (count index : Nat) :
    prefixWeightRec coordinates (count + 1) index =
      prefixWeightRec coordinates count (index / 2) *
        (if index % 2 = 0 then 1 - coordinates count
          else coordinates count) := by
  rfl

def ExpandedEntry (base : Nat → ExactQM31)
    (coordinate : ExactQM31) (index : Nat) : ExactQM31 :=
  base (index / 2) *
    (if index % 2 = 0 then 1 - coordinate else coordinate)

theorem usize_wrapping_mul_two_val (index : Std.Usize)
    (hbound : 2 * index.val < Std.Usize.size) :
    (Std.Usize.wrapping_mul 2#usize index).val = 2 * index.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [Nat.mul_comm] using hbound

theorem usize_wrapping_add_one_val (index : Std.Usize)
    (hbound : index.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hbound

def InnerInvariant {N : Std.Usize} (base : Nat → ExactQM31)
    (coordinate : ExactQM31) (weights : Array RustQM31 N)
    (upper width : Std.Usize) : Prop :=
  ValidWeights weights ∧
  upper.val ≤ width.val ∧
  2 * width.val ≤ N.val ∧
  N.val ≤ 64 ∧
  (∀ output : Fin N.val, output.val < upper.val →
    weightsToExact weights output = base output.val) ∧
  (∀ output : Fin N.val,
    2 * upper.val ≤ output.val → output.val < 2 * width.val →
    weightsToExact weights output =
      ExpandedEntry base coordinate output.val)

private abbrev innerBody {N : Std.Usize} :=
  @V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0.body N

private abbrev innerLoop {N : Std.Usize} :=
  @V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0 N

theorem innerBody_step {N : Std.Usize}
    (base : Nat → ExactQM31) (coordinate : ExactQM31)
    (localCoordinate : RustQM31) (prepared : RustPrepared)
    (weights : Array RustQM31 N) (upper width : Std.Usize)
    (hcoordinateValid : ValidQM31 localCoordinate)
    (hcoordinateExact : toExact localCoordinate = coordinate)
    (hprepared : RepresentsPrepared prepared localCoordinate)
    (hpositive : 0 < upper.val)
    (hinvariant : InnerInvariant base coordinate weights upper width) :
    ∃ previous : Std.Usize,
    ∃ nextWeights : Array RustQM31 N,
      previous.val = upper.val - 1 ∧
      innerBody prepared (reverseRange upper) weights =
        .ok (.cont (reverseRange previous, nextWeights)) ∧
      InnerInvariant base coordinate nextWeights previous width := by
  rcases hinvariant with
    ⟨hweightsValid, hupperWidth, hdoubleWidth, hcapacity,
      hunprocessed, hprocessed⟩
  rcases reverseRange_next_positive upper hpositive with
    ⟨previous, hprevious, hnext⟩
  have hpreviousUpper : previous.val < upper.val := by omega
  have hparentBound : previous.val < N.val := by omega
  have hparentCall := weight_index_call weights previous hparentBound
  let parent := weightEntry weights ⟨previous.val, hparentBound⟩
  have hparentValid : ValidQM31 parent :=
    hweightsValid ⟨previous.val, hparentBound⟩
  have hparentExact : toExact parent = base previous.val := by
    change weightsToExact weights ⟨previous.val, hparentBound⟩ = _
    exact hunprocessed _ hpreviousUpper
  rcases prepared_mul_corresponds prepared localCoordinate parent
      hprepared hcoordinateValid hparentValid with
    ⟨right, hrightCall, hrightValid, hrightExact⟩
  rcases qm31_sub_corresponds parent right hparentValid hrightValid with
    ⟨left, hleftCall, hleftValid, hleftExact⟩
  let evenIndex := Std.Usize.wrapping_mul 2#usize previous
  have hsize : 65 < Std.Usize.size := by
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
  have hevenIndex : evenIndex.val = 2 * previous.val := by
    apply usize_wrapping_mul_two_val
    omega
  have hevenBound : evenIndex.val < N.val := by omega
  have hevenUpdate := weight_update_call weights evenIndex hevenBound left
  let weights1 := weights.set evenIndex left
  let oddIndex := Std.Usize.wrapping_add evenIndex 1#usize
  have hoddIndex : oddIndex.val = evenIndex.val + 1 := by
    apply usize_wrapping_add_one_val
    omega
  have hoddBound : oddIndex.val < N.val := by omega
  have hoddUpdate := weight_update_call weights1 oddIndex hoddBound right
  let weights2 := weights1.set oddIndex right
  have hweights1Valid : ValidWeights weights1 :=
    valid_weights_set weights evenIndex hevenBound left
      hweightsValid hleftValid
  have hweights2Valid : ValidWeights weights2 :=
    valid_weights_set weights1 oddIndex hoddBound right
      hweights1Valid hrightValid
  have hrightMath : toExact right = base previous.val * coordinate := by
    rw [hrightExact, hcoordinateExact, hparentExact]
    ring
  have hleftMath : toExact left = base previous.val * (1 - coordinate) := by
    rw [hleftExact, hparentExact, hrightMath]
    ring
  have hunprocessed2 : ∀ output : Fin N.val,
      output.val < previous.val →
      weightsToExact weights2 output = base output.val := by
    intro output houtput
    have hneOdd : oddIndex.val ≠ output.val := by omega
    have hneEven : evenIndex.val ≠ output.val := by omega
    rw [weightsToExact,
      weightEntry_set_other weights1 oddIndex right output hneOdd,
      weightEntry_set_other weights evenIndex left output hneEven]
    exact hunprocessed output (by omega)
  have hprocessed2 : ∀ output : Fin N.val,
      2 * previous.val ≤ output.val → output.val < 2 * width.val →
      weightsToExact weights2 output =
        ExpandedEntry base coordinate output.val := by
    intro output hlow hhigh
    by_cases heven : output.val = evenIndex.val
    · have hout : output = ⟨evenIndex.val, hevenBound⟩ := Fin.ext heven
      subst output
      rw [weightsToExact,
        weightEntry_set_other weights1 oddIndex right _ (by omega),
        weightEntry_set_same]
      rw [hleftMath]
      simp [ExpandedEntry, hevenIndex]
    · by_cases hodd : output.val = oddIndex.val
      · have hout : output = ⟨oddIndex.val, hoddBound⟩ := Fin.ext hodd
        subst output
        rw [weightsToExact, weightEntry_set_same]
        rw [hrightMath]
        unfold ExpandedEntry
        have hhalf : oddIndex.val / 2 = previous.val := by
          omega
        rw [hhalf]
        simp [hoddIndex, hevenIndex]
      · rw [weightsToExact,
          weightEntry_set_other weights1 oddIndex right output
            (Ne.symm hodd),
          weightEntry_set_other weights evenIndex left output
            (Ne.symm heven)]
        apply hprocessed output
        · omega
        · exact hhigh
  have hparentCallLiteral :
      Array.index_usize weights previous = .ok parent := by
    simpa [parent] using hparentCall
  have hevenUpdateLiteral :
      Array.update weights
          (Std.Usize.wrapping_mul 2#usize previous) left =
        .ok weights1 := by
    simpa [evenIndex, weights1] using hevenUpdate
  have hoddUpdateLiteral :
      Array.update weights1
          (Std.Usize.wrapping_add
            (Std.Usize.wrapping_mul 2#usize previous) 1#usize) right =
        .ok weights2 := by
    simpa [evenIndex, oddIndex, weights1, weights2] using hoddUpdate
  refine ⟨previous, weights2, hprevious, ?_, ?_⟩
  · unfold innerBody
    unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0.body
    rw [hnext]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hparentCallLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hrightCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hleftCall]
    simp only [Aeneas.Std.bind_tc_ok]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
    rw [hevenUpdateLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hoddUpdateLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
  · exact ⟨hweights2Valid, by omega, hdoubleWidth, hcapacity,
      hunprocessed2, hprocessed2⟩

private theorem innerBody_done {N : Std.Usize}
    (prepared : RustPrepared) (weights : Array RustQM31 N) :
    innerBody prepared (reverseRange 0#usize) weights =
      .ok (.done weights) := by
  unfold innerBody
  unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0.body
  rw [reverseRange_next_zero]
  simp only [Aeneas.Std.bind_tc_ok]

def InnerLoopInvariant {N : Std.Usize} (base : Nat → ExactQM31)
    (coordinate : ExactQM31)
    (state : ReverseUsizeRange × Array RustQM31 N)
    (width : Std.Usize) : Prop :=
  ∃ upper : Std.Usize,
    state.1 = reverseRange upper ∧
    InnerInvariant base coordinate state.2 upper width

theorem innerBody_transition_spec {N : Std.Usize}
    (base : Nat → ExactQM31) (coordinate : ExactQM31)
    (localCoordinate : RustQM31) (prepared : RustPrepared)
    (state : ReverseUsizeRange × Array RustQM31 N)
    (width : Std.Usize)
    (hcoordinateValid : ValidQM31 localCoordinate)
    (hcoordinateExact : toExact localCoordinate = coordinate)
    (hprepared : RepresentsPrepared prepared localCoordinate)
    (hinvariant : InnerLoopInvariant base coordinate state width) :
    ∃ flow,
      innerBody prepared state.1 state.2 = .ok flow ∧
      (match flow with
        | .done result =>
            ValidWeights result ∧
            ∀ output : Fin N.val, output.val < 2 * width.val →
              weightsToExact result output =
                ExpandedEntry base coordinate output.val
        | .cont next =>
            InnerLoopInvariant base coordinate next width ∧
            next.1.iter.«end».val < state.1.iter.«end».val) := by
  rcases state with ⟨stateIter, stateWeights⟩
  rcases hinvariant with ⟨upper, hstateIter, hstate⟩
  change stateIter = reverseRange upper at hstateIter
  subst stateIter
  by_cases hpositive : 0 < upper.val
  · rcases innerBody_step base coordinate localCoordinate prepared
      stateWeights upper width hcoordinateValid hcoordinateExact hprepared
      hpositive hstate with
      ⟨previous, nextWeights, hprevious, hcall, hnextInvariant⟩
    refine ⟨.cont (reverseRange previous, nextWeights), hcall, ?_⟩
    refine ⟨⟨previous, rfl, hnextInvariant⟩, ?_⟩
    simp [reverseRange, hprevious]
    omega
  · have hzero : upper.val = 0 := by omega
    have hupper : upper = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hzero
    subst upper
    refine ⟨.done stateWeights, innerBody_done prepared stateWeights,
      hstate.1, ?_⟩
    intro output houtput
    exact hstate.2.2.2.2.2 output (by simp) houtput

theorem innerLoop_spec {N : Std.Usize}
    (base : Nat → ExactQM31) (coordinate : ExactQM31)
    (localCoordinate : RustQM31) (prepared : RustPrepared)
    (weights : Array RustQM31 N) (width : Std.Usize)
    (hcoordinateValid : ValidQM31 localCoordinate)
    (hcoordinateExact : toExact localCoordinate = coordinate)
    (hprepared : RepresentsPrepared prepared localCoordinate)
    (hinvariant : InnerInvariant base coordinate weights width width) :
    ∃ result : Array RustQM31 N,
      innerLoop (reverseRange width) weights prepared = .ok result ∧
      ValidWeights result ∧
      (∀ output : Fin N.val, output.val < 2 * width.val →
        weightsToExact result output =
          ExpandedEntry base coordinate output.val) := by
  have hspec : Aeneas.Std.WP.spec
      (innerLoop (reverseRange width) weights prepared)
      (fun result => ValidWeights result ∧
        ∀ output : Fin N.val, output.val < 2 * width.val →
          weightsToExact result output =
            ExpandedEntry base coordinate output.val) := by
    unfold innerLoop
    unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => state.1.iter.«end».val)
      (inv := fun state => InnerLoopInvariant base coordinate state width)
    · rintro ⟨nextIter, nextWeights⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := innerBody_transition_spec base coordinate
        localCoordinate prepared (nextIter, nextWeights) width
        hcoordinateValid hcoordinateExact hprepared hstate
      unfold innerBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      refine ⟨flow, hcall, ?_⟩
      cases flow <;> exact hpost
    · exact ⟨width, rfl, hinvariant⟩
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hvalid, hexact⟩
  exact ⟨result, hcall, hvalid, hexact⟩

def coordinateEntry (coordinates : Slice RustQM31)
    (index : Fin coordinates.val.length) : RustQM31 :=
  coordinates.val[index.val]

def exactCoordinate (coordinates : Slice RustQM31) (index : Nat) :
    ExactQM31 :=
  if hindex : index < coordinates.val.length then
    toExact (coordinateEntry coordinates ⟨index, hindex⟩)
  else 0

def ValidCoordinates (coordinates : Slice RustQM31) : Prop :=
  ∀ index : Fin coordinates.val.length,
    ValidQM31 (coordinateEntry coordinates index)

theorem sliceIterator_next_active (coordinates : Slice RustQM31)
    (index : Nat) (hindex : index < coordinates.val.length) :
    core.slice.iter.IteratorSliceIter.next
        ({ slice := coordinates, i := index } :
          core.slice.iter.Iter RustQM31) =
      .ok (some (coordinateEntry coordinates ⟨index, hindex⟩),
        { slice := coordinates, i := index + 1 }) := by
  simp [core.slice.iter.IteratorSliceIter.next, hindex,
    coordinateEntry]
  exact Slice.getElem_Nat_eq coordinates index hindex

theorem sliceIterator_next_done (coordinates : Slice RustQM31) :
    core.slice.iter.IteratorSliceIter.next
        ({ slice := coordinates, i := coordinates.val.length } :
          core.slice.iter.Iter RustQM31) =
      .ok (none,
        { slice := coordinates, i := coordinates.val.length }) := by
  simp [core.slice.iter.IteratorSliceIter.next]

def zeroRustQM31 : RustQM31 :=
  { c0 := { a := 0#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def oneRustQM31 : RustQM31 :=
  { c0 := { a := 1#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

theorem generated_zero_eq :
    V5RowExpandGenerated.aspis_core.field.QM31.ZERO = zeroRustQM31 := by
  rw [V5RowExpandGenerated.aspis_core.field.QM31.ZERO]
  rfl

theorem generated_one_eq :
    V5RowExpandGenerated.aspis_core.field.QM31.ONE = oneRustQM31 := by
  rw [V5RowExpandGenerated.aspis_core.field.QM31.ONE]
  rfl

theorem zeroRustQM31_valid : ValidQM31 zeroRustQM31 := by
  norm_num [ValidQM31, toReferenceQM31, toReferenceCM31,
    zeroRustQM31, AspisAeneasQM31Mul.CanonicalQM31,
    AspisAeneasCM31Multiplicative.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

theorem oneRustQM31_valid : ValidQM31 oneRustQM31 := by
  norm_num [ValidQM31, toReferenceQM31, toReferenceCM31,
    oneRustQM31, AspisAeneasQM31Mul.CanonicalQM31,
    AspisAeneasCM31Multiplicative.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus]

theorem zeroRustQM31_exact : toExact zeroRustQM31 = 0 := by
  rfl

theorem oneRustQM31_exact : toExact oneRustQM31 = 1 := by
  rfl

def zeroWeights (N : Std.Usize) : Array RustQM31 N :=
  Array.repeat N zeroRustQM31

def initialWeights (N : Std.Usize) : Array RustQM31 N :=
  (zeroWeights N).set 0#usize oneRustQM31

theorem zeroWeights_valid (N : Std.Usize) :
    ValidWeights (zeroWeights N) := by
  intro index
  unfold weightEntry zeroWeights
  simpa only [Array.repeat_val, List.getElem_replicate]
    using zeroRustQM31_valid

theorem initialWeights_valid (N : Std.Usize) (hpositive : 0 < N.val) :
    ValidWeights (initialWeights N) := by
  exact valid_weights_set (zeroWeights N) 0#usize hpositive oneRustQM31
    (zeroWeights_valid N) oneRustQM31_valid

theorem initialWeights_active (N : Std.Usize) (hpositive : 0 < N.val)
    (output : Fin N.val) (houtput : output.val < 1) :
    weightsToExact (initialWeights N) output =
      prefixWeightRec coordinates 0 output.val := by
  have hzeroVal : output.val = 0 := by omega
  have hzero : output = ⟨0, hpositive⟩ := by
    apply Fin.ext
    simpa using hzeroVal
  subst output
  have hentry := weightEntry_set_same (zeroWeights N) 0#usize
    hpositive oneRustQM31
  have hfin : (⟨0, hpositive⟩ : Fin N.val) =
      ⟨(0#usize : Std.Usize).val, hpositive⟩ := by
    apply Fin.ext
    rfl
  rw [weightsToExact, initialWeights, hfin, hentry,
    oneRustQM31_exact]
  rfl

@[simp] theorem exactCoordinate_active (coordinates : Slice RustQM31)
    (index : Nat) (hindex : index < coordinates.val.length) :
    exactCoordinate coordinates index =
      toExact (coordinateEntry coordinates ⟨index, hindex⟩) := by
  simp [exactCoordinate, hindex]

def exactWeightAt {N : Std.Usize} (weights : Array RustQM31 N)
    (index : Nat) : ExactQM31 :=
  if hindex : index < N.val then
    weightsToExact weights ⟨index, hindex⟩
  else 0

@[simp] theorem exactWeightAt_active {N : Std.Usize}
    (weights : Array RustQM31 N) (index : Nat)
    (hindex : index < N.val) :
    exactWeightAt weights index =
      weightsToExact weights ⟨index, hindex⟩ := by
  simp [exactWeightAt, hindex]

def OuterInvariant {N : Std.Usize} (coordinates : Slice RustQM31)
    (weights : Array RustQM31 N) (width : Std.Usize)
    (index : Nat) : Prop :=
  ValidWeights weights ∧
  index ≤ coordinates.val.length ∧
  width.val = 2 ^ index ∧
  N.val = 2 ^ coordinates.val.length ∧
  N.val ≤ 64 ∧
  (∀ output : Fin N.val, output.val < width.val →
    weightsToExact weights output =
      prefixWeightRec (exactCoordinate coordinates) index output.val)

private abbrev outerBody {N : Std.Usize} :=
  @V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0.body N

private abbrev outerLoop {N : Std.Usize} :=
  @V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0 N

theorem outerBody_step {N : Std.Usize}
    (coordinates : Slice RustQM31) (weights : Array RustQM31 N)
    (width : Std.Usize) (index : Nat)
    (hcoordinates : ValidCoordinates coordinates)
    (hinvariant : OuterInvariant coordinates weights width index)
    (hcontinue : index < coordinates.val.length) :
    ∃ nextWeights : Array RustQM31 N,
    ∃ nextWidth : Std.Usize,
      outerBody
          ({ slice := coordinates, i := index } :
            core.slice.iter.Iter RustQM31)
          weights width =
        .ok (.cont
          ({ slice := coordinates, i := index + 1 }, nextWeights, nextWidth)) ∧
      nextWidth.val = 2 * width.val ∧
      OuterInvariant coordinates nextWeights nextWidth (index + 1) := by
  rcases hinvariant with
    ⟨hweightsValid, hindexBound, hwidth, hcapacityExact,
      hcapacity, hweightsExact⟩
  have hnext := sliceIterator_next_active coordinates index hcontinue
  let localCoordinate := coordinateEntry coordinates ⟨index, hcontinue⟩
  let coordinate := exactCoordinate coordinates index
  have hcoordinateValid : ValidQM31 localCoordinate :=
    hcoordinates ⟨index, hcontinue⟩
  have hcoordinateExact : toExact localCoordinate = coordinate := by
    symm
    exact exactCoordinate_active coordinates index hcontinue
  rcases prepared_new_establishes localCoordinate hcoordinateValid with
    ⟨prepared, hpreparedCall, hprepared⟩
  have hpow : 2 ^ (index + 1) ≤ 2 ^ coordinates.val.length :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdoubleWidth : 2 * width.val ≤ N.val := by
    rw [hwidth, hcapacityExact]
    simpa [pow_succ, Nat.mul_comm] using hpow
  have hinnerInvariant : InnerInvariant (exactWeightAt weights)
      coordinate weights width width := by
    refine ⟨hweightsValid, le_rfl, hdoubleWidth, hcapacity, ?_, ?_⟩
    · intro output _
      symm
      exact exactWeightAt_active weights output.val output.isLt
    · intro output hlow hhigh
      omega
  rcases innerLoop_spec (exactWeightAt weights) coordinate
      localCoordinate prepared weights width hcoordinateValid
      hcoordinateExact hprepared hinnerInvariant with
    ⟨weights1, hweights1Call, hweights1Valid, hweights1Exact⟩
  let width1 := Std.Usize.wrapping_mul width 2#usize
  have hsize : 65 < Std.Usize.size := by
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
  have hwidth1 : width1.val = 2 * width.val := by
    rw [Std.Usize.wrapping_mul_val_eq]
    rw [UScalar.size_UScalarTyUsize]
    have htwo : (2#usize : Std.Usize).val = 2 := rfl
    rw [htwo]
    rw [Nat.mul_comm]
    apply Nat.mod_eq_of_lt
    omega
  have hweights1Math : ∀ output : Fin N.val,
      output.val < width1.val →
      weightsToExact weights1 output =
        prefixWeightRec (exactCoordinate coordinates) (index + 1)
          output.val := by
    intro output houtput
    have houtput2 : output.val < 2 * width.val := by omega
    rw [hweights1Exact output houtput2]
    unfold ExpandedEntry
    have hparentWidth : output.val / 2 < width.val := by omega
    have hparentN : output.val / 2 < N.val := by omega
    rw [exactWeightAt_active weights (output.val / 2) hparentN]
    rw [hweightsExact ⟨output.val / 2, hparentN⟩ hparentWidth]
    rw [prefixWeightRec_succ]
  have hrev :
      core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize)
          ({ start := 0#usize, «end» := width } :
            core.ops.range.Range Std.Usize) =
        .ok (reverseRange width) := by
    rfl
  have hinnerCallLiteral :
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0_loop0
          (reverseRange width) weights prepared = .ok weights1 := by
    simpa [innerLoop] using hweights1Call
  refine ⟨weights1, width1, ?_, hwidth1, ?_⟩
  · unfold outerBody
    unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0.body
    rw [hnext]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hpreparedCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hrev]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hinnerCallLiteral]
    simp only [Aeneas.Std.bind_tc_ok]
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, width1]
  · refine ⟨hweights1Valid, by omega, ?_, hcapacityExact,
      hcapacity, hweights1Math⟩
    rw [hwidth1, hwidth, pow_succ]
    ring

private theorem outerBody_done {N : Std.Usize}
    (coordinates : Slice RustQM31) (weights : Array RustQM31 N)
    (width : Std.Usize) :
    outerBody
        ({ slice := coordinates, i := coordinates.val.length } :
          core.slice.iter.Iter RustQM31)
        weights width = .ok (.done weights) := by
  unfold outerBody
  unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0.body
  rw [sliceIterator_next_done]
  simp only [Aeneas.Std.bind_tc_ok]

def OuterLoopInvariant {N : Std.Usize} (coordinates : Slice RustQM31)
    (state : core.slice.iter.Iter RustQM31 ×
      Array RustQM31 N × Std.Usize) : Prop :=
  ∃ index : Nat,
    state.1 = { slice := coordinates, i := index } ∧
    OuterInvariant coordinates state.2.1 state.2.2 index

theorem outerBody_transition_spec {N : Std.Usize}
    (coordinates : Slice RustQM31)
    (state : core.slice.iter.Iter RustQM31 ×
      Array RustQM31 N × Std.Usize)
    (hcoordinates : ValidCoordinates coordinates)
    (hinvariant : OuterLoopInvariant coordinates state) :
    ∃ flow,
      outerBody state.1 state.2.1 state.2.2 = .ok flow ∧
      (match flow with
        | .done result =>
            ValidWeights result ∧
            ∀ output : Fin N.val,
              weightsToExact result output =
                prefixWeightRec (exactCoordinate coordinates)
                  coordinates.val.length output.val
        | .cont next =>
            OuterLoopInvariant coordinates next ∧
            coordinates.val.length - next.1.i <
              coordinates.val.length - state.1.i) := by
  rcases state with ⟨stateIter, stateWeights, stateWidth⟩
  rcases hinvariant with ⟨index, hstateIter, hstate⟩
  change stateIter =
    ({ slice := coordinates, i := index } :
      core.slice.iter.Iter RustQM31) at hstateIter
  subst stateIter
  by_cases hcontinue : index < coordinates.val.length
  · rcases outerBody_step coordinates stateWeights stateWidth index
      hcoordinates hstate hcontinue with
      ⟨nextWeights, nextWidth, hcall, hnextWidth, hnextInvariant⟩
    refine ⟨.cont
      ({ slice := coordinates, i := index + 1 }, nextWeights, nextWidth),
      hcall, ?_⟩
    refine ⟨⟨index + 1, rfl, hnextInvariant⟩, ?_⟩
    simp
    omega
  · have hfinal : index = coordinates.val.length := by
      have hbound := hstate.2.1
      omega
    subst index
    refine ⟨.done stateWeights,
      outerBody_done coordinates stateWeights stateWidth,
      hstate.1, ?_⟩
    intro output
    have hwidthFinal : stateWidth.val = N.val := by
      rw [hstate.2.2.1, hstate.2.2.2.1]
    exact hstate.2.2.2.2.2 output (by
      rw [hwidthFinal]
      exact output.isLt)

theorem outerLoop_spec {N : Std.Usize}
    (coordinates : Slice RustQM31) (weights : Array RustQM31 N)
    (width : Std.Usize) (index : Nat)
    (hcoordinates : ValidCoordinates coordinates)
    (hinvariant : OuterInvariant coordinates weights width index) :
    ∃ result : Array RustQM31 N,
      outerLoop
          ({ slice := coordinates, i := index } :
            core.slice.iter.Iter RustQM31)
          weights width = .ok result ∧
      ValidWeights result ∧
      (∀ output : Fin N.val,
        weightsToExact result output =
          prefixWeightRec (exactCoordinate coordinates)
            coordinates.val.length output.val) := by
  have hspec : Aeneas.Std.WP.spec
      (outerLoop
        ({ slice := coordinates, i := index } :
          core.slice.iter.Iter RustQM31)
        weights width)
      (fun result => ValidWeights result ∧
        ∀ output : Fin N.val,
          weightsToExact result output =
            prefixWeightRec (exactCoordinate coordinates)
              coordinates.val.length output.val) := by
    unfold outerLoop
    unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand_loop0
    apply Aeneas.Std.loop.spec_decr_nat
      (measure := fun state => coordinates.val.length - state.1.i)
      (inv := fun state => OuterLoopInvariant coordinates state)
    · rintro ⟨nextIter, nextWeights, nextWidth⟩ hstate
      simp only
      apply Aeneas.Std.WP.exists_imp_spec
      have htransition := outerBody_transition_spec coordinates
        (nextIter, nextWeights, nextWidth) hcoordinates hstate
      unfold outerBody at htransition
      rcases htransition with ⟨flow, hcall, hpost⟩
      refine ⟨flow, hcall, ?_⟩
      cases flow <;> exact hpost
    · exact ⟨index, rfl, hinvariant⟩
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨result, hcall, hvalid, hexact⟩
  exact ⟨result, hcall, hvalid, hexact⟩

theorem expand_exact_spec {N : Std.Usize}
    (coordinates : Slice RustQM31)
    (hcoordinates : ValidCoordinates coordinates)
    (hsize : N.val = 2 ^ coordinates.val.length)
    (hcapacity : N.val ≤ 64) :
    ∃ result : Array RustQM31 N,
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          N coordinates = .ok result ∧
      ValidWeights result ∧
      (∀ output : Fin N.val,
        weightsToExact result output =
          prefixWeightRec (exactCoordinate coordinates)
            coordinates.val.length output.val) := by
  have hpositive : 0 < N.val := by
    rw [hsize]
    exact Nat.two_pow_pos _
  have hinitial : OuterInvariant coordinates
      (initialWeights N) 1#usize 0 := by
    refine ⟨initialWeights_valid N hpositive, by omega, by norm_num,
      hsize, hcapacity, ?_⟩
    intro output houtput
    exact initialWeights_active N hpositive output houtput
  rcases outerLoop_spec coordinates (initialWeights N) 1#usize 0
      hcoordinates hinitial with
    ⟨result, hloop, hvalid, hexact⟩
  have hupdate : Array.update (zeroWeights N) 0#usize oneRustQM31 =
      .ok (initialWeights N) := by
    exact weight_update_call (zeroWeights N) 0#usize hpositive oneRustQM31
  refine ⟨result, ?_, hvalid, hexact⟩
  unfold V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
  rw [generated_zero_eq, generated_one_eq]
  change (do
    let a ← Array.update (zeroWeights N) 0#usize oneRustQM31
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        coordinates
    outerLoop iter a 1#usize) = .ok result
  rw [hupdate]
  simp only [Aeneas.Std.bind_tc_ok]
  change outerLoop
      ({ slice := coordinates, i := 0 } : core.slice.iter.Iter RustQM31)
      (initialWeights N) 1#usize = .ok result
  exact hloop

end Expand

namespace Access

abbrev RustM31 := V5RowAccessGenerated.aspis_core.field.M31
abbrev RustCM31 := V5RowAccessGenerated.aspis_core.field.CM31
abbrev RustQM31 := V5RowAccessGenerated.aspis_core.field.QM31
abbrev RustSelectors :=
  V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors
abbrev ExactQM31 := AspisAeneasQM31Mul.QM31Exact

def toReferenceCM31 (value : RustCM31) :
    AspisCoreCM31Multiplicative.field.CM31 :=
  { a := value.a, b := value.b }

def toReferenceQM31 (value : RustQM31) :
    AspisCoreCM31Multiplicative.field.QM31 :=
  { c0 := toReferenceCM31 value.c0, c1 := toReferenceCM31 value.c1 }

def fromReferenceCM31 (value : AspisCoreCM31Multiplicative.field.CM31) :
    RustCM31 :=
  { a := value.a, b := value.b }

def fromReferenceQM31 (value : AspisCoreCM31Multiplicative.field.QM31) :
    RustQM31 :=
  { c0 := fromReferenceCM31 value.c0,
    c1 := fromReferenceCM31 value.c1 }

def ValidQM31 (value : RustQM31) : Prop :=
  AspisAeneasQM31Mul.CanonicalQM31 (toReferenceQM31 value)

def ValidCM31 (value : RustCM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalCM31
    (toReferenceCM31 value)

def cm31ToExact (value : RustCM31) :
    AspisAeneasQM31Mul.CM31Exact :=
  AspisAeneasQM31Mul.cm31ToExact (toReferenceCM31 value)

def toExact (value : RustQM31) : ExactQM31 :=
  AspisAeneasQM31Mul.qm31ToExact (toReferenceQM31 value)

theorem m31_add_call_eq_reference (left right : RustM31) :
    V5RowAccessGenerated.aspis_core.field.M31.add left right =
      AspisCoreCM31Multiplicative.field.M31.add left right := by
  unfold V5RowAccessGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [V5RowAccessGenerated.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.P]

theorem m31_sub_call_eq_reference (left right : RustM31) :
    V5RowAccessGenerated.aspis_core.field.M31.sub left right =
      AspisCoreCM31Multiplicative.field.M31.sub left right := by
  unfold V5RowAccessGenerated.aspis_core.field.M31.sub
    AspisCoreCM31Multiplicative.field.M31.sub
  rw [V5RowAccessGenerated.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.P]

theorem m31_mul_call_eq_reference (left right : RustM31) :
    V5RowAccessGenerated.aspis_core.field.M31.mul left right =
      AspisCoreCM31Multiplicative.field.M31.mul left right := by
  unfold V5RowAccessGenerated.aspis_core.field.M31.mul
    AspisCoreCM31Multiplicative.field.M31.mul
    V5RowAccessGenerated.aspis_core.field.reduce_u64
    AspisCoreCM31Multiplicative.field.reduce_u64
  rw [V5RowAccessGenerated.aspis_core.field.P,
    AspisCoreCM31Multiplicative.field.P]

theorem cm31_add_corresponds (left right : RustCM31)
    (hleft : ValidCM31 left) (hright : ValidCM31 right) :
    ∃ output : RustCM31,
      V5RowAccessGenerated.aspis_core.field.CM31.add left right = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output = cm31ToExact left + cm31ToExact right := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hvalidA, hexactA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hvalidB, hexactB⟩
  let output : RustCM31 := { a := oa, b := ob }
  refine ⟨output, ?_, ⟨hvalidA, hvalidB⟩, ?_⟩
  · simp [V5RowAccessGenerated.aspis_core.field.CM31.add,
      m31_add_call_eq_reference, hcallA, hcallB, output]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem cm31_sub_corresponds (left right : RustCM31)
    (hleft : ValidCM31 left) (hright : ValidCM31 right) :
    ∃ output : RustCM31,
      V5RowAccessGenerated.aspis_core.field.CM31.sub left right = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output = cm31ToExact left - cm31ToExact right := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      left.a right.a hleft.1 hright.1 with
    ⟨oa, hcallA, hvalidA, hexactA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      left.b right.b hleft.2 hright.2 with
    ⟨ob, hcallB, hvalidB, hexactB⟩
  let output : RustCM31 := { a := oa, b := ob }
  refine ⟨output, ?_, ⟨hvalidA, hvalidB⟩, ?_⟩
  · simp [V5RowAccessGenerated.aspis_core.field.CM31.sub,
      m31_sub_call_eq_reference, hcallA, hcallB, output]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

theorem cm31_mul_corresponds (left right : RustCM31)
    (hleft : ValidCM31 left) (hright : ValidCM31 right) :
    ∃ output : RustCM31,
      V5RowAccessGenerated.aspis_core.field.CM31.mul left right = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output = cm31ToExact left * cm31ToExact right := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      left.a right.a hleft.1 hright.1 with
    ⟨m0, hm0Reference, hm0Valid, hm0Exact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      left.b right.b hleft.2 hright.2 with
    ⟨m1, hm1Reference, hm1Valid, hm1Exact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      left.a left.b hleft.1 hleft.2 with
    ⟨leftSum, hleftSumReference, hleftSumValid, hleftSumExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      right.a right.b hright.1 hright.2 with
    ⟨rightSum, hrightSumReference, hrightSumValid, hrightSumExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
      leftSum rightSum hleftSumValid hrightSumValid with
    ⟨m2, hm2Reference, hm2Valid, hm2Exact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      m0 m1 hm0Valid hm1Valid with
    ⟨real, hrealReference, hrealValid, hrealExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      m2 m0 hm2Valid hm0Valid with
    ⟨imagPartial, himagPartialReference,
      himagPartialValid, himagPartialExact⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      imagPartial m1 himagPartialValid hm1Valid with
    ⟨imag, himagReference, himagValid, himagExact⟩
  have hm0 : V5RowAccessGenerated.aspis_core.field.M31.mul
      left.a right.a = .ok m0 := by
    simpa [m31_mul_call_eq_reference] using hm0Reference
  have hm1 : V5RowAccessGenerated.aspis_core.field.M31.mul
      left.b right.b = .ok m1 := by
    simpa [m31_mul_call_eq_reference] using hm1Reference
  have hleftSum : V5RowAccessGenerated.aspis_core.field.M31.add
      left.a left.b = .ok leftSum := by
    simpa [m31_add_call_eq_reference] using hleftSumReference
  have hrightSum : V5RowAccessGenerated.aspis_core.field.M31.add
      right.a right.b = .ok rightSum := by
    simpa [m31_add_call_eq_reference] using hrightSumReference
  have hm2 : V5RowAccessGenerated.aspis_core.field.M31.mul
      leftSum rightSum = .ok m2 := by
    simpa [m31_mul_call_eq_reference] using hm2Reference
  have hreal : V5RowAccessGenerated.aspis_core.field.M31.sub
      m0 m1 = .ok real := by
    simpa [m31_sub_call_eq_reference] using hrealReference
  have himagPartial : V5RowAccessGenerated.aspis_core.field.M31.sub
      m2 m0 = .ok imagPartial := by
    simpa [m31_sub_call_eq_reference] using himagPartialReference
  have himag : V5RowAccessGenerated.aspis_core.field.M31.sub
      imagPartial m1 = .ok imag := by
    simpa [m31_sub_call_eq_reference] using himagReference
  let output : RustCM31 := { a := real, b := imag }
  refine ⟨output, ?_, ⟨hrealValid, himagValid⟩, ?_⟩
  · simp [V5RowAccessGenerated.aspis_core.field.CM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2,
      hreal, himagPartial, himag, output]
  · apply QuadraticAlgebra.ext
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        output, toReferenceCM31, QuadraticAlgebra.re_mul]
      rw [hrealExact, hm0Exact, hm1Exact]
      ring
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        output, toReferenceCM31, QuadraticAlgebra.im_mul]
      rw [himagExact, himagPartialExact, hm2Exact,
        hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      ring

theorem mul_by_r_corresponds (value : RustCM31)
    (hvalue : ValidCM31 value) :
    ∃ output : RustCM31,
      V5RowAccessGenerated.aspis_core.field.mul_by_r value = .ok output ∧
      ValidCM31 output ∧
      cm31ToExact output =
        cm31ToExact value * AspisAeneasQM31Mul.qm31R := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_double_corresponds
      value.a hvalue.1 with
    ⟨twiceA, htwiceA, hvalidTwiceA, hexactTwiceA⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
      twiceA value.b hvalidTwiceA hvalue.2 with
    ⟨real, hreal, hvalidReal, hexactReal⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_double_corresponds
      value.b hvalue.2 with
    ⟨twiceB, htwiceB, hvalidTwiceB, hexactTwiceB⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      value.a twiceB hvalue.1 hvalidTwiceB with
    ⟨imag, himag, hvalidImag, hexactImag⟩
  let output : RustCM31 := { a := real, b := imag }
  refine ⟨output, ?_, ⟨hvalidReal, hvalidImag⟩, ?_⟩
  · have htwiceA' :
        V5RowAccessGenerated.aspis_core.field.M31.double value.a =
          .ok twiceA := by
      simpa [V5RowAccessGenerated.aspis_core.field.M31.double,
        AspisCoreCM31Multiplicative.field.M31.double,
        m31_add_call_eq_reference] using htwiceA
    have hreal' :
        V5RowAccessGenerated.aspis_core.field.M31.sub twiceA value.b =
          .ok real := by
      simpa [m31_sub_call_eq_reference] using hreal
    have htwiceB' :
        V5RowAccessGenerated.aspis_core.field.M31.double value.b =
          .ok twiceB := by
      simpa [V5RowAccessGenerated.aspis_core.field.M31.double,
        AspisCoreCM31Multiplicative.field.M31.double,
        m31_add_call_eq_reference] using htwiceB
    have himag' :
        V5RowAccessGenerated.aspis_core.field.M31.add value.a twiceB =
          .ok imag := by
      simpa [m31_add_call_eq_reference] using himag
    simp [V5RowAccessGenerated.aspis_core.field.mul_by_r,
      htwiceA', hreal', htwiceB', himag', output]
  · apply QuadraticAlgebra.ext
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        QuadraticAlgebra.re_mul, AspisAeneasQM31Mul.qm31R]
      simp only [output, toReferenceCM31]
      rw [hexactReal, hexactTwiceA]
      ring
    · simp only [cm31ToExact, AspisAeneasQM31Mul.cm31ToExact,
        QuadraticAlgebra.im_mul, AspisAeneasQM31Mul.qm31R]
      simp only [output, toReferenceCM31]
      rw [hexactImag, hexactTwiceB]
      ring

theorem qm31_mul_corresponds (left right : RustQM31)
    (hleft : ValidQM31 left) (hright : ValidQM31 right) :
    ∃ output : RustQM31,
      V5RowAccessGenerated.aspis_core.field.QM31.mul left right = .ok output ∧
      ValidQM31 output ∧
      toExact output = toExact left * toExact right := by
  rcases cm31_mul_corresponds left.c0 right.c0 hleft.1 hright.1 with
    ⟨m0, hm0, hm0Valid, hm0Exact⟩
  rcases cm31_mul_corresponds left.c1 right.c1 hleft.2 hright.2 with
    ⟨m1, hm1, hm1Valid, hm1Exact⟩
  rcases cm31_add_corresponds left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSum, hleftSumValid, hleftSumExact⟩
  rcases cm31_add_corresponds right.c0 right.c1 hright.1 hright.2 with
    ⟨rightSum, hrightSum, hrightSumValid, hrightSumExact⟩
  rcases cm31_mul_corresponds leftSum rightSum
      hleftSumValid hrightSumValid with
    ⟨m2, hm2, hm2Valid, hm2Exact⟩
  rcases mul_by_r_corresponds m1 hm1Valid with
    ⟨rM1, hrM1, hrM1Valid, hrM1Exact⟩
  rcases cm31_add_corresponds m0 rM1 hm0Valid hrM1Valid with
    ⟨low, hlow, hlowValid, hlowExact⟩
  rcases cm31_sub_corresponds m2 m0 hm2Valid hm0Valid with
    ⟨highPartial, hhighPartial, hhighPartialValid, hhighPartialExact⟩
  rcases cm31_sub_corresponds highPartial m1
      hhighPartialValid hm1Valid with
    ⟨high, hhigh, hhighValid, hhighExact⟩
  have hlowTower : cm31ToExact low =
      cm31ToExact left.c0 * cm31ToExact right.c0 +
        AspisAeneasQM31Mul.qm31R *
          (cm31ToExact left.c1 * cm31ToExact right.c1) := by
    rw [hlowExact, hm0Exact, hrM1Exact, hm1Exact]
    ring
  have hhighTower : cm31ToExact high =
      cm31ToExact left.c0 * cm31ToExact right.c1 +
        cm31ToExact left.c1 * cm31ToExact right.c0 := by
    calc
      cm31ToExact high = cm31ToExact highPartial - cm31ToExact m1 :=
        hhighExact
      _ = (cm31ToExact m2 - cm31ToExact m0) - cm31ToExact m1 := by
        rw [hhighPartialExact]
      _ = ((cm31ToExact left.c0 + cm31ToExact left.c1) *
            (cm31ToExact right.c0 + cm31ToExact right.c1) -
            cm31ToExact left.c0 * cm31ToExact right.c0) -
            cm31ToExact left.c1 * cm31ToExact right.c1 := by
        rw [hm2Exact, hleftSumExact, hrightSumExact, hm0Exact, hm1Exact]
      _ = cm31ToExact left.c0 * cm31ToExact right.c1 +
            cm31ToExact left.c1 * cm31ToExact right.c0 := by ring
  let output : RustQM31 := { c0 := low, c1 := high }
  refine ⟨output, ?_, ⟨hlowValid, hhighValid⟩, ?_⟩
  · simp [V5RowAccessGenerated.aspis_core.field.QM31.mul,
      hm0, hm1, hleftSum, hrightSum, hm2,
      hrM1, hlow, hhighPartial, hhigh, output]
  · apply QuadraticAlgebra.ext
    · change cm31ToExact low =
        cm31ToExact left.c0 * cm31ToExact right.c0 +
          AspisAeneasQM31Mul.qm31R * cm31ToExact left.c1 *
            cm31ToExact right.c1
      rw [hlowTower]
      ring
    · simpa [toExact, AspisAeneasQM31Mul.qm31ToExact,
        toReferenceQM31, output, cm31ToExact] using hhighTower

def arrayEntry {N : Std.Usize} (values : Array RustQM31 N)
    (index : Fin N.val) : RustQM31 :=
  values.val[index.val]'(by rw [values.property]; exact index.isLt)

def ArrayValid {N : Std.Usize} (values : Array RustQM31 N) : Prop :=
  ∀ index : Fin N.val, ValidQM31 (arrayEntry values index)

theorem array_index_call {N : Std.Usize}
    (values : Array RustQM31 N) (index : Std.Usize)
    (hindex : index.val < N.val) :
    Array.index_usize values index =
      .ok (arrayEntry values ⟨index.val, hindex⟩) := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem (by rw [values.property]; exact hindex)]
  rfl

end Access

namespace Composition

open scoped BigOperators

theorem generated_coordinate_slices_exact {T : Type}
    (point : Array T 10#usize) :
    ∃ high low : Slice T,
      V5RowCallSiteGenerated.atomic_semantic_selector_coordinate_slices point =
        .ok (high, low) ∧
      high.val = point.val.take 6 ∧
      low.val = point.val.drop 6 := by
  unfold V5RowCallSiteGenerated.atomic_semantic_selector_coordinate_slices
  simp [core.array.Array.index, core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    Array.to_slice, Slice.drop]

abbrev ExactQM31 := AspisAeneasQM31Mul.QM31Exact

def expandToAccessQM31 (value : Expand.RustQM31) : Access.RustQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b },
    c1 := { a := value.c1.a, b := value.c1.b } }

def expandArrayToAccess {N : Std.Usize}
    (values : Array Expand.RustQM31 N) : Array Access.RustQM31 N :=
  ⟨values.val.map expandToAccessQM31, by
    simp only [List.length_map]
    exact values.property⟩

@[simp] theorem expandToAccess_valid (value : Expand.RustQM31) :
    Access.ValidQM31 (expandToAccessQM31 value) ↔
      Expand.ValidQM31 value := by
  rfl

@[simp] theorem expandToAccess_exact (value : Expand.RustQM31) :
    Access.toExact (expandToAccessQM31 value) = Expand.toExact value := by
  rfl

@[simp] theorem expandArrayToAccess_entry {N : Std.Usize}
    (values : Array Expand.RustQM31 N) (index : Fin N.val) :
    Access.arrayEntry (expandArrayToAccess values) index =
      expandToAccessQM31 (Expand.weightEntry values index) := by
  simp [Access.arrayEntry, expandArrayToAccess, Expand.weightEntry]

theorem expandArrayToAccess_valid {N : Std.Usize}
    (values : Array Expand.RustQM31 N)
    (hvalues : Expand.ValidWeights values) :
    Access.ArrayValid (expandArrayToAccess values) := by
  intro index
  rw [expandArrayToAccess_entry, expandToAccess_valid]
  exact hvalues index

set_option maxHeartbeats 1000000 in
theorem prefixWeightRec_six_eq_product
    (coordinates : Nat → ExactQM31) (index : Fin 64) :
    Expand.prefixWeightRec coordinates 6 index.val =
      ∏ coordinate : Fin 6,
        if Nat.testBit index.val (5 - coordinate.val) then
          coordinates coordinate.val
        else 1 - coordinates coordinate.val := by
  fin_cases index <;>
    norm_num [Expand.prefixWeightRec, Fin.prod_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq] <;>
    ring

set_option maxHeartbeats 1000000 in
theorem prefixWeightRec_four_eq_product
    (coordinates : Nat → ExactQM31) (index : Fin 16) :
    Expand.prefixWeightRec coordinates 4 index.val =
      ∏ coordinate : Fin 4,
        if Nat.testBit index.val (3 - coordinate.val) then
          coordinates coordinate.val
        else 1 - coordinates coordinate.val := by
  fin_cases index <;>
    norm_num [Expand.prefixWeightRec, Fin.prod_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq] <;>
    ring

abbrev TerminalPoint :=
  AspisV5ProductionRowSelector.TerminalPoint ExactQM31

def highProduct (point : TerminalPoint) (index : Fin 64) : ExactQM31 :=
  ∏ coordinate : Fin 6,
    if Nat.testBit index.val (5 - coordinate.val) then
      point ⟨coordinate.val, by omega⟩
    else 1 - point ⟨coordinate.val, by omega⟩

def lowProduct (point : TerminalPoint) (index : Fin 16) : ExactQM31 :=
  ∏ coordinate : Fin 4,
    if Nat.testBit index.val (3 - coordinate.val) then
      point ⟨6 + coordinate.val, by omega⟩
    else 1 - point ⟨6 + coordinate.val, by omega⟩

def ExactHighCoordinates (point : TerminalPoint)
    (coordinates : Slice Expand.RustQM31) : Prop :=
  coordinates.val.length = 6 ∧
  ∀ coordinate : Fin 6,
    Expand.exactCoordinate coordinates coordinate.val =
      point ⟨coordinate.val, by omega⟩

def ExactLowCoordinates (point : TerminalPoint)
    (coordinates : Slice Expand.RustQM31) : Prop :=
  coordinates.val.length = 4 ∧
  ∀ coordinate : Fin 4,
    Expand.exactCoordinate coordinates coordinate.val =
      point ⟨6 + coordinate.val, by omega⟩

def pointEntry (point : Array Expand.RustQM31 10#usize)
    (coordinate : Fin 10) : Expand.RustQM31 :=
  point.val[coordinate.val]'(by rw [point.property]; exact coordinate.isLt)

def ValidTerminalPointRepresentation
    (point : Array Expand.RustQM31 10#usize) : Prop :=
  ∀ coordinate : Fin 10, Expand.ValidQM31 (pointEntry point coordinate)

def ExactTerminalPointRepresentation (point : TerminalPoint)
    (rustPoint : Array Expand.RustQM31 10#usize) : Prop :=
  ∀ coordinate : Fin 10,
    Expand.toExact (pointEntry rustPoint coordinate) = point coordinate

theorem generated_coordinate_slices_match_terminal_point
    (point : TerminalPoint)
    (rustPoint : Array Expand.RustQM31 10#usize)
    (hvalid : ValidTerminalPointRepresentation rustPoint)
    (hexact : ExactTerminalPointRepresentation point rustPoint) :
    ∃ highCoordinates lowCoordinates : Slice Expand.RustQM31,
      V5RowCallSiteGenerated.atomic_semantic_selector_coordinate_slices
          rustPoint = .ok (highCoordinates, lowCoordinates) ∧
      Expand.ValidCoordinates highCoordinates ∧
      Expand.ValidCoordinates lowCoordinates ∧
      ExactHighCoordinates point highCoordinates ∧
      ExactLowCoordinates point lowCoordinates := by
  rcases generated_coordinate_slices_exact rustPoint with
    ⟨highCoordinates, lowCoordinates, hcall, hhigh, hlow⟩
  have hhighLength : highCoordinates.val.length = 6 := by
    rw [hhigh, List.length_take, rustPoint.property]
    norm_num
  have hlowLength : lowCoordinates.val.length = 4 := by
    rw [hlow, List.length_drop, rustPoint.property]
    norm_num
  refine ⟨highCoordinates, lowCoordinates, hcall, ?_, ?_, ?_, ?_⟩
  · intro coordinate
    have hcoordinate : coordinate.val < 10 := by omega
    simpa [Expand.coordinateEntry, hhigh, pointEntry] using
      hvalid ⟨coordinate.val, hcoordinate⟩
  · intro coordinate
    have hcoordinate : 6 + coordinate.val < 10 := by omega
    simpa [Expand.coordinateEntry, hlow, pointEntry, Nat.add_comm] using
      hvalid ⟨6 + coordinate.val, hcoordinate⟩
  · constructor
    · exact hhighLength
    · intro coordinate
      have hcoordinate : coordinate.val < 10 := by omega
      simpa [Expand.exactCoordinate, Expand.coordinateEntry, hhigh,
        rustPoint.property, pointEntry] using
        hexact ⟨coordinate.val, hcoordinate⟩
  · constructor
    · exact hlowLength
    · intro coordinate
      have hcoordinate : 6 + coordinate.val < 10 := by omega
      simpa [Expand.exactCoordinate, Expand.coordinateEntry, hlow,
        rustPoint.property, pointEntry, Nat.add_comm] using
        hexact ⟨6 + coordinate.val, hcoordinate⟩

theorem expand_high_exact (point : TerminalPoint)
    (coordinates : Slice Expand.RustQM31)
    (hvalid : Expand.ValidCoordinates coordinates)
    (hexact : ExactHighCoordinates point coordinates) :
    ∃ result : Array Expand.RustQM31 64#usize,
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          64#usize coordinates = .ok result ∧
      Expand.ValidWeights result ∧
      ∀ index : Fin 64,
        Expand.weightsToExact result index = highProduct point index := by
  rcases Expand.expand_exact_spec (N := 64#usize) coordinates hvalid
      (by norm_num [hexact.1]) (by norm_num) with
    ⟨result, hcall, hresultValid, hresultExact⟩
  refine ⟨result, hcall, hresultValid, ?_⟩
  intro index
  rw [hresultExact index]
  rw [hexact.1]
  rw [prefixWeightRec_six_eq_product]
  unfold highProduct
  apply Finset.prod_congr rfl
  intro coordinate _
  rw [hexact.2 coordinate]

theorem expand_low_exact (point : TerminalPoint)
    (coordinates : Slice Expand.RustQM31)
    (hvalid : Expand.ValidCoordinates coordinates)
    (hexact : ExactLowCoordinates point coordinates) :
    ∃ result : Array Expand.RustQM31 16#usize,
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          16#usize coordinates = .ok result ∧
      Expand.ValidWeights result ∧
      ∀ index : Fin 16,
        Expand.weightsToExact result index = lowProduct point index := by
  rcases Expand.expand_exact_spec (N := 16#usize) coordinates hvalid
      (by norm_num [hexact.1]) (by norm_num) with
    ⟨result, hcall, hresultValid, hresultExact⟩
  refine ⟨result, hcall, hresultValid, ?_⟩
  intro index
  rw [hresultExact index]
  rw [hexact.1]
  rw [prefixWeightRec_four_eq_product]
  unfold lowProduct
  apply Finset.prod_congr rfl
  intro coordinate _
  rw [hexact.2 coordinate]

abbrev TraceRow := AspisV5ProductionRowSelector.TraceRow

def highIndex (row : TraceRow) : Fin 64 :=
  ⟨row.val / 16, by omega⟩

def lowIndex (row : TraceRow) : Fin 16 :=
  ⟨row.val % 16, Nat.mod_lt _ (by omega)⟩

theorem highProduct_eq_sourceHighWeight
    (point : TerminalPoint) (row : TraceRow) :
    highProduct point (highIndex row) =
      AspisV5ProductionRowSelector.sourceHighWeight point row := by
  rfl

theorem lowProduct_eq_sourceLowWeight
    (point : TerminalPoint) (row : TraceRow) :
    lowProduct point (lowIndex row) =
      AspisV5ProductionRowSelector.sourceLowWeight point row := by
  rfl

def rowUsize (row : TraceRow) : Std.Usize :=
  Std.Usize.ofNatCore row.val (by
    have hrow := row.isLt
    rcases System.Platform.numBits_eq with hplatform | hplatform
    · rw [UScalarTy.Usize_numBits_eq, hplatform]
      norm_num at hrow ⊢
      omega
    · rw [UScalarTy.Usize_numBits_eq, hplatform]
      norm_num at hrow ⊢
      omega)

@[simp] theorem rowUsize_val (row : TraceRow) :
    (rowUsize row).val = row.val := by
  rfl

theorem rowUsize_shr_four_val (row : TraceRow) :
    (Std.Usize.wrapping_shr (rowUsize row) 4#u32).val =
      row.val / 16 := by
  unfold Std.Usize.wrapping_shr UScalar.wrapping_shr UScalar.val
  change ((rowUsize row).bv >>>
    (4 % UScalarTy.Usize.numBits)).toNat = row.val / 16
  rw [BitVec.toNat_ushiftRight]
  change (rowUsize row).val >>> (4 % UScalarTy.Usize.numBits) =
    row.val / 16
  rw [rowUsize_val]
  have hmod : 4 % UScalarTy.Usize.numBits = 4 := by
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      norm_num [UScalarTy.Usize_numBits_eq, hplatform]
  rw [hmod, Nat.shiftRight_eq_div_pow]

theorem rowUsize_and_fifteen_val (row : TraceRow) :
    (rowUsize row &&& 15#usize).val = row.val % 16 := by
  rw [UScalar.val_and]
  change row.val &&& 15 = row.val % 16
  simpa using Nat.and_two_pow_sub_one_eq_mod row.val 4

theorem generated_row_corresponds
    (point : TerminalPoint) (selectors : Access.RustSelectors)
    (hhighValid : Access.ArrayValid selectors.high)
    (hlowValid : Access.ArrayValid selectors.low)
    (hhighExact : ∀ index : Fin 64,
      Access.toExact (Access.arrayEntry selectors.high index) =
        highProduct point index)
    (hlowExact : ∀ index : Fin 16,
      Access.toExact (Access.arrayEntry selectors.low index) =
        lowProduct point index)
    (row : TraceRow) :
    ∃ output : Access.RustQM31,
      V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
          selectors (rowUsize row) = .ok output ∧
      Access.ValidQM31 output ∧
      Access.toExact output =
        AspisV5ProductionRowSelector.factoredSourceRowSelector point row := by
  let highScalar := Std.Usize.wrapping_shr (rowUsize row) 4#u32
  let lowScalar := rowUsize row &&& 15#usize
  have hhighVal : highScalar.val = row.val / 16 := by
    exact rowUsize_shr_four_val row
  have hlowVal : lowScalar.val = row.val % 16 := by
    exact rowUsize_and_fifteen_val row
  have hhighBound : highScalar.val < (64#usize : Std.Usize).val := by
    change highScalar.val < 64
    rw [hhighVal]
    omega
  have hlowBound : lowScalar.val < (16#usize : Std.Usize).val := by
    change lowScalar.val < 16
    rw [hlowVal]
    exact Nat.mod_lt _ (by omega)
  have hhighIndex : (⟨highScalar.val, hhighBound⟩ : Fin 64) =
      highIndex row := by
    apply Fin.ext
    exact hhighVal
  have hlowIndex : (⟨lowScalar.val, hlowBound⟩ : Fin 16) =
      lowIndex row := by
    apply Fin.ext
    exact hlowVal
  let highEntry := Access.arrayEntry selectors.high
    (highIndex row)
  let lowEntry := Access.arrayEntry selectors.low
    (lowIndex row)
  have hhighCall : Array.index_usize selectors.high highScalar =
      .ok highEntry := by
    calc
      Array.index_usize selectors.high highScalar =
          .ok (Access.arrayEntry selectors.high
            ⟨highScalar.val, hhighBound⟩) :=
        Access.array_index_call selectors.high highScalar hhighBound
      _ = .ok highEntry := by
        apply congrArg Result.ok
        unfold highEntry
        exact congrArg (Access.arrayEntry selectors.high) hhighIndex
  have hlowCall : Array.index_usize selectors.low lowScalar =
      .ok lowEntry := by
    calc
      Array.index_usize selectors.low lowScalar =
          .ok (Access.arrayEntry selectors.low
            ⟨lowScalar.val, hlowBound⟩) :=
        Access.array_index_call selectors.low lowScalar hlowBound
      _ = .ok lowEntry := by
        apply congrArg Result.ok
        unfold lowEntry
        exact congrArg (Access.arrayEntry selectors.low) hlowIndex
  have hhighEntryValid : Access.ValidQM31 highEntry :=
    hhighValid (highIndex row)
  have hlowEntryValid : Access.ValidQM31 lowEntry :=
    hlowValid (lowIndex row)
  rcases Access.qm31_mul_corresponds highEntry lowEntry
      hhighEntryValid hlowEntryValid with
    ⟨output, hmulCall, houtputValid, houtputExact⟩
  refine ⟨output, ?_, houtputValid, ?_⟩
  · unfold V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
    change (do
      let q ← Array.index_usize selectors.high highScalar
      let q1 ← Array.index_usize selectors.low lowScalar
      V5RowAccessGenerated.aspis_core.field.QM31.mul q q1) = .ok output
    rw [hhighCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hlowCall]
    simp only [Aeneas.Std.bind_tc_ok]
    exact hmulCall
  · rw [houtputExact]
    change
      Access.toExact (Access.arrayEntry selectors.high (highIndex row)) *
        Access.toExact (Access.arrayEntry selectors.low (lowIndex row)) =
      AspisV5ProductionRowSelector.factoredSourceRowSelector point row
    rw [hhighExact, hlowExact, highProduct_eq_sourceHighWeight,
      lowProduct_eq_sourceLowWeight]
    rfl

def zeroAccessQM31 : Access.RustQM31 :=
  { c0 := { a := 0#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def selectorsOfExpanded
    (high : Array Expand.RustQM31 64#usize)
    (low : Array Expand.RustQM31 16#usize) : Access.RustSelectors :=
  { high := expandArrayToAccess high,
    low := expandArrayToAccess low,
    poseidon_block := zeroAccessQM31,
    path_block := zeroAccessQM31 }

/-- For any valid terminal point, the two extracted Rust table builders and
the extracted Rust row lookup return the exact factored selector formula. -/
theorem extracted_expand_and_row_agree
    (point : TerminalPoint)
    (highCoordinates lowCoordinates : Slice Expand.RustQM31)
    (hhighValid : Expand.ValidCoordinates highCoordinates)
    (hlowValid : Expand.ValidCoordinates lowCoordinates)
    (hhighExact : ExactHighCoordinates point highCoordinates)
    (hlowExact : ExactLowCoordinates point lowCoordinates) :
    ∃ high : Array Expand.RustQM31 64#usize,
    ∃ low : Array Expand.RustQM31 16#usize,
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          64#usize highCoordinates = .ok high ∧
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          16#usize lowCoordinates = .ok low ∧
      ∀ row : TraceRow,
        ∃ output : Access.RustQM31,
          V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
              (selectorsOfExpanded high low) (rowUsize row) = .ok output ∧
          Access.ValidQM31 output ∧
          Access.toExact output =
            AspisV5ProductionRowSelector.factoredSourceRowSelector point row := by
  rcases expand_high_exact point highCoordinates hhighValid hhighExact with
    ⟨high, hhighCall, hhighResultValid, hhighResultExact⟩
  rcases expand_low_exact point lowCoordinates hlowValid hlowExact with
    ⟨low, hlowCall, hlowResultValid, hlowResultExact⟩
  have hselectorsHighValid :
      Access.ArrayValid (selectorsOfExpanded high low).high := by
    exact expandArrayToAccess_valid high hhighResultValid
  have hselectorsLowValid :
      Access.ArrayValid (selectorsOfExpanded high low).low := by
    exact expandArrayToAccess_valid low hlowResultValid
  have hselectorsHighExact : ∀ index : Fin 64,
      Access.toExact
          (Access.arrayEntry (selectorsOfExpanded high low).high index) =
        highProduct point index := by
    intro index
    rw [show (selectorsOfExpanded high low).high =
        expandArrayToAccess high by rfl]
    rw [expandArrayToAccess_entry, expandToAccess_exact]
    exact hhighResultExact index
  have hselectorsLowExact : ∀ index : Fin 16,
      Access.toExact
          (Access.arrayEntry (selectorsOfExpanded high low).low index) =
        lowProduct point index := by
    intro index
    rw [show (selectorsOfExpanded high low).low =
        expandArrayToAccess low by rfl]
    rw [expandArrayToAccess_entry, expandToAccess_exact]
    exact hlowResultExact index
  refine ⟨high, low, hhighCall, hlowCall, ?_⟩
  intro row
  exact generated_row_corresponds point (selectorsOfExpanded high low)
    hselectorsHighValid hselectorsLowValid
    hselectorsHighExact hselectorsLowExact row

/-- At a Boolean terminal point, the extracted Rust table construction and
row method return one for the selected physical row and zero for every other
row. -/
theorem generated_row_selects_exactly_one
    (selected : TraceRow)
    (selectors : Access.RustSelectors)
    (hhighValid : Access.ArrayValid selectors.high)
    (hlowValid : Access.ArrayValid selectors.low)
    (hhighExact : ∀ index : Fin 64,
      Access.toExact (Access.arrayEntry selectors.high index) =
        highProduct
          (AspisV5ProductionRowSelector.booleanPointOfRow
            (F := ExactQM31) selected) index)
    (hlowExact : ∀ index : Fin 16,
      Access.toExact (Access.arrayEntry selectors.low index) =
        lowProduct
          (AspisV5ProductionRowSelector.booleanPointOfRow
            (F := ExactQM31) selected) index)
    (row : TraceRow) :
    ∃ output : Access.RustQM31,
      V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
          selectors (rowUsize row) = .ok output ∧
      Access.ValidQM31 output ∧
      Access.toExact output = if row = selected then 1 else 0 := by
  rcases generated_row_corresponds
      (AspisV5ProductionRowSelector.booleanPointOfRow
        (F := ExactQM31) selected)
      selectors hhighValid hlowValid hhighExact hlowExact row with
    ⟨output, hrowCall, houtputValid, houtputExact⟩
  refine ⟨output, hrowCall, houtputValid, ?_⟩
  exact houtputExact.trans
    (AspisV5ProductionRowSelector.factoredSourceRowSelector_at_booleanPoint
      (F := ExactQM31) selected row)

/-- At a Boolean terminal point, the two extracted Rust table builders and
the extracted Rust row method together return one for the selected physical
row and zero for every other row. -/
theorem extracted_expand_and_row_select_exactly_one
    (selected : TraceRow)
    (highCoordinates lowCoordinates : Slice Expand.RustQM31)
    (hhighValid : Expand.ValidCoordinates highCoordinates)
    (hlowValid : Expand.ValidCoordinates lowCoordinates)
    (hhighExact : ExactHighCoordinates
      (AspisV5ProductionRowSelector.booleanPointOfRow
        (F := ExactQM31) selected)
      highCoordinates)
    (hlowExact : ExactLowCoordinates
      (AspisV5ProductionRowSelector.booleanPointOfRow
        (F := ExactQM31) selected)
      lowCoordinates) :
    ∃ high : Array Expand.RustQM31 64#usize,
    ∃ low : Array Expand.RustQM31 16#usize,
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          64#usize highCoordinates = .ok high ∧
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          16#usize lowCoordinates = .ok low ∧
      ∀ row : TraceRow,
        ∃ output : Access.RustQM31,
          V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
              (selectorsOfExpanded high low) (rowUsize row) = .ok output ∧
          Access.ValidQM31 output ∧
          Access.toExact output = if row = selected then 1 else 0 := by
  rcases extracted_expand_and_row_agree
      (AspisV5ProductionRowSelector.booleanPointOfRow
        (F := ExactQM31) selected)
      highCoordinates lowCoordinates hhighValid hlowValid hhighExact hlowExact with
    ⟨high, low, hhighCall, hlowCall, hrows⟩
  refine ⟨high, low, hhighCall, hlowCall, ?_⟩
  intro row
  rcases hrows row with ⟨output, hrowCall, houtputValid, houtputExact⟩
  refine ⟨output, hrowCall, houtputValid, ?_⟩
  exact houtputExact.trans
    (AspisV5ProductionRowSelector.factoredSourceRowSelector_at_booleanPoint
      (F := ExactQM31) selected row)

/-- For an arbitrary valid ten-coordinate point, the source-bound call-site
witness, extracted table builders, and extracted row lookup return the exact
production selector formula. -/
theorem source_bound_at_point_expand_and_row_agree
    (point : TerminalPoint)
    (rustPoint : Array Expand.RustQM31 10#usize)
    (hvalid : ValidTerminalPointRepresentation rustPoint)
    (hexact : ExactTerminalPointRepresentation point rustPoint) :
    ∃ highCoordinates lowCoordinates : Slice Expand.RustQM31,
    ∃ high : Array Expand.RustQM31 64#usize,
    ∃ low : Array Expand.RustQM31 16#usize,
      V5RowCallSiteGenerated.atomic_semantic_selector_coordinate_slices
          rustPoint = .ok (highCoordinates, lowCoordinates) ∧
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          64#usize highCoordinates = .ok high ∧
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          16#usize lowCoordinates = .ok low ∧
      ∀ row : TraceRow,
        ∃ output : Access.RustQM31,
          V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
              (selectorsOfExpanded high low) (rowUsize row) = .ok output ∧
          Access.ValidQM31 output ∧
          Access.toExact output =
            AspisV5ProductionRowSelector.factoredSourceRowSelector point row := by
  rcases generated_coordinate_slices_match_terminal_point
      point rustPoint hvalid hexact with
    ⟨highCoordinates, lowCoordinates, hcall, hhighValid, hlowValid,
      hhighExact, hlowExact⟩
  rcases extracted_expand_and_row_agree point
      highCoordinates lowCoordinates hhighValid hlowValid
      hhighExact hlowExact with
    ⟨high, low, hhighCall, hlowCall, hrows⟩
  exact ⟨highCoordinates, lowCoordinates, high, low, hcall,
    hhighCall, hlowCall, hrows⟩

/-- The source-bound call-site witness removes the two slice premises from the
Boolean-row theorem.  The replay checks that its two expressions are exactly
the two arguments used by production `AtomicSemanticSelectors::at_point`. -/
theorem source_bound_at_point_expand_and_row_select_exactly_one
    (selected : TraceRow)
    (rustPoint : Array Expand.RustQM31 10#usize)
    (hvalid : ValidTerminalPointRepresentation rustPoint)
    (hexact : ExactTerminalPointRepresentation
      (AspisV5ProductionRowSelector.booleanPointOfRow
        (F := ExactQM31) selected)
      rustPoint) :
    ∃ highCoordinates lowCoordinates : Slice Expand.RustQM31,
    ∃ high : Array Expand.RustQM31 64#usize,
    ∃ low : Array Expand.RustQM31 16#usize,
      V5RowCallSiteGenerated.atomic_semantic_selector_coordinate_slices
          rustPoint = .ok (highCoordinates, lowCoordinates) ∧
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          64#usize highCoordinates = .ok high ∧
      V5RowExpandGenerated.atomic_state_only_terminal.AtomicSelectors.expand
          16#usize lowCoordinates = .ok low ∧
      ∀ row : TraceRow,
        ∃ output : Access.RustQM31,
          V5RowAccessGenerated.atomic_state_only_terminal.AtomicSemanticSelectors.row
              (selectorsOfExpanded high low) (rowUsize row) = .ok output ∧
          Access.ValidQM31 output ∧
          Access.toExact output = if row = selected then 1 else 0 := by
  rcases generated_coordinate_slices_match_terminal_point
      (AspisV5ProductionRowSelector.booleanPointOfRow
        (F := ExactQM31) selected)
      rustPoint hvalid hexact with
    ⟨highCoordinates, lowCoordinates, hcall, hhighValid, hlowValid,
      hhighExact, hlowExact⟩
  rcases extracted_expand_and_row_select_exactly_one selected
      highCoordinates lowCoordinates hhighValid hlowValid
      hhighExact hlowExact with
    ⟨high, low, hhighCall, hlowCall, hrows⟩
  exact ⟨highCoordinates, lowCoordinates, high, low, hcall,
    hhighCall, hlowCall, hrows⟩

#print axioms Expand.expand_exact_spec
#print axioms Access.qm31_mul_corresponds
#print axioms generated_row_corresponds
#print axioms extracted_expand_and_row_agree
#print axioms generated_row_selects_exactly_one
#print axioms extracted_expand_and_row_select_exactly_one
#print axioms generated_coordinate_slices_exact
#print axioms generated_coordinate_slices_match_terminal_point
#print axioms source_bound_at_point_expand_and_row_agree
#print axioms source_bound_at_point_expand_and_row_select_exactly_one

end Composition

end AspisV5RowSelectorImplementationProof
