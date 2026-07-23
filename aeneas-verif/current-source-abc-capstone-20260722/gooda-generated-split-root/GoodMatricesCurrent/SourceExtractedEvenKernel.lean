import GoodMatricesCurrent.Funs
import GoodMatricesCurrent.SourceExtractedField
import AspisFormal.V5GoodGateSparseShift
import AspisFormal.V5ComponentCQM31RustFormulaSeam
import AspisFormal.V5M31RawMulReduction
import Aeneas.Tactic.Step.DspecInduction

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedEvenKernel

open AspisV5GoodGateSparseShift
open AspisV5M31RawMulReduction

private abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
private abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
private abbrev LocalVector := Array LocalM31 48#usize
private abbrev LocalKernel := Array LocalM31 37#usize

/-- Source binding for the exact Rust file represented by this extraction. -/
def sourceSha256 : String :=
  "1f738fd666b1ea4fcf57e0f1571e7ed32875fb5906a1870329742e3e5e61d251"

def m31ToExact (value : LocalM31) : ExactM31 := value.val

def CanonicalLocalM31 (value : LocalM31) : Prop :=
  value.val < AspisV5ComponentCQM31TowerExact.P

def arrayEntry48 (values : LocalVector) (index : Fin 48) : LocalM31 :=
  values.val[index.val]'(by
    rw [values.property]
    simpa using index.isLt)

def arrayToExact48 (values : LocalVector) : Fin 48 → ExactM31 :=
  fun index ↦ m31ToExact (arrayEntry48 values index)

def CanonicalLocalVector (values : LocalVector) : Prop :=
  ∀ index : Fin 48, CanonicalLocalM31 (arrayEntry48 values index)

def CanonicalLocalKernel (kernel : LocalKernel) : Prop :=
  ∀ index : Fin 37,
    CanonicalLocalM31
      (kernel.val[index.val]'(by rw [kernel.property]; exact index.isLt))

def evenKernelOrdinary (kernel : Array Std.U32 37#usize) :
    Fin 48 → ExactM31 :=
  fun degree ↦
    if hdegree : degree.val < 37 then
      if degree.val % 2 = 0 then
        (kernel.val[degree.val]'(by
          rw [kernel.property]
          exact hdegree)).val
      else 0
    else 0

private def parityTableEntry (row column : Fin 24) : Std.U32 :=
  let table := v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY
  let tableRow := table.val[row.val]'(by
    rw [table.property]
    simpa using row.isLt)
  tableRow.val[column.val]'(by
    rw [tableRow.property]
    simpa using column.isLt)

private def parityTableExact (row column : Fin 24) : ExactM31 :=
  (parityTableEntry row column).val

private def usedParityRow0 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    1#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow1 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    1073741824#u32, 1073741824#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow2 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    805306368#u32, 1073741824#u32, 268435456#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow3 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    671088640#u32, 939524096#u32, 402653184#u32, 134217728#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow4 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    587202560#u32, 805306368#u32, 469762048#u32, 268435456#u32, 16777216#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow5 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    528482304#u32, 696254464#u32, 503316480#u32, 369098752#u32, 41943040#u32, 8388608#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow6 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    484442112#u32, 612368384#u32, 517996544#u32, 436207616#u32, 69206016#u32, 25165824#u32,
    2097152#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow7 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    449839104#u32, 548405248#u32, 521142272#u32, 477102080#u32, 95420416#u32, 47185920#u32,
    7340032#u32, 1048576#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow8 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    421724160#u32, 499122176#u32, 516947968#u32, 499122176#u32, 119275520#u32, 71303168#u32,
    15728640#u32, 4194304#u32, 65536#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow9 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    398295040#u32, 460423168#u32, 508035072#u32, 508035072#u32, 140378112#u32, 95289344#u32,
    26738688#u32, 9961472#u32, 294912#u32, 32768#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow10 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    378380288#u32, 429359104#u32, 496132096#u32, 508035072#u32, 158760960#u32, 117833728#u32,
    39682048#u32, 18350080#u32, 778240#u32, 163840#u32, 8192#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow11 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    361181184#u32, 403869696#u32, 482414592#u32, 502083584#u32, 174637056#u32, 138297344#u32,
    53886976#u32, 29016064#u32, 1576960#u32, 471040#u32, 45056#u32, 4096#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow12 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    346131968#u32, 382525440#u32, 467695616#u32, 492249088#u32, 188280320#u32, 156467200#u32,
    68771840#u32, 41451520#u32, 2720256#u32, 1024000#u32, 141312#u32, 24576#u32,
    512#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow13 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    332819200#u32, 364328704#u32, 452541440#u32, 479972352#u32, 199969536#u32, 172373760#u32,
    83865600#u32, 55111680#u32, 4209920#u32, 1872128#u32, 332800#u32, 82944#u32,
    3328#u32, 256#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow14 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    320932800#u32, 348573952#u32, 437345984#u32, 466256896#u32, 209963712#u32, 186171648#u32,
    98804160#u32, 69488640#u32, 6027840#u32, 3041024#u32, 655168#u32, 207872#u32,
    12096#u32, 1792#u32, 64#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow15 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    310235040#u32, 334753376#u32, 422380704#u32, 451801440#u32, 218492960#u32, 198067680#u32,
    113317152#u32, 84146400#u32, 8143200#u32, 4534432#u32, 1139808#u32, 431520#u32,
    32480#u32, 6944#u32, 480#u32, 32#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow16 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    300540195#u32, 322494208#u32, 407829056#u32, 437091072#u32, 225756880#u32, 208280320#u32,
    127212096#u32, 98731776#u32, 10518300#u32, 6338816#u32, 1811392#u32, 785664#u32,
    71920#u32, 19712#u32, 1984#u32, 256#u32, 1#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow17 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    1365442601#u32, 1385259025#u32, 393810848#u32, 422460064#u32, 231926376#u32, 217018600#u32,
    140359072#u32, 112971936#u32, 13112814#u32, 8428558#u32, 2686816#u32, 1298528#u32,
    139128#u32, 45816#u32, 5984#u32, 1120#u32, 1073741832#u32, 1073741824#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityRow18 : Array Std.U32 24#usize :=
  Array.make 24#usize [
    552033434#u32, 1375350813#u32, 1185706108#u32, 408135456#u32, 237146838#u32, 224472488#u32,
    152677170#u32, 126665504#u32, 1089628502#u32, 10770686#u32, 1077517003#u32, 1992672#u32,
    243474#u32, 92472#u32, 14726#u32, 3552#u32, 805306407#u32, 1073741828#u32,
    268435456#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
  ]

private def usedParityTable : Array (Array Std.U32 24#usize) 19#usize :=
  Array.make 19#usize [
    usedParityRow0, usedParityRow1, usedParityRow2, usedParityRow3, usedParityRow4,
    usedParityRow5, usedParityRow6, usedParityRow7, usedParityRow8, usedParityRow9,
    usedParityRow10, usedParityRow11, usedParityRow12, usedParityRow13, usedParityRow14,
    usedParityRow15, usedParityRow16, usedParityRow17, usedParityRow18
  ]

private def usedParityRow (row : Fin 19) : Array Std.U32 24#usize :=
  match row.val with
  | 0 => usedParityRow0
  | 1 => usedParityRow1
  | 2 => usedParityRow2
  | 3 => usedParityRow3
  | 4 => usedParityRow4
  | 5 => usedParityRow5
  | 6 => usedParityRow6
  | 7 => usedParityRow7
  | 8 => usedParityRow8
  | 9 => usedParityRow9
  | 10 => usedParityRow10
  | 11 => usedParityRow11
  | 12 => usedParityRow12
  | 13 => usedParityRow13
  | 14 => usedParityRow14
  | 15 => usedParityRow15
  | 16 => usedParityRow16
  | 17 => usedParityRow17
  | _ => usedParityRow18

private def usedParityEntry (row : Fin 19) (column : Fin 24) : Std.U32 :=
  let tableRow := usedParityRow row
  tableRow.val[column.val]'(by
    rw [tableRow.property]
    exact column.isLt)

private def usedRowIndex (row : Fin 19) : Fin 24 :=
  ⟨row.val, by omega⟩

private theorem parityTableEntry_used (row : Fin 19) (column : Fin 24) :
    parityTableEntry ⟨row.val, by omega⟩ column = usedParityEntry row column := by
  unfold parityTableEntry usedParityEntry usedParityRow
  unfold usedParityRow0 usedParityRow1 usedParityRow2 usedParityRow3 usedParityRow4 usedParityRow5 usedParityRow6 usedParityRow7 usedParityRow8 usedParityRow9 usedParityRow10 usedParityRow11 usedParityRow12 usedParityRow13 usedParityRow14 usedParityRow15 usedParityRow16 usedParityRow17 usedParityRow18
  unfold v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY
  fin_cases row <;> rfl

private theorem parityTableExact_used (row : Fin 19) (column : Fin 24) :
    parityTableExact (usedRowIndex row) column =
      (usedParityEntry row column).val := by
  unfold parityTableExact
  unfold usedRowIndex
  rw [parityTableEntry_used]

private theorem usedParityEntry_zero_zero :
    usedParityEntry (0 : Fin 19) (0 : Fin 24) = 1#u32 := by
  rfl

private theorem usedParityEntry_one_zero :
    usedParityEntry (1 : Fin 19) (0 : Fin 24) = 1073741824#u32 := by
  rfl

private theorem usedParityEntry_one_one :
    usedParityEntry (1 : Fin 19) (1 : Fin 24) = 1073741824#u32 := by
  rfl

private theorem parityTableExact_zero_zero :
    parityTableExact (usedRowIndex (0 : Fin 19)) (0 : Fin 24) =
      (1 : ExactM31) := by
  have hsource := parityTableExact_used (0 : Fin 19) (0 : Fin 24)
  change parityTableExact (usedRowIndex (0 : Fin 19)) (0 : Fin 24) = _
  rw [hsource, usedParityEntry_zero_zero]
  rfl




private def parityRow (degreeHalf : Fin 19) : Fin 48 → ExactM31 :=
  fun coordinate ↦
    if coordinate.val % 2 = 0 then
      let naturalHalf := coordinate.val / 2
      if naturalHalf ≤ degreeHalf.val then
        parityTableExact (usedRowIndex degreeHalf)
          ⟨naturalHalf, by omega⟩
      else 0
    else 0

private theorem parityRow_zero :
    parityRow (0 : Fin 19) =
      Pi.single (0 : Fin 48) (1 : ExactM31) := by
  funext coordinate
  by_cases hzero : coordinate = (0 : Fin 48)
  · subst coordinate
    simp [parityRow, parityTableExact_zero_zero]
  · have hleft : parityRow (0 : Fin 19) coordinate = 0 := by
      unfold parityRow
      by_cases heven : coordinate.val % 2 = 0
      · rw [if_pos heven]
        dsimp only
        have hhalf : ¬ coordinate.val / 2 ≤ (0 : Fin 19).val := by
          intro hle
          apply hzero
          apply Fin.ext
          omega
        rw [if_neg hhalf]
      · rw [if_neg heven]
    rw [hleft]
    simp [Pi.single_apply, hzero]

private theorem sourceCoefficients_single (index : Fin 47)
    (coefficient : ExactM31) :
    (fun source : Fin 47 =>
      (Pi.single (sourceIndex index) coefficient : Fin 48 → ExactM31)
        (sourceIndex source)) =
      Pi.single index coefficient := by
  classical
  funext source
  simp [sourceIndex, Pi.single_apply, Fin.ext_iff]

private theorem sparseShift_single (index : Fin 47)
    (coefficient : ExactM31) :
    sparseShift
        (Pi.single (sourceIndex index) coefficient : Fin 48 → ExactM31) =
      coefficient • sparseBasis index := by
  classical
  unfold sparseShift
  rw [sourceCoefficients_single, Fintype.linearCombination_apply_single]

private noncomputable def sourceRestriction :
    (Fin 48 → ExactM31) →ₗ[ExactM31] (Fin 47 → ExactM31) where
  toFun input := fun index => input (sourceIndex index)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sparseShift_linearCombination {ι : Type*} [Fintype ι]
    (vectors : ι → Fin 48 → ExactM31) (coefficients : ι → ExactM31) :
    sparseShift (Fintype.linearCombination ExactM31 vectors coefficients) =
      Fintype.linearCombination ExactM31
        (fun index => sparseShift (vectors index)) coefficients := by
  unfold sparseShift
  change
    (Fintype.linearCombination ExactM31 (sparseBasis (K := ExactM31)))
        (sourceRestriction
          (Fintype.linearCombination ExactM31 vectors coefficients)) =
      Fintype.linearCombination ExactM31
        (fun index =>
          (Fintype.linearCombination ExactM31
            (sparseBasis (K := ExactM31)))
            (sourceRestriction (vectors index))) coefficients
  rw [map_fintypeLinearCombination sourceRestriction vectors coefficients]
  exact map_fintypeLinearCombination
    (Fintype.linearCombination ExactM31 (sparseBasis (K := ExactM31)))
    (fun index => sourceRestriction (vectors index)) coefficients

private def evenSource (index : Fin 19) : Fin 47 :=
  ⟨2 * index.val, by omega⟩

private def oddSource (index : Fin 19) : Fin 47 :=
  ⟨2 * index.val + 1, by omega⟩

private def evenBasis (index : Fin 19) : Fin 48 → ExactM31 :=
  Pi.single (sourceIndex (evenSource index)) 1

private theorem sparseShift_evenBasis (index : Fin 19) :
    sparseShift (evenBasis index) =
      Pi.single (sourceIndex (oddSource index)) (1 : ExactM31) := by
  rw [evenBasis, sparseShift_single]
  simp [sparseBasis, evenSource, oddSource, successorIndex, sourceIndex]

private theorem sparseShift_twice_evenBasis (index : Fin 19) :
    sparseShift (sparseShift (evenBasis index)) =
      sparseBasis (oddSource index) := by
  rw [sparseShift_evenBasis, sparseShift_single]
  simp

private def parityCoefficient (degreeHalf index : Fin 19) : ExactM31 :=
  if index.val ≤ degreeHalf.val then
    parityTableExact (usedRowIndex degreeHalf) ⟨index.val, by omega⟩
  else 0

private theorem parityRow_eq_linearCombination (degreeHalf : Fin 19) :
    parityRow degreeHalf =
      Fintype.linearCombination ExactM31 evenBasis
        (parityCoefficient degreeHalf) := by
  classical
  funext coordinate
  simp only [Fintype.linearCombination_apply, Fintype.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases heven : coordinate.val % 2 = 0
  · by_cases hhalf : coordinate.val / 2 < 19
    · let index : Fin 19 := ⟨coordinate.val / 2, hhalf⟩
      have hdouble : 2 * (coordinate.val / 2) = coordinate.val := by omega
      have htarget : sourceIndex (evenSource index) = coordinate := by
        apply Fin.ext
        simp [sourceIndex, evenSource, index, hdouble]
      rw [Fintype.sum_eq_single index]
      · simp [parityRow, heven, parityCoefficient, evenBasis, htarget, index]
      · intro other hne
        have htargetNe : sourceIndex (evenSource other) ≠ coordinate := by
          intro equal
          apply hne
          apply Fin.ext
          have hvalue := congrArg Fin.val equal
          simp [sourceIndex, evenSource, index, hdouble] at hvalue ⊢
          omega
        simp [evenBasis, htargetNe]
    · have habove : ¬ coordinate.val / 2 ≤ degreeHalf.val := by omega
      rw [show parityRow degreeHalf coordinate = 0 by
        simp [parityRow, heven, habove]]
      have hzero : ∀ index : Fin 19, evenBasis index coordinate = 0 := by
        intro index
        have htargetNe : sourceIndex (evenSource index) ≠ coordinate := by
          intro equal
          have hvalue := congrArg Fin.val equal
          simp [sourceIndex, evenSource] at hvalue
          omega
        simp [evenBasis, htargetNe]
      simp_rw [hzero]
      simp
  · rw [show parityRow degreeHalf coordinate = 0 by simp [parityRow, heven]]
    have hzero : ∀ index : Fin 19, evenBasis index coordinate = 0 := by
      intro index
      have htargetNe : sourceIndex (evenSource index) ≠ coordinate := by
        intro equal
        have hvalue := congrArg Fin.val equal
        simp [sourceIndex, evenSource] at hvalue
        omega
      simp [evenBasis, htargetNe]
    simp_rw [hzero]
    simp

private theorem sparseShift_twice_parityRow (degreeHalf : Fin 19) :
    sparseShift (sparseShift (parityRow degreeHalf)) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient degreeHalf) := by
  rw [parityRow_eq_linearCombination,
    sparseShift_linearCombination, sparseShift_linearCombination]
  apply fintypeLinearCombination_congr
  intro index
  exact sparseShift_twice_evenBasis index

private theorem parityCoefficient_zero :
    parityCoefficient (0 : Fin 19) =
      Pi.single (0 : Fin 19) (1 : ExactM31) := by
  funext index
  fin_cases index
  · simp only [parityCoefficient, Fin.isValue, le_refl, ↓reduceIte,
      Pi.single_eq_same]
    have hsource := parityTableExact_used (0 : Fin 19) (0 : Fin 24)
    change parityTableExact (usedRowIndex (0 : Fin 19)) (0 : Fin 24) = _
    rw [hsource, usedParityEntry_zero_zero]
    rfl
  all_goals norm_num [parityCoefficient, Pi.single_apply, Fin.ext_iff]

private def rowOneVector : Fin 48 → ExactM31 :=
  Pi.single (0 : Fin 48) (1073741824 : ExactM31) +
    Pi.single (2 : Fin 48) (1073741824 : ExactM31)

private theorem exactHalf_eq_literal :
    (2 : ExactM31)⁻¹ = (1073741824 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

@[simp] private theorem trailingOnes_one : trailingOnes 1 = 1 := by
  calc
    trailingOnes 1 = 1 + trailingOnes 0 :=
      trailingOnes_two_mul_add_one 0
    _ = 1 := by rw [trailingOnes_of_even 0 (by omega)]

@[simp] private theorem trailingOnes_three : trailingOnes 3 = 2 := by
  calc
    trailingOnes 3 = 1 + trailingOnes 1 :=
      trailingOnes_two_mul_add_one 1
    _ = 2 := by rw [trailingOnes_one]

@[simp] private theorem trailingOnes_five : trailingOnes 5 = 1 := by
  calc
    trailingOnes 5 = 1 + trailingOnes 2 :=
      trailingOnes_two_mul_add_one 2
    _ = 1 := by rw [trailingOnes_of_even 2 (by omega)]

@[simp] private theorem trailingOnes_seven : trailingOnes 7 = 3 := by
  calc
    trailingOnes 7 = 1 + trailingOnes 3 :=
      trailingOnes_two_mul_add_one 3
    _ = 3 := by rw [trailingOnes_three]

@[simp] private theorem trailingOnes_nine : trailingOnes 9 = 1 := by
  calc
    trailingOnes 9 = 1 + trailingOnes 4 :=
      trailingOnes_two_mul_add_one 4
    _ = 1 := by rw [trailingOnes_of_even 4 (by omega)]

@[simp] private theorem trailingOnes_eleven : trailingOnes 11 = 2 := by
  calc
    trailingOnes 11 = 1 + trailingOnes 5 :=
      trailingOnes_two_mul_add_one 5
    _ = 2 := by rw [trailingOnes_five]

@[simp] private theorem trailingOnes_thirteen : trailingOnes 13 = 1 := by
  calc
    trailingOnes 13 = 1 + trailingOnes 6 :=
      trailingOnes_two_mul_add_one 6
    _ = 1 := by rw [trailingOnes_of_even 6 (by omega)]

@[simp] private theorem trailingOnes_fifteen : trailingOnes 15 = 4 := by
  calc
    trailingOnes 15 = 1 + trailingOnes 7 :=
      trailingOnes_two_mul_add_one 7
    _ = 4 := by rw [trailingOnes_seven]

@[simp] private theorem trailingOnes_seventeen : trailingOnes 17 = 1 := by
  calc
    trailingOnes 17 = 1 + trailingOnes 8 :=
      trailingOnes_two_mul_add_one 8
    _ = 1 := by rw [trailingOnes_of_even 8 (by omega)]

@[simp] private theorem trailingOnes_nineteen : trailingOnes 19 = 2 := by
  calc
    trailingOnes 19 = 1 + trailingOnes 9 :=
      trailingOnes_two_mul_add_one 9
    _ = 2 := by rw [trailingOnes_nine]

@[simp] private theorem trailingOnes_twenty_one : trailingOnes 21 = 1 := by
  calc
    trailingOnes 21 = 1 + trailingOnes 10 :=
      trailingOnes_two_mul_add_one 10
    _ = 1 := by rw [trailingOnes_of_even 10 (by omega)]

@[simp] private theorem trailingOnes_twenty_three : trailingOnes 23 = 3 := by
  calc
    trailingOnes 23 = 1 + trailingOnes 11 :=
      trailingOnes_two_mul_add_one 11
    _ = 3 := by rw [trailingOnes_eleven]

@[simp] private theorem trailingOnes_twenty_five : trailingOnes 25 = 1 := by
  calc
    trailingOnes 25 = 1 + trailingOnes 12 :=
      trailingOnes_two_mul_add_one 12
    _ = 1 := by rw [trailingOnes_of_even 12 (by omega)]

@[simp] private theorem trailingOnes_twenty_seven : trailingOnes 27 = 2 := by
  calc
    trailingOnes 27 = 1 + trailingOnes 13 :=
      trailingOnes_two_mul_add_one 13
    _ = 2 := by rw [trailingOnes_thirteen]

@[simp] private theorem trailingOnes_twenty_nine : trailingOnes 29 = 1 := by
  calc
    trailingOnes 29 = 1 + trailingOnes 14 :=
      trailingOnes_two_mul_add_one 14
    _ = 1 := by rw [trailingOnes_of_even 14 (by omega)]

@[simp] private theorem trailingOnes_thirty_one : trailingOnes 31 = 5 := by
  calc
    trailingOnes 31 = 1 + trailingOnes 15 :=
      trailingOnes_two_mul_add_one 15
    _ = 5 := by rw [trailingOnes_fifteen]

@[simp] private theorem trailingOnes_thirty_three : trailingOnes 33 = 1 := by
  calc
    trailingOnes 33 = 1 + trailingOnes 16 :=
      trailingOnes_two_mul_add_one 16
    _ = 1 := by rw [trailingOnes_of_even 16 (by omega)]

@[simp] private theorem trailingOnes_thirty_five : trailingOnes 35 = 2 := by
  calc
    trailingOnes 35 = 1 + trailingOnes 17 :=
      trailingOnes_two_mul_add_one 17
    _ = 2 := by rw [trailingOnes_seventeen]

@[simp] private theorem trailingOnes_thirty_seven : trailingOnes 37 = 1 := by
  calc
    trailingOnes 37 = 1 + trailingOnes 18 :=
      trailingOnes_two_mul_add_one 18
    _ = 1 := by rw [trailingOnes_of_even 18 (by omega)]

private def oddCount (index : Fin 19) : Nat :=
  match index.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 3
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 4
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 3
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 5
  | 16 => 1
  | 17 => 2
  | _ => 1

private theorem trailingOnes_oddSource (index : Fin 19) :
    trailingOnes (oddSource index).val = oddCount index := by
  fin_cases index <;>
    simp [oddSource, oddCount]

private theorem parityTableExact_one_zero :
    parityTableExact (usedRowIndex (1 : Fin 19)) (0 : Fin 24) =
      (1073741824 : ExactM31) := by
  have hsource := parityTableExact_used (1 : Fin 19) (0 : Fin 24)
  change parityTableExact (usedRowIndex (1 : Fin 19)) (0 : Fin 24) = _
  rw [hsource, usedParityEntry_one_zero]
  rfl

private theorem parityTableExact_one_one :
    parityTableExact (usedRowIndex (1 : Fin 19)) (1 : Fin 24) =
      (1073741824 : ExactM31) := by
  have hsource := parityTableExact_used (1 : Fin 19) (1 : Fin 24)
  change parityTableExact (usedRowIndex (1 : Fin 19)) (1 : Fin 24) = _
  rw [hsource, usedParityEntry_one_one]
  rfl

private theorem parityTableExact_two_zero :
    parityTableExact (usedRowIndex (2 : Fin 19)) (0 : Fin 24) =
      (805306368 : ExactM31) := by
  have hsource := parityTableExact_used (2 : Fin 19) (0 : Fin 24)
  change parityTableExact (usedRowIndex (2 : Fin 19)) (0 : Fin 24) = _
  rw [hsource]
  rfl

private theorem parityTableExact_two_one :
    parityTableExact (usedRowIndex (2 : Fin 19)) (1 : Fin 24) =
      (1073741824 : ExactM31) := by
  have hsource := parityTableExact_used (2 : Fin 19) (1 : Fin 24)
  change parityTableExact (usedRowIndex (2 : Fin 19)) (1 : Fin 24) = _
  rw [hsource]
  rfl

private theorem parityTableExact_two_two :
    parityTableExact (usedRowIndex (2 : Fin 19)) (2 : Fin 24) =
      (268435456 : ExactM31) := by
  have hsource := parityTableExact_used (2 : Fin 19) (2 : Fin 24)
  change parityTableExact (usedRowIndex (2 : Fin 19)) (2 : Fin 24) = _
  rw [hsource]
  rfl

private theorem parityRow_one_vector :
    parityRow (1 : Fin 19) = rowOneVector := by
  funext coordinate
  by_cases hzero : coordinate = (0 : Fin 48)
  · subst coordinate
    simp [parityRow, rowOneVector, parityTableExact_one_zero,
      Pi.single_apply, Fin.ext_iff]
  · by_cases htwo : coordinate = (2 : Fin 48)
    · subst coordinate
      simp [parityRow, rowOneVector, parityTableExact_one_one,
        Pi.single_apply, Fin.ext_iff]
    · have houtside : parityRow (1 : Fin 19) coordinate = 0 := by
        unfold parityRow
        by_cases heven : coordinate.val % 2 = 0
        · rw [if_pos heven]
          dsimp only
          by_cases hhalf : coordinate.val / 2 ≤ 1
          · have hcoordinate : coordinate.val = 0 ∨ coordinate.val = 2 := by
              omega
            rcases hcoordinate with hcoordinate | hcoordinate
            · exact (hzero (Fin.ext hcoordinate)).elim
            · exact (htwo (Fin.ext hcoordinate)).elim
          · have hhalf' : ¬ coordinate.val / 2 ≤ (1 : Fin 19).val := by
              simpa using hhalf
            rw [if_neg hhalf']
        · rw [if_neg heven]
      rw [houtside]
      simp [rowOneVector, Pi.single_apply, hzero, htwo, Fin.ext_iff]

private theorem sparseBasis_oddSource_zero :
    sparseBasis (oddSource (0 : Fin 19)) = rowOneVector := by
  rw [show oddSource (0 : Fin 19) = (1 : Fin 47) by rfl]
  unfold sparseBasis
  rw [if_neg (by norm_num)]
  dsimp only
  rw [show trailingOnes ((1 : Fin 47) : Nat) = 1 by
    exact trailingOnes_one]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change
    Pi.single (2 : Fin 48) ((2 : ExactM31)⁻¹) +
        Pi.single (0 : Fin 48) ((2 : ExactM31)⁻¹) = rowOneVector
  rw [exactHalf_eq_literal]
  unfold rowOneVector
  ac_rfl

private def oddOneVector : Fin 48 → ExactM31 :=
  Pi.single (4 : Fin 48) (536870912 : ExactM31) +
    Pi.single (2 : Fin 48) (1073741824 : ExactM31) +
      Pi.single (0 : Fin 48) (536870912 : ExactM31)

private theorem exactQuarter_eq_literal :
    (4 : ExactM31)⁻¹ = (536870912 : ExactM31) := by
  apply ZMod.inv_eq_of_mul_eq_one
  decide

private def dyadicLiteral : Nat → ExactM31
  | 0 => 1
  | 1 => 1073741824
  | 2 => 536870912
  | 3 => 268435456
  | 4 => 134217728
  | 5 => 67108864
  | _ => 0

@[simp] private theorem dyadic_one_literal :
    dyadic (K := ExactM31) 1 = dyadicLiteral 1 := by
  rw [show 1 = 0 + 1 by omega, dyadic_succ, dyadic_zero,
    exactHalf_eq_literal]
  rfl

@[simp] private theorem dyadic_two_literal :
    dyadic (K := ExactM31) 2 = dyadicLiteral 2 := by
  rw [show 2 = 1 + 1 by omega, dyadic_succ, dyadic_one_literal,
    exactHalf_eq_literal]
  decide

@[simp] private theorem dyadic_three_literal :
    dyadic (K := ExactM31) 3 = dyadicLiteral 3 := by
  rw [show 3 = 2 + 1 by omega, dyadic_succ, dyadic_two_literal,
    exactHalf_eq_literal]
  decide

@[simp] private theorem dyadic_four_literal :
    dyadic (K := ExactM31) 4 = dyadicLiteral 4 := by
  rw [show 4 = 3 + 1 by omega, dyadic_succ, dyadic_three_literal,
    exactHalf_eq_literal]
  decide

@[simp] private theorem dyadic_five_literal :
    dyadic (K := ExactM31) 5 = dyadicLiteral 5 := by
  rw [show 5 = 4 + 1 by omega, dyadic_succ, dyadic_four_literal,
    exactHalf_eq_literal]
  decide

private theorem dyadic_eq_literal (count : Nat) (hcount : count ≤ 5) :
    dyadic (K := ExactM31) count = dyadicLiteral count := by
  have hcases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨
      count = 4 ∨ count = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact dyadic_zero
  · exact dyadic_one_literal
  · exact dyadic_two_literal
  · exact dyadic_three_literal
  · exact dyadic_four_literal
  · exact dyadic_five_literal

private def literalSparseOdd (index : Fin 19) :
    Fin 48 → ExactM31 :=
  Pi.single (successorIndex (oddSource index)) (dyadicLiteral (oddCount index)) +
    ∑ carry ∈ Finset.range (oddCount index),
      Pi.single (carryIndex (oddSource index) (carry + 1))
        (dyadicLiteral (carry + 1))

private theorem oddCount_le_five (index : Fin 19) : oddCount index ≤ 5 := by
  fin_cases index <;> decide

private theorem sparseBasis_oddSource_literal (index : Fin 19) :
    sparseBasis (oddSource index) = literalSparseOdd index := by
  unfold sparseBasis literalSparseOdd
  rw [if_neg (by simp [oddSource])]
  dsimp only
  rw [trailingOnes_oddSource,
    dyadic_eq_literal (oddCount index) (oddCount_le_five index)]
  congr 1
  apply Finset.sum_congr rfl
  intro carry hcarry
  rw [dyadic_eq_literal]
  have hcarryBound : carry < oddCount index := Finset.mem_range.mp hcarry
  have hcountBound := oddCount_le_five index
  omega

private theorem sparseBasis_oddSource_family :
    (fun index : Fin 19 => sparseBasis (oddSource index)) =
      literalSparseOdd := by
  funext index
  exact sparseBasis_oddSource_literal index

private theorem sparseBasis_oddSource_one :
    sparseBasis (oddSource (1 : Fin 19)) = oddOneVector := by
  rw [show oddSource (1 : Fin 19) = (3 : Fin 47) by rfl]
  unfold sparseBasis
  rw [if_neg (by norm_num)]
  dsimp only
  rw [show trailingOnes ((3 : Fin 47) : Nat) = 2 by
    exact trailingOnes_three]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change
    Pi.single (4 : Fin 48) ((4 : ExactM31)⁻¹) +
        (Pi.single (2 : Fin 48) ((2 : ExactM31)⁻¹) +
          Pi.single (0 : Fin 48) ((4 : ExactM31)⁻¹)) = oddOneVector
  rw [exactHalf_eq_literal, exactQuarter_eq_literal]
  unfold oddOneVector
  ac_rfl

private theorem parityRow_one :
    parityRow (1 : Fin 19) = sparseBasis (oddSource (0 : Fin 19)) := by
  rw [parityRow_one_vector, sparseBasis_oddSource_zero]

private theorem parityRow_step_factored_0 :
    parityRow (1 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (0 : Fin 19)) := by
  rw [parityCoefficient_zero, Fintype.linearCombination_apply_single]
  simpa using parityRow_one

private theorem parityCoefficient_one :
    parityCoefficient (1 : Fin 19) =
      Pi.single (0 : Fin 19) (1073741824 : ExactM31) +
        Pi.single (1 : Fin 19) (1073741824 : ExactM31) := by
  funext index
  fin_cases index <;>
    norm_num [parityCoefficient, parityTableExact_one_zero,
      parityTableExact_one_one,
      Pi.single_apply, Fin.ext_iff]
  all_goals rfl

private def rowTwoVector : Fin 48 → ExactM31 :=
  Pi.single (0 : Fin 48) (805306368 : ExactM31) +
    Pi.single (2 : Fin 48) (1073741824 : ExactM31) +
      Pi.single (4 : Fin 48) (268435456 : ExactM31)

private theorem parityRow_two_vector :
    parityRow (2 : Fin 19) = rowTwoVector := by
  funext coordinate
  by_cases hzero : coordinate = (0 : Fin 48)
  · subst coordinate
    simp [parityRow, rowTwoVector, parityTableExact_two_zero]
  · by_cases htwo : coordinate = (2 : Fin 48)
    · subst coordinate
      simp [parityRow, rowTwoVector, parityTableExact_two_one]
    · by_cases hfour : coordinate = (4 : Fin 48)
      · subst coordinate
        simp [parityRow, rowTwoVector, parityTableExact_two_two]
      · have hleft : parityRow (2 : Fin 19) coordinate = 0 := by
          unfold parityRow
          by_cases heven : coordinate.val % 2 = 0
          · rw [if_pos heven]
            dsimp only
            have hhalf : ¬ coordinate.val / 2 ≤ (2 : Fin 19).val := by
              intro hle
              have hcoordinate : coordinate.val = 0 ∨ coordinate.val = 2 ∨
                  coordinate.val = 4 := by omega
              rcases hcoordinate with hcoordinate | hcoordinate | hcoordinate
              · exact hzero (Fin.ext hcoordinate)
              · exact htwo (Fin.ext hcoordinate)
              · exact hfour (Fin.ext hcoordinate)
            rw [if_neg hhalf]
          · rw [if_neg heven]
        rw [hleft]
        simp [rowTwoVector, Pi.single_apply, hzero, htwo, hfour]

private theorem rowTwoVector_factored :
    rowTwoVector =
      (1073741824 : ExactM31) • rowOneVector +
        (1073741824 : ExactM31) • oddOneVector := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [rowTwoVector, rowOneVector, oddOneVector, Pi.single_apply,
      Fin.ext_iff]
  all_goals decide

private theorem parityRow_step_factored_1 :
    parityRow (2 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (1 : Fin 19)) := by
  rw [parityCoefficient_one, map_add,
    Fintype.linearCombination_apply_single,
    Fintype.linearCombination_apply_single]
  rw [parityRow_two_vector, sparseBasis_oddSource_zero,
    sparseBasis_oddSource_one]
  exact rowTwoVector_factored

private theorem parityRow_step_literal_2_zero :
    parityRow (3 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (2 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow2, usedParityRow3,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_2_two :
    parityRow (3 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (2 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow2, usedParityRow3,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_2_four :
    parityRow (3 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (2 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow2, usedParityRow3,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_2_six :
    parityRow (3 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (2 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow2, usedParityRow3,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_2 :
    parityRow (3 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (2 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_2_zero
    | exact parityRow_step_literal_2_two
    | exact parityRow_step_literal_2_four
    | exact parityRow_step_literal_2_six
    | decide

private theorem parityRow_step_literal_3_0 :
    parityRow (4 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (3 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow3, usedParityRow4,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_3_1 :
    parityRow (4 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (3 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow3, usedParityRow4,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_3_2 :
    parityRow (4 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (3 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow3, usedParityRow4,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_3_3 :
    parityRow (4 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (3 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow3, usedParityRow4,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_3_4 :
    parityRow (4 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (3 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow3, usedParityRow4,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_3 :
    parityRow (4 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (3 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_3_0
    | exact parityRow_step_literal_3_1
    | exact parityRow_step_literal_3_2
    | exact parityRow_step_literal_3_3
    | exact parityRow_step_literal_3_4
    | decide

private theorem parityRow_step_literal_4_0 :
    parityRow (5 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (4 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow4, usedParityRow5,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_4_1 :
    parityRow (5 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (4 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow4, usedParityRow5,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_4_2 :
    parityRow (5 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (4 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow4, usedParityRow5,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_4_3 :
    parityRow (5 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (4 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow4, usedParityRow5,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_4_4 :
    parityRow (5 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (4 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow4, usedParityRow5,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_4_5 :
    parityRow (5 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (4 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow4, usedParityRow5,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_4 :
    parityRow (5 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (4 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_4_0
    | exact parityRow_step_literal_4_1
    | exact parityRow_step_literal_4_2
    | exact parityRow_step_literal_4_3
    | exact parityRow_step_literal_4_4
    | exact parityRow_step_literal_4_5
    | decide

private theorem parityRow_step_literal_5_0 :
    parityRow (6 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_5_1 :
    parityRow (6 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_5_2 :
    parityRow (6 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_5_3 :
    parityRow (6 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_5_4 :
    parityRow (6 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_5_5 :
    parityRow (6 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_5_6 :
    parityRow (6 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (5 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow5, usedParityRow6,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_5 :
    parityRow (6 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (5 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_5_0
    | exact parityRow_step_literal_5_1
    | exact parityRow_step_literal_5_2
    | exact parityRow_step_literal_5_3
    | exact parityRow_step_literal_5_4
    | exact parityRow_step_literal_5_5
    | exact parityRow_step_literal_5_6
    | decide

private theorem parityRow_step_literal_6_0 :
    parityRow (7 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_1 :
    parityRow (7 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_2 :
    parityRow (7 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_3 :
    parityRow (7 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_4 :
    parityRow (7 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_5 :
    parityRow (7 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_6 :
    parityRow (7 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_6_7 :
    parityRow (7 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (6 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow6, usedParityRow7,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_6 :
    parityRow (7 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (6 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_6_0
    | exact parityRow_step_literal_6_1
    | exact parityRow_step_literal_6_2
    | exact parityRow_step_literal_6_3
    | exact parityRow_step_literal_6_4
    | exact parityRow_step_literal_6_5
    | exact parityRow_step_literal_6_6
    | exact parityRow_step_literal_6_7
    | decide

private theorem parityRow_step_literal_7_0 :
    parityRow (8 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_1 :
    parityRow (8 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_2 :
    parityRow (8 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_3 :
    parityRow (8 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_4 :
    parityRow (8 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_5 :
    parityRow (8 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_6 :
    parityRow (8 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_7 :
    parityRow (8 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_7_8 :
    parityRow (8 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (7 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow7, usedParityRow8,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_7 :
    parityRow (8 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (7 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_7_0
    | exact parityRow_step_literal_7_1
    | exact parityRow_step_literal_7_2
    | exact parityRow_step_literal_7_3
    | exact parityRow_step_literal_7_4
    | exact parityRow_step_literal_7_5
    | exact parityRow_step_literal_7_6
    | exact parityRow_step_literal_7_7
    | exact parityRow_step_literal_7_8
    | decide

private theorem parityRow_step_literal_8_0 :
    parityRow (9 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_1 :
    parityRow (9 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_2 :
    parityRow (9 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_3 :
    parityRow (9 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_4 :
    parityRow (9 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_5 :
    parityRow (9 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_6 :
    parityRow (9 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_7 :
    parityRow (9 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_8 :
    parityRow (9 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_8_9 :
    parityRow (9 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (8 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow8, usedParityRow9,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_8 :
    parityRow (9 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (8 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_8_0
    | exact parityRow_step_literal_8_1
    | exact parityRow_step_literal_8_2
    | exact parityRow_step_literal_8_3
    | exact parityRow_step_literal_8_4
    | exact parityRow_step_literal_8_5
    | exact parityRow_step_literal_8_6
    | exact parityRow_step_literal_8_7
    | exact parityRow_step_literal_8_8
    | exact parityRow_step_literal_8_9
    | decide

private theorem parityRow_step_literal_9_0 :
    parityRow (10 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_1 :
    parityRow (10 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_2 :
    parityRow (10 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_3 :
    parityRow (10 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_4 :
    parityRow (10 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_5 :
    parityRow (10 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_6 :
    parityRow (10 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_7 :
    parityRow (10 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_8 :
    parityRow (10 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_9 :
    parityRow (10 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_9_10 :
    parityRow (10 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (9 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow9, usedParityRow10,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_9 :
    parityRow (10 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (9 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_9_0
    | exact parityRow_step_literal_9_1
    | exact parityRow_step_literal_9_2
    | exact parityRow_step_literal_9_3
    | exact parityRow_step_literal_9_4
    | exact parityRow_step_literal_9_5
    | exact parityRow_step_literal_9_6
    | exact parityRow_step_literal_9_7
    | exact parityRow_step_literal_9_8
    | exact parityRow_step_literal_9_9
    | exact parityRow_step_literal_9_10
    | decide

private theorem parityRow_step_literal_10_0 :
    parityRow (11 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_1 :
    parityRow (11 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_2 :
    parityRow (11 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_3 :
    parityRow (11 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_4 :
    parityRow (11 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_5 :
    parityRow (11 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_6 :
    parityRow (11 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_7 :
    parityRow (11 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_8 :
    parityRow (11 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_9 :
    parityRow (11 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_10 :
    parityRow (11 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_10_11 :
    parityRow (11 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (10 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow10, usedParityRow11,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_10 :
    parityRow (11 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (10 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_10_0
    | exact parityRow_step_literal_10_1
    | exact parityRow_step_literal_10_2
    | exact parityRow_step_literal_10_3
    | exact parityRow_step_literal_10_4
    | exact parityRow_step_literal_10_5
    | exact parityRow_step_literal_10_6
    | exact parityRow_step_literal_10_7
    | exact parityRow_step_literal_10_8
    | exact parityRow_step_literal_10_9
    | exact parityRow_step_literal_10_10
    | exact parityRow_step_literal_10_11
    | decide

private theorem parityRow_step_literal_11_0 :
    parityRow (12 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_1 :
    parityRow (12 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_2 :
    parityRow (12 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_3 :
    parityRow (12 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_4 :
    parityRow (12 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_5 :
    parityRow (12 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_6 :
    parityRow (12 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_7 :
    parityRow (12 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_8 :
    parityRow (12 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_9 :
    parityRow (12 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_10 :
    parityRow (12 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_11 :
    parityRow (12 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_11_12 :
    parityRow (12 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (11 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow11, usedParityRow12,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_11 :
    parityRow (12 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (11 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_11_0
    | exact parityRow_step_literal_11_1
    | exact parityRow_step_literal_11_2
    | exact parityRow_step_literal_11_3
    | exact parityRow_step_literal_11_4
    | exact parityRow_step_literal_11_5
    | exact parityRow_step_literal_11_6
    | exact parityRow_step_literal_11_7
    | exact parityRow_step_literal_11_8
    | exact parityRow_step_literal_11_9
    | exact parityRow_step_literal_11_10
    | exact parityRow_step_literal_11_11
    | exact parityRow_step_literal_11_12
    | decide

private theorem parityRow_step_literal_12_0 :
    parityRow (13 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_1 :
    parityRow (13 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_2 :
    parityRow (13 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_3 :
    parityRow (13 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_4 :
    parityRow (13 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_5 :
    parityRow (13 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_6 :
    parityRow (13 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_7 :
    parityRow (13 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_8 :
    parityRow (13 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_9 :
    parityRow (13 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_10 :
    parityRow (13 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_11 :
    parityRow (13 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_12 :
    parityRow (13 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_12_13 :
    parityRow (13 : Fin 19) (26 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (12 : Fin 19))) (26 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow12, usedParityRow13,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_12 :
    parityRow (13 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (12 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_12_0
    | exact parityRow_step_literal_12_1
    | exact parityRow_step_literal_12_2
    | exact parityRow_step_literal_12_3
    | exact parityRow_step_literal_12_4
    | exact parityRow_step_literal_12_5
    | exact parityRow_step_literal_12_6
    | exact parityRow_step_literal_12_7
    | exact parityRow_step_literal_12_8
    | exact parityRow_step_literal_12_9
    | exact parityRow_step_literal_12_10
    | exact parityRow_step_literal_12_11
    | exact parityRow_step_literal_12_12
    | exact parityRow_step_literal_12_13
    | decide

private theorem parityRow_step_literal_13_0 :
    parityRow (14 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_1 :
    parityRow (14 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_2 :
    parityRow (14 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_3 :
    parityRow (14 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_4 :
    parityRow (14 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_5 :
    parityRow (14 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_6 :
    parityRow (14 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_7 :
    parityRow (14 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_8 :
    parityRow (14 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_9 :
    parityRow (14 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_10 :
    parityRow (14 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_11 :
    parityRow (14 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_12 :
    parityRow (14 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_13 :
    parityRow (14 : Fin 19) (26 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (26 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_13_14 :
    parityRow (14 : Fin 19) (28 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (13 : Fin 19))) (28 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow13, usedParityRow14,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_13 :
    parityRow (14 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (13 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_13_0
    | exact parityRow_step_literal_13_1
    | exact parityRow_step_literal_13_2
    | exact parityRow_step_literal_13_3
    | exact parityRow_step_literal_13_4
    | exact parityRow_step_literal_13_5
    | exact parityRow_step_literal_13_6
    | exact parityRow_step_literal_13_7
    | exact parityRow_step_literal_13_8
    | exact parityRow_step_literal_13_9
    | exact parityRow_step_literal_13_10
    | exact parityRow_step_literal_13_11
    | exact parityRow_step_literal_13_12
    | exact parityRow_step_literal_13_13
    | exact parityRow_step_literal_13_14
    | decide

private theorem parityRow_step_literal_14_0 :
    parityRow (15 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_1 :
    parityRow (15 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_2 :
    parityRow (15 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_3 :
    parityRow (15 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_4 :
    parityRow (15 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_5 :
    parityRow (15 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_6 :
    parityRow (15 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_7 :
    parityRow (15 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_8 :
    parityRow (15 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_9 :
    parityRow (15 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_10 :
    parityRow (15 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_11 :
    parityRow (15 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_12 :
    parityRow (15 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_13 :
    parityRow (15 : Fin 19) (26 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (26 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_14 :
    parityRow (15 : Fin 19) (28 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (28 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_14_15 :
    parityRow (15 : Fin 19) (30 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (14 : Fin 19))) (30 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow14, usedParityRow15,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_14 :
    parityRow (15 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (14 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_14_0
    | exact parityRow_step_literal_14_1
    | exact parityRow_step_literal_14_2
    | exact parityRow_step_literal_14_3
    | exact parityRow_step_literal_14_4
    | exact parityRow_step_literal_14_5
    | exact parityRow_step_literal_14_6
    | exact parityRow_step_literal_14_7
    | exact parityRow_step_literal_14_8
    | exact parityRow_step_literal_14_9
    | exact parityRow_step_literal_14_10
    | exact parityRow_step_literal_14_11
    | exact parityRow_step_literal_14_12
    | exact parityRow_step_literal_14_13
    | exact parityRow_step_literal_14_14
    | exact parityRow_step_literal_14_15
    | decide

private theorem parityRow_step_literal_15_0 :
    parityRow (16 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_1 :
    parityRow (16 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_2 :
    parityRow (16 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_3 :
    parityRow (16 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_4 :
    parityRow (16 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_5 :
    parityRow (16 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_6 :
    parityRow (16 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_7 :
    parityRow (16 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_8 :
    parityRow (16 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_9 :
    parityRow (16 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_10 :
    parityRow (16 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_11 :
    parityRow (16 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_12 :
    parityRow (16 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_13 :
    parityRow (16 : Fin 19) (26 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (26 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_14 :
    parityRow (16 : Fin 19) (28 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (28 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_15 :
    parityRow (16 : Fin 19) (30 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (30 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_15_16 :
    parityRow (16 : Fin 19) (32 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (15 : Fin 19))) (32 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow15, usedParityRow16,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_15 :
    parityRow (16 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (15 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_15_0
    | exact parityRow_step_literal_15_1
    | exact parityRow_step_literal_15_2
    | exact parityRow_step_literal_15_3
    | exact parityRow_step_literal_15_4
    | exact parityRow_step_literal_15_5
    | exact parityRow_step_literal_15_6
    | exact parityRow_step_literal_15_7
    | exact parityRow_step_literal_15_8
    | exact parityRow_step_literal_15_9
    | exact parityRow_step_literal_15_10
    | exact parityRow_step_literal_15_11
    | exact parityRow_step_literal_15_12
    | exact parityRow_step_literal_15_13
    | exact parityRow_step_literal_15_14
    | exact parityRow_step_literal_15_15
    | exact parityRow_step_literal_15_16
    | decide

private theorem parityRow_step_literal_16_0 :
    parityRow (17 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_1 :
    parityRow (17 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_2 :
    parityRow (17 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_3 :
    parityRow (17 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_4 :
    parityRow (17 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_5 :
    parityRow (17 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_6 :
    parityRow (17 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_7 :
    parityRow (17 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_8 :
    parityRow (17 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_9 :
    parityRow (17 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_10 :
    parityRow (17 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_11 :
    parityRow (17 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_12 :
    parityRow (17 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_13 :
    parityRow (17 : Fin 19) (26 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (26 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_14 :
    parityRow (17 : Fin 19) (28 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (28 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_15 :
    parityRow (17 : Fin 19) (30 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (30 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_16 :
    parityRow (17 : Fin 19) (32 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (32 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_16_17 :
    parityRow (17 : Fin 19) (34 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (16 : Fin 19))) (34 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow16, usedParityRow17,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_16 :
    parityRow (17 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (16 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_16_0
    | exact parityRow_step_literal_16_1
    | exact parityRow_step_literal_16_2
    | exact parityRow_step_literal_16_3
    | exact parityRow_step_literal_16_4
    | exact parityRow_step_literal_16_5
    | exact parityRow_step_literal_16_6
    | exact parityRow_step_literal_16_7
    | exact parityRow_step_literal_16_8
    | exact parityRow_step_literal_16_9
    | exact parityRow_step_literal_16_10
    | exact parityRow_step_literal_16_11
    | exact parityRow_step_literal_16_12
    | exact parityRow_step_literal_16_13
    | exact parityRow_step_literal_16_14
    | exact parityRow_step_literal_16_15
    | exact parityRow_step_literal_16_16
    | exact parityRow_step_literal_16_17
    | decide

private theorem parityRow_step_literal_17_0 :
    parityRow (18 : Fin 19) (0 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (0 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_1 :
    parityRow (18 : Fin 19) (2 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (2 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_2 :
    parityRow (18 : Fin 19) (4 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (4 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_3 :
    parityRow (18 : Fin 19) (6 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (6 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_4 :
    parityRow (18 : Fin 19) (8 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (8 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_5 :
    parityRow (18 : Fin 19) (10 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (10 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_6 :
    parityRow (18 : Fin 19) (12 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (12 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_7 :
    parityRow (18 : Fin 19) (14 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (14 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_8 :
    parityRow (18 : Fin 19) (16 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (16 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_9 :
    parityRow (18 : Fin 19) (18 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (18 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_10 :
    parityRow (18 : Fin 19) (20 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (20 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_11 :
    parityRow (18 : Fin 19) (22 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (22 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_12 :
    parityRow (18 : Fin 19) (24 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (24 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_13 :
    parityRow (18 : Fin 19) (26 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (26 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_14 :
    parityRow (18 : Fin 19) (28 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (28 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_15 :
    parityRow (18 : Fin 19) (30 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (30 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_16 :
    parityRow (18 : Fin 19) (32 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (32 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_17 :
    parityRow (18 : Fin 19) (34 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (34 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_literal_17_18 :
    parityRow (18 : Fin 19) (36 : Fin 48) =
      (Fintype.linearCombination ExactM31 literalSparseOdd
        (parityCoefficient (17 : Fin 19))) (36 : Fin 48) := by
  simp [parityRow, parityCoefficient, parityTableExact_used,
    usedParityEntry, usedParityRow, usedParityRow17, usedParityRow18,
    literalSparseOdd, oddCount, dyadicLiteral, oddSource, successorIndex,
    carryIndex, Fintype.linearCombination_apply, Pi.single_apply,
    Fin.sum_univ_succ]
  all_goals rfl

private theorem parityRow_step_factored_17 :
    parityRow (18 : Fin 19) =
      Fintype.linearCombination ExactM31
        (fun index => sparseBasis (oddSource index))
        (parityCoefficient (17 : Fin 19)) := by
  rw [sparseBasis_oddSource_family]
  funext coordinate
  fin_cases coordinate <;>
    first
    | exact parityRow_step_literal_17_0
    | exact parityRow_step_literal_17_1
    | exact parityRow_step_literal_17_2
    | exact parityRow_step_literal_17_3
    | exact parityRow_step_literal_17_4
    | exact parityRow_step_literal_17_5
    | exact parityRow_step_literal_17_6
    | exact parityRow_step_literal_17_7
    | exact parityRow_step_literal_17_8
    | exact parityRow_step_literal_17_9
    | exact parityRow_step_literal_17_10
    | exact parityRow_step_literal_17_11
    | exact parityRow_step_literal_17_12
    | exact parityRow_step_literal_17_13
    | exact parityRow_step_literal_17_14
    | exact parityRow_step_literal_17_15
    | exact parityRow_step_literal_17_16
    | exact parityRow_step_literal_17_17
    | exact parityRow_step_literal_17_18
    | decide

private abbrev WordModel := Fin 24 → Fin 24 → Std.U32
private def kernelEntry (kernel : LocalKernel) (index : Fin 37) : LocalM31 :=
  kernel.val[index.val]'(by
    rw [kernel.property]
    exact index.isLt)

private def kernelWord (kernel : LocalKernel) (half : Nat)
    (hhalf : half < 19) : LocalM31 :=
  kernelEntry kernel ⟨2 * half, by omega⟩

private def modelWord (words : WordModel) (row column : Nat)
    (hrow : row < 19)
    (hcolumn : column < 19) : Std.U32 :=
  words ⟨row, by omega⟩ ⟨column, by omega⟩

private def TableBound (words : WordModel) : Prop :=
  ∀ (row column : Nat) (hrow : row < 19) (hcolumn : column < 19),
    (modelWord words row column hrow hcolumn).val < 2 ^ 31

private def TableCalls (words : WordModel) : Prop :=
  ∀ (row column : Std.Usize) (hrow : row.val < 19)
    (hcolumn : column.val < 19),
    ∃ tableRow : Array Std.U32 24#usize, ∃ coefficient : Std.U32,
      Array.index_usize
          v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY row =
        .ok tableRow ∧
      Array.index_usize tableRow column = .ok coefficient ∧
      coefficient = modelWord words row.val column.val hrow hcolumn

private def rawTerm (words : WordModel) (kernel : LocalKernel)
    (column row : Nat) : Nat :=
  if hrow : row < 19 then
    if hcolumn : column < 19 then
      (kernelWord kernel row hrow).val *
        (modelWord words row column hrow hcolumn).val
    else 0
  else 0

private def exactTerm (words : WordModel) (kernel : LocalKernel)
    (column row : Nat) : ExactM31 :=
  (rawTerm words kernel column row : Nat)

private def rawRange (words : WordModel) (kernel : LocalKernel)
    (column start stop : Nat) : Nat :=
  ∑ row ∈ Finset.Ico start stop, rawTerm words kernel column row

private def exactRange (words : WordModel) (kernel : LocalKernel)
    (column start stop : Nat) : ExactM31 :=
  ∑ row ∈ Finset.Ico start stop, exactTerm words kernel column row

private theorem rawRange_cast (words : WordModel) (kernel : LocalKernel)
    (column start stop : Nat) :
    ((rawRange words kernel column start stop : Nat) : ExactM31) =
      exactRange words kernel column start stop := by
  simp [rawRange, exactRange, exactTerm]

private theorem rawTerm_bound (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (column row : Nat) (hcolumn : column < 19) (hrow : row < 19) :
    rawTerm words kernel column row ≤
      (AspisV5ComponentCQM31TowerExact.P - 1) *
        AspisV5ComponentCQM31TowerExact.P := by
  rw [rawTerm, dif_pos hrow, dif_pos hcolumn]
  have hk := hkernel ⟨2 * row, by omega⟩
  have ht := htable row column hrow hcolumn
  change GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalM31
    (kernelWord kernel row hrow) at hk
  change (kernelWord kernel row hrow).val *
      (modelWord words row column hrow hcolumn).val ≤ _
  have hp : AspisV5ComponentCQM31TowerExact.P = 2 ^ 31 - 1 := by
    norm_num [AspisV5ComponentCQM31TowerExact.P]
  change (kernelWord kernel row hrow).val <
    AspisV5ComponentCQM31TowerExact.P at hk
  have hk' : (kernelWord kernel row hrow).val ≤
      AspisV5ComponentCQM31TowerExact.P - 1 := by omega
  have ht' : (modelWord words row column hrow hcolumn).val ≤
      AspisV5ComponentCQM31TowerExact.P := by
    rw [hp]
    omega
  exact Nat.mul_le_mul hk' ht'

private theorem rawRange_lt_u64 (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (column start stop : Nat) (hcolumn : column < 19)
    (hstart : start ≤ stop) (hstop : stop ≤ 19)
    (hwidth : stop ≤ start + 4) :
    rawRange words kernel column start stop < 2 ^ 64 := by
  have hterm : ∀ row ∈ Finset.Ico start stop,
      rawTerm words kernel column row ≤
        (AspisV5ComponentCQM31TowerExact.P - 1) *
          AspisV5ComponentCQM31TowerExact.P := by
    intro row hrow
    have hrange := Finset.mem_Ico.mp hrow
    exact rawTerm_bound words kernel hkernel htable column row hcolumn (by omega)
  calc
    rawRange words kernel column start stop ≤
        ∑ _row ∈ Finset.Ico start stop,
          (AspisV5ComponentCQM31TowerExact.P - 1) *
            AspisV5ComponentCQM31TowerExact.P := by
      unfold rawRange
      exact Finset.sum_le_sum fun row hrow => hterm row hrow
    _ = (stop - start) *
        ((AspisV5ComponentCQM31TowerExact.P - 1) *
          AspisV5ComponentCQM31TowerExact.P) := by
      simp [Nat.mul_comm]
    _ < 2 ^ 64 := by
      have hcount : stop - start ≤ 4 := by omega
      norm_num [AspisV5ComponentCQM31TowerExact.P] at hcount ⊢
      omega

private theorem usize_wrapping_mul_two_val (value : Std.Usize)
    (hvalue : 2 * value.val < Std.Usize.size) :
    (Std.Usize.wrapping_mul 2#usize value).val = 2 * value.val := by
  rw [Std.Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  simpa [Nat.mul_comm] using hvalue

private theorem usize_wrapping_add_one_val (value : Std.Usize)
    (hvalue : value.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

private theorem u64_cast_u32_val (value : Std.U32) :
    (UScalar.cast .U64 value : Std.U64).val = value.val := by
  simp

private theorem rawRange_succ (words : WordModel) (kernel : LocalKernel)
    (column start row : Nat)
    (hstart : start ≤ row) :
    rawRange words kernel column start (row + 1) =
      rawRange words kernel column start row + rawTerm words kernel column row := by
  unfold rawRange
  rw [Finset.sum_Ico_succ_top hstart]

private abbrev innerBody :=
  v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0_loop0.body

private abbrev innerLoop :=
  v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0_loop0

private def InnerInvariant (words : WordModel) (kernel : LocalKernel)
    (column : Std.Usize)
    (blockStart blockEnd : Std.Usize) (raw : Std.U64) (row : Std.Usize) : Prop :=
  blockStart.val ≤ row.val ∧
  row.val ≤ blockEnd.val ∧
  blockEnd.val ≤ 19 ∧
  blockEnd.val ≤ blockStart.val + 4 ∧
  raw.val = rawRange words kernel column.val blockStart.val row.val

private theorem innerBody_step (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words)
    (column blockStart blockEnd row : Std.Usize) (raw : Std.U64)
    (hcolumn : column.val < 19) (hcontinue : row.val < blockEnd.val)
    (hinvariant : InnerInvariant words kernel column blockStart blockEnd raw row) :
    ∃ state : Std.U64 × Std.Usize,
      innerBody kernel column blockEnd raw row = .ok (.cont state) ∧
      state.2.val = row.val + 1 ∧
      InnerInvariant words kernel column blockStart blockEnd state.1 state.2 := by
  rcases hinvariant with ⟨hstart, hrowEnd, hend, hwidth, hraw⟩
  have hrow : row.val < 19 := by omega
  have hcondition : row < blockEnd := (UScalar.lt_equiv _ _).2 hcontinue
  let doubled := Std.Usize.wrapping_mul 2#usize row
  have hdoubled : doubled.val = 2 * row.val := by
    apply usize_wrapping_mul_two_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  have hkernelIndex : doubled.val < kernel.length := by
    change doubled.val < kernel.val.length
    rw [kernel.property, hdoubled]
    norm_num
    omega
  obtain ⟨coefficient, hcoefficient, hcoefficientValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec kernel doubled hkernelIndex)
  have hcoefficientWord : coefficient = kernelWord kernel row.val hrow := by
    have hdoubledBound : doubled.val < 37 := by
      rw [hdoubled]
      omega
    have hleft : coefficient =
        kernelEntry kernel ⟨doubled.val, hdoubledBound⟩ := hcoefficientValue
    rw [hleft]
    unfold kernelWord
    congr 1
    exact Fin.ext hdoubled
  let wideCoefficient : Std.U64 :=
    core.convert.num.FromU64U32.from coefficient
  have hwideCoefficient : wideCoefficient.val = coefficient.val := by
    simp [wideCoefficient, u64_cast_u32_val]
  obtain ⟨tableRow, tableCoefficient, htableRow, htableCoefficient,
      htableCoefficientWord⟩ := htableCall row column hrow hcolumn
  let wideTableCoefficient : Std.U64 :=
    core.convert.num.FromU64U32.from tableCoefficient
  have hwideTableCoefficient :
      wideTableCoefficient.val = tableCoefficient.val := by
    simp [wideTableCoefficient, u64_cast_u32_val]
  let product := Std.U64.wrapping_mul wideCoefficient wideTableCoefficient
  have htermBound := rawTerm_bound words kernel hkernel htable
    column.val row.val hcolumn hrow
  rw [rawTerm, dif_pos hrow, dif_pos hcolumn] at htermBound
  have hproductNat : coefficient.val * tableCoefficient.val < 2 ^ 64 := by
    rw [hcoefficientWord, htableCoefficientWord]
    have hmax :
        (AspisV5ComponentCQM31TowerExact.P - 1) *
            AspisV5ComponentCQM31TowerExact.P < 2 ^ 64 := by
      norm_num [AspisV5ComponentCQM31TowerExact.P]
    exact htermBound.trans_lt hmax
  have hproduct : product.val = coefficient.val * tableCoefficient.val := by
    unfold product
    rw [Std.U64.wrapping_mul_val_eq,
      hwideCoefficient, hwideTableCoefficient]
    apply Nat.mod_eq_of_lt
    simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hproductNat
  let rawNext := Std.U64.wrapping_add raw product
  have hprefixBound :
      rawRange words kernel column.val blockStart.val (row.val + 1) < 2 ^ 64 := by
    apply rawRange_lt_u64 words kernel hkernel htable column.val blockStart.val
      (row.val + 1) hcolumn
    · exact hstart.trans (Nat.le_add_right row.val 1)
    · omega
    · omega
  have hrawNext : rawNext.val =
      rawRange words kernel column.val blockStart.val (row.val + 1) := by
    unfold rawNext
    rw [Std.U64.wrapping_add_val_eq, hraw, hproduct,
      hcoefficientWord, htableCoefficientWord]
    have htermEq :
        (kernelWord kernel row.val hrow).val *
            (modelWord words row.val column.val hrow hcolumn).val =
          rawTerm words kernel column.val row.val := by
      rw [rawTerm, dif_pos hrow, dif_pos hcolumn]
    rw [htermEq,
      ← rawRange_succ words kernel column.val blockStart.val row.val hstart]
    apply Nat.mod_eq_of_lt
    simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using hprefixBound
  let rowNext := Std.Usize.wrapping_add row 1#usize
  have hrowNext : rowNext.val = row.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  refine ⟨(rawNext, rowNext), ?_, hrowNext, ?_⟩
  · unfold innerBody
    unfold
      v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0_loop0.body
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    rw [if_pos hcondition, hcoefficient]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [htableRow]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [htableCoefficient]
  · change InnerInvariant words kernel column blockStart blockEnd rawNext rowNext
    refine ⟨?_, ?_, hend, hwidth, ?_⟩
    · rw [hrowNext]
      omega
    · rw [hrowNext]
      omega
    · rw [hrowNext]
      exact hrawNext

private theorem innerLoop_spec (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words)
    (column blockStart blockEnd row : Std.Usize) (raw : Std.U64)
    (hcolumn : column.val < 19)
    (hinvariant : InnerInvariant words kernel column blockStart blockEnd raw row) :
    ∃ result : Std.U64,
      innerLoop kernel column blockEnd raw row = .ok result ∧
      result.val =
        rawRange words kernel column.val blockStart.val blockEnd.val := by
  by_cases hcontinue : row.val < blockEnd.val
  · obtain ⟨state, hbody, hrowNext, hstateInvariant⟩ :=
      innerBody_step words kernel hkernel htable htableCall column blockStart
        blockEnd row raw hcolumn hcontinue hinvariant
    obtain ⟨result, hresult, hresultValue⟩ :=
      innerLoop_spec words kernel hkernel htable htableCall column blockStart
        blockEnd state.2 state.1 hcolumn hstateInvariant
    unfold innerBody at hbody
    unfold innerLoop at hresult
    refine ⟨result, ?_, hresultValue⟩
    unfold innerLoop
    unfold
      v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hresult
  · rcases hinvariant with ⟨_hstart, hrowEnd, _hend, _hwidth, hraw⟩
    have hfinal : row.val = blockEnd.val := by omega
    have hcondition : ¬ row < blockEnd := by
      intro hlt
      exact hcontinue ((UScalar.lt_equiv _ _).1 hlt)
    have hbodyDone : innerBody kernel column blockEnd raw row =
        .ok (.done raw) := by
      unfold innerBody
      unfold
        v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0_loop0.body
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [if_neg hcondition]
    unfold innerBody at hbodyDone
    refine ⟨raw, ?_, ?_⟩
    · unfold innerLoop
      unfold
        v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0_loop0
      rw [loop.eq_def]
      simp only
      rw [hbodyDone]
    · rw [hraw, hfinal]
termination_by blockEnd.val - row.val
decreasing_by
  rw [hrowNext]
  omega

private theorem usize_wrapping_add_four_val (value : Std.Usize)
    (hvalue : value.val + 4 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 4#usize).val = value.val + 4 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

private theorem usize_min_spec (left right : Std.Usize) :
    ∃ result : Std.Usize,
      core.cmp.min core.cmp.OrdUsize left right = .ok result ∧
      result.val = Nat.min left.val right.val := by
  by_cases hlt : left.val < right.val
  · refine ⟨left, ?_, by simp [Nat.min_eq_left (Nat.le_of_lt hlt)]⟩
    simp [core.cmp.min, core.cmp.OrdUsize,
      core.cmp.impls.OrdUsize.min, core.cmp.Ord.min_body,
      (UScalar.lt_equiv left right).2 hlt]
  · have hle : right.val ≤ left.val := by omega
    refine ⟨right, ?_, by simp [Nat.min_eq_right hle]⟩
    have hnlt : ¬ left < right := by
      intro h
      exact hlt ((UScalar.lt_equiv left right).1 h)
    simp [core.cmp.min, core.cmp.OrdUsize,
      core.cmp.impls.OrdUsize.min, core.cmp.Ord.min_body, hnlt]

private theorem exactRange_consecutive (words : WordModel)
    (kernel : LocalKernel) (column start middle stop : Nat)
    (hstart : start ≤ middle) (hmiddle : middle ≤ stop) :
    exactRange words kernel column start middle +
        exactRange words kernel column middle stop =
      exactRange words kernel column start stop := by
  unfold exactRange
  rw [Finset.sum_Ico_consecutive _ hstart hmiddle]

private abbrev blockBody :=
  v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0.body

private abbrev blockLoop :=
  v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0

private def BlockInvariant (words : WordModel) (kernel : LocalKernel)
    (column : Std.Usize) (outer : Std.U64) (blockStart : Std.Usize) : Prop :=
  column.val ≤ blockStart.val ∧
  blockStart.val ≤ 19 ∧
  outer.val < (blockStart.val + 1) * AspisV5ComponentCQM31TowerExact.P ∧
  ((outer.val : Nat) : ExactM31) =
    exactRange words kernel column.val column.val blockStart.val

private theorem blockBody_step (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words)
    (column blockStart : Std.Usize) (outer : Std.U64)
    (hcolumn : column.val < 19) (hcontinue : blockStart.val ≤ 18)
    (hinvariant : BlockInvariant words kernel column outer blockStart) :
    ∃ state : Std.U64 × Std.Usize,
      blockBody 18#usize kernel column outer blockStart = .ok (.cont state) ∧
      blockStart.val < state.2.val ∧
      BlockInvariant words kernel column state.1 state.2 := by
  rcases hinvariant with ⟨hcolumnStart, hstart19, houterBound, houterExact⟩
  have hcondition : blockStart ≤ (18#usize : Std.Usize) :=
    (UScalar.le_equiv _ _).2 (by simpa using hcontinue)
  let startPlusFour := Std.Usize.wrapping_add blockStart 4#usize
  have hstartPlusFour : startPlusFour.val = blockStart.val + 4 := by
    apply usize_wrapping_add_four_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  let nineteen := Std.Usize.wrapping_add 18#usize 1#usize
  have hnineteen : nineteen.val = 19 := by
    apply usize_wrapping_add_one_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    change 19 < Std.Usize.size
    omega
  obtain ⟨blockEnd, hblockEndCall, hblockEnd⟩ :=
    usize_min_spec startPlusFour nineteen
  have hblockEndValue : blockEnd.val = Nat.min (blockStart.val + 4) 19 := by
    rw [hblockEnd, hstartPlusFour, hnineteen]
  have hstartEnd : blockStart.val < blockEnd.val := by
    rw [hblockEndValue]
    rw [Nat.lt_min]
    exact ⟨by omega, by omega⟩
  have hend19 : blockEnd.val ≤ 19 := by
    rw [hblockEndValue]
    exact Nat.min_le_right _ _
  have hendWidth : blockEnd.val ≤ blockStart.val + 4 := by
    rw [hblockEndValue]
    exact Nat.min_le_left _ _
  have hinnerInvariant :
      InnerInvariant words kernel column blockStart blockEnd 0#u64 blockStart := by
    refine ⟨le_rfl, Nat.le_of_lt hstartEnd, hend19, hendWidth, ?_⟩
    simp [rawRange]
  obtain ⟨rawResult, hinnerCall, hrawResult⟩ :=
    innerLoop_spec words kernel hkernel htable htableCall column blockStart
      blockEnd blockStart 0#u64 hcolumn hinnerInvariant
  have hrawBound : rawResult.val < 2 ^ 64 := by
    rw [hrawResult]
    exact rawRange_lt_u64 words kernel hkernel htable column.val
      blockStart.val blockEnd.val hcolumn (Nat.le_of_lt hstartEnd) hend19
      hendWidth
  obtain ⟨reduced, hreduceCall, hreduced⟩ :=
    GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
      rawResult
  have hreducedCanonical : reduced.val < AspisV5ComponentCQM31TowerExact.P := by
    rw [hreduced]
    exact rawReduceU64_canonical _ hrawBound
  have hreducedExact : ((reduced.val : Nat) : ExactM31) =
      exactRange words kernel column.val blockStart.val blockEnd.val := by
    rw [hreduced, rawReduceU64_residue _ hrawBound, hrawResult,
      rawRange_cast]
  let wideReduced : Std.U64 := core.convert.num.FromU64U32.from reduced
  have hwideReduced : wideReduced.val = reduced.val := by
    simp [wideReduced]
  let outerNext := Std.U64.wrapping_add outer wideReduced
  have houterNatBound : outer.val + reduced.val < 2 ^ 64 := by
    calc
      outer.val + reduced.val <
          (blockStart.val + 1) * AspisV5ComponentCQM31TowerExact.P +
            AspisV5ComponentCQM31TowerExact.P :=
        Nat.add_lt_add houterBound hreducedCanonical
      _ < 2 ^ 64 := by
        norm_num [AspisV5ComponentCQM31TowerExact.P] at hcontinue ⊢
        omega
  have houterNext : outerNext.val = outer.val + reduced.val := by
    unfold outerNext
    rw [Std.U64.wrapping_add_val_eq, hwideReduced]
    apply Nat.mod_eq_of_lt
    simpa [UScalar.size, Std.U64.size, Std.U64.numBits] using houterNatBound
  have houterNextBound : outerNext.val <
      (blockEnd.val + 1) * AspisV5ComponentCQM31TowerExact.P := by
    rw [houterNext]
    calc
      outer.val + reduced.val <
          (blockStart.val + 1) * AspisV5ComponentCQM31TowerExact.P +
            AspisV5ComponentCQM31TowerExact.P :=
        Nat.add_lt_add houterBound hreducedCanonical
      _ ≤ (blockEnd.val + 1) * AspisV5ComponentCQM31TowerExact.P := by
        norm_num [AspisV5ComponentCQM31TowerExact.P] at hstartEnd ⊢
        omega
  have houterNextExact : ((outerNext.val : Nat) : ExactM31) =
      exactRange words kernel column.val column.val blockEnd.val := by
    rw [houterNext, Nat.cast_add, houterExact, hreducedExact]
    exact exactRange_consecutive words kernel column.val column.val
      blockStart.val blockEnd.val hcolumnStart (Nat.le_of_lt hstartEnd)
  refine ⟨(outerNext, blockEnd), ?_, hstartEnd, ?_⟩
  · unfold blockBody
    unfold
      v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0.body
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    rw [if_pos hcondition]
    change (do
      let block_end ← core.cmp.min core.cmp.OrdUsize startPlusFour nineteen
      let raw1 ← innerLoop kernel column block_end 0#u64 blockStart
      let m ← aspis_core.field.M31.reduce_u64 raw1
      let i3 ← lift (core.convert.num.FromU64U32.from m)
      let outer1 ← lift (Std.U64.wrapping_add outer i3)
      ok (cont (outer1, block_end))) = _
    rw [hblockEndCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hinnerCall]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold aspis_core.field.M31.reduce_u64
    rw [hreduceCall]
    rfl
  · change BlockInvariant words kernel column outerNext blockEnd
    exact ⟨hcolumnStart.trans (Nat.le_of_lt hstartEnd), hend19,
      houterNextBound, houterNextExact⟩

private theorem blockLoop_spec (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words)
    (column blockStart : Std.Usize) (outer : Std.U64)
    (hcolumn : column.val < 19)
    (hinvariant : BlockInvariant words kernel column outer blockStart) :
    ∃ result : Std.U64,
      blockLoop 18#usize kernel column outer blockStart = .ok result ∧
      result.val < 20 * AspisV5ComponentCQM31TowerExact.P ∧
      ((result.val : Nat) : ExactM31) =
        exactRange words kernel column.val column.val 19 := by
  by_cases hcontinue : blockStart.val ≤ 18
  · obtain ⟨state, hbody, hprogress, hstateInvariant⟩ :=
      blockBody_step words kernel hkernel htable htableCall column blockStart
        outer hcolumn hcontinue hinvariant
    obtain ⟨result, hresult, hbound, hexact⟩ :=
      blockLoop_spec words kernel hkernel htable htableCall column state.2
        state.1 hcolumn hstateInvariant
    unfold blockBody at hbody
    unfold blockLoop at hresult
    refine ⟨result, ?_, hbound, hexact⟩
    unfold blockLoop
    unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hresult
  · rcases hinvariant with ⟨_hcolumnStart, hstart19, houterBound, houterExact⟩
    have hfinal : blockStart.val = 19 := by omega
    have hcondition : ¬ blockStart ≤ (18#usize : Std.Usize) := by
      intro hle
      exact hcontinue (by
        have := (UScalar.le_equiv _ _).1 hle
        simpa using this)
    have hbodyDone : blockBody 18#usize kernel column outer blockStart =
        .ok (.done outer) := by
      unfold blockBody
      unfold
        v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0.body
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [if_neg hcondition]
    unfold blockBody at hbodyDone
    refine ⟨outer, ?_, ?_, ?_⟩
    · unfold blockLoop
      unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0_loop0
      rw [loop.eq_def]
      simp only
      rw [hbodyDone]
    · rw [hfinal] at houterBound
      simpa [Nat.mul_comm] using houterBound
    · simpa [hfinal] using houterExact
termination_by 19 - blockStart.val
decreasing_by
  omega

private theorem blockLoop_from_zero (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words) (column : Std.Usize)
    (hcolumn : column.val < 19) :
    ∃ result : Std.U64,
      blockLoop 18#usize kernel column 0#u64 column = .ok result ∧
      result.val < 20 * AspisV5ComponentCQM31TowerExact.P ∧
      ((result.val : Nat) : ExactM31) =
        exactRange words kernel column.val column.val 19 := by
  apply blockLoop_spec words kernel hkernel htable htableCall column column
    0#u64 hcolumn
  refine ⟨le_rfl, Nat.le_of_lt hcolumn, ?_, ?_⟩
  · norm_num [AspisV5ComponentCQM31TowerExact.P]
  · simp [exactRange]

private theorem arrayEntry48_set_same (values : LocalVector)
    (index : Std.Usize) (hindex : index.val < 48) (value : LocalM31) :
    GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48
      (values.set index value) ⟨index.val, hindex⟩ = value := by
  unfold GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [values.property]
    simpa using hindex)

private theorem arrayEntry48_set_other (values : LocalVector)
    (index : Std.Usize) (value : LocalM31) (output : Fin 48)
    (hne : index.val ≠ output.val) :
    GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48
      (values.set index value) output =
    GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48 values output := by
  unfold GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [values.property]
    simpa using output.isLt)

private theorem canonicalLocalVector_set (values : LocalVector)
    (index : Std.Usize) (hindex : index.val < 48) (value : LocalM31)
    (hvalues :
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector values)
    (hvalue :
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalM31 value) :
    GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector
      (values.set index value) := by
  intro output
  by_cases heq : index.val = output.val
  · have hout : output = ⟨index.val, hindex⟩ := Fin.ext heq.symm
    subst output
    change (GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48
      (values.set index value) ⟨index.val, hindex⟩).val < _
    rw [arrayEntry48_set_same]
    exact hvalue
  · rw [arrayEntry48_set_other values index value output heq]
    exact hvalues output

private def expectedNatural (words : WordModel) (kernel : LocalKernel)
    (limit : Nat) : Fin 48 → ExactM31 :=
  fun index =>
    if index.val % 2 = 0 ∧ index.val / 2 < limit then
      exactRange words kernel (index.val / 2) (index.val / 2) 19
    else 0

private theorem expectedNatural_at_target (words : WordModel)
    (kernel : LocalKernel) (coordinate : Nat) (hcoordinate : coordinate < 19) :
    expectedNatural words kernel (coordinate + 1)
        ⟨2 * coordinate, by omega⟩ =
      exactRange words kernel coordinate coordinate 19 := by
  unfold expectedNatural
  simp

private theorem expectedNatural_succ_other (words : WordModel)
    (kernel : LocalKernel) (coordinate : Nat) (hcoordinate : coordinate < 19)
    (output : Fin 48) (hne : 2 * coordinate ≠ output.val) :
    expectedNatural words kernel (coordinate + 1) output =
      expectedNatural words kernel coordinate output := by
  unfold expectedNatural
  by_cases heven : output.val % 2 = 0
  · by_cases hlt : output.val / 2 < coordinate
    · rw [if_pos ⟨heven, by omega⟩, if_pos ⟨heven, hlt⟩]
    · have hnotNext : ¬ output.val / 2 < coordinate + 1 := by
        intro hnext
        have hquotient : output.val / 2 = coordinate := by omega
        have hdecomp := Nat.mod_add_div output.val 2
        rw [heven, zero_add, hquotient] at hdecomp
        exact hne hdecomp
      rw [if_neg (by aesop), if_neg (by aesop)]
  · rw [if_neg (by aesop), if_neg (by aesop)]

private theorem arrayToExact48_set_expected_succ (words : WordModel)
    (kernel : LocalKernel) (coordinate : Std.Usize)
    (hcoordinate : coordinate.val < 19) (values : LocalVector)
    (hvalues :
      GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48 values =
        expectedNatural words kernel coordinate.val)
    (value : LocalM31)
    (hvalue : ((value.val : Nat) : ExactM31) =
      exactRange words kernel coordinate.val coordinate.val 19) :
    let target := Std.Usize.wrapping_mul 2#usize coordinate
    GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48
        (values.set target value) =
      expectedNatural words kernel (coordinate.val + 1) := by
  let target := Std.Usize.wrapping_mul 2#usize coordinate
  have htarget : target.val = 2 * coordinate.val := by
    apply usize_wrapping_mul_two_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  have htargetBound : target.val < 48 := by rw [htarget]; omega
  funext output
  by_cases heq : target.val = output.val
  · have hout : output = ⟨target.val, htargetBound⟩ := Fin.ext heq.symm
    subst output
    rw [GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48,
      arrayEntry48_set_same]
    change ((value.val : Nat) : ExactM31) = _
    rw [hvalue]
    have htargetFin : (⟨target.val, htargetBound⟩ : Fin 48) =
        ⟨2 * coordinate.val, by omega⟩ := Fin.ext htarget
    rw [htargetFin]
    exact (expectedNatural_at_target words kernel coordinate.val hcoordinate).symm
  · rw [GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48,
      arrayEntry48_set_other values target value output heq]
    have hpoint := congrFun hvalues output
    rw [GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48] at hpoint
    rw [hpoint]
    apply (expectedNatural_succ_other words kernel coordinate.val hcoordinate
      output ?_).symm
    intro heqTarget
    apply heq
    rw [htarget]
    exact heqTarget

private abbrev outerBody :=
  v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0.body

private abbrev outerLoop :=
  v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0

private def OuterInvariant (words : WordModel) (kernel : LocalKernel)
    (values : LocalVector) (coordinate : Std.Usize) : Prop :=
  coordinate.val ≤ 19 ∧
  GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector values ∧
  GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48 values =
    expectedNatural words kernel coordinate.val

private theorem array_update_eq_ok {α : Type u} {n : Std.Usize}
    (values : Array α n) (index : Std.Usize) (value : α)
    (hbound : index.val < values.val.length) :
    Array.update values index value = .ok (values.set index value) := by
  unfold Aeneas.Std.Array.update Aeneas.Std.Array.set
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem hbound]

private theorem kernelDegreeHalf_call :
    v5_cu_probe.good_gate_probe.KERNEL_DEGREE / 2#usize =
      (.ok 18#usize : Result Std.Usize) := by
  obtain ⟨result, hcall, hvalue⟩ :=
    UScalar.div_spec v5_cu_probe.good_gate_probe.KERNEL_DEGREE
      (y := 2#usize) (by norm_num)
  have hresult : result.val = 18 := by
    simpa [v5_cu_probe.good_gate_probe.KERNEL_DEGREE] using hvalue
  have heq : result = 18#usize := UScalar.eq_of_val_eq (by simpa using hresult)
  subst result
  exact hcall

private theorem outerBody_step (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words) (values : LocalVector)
    (coordinate : Std.Usize) (hcontinue : coordinate.val ≤ 18)
    (hinvariant : OuterInvariant words kernel values coordinate) :
    ∃ state : LocalVector × Std.Usize,
      outerBody kernel values coordinate = .ok (.cont state) ∧
      state.2.val = coordinate.val + 1 ∧
      OuterInvariant words kernel state.1 state.2 := by
  rcases hinvariant with ⟨hcoordinate19, hvaluesCanonical, hvaluesExact⟩
  have hcoordinate : coordinate.val < 19 := by omega
  have hcondition : coordinate ≤ (18#usize : Std.Usize) :=
    (UScalar.le_equiv _ _).2 (by simpa using hcontinue)
  obtain ⟨outer, houterCall, houterBound, houterExact⟩ :=
    blockLoop_from_zero words kernel hkernel htable htableCall coordinate
      hcoordinate
  have houter64 : outer.val < 2 ^ 64 := by
    calc
      outer.val < 20 * AspisV5ComponentCQM31TowerExact.P := houterBound
      _ < 2 ^ 64 := by norm_num [AspisV5ComponentCQM31TowerExact.P]
  obtain ⟨reduced, hreduceCall, hreduced⟩ :=
    GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec outer
  have hreducedCanonical :
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalM31 reduced := by
    change reduced.val < AspisV5ComponentCQM31TowerExact.P
    rw [hreduced]
    exact rawReduceU64_canonical _ houter64
  have hreducedExact : ((reduced.val : Nat) : ExactM31) =
      exactRange words kernel coordinate.val coordinate.val 19 := by
    rw [hreduced, rawReduceU64_residue _ houter64]
    exact houterExact
  let target := Std.Usize.wrapping_mul 2#usize coordinate
  have htarget : target.val = 2 * coordinate.val := by
    apply usize_wrapping_mul_two_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  have htargetBound : target.val < 48 := by rw [htarget]; omega
  have htargetLength : target.val < values.length := by
    change target.val < values.val.length
    rw [values.property]
    simpa using htargetBound
  have hupdate : Array.update values target reduced =
      .ok (values.set target reduced) :=
    array_update_eq_ok _ _ _ htargetLength
  let coordinateNext := Std.Usize.wrapping_add coordinate 1#usize
  have hcoordinateNext : coordinateNext.val = coordinate.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  have hnextCanonical := canonicalLocalVector_set values target htargetBound
    reduced hvaluesCanonical hreducedCanonical
  have hnextExact :
      GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48
          (values.set target reduced) =
        expectedNatural words kernel (coordinate.val + 1) := by
    exact arrayToExact48_set_expected_succ words kernel coordinate hcoordinate
      values hvaluesExact reduced hreducedExact
  refine ⟨(values.set target reduced, coordinateNext), ?_, hcoordinateNext, ?_⟩
  · unfold outerBody
    unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0.body
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    rw [kernelDegreeHalf_call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [if_pos hcondition]
    unfold blockLoop at houterCall
    rw [houterCall]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold aspis_core.field.M31.reduce_u64
    rw [hreduceCall]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
      let a ← Array.update values target reduced
      ok (cont (a, coordinateNext))) = _
    rw [hupdate]
    rfl
  · change OuterInvariant words kernel (values.set target reduced) coordinateNext
    refine ⟨?_, hnextCanonical, ?_⟩
    · rw [hcoordinateNext]
      omega
    · rw [hcoordinateNext]
      exact hnextExact

private theorem outerLoop_spec (words : WordModel) (kernel : LocalKernel)
    (hkernel : CanonicalLocalKernel kernel) (htable : TableBound words)
    (htableCall : TableCalls words) (values : LocalVector)
    (coordinate : Std.Usize)
    (hinvariant : OuterInvariant words kernel values coordinate) :
    ∃ result : LocalVector,
      outerLoop kernel values coordinate = .ok result ∧
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector result ∧
      GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48 result =
        expectedNatural words kernel 19 := by
  by_cases hcontinue : coordinate.val ≤ 18
  · obtain ⟨state, hbody, hcoordinateNext, hstateInvariant⟩ :=
      outerBody_step words kernel hkernel htable htableCall values coordinate
        hcontinue hinvariant
    obtain ⟨result, hresult, hcanonical, hexact⟩ :=
      outerLoop_spec words kernel hkernel htable htableCall state.1 state.2
        hstateInvariant
    unfold outerBody at hbody
    unfold outerLoop at hresult
    refine ⟨result, ?_, hcanonical, hexact⟩
    unfold outerLoop
    unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hresult
  · rcases hinvariant with ⟨hcoordinate19, hcanonical, hexact⟩
    have hfinal : coordinate.val = 19 := by omega
    have hcondition : ¬ coordinate ≤ (18#usize : Std.Usize) := by
      intro hle
      exact hcontinue (by
        have := (UScalar.le_equiv _ _).1 hle
        simpa using this)
    have hbodyDone : outerBody kernel values coordinate =
        .ok (.done values) := by
      unfold outerBody
      unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0.body
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [kernelDegreeHalf_call]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [if_neg hcondition]
    unfold outerBody at hbodyDone
    refine ⟨values, ?_, hcanonical, ?_⟩
    · unfold outerLoop
      unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural_loop0
      rw [loop.eq_def]
      simp only
      rw [hbodyDone]
    · simpa [hfinal] using hexact
termination_by 19 - coordinate.val
decreasing_by
  rw [hcoordinateNext]
  omega

private theorem repeated_zero_canonical :
    GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector
      (Array.repeat 48#usize (0#u32 : LocalM31)) := by
  intro index
  unfold GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48 Array.repeat
  rw [List.getElem_replicate]
  change (0 : Nat) < AspisV5ComponentCQM31TowerExact.P
  norm_num [AspisV5ComponentCQM31TowerExact.P]

private theorem repeated_zero_expected (words : WordModel)
    (kernel : LocalKernel) :
    GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48
        (Array.repeat 48#usize (0#u32 : LocalM31)) =
      expectedNatural words kernel 0 := by
  funext index
  unfold GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48
    GoodMatricesCurrent.SourceExtractedEvenKernel.arrayEntry48
    GoodMatricesCurrent.SourceExtractedEvenKernel.m31ToExact Array.repeat
    expectedNatural
  rw [List.getElem_replicate]
  simp

private theorem evenKernelRuntime_expected (words : WordModel)
    (kernel : LocalKernel) (hkernel : CanonicalLocalKernel kernel)
    (htable : TableBound words) (htableCall : TableCalls words) :
    ∃ output : LocalVector,
      v5_cu_probe.good_gate_probe.even_kernel_to_natural kernel = .ok output ∧
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector output ∧
      GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48 output =
        expectedNatural words kernel 19 := by
  let zero : LocalM31 := 0#u32
  let initial : LocalVector := Array.repeat 48#usize zero
  have hzeroCall : aspis_verifier.aspis_core.field.M31.ZERO = .ok zero := by
    unfold aspis_verifier.aspis_core.field.M31.ZERO zero
    rw [_root_.aspis_core.field.M31.ZERO]
  have hinitialCanonical :
      GoodMatricesCurrent.SourceExtractedEvenKernel.CanonicalLocalVector initial := by
    exact repeated_zero_canonical
  have hinitialExact :
      GoodMatricesCurrent.SourceExtractedEvenKernel.arrayToExact48 initial =
        expectedNatural words kernel 0 := by
    exact repeated_zero_expected words kernel
  have hinitialInvariant : OuterInvariant words kernel initial 0#usize := by
    exact ⟨by norm_num, hinitialCanonical, hinitialExact⟩
  obtain ⟨output, hloop, hcanonical, hexact⟩ :=
    outerLoop_spec words kernel hkernel htable htableCall initial 0#usize
      hinitialInvariant
  refine ⟨output, ?_, hcanonical, hexact⟩
  unfold v5_cu_probe.good_gate_probe.even_kernel_to_natural
  rw [hzeroCall]
  unfold outerLoop at hloop
  exact hloop


private def sourceWords : WordModel := parityTableEntry

private theorem sourceWords_row_0_bound (column : Fin 19) :
    (sourceWords (0 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(0 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (0 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_1_bound (column : Fin 19) :
    (sourceWords (1 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(1 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (1 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_2_bound (column : Fin 19) :
    (sourceWords (2 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(2 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (2 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_3_bound (column : Fin 19) :
    (sourceWords (3 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(3 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (3 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_4_bound (column : Fin 19) :
    (sourceWords (4 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(4 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (4 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_5_bound (column : Fin 19) :
    (sourceWords (5 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(5 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (5 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_6_bound (column : Fin 19) :
    (sourceWords (6 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(6 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (6 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_7_bound (column : Fin 19) :
    (sourceWords (7 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(7 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (7 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_8_bound (column : Fin 19) :
    (sourceWords (8 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(8 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (8 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_9_bound (column : Fin 19) :
    (sourceWords (9 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(9 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (9 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_10_bound (column : Fin 19) :
    (sourceWords (10 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(10 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (10 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_11_bound (column : Fin 19) :
    (sourceWords (11 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(11 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (11 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_12_bound (column : Fin 19) :
    (sourceWords (12 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(12 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (12 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_13_bound (column : Fin 19) :
    (sourceWords (13 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(13 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (13 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_14_bound (column : Fin 19) :
    (sourceWords (14 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(14 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (14 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_15_bound (column : Fin 19) :
    (sourceWords (15 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(15 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (15 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_16_bound (column : Fin 19) :
    (sourceWords (16 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(16 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (16 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_17_bound (column : Fin 19) :
    (sourceWords (17 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(17 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (17 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_row_18_bound (column : Fin 19) :
    (sourceWords (18 : Fin 24) ⟨column.val, by omega⟩).val < 2 ^ 31 := by
  unfold sourceWords
  change
    (parityTableEntry ⟨(18 : Fin 19).val, by omega⟩
      ⟨column.val, by omega⟩).val < 2 ^ 31
  rw [parityTableEntry_used (18 : Fin 19)]
  fin_cases column <;> decide

private theorem sourceWords_fin_bound (row column : Fin 19) :
    (sourceWords ⟨row.val, by omega⟩ ⟨column.val, by omega⟩).val <
      2 ^ 31 := by
  fin_cases row
  · exact sourceWords_row_0_bound column
  · exact sourceWords_row_1_bound column
  · exact sourceWords_row_2_bound column
  · exact sourceWords_row_3_bound column
  · exact sourceWords_row_4_bound column
  · exact sourceWords_row_5_bound column
  · exact sourceWords_row_6_bound column
  · exact sourceWords_row_7_bound column
  · exact sourceWords_row_8_bound column
  · exact sourceWords_row_9_bound column
  · exact sourceWords_row_10_bound column
  · exact sourceWords_row_11_bound column
  · exact sourceWords_row_12_bound column
  · exact sourceWords_row_13_bound column
  · exact sourceWords_row_14_bound column
  · exact sourceWords_row_15_bound column
  · exact sourceWords_row_16_bound column
  · exact sourceWords_row_17_bound column
  · exact sourceWords_row_18_bound column

private theorem sourceWords_bound : TableBound sourceWords := by
  intro row column hrow hcolumn
  unfold modelWord
  exact sourceWords_fin_bound ⟨row, hrow⟩ ⟨column, hcolumn⟩

private theorem sourceWords_calls : TableCalls sourceWords := by
  intro row column hrow hcolumn
  have hrowLength : row.val <
      v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY.length := by
    change row.val <
      v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY.val.length
    rw [v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY.property]
    norm_num
    omega
  obtain ⟨tableRow, htableRow, htableRowValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec
      v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY row hrowLength)
  have hcolumnLength : column.val < tableRow.length := by
    change column.val < tableRow.val.length
    rw [tableRow.property]
    norm_num
    omega
  obtain ⟨coefficient, hcoefficient, hcoefficientValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec tableRow column hcolumnLength)
  subst tableRow
  refine ⟨_, coefficient, htableRow, hcoefficient, ?_⟩
  unfold modelWord sourceWords parityTableEntry
  simpa using hcoefficientValue

private def modelParityRow (words : WordModel) (degreeHalf : Fin 19) :
    Fin 48 → ExactM31 :=
  fun coordinate =>
    if coordinate.val % 2 = 0 then
      let naturalHalf := coordinate.val / 2
      if hhalf : naturalHalf ≤ degreeHalf.val then
        ((modelWord words degreeHalf.val naturalHalf degreeHalf.isLt
          (by omega)).val : Nat)
      else 0
    else 0

private def modelKernelCoefficient (kernel : LocalKernel)
    (degreeHalf : Fin 19) : ExactM31 :=
  ((kernelWord kernel degreeHalf.val degreeHalf.isLt).val : Nat)

private theorem expectedNatural_eq_modelCombination (words : WordModel)
    (kernel : LocalKernel) :
    expectedNatural words kernel 19 =
      Fintype.linearCombination ExactM31 (modelParityRow words)
        (modelKernelCoefficient kernel) := by
  funext coordinate
  by_cases heven : coordinate.val % 2 = 0
  · by_cases hhalf : coordinate.val / 2 < 19
    · let column : Fin 19 := ⟨coordinate.val / 2, hhalf⟩
      have hfilter :
          (Finset.range 19).filter (fun row => column.val ≤ row) =
            Finset.Ico column.val 19 := by
        ext row
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      have hsum :
          (∑ row ∈ Finset.range 19,
            if hrow : row < 19 then
              modelKernelCoefficient kernel ⟨row, hrow⟩ *
                modelParityRow words ⟨row, hrow⟩ coordinate
            else 0) =
          ∑ row ∈ Finset.range 19,
            if column.val ≤ row then
              exactTerm words kernel column.val row
            else 0 := by
        apply Finset.sum_congr rfl
        intro row hrowMem
        have hrow : row < 19 := Finset.mem_range.mp hrowMem
        rw [dif_pos hrow]
        by_cases hle : column.val ≤ row
        · rw [if_pos hle]
          unfold modelParityRow
          rw [if_pos heven]
          dsimp only
          have hle' : coordinate.val / 2 ≤ row := by simpa [column] using hle
          rw [dif_pos hle']
          unfold modelKernelCoefficient exactTerm rawTerm
          rw [dif_pos hrow, dif_pos hhalf, Nat.cast_mul]
        · rw [if_neg hle]
          unfold modelParityRow
          rw [if_pos heven]
          dsimp only
          have hle' : ¬ coordinate.val / 2 ≤ row := by simpa [column] using hle
          rw [dif_neg hle']
          simp
      have hrange :
          (∑ degree : Fin 19,
            modelKernelCoefficient kernel degree *
              modelParityRow words degree coordinate) =
          ∑ row ∈ Finset.range 19,
            if hrow : row < 19 then
              modelKernelCoefficient kernel ⟨row, hrow⟩ *
                modelParityRow words ⟨row, hrow⟩ coordinate
            else 0 := by
        rw [Finset.sum_fin_eq_sum_range]
      unfold expectedNatural
      rw [if_pos ⟨heven, hhalf⟩]
      change exactRange words kernel column.val column.val 19 = _
      simp only [Fintype.linearCombination_apply, Fintype.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hrange, hsum]
      symm
      calc
        (∑ row ∈ Finset.range 19,
            if column.val ≤ row then exactTerm words kernel column.val row
            else 0) =
            ∑ row ∈ (Finset.range 19).filter (fun row => column.val ≤ row),
              exactTerm words kernel column.val row := by
          rw [Finset.sum_filter]
        _ = ∑ row ∈ Finset.Ico column.val 19,
              exactTerm words kernel column.val row := by rw [hfilter]
        _ = exactRange words kernel column.val column.val 19 := by rfl
    · unfold expectedNatural
      rw [if_neg (by aesop)]
      simp only [Fintype.linearCombination_apply, Fintype.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      have hzero : ∀ degree : Fin 19,
          modelParityRow words degree coordinate = 0 := by
        intro degree
        have hle : ¬ coordinate.val / 2 ≤ degree.val := by omega
        simp [modelParityRow, heven, hle]
      simp_rw [hzero]
      simp
  · unfold expectedNatural
    rw [if_neg (by aesop)]
    simp only [Fintype.linearCombination_apply, Fintype.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    have hzero : ∀ degree : Fin 19,
        modelParityRow words degree coordinate = 0 := by
      intro degree
      simp [modelParityRow, heven]
    simp_rw [hzero]
    simp

private theorem evenKernelOrdinary_eq_linearCombination (kernel : LocalKernel) :
    GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary kernel =
      Fintype.linearCombination ExactM31 evenBasis
        (modelKernelCoefficient kernel) := by
  classical
  funext coordinate
  simp only [Fintype.linearCombination_apply, Fintype.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hdegree : coordinate.val < 37
  · by_cases heven : coordinate.val % 2 = 0
    · have hhalf : coordinate.val / 2 < 19 := by omega
      let index : Fin 19 := ⟨coordinate.val / 2, hhalf⟩
      have hdouble : 2 * (coordinate.val / 2) = coordinate.val := by omega
      have htarget : AspisV5GoodGateSparseShift.sourceIndex
          (evenSource index) = coordinate := by
        apply Fin.ext
        simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex,
          index, hdouble]
      rw [Fintype.sum_eq_single index]
      · simp [GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary,
          hdegree, heven, evenBasis, htarget, modelKernelCoefficient,
          kernelWord, kernelEntry, index, hdouble]
      · intro other hne
        have htargetNe : AspisV5GoodGateSparseShift.sourceIndex
            (evenSource other) ≠ coordinate := by
          intro equal
          apply hne
          apply Fin.ext
          have hvalue := congrArg Fin.val equal
          simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex,
            index] at hvalue ⊢
          omega
        simp [evenBasis, htargetNe]
    · rw [show GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
          kernel coordinate = 0 by
        simp [GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary,
          hdegree, heven]]
      have hzero : ∀ index : Fin 19, evenBasis index coordinate = 0 := by
        intro index
        have htargetNe : AspisV5GoodGateSparseShift.sourceIndex
            (evenSource index) ≠ coordinate := by
          intro equal
          have hvalue := congrArg Fin.val equal
          simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hvalue
          omega
        simp [evenBasis, htargetNe]
      simp_rw [hzero]
      simp
  · rw [show GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
        kernel coordinate = 0 by
      simp [GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary,
        hdegree]]
    have hzero : ∀ index : Fin 19, evenBasis index coordinate = 0 := by
      intro index
      have htargetNe : AspisV5GoodGateSparseShift.sourceIndex
          (evenSource index) ≠ coordinate := by
        intro equal
        have hvalue := congrArg Fin.val equal
        simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hvalue
        omega
      simp [evenBasis, htargetNe]
    simp_rw [hzero]
    simp

private theorem modelParityRow_source (degreeHalf : Fin 19) :
    modelParityRow sourceWords degreeHalf = parityRow degreeHalf := by
  funext coordinate
  unfold modelParityRow parityRow
  by_cases heven : coordinate.val % 2 = 0
  · rw [if_pos heven, if_pos heven]
    dsimp only
    by_cases hhalf : coordinate.val / 2 ≤ degreeHalf.val
    · rw [dif_pos hhalf, if_pos hhalf]
      unfold modelWord sourceWords parityTableExact usedRowIndex
      rfl
    · rw [dif_neg hhalf, if_neg hhalf]
  · rw [if_neg heven, if_neg heven]

private theorem convert_evenBasis_zero :
    AspisV5GoodGateSparseShift.convert (evenBasis (0 : Fin 19)) =
      evenBasis (0 : Fin 19) := by
  letI : NeZero (2 : ExactM31) := ⟨by decide⟩
  apply AspisV5GoodGateSparseShift.naturalSynthesis_injective
  rw [AspisV5GoodGateSparseShift.naturalSynthesis_convert]
  have hbasis : evenBasis (0 : Fin 19) =
      Pi.single (0 : Fin 48) (1 : ExactM31) := by rfl
  rw [hbasis, AspisV5GoodGateSparseShift.naturalSynthesis_single]
  classical
  simp [AspisV5GoodGateSparseShift.ordinarySynthesis,
    Pi.single_apply, AspisCircleTensorBinding.naturalLinePoly]

private theorem ordinaryShift_twice_evenBasis (index : Fin 18) :
    AspisV5GoodGateSparseShift.ordinaryShift
        (AspisV5GoodGateSparseShift.ordinaryShift
          (evenBasis ⟨index.val, by omega⟩)) =
      evenBasis ⟨index.val + 1, by omega⟩ := by
  funext coordinate
  refine Fin.cases ?_ (fun previous => ?_) coordinate
  · change 0 = evenBasis ⟨index.val + 1, by omega⟩ (0 : Fin 48)
    unfold evenBasis
    rw [Pi.single_eq_of_ne]
    intro heq
    have hval := congrArg Fin.val heq
    simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hval
  · refine Fin.cases ?_ (fun previous2 => ?_) previous
    · change 0 = evenBasis ⟨index.val + 1, by omega⟩ (1 : Fin 48)
      unfold evenBasis
      rw [Pi.single_eq_of_ne]
      intro heq
      have hval := congrArg Fin.val heq
      simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hval
    · change evenBasis ⟨index.val, by omega⟩
          ⟨previous2.val, by omega⟩ =
        evenBasis ⟨index.val + 1, by omega⟩
          ⟨previous2.val + 2, by omega⟩
      unfold evenBasis
      by_cases heq : previous2.val = 2 * index.val
      · have hleft :
            (⟨previous2.val, by omega⟩ : Fin 48) =
              AspisV5GoodGateSparseShift.sourceIndex
                (evenSource ⟨index.val, by omega⟩) := by
          apply Fin.ext
          simpa [evenSource, AspisV5GoodGateSparseShift.sourceIndex]
            using heq
        have hright :
            (⟨previous2.val + 2, by omega⟩ : Fin 48) =
              AspisV5GoodGateSparseShift.sourceIndex
                (evenSource ⟨index.val + 1, by omega⟩) := by
          apply Fin.ext
          simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex]
          omega
        rw [hleft, hright, Pi.single_eq_same, Pi.single_eq_same]
      · have hleft :
            AspisV5GoodGateSparseShift.sourceIndex
                (evenSource ⟨index.val, by omega⟩) ≠
              (⟨previous2.val, by omega⟩ : Fin 48) := by
          intro equal
          apply heq
          have hval := congrArg Fin.val equal
          simpa [evenSource, AspisV5GoodGateSparseShift.sourceIndex]
            using hval.symm
        have hright :
            AspisV5GoodGateSparseShift.sourceIndex
                (evenSource ⟨index.val + 1, by omega⟩) ≠
              (⟨previous2.val + 2, by omega⟩ : Fin 48) := by
          intro equal
          apply heq
          have hval := congrArg Fin.val equal
          simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hval
          omega
        rw [Pi.single_eq_of_ne hleft.symm,
          Pi.single_eq_of_ne hright.symm]

private theorem convert_evenBasis_linearCombination
    (coefficients : Fin 19 → ExactM31) :
    AspisV5GoodGateSparseShift.convert
        (Fintype.linearCombination ExactM31 evenBasis coefficients) =
      Fintype.linearCombination ExactM31
        (fun index =>
          AspisV5GoodGateSparseShift.convert (evenBasis index))
        coefficients := by
  unfold AspisV5GoodGateSparseShift.convert
  change
    (AspisCircleTensorBinding.monomialToNatural ExactM31 48).mulVecLin
        (Fintype.linearCombination ExactM31 evenBasis coefficients) = _
  exact AspisV5GoodGateSparseShift.map_fintypeLinearCombination
    (AspisCircleTensorBinding.monomialToNatural ExactM31 48).mulVecLin
    evenBasis coefficients

private theorem parityRow_step (index : Fin 18) :
    parityRow ⟨index.val + 1, by omega⟩ =
      sparseShift (sparseShift (parityRow ⟨index.val, by omega⟩)) := by
  rw [sparseShift_twice_parityRow]
  fin_cases index
  · exact parityRow_step_factored_0
  · exact parityRow_step_factored_1
  · exact parityRow_step_factored_2
  · exact parityRow_step_factored_3
  · exact parityRow_step_factored_4
  · exact parityRow_step_factored_5
  · exact parityRow_step_factored_6
  · exact parityRow_step_factored_7
  · exact parityRow_step_factored_8
  · exact parityRow_step_factored_9
  · exact parityRow_step_factored_10
  · exact parityRow_step_factored_11
  · exact parityRow_step_factored_12
  · exact parityRow_step_factored_13
  · exact parityRow_step_factored_14
  · exact parityRow_step_factored_15
  · exact parityRow_step_factored_16
  · exact parityRow_step_factored_17

private theorem evenBasis_top_zero (index : Fin 19) :
    evenBasis index (47 : Fin 48) = 0 := by
  unfold evenBasis
  rw [Pi.single_eq_of_ne]
  intro heq
  have hval := congrArg Fin.val heq
  simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hval
  omega

private theorem ordinaryShift_evenBasis_top_zero (index : Fin 18) :
    AspisV5GoodGateSparseShift.ordinaryShift
        (evenBasis ⟨index.val, by omega⟩) (47 : Fin 48) = 0 := by
  change evenBasis ⟨index.val, by omega⟩ (46 : Fin 48) = 0
  unfold evenBasis
  rw [Pi.single_eq_of_ne]
  intro heq
  have hval := congrArg Fin.val heq
  simp [evenSource, AspisV5GoodGateSparseShift.sourceIndex] at hval
  omega

private theorem parityRow_eq_convert_evenBasis_nat :
    ∀ n : Nat, (hn : n < 19) →
      parityRow ⟨n, hn⟩ =
        AspisV5GoodGateSparseShift.convert (evenBasis ⟨n, hn⟩) := by
  intro n
  induction n with
  | zero =>
      intro hn
      have hindex : (⟨0, hn⟩ : Fin 19) = (0 : Fin 19) := Fin.ext rfl
      rw [hindex, parityRow_zero, convert_evenBasis_zero]
      rfl
  | succ n inductionHypothesis =>
      intro hn
      letI : NeZero (2 : ExactM31) := ⟨by decide⟩
      have hn18 : n < 18 := by omega
      have hprevious := inductionHypothesis (by omega)
      rw [parityRow_step ⟨n, hn18⟩, hprevious]
      rw [AspisV5GoodGateSparseShift.sparseShift_convert
        (evenBasis ⟨n, by omega⟩) (evenBasis_top_zero _)]
      rw [AspisV5GoodGateSparseShift.sparseShift_convert
        (AspisV5GoodGateSparseShift.ordinaryShift
          (evenBasis ⟨n, by omega⟩))
        (ordinaryShift_evenBasis_top_zero ⟨n, hn18⟩)]
      rw [ordinaryShift_twice_evenBasis ⟨n, hn18⟩]

private theorem parityRow_eq_convert_evenBasis (index : Fin 19) :
    parityRow index =
      AspisV5GoodGateSparseShift.convert (evenBasis index) := by
  exact parityRow_eq_convert_evenBasis_nat index.val index.isLt

private theorem expectedNatural_source_eq_convert (kernel : LocalKernel) :
    expectedNatural sourceWords kernel 19 =
      AspisV5GoodGateSparseShift.convert
        (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
          kernel) := by
  calc
    expectedNatural sourceWords kernel 19 =
        Fintype.linearCombination ExactM31 (modelParityRow sourceWords)
          (modelKernelCoefficient kernel) :=
      expectedNatural_eq_modelCombination sourceWords kernel
    _ = Fintype.linearCombination ExactM31 parityRow
          (modelKernelCoefficient kernel) := by
      apply fintypeLinearCombination_congr
      intro index
      exact modelParityRow_source index
    _ = Fintype.linearCombination ExactM31
          (fun index =>
            AspisV5GoodGateSparseShift.convert (evenBasis index))
          (modelKernelCoefficient kernel) := by
      apply fintypeLinearCombination_congr
      intro index
      exact parityRow_eq_convert_evenBasis index
    _ = AspisV5GoodGateSparseShift.convert
          (Fintype.linearCombination ExactM31 evenBasis
            (modelKernelCoefficient kernel)) :=
      (convert_evenBasis_linearCombination
        (modelKernelCoefficient kernel)).symm
    _ = AspisV5GoodGateSparseShift.convert
          (GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary
            kernel) := by
      rw [evenKernelOrdinary_eq_linearCombination]

/-- Public, source-table-shaped exact model of the extracted even-kernel
conversion.  Unlike the dense conversion presentation, this keeps the
literal 19-row parity computation available for default-limit concrete
replay. -/
def sourceParityConversion (kernel : LocalKernel) : Fin 48 → ExactM31 :=
  expectedNatural sourceWords kernel 19

/-- One exact word of the authentic source conversion table, restricted to
the 19-by-19 triangle reached by an even degree-36 kernel. -/
def sourceParityTableWord (row column : Fin 19) : ExactM31 :=
  let table := v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY
  let tableRow := table.val[row.val]'(by
    rw [table.property]
    simpa using (show row.val < 24 by omega))
  ((tableRow.val[column.val]'(by
    rw [tableRow.property]
    simpa using (show column.val < 24 by omega))).val : Nat)

/-- The even ordinary-kernel coefficient used by one source table row. -/
def sourceParityKernelCoefficient (kernel : LocalKernel)
    (row : Fin 19) : ExactM31 :=
  let coefficient := kernel.val[2 * row.val]'(by
    rw [kernel.property]
    simpa using (show 2 * row.val < 37 by omega))
  (coefficient.val : Nat)

/-- Literal exact row of the source parity table. -/
def sourceParityRow (row : Fin 19) : Fin 48 → ExactM31 :=
  fun coordinate =>
    if heven : coordinate.val % 2 = 0 then
      let column := coordinate.val / 2
      if hcolumn : column ≤ row.val then
        sourceParityTableWord row ⟨column, by omega⟩
      else 0
    else 0

/-- Public finite-sum presentation of the exact source parity conversion.
This is deliberately computational: concrete callers can normalize nineteen
source-table products without unfolding the proved runtime loop invariant. -/
def sourceParityFormula (kernel : LocalKernel) : Fin 48 → ExactM31 :=
  Fintype.linearCombination ExactM31 sourceParityRow
    (sourceParityKernelCoefficient kernel)

theorem sourceParityConversion_eq_formula (kernel : LocalKernel) :
    sourceParityConversion kernel = sourceParityFormula kernel := by
  have hrows :
      modelParityRow sourceWords = sourceParityRow := by
    funext row coordinate
    unfold modelParityRow sourceParityRow sourceParityTableWord
    unfold modelWord sourceWords parityTableEntry
    rfl
  have hcoefficients :
      modelKernelCoefficient kernel =
        sourceParityKernelCoefficient kernel := by
    funext row
    unfold modelKernelCoefficient sourceParityKernelCoefficient kernelWord
    unfold kernelEntry
    rfl
  unfold sourceParityConversion sourceParityFormula
  rw [expectedNatural_eq_modelCombination, hrows, hcoefficients]

theorem sourceParityConversion_eq_convert (kernel : LocalKernel) :
    sourceParityConversion kernel =
      AspisV5GoodGateSparseShift.convert (evenKernelOrdinary kernel) := by
  exact expectedNatural_source_eq_convert kernel

/-- Exact source-level specification retaining the literal parity-table
model before its separately proved equality with the dense maintained
conversion. -/
theorem even_kernel_to_natural_source_model_spec
    (kernel : Array LocalM31 37#usize)
    (hkernel : CanonicalLocalKernel kernel) :
    ∃ output,
      v5_cu_probe.good_gate_probe.even_kernel_to_natural kernel = .ok output ∧
      CanonicalLocalVector output ∧
      arrayToExact48 output = sourceParityConversion kernel := by
  obtain ⟨output, hcall, hcanonical, hexact⟩ :=
    evenKernelRuntime_expected sourceWords kernel hkernel sourceWords_bound
      sourceWords_calls
  exact ⟨output, hcall, hcanonical, hexact⟩

/-- The converted even kernel has exactly the parity and degree support used
by the extracted fixed-support shift chain: only even coordinates below 37
can be nonzero.  This is the public support corollary of the certified literal
parity-row conversion above. -/
theorem convert_evenKernelOrdinary_fixed_support (kernel : LocalKernel) :
    ∀ coordinate : Fin 48,
      (coordinate.val % 2 ≠ 0 ∨ 37 ≤ coordinate.val) →
        AspisV5GoodGateSparseShift.convert (evenKernelOrdinary kernel)
          coordinate = 0 := by
  have hconvert :
      AspisV5GoodGateSparseShift.convert (evenKernelOrdinary kernel) =
        Fintype.linearCombination ExactM31 parityRow
          (modelKernelCoefficient kernel) := by
    rw [evenKernelOrdinary_eq_linearCombination,
      convert_evenBasis_linearCombination]
    apply fintypeLinearCombination_congr
    intro index
    exact (parityRow_eq_convert_evenBasis index).symm
  intro coordinate houtside
  rw [hconvert]
  simp only [Fintype.linearCombination_apply, Fintype.sum_apply,
    Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro degree _
  have hrow : parityRow degree coordinate = 0 := by
    rcases houtside with hparity | habove
    · have hodd : coordinate.val % 2 ≠ 0 := hparity
      simp [parityRow, hodd]
    · by_cases heven : coordinate.val % 2 = 0
      · have hhalf : ¬ coordinate.val / 2 ≤ degree.val := by omega
        simp [parityRow, heven, hhalf]
      · simp [parityRow, heven]
  rw [hrow, smul_zero]

/-- Exact source-level specification of the extracted even-kernel conversion.
The result is canonical and equals the formal ordinary-to-natural conversion. -/
theorem even_kernel_to_natural_exact_spec
    (kernel : Array LocalM31 37#usize)
    (hkernel : CanonicalLocalKernel kernel) :
    ∃ output,
      v5_cu_probe.good_gate_probe.even_kernel_to_natural kernel = .ok output ∧
      CanonicalLocalVector output ∧
      arrayToExact48 output =
        AspisV5GoodGateSparseShift.convert (evenKernelOrdinary kernel) := by
  obtain ⟨output, hcall, hcanonical, hexact⟩ :=
    evenKernelRuntime_expected sourceWords kernel hkernel sourceWords_bound
      sourceWords_calls
  refine ⟨output, hcall, hcanonical, ?_⟩
  rw [hexact]
  exact expectedNatural_source_eq_convert kernel

#print axioms even_kernel_to_natural_exact_spec
#print axioms even_kernel_to_natural_source_model_spec
#print axioms sourceParityConversion_eq_formula
#print axioms sourceParityConversion_eq_convert
#print axioms convert_evenKernelOrdinary_fixed_support

end GoodMatricesCurrent.SourceExtractedEvenKernel
