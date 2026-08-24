import V5RelationCompactNewGenerated
import V5RelationGeneratedFieldProjection
import V5RelationLinkedFoldArithmetic
import AspisFormal.V5CompactTerminalOptimized
import HalfProof

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CompactScratchNew

open Aeneas Aeneas.Std Result ControlFlow Error
open V5RelationCompactNewGenerated

abbrev Raw := V5RelationCompactNewGenerated.aspis_core.field.QM31
abbrev Block := V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev State :=
  V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights
abbrev FullRaw := V5RelationFullGenerated.aspis_core.field.QM31
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited Raw :=
  ⟨V5RelationCompactNewGenerated.aspis_core.field.QM31.ZERO⟩

def toFull (value : Raw) : FullRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def fromFull (value : FullRaw) : Raw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

@[simp] theorem toFull_fromFull (value : FullRaw) :
    toFull (fromFull value) = value := by cases value <;> rfl

@[simp] theorem fromFull_toFull (value : Raw) :
    fromFull (toFull value) = value := by cases value <;> rfl

def Canonical (value : Raw) : Prop :=
  AspisV5RelationGeneratedFieldProjection.CanonicalQM31 (toFull value)

def toExact (value : Raw) : K :=
  AspisV5RelationGeneratedFieldProjection.toMaintainedExact (toFull value)

private theorem oldMap_fullToExact (value : FullRaw) :
    AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained
        (AspisV5RelationGeneratedFieldProjection.toExact value) =
      AspisV5RelationGeneratedFieldProjection.toMaintainedExact value := by
  rfl

private theorem P_eq_full :
    V5RelationCompactNewGenerated.aspis_core.field.P =
      V5RelationFullGenerated.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationCompactNewGenerated.aspis_core.field.P
    V5RelationFullGenerated.aspis_core.field.P
  rfl

private theorem reduce_u64_eq_full (value : Std.U64) :
    V5RelationCompactNewGenerated.aspis_core.field.reduce_u64 value =
      V5RelationFullGenerated.aspis_core.field.reduce_u64 value := by
  unfold V5RelationCompactNewGenerated.aspis_core.field.reduce_u64
    V5RelationFullGenerated.aspis_core.field.reduce_u64
  rw [P_eq_full]

private theorem m31_add_eq_full
    (left right : V5RelationCompactNewGenerated.aspis_core.field.M31) :
    V5RelationCompactNewGenerated.aspis_core.field.M31.add left right =
      V5RelationFullGenerated.aspis_core.field.M31.add left right := by
  unfold V5RelationCompactNewGenerated.aspis_core.field.M31.add
    V5RelationFullGenerated.aspis_core.field.M31.add
  rw [P_eq_full]

private theorem m31_sub_eq_full
    (left right : V5RelationCompactNewGenerated.aspis_core.field.M31) :
    V5RelationCompactNewGenerated.aspis_core.field.M31.sub left right =
      V5RelationFullGenerated.aspis_core.field.M31.sub left right := by
  unfold V5RelationCompactNewGenerated.aspis_core.field.M31.sub
    V5RelationFullGenerated.aspis_core.field.M31.sub
  rw [P_eq_full]

private theorem m31_mul_eq_full
    (left right : V5RelationCompactNewGenerated.aspis_core.field.M31) :
    V5RelationCompactNewGenerated.aspis_core.field.M31.mul left right =
      V5RelationFullGenerated.aspis_core.field.M31.mul left right := by
  unfold V5RelationCompactNewGenerated.aspis_core.field.M31.mul
    V5RelationFullGenerated.aspis_core.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [reduce_u64_eq_full]

private theorem m31_half_eq_half
    (value : V5RelationCompactNewGenerated.aspis_core.field.M31) :
    V5RelationCompactNewGenerated.aspis_core.field.M31.half value =
      AspisCoreHalf.field.M31.half value := by
  unfold V5RelationCompactNewGenerated.aspis_core.field.M31.half
    AspisCoreHalf.field.M31.half
  rw [show V5RelationCompactNewGenerated.aspis_core.field.P =
      AspisCoreHalf.field.P by
    apply UScalar.eq_of_val_eq
    unfold V5RelationCompactNewGenerated.aspis_core.field.P
      AspisCoreHalf.field.P
    rfl]
  simp only [halfShiftCountOne_exact]

private theorem square_toFull (value : Raw) :
    (do
      let output <-
        V5RelationCompactNewGenerated.aspis_core.field.QM31.square value
      ok (toFull output)) =
    V5RelationFullGenerated.aspis_core.field.QM31.square (toFull value) := by
  simp [V5RelationCompactNewGenerated.aspis_core.field.QM31.square,
    V5RelationFullGenerated.aspis_core.field.QM31.square,
    V5RelationCompactNewGenerated.aspis_core.field.CM31.square,
    V5RelationFullGenerated.aspis_core.field.CM31.square,
    V5RelationCompactNewGenerated.aspis_core.field.CM31.mul,
    V5RelationFullGenerated.aspis_core.field.CM31.mul,
    V5RelationCompactNewGenerated.aspis_core.field.CM31.double,
    V5RelationFullGenerated.aspis_core.field.CM31.double,
    V5RelationCompactNewGenerated.aspis_core.field.CM31.add,
    V5RelationFullGenerated.aspis_core.field.CM31.add,
    V5RelationCompactNewGenerated.aspis_core.field.M31.double,
    V5RelationFullGenerated.aspis_core.field.M31.double,
    V5RelationCompactNewGenerated.aspis_core.field.mul_by_r,
    V5RelationFullGenerated.aspis_core.field.mul_by_r,
    m31_add_eq_full, m31_sub_eq_full, m31_mul_eq_full, toFull]

theorem square_corresponds (value : Raw) (canonical : Canonical value) :
    ∃ output : Raw,
      V5RelationCompactNewGenerated.aspis_core.field.QM31.square value =
        ok output ∧
      Canonical output ∧ toExact output = toExact value ^ 2 := by
  obtain ⟨output, run, outputCanonical, exact⟩ :=
    AspisV5RelationGeneratedFieldProjection.generated_qm31_square_corresponds
      (toFull value) canonical
  refine ⟨fromFull output, ?_, ?_, ?_⟩
  · have mapped := square_toFull value
    rw [run] at mapped
    generalize compactRun :
      V5RelationCompactNewGenerated.aspis_core.field.QM31.square value =
        compactResult at mapped
    cases compactResult with
    | fail error => simp at mapped
    | div => simp at mapped
    | ok compactOutput =>
      simp only [bind_tc_ok] at mapped
      have outputEquality : compactOutput = fromFull output := by
        have mappedValue : toFull compactOutput = output := Result.ok.inj mapped
        have mappedBack := congrArg fromFull mappedValue
        simpa using mappedBack
      simpa [compactRun, outputEquality]
  · simpa [Canonical] using outputCanonical
  · have exactM := congrArg
        AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained exact
    simpa only [toExact, toFull_fromFull, oldMap_fullToExact, pow_two,
      AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_mul] using exactM

theorem square_exact (input output : Raw) (canonical : Canonical input)
    (run : V5RelationCompactNewGenerated.aspis_core.field.QM31.square input =
      ok output) :
    Canonical output ∧ toExact output = toExact input ^ 2 := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    square_corresponds input canonical
  rw [run] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

theorem half_corresponds (value : Raw) (canonical : Canonical value) :
    ∃ output : Raw,
      V5RelationCompactNewGenerated.aspis_core.field.QM31.half value =
        ok output ∧
      Canonical output ∧ toExact output + toExact output = toExact value := by
  have m31Half
      (input : V5RelationCompactNewGenerated.aspis_core.field.M31)
      (inputCanonical :
        AspisAeneasCM31Multiplicative.CanonicalRawM31 input.val) :
      ∃ output : V5RelationCompactNewGenerated.aspis_core.field.M31,
        V5RelationCompactNewGenerated.aspis_core.field.M31.half input =
          ok output ∧
        AspisAeneasCM31Multiplicative.CanonicalRawM31 output.val ∧
        ((output.val : Nat) : ComponentBRealEvaluatorProof.ExactM31) +
            (output.val : ComponentBRealEvaluatorProof.ExactM31) =
          (input.val : ComponentBRealEvaluatorProof.ExactM31) := by
    obtain ⟨output, oldRun, _, outputCanonical, exact⟩ :=
      AspisAeneasHalf.extracted_m31_half_corresponds input inputCanonical
    refine ⟨output, ?_, outputCanonical, ?_⟩
    · rw [m31_half_eq_half]
      exact oldRun
    · have twoNeZero :
          (2 : ComponentBRealEvaluatorProof.ExactM31) ≠ 0 := by decide
      rw [← mul_two]
      exact (eq_div_iff twoNeZero).1 exact
  obtain ⟨o00, h00, c00, e00⟩ := m31Half value.c0.a canonical.1.1
  obtain ⟨o01, h01, c01, e01⟩ := m31Half value.c0.b canonical.1.2
  obtain ⟨o10, h10, c10, e10⟩ := m31Half value.c1.a canonical.2.1
  obtain ⟨o11, h11, c11, e11⟩ := m31Half value.c1.b canonical.2.2
  let output : Raw := ⟨⟨o00, o01⟩, ⟨o10, o11⟩⟩
  refine ⟨output, ?_, ⟨⟨c00, c01⟩, ⟨c10, c11⟩⟩, ?_⟩
  · simp [V5RelationCompactNewGenerated.aspis_core.field.QM31.half,
      V5RelationCompactNewGenerated.aspis_core.field.CM31.half,
      h00, h01, h10, h11, output]
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext <;> assumption
    · apply QuadraticAlgebra.ext <;> assumption

theorem half_exact (input output : Raw) (canonical : Canonical input)
    (run : V5RelationCompactNewGenerated.aspis_core.field.QM31.half input =
      ok output) :
    Canonical output ∧ toExact output = toExact input / 2 := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    half_corresponds input canonical
  rw [run] at expectedRun
  cases expectedRun
  refine ⟨expectedCanonical, ?_⟩
  have twoNeZero : (2 : K) ≠ 0 := by decide
  apply (eq_div_iff twoNeZero).2
  rw [mul_two]
  exact expectedExact

def projectBlock (block : Block) :
    AspisV5CompactTerminalOptimized.OptimizedBlock K :=
  { scale := toExact block.scale
    powerLo := toExact block.power_lo
    powerHi := toExact block.power_hi
    selector := block.selector.val }

def blockAt (state : State) (index : Fin 10) : Block :=
  state.blocks.val[index.val]'(by
    rw [state.blocks.property]
    exact index.isLt)

def projectState (state : State) :
    AspisV5CompactTerminalOptimized.OptimizedState K :=
  { blocks := fun index => projectBlock (blockAt state index)
    deltaScale := toExact state.delta_scale }

def CanonicalBlock (block : Block) : Prop :=
  Canonical block.scale ∧ Canonical block.power_lo ∧
    Canonical block.power_hi

def CanonicalState (state : State) : Prop :=
  (∀ index : Fin 10, CanonicalBlock (blockAt state index)) ∧
    Canonical state.delta_scale

def pointAt (point : Array Raw 10#usize) (index : Fin 10) : Raw :=
  point.val[index.val]!

private theorem arrayIndexRun {N : Std.Usize}
    (values : Array Raw N) (index : Std.Usize) (hindex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hindex))
  have hbound : index.val < values.val.length := by
    simpa [Array.length_eq] using hindex
  have elementEq : values.val[index.val]! = values.val[index.val] := by
    apply List.getElem!_of_getElem?
    simp [hbound]
  simpa [valueEq, elementEq] using run

private theorem pointIndexRun (point : Array Raw 10#usize)
    (index : Std.Usize) (slot : Fin 10) (sameIndex : index.val = slot.val) :
    Array.index_usize point index = ok (pointAt point slot) := by
  have hindex : index.val < (10#usize).val := by
    norm_num
    omega
  simpa [pointAt, sameIndex] using arrayIndexRun point index hindex

/-- The explicit ten-block constructor program after source-loop unrolling.
The separate source-unroll module proves that this is exactly the extracted
`CompactBTerminalWeights::new` loop. -/
def constructorProgram (point : Array Raw 10#usize) (scale : Raw) :
    Result State := do
  let scale8 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale
  let scale7 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale8
  let scale6 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale7
  let scale5 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale6
  let scale4 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale5
  let scale3 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale4
  let scale2 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale3
  let scale1 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale2
  let scale0 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale1
  let point0 <- Array.index_usize point 0#usize
  let square0 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point0
  let point1 <- Array.index_usize point 1#usize
  let square1 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point1
  let point2 <- Array.index_usize point 2#usize
  let square2 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point2
  let point3 <- Array.index_usize point 3#usize
  let square3 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point3
  let point4 <- Array.index_usize point 4#usize
  let square4 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point4
  let point5 <- Array.index_usize point 5#usize
  let square5 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point5
  let point6 <- Array.index_usize point 6#usize
  let square6 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point6
  let point7 <- Array.index_usize point 7#usize
  let square7 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point7
  let point8 <- Array.index_usize point 8#usize
  let square8 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point8
  let point9 <- Array.index_usize point 9#usize
  let square9 <- V5RelationCompactNewGenerated.aspis_core.field.QM31.square point9
  let delta <- V5RelationCompactNewGenerated.aspis_core.field.QM31.half scale0
  ok {
    blocks := Array.make 10#usize [
      { scale := scale0, power_lo := point0, power_hi := square0, selector := 0#u8 },
      { scale := scale1, power_lo := point1, power_hi := square1, selector := 1#u8 },
      { scale := scale2, power_lo := point2, power_hi := square2, selector := 2#u8 },
      { scale := scale3, power_lo := point3, power_hi := square3, selector := 3#u8 },
      { scale := scale4, power_lo := point4, power_hi := square4, selector := 4#u8 },
      { scale := scale5, power_lo := point5, power_hi := square5, selector := 5#u8 },
      { scale := scale6, power_lo := point6, power_hi := square6, selector := 6#u8 },
      { scale := scale7, power_lo := point7, power_hi := square7, selector := 28#u8 },
      { scale := scale8, power_lo := point8, power_hi := square8, selector := 29#u8 },
      { scale := scale, power_lo := point9, power_hi := square9, selector := 30#u8 }]
    delta_scale := delta
    folds := 0#u8 }

private theorem iteratedHalf_succ (count : Nat) (value : K) :
    AspisV5CompactTerminalOptimized.iteratedHalf (count + 1) value =
      AspisV5CompactTerminalOptimized.iteratedHalf count value / 2 := by
  simp [AspisV5CompactTerminalOptimized.iteratedHalf,
    Function.iterate_succ_apply']

/-- The completely unrolled constructor program denotes the independent
optimized-state initializer, for every canonical ten-coordinate point and
scale. -/
theorem constructorProgram_corresponds
    (point : Array Raw 10#usize) (scale : Raw) (state : State)
    (pointCanonical : ∀ index : Fin 10, Canonical (pointAt point index))
    (scaleCanonical : Canonical scale)
    (run : constructorProgram point scale = ok state) :
    CanonicalState state ∧ state.folds = 0#u8 ∧
      projectState state =
        AspisV5CompactTerminalOptimized.optimizedInit
          (fun index => toExact (pointAt point index)) (toExact scale) := by
  obtain ⟨scale8, scale8Run, scale8Canonical, scale8Exact⟩ :=
    half_corresponds scale scaleCanonical
  obtain ⟨scale7, scale7Run, scale7Canonical, scale7Exact⟩ :=
    half_corresponds scale8 scale8Canonical
  obtain ⟨scale6, scale6Run, scale6Canonical, scale6Exact⟩ :=
    half_corresponds scale7 scale7Canonical
  obtain ⟨scale5, scale5Run, scale5Canonical, scale5Exact⟩ :=
    half_corresponds scale6 scale6Canonical
  obtain ⟨scale4, scale4Run, scale4Canonical, scale4Exact⟩ :=
    half_corresponds scale5 scale5Canonical
  obtain ⟨scale3, scale3Run, scale3Canonical, scale3Exact⟩ :=
    half_corresponds scale4 scale4Canonical
  obtain ⟨scale2, scale2Run, scale2Canonical, scale2Exact⟩ :=
    half_corresponds scale3 scale3Canonical
  obtain ⟨scale1, scale1Run, scale1Canonical, scale1Exact⟩ :=
    half_corresponds scale2 scale2Canonical
  obtain ⟨scale0, scale0Run, scale0Canonical, scale0Exact⟩ :=
    half_corresponds scale1 scale1Canonical
  have point0Run : Array.index_usize point 0#usize =
      ok (pointAt point 0) := pointIndexRun point 0#usize 0 rfl
  have point1Run : Array.index_usize point 1#usize =
      ok (pointAt point 1) := pointIndexRun point 1#usize 1 rfl
  have point2Run : Array.index_usize point 2#usize =
      ok (pointAt point 2) := pointIndexRun point 2#usize 2 rfl
  have point3Run : Array.index_usize point 3#usize =
      ok (pointAt point 3) := pointIndexRun point 3#usize 3 rfl
  have point4Run : Array.index_usize point 4#usize =
      ok (pointAt point 4) := pointIndexRun point 4#usize 4 rfl
  have point5Run : Array.index_usize point 5#usize =
      ok (pointAt point 5) := pointIndexRun point 5#usize 5 rfl
  have point6Run : Array.index_usize point 6#usize =
      ok (pointAt point 6) := pointIndexRun point 6#usize 6 rfl
  have point7Run : Array.index_usize point 7#usize =
      ok (pointAt point 7) := pointIndexRun point 7#usize 7 rfl
  have point8Run : Array.index_usize point 8#usize =
      ok (pointAt point 8) := pointIndexRun point 8#usize 8 rfl
  have point9Run : Array.index_usize point 9#usize =
      ok (pointAt point 9) := pointIndexRun point 9#usize 9 rfl
  obtain ⟨square0, square0Run, square0Canonical, square0Exact⟩ :=
    square_corresponds (pointAt point 0) (pointCanonical 0)
  obtain ⟨square1, square1Run, square1Canonical, square1Exact⟩ :=
    square_corresponds (pointAt point 1) (pointCanonical 1)
  obtain ⟨square2, square2Run, square2Canonical, square2Exact⟩ :=
    square_corresponds (pointAt point 2) (pointCanonical 2)
  obtain ⟨square3, square3Run, square3Canonical, square3Exact⟩ :=
    square_corresponds (pointAt point 3) (pointCanonical 3)
  obtain ⟨square4, square4Run, square4Canonical, square4Exact⟩ :=
    square_corresponds (pointAt point 4) (pointCanonical 4)
  obtain ⟨square5, square5Run, square5Canonical, square5Exact⟩ :=
    square_corresponds (pointAt point 5) (pointCanonical 5)
  obtain ⟨square6, square6Run, square6Canonical, square6Exact⟩ :=
    square_corresponds (pointAt point 6) (pointCanonical 6)
  obtain ⟨square7, square7Run, square7Canonical, square7Exact⟩ :=
    square_corresponds (pointAt point 7) (pointCanonical 7)
  obtain ⟨square8, square8Run, square8Canonical, square8Exact⟩ :=
    square_corresponds (pointAt point 8) (pointCanonical 8)
  obtain ⟨square9, square9Run, square9Canonical, square9Exact⟩ :=
    square_corresponds (pointAt point 9) (pointCanonical 9)
  obtain ⟨delta, deltaRun, deltaCanonical, deltaExact⟩ :=
    half_corresponds scale0 scale0Canonical
  let expected : State := {
    blocks := Array.make 10#usize [
      { scale := scale0, power_lo := pointAt point 0, power_hi := square0,
        selector := 0#u8 },
      { scale := scale1, power_lo := pointAt point 1, power_hi := square1,
        selector := 1#u8 },
      { scale := scale2, power_lo := pointAt point 2, power_hi := square2,
        selector := 2#u8 },
      { scale := scale3, power_lo := pointAt point 3, power_hi := square3,
        selector := 3#u8 },
      { scale := scale4, power_lo := pointAt point 4, power_hi := square4,
        selector := 4#u8 },
      { scale := scale5, power_lo := pointAt point 5, power_hi := square5,
        selector := 5#u8 },
      { scale := scale6, power_lo := pointAt point 6, power_hi := square6,
        selector := 6#u8 },
      { scale := scale7, power_lo := pointAt point 7, power_hi := square7,
        selector := 28#u8 },
      { scale := scale8, power_lo := pointAt point 8, power_hi := square8,
        selector := 29#u8 },
      { scale := scale, power_lo := pointAt point 9, power_hi := square9,
        selector := 30#u8 }]
    delta_scale := delta
    folds := 0#u8 }
  have expectedRun : constructorProgram point scale = ok expected := by
    simp [constructorProgram, scale8Run, scale7Run, scale6Run, scale5Run,
      scale4Run, scale3Run, scale2Run, scale1Run, scale0Run,
      point0Run, point1Run, point2Run, point3Run, point4Run, point5Run,
      point6Run, point7Run, point8Run, point9Run,
      square0Run, square1Run, square2Run, square3Run, square4Run,
      square5Run, square6Run, square7Run, square8Run, square9Run,
      deltaRun, expected]
  rw [run] at expectedRun
  have stateEquality : state = expected := Result.ok.inj expectedRun
  subst state
  have scale8Iter : toExact scale8 =
      AspisV5CompactTerminalOptimized.iteratedHalf 1 (toExact scale) := by
    simpa [AspisV5CompactTerminalOptimized.iteratedHalf] using
      (half_exact scale scale8 scaleCanonical scale8Run).2
  have scale7Iter : toExact scale7 =
      AspisV5CompactTerminalOptimized.iteratedHalf 2 (toExact scale) := by
    calc
      toExact scale7 = toExact scale8 / 2 :=
        (half_exact scale8 scale7 scale8Canonical scale7Run).2
      _ = AspisV5CompactTerminalOptimized.iteratedHalf 1 (toExact scale) / 2 :=
        congrArg (fun value : K => value / 2) scale8Iter
      _ = _ := (iteratedHalf_succ 1 (toExact scale)).symm
  have scale6Iter : toExact scale6 =
      AspisV5CompactTerminalOptimized.iteratedHalf 3 (toExact scale) := by
    rw [(half_exact scale7 scale6 scale7Canonical scale6Run).2, scale7Iter]
    exact (iteratedHalf_succ 2 (toExact scale)).symm
  have scale5Iter : toExact scale5 =
      AspisV5CompactTerminalOptimized.iteratedHalf 4 (toExact scale) := by
    rw [(half_exact scale6 scale5 scale6Canonical scale5Run).2, scale6Iter]
    exact (iteratedHalf_succ 3 (toExact scale)).symm
  have scale4Iter : toExact scale4 =
      AspisV5CompactTerminalOptimized.iteratedHalf 5 (toExact scale) := by
    rw [(half_exact scale5 scale4 scale5Canonical scale4Run).2, scale5Iter]
    exact (iteratedHalf_succ 4 (toExact scale)).symm
  have scale3Iter : toExact scale3 =
      AspisV5CompactTerminalOptimized.iteratedHalf 6 (toExact scale) := by
    rw [(half_exact scale4 scale3 scale4Canonical scale3Run).2, scale4Iter]
    exact (iteratedHalf_succ 5 (toExact scale)).symm
  have scale2Iter : toExact scale2 =
      AspisV5CompactTerminalOptimized.iteratedHalf 7 (toExact scale) := by
    rw [(half_exact scale3 scale2 scale3Canonical scale2Run).2, scale3Iter]
    exact (iteratedHalf_succ 6 (toExact scale)).symm
  have scale1Iter : toExact scale1 =
      AspisV5CompactTerminalOptimized.iteratedHalf 8 (toExact scale) := by
    rw [(half_exact scale2 scale1 scale2Canonical scale1Run).2, scale2Iter]
    exact (iteratedHalf_succ 7 (toExact scale)).symm
  have scale0Iter : toExact scale0 =
      AspisV5CompactTerminalOptimized.iteratedHalf 9 (toExact scale) := by
    rw [(half_exact scale1 scale0 scale1Canonical scale0Run).2, scale1Iter]
    exact (iteratedHalf_succ 8 (toExact scale)).symm
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro index
      fin_cases index <;>
        simp [CanonicalBlock, blockAt, expected, Array.make, pointCanonical,
          scale0Canonical, scale1Canonical, scale2Canonical, scale3Canonical,
          scale4Canonical, scale5Canonical, scale6Canonical, scale7Canonical,
          scale8Canonical, scaleCanonical, square0Canonical, square1Canonical,
          square2Canonical, square3Canonical, square4Canonical,
          square5Canonical, square6Canonical, square7Canonical,
          square8Canonical, square9Canonical]
    · exact deltaCanonical
  · apply congrArg₂ (fun
        (blocks : Fin 10 → AspisV5CompactTerminalOptimized.OptimizedBlock K)
        (deltaScale : K) =>
        ({ blocks := blocks, deltaScale := deltaScale } :
          AspisV5CompactTerminalOptimized.OptimizedState K))
    · funext index
      fin_cases index <;>
        simp [projectState, blockAt, projectBlock, expected, Array.make,
          AspisV5CompactTerminalOptimized.optimizedInit,
          AspisV5CompactTerminal.blockSelector, scale0Iter, scale1Iter,
          scale2Iter, scale3Iter, scale4Iter, scale5Iter, scale6Iter,
          scale7Iter, scale8Iter, square0Exact, square1Exact, square2Exact,
          square3Exact, square4Exact, square5Exact, square6Exact,
          square7Exact, square8Exact, square9Exact,
          AspisV5CompactTerminalOptimized.iteratedHalf]
    · change toExact delta =
        AspisV5CompactTerminalOptimized.iteratedHalf 9 (toExact scale) / 2
      rw [(half_exact scale0 delta scale0Canonical deltaRun).2, scale0Iter]

end V5CompactScratchNew
