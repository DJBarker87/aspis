import V5RelationCompactFinalGenerated
import V5RelationGeneratedFieldProjection
import V5RelationLinkedFoldArithmetic
import AspisFormal.V5CompactTerminalOptimized

/-!
# Exact field semantics of the compact final scatter

The source-loop proof is kept separate from this inexpensive arithmetic
module.  Here the eleven additions performed after the ten fixed compact
blocks have been folded are checked against the maintained QM31 tower and the
independent `optimizedFinalWeights` definition.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5CompactFinalFieldSemantics

abbrev Raw := V5RelationCompactFinalGenerated.aspis_core.field.QM31
abbrev Block :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev State :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights
abbrev FullRaw := V5RelationFullGenerated.aspis_core.field.QM31
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited Raw :=
  ⟨V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO⟩
local instance : Inhabited Block :=
  ⟨{ scale := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     power_lo := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     power_hi := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

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
    V5RelationCompactFinalGenerated.aspis_core.field.P =
      V5RelationFullGenerated.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationCompactFinalGenerated.aspis_core.field.P
    V5RelationFullGenerated.aspis_core.field.P
  rfl

private theorem m31_add_eq_full
    (left right : V5RelationCompactFinalGenerated.aspis_core.field.M31) :
    V5RelationCompactFinalGenerated.aspis_core.field.M31.add left right =
      V5RelationFullGenerated.aspis_core.field.M31.add left right := by
  unfold V5RelationCompactFinalGenerated.aspis_core.field.M31.add
    V5RelationFullGenerated.aspis_core.field.M31.add
  rw [P_eq_full]

private theorem add_toFull (left right : Raw) :
    (do
      let output ←
        V5RelationCompactFinalGenerated.aspis_core.field.QM31.add left right
      ok (toFull output)) =
    V5RelationFullGenerated.aspis_core.field.QM31.add
      (toFull left) (toFull right) := by
  simp [V5RelationCompactFinalGenerated.aspis_core.field.QM31.add,
    V5RelationFullGenerated.aspis_core.field.QM31.add,
    V5RelationCompactFinalGenerated.aspis_core.field.CM31.add,
    V5RelationFullGenerated.aspis_core.field.CM31.add,
    m31_add_eq_full, toFull]

theorem add_corresponds (left right : Raw)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right) :
    ∃ output : Raw,
      V5RelationCompactFinalGenerated.aspis_core.field.QM31.add left right =
        ok output ∧
      Canonical output ∧ toExact output = toExact left + toExact right := by
  obtain ⟨output, fullRun, outputCanonical, exact⟩ :=
    AspisV5RelationGeneratedFieldProjection.generated_qm31_add_corresponds
      (toFull left) (toFull right) leftCanonical rightCanonical
  refine ⟨fromFull output, ?_, ?_, ?_⟩
  · have mapped := add_toFull left right
    rw [fullRun] at mapped
    generalize compactRun :
      V5RelationCompactFinalGenerated.aspis_core.field.QM31.add left right =
        compactResult at mapped
    cases compactResult with
    | fail error => simp at mapped
    | div => simp at mapped
    | ok compactOutput =>
      simp only [bind_tc_ok] at mapped
      have mappedValue : toFull compactOutput = output := Result.ok.inj mapped
      have outputEquality : compactOutput = fromFull output := by
        have mappedBack := congrArg fromFull mappedValue
        simpa using mappedBack
      simpa [compactRun, outputEquality]
  · simpa [Canonical] using outputCanonical
  · have exactM := congrArg
        AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained exact
    simpa only [toExact, toFull_fromFull, oldMap_fullToExact,
      AspisV5RelationLinkedFoldArithmetic.oldQm31ToMaintained_add] using exactM

theorem zero_canonical :
    Canonical V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [Canonical, toFull,
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    AspisAeneasCM31Multiplicative.m31Modulus,
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO]

@[simp] theorem zero_exact :
    toExact V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO = 0 := by
  norm_num [toExact, toFull,
    AspisV5RelationGeneratedFieldProjection.toMaintainedExact,
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp
  · apply QuadraticAlgebra.ext <;> simp

def blockAt (state : State) (index : Fin 10) : Block :=
  state.blocks.val[index.val]!

def projectBlock (block : Block) :
    AspisV5CompactTerminalOptimized.OptimizedBlock K :=
  { scale := toExact block.scale
    powerLo := toExact block.power_lo
    powerHi := toExact block.power_hi
    selector := block.selector.val }

def projectState (state : State) :
    AspisV5CompactTerminalOptimized.OptimizedState K :=
  { blocks := fun index => projectBlock (blockAt state index)
    deltaScale := toExact state.delta_scale }

def CanonicalScales (state : State) : Prop :=
  (∀ index : Fin 10, Canonical (blockAt state index).scale) ∧
    Canonical state.delta_scale

def ReleasedSelectors (state : State) : Prop :=
  ∀ index : Fin 10,
    (blockAt state index).selector.val = AspisV5CompactTerminal.blockSelector index

/-- The arithmetic-only normal form of the fixed scatter: selectors 0--6
land in slot zero, selectors 28--30 land in slot three, and the delta scale is
added to slot three last. -/
def finalProgram (state : State) : Result (Array Raw 4#usize) := do
  let slot0a ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
    (blockAt state 0).scale
  let slot0b ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot0a (blockAt state 1).scale
  let slot0c ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot0b (blockAt state 2).scale
  let slot0d ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot0c (blockAt state 3).scale
  let slot0e ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot0d (blockAt state 4).scale
  let slot0f ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot0e (blockAt state 5).scale
  let slot0g ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot0f (blockAt state 6).scale
  let slot3a ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
    (blockAt state 7).scale
  let slot3b ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot3a (blockAt state 8).scale
  let slot3c ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot3b (blockAt state 9).scale
  let slot3d ← V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
    slot3c state.delta_scale
  ok (Array.make 4#usize [slot0g,
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO,
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO, slot3d])

def exactOutput (state : State) : Fin 4 → K := fun index =>
  if index = 0 then
    ∑ round : Fin 7, toExact (blockAt state ⟨round.val, by omega⟩).scale
  else if index = 3 then
    toExact (blockAt state 7).scale +
      toExact (blockAt state 8).scale +
      toExact (blockAt state 9).scale + toExact state.delta_scale
  else 0

theorem finalProgram_corresponds (state : State) (output : Array Raw 4#usize)
    (canonical : CanonicalScales state)
    (run : finalProgram state = ok output) :
    (∀ index : Fin 4, Canonical output.val[index.val]!) ∧
      (fun index : Fin 4 => toExact output.val[index.val]!) = exactOutput state := by
  obtain ⟨slot0a, run0a, can0a, exact0a⟩ := add_corresponds
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
    (blockAt state 0).scale zero_canonical (canonical.1 0)
  obtain ⟨slot0b, run0b, can0b, exact0b⟩ := add_corresponds
    slot0a (blockAt state 1).scale can0a (canonical.1 1)
  obtain ⟨slot0c, run0c, can0c, exact0c⟩ := add_corresponds
    slot0b (blockAt state 2).scale can0b (canonical.1 2)
  obtain ⟨slot0d, run0d, can0d, exact0d⟩ := add_corresponds
    slot0c (blockAt state 3).scale can0c (canonical.1 3)
  obtain ⟨slot0e, run0e, can0e, exact0e⟩ := add_corresponds
    slot0d (blockAt state 4).scale can0d (canonical.1 4)
  obtain ⟨slot0f, run0f, can0f, exact0f⟩ := add_corresponds
    slot0e (blockAt state 5).scale can0e (canonical.1 5)
  obtain ⟨slot0g, run0g, can0g, exact0g⟩ := add_corresponds
    slot0f (blockAt state 6).scale can0f (canonical.1 6)
  obtain ⟨slot3a, run3a, can3a, exact3a⟩ := add_corresponds
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
    (blockAt state 7).scale zero_canonical (canonical.1 7)
  obtain ⟨slot3b, run3b, can3b, exact3b⟩ := add_corresponds
    slot3a (blockAt state 8).scale can3a (canonical.1 8)
  obtain ⟨slot3c, run3c, can3c, exact3c⟩ := add_corresponds
    slot3b (blockAt state 9).scale can3b (canonical.1 9)
  obtain ⟨slot3d, run3d, can3d, exact3d⟩ := add_corresponds
    slot3c state.delta_scale can3c canonical.2
  let expected := Array.make 4#usize [slot0g,
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO,
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO, slot3d]
  have expectedRun : finalProgram state = ok expected := by
    simp [finalProgram, run0a, run0b, run0c, run0d, run0e, run0f, run0g,
      run3a, run3b, run3c, run3d, expected]
  rw [run] at expectedRun
  have outputEquality : output = expected := Result.ok.inj expectedRun
  subst output
  constructor
  · intro index
    fin_cases index <;> simp [expected, Array.make, can0g, can3d, zero_canonical]
  · funext index
    fin_cases index <;>
      simp [expected, Array.make, exactOutput, exact0a, exact0b, exact0c,
        exact0d, exact0e, exact0f, exact0g, exact3a, exact3b, exact3c,
        exact3d, Fin.sum_univ_succ, add_assoc]

theorem optimizedFinalWeights_eq_exactOutput (state : State)
    (selectors : ReleasedSelectors state) :
    AspisV5CompactTerminalOptimized.optimizedFinalWeights (projectState state) =
      exactOutput state := by
  have s0 := selectors (0 : Fin 10)
  have s1 := selectors (1 : Fin 10)
  have s2 := selectors (2 : Fin 10)
  have s3 := selectors (3 : Fin 10)
  have s4 := selectors (4 : Fin 10)
  have s5 := selectors (5 : Fin 10)
  have s6 := selectors (6 : Fin 10)
  have s7 := selectors (7 : Fin 10)
  have s8 := selectors (8 : Fin 10)
  have s9 := selectors (9 : Fin 10)
  norm_num [AspisV5CompactTerminal.blockSelector] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  funext index
  fin_cases index <;>
    simp [AspisV5CompactTerminalOptimized.optimizedFinalWeights,
      AspisV5CompactTerminalOptimized.indicator, projectState, projectBlock,
      exactOutput, Fin.sum_univ_succ, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9,
      AspisV5CompactTerminal.blockSelector, add_assoc]

#print axioms add_corresponds
#print axioms finalProgram_corresponds
#print axioms optimizedFinalWeights_eq_exactOutput

end AspisV5CompactFinalFieldSemantics
