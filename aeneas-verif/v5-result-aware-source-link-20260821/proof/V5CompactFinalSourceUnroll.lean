import V5RelationCompactFinalGenerated
import V5RelationGeneratedFieldProjection

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5CompactFinalSourceUnroll

open V5RelationCompactFinalGenerated

abbrev Raw := V5RelationCompactFinalGenerated.aspis_core.field.QM31
abbrev Block :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev State :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights

local instance : Inhabited Raw :=
  ⟨V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO⟩

local instance : Inhabited Block :=
  ⟨{ scale := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     power_lo := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     power_hi := V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩

def toFull (value : Raw) : V5RelationFullGenerated.aspis_core.field.QM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

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

theorem qm31_add_toFull (left right : Raw) :
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

def step (block : Block) (output : Array Raw 4#usize) :
    Result (Array Raw 4#usize) := do
  let shifted ← lift (Std.U8.wrapping_shr block.selector 3#u32)
  let index ← lift (core.convert.num.FromUsizeU8.from shifted)
  let old ← Array.index_usize output index
  let next ←
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.add old block.scale
  Array.update output index next

abbrev Iter :=
  V5RelationCompactFinalGenerated.core.array.iter.IntoIter Block 10#usize

def iteratorAt (blocks : Array Block 10#usize) (index : Nat) : Iter :=
  { array := blocks, index := index }

private theorem iterator_next_some
    (blocks : Array Block 10#usize) (index : Nat)
    (inBounds : index < blocks.val.length) :
    V5RelationCompactFinalGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
        (iteratorAt blocks index) =
      .ok (some (blocks.val[index]'(by exact inBounds)),
        iteratorAt blocks (index + 1)) := by
  have h : index < (10#usize).val := by simpa using inBounds
  have tenVal : (10#usize).val = 10 := by rfl
  rw [tenVal] at h
  simp [V5RelationCompactFinalGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    iteratorAt, h]

private theorem iterator_next_none
    (blocks : Array Block 10#usize) (index : Nat)
    (exhausted : ¬ index < blocks.val.length) :
    V5RelationCompactFinalGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
        (iteratorAt blocks index) =
      .ok (none, iteratorAt blocks index) := by
  have h : ¬ index < (10#usize).val := by simpa using exhausted
  have tenVal : (10#usize).val = 10 := by rfl
  rw [tenVal] at h
  simp [V5RelationCompactFinalGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    iteratorAt, h]

private theorem final_body_some
    (blocks : Array Block 10#usize) (index : Nat)
    (output : Array Raw 4#usize)
    (inBounds : index < blocks.val.length) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop.body
        (iteratorAt blocks index) output =
      (do
        let next ← step (blocks.val[index]'(by exact inBounds)) output
        .ok (cont (iteratorAt blocks (index + 1), next))) := by
  unfold V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop.body
  rw [iterator_next_some blocks index inBounds]
  simp only [bind_tc_ok]
  unfold step
  simp only [Aeneas.Std.bind_assoc_eq]

private theorem final_loop_step
    (blocks : Array Block 10#usize) (index : Nat)
    (output : Array Raw 4#usize)
    (inBounds : index < blocks.val.length) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop
        (iteratorAt blocks index) output =
      (do
        let next ← step (blocks.val[index]'(by exact inBounds)) output
        V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop
          (iteratorAt blocks (index + 1)) next) := by
  rw [V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop,
    Aeneas.Std.loop.eq_def]
  simp only
  rw [final_body_some blocks index output inBounds]
  generalize stepRun :
    step (blocks.val[index]'(by exact inBounds)) output = result
  cases result <;>
    simp [stepRun,
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop]

private theorem final_loop_done
    (blocks : Array Block 10#usize) (index : Nat)
    (output : Array Raw 4#usize)
    (exhausted : ¬ index < blocks.val.length) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop
        (iteratorAt blocks index) output = .ok output := by
  rw [V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop,
    Aeneas.Std.loop.eq_def]
  simp only
  unfold V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop.body
  rw [iterator_next_none blocks index exhausted]
  rfl

def stepsN (blocks : Array Block 10#usize) :
    Nat → Nat → Array Raw 4#usize → Result (Array Raw 4#usize)
  | 0, _, output => .ok output
  | remaining + 1, index, output => do
      let next ← step blocks.val[index]! output
      stepsN blocks remaining (index + 1) next

private theorem get_eq_getElemBang {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (inBounds : index < values.length) :
    values[index]'(by exact inBounds) = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [inBounds]

private theorem final_loop_eq_stepsN
    (blocks : Array Block 10#usize) (remaining index : Nat)
    (output : Array Raw 4#usize)
    (lengthExact : index + remaining = 10) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights_loop
        (iteratorAt blocks index) output =
      stepsN blocks remaining index output := by
  induction remaining generalizing index output with
  | zero =>
      have exhausted : ¬ index < blocks.val.length := by
        have arrayLength : blocks.val.length = 10 := by
          simpa using blocks.property
        omega
      rw [final_loop_done blocks index output exhausted]
      rfl
  | succ remaining inductionHypothesis =>
      have inBounds : index < blocks.val.length := by
        have arrayLength : blocks.val.length = 10 := by
          simpa using blocks.property
        omega
      rw [final_loop_step blocks index output inBounds]
      rw [get_eq_getElemBang blocks.val index inBounds]
      unfold stepsN
      apply (Aeneas.Std.bind_eq_iff _ _ _).2
      intro next _
      exact inductionHypothesis (index := index + 1) (output := next) (by omega)

def unrolled (state : State) : Result (Array Raw 4#usize) := do
  let output0 ← step state.blocks.val[0]! (Array.repeat 4#usize
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.ZERO)
  let output1 ← step state.blocks.val[1]! output0
  let output2 ← step state.blocks.val[2]! output1
  let output3 ← step state.blocks.val[3]! output2
  let output4 ← step state.blocks.val[4]! output3
  let output5 ← step state.blocks.val[5]! output4
  let output6 ← step state.blocks.val[6]! output5
  let output7 ← step state.blocks.val[7]! output6
  let output8 ← step state.blocks.val[8]! output7
  let output9 ← step state.blocks.val[9]! output8
  let i ← lift (Std.Usize.wrapping_sub
    V5RelationCompactFinalGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_FINAL_VALUES
    1#usize)
  let slot3 ← Array.index_usize output9 i
  let withDelta ←
    V5RelationCompactFinalGenerated.aspis_core.field.QM31.add
      slot3 state.delta_scale
  let i1 ← lift (Std.Usize.wrapping_sub
    V5RelationCompactFinalGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_FINAL_VALUES
    1#usize)
  Array.update output9 i1 withDelta

theorem final_weights_eq_unrolled (state : State) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights state =
      unrolled state := by
  unfold V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
  simp only [
    V5RelationCompactFinalGenerated.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    bind_tc_ok]
  rw [show ({ array := state.blocks } : Iter) = iteratorAt state.blocks 0 by rfl]
  rw [final_loop_eq_stepsN state.blocks 10 0 _ (by omega)]
  simp only [stepsN, Nat.reduceAdd, Aeneas.Std.bind_assoc_eq]
  unfold unrolled
  rfl

#print axioms final_weights_eq_unrolled

end AspisV5CompactFinalSourceUnroll
