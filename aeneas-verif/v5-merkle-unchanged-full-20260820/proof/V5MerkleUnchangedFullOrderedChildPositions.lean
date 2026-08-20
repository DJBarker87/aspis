import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullRadixSoundness

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullOrderedChildPositions

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleUnchangedFullRadixSoundness

/-- The production mask says that this numbered child comes from the live
level rather than from the uploaded frontier.  The existential scalar keeps
this definition exactly at the generated Rust bit-test boundary while the
positional theorems below use ordinary natural-number indices. -/
def ChildPresent (present : Std.U8) (slot : Nat) : Prop :=
  ∃ scalar : Std.Usize,
    scalar.val = slot ∧
      present &&& Std.U8.wrapping_shl 1#u8 (UScalar.cast .U32 scalar) != 0#u8

noncomputable def liveBefore (present : Std.U8) : Nat → Nat
  | 0 => 0
  | count + 1 => by
      classical
      exact liveBefore present count +
        if ChildPresent present count then 1 else 0

noncomputable def frontierBefore (present : Std.U8) : Nat → Nat
  | 0 => 0
  | count + 1 => by
      classical
      exact frontierBefore present count +
        if ChildPresent present count then 0 else 1

theorem childPresent_of_generated_bit
    (present : Std.U8) (slot : Std.Usize) (count : Nat)
    (slot_eq : slot.val = count)
    (present_bit :
      present &&& Std.U8.wrapping_shl 1#u8 (UScalar.cast .U32 slot) != 0#u8) :
    ChildPresent present count := by
  exact ⟨slot, slot_eq, present_bit⟩

theorem not_childPresent_of_generated_bit
    (present : Std.U8) (slot : Std.Usize) (count : Nat)
    (slot_eq : slot.val = count)
    (absent_bit : ¬
      (present &&& Std.U8.wrapping_shl 1#u8 (UScalar.cast .U32 slot) != 0#u8)) :
    ¬ ChildPresent present count := by
  rintro ⟨other, other_eq, other_bit⟩
  have same : other = slot := by
    apply UScalar.eq_of_val_eq
    exact other_eq.trans slot_eq.symm
  subst other
  exact absent_bit other_bit

theorem liveBefore_succ_of_present
    (present : Std.U8) (count : Nat) (bit : ChildPresent present count) :
    liveBefore present (count + 1) = liveBefore present count + 1 := by
  simp [liveBefore, bit]

theorem liveBefore_succ_of_absent
    (present : Std.U8) (count : Nat) (bit : ¬ ChildPresent present count) :
    liveBefore present (count + 1) = liveBefore present count := by
  simp [liveBefore, bit]

theorem frontierBefore_succ_of_present
    (present : Std.U8) (count : Nat) (bit : ChildPresent present count) :
    frontierBefore present (count + 1) = frontierBefore present count := by
  simp [frontierBefore, bit]

theorem frontierBefore_succ_of_absent
    (present : Std.U8) (count : Nat) (bit : ¬ ChildPresent present count) :
    frontierBefore present (count + 1) =
      frontierBefore present count + 1 := by
  simp [frontierBefore, bit]

/-- Everything needed later to align the generated four-child loop with the
maintained Merkle topology: exact cursor totals and the exact source of every
indexed child. -/
structure OrderedChildPositionFacts
    (nodeBytes : Slice Std.U8) (level : GeneratedDigestVec)
    (present : Std.U8) (count : Nat)
    (startNodePos startValuePos : Std.Usize)
    (children : List GeneratedDigest)
    (finalNodePos finalValuePos : Std.Usize) : Prop where
  children_length : children.length = count
  final_value_pos :
    finalValuePos.val = startValuePos.val + liveBefore present count
  final_node_pos :
    finalNodePos.val = startNodePos.val + 32 * frontierBefore present count
  live_source : ∀ slot, slot < count → ChildPresent present slot →
    children[slot]! =
      level.val[startValuePos.val + liveBefore present slot]!
  frontier_source : ∀ slot, slot < count → ¬ ChildPresent present slot →
    ∀ byte, byte < 32 →
      children[slot]!.val[byte]! =
        nodeBytes.val[
          startNodePos.val + 32 * frontierBefore present slot + byte]!

theorem OrderedChildReads.position_facts
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {present : Std.U8} {count : Nat}
    {startNodePos startValuePos finalNodePos finalValuePos : Std.Usize}
    {children : List GeneratedDigest}
    (reads : OrderedChildReads nodeBytes level present count startNodePos
      startValuePos children finalNodePos finalValuePos) :
    OrderedChildPositionFacts nodeBytes level present count startNodePos
      startValuePos children finalNodePos finalValuePos := by
  induction reads with
  | nil nodePos valuePos =>
      exact {
        children_length := rfl
        final_value_pos := by simp [liveBefore]
        final_node_pos := by simp [frontierBefore]
        live_source := by simp
        frontier_source := by simp }
  | @live stepCount stepStartNode stepStartValue nodePos valuePos stepChildren
      slot child nextValuePos prior slot_eq slot_lt present_bit value_bound
      child_eq next_value_eq ih =>
      have currentPresent : ChildPresent present stepCount :=
        childPresent_of_generated_bit present slot stepCount slot_eq present_bit
      have lengthPrior : stepChildren.length = stepCount := ih.children_length
      refine {
        children_length := by simp [lengthPrior]
        final_value_pos := ?_
        final_node_pos := ?_
        live_source := ?_
        frontier_source := ?_ }
      · rw [next_value_eq, ih.final_value_pos,
          liveBefore_succ_of_present present stepCount currentPresent]
        omega
      · rw [ih.final_node_pos,
          frontierBefore_succ_of_present present stepCount currentPresent]
      · intro target target_lt targetPresent
        by_cases earlier : target < stepCount
        · rw [List.getElem!_append_left stepChildren [child] target (by
              rw [lengthPrior]
              exact earlier)]
          exact ih.live_source target earlier targetPresent
        · have target_eq : target = stepCount := by omega
          subst target
          rw [List.getElem!_append_right stepChildren [child] stepCount (by
                rw [lengthPrior])]
          simp only [lengthPrior, Nat.sub_self, List.getElem!_cons_zero]
          rw [child_eq, ih.final_value_pos]
      · intro target target_lt targetAbsent byte byte_lt
        by_cases earlier : target < stepCount
        · rw [List.getElem!_append_left stepChildren [child] target (by
              rw [lengthPrior]
              exact earlier)]
          exact ih.frontier_source target earlier targetAbsent byte byte_lt
        · have target_eq : target = stepCount := by omega
          subst target
          exact False.elim (targetAbsent currentPresent)
  | @frontier stepCount stepStartNode stepStartValue nodePos valuePos
      stepChildren slot child nextNodePos prior slot_eq slot_lt absent_bit
      frontier_room child_bytes next_node_eq ih =>
      have currentAbsent : ¬ ChildPresent present stepCount :=
        not_childPresent_of_generated_bit present slot stepCount slot_eq
          absent_bit
      have lengthPrior : stepChildren.length = stepCount := ih.children_length
      refine {
        children_length := by simp [lengthPrior]
        final_value_pos := ?_
        final_node_pos := ?_
        live_source := ?_
        frontier_source := ?_ }
      · rw [ih.final_value_pos,
          liveBefore_succ_of_absent present stepCount currentAbsent]
      · rw [next_node_eq, ih.final_node_pos,
          frontierBefore_succ_of_absent present stepCount currentAbsent]
        omega
      · intro target target_lt targetPresent
        by_cases earlier : target < stepCount
        · rw [List.getElem!_append_left stepChildren [child] target (by
              rw [lengthPrior]
              exact earlier)]
          exact ih.live_source target earlier targetPresent
        · have target_eq : target = stepCount := by omega
          subst target
          exact False.elim (currentAbsent targetPresent)
      · intro target target_lt targetAbsent byte byte_lt
        by_cases earlier : target < stepCount
        · rw [List.getElem!_append_left stepChildren [child] target (by
              rw [lengthPrior]
              exact earlier)]
          exact ih.frontier_source target earlier targetAbsent byte byte_lt
        · have target_eq : target = stepCount := by omega
          subst target
          rw [List.getElem!_append_right stepChildren [child] stepCount (by
                rw [lengthPrior])]
          simp only [lengthPrior, Nat.sub_self, List.getElem!_cons_zero]
          simpa only [ih.final_node_pos] using child_bytes byte byte_lt

#print axioms OrderedChildReads.position_facts

end AspisV5MerkleUnchangedFullOrderedChildPositions
