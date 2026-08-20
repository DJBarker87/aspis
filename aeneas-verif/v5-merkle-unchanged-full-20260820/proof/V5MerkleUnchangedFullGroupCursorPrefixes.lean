import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullGroupTraceLists

/-! Prefix-count interpretation of the exact generated group cursors. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullGroupCursorPrefixes

open V5MerkleUnchangedCompat
variable [HashContext]

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullOrderedChildPositions
open AspisV5MerkleUnchangedFullGroupTraceLists

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

noncomputable def groupLiveCounts
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (steps : List (RawGroupStepSummary sha256 nodeBytes level)) : List Nat :=
  steps.map fun summary => liveBefore summary.present 4

noncomputable def groupFrontierCounts
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    (steps : List (RawGroupStepSummary sha256 nodeBytes level)) : List Nat :=
  steps.map fun summary => frontierBefore summary.present 4

/-- The source cursors at every group are exactly the initial cursors plus
the present/absent child counts of all preceding masks. -/
theorem OrderedGroupStepChain.cursor_prefixes
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {initialNext terminalNext : GeneratedDigestVec}
    {initialNodePos initialValuePos terminalNodePos terminalValuePos :
      Std.Usize}
    {steps : List (RawGroupStepSummary sha256 nodeBytes level)}
    (chain : OrderedGroupStepChain sha256 nodeBytes level initialNext
      initialNodePos initialValuePos steps terminalNext terminalNodePos
      terminalValuePos) :
    ∀ index (index_lt : index < steps.length),
      let summary := steps[index]
      summary.startValuePos.val = initialValuePos.val +
          ((groupLiveCounts steps).take index).sum ∧
        summary.startNodePos.val = initialNodePos.val + 32 *
          ((groupFrontierCounts steps).take index).sum := by
  induction chain with
  | nil next nodePos valuePos =>
      intro index index_lt
      simp at index_lt
  | @cons summary tail terminalNext terminalNodePos terminalValuePos rest ih =>
      intro index index_lt
      cases index with
      | zero =>
          simp [groupLiveCounts, groupFrontierCounts]
      | succ index =>
          have tail_lt : index < tail.length := by
            simpa using index_lt
          have tailFacts := ih index tail_lt
          have positions := summary_child_positions_are_exact summary
          rcases tailFacts with ⟨tailValue, tailNode⟩
          constructor
          · simpa [groupLiveCounts, List.take_succ_cons,
              positions.final_value_pos, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using tailValue
          · simpa [groupFrontierCounts, List.take_succ_cons,
              positions.final_node_pos, Nat.mul_add, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using tailNode

/-- Terminal form: the complete source loop advances by exactly the total
present-child count and exactly 32 bytes per absent child. -/
theorem OrderedGroupStepChain.terminal_cursors
    {sha256 : List ModelByte → Digest32}
    {nodeBytes : Slice Std.U8} {level : GeneratedDigestVec}
    {initialNext terminalNext : GeneratedDigestVec}
    {initialNodePos initialValuePos terminalNodePos terminalValuePos :
      Std.Usize}
    {steps : List (RawGroupStepSummary sha256 nodeBytes level)}
    (chain : OrderedGroupStepChain sha256 nodeBytes level initialNext
      initialNodePos initialValuePos steps terminalNext terminalNodePos
      terminalValuePos) :
    terminalValuePos.val = initialValuePos.val + (groupLiveCounts steps).sum ∧
      terminalNodePos.val = initialNodePos.val +
        32 * (groupFrontierCounts steps).sum := by
  induction chain with
  | nil next nodePos valuePos =>
      simp [groupLiveCounts, groupFrontierCounts]
  | @cons summary tail terminalNext terminalNodePos terminalValuePos rest ih =>
      have positions := summary_child_positions_are_exact summary
      rcases ih with ⟨tailValue, tailNode⟩
      constructor
      · simpa [groupLiveCounts, positions.final_value_pos, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using tailValue
      · simpa [groupFrontierCounts, positions.final_node_pos, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailNode

#print axioms OrderedGroupStepChain.cursor_prefixes
#print axioms OrderedGroupStepChain.terminal_cursors

end AspisV5MerkleUnchangedFullGroupCursorPrefixes
