import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullGroupChildSources

/-! Exact maintained frontier offsets for the extracted outer radix loop. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullLevelChildSources

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullGroupTraceLists
open AspisV5MerkleUnchangedFullGroupCursorPrefixes
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionChildOrder
open AspisV5MerkleUnchangedFullGroupChildSources

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

noncomputable def rawLevelFrontierCounts
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)) : List Nat :=
  steps.map fun summary => (groupFrontierCounts summary.groupSteps).sum

def sectionLevelFrontierCounts (tree : V5PrivateSection)
    (queries : Finset V5Query) : List Nat :=
  (List.range (radixLevelCount tree)).map fun level =>
    (levelAbsentChildIndices tree queries level).length

def sectionFrontierOffset (tree : V5PrivateSection)
    (queries : Finset V5Query) (level : Nat) : Nat :=
  ((sectionLevelFrontierCounts tree queries).take level).sum

/-- A child at a known within-level absent-child rank has this exact global
position in the maintained radix frontier. -/
theorem level_frontier_rank_to_global
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (level localOrdinal index : Nat)
    (level_lt : level < radixLevelCount tree)
    (local_at : (levelAbsentChildIndices tree queries level)[localOrdinal]? =
      some index) :
    (radixFrontierPositions tree queries)[
      sectionFrontierOffset tree queries level + localOrdinal]? =
        some ({ level := level, index := index } : FrontierPosition) := by
  obtain ⟨local_lt, local_value⟩ :=
    List.getElem?_eq_some_iff.mp local_at
  let levels := List.range (radixLevelCount tree)
  let groups := levels.map fun currentLevel =>
    (levelAbsentChildIndices tree queries currentLevel).map fun currentIndex =>
      ({ level := currentLevel, index := currentIndex } : FrontierPosition)
  have group_lt : level < groups.length := by
    simpa [groups, levels] using level_lt
  have group_eq : groups.get ⟨level, group_lt⟩ =
      (levelAbsentChildIndices tree queries level).map fun currentIndex =>
        ({ level := level, index := currentIndex } : FrontierPosition) := by
    rw [List.get_eq_getElem]
    simp [groups, levels, List.getElem_map, List.getElem_range]
  have group_local_lt : localOrdinal <
      (groups.get ⟨level, group_lt⟩).length := by
    rw [group_eq, List.length_map]
    exact local_lt
  have flattened := flatten_get_at_group groups level group_lt localOrdinal
    group_local_lt
  have group_value :
      (groups.get ⟨level, group_lt⟩).get
          ⟨localOrdinal, group_local_lt⟩ =
        ({ level := level, index := index } : FrontierPosition) := by
    calc
      (groups.get ⟨level, group_lt⟩).get
          ⟨localOrdinal, group_local_lt⟩ =
          (((levelAbsentChildIndices tree queries level).map fun currentIndex =>
            ({ level := level, index := currentIndex } : FrontierPosition)).get
              ⟨localOrdinal, by simpa using local_lt⟩) :=
        List.getElem_of_eq group_eq group_local_lt
      _ = ({ level := level, index := index } : FrontierPosition) := by
        rw [List.get_eq_getElem, List.getElem_map]
        exact congrArg
          (fun currentIndex =>
            ({ level := level, index := currentIndex } : FrontierPosition))
          local_value
  have flattened_value : groups.flatten[
      ((groups.map List.length).take level).sum + localOrdinal]? =
        some ({ level := level, index := index } : FrontierPosition) := by
    rw [flattened, group_value]
  rw [radixFrontierPositions_eq_levelAbsentChildIndices]
  simpa [sectionFrontierOffset, sectionLevelFrontierCounts, groups, levels,
    List.flatMap, Function.comp_def] using flattened_value

/-- One generated outer iteration consumes exactly one 32-byte block per
maintained absent child at that local radix level. -/
theorem level_step_frontier_count_exact
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    (summary : RawLevelStepSummary sha256 root nodeBytes topology binaryDepth)
    (fields : FullExactConstructedTopologyFields queries topology)
    (plan_eq : summary.planLevel.val = sectionRadixStart tree + level)
    (level_lt : level < radixLevelCount tree) :
    (groupFrontierCounts summary.groupSteps).sum =
        (levelAbsentChildIndices tree queries level).length ∧
      summary.endNodePos.val = summary.startNodePos.val +
        32 * (levelAbsentChildIndices tree queries level).length := by
  have counts := level_group_count_lists_exact tree queries level summary
    fields plan_eq level_lt
  have terminal :=
    AspisV5MerkleUnchangedFullGroupCursorPrefixes.OrderedGroupStepChain.terminal_cursors
      summary.group_view.chain
  have countExact : (groupFrontierCounts summary.groupSteps).sum =
      (levelAbsentChildIndices tree queries level).length := by
    rw [counts.2]
    simp [levelAbsentChildIndices, List.length_flatMap, Function.comp_def]
  constructor
  · exact countExact
  · rw [terminal.2, countExact]

/-- Generic outer-loop cursor prefix: before iteration `index`, the source
has consumed exactly the absent-child totals of all earlier iterations. -/
theorem OrderedLevelStepChain.node_cursor_prefixes
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {initialLevel initialNext finalLevel finalNext : GeneratedDigestVec}
    {initialNodePos finalNodePos : Std.Usize}
    {initialPending finalPending : Option Bool}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (chain : OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
      initialLevel initialNext initialNodePos initialPending steps finalLevel
      finalNext finalNodePos finalPending) :
    ∀ index (index_lt : index < steps.length),
      steps[index].startNodePos.val = initialNodePos.val + 32 *
        ((rawLevelFrontierCounts steps).take index).sum := by
  induction chain with
  | nil level next nodePos pending =>
      intro index index_lt
      simp at index_lt
  | @cons summary tail finalLevel finalNext finalNodePos finalPending rest ih =>
      intro index index_lt
      cases index with
      | zero => simp [rawLevelFrontierCounts]
      | succ index =>
          have tail_lt : index < tail.length := by simpa using index_lt
          have tailCursor := ih index tail_lt
          have groupTerminal :=
            AspisV5MerkleUnchangedFullGroupCursorPrefixes.OrderedGroupStepChain.terminal_cursors
              summary.group_view.chain
          simpa [rawLevelFrontierCounts, List.take_succ_cons,
            groupTerminal.2, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using tailCursor

/-- At outer-loop termination the source cursor has consumed exactly the
sum of the absent-child blocks recorded by every extracted level step. -/
theorem OrderedLevelStepChain.terminal_node_cursor
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {initialLevel initialNext finalLevel finalNext : GeneratedDigestVec}
    {initialNodePos finalNodePos : Std.Usize}
    {initialPending finalPending : Option Bool}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (chain : OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
      initialLevel initialNext initialNodePos initialPending steps finalLevel
      finalNext finalNodePos finalPending) :
    finalNodePos.val = initialNodePos.val + 32 *
      (rawLevelFrontierCounts steps).sum := by
  induction chain with
  | nil level next nodePos pending => simp [rawLevelFrontierCounts]
  | @cons summary tail finalLevel finalNext finalNodePos finalPending rest ih =>
      have groupTerminal :=
        AspisV5MerkleUnchangedFullGroupCursorPrefixes.OrderedGroupStepChain.terminal_cursors
          summary.group_view.chain
      simpa [rawLevelFrontierCounts, groupTerminal.2, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

/-- The exact outer-loop list view enumerates the section's local radix
levels consecutively when its generated start and end fields are identified. -/
theorem raw_level_view_has_exact_section_plans
    (tree : V5PrivateSection)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {iter : core.ops.range.Range Std.Usize}
    {initialLevel initialNext finalLevel finalNext : GeneratedDigestVec}
    {initialNodePos : Std.Usize} {initialPending : Option Bool}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)} {terminalNodePos : Std.Usize}
    (view : RawLevelTraceListView sha256 root nodeBytes topology binaryDepth
      iter initialLevel initialNext initialNodePos initialPending finalLevel
      finalNext steps terminalNodePos)
    (start_eq : iter.start.val = sectionRadixStart tree)
    (end_eq : iter.end.val = 8) :
    steps.length = radixLevelCount tree ∧
      ∀ level (level_lt : level < steps.length),
        steps[level].planLevel.val = sectionRadixStart tree + level := by
  have count := level_plan_count_is_exact view
  have sectionEnd := section_start_add_radix_count tree
  have stepsLength : steps.length = radixLevelCount tree := by
    rw [count, end_eq, start_eq]
    omega
  refine ⟨stepsLength, ?_⟩
  intro level level_lt
  have remaining_lt : level < iter.end.val - iter.start.val := by
    rw [← count]
    exact level_lt
  have remaining_lt' :
      level < iter.end.val - sectionRadixStart tree := by
    simpa [start_eq] using remaining_lt
  have point := congrArg (fun values => values[level]!) view.plans_exact
  simpa [levelPlans, remainingPlanLevels, level_lt, remaining_lt,
    remaining_lt', start_eq]
    using point

/-- Once the extracted steps are identified with the section's local levels,
their per-level source counts are exactly the maintained absent-child counts. -/
theorem raw_level_frontier_counts_exact
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (fields : FullExactConstructedTopologyFields queries topology)
    (steps_length : steps.length = radixLevelCount tree)
    (plan_at : ∀ level (level_lt : level < radixLevelCount tree),
      steps[level].planLevel.val = sectionRadixStart tree + level) :
    rawLevelFrontierCounts steps =
      sectionLevelFrontierCounts tree queries := by
  apply List.ext_getElem
  · simpa [rawLevelFrontierCounts, sectionLevelFrontierCounts, steps_length]
  · intro ordinal source_lt model_lt
    have ordinal_lt : ordinal < radixLevelCount tree := by
      simpa [sectionLevelFrontierCounts] using model_lt
    have sourceStep_lt : ordinal < steps.length := by
      rw [steps_length]
      exact ordinal_lt
    have exact := level_step_frontier_count_exact tree queries ordinal
      steps[ordinal] fields (plan_at ordinal ordinal_lt) ordinal_lt
    simp only [rawLevelFrontierCounts, sectionLevelFrontierCounts,
      List.getElem_map, List.getElem_range]
    exact exact.1

/-- The maintained cross-level absent-child totals flatten to exactly the
radix portion of the section frontier. -/
theorem section_level_frontier_total_exact
    (tree : V5PrivateSection) (queries : Finset V5Query) :
    (sectionLevelFrontierCounts tree queries).sum =
      (radixFrontierPositions tree queries).length := by
  rw [radixFrontierPositions_eq_levelAbsentChildIndices]
  simp [sectionLevelFrontierCounts, List.length_flatMap, Function.comp_def]

/-- If the source steps are the section's exact consecutive local levels,
their source frontier cursor is the exact maintained cross-level offset. -/
theorem ordered_section_level_start_cursor_exact
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {initialLevel initialNext finalLevel finalNext : GeneratedDigestVec}
    {initialNodePos finalNodePos : Std.Usize}
    {initialPending finalPending : Option Bool}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (chain : OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
      initialLevel initialNext initialNodePos initialPending steps finalLevel
      finalNext finalNodePos finalPending)
    (fields : FullExactConstructedTopologyFields queries topology)
    (steps_length : steps.length = radixLevelCount tree)
    (plan_at : ∀ level (level_lt : level < radixLevelCount tree),
      steps[level].planLevel.val = sectionRadixStart tree + level)
    (level : Nat) (level_lt : level < radixLevelCount tree) :
    steps[level].startNodePos.val = initialNodePos.val +
      32 * sectionFrontierOffset tree queries level := by
  have rawCountsExact : rawLevelFrontierCounts steps =
      sectionLevelFrontierCounts tree queries := by
    apply List.ext_getElem
    · simpa [rawLevelFrontierCounts, sectionLevelFrontierCounts,
        steps_length]
    · intro ordinal source_lt model_lt
      have ordinal_lt : ordinal < radixLevelCount tree := by
        simpa [sectionLevelFrontierCounts] using model_lt
      have sourceStep_lt : ordinal < steps.length := by
        rw [steps_length]
        exact ordinal_lt
      have exact := level_step_frontier_count_exact tree queries ordinal
        steps[ordinal] fields (plan_at ordinal ordinal_lt) ordinal_lt
      simp only [rawLevelFrontierCounts, sectionLevelFrontierCounts,
        List.getElem_map, List.getElem_range]
      exact exact.1
  have cursor := OrderedLevelStepChain.node_cursor_prefixes chain level
    (by simpa [steps_length] using level_lt)
  rw [rawCountsExact] at cursor
  simpa [sectionFrontierOffset] using cursor

/-- The cursor passed to the final binary-cap check starts immediately after
all and only the maintained radix-frontier blocks. -/
theorem ordered_section_terminal_cursor_exact
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {nodeBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32}
    {initialLevel initialNext finalLevel finalNext : GeneratedDigestVec}
    {initialNodePos finalNodePos : Std.Usize}
    {initialPending finalPending : Option Bool}
    {steps : List (RawLevelStepSummary sha256 root nodeBytes topology
      binaryDepth)}
    (chain : OrderedLevelStepChain sha256 root nodeBytes topology binaryDepth
      initialLevel initialNext initialNodePos initialPending steps finalLevel
      finalNext finalNodePos finalPending)
    (fields : FullExactConstructedTopologyFields queries topology)
    (steps_length : steps.length = radixLevelCount tree)
    (plan_at : ∀ level (level_lt : level < radixLevelCount tree),
      steps[level].planLevel.val = sectionRadixStart tree + level) :
    finalNodePos.val = initialNodePos.val + 32 *
      (radixFrontierPositions tree queries).length := by
  have terminal := OrderedLevelStepChain.terminal_node_cursor chain
  have counts := raw_level_frontier_counts_exact tree queries fields
    steps_length plan_at
  rw [counts, section_level_frontier_total_exact] at terminal
  exact terminal

#print axioms level_step_frontier_count_exact
#print axioms level_frontier_rank_to_global
#print axioms OrderedLevelStepChain.node_cursor_prefixes
#print axioms OrderedLevelStepChain.terminal_node_cursor
#print axioms raw_level_view_has_exact_section_plans
#print axioms raw_level_frontier_counts_exact
#print axioms section_level_frontier_total_exact
#print axioms ordered_section_level_start_cursor_exact
#print axioms ordered_section_terminal_cursor_exact

end AspisV5MerkleUnchangedFullLevelChildSources
