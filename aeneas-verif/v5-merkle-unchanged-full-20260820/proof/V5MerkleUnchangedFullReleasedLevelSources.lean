import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullHelperSoundness
import V5MerkleUnchangedFullLevelChildSources
import V5MerkleUnchangedFullMatchedSuffixShape

/-! Exact outer-level source alignment for one accepted released helper. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullReleasedLevelSources

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullLevelChildSources
open AspisV5MerkleUnchangedFullMatchedSuffixShape

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- The accepted helper's extracted outer loop, identified with the exact
local section levels and the exact global radix-frontier cursor. -/
structure ExactReleasedSectionLevelSources
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {generatedTag : Std.U8}
    {generatedWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : FullExactReleasedHelperTrace sha256 root binaryDepth generatedTag
      generatedWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (tree : V5PrivateSection) (queries : Finset V5Query) : Type where
  matched_shape : ExactMatchedSuffixShape topology radixLevel binaryDepth
    expectedIndices trace.execution.matched
  steps : List (RawLevelStepSummary sha256 root opening.frontier
    trace.execution.matched.topology trace.execution.matched.binary_depth)
  terminalNodePos : Std.Usize
  view : RawLevelTraceListView sha256 root opening.frontier
    trace.execution.matched.topology trace.execution.matched.binary_depth
    { start := trace.execution.matched.radix_level,
      «end» := trace.execution.matched.topology.radix_levels }
    trace.execution.leafLevel next 0#usize none outputLevel outputNext steps
    terminalNodePos
  steps_length : steps.length = radixLevelCount tree
  plan_at : ∀ localLevel (localLevel_lt : localLevel < radixLevelCount tree),
    steps[localLevel].planLevel.val = sectionRadixStart tree + localLevel
  start_cursor : ∀ localLevel
      (localLevel_lt : localLevel < radixLevelCount tree),
    steps[localLevel].startNodePos.val =
      32 * sectionFrontierOffset tree queries localLevel
  terminal_cursor : terminalNodePos.val =
    32 * (radixFrontierPositions tree queries).length

/-- The literal matcher result, extracted outer trace, released start level,
and constructor fields suffice to build the complete source-alignment package.
No independent loop or cursor equality is assumed. -/
theorem released_helper_yields_exact_level_sources
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {generatedTag : Std.U8}
    {generatedWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : FullExactReleasedHelperTrace sha256 root binaryDepth generatedTag
      generatedWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (radix_start : radixLevel.val = sectionRadixStart tree)
    (fields : FullExactConstructedTopologyFields queries topology) :
    Nonempty (ExactReleasedSectionLevelSources trace tree queries) := by
  have matchedShape := matched_suffix_success_shape topology radixLevel
    binaryDepth expectedIndices trace.execution.matched
    trace.execution.matched_run
  have matchedEq : trace.execution.matched = {
      topology := topology
      radix_level := radixLevel
      binary_depth := binaryDepth
      expected_len := Slice.len expectedIndices
    } := by
    exact matchedShape
  let matchedFields : FullExactConstructedTopologyFields queries
      trace.execution.matched.topology := by
    simpa [matchedEq] using fields
  obtain ⟨steps, terminalNodePos, view⟩ :=
    raw_level_trace_yields_list_view trace.radix
  have startExact :
      trace.execution.matched.radix_level.val = sectionRadixStart tree := by
    simpa [matchedEq] using radix_start
  have endExact : trace.execution.matched.topology.radix_levels.val = 8 := by
    simpa [matchedEq] using fields.radixLevels
  have plans := raw_level_view_has_exact_section_plans tree view startExact
    endExact
  have startCursor := ordered_section_level_start_cursor_exact tree queries
    view.chain matchedFields plans.1
    (fun localLevel localLevel_lt =>
      plans.2 localLevel (by simpa [plans.1] using localLevel_lt))
  have terminalCursor := ordered_section_terminal_cursor_exact tree queries
    view.chain matchedFields plans.1
    (fun localLevel localLevel_lt =>
      plans.2 localLevel (by simpa [plans.1] using localLevel_lt))
  exact ⟨{
    matched_shape := matchedShape
    steps := steps
    terminalNodePos := terminalNodePos
    view := view
    steps_length := plans.1
    plan_at := fun localLevel localLevel_lt =>
      plans.2 localLevel (by simpa [plans.1] using localLevel_lt)
    start_cursor := by
      intro localLevel localLevel_lt
      have exact := startCursor localLevel localLevel_lt
      simpa using exact
    terminal_cursor := by simpa using terminalCursor }⟩

#print axioms released_helper_yields_exact_level_sources

end AspisV5MerkleUnchangedFullReleasedLevelSources
