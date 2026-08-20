import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullBinaryCapSemantics
import V5MerkleUnchangedFullReleasedLevelSources
import V5MerkleUnchangedFullSectionBase

/-! Exact final binary-cap data for one accepted released helper. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullReleasedBinaryCap

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullWireTable
open AspisV5MerkleUnchangedFullBinaryCapSemantics
open AspisV5MerkleUnchangedFullReleasedLevelSources

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

theorem top_active_iff_shared_level_eight
    (tree : V5PrivateSection) (queries : Finset V5Query) (index : Nat) :
    index ∈ activeIndices tree queries (radixLevelCount tree) ↔
      index ∈ sharedLevelIndices queries 8 := by
  constructor
  · intro active
    have ordered : index ∈
        orderedActiveIndices tree queries (radixLevelCount tree) :=
      (Finset.mem_sort (fun left right : Nat => left ≤ right)).mpr active
    rw [orderedActiveIndices_eq_shared_suffix,
      section_start_add_radix_count] at ordered
    exact ordered
  · intro shared
    have ordered : index ∈
        orderedActiveIndices tree queries (radixLevelCount tree) := by
      rw [orderedActiveIndices_eq_shared_suffix,
        section_start_add_radix_count]
      exact shared
    exact (Finset.mem_sort (fun left right : Nat => left ≤ right)).mp ordered

/-- The exact odd-cap location also proves the parser supplied exactly the
complete maintained frontier: no missing or trailing 32-byte block remains. -/
theorem odd_cap_data_yields_full_frontier_length
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {sha256 : List ModelByte → Digest32} {root : Digest32}
    {live frontier : List Digest32}
    (cap : ExactOddBinaryCapData sha256 root
      (sharedLevelIndices queries 8) live frontier
      (radixFrontierPositions tree queries).length) :
    frontier.length = (frontierPositions tree queries).length := by
  cases cap.location with
  | both activeExact liveExact frontierConsumed =>
      have zeroActive : 0 ∈
          activeIndices tree queries (radixLevelCount tree) :=
        (top_active_iff_shared_level_eight tree queries 0).mpr (by
          rw [activeExact]
          simp)
      have oneActive : 1 ∈
          activeIndices tree queries (radixLevelCount tree) :=
        (top_active_iff_shared_level_eight tree queries 1).mpr (by
          rw [activeExact]
          simp)
      have binaryEmpty : binaryCapFrontierPositions tree queries = [] := by
        simp [binaryCapFrontierPositions, zeroActive, oneActive]
      unfold frontierPositions
      rw [binaryEmpty, List.append_nil]
      exact frontierConsumed.symm
  | liveLeft activeExact liveExact frontierBound rightExact frontierConsumed =>
      have zeroActive : 0 ∈
          activeIndices tree queries (radixLevelCount tree) :=
        (top_active_iff_shared_level_eight tree queries 0).mpr (by
          rw [activeExact]
          simp)
      have oneInactive : 1 ∉
          activeIndices tree queries (radixLevelCount tree) := by
        intro oneActive
        have shared :=
          (top_active_iff_shared_level_eight tree queries 1).mp oneActive
        rw [activeExact] at shared
        simp at shared
      have binaryOne : binaryCapFrontierPositions tree queries =
          [{ level := radixLevelCount tree, index := 1 }] := by
        simp [binaryCapFrontierPositions, zeroActive, oneInactive]
      unfold frontierPositions
      rw [binaryOne, List.length_append, List.length_singleton]
      exact frontierConsumed.symm
  | liveRight activeExact liveExact frontierBound leftExact frontierConsumed =>
      have oneActive : 1 ∈
          activeIndices tree queries (radixLevelCount tree) :=
        (top_active_iff_shared_level_eight tree queries 1).mpr (by
          rw [activeExact]
          simp)
      have zeroInactive : 0 ∉
          activeIndices tree queries (radixLevelCount tree) := by
        intro zeroActive
        have shared :=
          (top_active_iff_shared_level_eight tree queries 0).mp zeroActive
        rw [activeExact] at shared
        simp at shared
      have binaryOne : binaryCapFrontierPositions tree queries =
          [{ level := radixLevelCount tree, index := 0 }] := by
        simp [binaryCapFrontierPositions, zeroInactive, oneActive]
      unfold frontierPositions
      rw [binaryOne, List.length_append, List.length_singleton]
      exact frontierConsumed.symm

/-- Root witness and full-frontier length exported from the literal accepted
helper execution. -/
structure ExactReleasedSectionBinaryCap
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
    (base : ExactSectionGeneratedBaseData sha256 tree queries
      trace.execution.leafLevel opening.frontier)
    (sources : ExactReleasedSectionLevelSources trace tree queries) : Type where
  cap : ExactOddBinaryCapData sha256
    (AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest root)
    (sharedLevelIndices queries 8)
    (outputLevel.val.map
      AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest)
    base.frontier (radixFrontierPositions tree queries).length
  frontier_length : base.frontier.length =
    (frontierPositions tree queries).length

theorem released_helper_yields_exact_binary_cap
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
    (base : ExactSectionGeneratedBaseData sha256 tree queries
      trace.execution.leafLevel opening.frontier)
    (sources : ExactReleasedSectionLevelSources trace tree queries)
    (depth_exact : binaryDepth.val = AspisV5MerkleAuthenticationBinding.binaryDepth tree)
    (fields : FullExactConstructedTopologyFields queries topology) :
    Nonempty (ExactReleasedSectionBinaryCap trace tree queries base sources) := by
  have matchedEq : trace.execution.matched = {
      topology := topology
      radix_level := radixLevel
      binary_depth := binaryDepth
      expected_len := Slice.len expectedIndices
    } := sources.matched_shape
  let matchedFields : FullExactConstructedTopologyFields queries
      trace.execution.matched.topology := by
    simpa [matchedEq] using fields
  have matchedDepth : trace.execution.matched.binary_depth.val =
      AspisV5MerkleAuthenticationBinding.binaryDepth tree := by
    simpa [matchedEq] using depth_exact
  have odd := released_binary_depth_is_odd tree
    trace.execution.matched.binary_depth matchedDepth
  have frontierFlat : base.frontier.flatMap digestBytes =
      opening.frontier.val.map
        AspisV5MerkleUnchangedFullRadixSoundness.generatedU8ToByte := by
    calc
      base.frontier.flatMap digestBytes =
          opening.frontier.val.map
            AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte :=
        base.generated_frontier_bytes_eq
      _ = opening.frontier.val.map
            AspisV5MerkleUnchangedFullRadixSoundness.generatedU8ToByte := by
        apply List.map_congr_left
        intro byte byteMem
        exact (radix_generated_byte_eq byte).symm
  have capData := final_root_witness_yields_binary_cap_data sha256 root
    opening.frontier trace.execution.matched.topology
    trace.execution.matched.binary_depth outputLevel sources.terminalNodePos
    queries matchedFields odd base.frontier
    (radixFrontierPositions tree queries).length frontierFlat
    sources.terminal_cursor sources.view.root_witness
  let cap := Classical.choice capData
  exact ⟨{
    cap := cap
    frontier_length := odd_cap_data_yields_full_frontier_length tree queries cap
  }⟩

#print axioms top_active_iff_shared_level_eight
#print axioms odd_cap_data_yields_full_frontier_length
#print axioms released_helper_yields_exact_binary_cap

end AspisV5MerkleUnchangedFullReleasedBinaryCap
