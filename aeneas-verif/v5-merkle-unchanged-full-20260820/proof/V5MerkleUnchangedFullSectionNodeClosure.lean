import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullReleasedBinaryCap
import V5MerkleUnchangedFullCanonicalLevelInduction

/-! Close the internal-node and root fields for one accepted released section. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullSectionNodeClosure

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullCanonicalNodeTable
open AspisV5MerkleUnchangedFullReleasedLevelSources
open AspisV5MerkleUnchangedFullReleasedBinaryCap
open AspisV5MerkleUnchangedFullCanonicalLevelInduction

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

private theorem complete_frontier_lookup
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries)
    (core : ExactSectionNodeCore sha256 tree queries base)
    (ordinal : Nat) (position : FrontierPosition)
    (position_at : (frontierPositions tree queries)[ordinal]? =
      some position) :
    base.frontier[ordinal]? =
      some (core.node position.level position.index) := by
  have point := congrArg (fun values => values[ordinal]?) core.frontier_eq
  rw [List.getElem?_map, position_at] at point
  simpa using point

private theorem first_binary_frontier_lookup
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (position : FrontierPosition)
    (binary_exact : binaryCapFrontierPositions tree queries = [position]) :
    (frontierPositions tree queries)[
      (radixFrontierPositions tree queries).length]? = some position := by
  unfold frontierPositions
  rw [List.getElem?_append_right (Nat.le_refl _), binary_exact]
  simp

/-- The generated radix induction and the exact odd-cap witness complete the
single maintained node table, including the final binary-root equation. -/
theorem released_helper_yields_exact_section_node_data
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
    (binary : ExactReleasedSectionBinaryCap trace tree queries base sources)
    (fields : FullExactConstructedTopologyFields queries topology) :
    Nonempty (ExactSectionNodeData sha256 tree
      (generatedArrayToDigest root) queries base.toExactSectionBaseData) := by
  let core := Classical.choice
    (frontier_length_yields_exact_node_core base.toExactSectionBaseData
      binary.frontier_length)
  have topValues := released_sources_final_level_matches_canonical_nodes trace
    tree queries base core sources fields
  have topOrder : orderedActiveIndices tree queries (radixLevelCount tree) =
      sharedLevelIndices queries 8 := by
    rw [orderedActiveIndices_eq_shared_suffix,
      section_start_add_radix_count]
  rw [topOrder] at topValues
  have rootEquation : (sha256MerkleHashing sha256).binaryNode
      (core.node (radixLevelCount tree) 0)
      (core.node (radixLevelCount tree) 1) = generatedArrayToDigest root := by
    cases binary.cap.location with
    | both activeExact liveExact frontierConsumed =>
        rw [activeExact, liveExact] at topValues
        simp only [List.map_cons, List.map_nil, List.cons.injEq,
          and_true] at topValues
        rcases topValues with ⟨leftExact, rightExact⟩
        calc
          (sha256MerkleHashing sha256).binaryNode
              (core.node (radixLevelCount tree) 0)
              (core.node (radixLevelCount tree) 1) =
              (sha256MerkleHashing sha256).binaryNode
                binary.cap.left binary.cap.right := by
            rw [leftExact, rightExact]
          _ = generatedArrayToDigest root := binary.cap.root_eq
    | liveLeft activeExact liveExact frontierBound rightExact
        frontierConsumed =>
        rw [activeExact, liveExact] at topValues
        simp only [List.map_cons, List.map_nil, List.cons.injEq,
          and_true] at topValues
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
        let position : FrontierPosition :=
          { level := radixLevelCount tree, index := 1 }
        have positionAt := first_binary_frontier_lookup tree queries position
          (by simpa [position] using binaryOne)
        have frontierAt := complete_frontier_lookup base.toExactSectionBaseData
          core (radixFrontierPositions tree queries).length position positionAt
        obtain ⟨frontierLt, frontierValue⟩ :=
          List.getElem?_eq_some_iff.mp frontierAt
        have rightNode : binary.cap.right =
            core.node (radixLevelCount tree) 1 := by
          calc
            binary.cap.right = base.frontier[
                (radixFrontierPositions tree queries).length] := rightExact
            _ = core.node (radixLevelCount tree) 1 := by
              simpa [position] using frontierValue
        calc
          (sha256MerkleHashing sha256).binaryNode
              (core.node (radixLevelCount tree) 0)
              (core.node (radixLevelCount tree) 1) =
              (sha256MerkleHashing sha256).binaryNode
                binary.cap.left binary.cap.right := by
            rw [topValues, rightNode]
          _ = generatedArrayToDigest root := binary.cap.root_eq
    | liveRight activeExact liveExact frontierBound leftExact
        frontierConsumed =>
        rw [activeExact, liveExact] at topValues
        simp only [List.map_cons, List.map_nil, List.cons.injEq,
          and_true] at topValues
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
        let position : FrontierPosition :=
          { level := radixLevelCount tree, index := 0 }
        have positionAt := first_binary_frontier_lookup tree queries position
          (by simpa [position] using binaryOne)
        have frontierAt := complete_frontier_lookup base.toExactSectionBaseData
          core (radixFrontierPositions tree queries).length position positionAt
        obtain ⟨frontierLt, frontierValue⟩ :=
          List.getElem?_eq_some_iff.mp frontierAt
        have leftNode : binary.cap.left =
            core.node (radixLevelCount tree) 0 := by
          calc
            binary.cap.left = base.frontier[
                (radixFrontierPositions tree queries).length] := leftExact
            _ = core.node (radixLevelCount tree) 0 := by
              simpa [position] using frontierValue
        calc
          (sha256MerkleHashing sha256).binaryNode
              (core.node (radixLevelCount tree) 0)
              (core.node (radixLevelCount tree) 1) =
              (sha256MerkleHashing sha256).binaryNode
                binary.cap.left binary.cap.right := by
            rw [leftNode, topValues]
          _ = generatedArrayToDigest root := binary.cap.root_eq
  exact ⟨{
    node := core.node
    leaf_node_eq := core.leaf_node_eq
    frontier_eq := core.frontier_eq
    parent_eq := core.parent_eq
    root_eq := rootEquation }⟩

/-- A completed section trace retaining its literal base fields.  These
equalities are needed when the five helper remainders are concatenated and
when the returned record slices are connected to their consumers. -/
structure ExactReleasedSectionTraceData
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {root : Digest32} {queries : Finset V5Query}
    (base : ExactSectionBaseData sha256 tree queries) where
  trace : ExactSectionTrace sha256 tree root queries
  wire_eq_base : trace.wire = base.wire
  recordAt_eq_base : trace.recordAt = base.recordAt
  frontier_eq_base : trace.frontier = base.frontier

/-- Parser/leaf/wire data plus the closed node table give the maintained
accepted section trace while retaining its exact base projections. -/
theorem released_helper_yields_exact_section_trace_data
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
    (binary : ExactReleasedSectionBinaryCap trace tree queries base sources)
    (fields : FullExactConstructedTopologyFields queries topology) :
    Nonempty (ExactReleasedSectionTraceData
      (root := generatedArrayToDigest root) base.toExactSectionBaseData) := by
  let nodes := Classical.choice
    (released_helper_yields_exact_section_node_data trace tree queries base
      sources binary fields)
  let sectionTrace := base_and_nodes_yield_exact_section_trace
    base.toExactSectionBaseData nodes
  exact ⟨{
    trace := sectionTrace
    wire_eq_base := rfl
    recordAt_eq_base := rfl
    frontier_eq_base := rfl }⟩

/-- Forgetting only the retained base projections gives the smaller section
trace used by the mathematical authentication model. -/
theorem released_helper_yields_exact_section_trace
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
    (binary : ExactReleasedSectionBinaryCap trace tree queries base sources)
    (fields : FullExactConstructedTopologyFields queries topology) :
    Nonempty (ExactSectionTrace sha256 tree (generatedArrayToDigest root)
      queries) := by
  let sectionData := Classical.choice
    (released_helper_yields_exact_section_trace_data trace tree queries base
      sources binary fields)
  exact ⟨sectionData.trace⟩

#print axioms released_helper_yields_exact_section_node_data
#print axioms released_helper_yields_exact_section_trace_data
#print axioms released_helper_yields_exact_section_trace

end AspisV5MerkleUnchangedFullSectionNodeClosure
