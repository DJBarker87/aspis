import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullCanonicalLevelStep
import V5MerkleUnchangedFullReleasedLevelSources

/-! Induct the one-level correspondence through the accepted outer loop. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AspisV5MerkleUnchangedFullCanonicalLevelInduction

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullLevelTraceLists
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullLevelChildSources
open AspisV5MerkleUnchangedFullCanonicalNodeTable
open AspisV5MerkleUnchangedFullCanonicalLevelStep
open AspisV5MerkleUnchangedFullReleasedLevelSources

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- The generated leaf vector is the canonical level-zero active vector. -/
theorem node_core_initial_level_exact
    {sha256 : List ModelByte → Digest32} {tree : V5PrivateSection}
    {queries : Finset V5Query} {leafLevel : GeneratedDigestVec}
    {frontierBytes : Slice Std.U8}
    (base : ExactSectionGeneratedBaseData sha256 tree queries leafLevel
      frontierBytes)
    (core : ExactSectionNodeCore sha256 tree queries
      base.toExactSectionBaseData) :
    (orderedActiveIndices tree queries 0).map (core.node 0) =
      leafLevel.val.map generatedArrayToDigest := by
  calc
    (orderedActiveIndices tree queries 0).map (core.node 0) =
        (orderedActiveIndices tree queries 0).map base.leafAt := by
      apply List.map_congr_left
      intro index indexMem
      exact core.leaf_node_eq index
        ((Finset.mem_sort (fun left right : Nat => left ≤ right)).mp indexMem)
    _ = leafLevel.val.map generatedArrayToDigest :=
      base.generated_leaf_level_eq

/-- Starting from any identified local level, an ordered extracted outer-loop
chain preserves the canonical active-vector equation through every step. -/
theorem ordered_chain_preserves_canonical_active_values
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {frontierBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {binaryDepth : Std.U32} {leafLevel : GeneratedDigestVec}
    (base : ExactSectionGeneratedBaseData sha256 tree queries leafLevel
      frontierBytes)
    (core : ExactSectionNodeCore sha256 tree queries
      base.toExactSectionBaseData)
    (fields : FullExactConstructedTopologyFields queries topology)
    {initialLevel initialNext finalLevel finalNext : GeneratedDigestVec}
    {initialNodePos finalNodePos : Std.Usize}
    {initialPending finalPending : Option Bool}
    {steps : List (RawLevelStepSummary sha256 root frontierBytes topology
      binaryDepth)}
    (chain : OrderedLevelStepChain sha256 root frontierBytes topology
      binaryDepth initialLevel initialNext initialNodePos initialPending steps
      finalLevel finalNext finalNodePos finalPending)
    (startLevel : Nat)
    (within_section : startLevel + steps.length ≤ radixLevelCount tree)
    (plan_at : ∀ ordinal (ordinal_lt : ordinal < steps.length),
      steps[ordinal].planLevel.val =
        sectionRadixStart tree + (startLevel + ordinal))
    (cursor_at : ∀ ordinal (ordinal_lt : ordinal < steps.length),
      steps[ordinal].startNodePos.val =
        32 * sectionFrontierOffset tree queries (startLevel + ordinal))
    (initial_values :
      (orderedActiveIndices tree queries startLevel).map
          (core.node startLevel) =
        initialLevel.val.map generatedArrayToDigest) :
    (orderedActiveIndices tree queries (startLevel + steps.length)).map
        (core.node (startLevel + steps.length)) =
      finalLevel.val.map generatedArrayToDigest := by
  induction chain generalizing startLevel with
  | nil level next nodePos pending =>
      simpa using initial_values
  | @cons summary tail finalLevel finalNext finalNodePos finalPending rest ih =>
      have headLevelLt : startLevel < radixLevelCount tree := by
        simp only [List.length_cons] at within_section
        omega
      have headPlan : summary.planLevel.val =
          sectionRadixStart tree + startLevel := by
        have exact := plan_at 0 (by simp)
        simpa using exact
      have headCursor : summary.startNodePos.val =
          32 * sectionFrontierOffset tree queries startLevel := by
        have exact := cursor_at 0 (by simp)
        simpa using exact
      have nextValues := level_step_preserves_canonical_active_values tree
        queries startLevel summary base core fields headPlan headLevelLt
        headCursor initial_values
      have tailWithin : startLevel + 1 + tail.length ≤
          radixLevelCount tree := by
        simp only [List.length_cons] at within_section
        omega
      have tailPlan : ∀ ordinal (ordinal_lt : ordinal < tail.length),
          tail[ordinal].planLevel.val =
            sectionRadixStart tree + (startLevel + 1 + ordinal) := by
        intro ordinal ordinal_lt
        have exact := plan_at (ordinal + 1) (by simpa using ordinal_lt)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using exact
      have tailCursor : ∀ ordinal (ordinal_lt : ordinal < tail.length),
          tail[ordinal].startNodePos.val =
            32 * sectionFrontierOffset tree queries
              (startLevel + 1 + ordinal) := by
        intro ordinal ordinal_lt
        have exact := cursor_at (ordinal + 1) (by simpa using ordinal_lt)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using exact
      have finalValues := ih (startLevel + 1) tailWithin
        tailPlan tailCursor nextValues
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalValues

/-- Applying the induction to the accepted released trace identifies its final
live vector with the canonical top active nodes. -/
theorem released_sources_final_level_matches_canonical_nodes
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {generatedTag : Std.U8}
    {generatedWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : AspisV5MerkleUnchangedFullHelperSoundness.FullExactReleasedHelperTrace
      sha256 root binaryDepth generatedTag generatedWidth expectedIndices
      proofBytes topology radixLevel level next opening remainder outputLevel
      outputNext)
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (base : ExactSectionGeneratedBaseData sha256 tree queries
      trace.execution.leafLevel opening.frontier)
    (core : ExactSectionNodeCore sha256 tree queries
      base.toExactSectionBaseData)
    (sources : ExactReleasedSectionLevelSources trace tree queries)
    (fields : FullExactConstructedTopologyFields queries topology) :
    (orderedActiveIndices tree queries (radixLevelCount tree)).map
        (core.node (radixLevelCount tree)) =
      outputLevel.val.map generatedArrayToDigest := by
  have matchedEq : trace.execution.matched = {
      topology := topology
      radix_level := radixLevel
      binary_depth := binaryDepth
      expected_len := Slice.len expectedIndices
    } := sources.matched_shape
  let matchedFields : FullExactConstructedTopologyFields queries
      trace.execution.matched.topology := by
    simpa [matchedEq] using fields
  have initialValues := node_core_initial_level_exact base core
  have finalValues := ordered_chain_preserves_canonical_active_values tree
    queries base core matchedFields sources.view.chain 0
    (by simpa [sources.steps_length])
    (fun ordinal ordinal_lt => by
      have local_lt : ordinal < radixLevelCount tree := by
        simpa [sources.steps_length] using ordinal_lt
      simpa using sources.plan_at ordinal local_lt)
    (fun ordinal ordinal_lt => by
      have local_lt : ordinal < radixLevelCount tree := by
        simpa [sources.steps_length] using ordinal_lt
      simpa using sources.start_cursor ordinal local_lt)
    initialValues
  simpa [sources.steps_length] using finalValues

#print axioms node_core_initial_level_exact
#print axioms ordered_chain_preserves_canonical_active_values
#print axioms released_sources_final_level_matches_canonical_nodes

end AspisV5MerkleUnchangedFullCanonicalLevelInduction
