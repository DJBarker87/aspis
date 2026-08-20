import V5MerkleUnchangedDriverProof
import V5MerkleUnchangedFullSectionCallBridge

/-! Thin released-parameter wrapper from the exact outer-loop call record to
the per-section maintained acceptance theorem. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedGeneratedSectionBridge

open V5MerkleUnchangedFull
open V5MerkleUnchangedDriverProof
open V5MerkleUnchangedCompat
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionCallBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev GeneratedOpening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev GeneratedHash := Slice (Slice Std.U8) → GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

def sectionOrdinal : V5PrivateSection → Std.Usize
  | .c1 => 0#usize
  | .c2 => 1#usize
  | .line1 => 2#usize
  | .line2 => 3#usize
  | .line3 => 4#usize

private def sectionDepthWord : V5PrivateSection → Std.U32
  | .c1 | .c2 => 17#u32
  | .line1 => 15#u32
  | .line2 => 13#u32
  | .line3 => 11#u32

private def sectionTagWord : V5PrivateSection → Std.U8
  | .c1 => 64#u8
  | .c2 => 192#u8
  | .line1 => 65#u8
  | .line2 => 66#u8
  | .line3 => 67#u8

private def sectionWidthWord : V5PrivateSection → Std.Usize
  | .c1 => 256#usize
  | .c2 => 192#usize
  | .line1 | .line2 | .line3 => 64#usize

private def releasedTagArray : Array Std.U8 5#usize :=
  Array.make 5#usize [64#u8, 192#u8, 65#u8, 66#u8, 67#u8]

private theorem generated_depth_lookup (tree : V5PrivateSection) :
    Array.index_usize private_openings.V5_PRIVATE_DEPTHS
      (sectionOrdinal tree) = .ok (sectionDepthWord tree) := by
  cases tree <;>
    unfold private_openings.V5_PRIVATE_DEPTHS sectionOrdinal sectionDepthWord
      Array.index_usize <;> rfl

private theorem generated_width_lookup (tree : V5PrivateSection) :
    Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS
      (sectionOrdinal tree) = .ok (sectionWidthWord tree) := by
  cases tree <;>
    unfold private_openings.V5_PRIVATE_VALUE_WIDTHS sectionOrdinal
      sectionWidthWord Array.index_usize <;> rfl

private theorem generated_tags_exact :
    private_openings.V5_PRIVATE_TREE_TAGS = .ok releasedTagArray := by
  unfold private_openings.V5_PRIVATE_TREE_TAGS releasedTagArray
    aspis_core.circle_line_merkle.CIRCLE_LINE_TAGS
    aspis_core.circle_merkle.CIRCLE_C1_LAYER0_TAG
    aspis_core.circle_merkle.CIRCLE_C2_LAYER0_TAG Array.index_usize
  rfl

private theorem generated_tag_lookup (tree : V5PrivateSection) :
    Array.index_usize releasedTagArray (sectionOrdinal tree) =
      .ok (sectionTagWord tree) := by
  cases tree <;>
    unfold releasedTagArray sectionOrdinal sectionTagWord Array.index_usize <;>
    rfl

private theorem section_depth_word_val (tree : V5PrivateSection) :
    (sectionDepthWord tree).val = binaryDepth tree := by
  cases tree <;> rfl

private theorem section_tag_word_val (tree : V5PrivateSection) :
    (sectionTagWord tree).val = (treeTag tree).val := by
  cases tree <;> rfl

private theorem section_width_word_val (tree : V5PrivateSection) :
    (sectionWidthWord tree).val = valueWidth tree := by
  cases tree <;> rfl

/-- Exact scalar and index identities selected by one generated outer-loop
call. -/
structure ReleasedGeneratedSectionParameters
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {hash : GeneratedHash} {selected : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {sectionIndex radixLevel : Std.Usize}
    {level0 next0 level1 next1 : GeneratedDigestVec}
    {remainder0 remainder1 : Slice Std.U8}
    {parsed0 parsed1 : Array (Option GeneratedOpening) 5#usize}
    (call : GeneratedSectionCall hash selected roots topology sectionIndex
      radixLevel level0 next0 level1 next1 remainder0 remainder1 parsed0
      parsed1) : Prop where
  depth : call.depth.val = binaryDepth tree
  tag : call.tag.val = (treeTag tree).val
  width : call.width.val = valueWidth tree
  radix : radixLevel.val = sectionRadixStart tree
  indices : selected.val.map (fun index => index.val) =
    orderedActiveIndices tree queries 0

theorem generated_section_call_parameters
    (tree : V5PrivateSection) (queries : Finset V5Query)
    {hash : GeneratedHash} {selected : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {sectionIndex radixLevel : Std.Usize}
    {level0 next0 level1 next1 : GeneratedDigestVec}
    {remainder0 remainder1 : Slice Std.U8}
    {parsed0 parsed1 : Array (Option GeneratedOpening) 5#usize}
    (call : GeneratedSectionCall hash selected roots topology sectionIndex
      radixLevel level0 next0 level1 next1 remainder0 remainder1 parsed0
      parsed1)
    (sectionModel : sectionIndex = sectionOrdinal tree)
    (radixModel : radixLevel.val = sectionRadixStart tree)
    (indicesModel : selected.val.map (fun index => index.val) =
      orderedActiveIndices tree queries 0) :
    ReleasedGeneratedSectionParameters tree queries call := by
  have depthLookup :
      Array.index_usize private_openings.V5_PRIVATE_DEPTHS sectionIndex =
        .ok (sectionDepthWord tree) := by
    rw [sectionModel]
    exact generated_depth_lookup tree
  have depthWord : sectionDepthWord tree = call.depth :=
    Result.ok.inj (depthLookup.symm.trans call.depth_eq)
  have widthLookup :
      Array.index_usize private_openings.V5_PRIVATE_VALUE_WIDTHS sectionIndex =
        .ok (sectionWidthWord tree) := by
    rw [sectionModel]
    exact generated_width_lookup tree
  have widthWord : sectionWidthWord tree = call.width :=
    Result.ok.inj (widthLookup.symm.trans call.width_eq)
  have tagsEq : releasedTagArray = call.tags :=
    Result.ok.inj (generated_tags_exact.symm.trans call.tags_eq)
  have tagLookupOrdinal :
      Array.index_usize call.tags (sectionOrdinal tree) =
        .ok (sectionTagWord tree) := by
    rw [← tagsEq]
    exact generated_tag_lookup tree
  have selectedTag :
      Array.index_usize call.tags sectionIndex =
        .ok (sectionTagWord tree) := by
    exact (congrArg (Array.index_usize call.tags) sectionModel).trans
      tagLookupOrdinal
  have tagWord : sectionTagWord tree = call.tag :=
    Result.ok.inj (selectedTag.symm.trans call.tag_eq)
  exact {
    depth := by rw [← depthWord]; exact section_depth_word_val tree
    tag := by rw [← tagWord]; exact section_tag_word_val tree
    width := by rw [← widthWord]; exact section_width_word_val tree
    radix := radixModel
    indices := indicesModel }

/-- Direct bridge requested by the five-call proof: the literal
`GeneratedSectionCall.helper_call` yields the maintained exact acceptance for
that call's root, input proof slice, and returned remainder. -/
theorem generated_section_call_yields_exact_acceptance
    (sha256 : List ModelByte → Digest32)
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (queryCount : queries.card = 18)
    {hash : GeneratedHash} {selected : Slice Std.U32}
    {roots : Array GeneratedDigest 5#usize}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {sectionIndex radixLevel : Std.Usize}
    {level0 next0 level1 next1 : GeneratedDigestVec}
    {remainder0 remainder1 : Slice Std.U8}
    {parsed0 parsed1 : Array (Option GeneratedOpening) 5#usize}
    (call : GeneratedSectionCall hash selected roots topology sectionIndex
      radixLevel level0 next0 level1 next1 remainder0 remainder1 parsed0
      parsed1)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (parameters : ReleasedGeneratedSectionParameters tree queries call)
    (fields : FullExactConstructedTopologyFields queries topology) :
    ExactStateOnlyTopologyHelperAcceptance sha256 {
      tree := tree
      root := AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest
        call.root
      queries := queries
      proofBytes := remainder0.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte
      remainder := remainder1.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte } := by
  letI : HashContext := { hash := hash }
  exact generated_helper_success_yields_exact_acceptance sha256 hhash tree
    queries queryCount call.root call.depth call.tag call.width selected
    remainder0 topology radixLevel level0 next0 call.opening remainder1 level1
    next1 parameters.depth parameters.tag parameters.width parameters.radix
    parameters.indices fields call.helper_call

#print axioms generated_section_call_parameters
#print axioms generated_section_call_yields_exact_acceptance

end AspisV5MerkleUnchangedGeneratedSectionBridge
