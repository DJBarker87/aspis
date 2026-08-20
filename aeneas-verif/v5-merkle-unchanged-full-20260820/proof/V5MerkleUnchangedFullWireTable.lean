import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullWireCanonicality
import V5MerkleUnchangedFullFrontierChunks
import V5MerkleUnchangedFullLeafTable

/-! Assemble the parser bytes, exact records, and exact frontier into one
maintained section-wire equation. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullWireTable

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullParserBridge
open AspisV5MerkleUnchangedFullWireCanonicality
open AspisV5MerkleUnchangedFullFrontierChunks
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullRecordChunks
open AspisV5MerkleUnchangedFullLeafTable

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte
abbrev generatedByte :=
  AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte

@[simp] theorem radix_generated_byte_eq (byte : Std.U8) :
    AspisV5MerkleUnchangedFullRadixSoundness.generatedU8ToByte byte =
      generatedByte byte := by
  apply Fin.ext
  rfl

/-- Public wire data needed by `ExactSectionTrace`.  `wire` is the exact
prefix consumed by the unchanged parser, while `remainder` is the literal
unconsumed suffix. -/
structure ExactWireTable
    (proofBytes remainder : Slice Std.U8)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (indices : List Nat) (recordAt : Nat → List ModelByte) where
  wire : List ModelByte
  frontier : List Digest32
  wire_eq : wire = encodePrivateSection (indices.map recordAt) frontier
  records_bytes : (indices.map recordAt).flatten =
    opening.records.val.map generatedByte
  frontier_bytes : frontier.flatMap digestBytes =
    opening.frontier.val.map generatedByte
  proof_split : proofBytes.val.map generatedByte =
    wire ++ remainder.val.map generatedByte

/-- A successful unchanged parser plus the exact leaf table determines the
literal maintained section encoding, including both length headers and every
frontier byte. -/
theorem released_helper_yields_exact_wire_table
    {sha256 : List ModelByte → Digest32}
    {root : GeneratedDigest} {binaryDepth : Std.U32} {treeTag : Std.U8}
    {valueWidth : Std.Usize} {expectedIndices : Slice Std.U32}
    {proofBytes : Slice Std.U8}
    {topology : aspis_core.merkle.Radix4BinaryCapTopology}
    {radixLevel : Std.Usize} {level next : GeneratedDigestVec}
    {opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening}
    {remainder : Slice Std.U8}
    {outputLevel outputNext : GeneratedDigestVec}
    (trace : FullExactReleasedHelperTrace sha256 root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext)
    (indices : List Nat)
    (indicesModel : expectedIndices.val.map (fun index => index.val) = indices)
    (expectedPositive : 0 < (Slice.len expectedIndices).val)
    (leafTable : ExactLeafTable sha256 treeTag valueWidth indices
      trace.execution.recordIter trace.execution.leafLevel) :
    Nonempty (ExactWireTable proofBytes remainder opening indices
      leafTable.recordAt) := by
  obtain ⟨chunks, recordWidth⟩ :=
    released_helper_record_chunks_exact trace.execution trace.parser
      expectedPositive
  obtain ⟨rawFrontierCount, countEq, widthEq, countOffset,
    recordsOffset, recordsEq, recordsLength, frontierCountOffset,
    frontierOffset, frontierEq, rawFrontierLength, endOffset, endBound,
    remainderEq⟩ := trace.parser
  obtain ⟨frontierCount, countHeader, frontierHeader, frontierLength⟩ :=
    parse_private_opening_success_headers proofBytes
      (Slice.len expectedIndices) valueWidth opening remainder
      trace.execution.parse_run
  have hfrontierCount : frontierCount = rawFrontierCount := by
    omega
  obtain ⟨frontier, frontierCountEq, frontierBytes⟩ :=
    reify_frontier_blocks opening.frontier.val frontierCount frontierLength
  have frontierBytesExact : frontier.flatMap digestBytes =
      opening.frontier.val.map generatedByte := by
    rw [frontierBytes]
    apply List.map_congr_left
    intro byte _
    exact radix_generated_byte_eq byte
  have hindexCount : (Slice.len expectedIndices).val = indices.length := by
    rw [Slice.len_val]
    have := congrArg List.length indicesModel
    simpa using this
  have recordsBytes :
      (indices.map leafTable.recordAt).flatten =
        opening.records.val.map generatedByte := by
    calc
      (indices.map leafTable.recordAt).flatten =
          (trace.execution.recordIter.chunks.map fun record =>
            record.val.map generatedByte).flatten := by
              rw [leafTable.records_eq]
      _ = ((trace.execution.recordIter.chunks.map fun record =>
          record.val).flatten).map generatedByte := by
            simp [List.map_flatten, List.map_map, Function.comp_def]
      _ = opening.records.val.map generatedByte := by
            rw [chunks.flatten_eq]
  let recordsEnd := 2 + (Slice.len expectedIndices).val *
    (valueWidth.val + 32)
  let frontierStart := recordsEnd + 4
  let sectionEnd := frontierStart + frontierCount * 32
  have hrawCount : rawFrontierCount = frontierCount := hfrontierCount.symm
  have hsectionEnd : opening.offsets.end.val = sectionEnd := by
    simpa [recordsEnd, frontierStart, sectionEnd, hrawCount] using endOffset
  have hrecordsSlice : opening.records.val =
      List.slice 2 recordsEnd proofBytes.val := by
    simpa [recordsEnd] using recordsEq
  have hfrontierSlice : opening.frontier.val =
      List.slice frontierStart sectionEnd proofBytes.val := by
    simpa [recordsEnd, frontierStart, sectionEnd, hrawCount] using frontierEq
  have hsplit := take_four_slices proofBytes.val 2 recordsEnd
    frontierStart sectionEnd (by simp [recordsEnd])
    (by simp [frontierStart]) (by simp [sectionEnd])
  let wire := (proofBytes.val.take opening.offsets.end.val).map
    generatedByte
  have wireEq : wire =
      encodePrivateSection (indices.map leafTable.recordAt) frontier := by
    unfold wire
    rw [hsectionEnd]
    rw [hsplit]
    simp only [List.map_append]
    have recordsSliceBytes :
        (List.slice 2 recordsEnd proofBytes.val).map generatedByte =
          (indices.map leafTable.recordAt).flatten := by
      rw [← hrecordsSlice, recordsBytes]
    have frontierSliceBytes :
        (List.slice frontierStart sectionEnd proofBytes.val).map
            generatedByte = frontier.flatMap digestBytes := by
      rw [← hfrontierSlice, frontierBytesExact]
    unfold encodePrivateSection
    rw [countHeader, recordsSliceBytes, frontierHeader,
      frontierSliceBytes, List.length_map, hindexCount, frontierCountEq]
  have proofSplit : proofBytes.val.map generatedByte =
      wire ++ remainder.val.map generatedByte := by
    unfold wire
    rw [remainderEq]
    have htakeDrop := List.take_append_drop opening.offsets.end.val
      proofBytes.val
    simpa only [List.map_append] using
      congrArg (List.map generatedByte) htakeDrop.symm
  exact ⟨{
    wire := wire
    frontier := frontier
    wire_eq := wireEq
    records_bytes := recordsBytes
    frontier_bytes := frontierBytesExact
    proof_split := proofSplit }⟩

#print axioms released_helper_yields_exact_wire_table

end AspisV5MerkleUnchangedFullWireTable
