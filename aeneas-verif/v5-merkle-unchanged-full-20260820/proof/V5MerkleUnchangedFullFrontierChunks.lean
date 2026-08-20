import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullParserBridge
import V5MerkleUnchangedFullRadixSoundness

/-! Reify the parsed frontier byte string as exact 32-byte model digests. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullFrontierChunks

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleUnchangedFullParserBridge
open AspisV5MerkleUnchangedFullRadixSoundness

abbrev GeneratedDigest := Array Std.U8 32#usize

private theorem take_drop_flatten_fixed_width
    {A : Type*} (records : List (List A)) (width ordinal : Nat)
    (hall : ∀ record ∈ records, record.length = width)
    (hordinal : ordinal < records.length) :
    ((records.flatten.drop (ordinal * width)).take width) =
      records[ordinal] := by
  have hlengths : records.map List.length =
      List.replicate records.length width := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp
    · intro value hvalue
      simp only [List.mem_map] at hvalue
      obtain ⟨record, hrecord, rfl⟩ := hvalue
      exact hall record hrecord
  have hprefix : ((records.map List.length).take ordinal).sum =
      ordinal * width := by
    rw [hlengths, List.take_replicate, List.sum_replicate]
    simp
    omega
  rw [← hprefix, List.drop_sum_flatten]
  have hdrop : records.drop ordinal =
      records[ordinal] :: records.drop (ordinal + 1) := by
    rw [List.drop_eq_getElem_cons hordinal]
  rw [hdrop, List.flatten_cons,
    List.take_append_of_le_length
      (hall records[ordinal] (List.getElem_mem hordinal) |>.symm.le)]
  exact List.take_of_length_le (by
    rw [hall records[ordinal] (List.getElem_mem hordinal)])

/-- A byte string whose length is an exact multiple of 32 can be represented
without padding, omission, or trailing bytes as a list of model digests. -/
theorem reify_frontier_blocks
    (bytes : List Std.U8) (count : Nat)
    (hlength : bytes.length = count * 32) :
    ∃ frontier : List Digest32,
      frontier.length = count ∧
      frontier.flatMap digestBytes = bytes.map generatedU8ToByte := by
  induction count generalizing bytes with
  | zero =>
      have hempty : bytes = [] := List.length_eq_zero_iff.mp
        (by simpa using hlength)
      subst bytes
      exact ⟨[], rfl, rfl⟩
  | succ count ih =>
      have hthirtyTwo : 32 ≤ bytes.length := by
        rw [hlength]
        omega
      let headBytes := bytes.take 32
      let tailBytes := bytes.drop 32
      have hheadLength : headBytes.length = 32 := by
        simp only [headBytes, List.length_take]
        omega
      have htailLength : tailBytes.length = count * 32 := by
        simp only [tailBytes, List.length_drop]
        rw [hlength]
        omega
      obtain ⟨tailFrontier, htailCount, htailBytes⟩ :=
        ih tailBytes htailLength
      let headDigest : GeneratedDigest := ⟨headBytes, by
        simpa using hheadLength⟩
      refine ⟨generatedArrayToDigest headDigest :: tailFrontier, ?_, ?_⟩
      · simp [htailCount]
      · simp only [List.flatMap_cons]
        rw [digestBytes_generatedArrayToDigest, htailBytes]
        change headBytes.map generatedU8ToByte ++
            tailBytes.map generatedU8ToByte = bytes.map generatedU8ToByte
        rw [← List.map_append]
        exact congrArg (List.map generatedU8ToByte)
          (List.take_append_drop 32 bytes)

/-- The digest at position `index` occupies exactly bytes
`32 * index .. 32 * (index + 1)` of the flattened frontier. -/
theorem frontier_digest_slice_exact
    (frontier : List Digest32) (index : Nat)
    (hindex : index < frontier.length) :
    digestBytes frontier[index] =
      List.slice (32 * index) (32 * (index + 1))
        (frontier.flatMap digestBytes) := by
  have hfixed : ∀ record ∈ frontier.map digestBytes,
      record.length = 32 := by
    intro record hrecord
    simp only [List.mem_map] at hrecord
    obtain ⟨digest, _, rfl⟩ := hrecord
    exact digestBytes_length digest
  have hordinal : index < (frontier.map digestBytes).length := by
    simpa using hindex
  have hblock := take_drop_flatten_fixed_width
    (frontier.map digestBytes) 32 index hfixed hordinal
  rw [List.slice]
  have hwidth : 32 * (index + 1) - 32 * index = 32 := by omega
  rw [hwidth]
  symm
  simpa [List.flatMap_def, Nat.mul_comm] using hblock

/-- Indexed form after identifying the flattened frontier with the exact
parsed bytes. -/
theorem reified_frontier_digest_slice_exact
    (bytes : List Std.U8) (frontier : List Digest32)
    (hflat : frontier.flatMap digestBytes =
      bytes.map generatedU8ToByte)
    (index : Nat) (hindex : index < frontier.length) :
    digestBytes frontier[index] =
      List.slice (32 * index) (32 * (index + 1))
        (bytes.map generatedU8ToByte) := by
  rw [← hflat]
  exact frontier_digest_slice_exact frontier index hindex

/-- Byte-level form used by the cursor proof: the `byte`th byte of frontier
digest `index` is exactly parsed byte `32 * index + byte`. -/
theorem reified_frontier_byte_exact
    (bytes : List Std.U8) (frontier : List Digest32)
    (hflat : frontier.flatMap digestBytes =
      bytes.map generatedU8ToByte)
    (index : Nat) (hindex : index < frontier.length)
    (byte : Nat) (hbyte : byte < 32) :
    frontier[index] ⟨byte, hbyte⟩ =
      generatedU8ToByte bytes[32 * index + byte]! := by
  have hlengthRaw := congrArg List.length hflat
  have hbytesLength : bytes.length = 32 * frontier.length := by
    simpa [List.length_flatMap, digestBytes_length, Nat.mul_comm] using
      hlengthRaw.symm
  have hbytesIndex : 32 * index + byte < bytes.length := by
    rw [hbytesLength]
    omega
  rw [getElem!_pos]
  · have hdigest := reified_frontier_digest_slice_exact bytes frontier hflat
      index hindex
    have hleft : byte < (digestBytes frontier[index]).length := by
      simpa [digestBytes_length] using hbyte
    have hpoint := List.getElem_of_eq hdigest hleft
    change (List.ofFn frontier[index])[byte] = _ at hpoint
    rw [List.getElem_ofFn] at hpoint
    simpa [List.slice, hbyte, Nat.mul_add, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hpoint
  · exact hbytesIndex

/-- The exact parser length equation supplies the digest list consumed by the
maintained section wire grammar. -/
theorem exact_raw_parser_frontier_blocks
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (parser : ExactRawParserOutput proofBytes expectedCount valueWidth
      opening remainder) :
    ∃ frontierCount : Nat, ∃ frontier : List Digest32,
      opening.frontier.val.length = frontierCount * 32 ∧
      frontier.length = frontierCount ∧
      frontier.flatMap digestBytes =
        opening.frontier.val.map generatedU8ToByte := by
  rcases parser with
    ⟨frontierCount, _, _, _, _, _, _, _, _, _, hfrontierLength, _, _, _⟩
  obtain ⟨frontier, hcount, hbytes⟩ :=
    reify_frontier_blocks opening.frontier.val frontierCount hfrontierLength
  exact ⟨frontierCount, frontier, hfrontierLength, hcount, hbytes⟩

/-- Direct specialization from a successful unchanged parser call. -/
theorem successful_parser_frontier_blocks
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (hrun : aspis_core.state_only_private_openings.parse_private_opening_from_proof
      proofBytes expectedCount valueWidth = .ok (.Ok (opening, remainder))) :
    ∃ frontierCount : Nat, ∃ frontier : List Digest32,
      opening.frontier.val.length = frontierCount * 32 ∧
      frontier.length = frontierCount ∧
      frontier.flatMap digestBytes =
        opening.frontier.val.map generatedU8ToByte := by
  exact exact_raw_parser_frontier_blocks proofBytes expectedCount valueWidth
    opening remainder
    (parse_private_opening_success_exact proofBytes expectedCount valueWidth
      opening remainder hrun)

#print axioms reify_frontier_blocks
#print axioms frontier_digest_slice_exact
#print axioms reified_frontier_digest_slice_exact
#print axioms reified_frontier_byte_exact
#print axioms exact_raw_parser_frontier_blocks
#print axioms successful_parser_frontier_blocks

end AspisV5MerkleUnchangedFullFrontierChunks
