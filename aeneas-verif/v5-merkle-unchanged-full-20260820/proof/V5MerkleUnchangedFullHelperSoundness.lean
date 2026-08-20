import V5MerkleUnchangedFullParserBridge
import V5MerkleUnchangedFullLeafBridge
import V5MerkleUnchangedFullRadixSoundness

/-! Accepted-helper inversion and exact parser/leaf/radix traces over the
unchanged full extraction. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.unusedSimpArgs false

namespace AspisV5MerkleUnchangedFullHelperSoundness

open V5MerkleUnchangedFull
open AspisV5MerkleUnchangedFullParserBridge
open AspisV5MerkleUnchangedFullLeafBridge
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleRustBridge
open V5MerkleUnchangedCompat

variable [HashContext]

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev GeneratedOpening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening

/-- Exact successful calls made by the released, nonzero-width branch of
`verify_state_only_private_opening_from_proof_with_topology`. -/
structure GeneratedReleasedHelperExecution
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec) where
  matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix
  clearedLevel : GeneratedDigestVec
  recordWidth : Std.Usize
  recordIter : core.slice.iter.ChunksExact Std.U8
  leafLevel : GeneratedDigestVec
  matched_run : aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix topology
    radixLevel binaryDepth expectedIndices = .ok (some matched)
  parse_run : aspis_core.state_only_private_openings.parse_private_opening_from_proof
    proofBytes (Slice.len expectedIndices) valueWidth =
      .ok (.Ok (opening, remainder))
  clear_run : alloc.vec.Vec.clear Global level = .ok clearedLevel
  record_width_run :
    aspis_core.state_only_private_openings.StateOnlyPrivateOpening.record_width opening =
      .ok recordWidth
  chunks_run : core.slice.Slice.chunks_exact opening.records recordWidth =
    .ok recordIter
  leaf_loop_run :
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop3
      recordIter HashContext.hash treeTag clearedLevel = .ok leafLevel
  merkle_run : aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology
    HashContext.hash root opening.frontier matched leafLevel next =
      .ok (true, outputLevel, outputNext)

/-- Successful production execution in the released branch exposes the
literal parser, record hashing, and Merkle calls above. -/
theorem released_helper_success_yields_execution
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec)
    (hvalueWidth : valueWidth ≠ 0#usize)
    (hcountBound : ¬ Slice.len expectedIndices >
      UScalar.cast .Usize core.num.U16.MAX)
    (matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix)
    (hmatched : aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth expectedIndices = .ok (some matched))
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        HashContext.hash root binaryDepth treeTag valueWidth expectedIndices proofBytes
        topology radixLevel level next =
          .ok (.Ok (opening, remainder), outputLevel, outputNext)) :
    Nonempty (GeneratedReleasedHelperExecution root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext) := by
  unfold aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology at hrun
  rw [hmatched] at hrun
  simp only [Aeneas.Std.bind_tc_ok] at hrun
  rw [if_neg hvalueWidth] at hrun
  simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
  rw [if_neg hcountBound] at hrun
  simp only [core.option.Option.is_none, Bool.false_eq_true, if_false] at hrun
  generalize hparse :
    aspis_core.state_only_private_openings.parse_private_opening_from_proof proofBytes
      (Slice.len expectedIndices) valueWidth = parseResult at hrun
  cases parseResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok parsed =>
    simp only [Aeneas.Std.bind_tc_ok] at hrun
    cases parsed with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        at hrun
    | Ok parsedPair =>
      rcases parsedPair with ⟨parsedOpening, parsedRemainder⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        Aeneas.Std.bind_tc_ok] at hrun
      generalize hclear : alloc.vec.Vec.clear Global level = clearResult at hrun
      cases clearResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok clearedLevel =>
        simp only [Aeneas.Std.bind_tc_ok] at hrun
        generalize hrecordWidth :
          aspis_core.state_only_private_openings.StateOnlyPrivateOpening.record_width
            parsedOpening = recordWidthResult at hrun
        cases recordWidthResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok recordWidth =>
          simp only [Aeneas.Std.bind_tc_ok] at hrun
          generalize hchunks :
            core.slice.Slice.chunks_exact parsedOpening.records recordWidth =
              chunksResult at hrun
          cases chunksResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok recordIter =>
            simp only [Aeneas.Std.bind_tc_ok] at hrun
            generalize hleaf :
              aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop3
                recordIter HashContext.hash treeTag clearedLevel = leafResult at hrun
            cases leafResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok leafLevel =>
              simp only [Aeneas.Std.bind_tc_ok] at hrun
              generalize hmerkle :
                aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology
                  HashContext.hash root parsedOpening.frontier matched leafLevel next =
                    merkleResult at hrun
              cases merkleResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok merkleOutput =>
                rcases merkleOutput with ⟨accepted, finalLevel, finalNext⟩
                simp only [Aeneas.Std.bind_tc_ok] at hrun
                by_cases haccepted : accepted = true
                · rw [haccepted] at hrun
                  simp at hrun
                  rcases hrun with ⟨hopening, hremainder, hlevel, hnext⟩
                  subst parsedOpening
                  subst parsedRemainder
                  subst finalLevel
                  subst finalNext
                  exact ⟨{
                    matched := matched
                    clearedLevel := clearedLevel
                    recordWidth := recordWidth
                    recordIter := recordIter
                    leafLevel := leafLevel
                    matched_run := hmatched
                    parse_run := hparse
                    clear_run := hclear
                    record_width_run := hrecordWidth
                    chunks_run := hchunks
                    leaf_loop_run := hleaf
                    merkle_run := by simpa [haccepted] using hmerkle }⟩
                · have hacceptedFalse : accepted = false :=
                    Bool.eq_false_of_not_eq_true haccepted
                  rw [hacceptedFalse] at hrun
                  simp at hrun

/-- Every successful released-branch helper call exposes the exact parser,
record-hash, and unchanged nested-radix traces in one namespace. -/
structure FullExactReleasedHelperTrace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec) where
  execution : GeneratedReleasedHelperExecution root binaryDepth treeTag
    valueWidth expectedIndices proofBytes topology radixLevel level next
    opening remainder outputLevel outputNext
  parser : ExactRawParserOutput proofBytes (Slice.len expectedIndices)
    valueWidth opening remainder
  leaves : GeneratedLeafTrace sha256 HashContext.hash treeTag execution.recordIter
    execution.clearedLevel execution.leafLevel
  radix : RawLevelTrace sha256 root opening.frontier
    execution.matched.topology execution.matched.binary_depth
    { start := execution.matched.radix_level,
      «end» := execution.matched.topology.radix_levels }
    execution.leafLevel next 0#usize none outputLevel outputNext

theorem released_helper_success_yields_full_exact_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash : AspisV5MerkleUnchangedFullRadixSoundness.FixedHashvEqualsSha256
      sha256)
    (hleafHash : HashCallbackEqualsSha256 sha256 HashContext.hash)
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec)
    (hvalueWidth : valueWidth ≠ 0#usize)
    (hcountBound : ¬ Slice.len expectedIndices >
      UScalar.cast .Usize core.num.U16.MAX)
    (hfrontierRoom : opening.frontier.val.length + 32 < UScalar.size .Usize)
    (matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix)
    (hmatched : aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth expectedIndices = .ok (some matched))
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        HashContext.hash root binaryDepth treeTag valueWidth expectedIndices proofBytes
        topology radixLevel level next =
          .ok (.Ok (opening, remainder), outputLevel, outputNext)) :
    Nonempty (FullExactReleasedHelperTrace sha256 root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext) := by
  let execution := Classical.choice
    (released_helper_success_yields_execution root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext hvalueWidth hcountBound matched
      hmatched hrun)
  let parser := parse_private_opening_success_exact proofBytes
    (Slice.len expectedIndices) valueWidth opening remainder
    execution.parse_run
  let leaves := Classical.choice
    (generated_loop3_success_yields_trace sha256 HashContext.hash hleafHash
      execution.recordIter treeTag execution.clearedLevel execution.leafLevel
      execution.leaf_loop_run)
  let radix := Classical.choice
    (accepted_unchanged_radix_yields_full_trace sha256 hhash root
      opening.frontier execution.matched execution.leafLevel next outputLevel
      outputNext hfrontierRoom execution.merkle_run)
  exact ⟨{ execution, parser, leaves, radix }⟩

#print axioms released_helper_success_yields_execution
#print axioms released_helper_success_yields_full_exact_trace

end AspisV5MerkleUnchangedFullHelperSoundness
