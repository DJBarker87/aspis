import V5MerkleGeneratedParserBridge
import V5MerkleGeneratedLeafBridge
import V5MerkleGeneratedRadixBridge
import V5MerkleGeneratedTopologyBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedHelperSoundness

open V5MerkleDeployedSource
open AspisV5MerkleGeneratedParserBridge
open AspisV5MerkleGeneratedLeafBridge
open AspisV5MerkleGeneratedRadixBridge
open AspisV5MerkleGeneratedTopologyBridge
open AspisV5MerkleGeneratedHelperBridge
open AspisV5MerkleRustBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev GeneratedOpening :=
  state_only_private_openings.StateOnlyPrivateOpening

/-- Exact successful calls made by the released, nonzero-width branch of
`verify_state_only_private_opening_from_proof_with_topology`. -/
structure GeneratedReleasedHelperExecution
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec) where
  matched : merkle.MatchedRadix4BinaryCapSuffix
  clearedLevel : GeneratedDigestVec
  recordWidth : Std.Usize
  recordIter : core.slice.iter.ChunksExact Std.U8
  leafLevel : GeneratedDigestVec
  matched_run : merkle.Radix4BinaryCapTopology.matched_suffix topology
    radixLevel binaryDepth expectedIndices = .ok (some matched)
  parse_run : state_only_private_openings.parse_private_opening_from_proof
    proofBytes (Slice.len expectedIndices) valueWidth =
      .ok (.Ok (opening, remainder))
  clear_run : alloc.vec.Vec.clear Global level = .ok clearedLevel
  record_width_run :
    state_only_private_openings.StateOnlyPrivateOpening.record_width opening =
      .ok recordWidth
  chunks_run : core.slice.Slice.chunks_exact opening.records recordWidth =
    .ok recordIter
  leaf_loop_run :
    state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop3
      recordIter treeTag clearedLevel = .ok leafLevel
  merkle_run : merkle.verify_radix4_binary_cap_with_matched_topology root
    opening.frontier matched leafLevel next =
      .ok (true, outputLevel, outputNext)

/-- Successful production execution in the released branch exposes the
literal parser, record hashing, and Merkle calls above. -/
theorem released_helper_success_yields_execution
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec)
    (hvalueWidth : valueWidth ≠ 0#usize)
    (hcountBound : ¬ Slice.len expectedIndices >
      UScalar.cast .Usize core.num.U16.MAX)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hmatched : merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth expectedIndices = .ok (some matched))
    (hrun :
      state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        root binaryDepth treeTag valueWidth expectedIndices proofBytes
        topology radixLevel level next =
          .ok (.Ok (opening, remainder), outputLevel, outputNext)) :
    Nonempty (GeneratedReleasedHelperExecution root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext) := by
  unfold state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology at hrun
  rw [hmatched] at hrun
  simp only [Aeneas.Std.bind_tc_ok] at hrun
  rw [if_neg hvalueWidth] at hrun
  simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
  rw [if_neg hcountBound] at hrun
  simp only [core.option.Option.is_none, Bool.false_eq_true, if_false] at hrun
  generalize hparse :
    state_only_private_openings.parse_private_opening_from_proof proofBytes
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
          state_only_private_openings.StateOnlyPrivateOpening.record_width
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
              state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop3
                recordIter treeTag clearedLevel = leafResult at hrun
            cases leafResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok leafLevel =>
              simp only [Aeneas.Std.bind_tc_ok] at hrun
              generalize hmerkle :
                merkle.verify_radix4_binary_cap_with_matched_topology root
                  parsedOpening.frontier matched leafLevel next =
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

/-- The complete concrete evidence recovered from one released helper
acceptance: parser slices, every leaf hash, recursive radix execution, exact
cap child locations, and the root equation. -/
structure GeneratedReleasedHelperSoundnessTrace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec) where
  execution : GeneratedReleasedHelperExecution root binaryDepth treeTag
    valueWidth expectedIndices proofBytes topology radixLevel level next
    opening remainder outputLevel outputNext
  parser : ExactRawParserOutput proofBytes (Slice.len expectedIndices)
    valueWidth opening remainder
  leaves : GeneratedLeafTrace sha256 treeTag execution.recordIter
    execution.clearedLevel execution.leafLevel
  initialLevel : GeneratedDigestVec
  initialNext : GeneratedDigestVec
  finalLevel : GeneratedDigestVec
  finalNext : GeneratedDigestVec
  finalNodePos : Std.Usize
  finalIndices : Slice Std.U32
  clone_level_run : alloc.vec.CloneVec.clone
      (core.clone.CloneArray 32#usize core.clone.CloneU8) execution.leafLevel =
    .ok initialLevel
  clone_next_run : alloc.vec.CloneVec.clone
      (core.clone.CloneArray 32#usize core.clone.CloneU8) next =
    .ok initialNext
  levels_run : merkle.fixed_hash_radix_levels execution.matched.topology
      opening.frontier execution.matched.radix_level 0#usize initialLevel
      initialNext = .ok (some (finalLevel, finalNext, finalNodePos))
  levels : GeneratedLevelTrace execution.matched.topology opening.frontier
    execution.matched.radix_level 0#usize initialLevel initialNext finalLevel
    finalNext finalNodePos
  indices_run : merkle.Radix4BinaryCapTopology.impl.level_indices
      execution.matched.topology execution.matched.topology.radix_levels =
    .ok (some finalIndices)
  cap : GeneratedOddCapWitness sha256 root opening.frontier finalIndices
    finalLevel finalNodePos

theorem released_helper_success_yields_soundness_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hhash : FixedHashvEqualsSha256 sha256)
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8) (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec)
    (hvalueWidth : valueWidth ≠ 0#usize)
    (hcountBound : ¬ Slice.len expectedIndices >
      UScalar.cast .Usize core.num.U16.MAX)
    (hodd : binaryDepth &&& 1#u32 ≠ 0#u32)
    (hfrontierRoom : opening.frontier.val.length + 32 < UScalar.size .Usize)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hmatched : merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth expectedIndices = .ok (some matched))
    (hrun :
      state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        root binaryDepth treeTag valueWidth expectedIndices proofBytes
        topology radixLevel level next =
          .ok (.Ok (opening, remainder), outputLevel, outputNext)) :
    Nonempty (GeneratedReleasedHelperSoundnessTrace sha256 root binaryDepth
      treeTag valueWidth expectedIndices proofBytes topology radixLevel level
      next opening remainder outputLevel outputNext) := by
  let execution := Classical.choice
    (released_helper_success_yields_execution root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext hvalueWidth hcountBound matched
      hmatched hrun)
  have hparser := parse_private_opening_success_exact proofBytes
    (Slice.len expectedIndices) valueWidth opening remainder
    execution.parse_run
  let leaves := Classical.choice
    (generated_loop3_success_yields_trace sha256 hhash execution.recordIter
      treeTag execution.clearedLevel execution.leafLevel
      execution.leaf_loop_run)
  have hmatchedShape :=
    matched_suffix_success_shape topology radixLevel binaryDepth
      expectedIndices execution.matched execution.matched_run
  have hoddExecution : execution.matched.binary_depth &&& 1#u32 ≠ 0#u32 := by
    rw [hmatchedShape]
    exact hodd
  obtain ⟨initialLevel, initialNext, finalLevel, finalNext, finalNodePos,
      finalIndices, hcloneLevel, hcloneNext, hlevels, hindices, hcapRun⟩ :=
    verify_radix4_binary_cap_odd_success_factors root opening.frontier
      execution.matched execution.leafLevel next outputLevel outputNext
      hoddExecution execution.merkle_run
  let levels := Classical.choice
    (fixed_hash_radix_levels_success_yields_trace execution.matched.topology
      opening.frontier execution.matched.radix_level 0#usize initialLevel
      initialNext finalLevel finalNext finalNodePos (by norm_num)
      hfrontierRoom hlevels)
  let cap := Classical.choice
    (generated_odd_binary_cap_success_has_witness sha256 hhash root
      opening.frontier finalIndices finalLevel finalNext finalNodePos
      outputLevel outputNext hcapRun)
  exact ⟨{
    execution := execution
    parser := hparser
    leaves := leaves
    initialLevel := initialLevel
    initialNext := initialNext
    finalLevel := finalLevel
    finalNext := finalNext
    finalNodePos := finalNodePos
    finalIndices := finalIndices
    clone_level_run := hcloneLevel
    clone_next_run := hcloneNext
    levels_run := hlevels
    levels := levels
    indices_run := hindices
    cap := cap }⟩

#print axioms released_helper_success_yields_execution
#print axioms released_helper_success_yields_soundness_trace

end AspisV5MerkleGeneratedHelperSoundness
