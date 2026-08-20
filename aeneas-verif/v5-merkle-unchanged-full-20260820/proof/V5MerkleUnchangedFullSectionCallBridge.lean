import V5MerkleUnchangedFullSectionNodeClosure
import V5MerkleUnchangedFullParserBounds

/-! One successful exact generated helper call yields the maintained accepted
section, including the literal returned remainder. -/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace AspisV5MerkleUnchangedFullSectionCallBridge

open V5MerkleUnchangedFull
open V5MerkleUnchangedCompat

variable [HashContext]

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleUnchangedFullParserBridge
open AspisV5MerkleUnchangedFullParserBounds
open AspisV5MerkleUnchangedFullRadixSoundness
open AspisV5MerkleUnchangedFullHelperSoundness
open AspisV5MerkleUnchangedFullConstructorSemantics
open AspisV5MerkleUnchangedFullSectionTopologyAlignment
open AspisV5MerkleUnchangedFullSectionBase
open AspisV5MerkleUnchangedFullReleasedLevelSources
open AspisV5MerkleUnchangedFullReleasedBinaryCap
open AspisV5MerkleUnchangedFullSectionNodeClosure
open AspisV5MerkleUnchangedFullWireTable

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev GeneratedOpening :=
  aspis_core.state_only_private_openings.StateOnlyPrivateOpening
abbrev ModelByte := AspisV5MerkleAuthenticationBinding.Byte

/-- The callback premise already used for leaves also discharges the replay
adapter's result-shaped hash premise.  This is one boundary, not two. -/
theorem hash_callback_implies_fixed_hashv
    (sha256 : List ModelByte → Digest32)
    (hhash : HashCallbackEqualsSha256 sha256 HashContext.hash) :
    FixedHashvEqualsSha256 sha256 := by
  intro inputs output hrun
  unfold V5MerkleUnchangedCompat.merkle.fixed_hashv at hrun
  have outputEq : HashContext.hash inputs = output := Result.ok.inj hrun
  subst output
  rw [← helper_digest_eq_radix_digest]
  calc
    AspisV5MerkleUnchangedFullHelperBridge.generatedArrayToDigest
          (HashContext.hash inputs) =
        sha256 ((inputs.val.flatMap fun input => input.val).map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte) :=
      hhash inputs
    _ = sha256 ((inputs.val.flatMap fun input => input.val).map
          AspisV5MerkleUnchangedFullRadixSoundness.generatedU8ToByte) := by
      congr 1

/-- A successful nonzero-width call cannot have taken the topology-mismatch
branch: the exact generated matcher returned one concrete suffix. -/
theorem released_helper_success_has_matched_suffix
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec)
    (hvalueWidth : valueWidth ≠ 0#usize)
    (hcountBound : ¬ Slice.len expectedIndices >
      UScalar.cast .Usize core.num.U16.MAX)
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        HashContext.hash root binaryDepth treeTag valueWidth expectedIndices
        proofBytes topology radixLevel level next =
          .ok (.Ok (opening, remainder), outputLevel, outputNext)) :
    ∃ matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix,
      aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix topology
        radixLevel binaryDepth expectedIndices = .ok (some matched) := by
  unfold
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
    at hrun
  generalize hmatched :
    aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth expectedIndices = matchedResult at hrun
  cases matchedResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok matchedOption =>
      simp only [Aeneas.Std.bind_tc_ok] at hrun
      cases matchedOption with
      | none =>
          rw [if_neg hvalueWidth] at hrun
          simp only [lift, Aeneas.Std.bind_tc_ok] at hrun
          rw [if_neg hcountBound] at hrun
          simp only [core.option.Option.is_none, if_pos rfl] at hrun
          generalize hvalidate :
            aspis_core.state_only_private_openings.validate_shape binaryDepth
              valueWidth expectedIndices = validateResult at hrun
          cases validateResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok validateInner =>
              simp only [Aeneas.Std.bind_tc_ok] at hrun
              cases validateInner with
              | Err error =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                    at hrun
              | Ok unit =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    Aeneas.Std.bind_tc_ok] at hrun
                  generalize hparse :
                    aspis_core.state_only_private_openings.parse_private_opening_from_proof
                      proofBytes (Slice.len expectedIndices) valueWidth =
                        parseResult at hrun
                  cases parseResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | ok parseInner =>
                      simp only [Aeneas.Std.bind_tc_ok] at hrun
                      cases parseInner with
                      | Err error =>
                          simp [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            at hrun
                      | Ok parsedPair =>
                          rcases parsedPair with ⟨parsedOpening, parsedRemainder⟩
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,
                            Aeneas.Std.bind_tc_ok] at hrun
                          generalize hclear :
                            alloc.vec.Vec.clear Global level = clearResult at hrun
                          cases clearResult with
                          | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | ok clearedLevel =>
                              simp only [Aeneas.Std.bind_tc_ok] at hrun
                              generalize hrecordWidth :
                                aspis_core.state_only_private_openings.StateOnlyPrivateOpening.record_width
                                  parsedOpening = recordWidthResult at hrun
                              cases recordWidthResult with
                              | fail error =>
                                  simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | div =>
                                  simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | ok recordWidth =>
                                  simp only [Aeneas.Std.bind_tc_ok] at hrun
                                  generalize hchunks :
                                    core.slice.Slice.chunks_exact
                                      parsedOpening.records recordWidth =
                                        chunksResult at hrun
                                  cases chunksResult with
                                  | fail error =>
                                      simp [Bind.bind, Aeneas.Std.bind] at hrun
                                  | div =>
                                      simp [Bind.bind, Aeneas.Std.bind] at hrun
                                  | ok recordIter =>
                                      simp only [Aeneas.Std.bind_tc_ok] at hrun
                                      generalize hleaf :
                                        aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop2
                                          recordIter HashContext.hash treeTag
                                          clearedLevel = leafResult at hrun
                                      cases leafResult <;>
                                        simp [Bind.bind, Aeneas.Std.bind] at hrun
      | some matched => exact ⟨matched, rfl⟩

private theorem ordered_active_indices_length_le_card
    (tree : V5PrivateSection) (queries : Finset V5Query) (level : Nat) :
    (orderedActiveIndices tree queries level).length ≤ queries.card := by
  unfold orderedActiveIndices activeIndices
  rw [Finset.length_sort]
  exact Finset.card_image_le

private theorem released_value_width_nonzero
    (tree : V5PrivateSection) (width : Std.Usize)
    (hwidth : width.val = valueWidth tree) : width ≠ 0#usize := by
  intro hzero
  have hval := congrArg UScalar.val hzero
  cases tree <;> norm_num [valueWidth] at hwidth hval <;> omega

private theorem released_index_count_bound
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (hcount : queries.card = 18) (indices : Slice Std.U32)
    (hindices : indices.val.map (fun index => index.val) =
      orderedActiveIndices tree queries 0) :
    ¬ Slice.len indices > UScalar.cast .Usize core.num.U16.MAX := by
  have hlength : indices.val.length ≤ 18 := by
    calc
      indices.val.length =
          (indices.val.map (fun index => index.val)).length := by simp
      _ = (orderedActiveIndices tree queries 0).length :=
        congrArg List.length hindices
      _ ≤ queries.card := ordered_active_indices_length_le_card tree queries 0
      _ = 18 := hcount
  intro htooLarge
  have htooLargeVal := (UScalar.lt_equiv _ _).mp htooLarge
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [Slice.len, core.num.U16.MAX, UScalar.cast_val_eq, U16.rMax,
      UScalarTy.Usize_numBits_eq, hbits] at htooLargeVal <;> omega

/-- Complete focused source theorem.  A successful exact generated helper
call, the released scalar/index identities, and the exact constructed
topology yield the maintained section trace with the same proof prefix and
literal returned remainder. -/
theorem generated_helper_success_yields_exact_acceptance
    (sha256 : List ModelByte → Digest32)
    (hhash : HashCallbackEqualsSha256 sha256 HashContext.hash)
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (queryCount : queries.card = 18)
    (root : GeneratedDigest) (binaryDepth : Std.U32) (treeTag : Std.U8)
    (valueWidth : Std.Usize) (expectedIndices : Slice Std.U32)
    (proofBytes : Slice Std.U8)
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (level next : GeneratedDigestVec)
    (opening : GeneratedOpening) (remainder : Slice Std.U8)
    (outputLevel outputNext : GeneratedDigestVec)
    (depthModel : binaryDepth.val =
      AspisV5MerkleAuthenticationBinding.binaryDepth tree)
    (tagModel : treeTag.val = (AspisV5MerkleAuthenticationBinding.treeTag tree).val)
    (widthModel : valueWidth.val = AspisV5MerkleAuthenticationBinding.valueWidth tree)
    (radixModel : radixLevel.val = sectionRadixStart tree)
    (indicesModel : expectedIndices.val.map (fun index => index.val) =
      orderedActiveIndices tree queries 0)
    (fields : FullExactConstructedTopologyFields queries topology)
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology
        HashContext.hash root binaryDepth treeTag valueWidth expectedIndices
        proofBytes topology radixLevel level next =
          .ok (.Ok (opening, remainder), outputLevel, outputNext)) :
    ExactStateOnlyTopologyHelperAcceptance sha256 {
      tree := tree
      root := AspisV5MerkleUnchangedFullRadixSoundness.generatedArrayToDigest root
      queries := queries
      proofBytes := proofBytes.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte
      remainder := remainder.val.map
        AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte } := by
  have hvalueWidth := released_value_width_nonzero tree valueWidth widthModel
  have hcountBound := released_index_count_bound tree queries queryCount
    expectedIndices indicesModel
  obtain ⟨matched, hmatched⟩ := released_helper_success_has_matched_suffix
    root binaryDepth treeTag valueWidth expectedIndices proofBytes topology
    radixLevel level next opening remainder outputLevel outputNext hvalueWidth
    hcountBound hrun
  let execution := Classical.choice
    (released_helper_success_yields_execution root binaryDepth treeTag
      valueWidth expectedIndices proofBytes topology radixLevel level next
      opening remainder outputLevel outputNext hvalueWidth hcountBound matched
      hmatched hrun)
  let raw := parse_private_opening_success_exact proofBytes
    (Slice.len expectedIndices) valueWidth opening remainder execution.parse_run
  have hqueries : queries.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hqueriesForBase := hqueries
  obtain ⟨query, hquery⟩ := hqueries
  have hactive : (activeIndices tree queries 0).Nonempty :=
    ⟨sectionIndex tree query, sectionIndex_mem_active tree hquery⟩
  have horderedPositive :
      0 < (orderedActiveIndices tree queries 0).length := by
    unfold orderedActiveIndices
    rw [Finset.length_sort]
    exact Finset.card_pos.mpr hactive
  have hindicesLength : expectedIndices.val.length =
      (orderedActiveIndices tree queries 0).length := by
    have := congrArg List.length indicesModel
    simpa using this
  have hexpectedPositive : 0 < (Slice.len expectedIndices).val := by
    rw [Slice.len_val]
    change 0 < expectedIndices.val.length
    rw [hindicesLength]
    exact horderedPositive
  have hwidthMinimum : 64 ≤ valueWidth.val := by
    rw [widthModel]
    cases tree <;> norm_num [AspisV5MerkleAuthenticationBinding.valueWidth]
  have hprefixRoom : 32 ≤
      2 + (Slice.len expectedIndices).val * (valueWidth.val + 32) + 4 := by
    rw [Slice.len_val]
    change 32 ≤ 2 + expectedIndices.val.length * (valueWidth.val + 32) + 4
    have hcountMinimum : 1 ≤ expectedIndices.val.length := by omega
    have hfactorMinimum : 96 ≤ valueWidth.val + 32 := by omega
    have hproductMinimum := Nat.mul_le_mul hcountMinimum hfactorMinimum
    norm_num at hproductMinimum
    omega
  have frontierRoom := raw_parser_frontier_has_digest_room proofBytes
    (Slice.len expectedIndices) valueWidth opening remainder raw hprefixRoom
  have fixedHash := hash_callback_implies_fixed_hashv sha256 hhash
  let trace := Classical.choice
    (released_helper_success_yields_full_exact_trace sha256 fixedHash hhash
      root binaryDepth treeTag valueWidth expectedIndices proofBytes topology
      radixLevel level next opening remainder outputLevel outputNext
      hvalueWidth hcountBound frontierRoom matched hmatched hrun)
  let baseSplit := Classical.choice
    (released_helper_yields_exact_section_base_with_split trace tree queries
      tagModel widthModel indicesModel hqueriesForBase)
  let base := baseSplit.toExactSectionGeneratedBaseData
  let sources := Classical.choice
    (released_helper_yields_exact_level_sources trace tree queries radixModel
      fields)
  let binary := Classical.choice
    (released_helper_yields_exact_binary_cap trace tree queries base sources
      depthModel fields)
  let sectionData := Classical.choice
    (released_helper_yields_exact_section_trace_data trace tree queries base
      sources binary fields)
  refine ⟨sectionData.trace, ?_⟩
  calc
    proofBytes.val.map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte =
        baseSplit.wire ++ remainder.val.map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte :=
      baseSplit.generated_proof_split
    _ = sectionData.trace.wire ++ remainder.val.map
          AspisV5MerkleUnchangedFullHelperBridge.generatedU8ToByte := by
      rw [sectionData.wire_eq_base]

#print axioms hash_callback_implies_fixed_hashv
#print axioms released_helper_success_has_matched_suffix
#print axioms generated_helper_success_yields_exact_acceptance

end AspisV5MerkleUnchangedFullSectionCallBridge
