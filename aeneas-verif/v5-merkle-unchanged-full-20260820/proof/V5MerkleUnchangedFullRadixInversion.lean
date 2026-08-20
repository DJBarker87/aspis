import V5MerkleUnchangedFull.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullRadixInversion

open V5MerkleUnchangedFull

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest
abbrev GeneratedHash :=
  Slice (Slice Std.U8) → Array Std.U8 32#usize

/-- Everything the unchanged generated verifier must have done before it can
return `true`.  Unused fixed-array entries are intentionally not observed. -/
structure AcceptedRadixExecution
    (hash : GeneratedHash) (root : GeneratedDigest)
    (nodeBytes : Slice Std.U8)
    (matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix)
    (level next outputLevel outputNext : GeneratedDigestVec) : Prop where
  level_nonempty_run :
    alloc.vec.Vec.is_empty Global level = .ok false
  frontier_aligned :
    (Slice.len nodeBytes &&& 31#usize) = 0#usize
  level_count_matches :
    alloc.vec.Vec.len level = matched.expected_len
  loop_run :
    aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology_loop0
      {
        start := matched.radix_level
        «end» := matched.topology.radix_levels
      }
      hash root nodeBytes matched.topology.binary_depth
      matched.topology.radix_levels matched.topology.level_indices
      matched.topology.level_offsets matched.topology.group_masks
      matched.topology.group_offsets matched.binary_depth level next
      0#usize none = .ok (outputLevel, outputNext, some true)

/-- Exact inversion of the accepted-result interface generated from the
unchanged Rust function. -/
theorem accepted_radix_execution
    (hash : GeneratedHash) (root : GeneratedDigest)
    (nodeBytes : Slice Std.U8)
    (matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix)
    (level next outputLevel outputNext : GeneratedDigestVec)
    (hrun :
      aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology
        hash root nodeBytes matched level next =
          .ok (true, outputLevel, outputNext)) :
    AcceptedRadixExecution hash root nodeBytes matched level next
      outputLevel outputNext := by
  unfold aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology at hrun
  generalize hempty : alloc.vec.Vec.is_empty Global level = emptyResult at hrun
  cases emptyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok isEmpty =>
    simp only [Aeneas.Std.bind_tc_ok] at hrun
    by_cases hisEmpty : isEmpty = true
    · rw [hisEmpty] at hrun
      simp at hrun
    · have hisEmptyFalse : isEmpty = false :=
        Bool.eq_false_of_not_eq_true hisEmpty
      rw [hisEmptyFalse] at hrun
      simp only [Bool.false_eq_true, if_false, lift,
        Aeneas.Std.bind_tc_ok] at hrun
      by_cases haligned :
          (Slice.len nodeBytes &&& 31#usize) = 0#usize
      · have hnotMisaligned :
            ((Slice.len nodeBytes &&& 31#usize) != 0#usize) = false := by
          simp [haligned]
        rw [hnotMisaligned] at hrun
        simp only [Bool.false_eq_true, if_false] at hrun
        by_cases hlength :
            alloc.vec.Vec.len level = matched.expected_len
        · have hnotWrongLength :
              (alloc.vec.Vec.len level != matched.expected_len) = false := by
            simp [hlength]
          rw [hnotWrongLength] at hrun
          simp only [Bool.false_eq_true, if_false] at hrun
          generalize hloop :
            aspis_core.merkle.verify_radix4_binary_cap_with_matched_topology_loop0
              {
                start := matched.radix_level
                «end» := matched.topology.radix_levels
              }
              hash root nodeBytes matched.topology.binary_depth
              matched.topology.radix_levels matched.topology.level_indices
              matched.topology.level_offsets matched.topology.group_masks
              matched.topology.group_offsets matched.binary_depth level next
              0#usize none = loopResult at hrun
          cases loopResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok loopOutput =>
            rcases loopOutput with ⟨finalLevel, finalNext, pendingReturn⟩
            simp only [Aeneas.Std.bind_tc_ok] at hrun
            cases pendingReturn with
            | none => simp at hrun
            | some accepted =>
              simp only at hrun
              have htuple :
                  (accepted, finalLevel, finalNext) =
                    (true, outputLevel, outputNext) :=
                Result.ok.inj hrun
              have haccepted : accepted = true := by
                exact congrArg Prod.fst htuple
              have houtputs :
                  (finalLevel, finalNext) = (outputLevel, outputNext) :=
                congrArg Prod.snd htuple
              have hlevel : finalLevel = outputLevel :=
                congrArg Prod.fst houtputs
              have hnext : finalNext = outputNext :=
                congrArg Prod.snd houtputs
              subst finalLevel
              subst finalNext
              exact {
                level_nonempty_run := by simpa [hisEmptyFalse] using hempty
                frontier_aligned := haligned
                level_count_matches := hlength
                loop_run := by simpa [haccepted] using hloop
              }
        · have hwrongLength :
              (alloc.vec.Vec.len level != matched.expected_len) = true := by
            simp [hlength]
          rw [hwrongLength] at hrun
          simp at hrun
      · have hmisaligned :
            ((Slice.len nodeBytes &&& 31#usize) != 0#usize) = true := by
          simp [haligned]
        rw [hmisaligned] at hrun
        simp at hrun

#print axioms accepted_radix_execution

end AspisV5MerkleUnchangedFullRadixInversion
