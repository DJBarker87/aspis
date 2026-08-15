import V5MerkleDeployedSource.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleGeneratedTopologyBridge

open V5MerkleDeployedSource

/-- Exact structure returned by a successful generated `matched_suffix`
call.  The theorem deliberately states only fields which are needed by the
subsequent hash execution; topology-array contents are handled separately. -/
def ExactMatchedSuffixShape
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix) : Prop :=
  matched = {
    topology := topology
    radix_level := radixLevel
    binary_depth := binaryDepth
    expected_len := Slice.len indices
  }

theorem matched_suffix_success_shape
    (topology : merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : merkle.MatchedRadix4BinaryCapSuffix)
    (hmatch : merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth indices = .ok (some matched)) :
    ExactMatchedSuffixShape topology radixLevel binaryDepth indices matched := by
  unfold merkle.Radix4BinaryCapTopology.matched_suffix at hmatch
  simp only [lift, Aeneas.Std.bind_tc_ok] at hmatch
  generalize hsub : U32.checked_sub topology.binary_depth
      (Std.U32.wrapping_mul (UScalar.cast .U32 radixLevel) 2#u32) =
    subResult at hmatch
  cases subResult with
  | none =>
    simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
      at hmatch
  | some remainingDepth =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      Aeneas.Std.bind_tc_ok] at hmatch
    generalize hindices :
      merkle.Radix4BinaryCapTopology.impl.level_indices topology radixLevel =
        indicesResult at hmatch
    cases indicesResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
    | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
    | ok maybeIndices =>
      simp only [Aeneas.Std.bind_tc_ok] at hmatch
      cases maybeIndices with
      | none =>
        simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
          at hmatch
      | some actualIndices =>
        simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          Aeneas.Std.bind_tc_ok] at hmatch
        by_cases hlevel : radixLevel ≤ topology.radix_levels
        · rw [if_pos hlevel] at hmatch
          by_cases hdepth : remainingDepth = binaryDepth
          · rw [if_pos hdepth] at hmatch
            generalize hequal :
              merkle.u32_slices_equal actualIndices indices 0#usize =
                equalResult at hmatch
            cases equalResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
            | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
            | ok equal =>
              simp only [Aeneas.Std.bind_tc_ok] at hmatch
              by_cases hequalTrue : equal = true
              · rw [hequalTrue] at hmatch
                simp at hmatch
                subst matched
                rfl
              · have hequalFalse : equal = false :=
                    Bool.eq_false_of_not_eq_true hequalTrue
                rw [hequalFalse] at hmatch
                simp at hmatch
          · rw [if_neg hdepth] at hmatch
            simp at hmatch
        · rw [if_neg hlevel] at hmatch
          simp at hmatch

#print axioms matched_suffix_success_shape

end AspisV5MerkleGeneratedTopologyBridge
