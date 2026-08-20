import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFull.Funs

/-! Exact fields returned by the unchanged full-extraction topology matcher. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullMatchedSuffixShape

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull

/-- The successful matcher does not manufacture a different topology or
parameter set: every field used by the following hash loop is the literal
input field. -/
def ExactMatchedSuffixShape
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix) : Prop :=
  matched = {
    topology := topology
    radix_level := radixLevel
    binary_depth := binaryDepth
    expected_len := Slice.len indices
  }

theorem matched_suffix_success_shape
    (topology : aspis_core.merkle.Radix4BinaryCapTopology)
    (radixLevel : Std.Usize) (binaryDepth : Std.U32)
    (indices : Slice Std.U32)
    (matched : aspis_core.merkle.MatchedRadix4BinaryCapSuffix)
    (hmatch : aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix topology
      radixLevel binaryDepth indices = .ok (some matched)) :
    ExactMatchedSuffixShape topology radixLevel binaryDepth indices matched := by
  unfold aspis_core.merkle.Radix4BinaryCapTopology.matched_suffix at hmatch
  simp only [lift, Aeneas.Std.bind_tc_ok] at hmatch
  split at hmatch
  next hlevel =>
    generalize hdepth :
      core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU32
        (U32.checked_sub topology.binary_depth
          (Std.U32.wrapping_mul (UScalar.cast .U32 radixLevel) 2#u32))
        (some binaryDepth) = depthResult at hmatch
    cases depthResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
    | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
    | ok equalDepth =>
      simp only [Aeneas.Std.bind_tc_ok] at hmatch
      by_cases hdepthTrue : equalDepth = true
      · rw [hdepthTrue] at hmatch
        generalize hindices :
          aspis_core.merkle.Radix4BinaryCapTopology.impl.level_indices topology
            radixLevel = indicesResult at hmatch
        cases indicesResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
        | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
        | ok maybeIndices =>
          simp only [Aeneas.Std.bind_tc_ok] at hmatch
          generalize hequal :
            core.option.Option.Insts.CoreCmpPartialEqOption.eq
              (core.cmp.PartialEqShared
                (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU32))
              maybeIndices (some indices) = equalResult at hmatch
          cases equalResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hmatch
          | div => simp [Bind.bind, Aeneas.Std.bind] at hmatch
          | ok equalIndices =>
            simp only [Aeneas.Std.bind_tc_ok] at hmatch
            by_cases hequalTrue : equalIndices = true
            · rw [hequalTrue] at hmatch
              simp at hmatch
              subst matched
              rfl
            · have hequalFalse : equalIndices = false :=
                Bool.eq_false_of_not_eq_true hequalTrue
              rw [hequalFalse] at hmatch
              simp at hmatch
      · have hdepthFalse : equalDepth = false :=
          Bool.eq_false_of_not_eq_true hdepthTrue
        rw [hdepthFalse] at hmatch
        simp at hmatch
  next hlevel => simp at hmatch

#print axioms matched_suffix_success_shape

end AspisV5MerkleUnchangedFullMatchedSuffixShape
