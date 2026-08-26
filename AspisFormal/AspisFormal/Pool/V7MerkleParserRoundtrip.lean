import AspisFormal.Pool.V7MerkleQueryExtractor

/-!
# Exact byte round trips for the Tag-73 K1.2 parser

The query-graph extractor may interpret a raw SHA input as a C1 leaf, C2 leaf,
or internal node only through `parseTypedPreimage`.  This module proves both
directions of the exact deployed grammar: serializing a typed value parses to
that value, and every successful parse serializes back to the original raw
input.  The latter rules out a lossy-parser gap in subsequent causal graph and
source-bridge proofs.
-/

set_option autoImplicit false

namespace AspisPool.V7MerkleParserRoundtrip

open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor

theorem parse_serialize_typed_preimage (typed : TypedPreimage) :
    parseTypedPreimage (serialize typed) = some typed := by
  cases typed with
  | c1Leaf value salt =>
      simp [parseTypedPreimage, serialize]
  | c2Leaf value salt =>
      simp [parseTypedPreimage, serialize]
  | node left right =>
      simp [parseTypedPreimage, serialize]

private theorem rebuild_c1_branch
    (input : RawHashInput)
    (lengthExact : input.length = 437)
    (tagExact : input.take 2 = [0x10, 0x71]) :
    serialize (.c1Leaf
        (fixedOfListD ((input.drop 2).take 403))
        (fixedOfListD ((input.drop 2).drop 403))) = input := by
  have tailLength : (input.drop 2).length = 435 := by
    rw [List.length_drop, lengthExact]
  have valueLength : ((input.drop 2).take 403).length = 403 := by
    rw [List.length_take, tailLength]
    norm_num
  have saltLength : ((input.drop 2).drop 403).length = 32 := by
    rw [List.length_drop, tailLength]
  rw [serialize,
    fixedBytes_fixedOfListD_of_length _ valueLength,
    fixedBytes_fixedOfListD_of_length _ saltLength]
  change [0x10, 0x71] ++ (input.drop 2).take 403 ++
      (input.drop 2).drop 403 = input
  calc
    [0x10, 0x71] ++ (input.drop 2).take 403 ++
        (input.drop 2).drop 403 =
      input.take 2 ++
        ((input.drop 2).take 403 ++ (input.drop 2).drop 403) := by
          rw [tagExact]
          simp
    _ = input.take 2 ++ input.drop 2 := by
      rw [List.take_append_drop]
    _ = input := List.take_append_drop 2 input

private theorem rebuild_c2_branch
    (input : RawHashInput)
    (lengthExact : input.length = 220)
    (tagExact : input.take 2 = [0x10, 0xf1]) :
    serialize (.c2Leaf
        (fixedOfListD ((input.drop 2).take 186))
        (fixedOfListD ((input.drop 2).drop 186))) = input := by
  have tailLength : (input.drop 2).length = 218 := by
    rw [List.length_drop, lengthExact]
  have valueLength : ((input.drop 2).take 186).length = 186 := by
    rw [List.length_take, tailLength]
    norm_num
  have saltLength : ((input.drop 2).drop 186).length = 32 := by
    rw [List.length_drop, tailLength]
  rw [serialize,
    fixedBytes_fixedOfListD_of_length _ valueLength,
    fixedBytes_fixedOfListD_of_length _ saltLength]
  change [0x10, 0xf1] ++ (input.drop 2).take 186 ++
      (input.drop 2).drop 186 = input
  calc
    [0x10, 0xf1] ++ (input.drop 2).take 186 ++
        (input.drop 2).drop 186 =
      input.take 2 ++
        ((input.drop 2).take 186 ++ (input.drop 2).drop 186) := by
          rw [tagExact]
          simp
    _ = input.take 2 ++ input.drop 2 := by
      rw [List.take_append_drop]
    _ = input := List.take_append_drop 2 input

private theorem rebuild_node_branch
    (input : RawHashInput)
    (lengthExact : input.length = 53)
    (tagExact : input.take 1 = [0x11]) :
    serialize (.node
        (fixedOfListD ((input.drop 1).take 26))
        (fixedOfListD ((input.drop 1).drop 26))) = input := by
  have tailLength : (input.drop 1).length = 52 := by
    rw [List.length_drop, lengthExact]
  have leftLength : ((input.drop 1).take 26).length = 26 := by
    rw [List.length_take, tailLength]
    norm_num
  have rightLength : ((input.drop 1).drop 26).length = 26 := by
    rw [List.length_drop, tailLength]
  rw [serialize,
    fixedBytes_fixedOfListD_of_length _ leftLength,
    fixedBytes_fixedOfListD_of_length _ rightLength]
  change [0x11] ++ (input.drop 1).take 26 ++
      (input.drop 1).drop 26 = input
  calc
    [0x11] ++ (input.drop 1).take 26 ++ (input.drop 1).drop 26 =
      input.take 1 ++
        ((input.drop 1).take 26 ++ (input.drop 1).drop 26) := by
          rw [tagExact]
          simp
    _ = input.take 1 ++ input.drop 1 := by
      rw [List.take_append_drop]
    _ = input := List.take_append_drop 1 input

theorem serialize_parse_typed_preimage
    (input : RawHashInput) (typed : TypedPreimage)
    (parsed : parseTypedPreimage input = some typed) :
    serialize typed = input := by
  unfold parseTypedPreimage at parsed
  split at parsed
  · rename_i c1Guard
    rcases c1Guard with ⟨lengthExact, tagExact⟩
    simp only [Option.some.injEq] at parsed
    subst typed
    exact rebuild_c1_branch input lengthExact tagExact
  · split at parsed
    · rename_i c2Guard
      rcases c2Guard with ⟨lengthExact, tagExact⟩
      simp only [Option.some.injEq] at parsed
      subst typed
      exact rebuild_c2_branch input lengthExact tagExact
    · split at parsed
      · rename_i nodeGuard
        rcases nodeGuard with ⟨lengthExact, tagExact⟩
        simp only [Option.some.injEq] at parsed
        subst typed
        exact rebuild_node_branch input lengthExact tagExact
      · simp at parsed

theorem parse_typed_preimage_eq_some_iff (input : RawHashInput)
    (typed : TypedPreimage) :
    parseTypedPreimage input = some typed ↔ serialize typed = input := by
  constructor
  · exact serialize_parse_typed_preimage input typed
  · intro serialized
    rw [← serialized]
    exact parse_serialize_typed_preimage typed

#print axioms parse_serialize_typed_preimage
#print axioms serialize_parse_typed_preimage
#print axioms parse_typed_preimage_eq_some_iff

end AspisPool.V7MerkleParserRoundtrip
