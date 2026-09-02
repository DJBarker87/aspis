import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# Injectivity of deployed Tag-73 squeeze-pair inputs

Every Tag-73 squeeze state `S` names two SHA-256 inputs, `S || 0x01` and
`S || 0x02`.  This leaf proves the exact deterministic facts needed to turn
reuse of either concrete input into equality of the underlying checkpoint
states:

* equal output-half inputs have equal states;
* equal advance-half inputs have equal states; and
* inputs from opposite halves are disjoint even when their states differ.

These are serialization facts only.  They contain no random-oracle,
target-cleanliness, restoration, acceptance, or extraction assumption.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SqueezeInputStateInjectivity

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement

/-! ## The fixed-width state serialization is injective -/

theorem digest_bytes_injective : Function.Injective (@bytes 32) := by
  intro first second equal
  exact List.ofFn_injective equal

theorem output_input_eq_implies_state_eq
    (first second : Digest256)
    (equal : bytes first ++ [domSqueeze] =
      bytes second ++ [domSqueeze]) :
    first = second := by
  apply digest_bytes_injective
  exact (List.append_left_inj [domSqueeze]).mp equal

theorem advance_input_eq_implies_state_eq
    (first second : Digest256)
    (equal : bytes first ++ [domAdvance] =
      bytes second ++ [domAdvance]) :
    first = second := by
  apply digest_bytes_injective
  exact (List.append_left_inj [domAdvance]).mp equal

theorem output_input_eq_iff_state_eq (first second : Digest256) :
    bytes first ++ [domSqueeze] = bytes second ++ [domSqueeze] ↔
      first = second := by
  constructor
  · exact output_input_eq_implies_state_eq first second
  · intro equal
    subst second
    rfl

theorem advance_input_eq_iff_state_eq (first second : Digest256) :
    bytes first ++ [domAdvance] = bytes second ++ [domAdvance] ↔
      first = second := by
  constructor
  · exact advance_input_eq_implies_state_eq first second
  · intro equal
    subst second
    rfl

/-! ## The two tagged input grammars are globally disjoint -/

theorem output_input_ne_advance_input
    (outputState advanceState : Digest256) :
    bytes outputState ++ [domSqueeze] ≠
      bytes advanceState ++ [domAdvance] := by
  intro equal
  have lastEqual := congrArg List.getLast? equal
  simpa [domSqueeze, domAdvance] using lastEqual

theorem advance_input_ne_output_input
    (advanceState outputState : Digest256) :
    bytes advanceState ++ [domAdvance] ≠
      bytes outputState ++ [domSqueeze] := by
  exact (output_input_ne_advance_input outputState advanceState).symm

/-! ## Fixed state prefixes with non-singleton suffixes are not duplex inputs -/

/-- Any input consisting of one serialized digest followed by a suffix whose
length is not one cannot be a deployed output-half input.  This is the base
case needed when backwards transcript induction reaches an absorption
boundary on one side while the other side still claims another duplex block. -/
theorem digest_suffix_ne_output_input_of_length_ne_one
    (boundaryState outputState : Digest256) (suffix : ByteString)
    (suffixLength : suffix.length ≠ 1) :
    bytes boundaryState ++ suffix ≠ bytes outputState ++ [domSqueeze] := by
  intro equal
  have lengths := congrArg List.length equal
  simp only [List.length_append, bytes_length, List.length_singleton] at lengths
  exact suffixLength (Nat.add_left_cancel lengths)

/-- The analogous separation from an advance-half input. -/
theorem digest_suffix_ne_advance_input_of_length_ne_one
    (boundaryState advanceState : Digest256) (suffix : ByteString)
    (suffixLength : suffix.length ≠ 1) :
    bytes boundaryState ++ suffix ≠ bytes advanceState ++ [domAdvance] := by
  intro equal
  have lengths := congrArg List.length equal
  simp only [List.length_append, bytes_length, List.length_singleton] at lengths
  exact suffixLength (Nat.add_left_cancel lengths)

/-! ## Classification of an overlap with one earlier pair -/

theorem output_input_overlap_classification
    (currentState earlierState : Digest256)
    (earlierInput : ByteString)
    (earlierIsPair :
      earlierInput = bytes earlierState ++ [domSqueeze] ∨
        earlierInput = bytes earlierState ++ [domAdvance])
    (overlap : earlierInput = bytes currentState ++ [domSqueeze]) :
    earlierState = currentState := by
  rcases earlierIsPair with outputHalf | advanceHalf
  · exact output_input_eq_implies_state_eq earlierState currentState
      (outputHalf.symm.trans overlap)
  · exact (advance_input_ne_output_input earlierState currentState
      (advanceHalf.symm.trans overlap)).elim

theorem advance_input_overlap_classification
    (currentState earlierState : Digest256)
    (earlierInput : ByteString)
    (earlierIsPair :
      earlierInput = bytes earlierState ++ [domSqueeze] ∨
        earlierInput = bytes earlierState ++ [domAdvance])
    (overlap : earlierInput = bytes currentState ++ [domAdvance]) :
    earlierState = currentState := by
  rcases earlierIsPair with outputHalf | advanceHalf
  · exact (output_input_ne_advance_input earlierState currentState
      (outputHalf.symm.trans overlap)).elim
  · exact advance_input_eq_implies_state_eq earlierState currentState
      (advanceHalf.symm.trans overlap)

theorem pair_input_overlap_implies_state_eq
    (currentState earlierState : Digest256)
    (currentInput earlierInput : ByteString)
    (currentIsPair :
      currentInput = bytes currentState ++ [domSqueeze] ∨
        currentInput = bytes currentState ++ [domAdvance])
    (earlierIsPair :
      earlierInput = bytes earlierState ++ [domSqueeze] ∨
        earlierInput = bytes earlierState ++ [domAdvance])
    (overlap : earlierInput = currentInput) :
    earlierState = currentState := by
  rcases currentIsPair with outputHalf | advanceHalf
  · apply output_input_overlap_classification currentState earlierState
      earlierInput earlierIsPair
    exact overlap.trans outputHalf
  · apply advance_input_overlap_classification currentState earlierState
      earlierInput earlierIsPair
    exact overlap.trans advanceHalf

#print axioms digest_bytes_injective
#print axioms output_input_eq_implies_state_eq
#print axioms advance_input_eq_implies_state_eq
#print axioms output_input_ne_advance_input
#print axioms advance_input_ne_output_input
#print axioms digest_suffix_ne_output_input_of_length_ne_one
#print axioms digest_suffix_ne_advance_input_of_length_ne_one
#print axioms pair_input_overlap_implies_state_eq

end AspisK1.V7Tag73SqueezeInputStateInjectivity
