import AspisFormal.K1.V7Tag73FinalWorkQ16CandidateController
import AspisFormal.K1.V7Tag73SchedulerNativeQ16Replay
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.Pool.V7MerkleUntypedErasureStability

/-!
# Merkle separation for the routed final-work/q16 coordinates

The causal K1.3 router changes only the selected final-work answer and the
512 q16 duplex answers.  Their literal SHA inputs have lengths 41, 42, or 33,
whereas the only accepted Merkle preimage lengths are 437, 220, and 53.
This module records the exact grammar separation used by the restored
complete-tree erasure argument.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73MerkleRoutedInputSeparation

open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleUntypedErasureStability

theorem runtimeInputToRawHashInput_length (input : ByteString) :
    (runtimeInputToRawHashInput input).length = input.length := by
  simp [runtimeInputToRawHashInput]

/-- Every q16 squeeze-output coordinate is outside the Merkle grammar. -/
theorem q16_output_input_is_not_merkle (digest : Digest256) :
    parseTypedPreimage
      (runtimeInputToRawHashInput (q16OutputInput digest)) = none := by
  apply parseTypedPreimage_eq_none_of_length
  all_goals
    simp [runtimeInputToRawHashInput, q16OutputInput, bytes_length]

/-- Every q16 duplex-advance coordinate is outside the Merkle grammar. -/
theorem q16_advance_input_is_not_merkle (digest : Digest256) :
    parseTypedPreimage
      (runtimeInputToRawHashInput (q16AdvanceInput digest)) = none := by
  apply parseTypedPreimage_eq_none_of_length
  all_goals
    simp [runtimeInputToRawHashInput, q16AdvanceInput, bytes_length]

/-- The selected final-work probe is outside the Merkle grammar. -/
theorem final_work_input_is_not_merkle
    (digest : Digest256) (nonce : NonceBytes) :
    parseTypedPreimage (runtimeInputToRawHashInput
      (literalFinalWorkKey digest nonce).workInput) = none := by
  apply parseTypedPreimage_eq_none_of_length
  all_goals
    simp [runtimeInputToRawHashInput, RawFinalWorkKey.workInput,
      literalFinalWorkKey, bytes_length]

/-- The selected final-nonce absorb coordinate is outside the Merkle grammar. -/
theorem final_work_absorb_input_is_not_merkle
    (digest : Digest256) (nonce : NonceBytes) :
    parseTypedPreimage (runtimeInputToRawHashInput
      (literalFinalWorkKey digest nonce).absorbInput) = none := by
  apply parseTypedPreimage_eq_none_of_length
  all_goals
    simp [runtimeInputToRawHashInput, RawFinalWorkKey.absorbInput,
      literalFinalWorkKey, bytes_length]

#print axioms runtimeInputToRawHashInput_length
#print axioms q16_output_input_is_not_merkle
#print axioms q16_advance_input_is_not_merkle
#print axioms final_work_input_is_not_merkle
#print axioms final_work_absorb_input_is_not_merkle

end AspisK1.V7Tag73MerkleRoutedInputSeparation
