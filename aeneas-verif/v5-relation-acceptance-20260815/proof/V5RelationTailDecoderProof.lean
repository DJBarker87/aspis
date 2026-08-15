import V5RelationDecodeGenerated
import V5FriDecoderProof
import AspisFormal.V5RelationStressSourceBridge

/-!
# Production relation-tail decoder fragments

This file joins two source-extracted facts without claiming that pinned
Aeneas translated the enclosing four-round relation loop:

* `V5RelationDecodeGenerated` is the exact extracted `decode_indexed` wrapper
  from `v5_relation_stress.rs`;
* `V5FriDecoderProof` proves the semantics of the production
  `QM31::from_le_bytes` decoder used by that wrapper.

The maintained relation-tail model splits all 928 bytes into exactly 58
sixteen-byte QM31 words.  The theorem below applies the extracted decoder
equality to every one of those words and every possible tail.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5RelationTailDecoderProof

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCRelationTailCodec
open AspisV5RelationStressSourceBridge

/-- The extracted source wrapper computes `offset + index * 16` and then
calls the extracted QM31 decoder.  This is the complete generated body of
production `decode_indexed`. -/
theorem extracted_decode_indexed_exact_call
    (bytes : Array Std.U8 928#usize)
    (offset index : Std.Usize) :
    V5RelationDecodeGenerated.relation_stress.decode_indexed bytes offset index = (do
      let scaled ← lift (Std.Usize.wrapping_mul
        index V5RelationDecodeGenerated.relation_stress.QM31_BYTES)
      let absolute ← lift (Std.Usize.wrapping_add
        offset scaled)
      V5RelationDecodeGenerated.relation_stress.decode_qm31 bytes absolute) := by
  rfl

/-- Apply the source-extracted production QM31 decoder to one exact word of
the maintained 928-byte relation tail. -/
def extractedRelationTailField
    (bytes : RelationTailBytes)
    (field : Fin physicalRelationTailFieldCount) : Option QM31Limbs :=
  AspisV5FriDecoderSourceProof.extractedQM31Decode
    (relationTailFieldBytes bytes field)

/-- Every one of the 58 relation-tail words has the exact maintained
little-endian semantics under the extracted production QM31 decoder. -/
theorem extracted_relation_tail_field_eq_model
    (bytes : RelationTailBytes)
    (field : Fin physicalRelationTailFieldCount) :
    extractedRelationTailField bytes field =
      decodeSourceRelationTailField (Equiv.refl QM31Limbs) bytes field := by
  simpa [extractedRelationTailField, decodeSourceRelationTailField] using
    AspisV5FriDecoderSourceProof.extractedQM31Decode_eq_model
      (relationTailFieldBytes bytes field)

/-- The previous equality is universal over the exact 58-word inventory; no
word category or selected runtime fixture is omitted. -/
theorem extracted_relation_tail_all_58_fields
    (bytes : RelationTailBytes) :
    ∀ field : Fin physicalRelationTailFieldCount,
      extractedRelationTailField bytes field =
        decodeSourceRelationTailField (Equiv.refl QM31Limbs) bytes field := by
  intro field
  exact extracted_relation_tail_field_eq_model bytes field

#print axioms extracted_decode_indexed_exact_call
#print axioms extracted_relation_tail_field_eq_model
#print axioms extracted_relation_tail_all_58_fields

end AspisV5RelationTailDecoderProof
