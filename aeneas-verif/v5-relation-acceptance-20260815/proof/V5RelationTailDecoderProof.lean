import V5RelationDecodeGenerated
import V5RelationLayoutGenerated
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

/-! ## Exact production layout constants and call categories -/

private theorem usizeMulExact (x y z : Std.Usize)
    (hbound : x.val * y.val ≤ Std.Usize.max)
    (hval : z.val = x.val * y.val) :
    x * y = ok z := by
  have hspec := Std.Usize.mul_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeAddExact (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have hspec := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

private theorem usizeSubExact (x y z : Std.Usize)
    (hbound : y.val ≤ x.val)
    (hval : z.val = x.val - y.val) :
    x - y = ok z := by
  have hspec := Std.Usize.sub_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists hspec
  have valueIsZ : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueIsZ]

/-- Charon/Aeneas evaluates the public production layout constants to the
seven byte offsets used by the verifier: the six category starts followed by
the complete tail length. -/
theorem extracted_relation_layout_exact :
    V5RelationLayoutGenerated.extract_relation_layout = .ok
      (Array.make 7#usize
        [0#usize, 64#usize, 160#usize, 288#usize, 416#usize, 864#usize,
          928#usize]) := by
  unfold V5RelationLayoutGenerated.extract_relation_layout
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_BYTES
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_FINAL_OFFSET
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_MIX_OFFSET
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_OOD_OFFSET
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_LINE_OFFSET
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET
    V5RelationLayoutGenerated.relation_stress.SUMCHECK_VALUES
    V5RelationLayoutGenerated.relation_stress.OOD_MIXES
    V5RelationLayoutGenerated.relation_stress.OOD_VALUES
    V5RelationLayoutGenerated.relation_stress.LINE_POINTS
    V5RelationLayoutGenerated.relation_stress.CIRCLE_COORDINATES
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_FINAL_COEFFICIENTS
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES
    V5RelationLayoutGenerated.relation_stress.V5_RELATION_STRESS_ROUNDS
    V5RelationLayoutGenerated.relation_stress.QM31_BYTES
    V5RelationLayoutGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS
  have mul2_2 : 2#usize * 2#usize = ok 4#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul4_16 : 4#usize * 16#usize = ok 64#usize := by
    apply usizeMulExact <;> scalar_tac
  have add0_64 : 0#usize + 64#usize = ok 64#usize := by
    apply usizeAddExact <;> scalar_tac
  have sub4_1 : 4#usize - 1#usize = ok 3#usize := by
    apply usizeSubExact <;> scalar_tac
  have mul3_2 : 3#usize * 2#usize = ok 6#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul6_16 : 6#usize * 16#usize = ok 96#usize := by
    apply usizeMulExact <;> scalar_tac
  have add64_96 : 64#usize + 96#usize = ok 160#usize := by
    apply usizeAddExact <;> scalar_tac
  have mul4_2 : 4#usize * 2#usize = ok 8#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul8_16 : 8#usize * 16#usize = ok 128#usize := by
    apply usizeMulExact <;> scalar_tac
  have add160_128 : 160#usize + 128#usize = ok 288#usize := by
    apply usizeAddExact <;> scalar_tac
  have add288_128 : 288#usize + 128#usize = ok 416#usize := by
    apply usizeAddExact <;> scalar_tac
  have mul4_7 : 4#usize * 7#usize = ok 28#usize := by
    apply usizeMulExact <;> scalar_tac
  have mul28_16 : 28#usize * 16#usize = ok 448#usize := by
    apply usizeMulExact <;> scalar_tac
  have add416_448 : 416#usize + 448#usize = ok 864#usize := by
    apply usizeAddExact <;> scalar_tac
  have add864_64 : 864#usize + 64#usize = ok 928#usize := by
    apply usizeAddExact <;> scalar_tac
  simp only [mul2_2, bind_tc_ok, mul4_16, add0_64, sub4_1, mul3_2,
    mul6_16, add64_96, mul4_2, mul8_16, add160_128, add288_128,
    mul4_7, mul28_16, add416_448, add864_64]

/-- Byte position computed by production `decode_indexed`. -/
def productionIndexedByteStart (categoryOffset wordIndex : Nat) : Nat :=
  categoryOffset + wordIndex * 16

theorem production_circle_x_selects_source_word (sample : Fin 2) :
    productionIndexedByteStart 0 (2 * sample.val) =
      16 * (sourceCircleWord
        ⟨2 * sample.val, by omega⟩).val := by
  simp [productionIndexedByteStart, sourceCircleWord]
  omega

theorem production_circle_y_selects_source_word (sample : Fin 2) :
    productionIndexedByteStart 0 (2 * sample.val + 1) =
      16 * (sourceCircleWord
        ⟨2 * sample.val + 1, by omega⟩).val := by
  simp [productionIndexedByteStart, sourceCircleWord]
  omega

theorem production_line_selects_source_word
    (lineRound : Fin 3) (sample : Fin 2) :
    productionIndexedByteStart 64 (2 * lineRound.val + sample.val) =
      16 * (sourceLineWord
        ⟨2 * lineRound.val + sample.val, by omega⟩).val := by
  simp [productionIndexedByteStart, sourceLineWord]
  omega

theorem production_ood_selects_source_word
    (round : Fin 4) (sample : Fin 2) :
    productionIndexedByteStart 160 (2 * round.val + sample.val) =
      16 * (sourceOodWord round sample).val := by
  simp [productionIndexedByteStart, sourceOodWord,
    physicalRelationIndex_ood_val]
  omega

theorem production_mix_selects_source_word
    (round : Fin 4) (sample : Fin 2) :
    productionIndexedByteStart 288 (2 * round.val + sample.val) =
      16 * (sourceMixWord round sample).val := by
  simp [productionIndexedByteStart, sourceMixWord, physicalMixStart]
  omega

theorem production_polynomial_selects_source_word
    (round : Fin 4) (degree : Fin 7) :
    productionIndexedByteStart 416 (7 * round.val + degree.val) =
      16 * (sourcePolynomialWord round degree).val := by
  simp [productionIndexedByteStart, sourcePolynomialWord,
    physicalRelationIndex_polynomial_val]
  omega

theorem production_final_selects_source_word (coefficient : Fin 4) :
    productionIndexedByteStart 864 coefficient.val =
      16 * (sourceFinalWord coefficient).val := by
  simp [productionIndexedByteStart, sourceFinalWord, physicalFinalStart]
  omega

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
#print axioms extracted_relation_layout_exact
#print axioms production_circle_x_selects_source_word
#print axioms production_circle_y_selects_source_word
#print axioms production_line_selects_source_word
#print axioms production_ood_selects_source_word
#print axioms production_mix_selects_source_word
#print axioms production_polynomial_selects_source_word
#print axioms production_final_selects_source_word
#print axioms extracted_relation_tail_field_eq_model
#print axioms extracted_relation_tail_all_58_fields

end AspisV5RelationTailDecoderProof
