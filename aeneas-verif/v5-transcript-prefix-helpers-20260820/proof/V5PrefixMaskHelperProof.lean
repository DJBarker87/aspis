import V5PrefixMaskHelperGenerated.Funs

namespace V5PrefixMaskHelperProof

open Aeneas Aeneas.Std Result ControlFlow Error
open V5PrefixMaskHelperGenerated

abbrev QM31Bytes := V5PrefixMaskHelperGenerated.aspis_core.field.QM31
abbrev Transcript :=
  V5PrefixMaskHelperGenerated.aspis_core.transcript.Transcript

/-- The complete successful behavior of the extracted unchanged production
helper: encode `(degree = 27, rounds = 10, initial claim)`, absorb it under
label 31, then request one nonzero field challenge. -/
theorem extracted_masked_sumcheck_success_exact
    (transcript : Transcript) (initialClaim eta : QM31Bytes)
    (hnext : transcript.next = some eta) :
    V5PrefixMaskHelperGenerated.extract_begin_state_only_masked_sumcheck
        transcript initialClaim =
      .ok (.Ok eta,
        { transcript with events :=
            transcript.events ++
              [.absorb 31#u8 ([27#u8, 10#u8] ++ initialClaim.val),
                .squeezeNonzero] }) := by
  simp [V5PrefixMaskHelperGenerated.extract_begin_state_only_masked_sumcheck,
    V5PrefixMaskHelperGenerated.aspis_core.state_only_hiding.begin_state_only_masked_sumcheck,
    V5PrefixMaskHelperGenerated.aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASKED_ORACLE_DEGREE,
    V5PrefixMaskHelperGenerated.aspis_core.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
    V5PrefixMaskHelperGenerated.aspis_core.field.QM31.write_le_bytes,
    V5PrefixMaskHelperGenerated.aspis_core.transcript.label.M31_STATE_ONLY_HIDING_MASK_CLAIM,
    V5PrefixMaskHelperGenerated.aspis_core.transcript.Transcript.absorb,
    V5PrefixMaskHelperGenerated.aspis_core.transcript.Transcript.challenge_nonzero_qm31,
    V5PrefixMaskHelperGenerated.core.result.Result.map_err,
    Array.update, Array.repeat, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Array.to_slice, Array.from_slice, Slice.drop, Slice.setSlice!,
    List.setSlice!, UScalar.cast, lift, hnext, initialClaim.property,
    List.append_assoc]
  simp_lists
  constructor <;> apply UScalar.eq_of_val_eq <;> decide

#print axioms extracted_masked_sumcheck_success_exact

end V5PrefixMaskHelperProof
