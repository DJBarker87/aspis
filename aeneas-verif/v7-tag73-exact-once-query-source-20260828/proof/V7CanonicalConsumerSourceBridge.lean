import V7CanonicalConsumerNormalized.Funs

/-!
# Source bridge for the selected deferred query consumer

The generated `gamma_combine_v6_packed_layer0` body is the validation-only
normalization of the selected Rust function.  Its length guards and both
production packed-decoder calls are unchanged; only the infallible arithmetic
after both decoders succeed is replaced by a zero result in the extraction
input.  The direct LLBC beside this proof pins the untouched function.
-/

set_option autoImplicit false

namespace AspisV7CanonicalConsumerSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CanonicalConsumerNormalizedGenerated

private theorem usize_result_mul_exact (left right result : Std.Usize)
    (bound : left.val * right.val ≤ Std.Usize.max)
    (value : result.val = left.val * right.val) :
    (left * right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.mul_spec (x := left) (y := right) bound)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_result_add_exact (left right result : Std.Usize)
    (bound : left.val + right.val ≤ Std.Usize.max)
    (value : result.val = left.val + right.val) :
    (left + right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.add_spec (x := left) (y := right) bound)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_result_div_exact (left right result : Std.Usize)
    (nonzero : right.val ≠ 0)
    (value : result.val = left.val / right.val) :
    (left / right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.div_spec left (y := right) nonzero)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_result_rem_exact (left right result : Std.Usize)
    (nonzero : right.val ≠ 0)
    (value : result.val = left.val % right.val) :
    (left % right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.rem_spec left (y := right) nonzero)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem c1_packed_bytes_run :
    v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY = ok 403#usize := by
  have mul_4_26 : (4#usize * 26#usize : Result Std.Usize) =
      ok 104#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_104_31 : (104#usize * 31#usize : Result Std.Usize) =
      ok 3224#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_3224_7 : (3224#usize + 7#usize : Result Std.Usize) =
      ok 3231#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_3231_8 : (3231#usize / 8#usize : Result Std.Usize) =
      ok 403#usize := by
    apply usize_result_div_exact <;> scalar_tac
  simp [v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY,
    v6_onefold.V6_C1_LIMBS_PER_QUERY, v6_onefold.V6_C1_COLUMNS,
    v6_onefold.packed_bytes, mul_4_26, mul_104_31, add_3224_7,
    div_3231_8]

private theorem c2_packed_bytes_run :
    v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY = ok 186#usize := by
  have mul_4_4 : (4#usize * 4#usize : Result Std.Usize) =
      ok 16#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_16_3 : (16#usize * 3#usize : Result Std.Usize) =
      ok 48#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_48_31 : (48#usize * 31#usize : Result Std.Usize) =
      ok 1488#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_1488_7 : (1488#usize + 7#usize : Result Std.Usize) =
      ok 1495#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_1495_8 : (1495#usize / 8#usize : Result Std.Usize) =
      ok 186#usize := by
    apply usize_result_div_exact <;> scalar_tac
  simp [v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY,
    v6_onefold.V6_C2_LIMBS_PER_QUERY, v6_onefold.V6_C2_COLUMNS,
    v6_onefold.packed_bytes, mul_4_4, mul_16_3, mul_48_31,
    add_1488_7, div_1495_8]

theorem extracted_query_record_widths_are_403_and_186 :
    v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY = ok 403#usize ∧
      v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY = ok 186#usize :=
  ⟨c1_packed_bytes_run, c2_packed_bytes_run⟩

/-- If the unchanged 104-limb scan reports any invalid representative, the
generated production decoder returns `NonCanonicalM31`. -/
theorem c1_decoder_reported_malformed_is_fail_closed
    (bytes : Slice Std.U8) (output : Array Std.U32 104#usize)
    (invalid : Std.U32)
    (exactLength : Slice.len bytes = 403#usize)
    (scan :
      v6_onefold.decode_packed_m31_eight_aligned_loop0
          13#usize bytes (Array.repeat 104#usize 0#u32) 0#u32 0#usize =
        ok (output, invalid))
    (malformed : invalid ≠ 0#u32) :
    v6_onefold.decode_packed_m31_eight_aligned 104#usize bytes =
      ok (.Err v6_onefold.V6WireError.NonCanonicalM31) := by
  have remRun : (104#usize % 8#usize : Result Std.Usize) =
      ok 0#usize := by
    apply usize_result_rem_exact <;> scalar_tac
  have divRun : (104#usize / 8#usize : Result Std.Usize) =
      ok 13#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have mulRun : (13#usize * 31#usize : Result Std.Usize) =
      ok 403#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  simp [v6_onefold.decode_packed_m31_eight_aligned, remRun, divRun,
    mulRun, exactLength, scan, malformed]

/-- The analogous fail-closed statement for the unchanged 48-limb scan. -/
theorem c2_decoder_reported_malformed_is_fail_closed
    (bytes : Slice Std.U8) (output : Array Std.U32 48#usize)
    (invalid : Std.U32)
    (exactLength : Slice.len bytes = 186#usize)
    (scan :
      v6_onefold.decode_packed_m31_eight_aligned_loop0
          6#usize bytes (Array.repeat 48#usize 0#u32) 0#u32 0#usize =
        ok (output, invalid))
    (malformed : invalid ≠ 0#u32) :
    v6_onefold.decode_packed_m31_eight_aligned 48#usize bytes =
      ok (.Err v6_onefold.V6WireError.NonCanonicalM31) := by
  have remRun : (48#usize % 8#usize : Result Std.Usize) =
      ok 0#usize := by
    apply usize_result_rem_exact <;> scalar_tac
  have divRun : (48#usize / 8#usize : Result Std.Usize) =
      ok 6#usize := by
    apply usize_result_div_exact <;> scalar_tac
  have mulRun : (6#usize * 31#usize : Result Std.Usize) =
      ok 186#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  simp [v6_onefold.decode_packed_m31_eight_aligned, remRun, divRun,
    mulRun, exactLength, scan, malformed]

/-- A successful normalized gamma consumer is possible only after the exact
production decoders at widths 104 and 48 have both returned `Ok`.  Hence the
consumer cannot bypass either canonicality scan. -/
theorem gamma_success_implies_both_exact_decoders_succeeded
    (c1Packed c2Packed : Slice Std.U8)
    (powers : state_only_spend_query.StateOnlySpendQueryPowers)
    (combined : Array field.QM31 4#usize)
    (success :
      v6_onefold.gamma_combine_v6_packed_layer0 c1Packed c2Packed powers =
        ok (.Ok combined)) :
    ∃ c1 : Array Std.U32 104#usize,
      ∃ c2 : Array Std.U32 48#usize,
        v6_onefold.decode_packed_m31_eight_aligned 104#usize c1Packed =
            ok (.Ok c1) ∧
          v6_onefold.decode_packed_m31_eight_aligned 48#usize c2Packed =
            ok (.Ok c2) := by
  simp only [v6_onefold.gamma_combine_v6_packed_layer0,
    c1_packed_bytes_run, c2_packed_bytes_run] at success
  simp only [bind_tc_ok] at success
  split at success
  · simp at success
  · split at success
    · simp at success
    · generalize c1Run :
          v6_onefold.decode_packed_m31_eight_aligned 104#usize c1Packed =
            c1Result at success ⊢
      cases c1Result with
      | fail error => simp at success
      | div => simp at success
      | ok c1Inner =>
          cases c1Inner with
          | Err error =>
              simp [
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                at success
          | Ok c1 =>
              generalize c2Run :
                  v6_onefold.decode_packed_m31_eight_aligned 48#usize c2Packed =
                    c2Result at success ⊢
              cases c2Result with
              | fail error => simp [
                    core.result.Result.Insts.CoreOpsTry.branch] at success
              | div => simp [
                    core.result.Result.Insts.CoreOpsTry.branch] at success
              | ok c2Inner =>
                  cases c2Inner with
                  | Err error =>
                      simp [
                        core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                        at success
                  | Ok c2 =>
                      exact ⟨c1, c2, rfl, rfl⟩

#print axioms extracted_query_record_widths_are_403_and_186
#print axioms c1_decoder_reported_malformed_is_fail_closed
#print axioms c2_decoder_reported_malformed_is_fail_closed
#print axioms gamma_success_implies_both_exact_decoders_succeeded

end AspisV7CanonicalConsumerSourceBridge
