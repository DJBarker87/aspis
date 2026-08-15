import V5TranscriptTailGenerated.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V5TranscriptTailGenerated

set_option maxRecDepth 3000

namespace AspisV5TranscriptTailSourceProof

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

private theorem usize_mul_4_16 :
    (4#usize * 16#usize : Result Std.Usize) = .ok 64#usize := by
  change UScalar.mul 4#usize 16#usize = .ok 64#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_mul_4_7 :
    (4#usize * 7#usize : Result Std.Usize) = .ok 28#usize := by
  change UScalar.mul 4#usize 7#usize = .ok 28#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_mul_28_16 :
    (28#usize * 16#usize : Result Std.Usize) = .ok 448#usize := by
  change UScalar.mul 28#usize 16#usize = .ok 448#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_mul_4_2 :
    (4#usize * 2#usize : Result Std.Usize) = .ok 8#usize := by
  change UScalar.mul 4#usize 2#usize = .ok 8#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_mul_8_16 :
    (8#usize * 16#usize : Result Std.Usize) = .ok 128#usize := by
  change UScalar.mul 8#usize 16#usize = .ok 128#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_sub_4_1 :
    (4#usize - 1#usize : Result Std.Usize) = .ok 3#usize := by
  change UScalar.sub 4#usize 1#usize = .ok 3#usize
  norm_num [UScalar.sub, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all <;>
    apply UScalar.eq_of_val_eq <;> simp [UScalar.val]

private theorem usize_mul_3_2 :
    (3#usize * 2#usize : Result Std.Usize) = .ok 6#usize := by
  change UScalar.mul 3#usize 2#usize = .ok 6#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_mul_6_16 :
    (6#usize * 16#usize : Result Std.Usize) = .ok 96#usize := by
  change UScalar.mul 6#usize 16#usize = .ok 96#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_mul_2_2 :
    (2#usize * 2#usize : Result Std.Usize) = .ok 4#usize := by
  change UScalar.mul 2#usize 2#usize = .ok 4#usize
  norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_0_64 :
    (0#usize + 64#usize : Result Std.Usize) = .ok 64#usize := by
  change UScalar.add 0#usize 64#usize = .ok 64#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_64_96 :
    (64#usize + 96#usize : Result Std.Usize) = .ok 160#usize := by
  change UScalar.add 64#usize 96#usize = .ok 160#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_160_128 :
    (160#usize + 128#usize : Result Std.Usize) = .ok 288#usize := by
  change UScalar.add 160#usize 128#usize = .ok 288#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_288_128 :
    (288#usize + 128#usize : Result Std.Usize) = .ok 416#usize := by
  change UScalar.add 288#usize 128#usize = .ok 416#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_416_448 :
    (416#usize + 448#usize : Result Std.Usize) = .ok 864#usize := by
  change UScalar.add 416#usize 448#usize = .ok 864#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_864_64 :
    (864#usize + 64#usize : Result Std.Usize) = .ok 928#usize := by
  change UScalar.add 864#usize 64#usize = .ok 928#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem u32_shift_one_by_17 :
    (1#u32 <<< 17#i32 : Result Std.U32) = .ok 131072#u32 := by
  change UScalar.shiftLeft_IScalar 1#u32 17#i32 = .ok 131072#u32
  have h17 : (17#i32).val = 17 := by scalar_tac
  simp [UScalar.shiftLeft_IScalar, UScalar.shiftLeft, h17]
  apply UScalar.eq_of_val_eq
  simp [UScalar.val]

theorem exact_tail_constants :
    aspis_core.transcript.label.M31_CIRCLE_FINAL_TENSOR_POLY = .ok 19#u8 ∧
      aspis_core.transcript.label.M31_STATE_ONLY_QUERY_CANDIDATE = .ok 44#u8 ∧
      v5_cu_probe.V5_CU_PROBE_QUERY_COUNT = .ok 18#usize ∧
      aspis_core.circle_hiding_prefix.PAYMENT_HIDING_QUERY_DRAW_LIMIT =
        .ok 64#usize := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- On every successful generated execution, the four decoded output values
are in source order `0,1,2,3`, and the returned 18 queries are exactly the
values returned by the transcript sampler.  The numeric QM31 observations are
decoder indices; no field or hash property is used. -/
theorem generated_tail_success_returns_exact_decodes_and_queries
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (selector : Std.U8)
    (polynomial : Array aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
  polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
      queries.val = transcript.sampledQueries.val ∧
      transcript.sampledQueries.val.length = 18 ∧
      selector.val < 3 := by
  unfold v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript at success
  simp [v5_relation_stress.V5_RELATION_STRESS_FINAL_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_MIX_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_OOD_OFFSET,
      v5_relation_stress.V5_RELATION_STRESS_LINE_OFFSET,
      v5_relation_stress.SUMCHECK_VALUES, v5_relation_stress.OOD_MIXES,
      v5_relation_stress.OOD_VALUES, v5_relation_stress.LINE_POINTS,
      v5_relation_stress.CIRCLE_COORDINATES,
      v5_relation_stress.V5_RELATION_STRESS_ROUNDS,
      v5_relation_stress.V5_RELATION_STRESS_OOD_SAMPLES,
      v5_relation_stress.V5_RELATION_STRESS_CIRCLE_OFFSET,
      v5_relation_stress.QM31_BYTES,
      aspis_core.sumcheck.SUMCHECK_COEFFICIENTS, v5_cu_probe.QM31_BYTES,
      v5_cu_probe.v5_query_selector_is_valid, v5_cu_probe.decode_qm31,
      aspis_core.transcript.label.M31_CIRCLE_FINAL_TENSOR_POLY,
      aspis_core.transcript.label.M31_STATE_ONLY_QUERY_CANDIDATE,
      aspis_core.transcript.Transcript.absorb,
      v5_cu_probe.check_and_absorb_real_v5_final_nonce,
      v5_cu_probe.V5_CU_PROBE_QUERY_COUNT,
      aspis_core.circle_hiding_prefix.PAYMENT_HIDING_QUERY_DRAW_LIMIT,
      aspis_core.transcript.Transcript.challenge_queries_without_replacement,
      core.result.Result.map_err,
      Array.Insts.CoreConvertTryFromVecVec.try_from,
      usize_mul_4_16, usize_mul_4_7, usize_mul_28_16, usize_mul_4_2,
      usize_mul_8_16, usize_sub_4_1, usize_mul_3_2, usize_mul_6_16,
      usize_mul_2_2, usize_add_0_64, usize_add_64_96,
      usize_add_160_128, usize_add_288_128, usize_add_416_448,
      usize_add_864_64] at success
  split at success
  all_goals
    generalize hslice :
      core.slice.index.SliceIndexRangeUsizeSlice.index
          { start := 864#usize, «end» := 928#usize }
          parsed.v5_relation_stress.to_slice = sliceResult at success
    cases sliceResult with
    | fail error => simp_all
    | div => simp_all
    | ok stressFinal =>
      generalize hcomparison :
        core.cmp.PartialEq.ne.default
            (core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8)
            stressFinal parsed.v5_final_coefficients = comparisonResult at success
      cases comparisonResult with
      | fail error => simp_all
      | div => simp_all
      | ok differs =>
        cases differs <;>
          simp_all [lift, Array.to_slice, u32_shift_one_by_17]
        try split at success
        all_goals
          simp_all [Array.make,
            v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32ProgramError.call_once]
        all_goals
          rcases success with ⟨hpolynomial, hqueries⟩
          subst polynomial
          subst queries
          exact ⟨rfl, rfl⟩

#print axioms exact_tail_constants
#print axioms generated_tail_success_returns_exact_decodes_and_queries

end AspisV5TranscriptTailSourceProof
