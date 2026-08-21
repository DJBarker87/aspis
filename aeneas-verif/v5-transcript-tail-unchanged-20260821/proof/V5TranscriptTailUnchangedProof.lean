import V5TranscriptTailUnchangedGenerated.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V5TranscriptTailUnchangedGenerated

set_option maxRecDepth 3000

namespace AspisV5TranscriptTailUnchangedProof

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

private abbrev TailIter :=
  core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.IterMut aspis_core.field.QM31)

private def tailZeroArray : Array aspis_core.field.QM31 4#usize :=
  Array.repeat 4#usize 0#usize

private def tailIter0 : TailIter :=
  { iter := { slice := Array.to_slice tailZeroArray, i := 0 }, count := 0#usize }

private def tailBack0 : TailIter → TailIter := fun e => e

private def tailIter1 : TailIter :=
  { tailIter0 with iter := { tailIter0.iter with i := 1 }, count := 1#usize }

private def tailBack1 : TailIter → TailIter := fun e =>
  { e with iter := { e.iter with slice := e.iter.slice.setAtNat 0 0#usize } }

private def tailIter2 : TailIter :=
  { tailIter0 with iter := { tailIter0.iter with i := 2 }, count := 2#usize }

private def tailBack2 : TailIter → TailIter := fun e =>
  tailBack1
    { e with iter := { e.iter with slice := e.iter.slice.setAtNat 1 1#usize } }

private def tailIter3 : TailIter :=
  { tailIter0 with iter := { tailIter0.iter with i := 3 }, count := 3#usize }

private def tailBack3 : TailIter → TailIter := fun e =>
  tailBack2
    { e with iter := { e.iter with slice := e.iter.slice.setAtNat 2 2#usize } }

private def tailIter4 : TailIter :=
  { tailIter0 with iter := { tailIter0.iter with i := 4 }, count := 4#usize }

private def tailBack4 : TailIter → TailIter := fun e =>
  tailBack3
    { e with iter := { e.iter with slice := e.iter.slice.setAtNat 3 3#usize } }

private theorem usize_add_0_1 :
    (0#usize + 1#usize : Result Std.Usize) = .ok 1#usize := by
  change UScalar.add 0#usize 1#usize = .ok 1#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_1_1 :
    (1#usize + 1#usize : Result Std.Usize) = .ok 2#usize := by
  change UScalar.add 1#usize 1#usize = .ok 2#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_2_1 :
    (2#usize + 1#usize : Result Std.Usize) = .ok 3#usize := by
  change UScalar.add 2#usize 1#usize = .ok 3#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem usize_add_3_1 :
    (3#usize + 1#usize : Result Std.Usize) = .ok 4#usize := by
  change UScalar.add 3#usize 1#usize = .ok 4#usize
  norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
  cases System.Platform.numBits_eq <;> simp_all

private theorem tail_body_state0
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8)
    (toSliceBack : Slice aspis_core.field.QM31 →
      Array aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut aspis_core.field.QM31 →
      Slice aspis_core.field.QM31)
    (enumBack : TailIter → core.slice.iter.IterMut aspis_core.field.QM31) :
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      tailIter0 tailBack0 = .ok (.cont (tailIter1, tailBack1)) := by
  simp [v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1,
    tailBack0, tailBack1, tailZeroArray, Array.to_slice, Array.repeat,
    usize_add_0_1, v5_cu_probe.decode_qm31]
  funext e
  rfl

private theorem tail_body_state1
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8)
    (toSliceBack : Slice aspis_core.field.QM31 →
      Array aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut aspis_core.field.QM31 →
      Slice aspis_core.field.QM31)
    (enumBack : TailIter → core.slice.iter.IterMut aspis_core.field.QM31) :
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      tailIter1 tailBack1 = .ok (.cont (tailIter2, tailBack2)) := by
  simp [v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter1, tailIter2,
    tailBack1, tailBack2, tailZeroArray, Array.to_slice, Array.repeat,
    usize_add_1_1, v5_cu_probe.decode_qm31]
  funext e
  rfl

private theorem tail_body_state2
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8)
    (toSliceBack : Slice aspis_core.field.QM31 →
      Array aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut aspis_core.field.QM31 →
      Slice aspis_core.field.QM31)
    (enumBack : TailIter → core.slice.iter.IterMut aspis_core.field.QM31) :
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      tailIter2 tailBack2 = .ok (.cont (tailIter3, tailBack3)) := by
  simp [v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter2, tailIter3,
    tailBack1, tailBack2, tailBack3, tailZeroArray, Array.to_slice,
    Array.repeat, usize_add_2_1, v5_cu_probe.decode_qm31]
  funext e
  rfl

private theorem tail_body_state3
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8)
    (toSliceBack : Slice aspis_core.field.QM31 →
      Array aspis_core.field.QM31 4#usize)
    (iterBack : core.slice.iter.IterMut aspis_core.field.QM31 →
      Slice aspis_core.field.QM31)
    (enumBack : TailIter → core.slice.iter.IterMut aspis_core.field.QM31) :
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed toSliceBack iterBack enumBack transcript nonce selector
      tailIter3 tailBack3 = .ok (.cont (tailIter4, tailBack4)) := by
  simp [v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next, tailIter0, tailIter3, tailIter4,
    tailBack1, tailBack2, tailBack3, tailBack4, tailZeroArray,
    Array.to_slice, Array.repeat, usize_add_3_1, v5_cu_probe.decode_qm31]
  funext e
  rfl

private theorem tailBack4_exact :
    ((tailBack4 tailIter4).iter.slice).val =
      [0#usize, 1#usize, 2#usize, 3#usize] := by
  simp [tailBack4, tailBack3, tailBack2, tailBack1, tailIter4,
    tailIter0, tailZeroArray, Array.to_slice, Array.repeat, Slice.setAtNat]

private theorem tailBack4_length :
    ((tailBack4 tailIter4).iter.slice).val.length = 4 := by
  rw [tailBack4_exact]
  rfl

private theorem tailFinalArray_exact :
    (Array.from_slice tailZeroArray (tailBack4 tailIter4).iter.slice).val =
      [0#usize, 1#usize, 2#usize, 3#usize] := by
  rw [Array.from_slice_val _ _ tailBack4_length]
  exact tailBack4_exact

private def TailOutputPost
    (transcript : aspis_core.transcript.Transcript)
    (out : Option (core.result.Result
      ((Array aspis_core.field.QM31 4#usize) × (Array Std.U32 18#usize))
      solana_program_error.ProgramError)) : Prop :=
  ∀ polynomial queries, out = some (.Ok (polynomial, queries)) →
    polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
    queries.val = transcript.sampledQueries.val ∧
    transcript.sampledQueries.val.length = 18

private theorem tail_body_state4
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8) :
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body
      parsed (fun s => Array.from_slice tailZeroArray s)
      (fun current => current.slice) (fun current => current.iter)
      transcript nonce selector tailIter4 tailBack4 ⦃ flow =>
        match flow with
        | .done out => TailOutputPost transcript out
        | .cont _ => False ⦄ := by
  simp [v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop.body,
    core.iter.adapters.enumerate.IteratorEnumerateMut.next,
    core.slice.iter.IteratorIterMut.next, tailIter4, tailIter0,
    tailZeroArray, Array.to_slice, Array.repeat,
    aspis_core.transcript.label.M31_CIRCLE_FINAL_TENSOR_POLY,
    aspis_core.transcript.label.M31_STATE_ONLY_QUERY_CANDIDATE,
    aspis_core.transcript.Transcript.absorb,
    v5_cu_probe.check_and_absorb_real_v5_final_nonce,
    v5_cu_probe.V5_CU_PROBE_QUERY_COUNT,
    aspis_core.circle_hiding_prefix.PAYMENT_HIDING_QUERY_DRAW_LIMIT,
    aspis_core.transcript.Transcript.challenge_queries_without_replacement,
    core.result.Result.map_err,
    Array.Insts.CoreConvertTryFromVecVec.try_from,
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript.closure_1.Insts.CoreOpsFunctionFnOnceTupleVecU32ProgramError.call_once,
    Array.make, Array.from_slice, TailOutputPost, u32_shift_one_by_17,
    lift, Aeneas.Std.WP.spec, Aeneas.Std.WP.theta,
    Aeneas.Std.WP.wp_return, tailBack4_exact]
  split
  all_goals
    cases System.Platform.numBits_eq <;>
      simp_all [Aeneas.Std.WP.wp_return, tailBack4_exact,
        tailBack4_length, UScalar.cMax]
  all_goals
    exact tailFinalArray_exact

private def TailLoopInv (state : TailIter × (TailIter → TailIter)) : Prop :=
  state = (tailIter0, tailBack0) ∨
  state = (tailIter1, tailBack1) ∨
  state = (tailIter2, tailBack2) ∨
  state = (tailIter3, tailBack3) ∨
  state = (tailIter4, tailBack4)

private theorem tail_generated_loop_post
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8) :
    v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
      parsed (fun s => Array.from_slice tailZeroArray s)
      (fun current => current.slice) (fun current => current.iter)
      tailIter0 tailBack0 transcript nonce selector
      ⦃ TailOutputPost transcript ⦄ := by
  unfold v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (fun state : TailIter × (TailIter → TailIter) =>
      4 - state.1.iter.i)
    TailLoopInv (TailOutputPost transcript)
  · rintro ⟨iter, back⟩ hstate
    rcases hstate with h0 | h1 | h2 | h3 | h4
    · cases h0
      dsimp only
      rw [tail_body_state0 parsed transcript nonce selector]
      simp only [Aeneas.Std.WP.spec_ok]
      exact ⟨Or.inr (Or.inl rfl), by norm_num [tailIter0, tailIter1]⟩
    · cases h1
      dsimp only
      rw [tail_body_state1 parsed transcript nonce selector]
      simp only [Aeneas.Std.WP.spec_ok]
      exact ⟨Or.inr (Or.inr (Or.inl rfl)),
        by norm_num [tailIter1, tailIter2]⟩
    · cases h2
      dsimp only
      rw [tail_body_state2 parsed transcript nonce selector]
      simp only [Aeneas.Std.WP.spec_ok]
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        by norm_num [tailIter2, tailIter3]⟩
    · cases h3
      dsimp only
      rw [tail_body_state3 parsed transcript nonce selector]
      simp only [Aeneas.Std.WP.spec_ok]
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))),
        by norm_num [tailIter3, tailIter4]⟩
    · cases h4
      dsimp only
      apply Aeneas.Std.WP.spec_mono
        (tail_body_state4 parsed transcript nonce selector)
      intro flow hflow
      cases flow with
      | done out => exact hflow
      | cont state => exact False.elim hflow
  · exact Or.inl rfl

private theorem tail_generated_loop_success
    (parsed : v5_cu_probe.ParsedProbeData)
    (transcript : aspis_core.transcript.Transcript)
    (nonce : Std.U64) (selector : Std.U8)
    (polynomial : Array aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
        parsed (fun s => Array.from_slice tailZeroArray s)
        (fun current => current.slice) (fun current => current.iter)
        tailIter0 tailBack0 transcript nonce selector =
          .ok (some (.Ok (polynomial, queries)))) :
    polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
      queries.val = transcript.sampledQueries.val ∧
      transcript.sampledQueries.val.length = 18 := by
  have hspec := tail_generated_loop_post parsed transcript nonce selector
  rw [success] at hspec
  simp only [Aeneas.Std.WP.spec_ok] at hspec
  exact hspec polynomial queries rfl

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
          simp [aspis_core.field.QM31.ZERO, lift, Array.to_slice_mut,
            Array.to_slice, core.slice.Slice.iter_mut,
            core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate,
            tailZeroArray, tailIter0, tailBack0] at success
          change
            (do
              let pending ←
                v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
                  parsed (fun s => Array.from_slice tailZeroArray s)
                  (fun current => current.slice) (fun current => current.iter)
                  tailIter0 tailBack0 transcript parsed.v5_final_nonce selector
              match pending with
              | none => fail panic
              | some r => ok r) =
              .ok (.Ok (polynomial, queries)) at success
          generalize hloop :
            v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript_loop
              parsed (fun s => Array.from_slice tailZeroArray s)
              (fun current => current.slice) (fun current => current.iter)
              tailIter0 tailBack0 transcript parsed.v5_final_nonce selector =
                loopResult at success
          cases loopResult with
          | fail error => simp_all
          | div => simp_all
          | ok pending =>
            cases pending with
            | none => simp_all
            | some result =>
              have hresult : result = .Ok (polynomial, queries) := by
                simpa using success
              subst result
              exact tail_generated_loop_success parsed transcript
                parsed.v5_final_nonce selector polynomial queries hloop

/-! ## Exact transcript-call observation -/

/-- The four transcript-affecting calls made after the polynomial decoder.
The nonce helper represents the production work check followed by its absorb;
the maintained transcript join expands that event into those two operations. -/
def expectedTailEvents
    (parsed : v5_cu_probe.ParsedProbeData) (selector : Std.U8) :
    List TailTranscriptEvent :=
  [.absorb 19#u8 parsed.v5_final_coefficients.val,
    .finalNonce parsed.v5_final_nonce,
    .absorb 44#u8 [selector],
    .querySample 18#usize 131072#u32 64#usize]

/-- Under the observation meanings supplied to the Aeneas-generated function,
the four transcript calls append exactly the production label, payload, nonce,
query count, bound, and draw limit. -/
theorem exact_observed_tail_calls
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (selector : Std.U8) :
    ∃ afterFinalPolynomial afterNonce afterSelector afterQueries,
      aspis_core.transcript.Transcript.absorb transcript 19#u8
          parsed.v5_final_coefficients = .ok afterFinalPolynomial ∧
      v5_cu_probe.check_and_absorb_real_v5_final_nonce
          afterFinalPolynomial parsed.v5_final_nonce =
        .ok (.Ok (), afterNonce) ∧
      aspis_core.transcript.Transcript.absorb afterNonce 44#u8
          (Array.to_slice (Array.make 1#usize [selector])) =
        .ok afterSelector ∧
      aspis_core.transcript.Transcript.challenge_queries_without_replacement
          afterSelector 18#usize 131072#u32 64#usize =
        .ok (.Ok transcript.sampledQueries, afterQueries) ∧
      afterQueries.events =
        transcript.events ++ expectedTailEvents parsed selector := by
  refine ⟨
    { transcript with events := transcript.events ++
        [.absorb 19#u8 parsed.v5_final_coefficients.val] },
    { transcript with events := transcript.events ++
        [.absorb 19#u8 parsed.v5_final_coefficients.val,
          .finalNonce parsed.v5_final_nonce] },
    { transcript with events := transcript.events ++
        [.absorb 19#u8 parsed.v5_final_coefficients.val,
          .finalNonce parsed.v5_final_nonce,
          .absorb 44#u8 [selector]] },
    { transcript with events := transcript.events ++
        expectedTailEvents parsed selector }, ?_⟩
  simp [aspis_core.transcript.Transcript.absorb,
    v5_cu_probe.check_and_absorb_real_v5_final_nonce,
    aspis_core.transcript.Transcript.challenge_queries_without_replacement,
    expectedTailEvents, Array.to_slice, Array.make, List.append_assoc]

/-- A successful generated tail therefore has both the previously proved
output dataflow and the exact transcript-call observation above. -/
theorem generated_tail_success_has_exact_calls_and_output
    (transcript : aspis_core.transcript.Transcript)
    (parsed : v5_cu_probe.ParsedProbeData)
    (selector : Std.U8)
    (polynomial : Array aspis_core.field.QM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (success :
      v5_cu_probe.derive_v5_complete_queries_for_selector_from_transcript
          transcript parsed selector = .ok (.Ok (polynomial, queries))) :
    (polynomial.val = [0#usize, 1#usize, 2#usize, 3#usize] ∧
      queries.val = transcript.sampledQueries.val ∧
      transcript.sampledQueries.val.length = 18 ∧ selector.val < 3) ∧
    ∃ afterFinalPolynomial afterNonce afterSelector afterQueries,
      aspis_core.transcript.Transcript.absorb transcript 19#u8
          parsed.v5_final_coefficients = .ok afterFinalPolynomial ∧
      v5_cu_probe.check_and_absorb_real_v5_final_nonce
          afterFinalPolynomial parsed.v5_final_nonce =
        .ok (.Ok (), afterNonce) ∧
      aspis_core.transcript.Transcript.absorb afterNonce 44#u8
          (Array.to_slice (Array.make 1#usize [selector])) =
        .ok afterSelector ∧
      aspis_core.transcript.Transcript.challenge_queries_without_replacement
          afterSelector 18#usize 131072#u32 64#usize =
        .ok (.Ok transcript.sampledQueries, afterQueries) ∧
      afterQueries.events =
        transcript.events ++ expectedTailEvents parsed selector := by
  exact ⟨
    generated_tail_success_returns_exact_decodes_and_queries
      transcript parsed selector polynomial queries success,
    exact_observed_tail_calls transcript parsed selector⟩

#print axioms exact_tail_constants
#print axioms generated_tail_success_returns_exact_decodes_and_queries
#print axioms exact_observed_tail_calls
#print axioms generated_tail_success_has_exact_calls_and_output

end AspisV5TranscriptTailUnchangedProof
