import V7CompactSemanticSourceBridge

/-!
# Exact fixed-field read schedule for the Tag-73 compact semantic verifier

This layer projects the literal Aeneas loop states back to the production
`V6FixedFieldReader`.  It records every successful `next_qm31` call in order;
no independently supplied message vector is introduced.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CompactSemanticFullGenerated
open V7CompactSemanticSourceBridge

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace V7CompactSemanticReadSchedule

/-- Rebuild the production reader from its six scalar state components. -/
def rawReader (slice : Slice Std.U8) (byteIndex : Std.Usize)
    (buffer : Std.U64) (bufferedBits : Std.U8) (remaining : Std.Usize) :
    RawReader := {
  packed := {
    bytes := slice
    byte_index := byteIndex
    buffer := buffer
    buffered_bits := bufferedBits }
  remaining := remaining
}

def innerStateReader : InnerState → RawReader
  | (_, slice, byteIndex, buffer, bufferedBits, remaining, _, _, _) =>
      rawReader slice byteIndex buffer bufferedBits remaining

def innerOutputReader : InnerOutput → RawReader
  | (_, slice, byteIndex, buffer, bufferedBits, remaining, _, _, _, _) =>
      rawReader slice byteIndex buffer bufferedBits remaining

def outerStateReader : OuterState → RawReader
  | (_, _, slice, byteIndex, buffer, bufferedBits, remaining, _, _, _) =>
      rawReader slice byteIndex buffer bufferedBits remaining

def outerOutputReader : OuterOutput → RawReader
  | (_, slice, byteIndex, buffer, bufferedBits, remaining, _) =>
      rawReader slice byteIndex buffer bufferedBits remaining

/-- Exact ordered sequence of successful production fixed-field reads. -/
inductive FieldReadTrace : RawReader → List RawQM31 → RawReader → Prop
  | nil (reader : RawReader) : FieldReadTrace reader [] reader
  | cons {before after final : RawReader} {value : RawQM31}
      {tail : List RawQM31}
      (read :
        V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
            before = .ok (.Ok value, after))
      (rest : FieldReadTrace after tail final) :
      FieldReadTrace before (value :: tail) final

theorem FieldReadTrace.append
    {first middle final : RawReader} {left right : List RawQM31}
    (leftTrace : FieldReadTrace first left middle)
    (rightTrace : FieldReadTrace middle right final) :
    FieldReadTrace first (left ++ right) final := by
  induction leftTrace with
  | nil => simpa using rightTrace
  | cons read rest inductionHypothesis =>
      simpa using FieldReadTrace.cons read (inductionHypothesis rightTrace)

theorem FieldReadTrace.length_remaining
    {first final : RawReader} {values : List RawQM31}
    (trace : FieldReadTrace first values final)
    (oneStep : ∀ before value after,
      V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
          before = .ok (.Ok value, after) →
      after.remaining.val + 1 = before.remaining.val) :
    final.remaining.val + values.length = first.remaining.val := by
  induction trace with
  | nil => simp
  | cons read rest inductionHypothesis =>
      simp only [List.length_cons]
      have step := oneStep _ _ _ read
      omega

private theorem inner_body_cont_exposes_exact_read_core
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option AcceptedPayload)
    (state next : InnerState)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.cont next)) :
    ∃ value,
      V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
          (innerStateReader state) =
        .ok (.Ok value, innerStateReader next) := by
  have decreases := inner_body_continue_decreases transcript point runningClaim
    round pendingReturn state next run
  have active : state.1.start.val < state.1.end.val := by
    unfold innerMeasure at decreases
    omega
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  have nextSpec :=
    core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
  obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
      nextEnd⟩ := WP.spec_imp_exists nextSpec
  rw [optionExact] at nextRun
  rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
  rcases run with ⟨iteratorPair, iteratorRun, run⟩
  have iteratorPairExact : iteratorPair = (some state.1.start, nextIter) :=
    Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
  subst iteratorPair
  generalize pairExact : (some state.1.start, nextIter) = pair at run
  rcases pair with ⟨actualOption, actualIter⟩
  cases actualOption with
  | none => simp at pairExact
  | some sent =>
      simp only [Prod.mk.injEq, Option.some.injEq] at pairExact
      simp at run
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨coefficient, coefficientRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨readerPair, readerRun, run⟩
      rcases readerPair with ⟨readerResult, fields⟩
      simp at run
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨flow, flowRun, run⟩
      cases flow with
      | Break residual =>
          simp at run
          repeat'
            (rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
             rcases run with ⟨_, _, run⟩
             simp at run)
      | Continue value =>
          simp at run
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨updatedPolynomial, updatedPolynomialRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨scaledOffset, scaledOffsetRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨framedOffset, framedOffsetRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with
            ⟨⟨framedWindow, putFramedWindow⟩, framedWindowRun, run⟩
          simp_all
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with
            ⟨⟨qm31Slot, putQm31Slot⟩, qm31SlotRun, run⟩
          simp_all
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨encodedSlot, encodedSlotRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb0, limb0Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨acc0, acc0Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨sum0, sum0Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨tail1, tail1Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb1, limb1Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨acc1, acc1Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨sum1, sum1Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨tail2, tail2Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb2, limb2Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨acc2, acc2Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨sum2, sum2Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨tail3, tail3Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb3, limb3Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨acc3, acc3Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨sum3, sum3Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨tail4, tail4Run, run⟩
          simp at run
          subst next
          cases readerResult with
          | Ok readValue =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
              subst value
              refine ⟨readValue, ?_⟩
              simpa [innerStateReader, rawReader] using readerRun
          | Err wireError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun

/-- Every continue edge of the exact generated inner body is caused by one
successful fixed-field read, and the next loop state carries exactly the
reader returned by that call. -/
theorem inner_body_cont_exposes_exact_read
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option AcceptedPayload)
    (state next : InnerState)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.cont next)) :
    ∃ value,
      V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
          (innerStateReader state) =
        .ok (.Ok value, innerStateReader next) :=
  inner_body_cont_exposes_exact_read_core transcript point runningClaim round
    pendingReturn state next run
/- Superseded broad automation retained temporarily for source-diff
provenance; it is not part of the compiled theorem surface.
  have decreases := inner_body_continue_decreases transcript point runningClaim
    round pendingReturn state next run
  have active : state.1.start.val < state.1.end.val := by
    unfold innerMeasure at decreases
    omega
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  have nextSpec :=
    core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
  obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, _, _⟩ :=
    WP.spec_imp_exists nextSpec
  rw [optionExact] at nextRun
  rw [nextRun] at run
  simp only [bind_tc_ok] at run
  simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader, rawReader,
    V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd]
  repeat'
    (split at run <;>
      try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader, rawReader,
        V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd])
  all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
  all_goals try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader,
    rawReader]
  repeat'
    (split at run <;>
      try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader, rawReader])
  all_goals try casesm
    (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
  all_goals try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader,
    rawReader]
  repeat'
    (split at run <;>
      try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader, rawReader])
  all_goals try casesm
    (Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
  all_goals try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader,
    rawReader]
  repeat'
    (split at run <;>
      try simp_all [Bind.bind, Aeneas.Std.bind, innerStateReader, rawReader])
  all_goals try subst next
  all_goals try casesm
    (core.result.Result RawQM31 v6_onefold.V6WireError)
  all_goals try simp_all [innerStateReader, rawReader]
  all_goals try simp_all
    [core.result.Result.Insts.CoreOpsTry.branch, innerStateReader, rawReader]
  all_goals exact ⟨_, by assumption⟩
-/

private theorem inner_body_done_status_one_reader_unchanged_core
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option AcceptedPayload)
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (normal : innerStatus output = 1#u32) :
    innerOutputReader output = innerStateReader state := by
  have exhausted := inner_body_done_status_one_exhausted transcript point
    runningClaim round pendingReturn state output run normal
  have inactive : state.1.start.val ≥ state.1.end.val := by
    unfold innerMeasure at exhausted
    omega
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  have nextSpec :=
    core.iter.range.IteratorRange.next_Usize_none_spec state.1 inactive
  obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
    WP.spec_imp_exists nextSpec
  rw [optionExact, nextExact] at nextRun
  rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
  rcases run with ⟨iteratorPair, iteratorRun, run⟩
  have iteratorPairExact : iteratorPair = (none, state.1) :=
    Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
  subst iteratorPair
  generalize pairExact : (none, state.1) = pair at run
  rcases pair with ⟨actualOption, actualIter⟩
  cases actualOption with
  | none =>
      simp at pairExact
      subst actualIter
      simp at run
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨tailLimb0, tailLimb0Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨reduced0, reduced0Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨tailLimb1, tailLimb1Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨reduced1, reduced1Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨cm0, cm0Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨tailLimb2, tailLimb2Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨reduced2, reduced2Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨tailLimb3, tailLimb3Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨reduced3, reduced3Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨cm1, cm1Run, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨adjustedClaim, adjustedClaimRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨completedPolynomial, completedPolynomialRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨boundarySum, boundarySumRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨boundaryEqual, boundaryEqualRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨asserted, assertedRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨framedSlice, framedSliceRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨absorbedTranscript, absorbedTranscriptRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with
        ⟨⟨challengeResult, challengedTranscript⟩, challengeRun, run⟩
      simp_all
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨mappedChallenge, mappedChallengeRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨challengeFlow, challengeFlowRun, run⟩
      cases challengeFlow with
      | Continue challenge =>
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨nextClaim, nextClaimRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨nextPoint, nextPointRun, run⟩
          simp at run
          subst output
          rfl
      | Break residual =>
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨convertedError, convertedErrorRun, run⟩
          simp at run
          subst output
          simp [innerStatus] at normal
  | some sent => simp at pairExact

/-- The status-one `done` edge is the exhausted inner range and performs no
field read, so its output carries the unchanged reader. -/
theorem inner_body_done_status_one_reader_unchanged
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option AcceptedPayload)
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (normal : innerStatus output = 1#u32) :
    innerOutputReader output = innerStateReader state :=
  inner_body_done_status_one_reader_unchanged_core transcript point runningClaim
    round pendingReturn state output run normal
/- Superseded broad automation retained temporarily for source-diff
provenance; it is not part of the compiled theorem surface.
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, _, _⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at run
    simp only [bind_tc_ok] at run
    simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
      Aeneas.Std.bind, V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd]
    repeat'
      (split at run <;>
        try simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
          Aeneas.Std.bind,
          V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
    all_goals try simp_all [innerOutputReader, innerStateReader, rawReader,
      Bind.bind, Aeneas.Std.bind]
    repeat'
      (split at run <;>
        try simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
          Aeneas.Std.bind])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
    all_goals try simp_all [innerOutputReader, innerStateReader, rawReader,
      Bind.bind, Aeneas.Std.bind,
      V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd,
      V7CompactSemanticSourceBridge.let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
          Aeneas.Std.bind,
          V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd,
          V7CompactSemanticSourceBridge.let_prod_eq_fst_snd])
    all_goals try subst output
    all_goals try simp_all
      [innerStatus, innerOutputReader, innerStateReader, rawReader]
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
      Aeneas.Std.bind,
      V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd]
    repeat'
      (split at run <;>
        try simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
          Aeneas.Std.bind,
          V7CompactSemanticSourceBridge.prod_rec_eq_fst_snd])
    all_goals try casesm (_ × RawTranscript)
    all_goals try simp_all [innerOutputReader, innerStateReader, rawReader,
      Bind.bind, Aeneas.Std.bind]
    repeat'
      (split at run <;>
        try simp_all [innerOutputReader, innerStateReader, rawReader, Bind.bind,
          Aeneas.Std.bind])
    all_goals try subst output
    all_goals try simp_all
      [innerStatus, innerOutputReader, innerStateReader, rawReader]
-/

/-- An exact normal inner trace is therefore precisely an ordered trace of
successful field reads, one per continue edge. -/
theorem inner_trace_status_one_exposes_exact_reads
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option AcceptedPayload)
    (state : InnerState) (output : InnerOutput)
    (trace : ExactLoopTrace
      (innerBody transcript point runningClaim round pendingReturn)
      state output)
    (normal : innerStatus output = 1#u32) :
    ∃ values,
      values.length = trace.contCount ∧
        FieldReadTrace (innerStateReader state) values
          (innerOutputReader output) := by
  induction trace with
  | done equation =>
      have readerExact := inner_body_done_status_one_reader_unchanged
        transcript point runningClaim round pendingReturn _ _ equation normal
      refine ⟨[], rfl, ?_⟩
      rw [readerExact]
      exact .nil _
  | cont equation tail inductionHypothesis =>
      obtain ⟨value, read⟩ := inner_body_cont_exposes_exact_read transcript point
        runningClaim round pendingReturn _ _ equation
      obtain ⟨values, lengthExact, rest⟩ := inductionHypothesis normal
      refine ⟨value :: values, ?_, .cons read rest⟩
      simp [ExactLoopTrace.contCount, lengthExact]

private theorem outer_body_cont_exposes_exact_round_reads_core
    (zero eta : RawQM31) (state next : OuterState)
    (run : outerBody zero eta state = .ok (.cont next)) :
    ∃ values,
      values.length = 27 ∧
        FieldReadTrace (outerStateReader state) values
          (outerStateReader next) := by
  have decreases := outer_body_continue_decreases zero eta state next run
  have active : state.1.start.val < state.1.end.val := by
    unfold outerMeasure at decreases
    omega
  unfold outerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    at run
  have nextSpec :=
    core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
  obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
      nextEnd⟩ := WP.spec_imp_exists nextSpec
  rw [optionExact] at nextRun
  rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
  rcases run with ⟨iteratorPair, iteratorRun, run⟩
  have iteratorPairExact : iteratorPair = (some state.1.start, nextIter) :=
    Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
  subst iteratorPair
  generalize pairExact : (some state.1.start, nextIter) = pair at run
  rcases pair with ⟨actualOption, actualIter⟩
  cases actualOption with
  | none => simp at pairExact
  | some round =>
      simp only [Prod.mk.injEq, Option.some.injEq] at pairExact
      simp at run
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨framedSlot, framedSlotRun, run⟩
      rcases framedSlot with ⟨framedByte, putFramedByte⟩
      simp at run
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨roundByte, roundByteRun, run⟩
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨readerPair, readerRun, run⟩
      rcases readerPair with ⟨readerResult, fields⟩
      simp at run
      rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
      rcases run with ⟨flow, flowRun, run⟩
      cases flow with
      | Break residual =>
          simp at run
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨convertedError, convertedErrorRun, run⟩
          simp at run
      | Continue value =>
          simp at run
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨polynomial, polynomialRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨q, qRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨framedWindowPair, framedWindowRun, run⟩
          rcases framedWindowPair with ⟨framedWindow, putFramedWindow⟩
          simp_all
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨encodedWindow, encodedWindowRun, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb0, limb0Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨doubled0, doubled0Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb1, limb1Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨doubled1, doubled1Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb2, limb2Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨doubled2, doubled2Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨limb3, limb3Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨doubled3, doubled3Run, run⟩
          rw [V7CompactSemanticSourceBridge.bind_eq_ok_iff] at run
          rcases run with ⟨innerOutput, innerRun, run⟩
          rcases innerOutput with
            ⟨transcript1, s3, i17, i18, i19, i20, point1,
              runningClaim1, pendingReturn1, status⟩
          simp at run
          split at run
          · simp at run
            subst next
            obtain ⟨innerTrace⟩ := inner_loop_success_has_exact_trace
              (run := innerRun)
            obtain ⟨innerValues, innerLength, innerReads⟩ :=
              inner_trace_status_one_exposes_exact_reads
                (trace := innerTrace) (normal := rfl)
            have innerCount := inner_trace_status_one_contCount_eq_measure
              (trace := innerTrace) (normal := rfl)
            cases readerResult with
            | Ok readValue =>
                simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
                subst value
                have firstRead :
                    V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
                        (outerStateReader state) =
                      .ok (.Ok readValue,
                        rawReader fields.packed.bytes fields.packed.byte_index
                          fields.packed.buffer fields.packed.buffered_bits
                          fields.remaining) := by
                  simpa [outerStateReader, rawReader] using readerRun
                refine ⟨readValue :: innerValues, ?_, .cons firstRead ?_⟩
                · simp [innerLength, innerCount, innerMeasure,
                    V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_SENT_VALUES]
                · change FieldReadTrace
                    (rawReader fields.packed.bytes fields.packed.byte_index
                      fields.packed.buffer fields.packed.buffered_bits
                      fields.remaining)
                    innerValues (rawReader s3 i17 i18 i19 i20) at innerReads
                  exact innerReads
            | Err wireError =>
                simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
          · cases pendingReturn1 <;> simp at run

/-- Every continue edge of the generated ten-round loop consumes exactly one
round-zero coefficient followed by the exact 26-value inner trace.  Thus one
and only one semantic round exposes 27 ordered production field reads. -/
theorem outer_body_cont_exposes_exact_round_reads
    (zero eta : RawQM31) (state next : OuterState)
    (run : outerBody zero eta state = .ok (.cont next)) :
    ∃ values,
      values.length = 27 ∧
        FieldReadTrace (outerStateReader state) values
          (outerStateReader next) :=
  outer_body_cont_exposes_exact_round_reads_core zero eta state next run
/- Superseded broad automation retained temporarily for source-diff
provenance; it is not part of the compiled theorem surface.
  unfold outerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, _, _⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at run
    simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader, rawReader]

    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
          rawReader])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try casesm
      (_ × (_ → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
      rawReader]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
          rawReader])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
      rawReader]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
          rawReader])
    all_goals try casesm (RawTranscript × _)
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
      rawReader]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
          rawReader])
    all_goals try casesm (Slice Std.U8 × Std.Usize × _)
    all_goals try casesm (Std.Usize × Std.U64 × _)
    all_goals try casesm (Std.U64 × Std.U8 × _)
    all_goals try casesm (Std.U8 × Std.Usize × _)
    all_goals try casesm
      (Std.Usize × Std.Array RawQM31 10#usize × _)
    all_goals try casesm
      (Std.Array RawQM31 10#usize × RawQM31 × _)
    all_goals try casesm (RawQM31 × Option AcceptedPayload × Std.U32)
    all_goals try casesm (Option AcceptedPayload × Std.U32)
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
      rawReader]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader,
          rawReader])
    all_goals try subst next
    all_goals try simp_all [outerStateReader, rawReader]
    all_goals try casesm
      (core.result.Result RawQM31 v6_onefold.V6WireError)
    all_goals try simp_all
      [core.result.Result.Insts.CoreOpsTry.branch, outerStateReader,
        innerStateReader, rawReader]
    all_goals
      obtain ⟨innerTrace⟩ := inner_loop_success_has_exact_trace
        (run := by assumption)
    all_goals
      obtain ⟨innerValues, innerLength, innerReads⟩ :=
        inner_trace_status_one_exposes_exact_reads
          (trace := innerTrace) (normal := rfl)
    all_goals
      have innerCount := inner_trace_status_one_contCount_eq_measure
        (trace := innerTrace) (normal := rfl)
    all_goals
      refine ⟨_ :: innerValues, ?_, .cons (by assumption) innerReads⟩
    all_goals
      simp [innerLength, innerCount, innerMeasure,
        V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_SENT_VALUES]
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    simp_all [Bind.bind, Aeneas.Std.bind, outerStateReader, rawReader]
-/

/-- An accepted terminal edge entered with no pending payload is the exhausted
outer range.  That branch performs no field read and returns the same reader. -/
theorem outer_body_done_ok_from_none_reader_unchanged
    (zero eta : RawQM31) (state : OuterState) (output : OuterOutput)
    (run : outerBody zero eta state = .ok (.done output))
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : outerOutputPending output = some (.Ok accepted))
    (noPending : outerStatePending state = none) :
    outerOutputReader output = outerStateReader state := by
  have exhausted := outer_body_done_ok_from_none_exhausted zero eta state
    output run accepted hasAccepted noPending
  have inactive : ¬ state.1.start.val < state.1.end.val := by
    unfold outerMeasure at exhausted
    omega
  unfold outerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    at run
  have nextSpec :=
    core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
  obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
    WP.spec_imp_exists nextSpec
  rw [optionExact, nextExact] at nextRun
  rw [nextRun] at run
  simp_all [Bind.bind, Aeneas.Std.bind, outerOutputReader, outerStateReader,
    rawReader, outerOutputPending, outerStatePending]
  subst output
  simp

/-- An accepted finite outer trace entered with no pending payload is exactly
the concatenation of its 27-read rounds and a zero-read exhausted terminal
edge. -/
theorem outer_trace_from_none_exposes_exact_reads
    (zero eta : RawQM31) (state : OuterState) (output : OuterOutput)
    (trace : ExactLoopTrace (outerBody zero eta) state output)
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : outerOutputPending output = some (.Ok accepted))
    (noPending : outerStatePending state = none) :
    ∃ values,
      values.length = 27 * trace.contCount ∧
        FieldReadTrace (outerStateReader state) values
          (outerOutputReader output) := by
  induction trace with
  | done equation =>
      have readerExact := outer_body_done_ok_from_none_reader_unchanged
        zero eta _ _ equation accepted hasAccepted noPending
      refine ⟨[], by simp [ExactLoopTrace.contCount], ?_⟩
      rw [readerExact]
      exact .nil _
  | @cont current nextState finalOutput equation tail inductionHypothesis =>
      have nextNoPending : outerStatePending nextState = none := by
        rw [outer_body_cont_preserves_pending zero eta current nextState
          equation, noPending]
      obtain ⟨roundValues, roundLength, roundReads⟩ :=
        outer_body_cont_exposes_exact_round_reads zero eta current nextState
          equation
      obtain ⟨tailValues, tailLength, tailReads⟩ :=
        inductionHypothesis hasAccepted nextNoPending
      refine ⟨roundValues ++ tailValues, ?_, roundReads.append tailReads⟩
      simp only [List.length_append, ExactLoopTrace.contCount]
      omega

/-- The accepted generated top-level verifier consumes exactly its initial
claim plus ten ordered 27-field semantic rounds: 271 production reads in all. -/
theorem accepted_execution_exposes_exact_271_reads
    {inputTranscript outputTranscript : RawTranscript}
    {inputFields outputFields : RawReader}
    {eta : RawQM31} {point : Array RawQM31 10#usize}
    {terminalClaim : RawQM31}
    (execution : AcceptedMainExecution inputTranscript outputTranscript
      inputFields outputFields eta point terminalClaim) :
    ∃ values,
      values.length = 271 ∧
        FieldReadTrace inputFields values outputFields := by
  obtain ⟨outerTrace⟩ := execution.outerTrace
  obtain ⟨outerValues, outerLength, outerReads⟩ :=
    outer_trace_from_none_exposes_exact_reads execution.zero
      execution.prefixEta _ _ outerTrace (eta, point, terminalClaim) rfl rfl
  have outerCount := outer_trace_from_none_contCount_eq_measure
    execution.zero execution.prefixEta _ _ outerTrace
      (eta, point, terminalClaim) rfl rfl
  refine ⟨execution.initialClaim :: outerValues, ?_, ?_⟩
  · simp [outerLength, outerCount, outerMeasure,
      V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_ROUNDS]
  · exact .cons execution.initialRead outerReads

/-- Direct accepted-entrypoint form: the 271-read schedule is extracted from
the translated production call itself, with no execution witness supplied by
the caller. -/
theorem accepted_main_exposes_exact_271_reads
    (inputTranscript outputTranscript : RawTranscript)
    (inputFields outputFields : RawReader)
    (eta : RawQM31) (point : Array RawQM31 10#usize)
    (terminalClaim : RawQM31)
    (run :
      V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck
          inputTranscript inputFields =
        .ok (.Ok (eta, point, terminalClaim), outputTranscript,
          outputFields)) :
    ∃ values,
      values.length = 271 ∧
        FieldReadTrace inputFields values outputFields := by
  obtain ⟨execution⟩ := accepted_main_exposes_exact_outer_trace
    inputTranscript outputTranscript inputFields outputFields eta point
      terminalClaim run
  exact accepted_execution_exposes_exact_271_reads execution

#print axioms FieldReadTrace.append
#print axioms inner_body_cont_exposes_exact_read
#print axioms inner_body_done_status_one_reader_unchanged
#print axioms inner_trace_status_one_exposes_exact_reads
#print axioms outer_body_cont_exposes_exact_round_reads
#print axioms outer_body_done_ok_from_none_reader_unchanged
#print axioms outer_trace_from_none_exposes_exact_reads
#print axioms accepted_execution_exposes_exact_271_reads
#print axioms accepted_main_exposes_exact_271_reads

end V7CompactSemanticReadSchedule
