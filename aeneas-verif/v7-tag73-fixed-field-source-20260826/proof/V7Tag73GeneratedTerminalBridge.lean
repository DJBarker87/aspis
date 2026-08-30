import V7Tag73GeneratedReaderBridge
import V7Tag73GeneratedRelationFieldsBridge

/-!
# Literal generated terminal fixed-field bridge

This file isolates the three fixed-field reads performed inside translated
`finish_onefold_relation`: one inactive claim followed by the two circle-OOD
claims.  The first step is the exact two-iteration translated circle loop.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 40000

namespace AspisV7Tag73GeneratedTerminalBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73AeneasExactLoopTrace
open AspisV7Tag73GeneratedReaderBridge
open AspisV7Tag73GeneratedRelationFieldsBridge

theorem iterator_range_next_i32_some_spec
    (range : core.ops.range.Range Std.I32)
    (startsBeforeEnd : range.start.val < range.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 range
    ⦃ (item : Option Std.I32) (rangeAfter : core.ops.range.Range Std.I32) =>
      item = some range.start ∧
      rangeAfter.start.val = range.start.val + 1 ∧
      rangeAfter.end = range.end ⦄ := by
  simp only [core.iter.range.IteratorRange.next,
    core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked, bind_tc_ok,
    core.cmp.impls.PartialOrdI32.lt, startsBeforeEnd, decide_true,
    ↓reduceIte]
  have forwardInBounds :
      range.start.val + (1#usize).val ≤ IScalar.max .I32 := by
    have startBounds := range.start.hBounds
    have endBounds := range.end.hBounds
    scalar_tac
  simp only [forwardInBounds, ↓reduceDIte, bind_tc_ok, WP.spec_ok]
  simp [Std.I32.ofInt_val_eq]

theorem iterator_range_next_i32_none_spec
    (range : core.ops.range.Range Std.I32)
    (notBefore : ¬ range.start.val < range.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 range
    ⦃ (item : Option Std.I32) (rangeAfter : core.ops.range.Range Std.I32) =>
      item = none ∧ rangeAfter = range ⦄ := by
  simp only [core.iter.range.IteratorRange.next,
    core.iter.range.IScalarStep,
    core.iter.range.IScalarStep.forward_checked, bind_tc_ok,
    core.cmp.impls.PartialOrdI32.lt, notBefore, decide_false,
    Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  simp

structure TerminalReadEnvironment
    (QueryFold DeriveQueries Trace : Type) where
  queryFoldInst : core.ops.function.FnOnce QueryFold
    v6_transcript.V6QueryBatchView
    (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
      v6_onefold.V6WireError)
  deriveQueriesInst : core.ops.function.FnOnce DeriveQueries
    transcript.Transcript
    (core.result.Result
      (Array Std.U32 16#usize × Std.U8 × Std.Usize ×
        Array Std.U8 32#usize × transcript.Transcript)
      v6_transcript.V6TranscriptError)
  traceInst : core.ops.function.FnMut Trace
    v6_transcript.V6RelationDiagnosticPhase Unit
  workNonces : Array Std.U8 24#usize
  c1Frontier : Slice Std.U8
  c2Frontier : Slice Std.U8
  workBits : Array Std.U8 3#usize
  selector : Std.U8
  frontierNodeBytes : Std.Usize
  queryBatchLabels : Std.U8 × Std.U8
  shiftQueryBatchForTag73 : Bool
  exposeFinal256ToQueryFold : Bool
  deriveQueries : DeriveQueries
  checkPow : Bool
  semanticPoint : Array field.QM31 10#usize
  queryFold : QueryFold
  trace : Trace
  gamma : field.QM31
  kappa : field.QM31
  dPower : field.QM31
  gammaPowers : state_only_spend_query.StateOnlySpendQueryPowers

abbrev TerminalReadState :=
  core.ops.range.Range Std.I32 × transcript.Transcript ×
    v6_onefold.V6FixedFieldReader × field.QM31 ×
    sumcheck.WeightAccumulator

abbrev TerminalReadOutput :=
  Option (core.result.Result v6_transcript.V6VerifiedTranscript
    v6_transcript.V6TranscriptError)

def terminalReadMeasure (state : TerminalReadState) : Nat :=
  (state.1.end.val - state.1.start.val).toNat

def terminalReadBody {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalReadState) :
    Result (ControlFlow TerminalReadState TerminalReadOutput) :=
  v6_transcript.finish_onefold_relation_loop0_loop0.body
    environment.queryFoldInst environment.deriveQueriesInst
    environment.traceInst
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    environment.workNonces environment.c1Frontier environment.c2Frontier
    environment.workBits environment.selector environment.frontierNodeBytes
    environment.queryBatchLabels environment.shiftQueryBatchForTag73
    environment.exposeFinal256ToQueryFold environment.deriveQueries
    environment.checkPow environment.semanticPoint environment.queryFold
    environment.trace environment.gamma environment.kappa environment.dPower
    environment.gammaPowers state.1 state.2.1 state.2.2.1
    state.2.2.2.1 state.2.2.2.2

set_option maxHeartbeats 400000 in
theorem terminal_read_body_cont_has_exact_read
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (state next : TerminalReadState)
    (run : terminalReadBody environment state = .ok (.cont next)) :
    terminalReadMeasure next + 1 = terminalReadMeasure state ∧
    ∃ value,
      v6_onefold.V6FixedFieldReader.next_qm31 state.2.2.1 =
        .ok (.Ok value, next.2.2.1) := by
  unfold terminalReadBody at run
  unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepI32 state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      simp only [bind_tc_ok] at run
      repeat' first
        | (rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
           rcases run with ⟨_, _, run⟩)
        | (split at run)
        | (simp only [bind_tc_ok] at run)
        | (cases run)
    | some sample =>
      simp only [bind_tc_ok] at run
      generalize challengeRun :
          transcript.Transcript.challenge_secure_circle_point state.2.1 =
            challengeResult at run
      cases challengeResult with
      | fail error => simp at run
      | div => simp at run
      | ok challengePair =>
        rcases challengePair with ⟨challengeOutcome, transcriptAfterPoint⟩
        cases challengeOutcome with
        | Err sampleError =>
          simp [core.result.Result.map_err,
            v6_transcript.finish_onefold_relation.closure_4.Insts.CoreOpsFunctionFnOnceTupleCirclePointSampleErrorV6TranscriptError.call_once,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
        | Ok point =>
          simp only [core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize readRun :
              v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
                state.2.2.1 = readResult at run
          cases readResult with
          | fail error => simp at run
          | div => simp at run
          | ok readPair =>
            rcases readPair with ⟨readOutcome, readerAfter⟩
            cases readOutcome with
            | Err wireError =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
              rcases run with ⟨_, _, run⟩
              simp at run
            | Ok value =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              repeat' first
                | (rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
                   rcases run with ⟨_, _, run⟩)
                | (split at run)
                | (simp only [bind_tc_ok] at run)
                | (cases run)
              have startsBeforeEnd : state.1.start.val < state.1.end.val := by
                by_contra notBefore
                have noneSpec :=
                  iterator_range_next_i32_none_spec state.1 notBefore
                rw [rangeRun] at noneSpec
                simp only [WP.spec_ok] at noneSpec
                simp at noneSpec
              have rangeSpec :=
                iterator_range_next_i32_some_spec state.1 startsBeforeEnd
              rw [rangeRun] at rangeSpec
              simp only [WP.spec_ok] at rangeSpec
              rcases rangeSpec with ⟨_, startExact, endExact⟩
              constructor
              · unfold terminalReadMeasure
                rw [endExact, startExact]
                omega
              · refine ⟨value, ?_⟩
                simpa [
                  v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31]
                  using readRun

set_option maxHeartbeats 400000 in
theorem terminal_read_body_done_ok_measure_zero
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalReadState)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : terminalReadBody environment state =
      .ok (.done (some (.Ok verified)))) :
    terminalReadMeasure state = 0 := by
  unfold terminalReadBody at run
  unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepI32 state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      have notBefore : ¬ state.1.start.val < state.1.end.val := by
        intro startsBeforeEnd
        have someSpec :=
          iterator_range_next_i32_some_spec state.1 startsBeforeEnd
        rw [rangeRun] at someSpec
        simp only [WP.spec_ok] at someSpec
        simp at someSpec
      unfold terminalReadMeasure
      omega
    | some sample =>
      simp only [bind_tc_ok] at run
      repeat' first
        | (rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
           rcases run with ⟨_, _, run⟩)
        | (split at run)
        | (simp only [bind_tc_ok] at run)
        | (cases run)
      all_goals
        try casesm (core.result.Result core.convert.Infallible
          v6_transcript.V6TranscriptError)
        <;> try casesm (core.result.Result core.convert.Infallible
          v6_onefold.V6WireError)
      all_goals try casesm core.convert.Infallible
      all_goals simp_all [
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,
          v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
      all_goals
        casesm (core.result.Result core.convert.Infallible
          v6_onefold.V6WireError)
        <;> try casesm core.convert.Infallible
        <;> simp_all [
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
      all_goals simp at *

set_option maxHeartbeats 600000 in
theorem terminal_read_body_done_ok_exposes_fixed_tail
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalReadState)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : terminalReadBody environment state =
      .ok (.done (some (.Ok verified)))) :
    ∃ relationFields readerAfterRelation final256,
      ∃ transcriptBeforeFinal transcriptAfterFinal : transcript.Transcript,
      ∃ readerAfterFinal,
      v6_transcript.decode_compact_relation_fields
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          state.2.2.1 = .ok (.Ok relationFields, readerAfterRelation) ∧
      v6_transcript.decode_and_absorb_final256
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          transcriptBeforeFinal readerAfterRelation =
            .ok (.Ok final256, transcriptAfterFinal, readerAfterFinal) ∧
      v6_onefold.V6FixedFieldReader.finish readerAfterFinal = .ok (.Ok ()) := by
  have exhausted :=
    terminal_read_body_done_ok_measure_zero environment state verified run
  have notBefore : ¬ state.1.start.val < state.1.end.val := by
    unfold terminalReadMeasure at exhausted
    omega
  have rangeSpec := iterator_range_next_i32_none_spec state.1 notBefore
  obtain ⟨rangePair, rangeRun, itemExact, rangeAfterExact⟩ :=
    WP.spec_imp_exists rangeSpec
  rcases rangePair with ⟨item, rangeAfter⟩
  have itemExact' : item = none := by simpa using itemExact
  have rangeAfterExact' : rangeAfter = state.1 := by
    simpa using rangeAfterExact
  rw [itemExact', rangeAfterExact'] at rangeRun
  unfold terminalReadBody at run
  unfold v6_transcript.finish_onefold_relation_loop0_loop0.body at run
  rw [rangeRun] at run
  simp only [bind_tc_ok] at run
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨circleTracePair, circleTraceRun, run⟩
  rcases circleTracePair with ⟨_, traceAfterCircle⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨relationPair, relationRun, run⟩
  rcases relationPair with ⟨relationOutcome, readerAfterRelation⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨relationFlow, relationFlowRun, run⟩
  cases relationFlow with
  | Break residual =>
    cases residual with
    | Ok impossible => cases impossible
    | Err error =>
      simp [
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run
  | Continue relationFields =>
    have relationOutcomeExact : relationOutcome = .Ok relationFields := by
      cases relationOutcome with
      | Err wireError =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at relationFlowRun
      | Ok actual =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at relationFlowRun
        subst actual
        rfl
    simp only [bind_tc_ok] at run
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨relationTracePair, relationTraceRun, run⟩
    rcases relationTracePair with ⟨_, traceAfterRelation⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨firstCoefficient, firstCoefficientRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨firstPolynomial, firstPolynomialRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨transcriptAfterPolynomial, polynomialAbsorbRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨foldNonce, foldNonceRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨foldWorkBits, foldWorkBitsRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨foldWorkPair, foldWorkRun, run⟩
    rcases foldWorkPair with ⟨foldWorkOutcome, transcriptAfterFoldWork⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨foldWorkFlow, foldWorkFlowRun, run⟩
    cases foldWorkFlow with
    | Break residual =>
      cases residual with
      | Ok impossible => cases impossible
      | Err error =>
        simp [
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at run
    | Continue foldWorkValue =>
      simp only [bind_tc_ok] at run
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨alphaPair, alphaRun, run⟩
      rcases alphaPair with ⟨alphaOutcome, transcriptAfterAlpha⟩
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨mappedAlpha, mappedAlphaRun, run⟩
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨alphaFlow, alphaFlowRun, run⟩
      cases alphaFlow with
      | Break residual =>
        cases residual with
        | Ok impossible => cases impossible
        | Err error =>
          simp [
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Continue alpha0 =>
        simp only [bind_tc_ok] at run
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨alpha, alphaUpdateRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨q, qRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨runningClaimAfterFold, evaluateRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨weightsAfterFold, weightsFoldRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨roundTracePair, roundTraceRun, run⟩
        rcases roundTracePair with ⟨_, traceAfterRoundZero⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨finalPair, finalRun, run⟩
        rcases finalPair with
          ⟨finalOutcome, transcriptAfterFinal, readerAfterFinal⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨finalFlow, finalFlowRun, run⟩
        cases finalFlow with
        | Break residual =>
          cases residual with
          | Ok impossible => cases impossible
          | Err error =>
            simp [
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at run
        | Continue final256 =>
          have finalOutcomeExact : finalOutcome = .Ok final256 := by
            cases finalOutcome with
            | Err transcriptError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at finalFlowRun
            | Ok actual =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at finalFlowRun
              subst actual
              rfl
          simp only [bind_tc_ok] at run
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨finishOutcome, finishRun, run⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨finishFlow, finishFlowRun, run⟩
          cases finishFlow with
          | Break residual =>
            cases residual with
            | Ok impossible => cases impossible
            | Err error =>
              simp [
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
                at run
          | Continue finishUnit =>
            have finishOutcomeExact : finishOutcome = .Ok () := by
              cases finishOutcome with
              | Err wireError =>
                simp [core.result.Result.Insts.CoreOpsTry.branch] at finishFlowRun
              | Ok actual =>
                cases actual
                rfl
            rw [relationOutcomeExact] at relationRun
            rw [finalOutcomeExact] at finalRun
            rw [finishOutcomeExact] at finishRun
            exact ⟨relationFields, readerAfterRelation, final256,
              transcriptAfterAlpha, transcriptAfterFinal, readerAfterFinal,
              relationRun, finalRun, finishRun⟩

theorem terminal_read_body_cont_decreases
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (state next : TerminalReadState)
    (run : terminalReadBody environment state = .ok (.cont next)) :
    terminalReadMeasure next < terminalReadMeasure state := by
  have exactStep :=
    (terminal_read_body_cont_has_exact_read environment state next run).1
  omega

theorem terminal_read_loop_success_has_exact_trace
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalReadState)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : loop (terminalReadBody environment) state =
      .ok (some (.Ok verified))) :
    Nonempty (ExactLoopTrace (terminalReadBody environment) state
      (some (.Ok verified))) := by
  exact loop_success_has_exact_trace (terminalReadBody environment)
    terminalReadMeasure (terminal_read_body_cont_decreases environment)
    state (some (.Ok verified)) run

theorem terminal_read_trace_has_exact_reads
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    {state : TerminalReadState}
    {output : TerminalReadOutput}
    (trace : ExactLoopTrace (terminalReadBody environment) state
      output) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace state.2.2.1 values readerAfter ∧
      values.length = trace.contCount := by
  induction trace with
  | done equation =>
      exact ⟨_, [], .nil _, rfl⟩
  | cont equation tail inductionHypothesis =>
      obtain ⟨value, read⟩ :=
        (terminal_read_body_cont_has_exact_read environment _ _ equation).2
      obtain ⟨readerAfter, values, rest, lengthExact⟩ := inductionHypothesis
      refine ⟨readerAfter, value :: values, .cons read rest, ?_⟩
      change values.length + 1 = tail.contCount + 1
      omega

theorem terminal_read_trace_cont_count_exact
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    {state : TerminalReadState}
    {output : TerminalReadOutput}
    (trace : ExactLoopTrace (terminalReadBody environment) state
      output)
    (verified : v6_transcript.V6VerifiedTranscript)
    (hasAccepted : output = some (.Ok verified)) :
    trace.contCount = terminalReadMeasure state := by
  induction trace with
  | done equation =>
      rw [hasAccepted] at equation
      have exhausted :=
        terminal_read_body_done_ok_measure_zero environment _ verified equation
      simpa [ExactLoopTrace.contCount] using exhausted.symm
  | cont equation tail inductionHypothesis =>
      have stepExact :=
        (terminal_read_body_cont_has_exact_read environment _ _ equation).1
      simp only [ExactLoopTrace.contCount]
      rw [inductionHypothesis hasAccepted]
      omega

theorem terminal_read_trace_accepted_has_complete_fixed_tail
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    {state : TerminalReadState} {output : TerminalReadOutput}
    (trace : ExactLoopTrace (terminalReadBody environment) state output)
    (verified : v6_transcript.V6VerifiedTranscript)
    (hasAccepted : output = some (.Ok verified)) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace state.2.2.1 values readerAfter ∧
      values.length = trace.contCount + 280 ∧
      v6_onefold.V6FixedFieldReader.finish readerAfter = .ok (.Ok ()) := by
  induction trace with
  | done equation =>
    rw [hasAccepted] at equation
    obtain ⟨relationFields, readerAfterRelation, final256,
        transcriptBeforeFinal, transcriptAfterFinal, readerAfterFinal,
        relationRun, finalRun, finishRun⟩ :=
      terminal_read_body_done_ok_exposes_fixed_tail environment _ verified
        equation
    obtain ⟨relationValues, relationReads, relationLength,
        relationCanonical⟩ :=
      generated_decode_compact_relation_fields_success_reads_exactly_24
        _ _ relationFields relationRun
    obtain ⟨finalValues, finalReads, finalLength, finalCanonical⟩ :=
      generated_decode_and_absorb_final256_success_reads_exactly_256
        transcriptBeforeFinal transcriptAfterFinal readerAfterRelation
        readerAfterFinal final256 finalRun
    refine ⟨readerAfterFinal, relationValues ++ finalValues,
      SuccessfulFixedReaderTrace.append relationReads finalReads, ?_,
      finishRun⟩
    simp [ExactLoopTrace.contCount, relationLength, finalLength]
  | cont equation tail inductionHypothesis =>
    obtain ⟨value, read⟩ :=
      (terminal_read_body_cont_has_exact_read environment _ _ equation).2
    obtain ⟨readerAfter, values, rest, lengthExact, finishRun⟩ :=
      inductionHypothesis hasAccepted
    refine ⟨readerAfter, value :: values, .cons read rest, ?_, finishRun⟩
    simp only [List.length_cons, ExactLoopTrace.contCount]
    omega

theorem generated_terminal_ood_loop_success_reads_exactly_282_and_finishes
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (transcriptBefore : transcript.Transcript)
    (reader : v6_onefold.V6FixedFieldReader)
    (runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run :
      v6_transcript.finish_onefold_relation_loop0_loop0
        environment.queryFoldInst environment.deriveQueriesInst
        environment.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#i32, «end» := 2#i32 }
        transcriptBefore environment.workNonces environment.c1Frontier
        environment.c2Frontier environment.workBits environment.selector
        environment.frontierNodeBytes environment.queryBatchLabels
        environment.shiftQueryBatchForTag73
        environment.exposeFinal256ToQueryFold environment.deriveQueries reader
        environment.checkPow environment.semanticPoint environment.queryFold
        environment.trace environment.gamma environment.kappa
        environment.dPower environment.gammaPowers runningClaim weights =
          .ok (some (.Ok verified))) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 282 ∧
      (∀ value ∈ values, CanonicalGeneratedQM31 value) ∧
      v6_onefold.V6FixedFieldReader.finish readerAfter = .ok (.Ok ()) := by
  let state : TerminalReadState :=
    ({ start := 0#i32, «end» := 2#i32 }, transcriptBefore, reader,
      runningClaim, weights)
  have loopRun : loop (terminalReadBody environment) state =
      .ok (some (.Ok verified)) := by
    exact run
  obtain ⟨trace⟩ := terminal_read_loop_success_has_exact_trace
    environment state verified loopRun
  obtain ⟨readerAfter, values, reads, lengthExact, finishRun⟩ :=
    terminal_read_trace_accepted_has_complete_fixed_tail environment trace
      verified rfl
  refine ⟨readerAfter, values, reads, ?_,
    successful_trace_values_canonical reads, finishRun⟩
  rw [lengthExact,
    terminal_read_trace_cont_count_exact environment trace verified rfl]
  norm_num [state, terminalReadMeasure, Int.toNat]

theorem generated_terminal_ood_loop_success_reads_exactly_2
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalReadEnvironment QueryFold DeriveQueries Trace)
    (transcriptBefore : transcript.Transcript)
    (reader : v6_onefold.V6FixedFieldReader)
    (runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run :
      v6_transcript.finish_onefold_relation_loop0_loop0
        environment.queryFoldInst environment.deriveQueriesInst
        environment.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#i32, «end» := 2#i32 }
        transcriptBefore environment.workNonces environment.c1Frontier
        environment.c2Frontier environment.workBits environment.selector
        environment.frontierNodeBytes environment.queryBatchLabels
        environment.shiftQueryBatchForTag73
        environment.exposeFinal256ToQueryFold environment.deriveQueries reader
        environment.checkPow environment.semanticPoint environment.queryFold
        environment.trace environment.gamma environment.kappa
        environment.dPower environment.gammaPowers runningClaim weights =
          .ok (some (.Ok verified))) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 2 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  let state : TerminalReadState :=
    ({ start := 0#i32, «end» := 2#i32 }, transcriptBefore, reader,
      runningClaim, weights)
  have loopRun : loop (terminalReadBody environment) state =
      .ok (some (.Ok verified)) := by
    exact run
  obtain ⟨trace⟩ := terminal_read_loop_success_has_exact_trace
    environment state verified loopRun
  obtain ⟨readerAfter, values, reads, lengthExact⟩ :=
    terminal_read_trace_has_exact_reads environment trace
  refine ⟨readerAfter, values, reads, ?_,
    successful_trace_values_canonical reads⟩
  rw [lengthExact,
    terminal_read_trace_cont_count_exact environment trace verified rfl]
  norm_num [state, terminalReadMeasure, Int.toNat]

structure TerminalOuterEnvironment
    (QueryFold DeriveQueries Trace : Type) where
  terminal : TerminalReadEnvironment QueryFold DeriveQueries Trace
  transcriptBefore : transcript.Transcript
  reader : v6_onefold.V6FixedFieldReader
  inactiveRowGroups : Array Std.U8 64#usize
  inactiveGroupMasks : Slice Std.U16
  points : Array (Array field.QM31 10#usize) 3#usize
  pointScales : Array field.QM31 3#usize
  runningClaim : field.QM31

abbrev TerminalOuterState :=
  core.ops.range.Range Std.Usize × sumcheck.WeightAccumulator

def terminalOuterBody {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalOuterState) :
    Result (ControlFlow TerminalOuterState TerminalReadOutput) :=
  v6_transcript.finish_onefold_relation_loop0.body
    environment.terminal.queryFoldInst environment.terminal.deriveQueriesInst
    environment.terminal.traceInst
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    environment.transcriptBefore environment.terminal.workNonces
    environment.terminal.c1Frontier environment.terminal.c2Frontier
    environment.terminal.workBits environment.terminal.selector
    environment.terminal.frontierNodeBytes environment.terminal.queryBatchLabels
    environment.terminal.shiftQueryBatchForTag73
    environment.terminal.exposeFinal256ToQueryFold
    environment.terminal.deriveQueries environment.reader
    environment.inactiveRowGroups environment.inactiveGroupMasks
    environment.terminal.checkPow environment.terminal.semanticPoint
    environment.terminal.queryFold environment.terminal.trace
    environment.terminal.gamma environment.terminal.kappa environment.points
    environment.pointScales environment.terminal.dPower
    environment.terminal.gammaPowers environment.runningClaim
    state.1 state.2

def terminalOuterFinish {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (weights : sumcheck.WeightAccumulator) : Result TerminalReadOutput :=
  v6_transcript.finish_onefold_relation_loop0
    environment.terminal.queryFoldInst environment.terminal.deriveQueriesInst
    environment.terminal.traceInst
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    { start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
    environment.transcriptBefore environment.terminal.workNonces
    environment.terminal.c1Frontier environment.terminal.c2Frontier
    environment.terminal.workBits environment.terminal.selector
    environment.terminal.frontierNodeBytes environment.terminal.queryBatchLabels
    environment.terminal.shiftQueryBatchForTag73
    environment.terminal.exposeFinal256ToQueryFold
    environment.terminal.deriveQueries environment.reader
    environment.inactiveRowGroups environment.inactiveGroupMasks
    environment.terminal.checkPow environment.terminal.semanticPoint
    environment.terminal.queryFold environment.terminal.trace
    environment.terminal.gamma environment.terminal.kappa environment.points
    environment.pointScales environment.terminal.dPower
    environment.terminal.gammaPowers environment.runningClaim weights

def terminalOuterMeasure (state : TerminalOuterState) : Nat :=
  state.1.end.val - state.1.start.val

set_option maxHeartbeats 400000 in
theorem terminal_outer_body_cont_decreases
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (state next : TerminalOuterState)
    (run : terminalOuterBody environment state = .ok (.cont next)) :
    terminalOuterMeasure next < terminalOuterMeasure state := by
  unfold terminalOuterBody at run
  unfold v6_transcript.finish_onefold_relation_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      simp only [bind_tc_ok] at run
      repeat' first
        | (rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
           rcases run with ⟨_, _, run⟩)
        | (split at run)
        | (simp only [bind_tc_ok] at run)
        | (cases run)
      all_goals simp_all
    | some row =>
      simp only [bind_tc_ok] at run
      repeat' first
        | (rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
           rcases run with ⟨_, _, run⟩)
        | (split at run)
        | (simp only [bind_tc_ok] at run)
        | (cases run)
      all_goals
        try casesm (core.result.Result core.convert.Infallible
          v6_transcript.V6TranscriptError)
      all_goals try casesm core.convert.Infallible
      all_goals try simp_all [
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl) (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have startsBeforeEnd : state.1.start.val < state.1.end.val := by
        by_contra notBefore
        simp [notBefore] at conditional
      simp [startsBeforeEnd] at conditional
      rcases conditional with ⟨_, startExact⟩
      unfold terminalOuterMeasure
      rw [endExact, startExact]
      omega

theorem terminal_outer_loop_success_has_exact_trace
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalOuterState) (output : TerminalReadOutput)
    (run : loop (terminalOuterBody environment) state = .ok output) :
    Nonempty (ExactLoopTrace (terminalOuterBody environment) state output) := by
  exact loop_success_has_exact_trace (terminalOuterBody environment)
    terminalOuterMeasure (terminal_outer_body_cont_decreases environment)
    state output run

theorem terminal_outer_trace_exposes_final_body
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    {state : TerminalOuterState} {output : TerminalReadOutput}
    (trace : ExactLoopTrace (terminalOuterBody environment) state output) :
    ∃ finalState,
      terminalOuterBody environment finalState = .ok (.done output) := by
  induction trace with
  | done equation => exact ⟨_, equation⟩
  | cont _ _ inductionHypothesis => exact inductionHypothesis

set_option maxHeartbeats 400000 in
theorem terminal_outer_body_done_accepted_exposes_ood_loop
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (state : TerminalOuterState)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : terminalOuterBody environment state =
      .ok (.done (some (.Ok verified)))) :
    ∃ weightsAfter traceAfter,
      v6_transcript.finish_onefold_relation_loop0_loop0
        environment.terminal.queryFoldInst
        environment.terminal.deriveQueriesInst environment.terminal.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#i32, «end» := 2#i32 }
        environment.transcriptBefore environment.terminal.workNonces
        environment.terminal.c1Frontier environment.terminal.c2Frontier
        environment.terminal.workBits environment.terminal.selector
        environment.terminal.frontierNodeBytes
        environment.terminal.queryBatchLabels
        environment.terminal.shiftQueryBatchForTag73
        environment.terminal.exposeFinal256ToQueryFold
        environment.terminal.deriveQueries environment.reader
        environment.terminal.checkPow environment.terminal.semanticPoint
        environment.terminal.queryFold traceAfter environment.terminal.gamma
        environment.terminal.kappa environment.terminal.dPower
        environment.terminal.gammaPowers environment.runningClaim weightsAfter =
          .ok (some (.Ok verified)) := by
  unfold terminalOuterBody at run
  unfold v6_transcript.finish_onefold_relation_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangePair =>
    rcases rangePair with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      simp only [bind_tc_ok] at run
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨groupedPair, groupedRun, run⟩
      rcases groupedPair with ⟨groupedResult, weightsAfter⟩
      simp only [bind_tc_ok] at run
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨mappedResult, mappedRun, run⟩
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨flow, flowRun, run⟩
      cases flow with
      | Break residual =>
        simp only [bind_tc_ok] at run
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨converted, convertedRun, run⟩
        simp at run
      | Continue value =>
        simp only [bind_tc_ok] at run
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨tracePair, traceRun, run⟩
        rcases tracePair with ⟨_, traceAfter⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨pending, pendingRun, run⟩
        cases pending with
        | none => simp at run
        | some outcome =>
          simp at run
          subst outcome
          exact ⟨weightsAfter, traceAfter, pendingRun⟩
    | some row =>
      simp only [bind_tc_ok] at run
      repeat' first
        | (rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
           rcases run with ⟨_, _, run⟩)
        | (split at run)
        | (simp only [bind_tc_ok] at run)
        | (cases run)
      all_goals
        try casesm (core.result.Result core.convert.Infallible
          v6_transcript.V6TranscriptError)
      all_goals try casesm core.convert.Infallible
      all_goals simp_all [
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]

theorem generated_terminal_outer_success_reads_exactly_2
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (weights : sumcheck.WeightAccumulator)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run :
      v6_transcript.finish_onefold_relation_loop0
        environment.terminal.queryFoldInst
        environment.terminal.deriveQueriesInst environment.terminal.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
        environment.transcriptBefore environment.terminal.workNonces
        environment.terminal.c1Frontier environment.terminal.c2Frontier
        environment.terminal.workBits environment.terminal.selector
        environment.terminal.frontierNodeBytes
        environment.terminal.queryBatchLabels
        environment.terminal.shiftQueryBatchForTag73
        environment.terminal.exposeFinal256ToQueryFold
        environment.terminal.deriveQueries environment.reader
        environment.inactiveRowGroups environment.inactiveGroupMasks
        environment.terminal.checkPow environment.terminal.semanticPoint
        environment.terminal.queryFold environment.terminal.trace
        environment.terminal.gamma environment.terminal.kappa
        environment.points environment.pointScales environment.terminal.dPower
        environment.terminal.gammaPowers environment.runningClaim weights =
          .ok (some (.Ok verified))) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace environment.reader values readerAfter ∧
      values.length = 2 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  let state : TerminalOuterState :=
    ({ start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS },
      weights)
  have loopRun : loop (terminalOuterBody environment) state =
      .ok (some (.Ok verified)) := by
    exact run
  obtain ⟨trace⟩ := terminal_outer_loop_success_has_exact_trace
    environment state (some (.Ok verified)) loopRun
  obtain ⟨finalState, finalEquation⟩ :=
    terminal_outer_trace_exposes_final_body environment trace
  obtain ⟨weightsAfter, traceAfter, oodRun⟩ :=
    terminal_outer_body_done_accepted_exposes_ood_loop environment
      finalState verified finalEquation
  let innerEnvironment : TerminalReadEnvironment QueryFold DeriveQueries Trace :=
    { environment.terminal with trace := traceAfter }
  have exactOodRun :
      v6_transcript.finish_onefold_relation_loop0_loop0
        innerEnvironment.queryFoldInst innerEnvironment.deriveQueriesInst
        innerEnvironment.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#i32, «end» := 2#i32 }
        environment.transcriptBefore innerEnvironment.workNonces
        innerEnvironment.c1Frontier innerEnvironment.c2Frontier
        innerEnvironment.workBits innerEnvironment.selector
        innerEnvironment.frontierNodeBytes innerEnvironment.queryBatchLabels
        innerEnvironment.shiftQueryBatchForTag73
        innerEnvironment.exposeFinal256ToQueryFold
        innerEnvironment.deriveQueries environment.reader
        innerEnvironment.checkPow innerEnvironment.semanticPoint
        innerEnvironment.queryFold innerEnvironment.trace
        innerEnvironment.gamma innerEnvironment.kappa innerEnvironment.dPower
        innerEnvironment.gammaPowers environment.runningClaim weightsAfter =
          .ok (some (.Ok verified)) := by
    simpa [innerEnvironment] using oodRun
  exact generated_terminal_ood_loop_success_reads_exactly_2
    innerEnvironment environment.transcriptBefore environment.reader
    environment.runningClaim weightsAfter verified exactOodRun

theorem generated_terminal_outer_success_reads_exactly_282_and_finishes
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalOuterEnvironment QueryFold DeriveQueries Trace)
    (weights : sumcheck.WeightAccumulator)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run :
      v6_transcript.finish_onefold_relation_loop0
        environment.terminal.queryFoldInst
        environment.terminal.deriveQueriesInst environment.terminal.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
        environment.transcriptBefore environment.terminal.workNonces
        environment.terminal.c1Frontier environment.terminal.c2Frontier
        environment.terminal.workBits environment.terminal.selector
        environment.terminal.frontierNodeBytes
        environment.terminal.queryBatchLabels
        environment.terminal.shiftQueryBatchForTag73
        environment.terminal.exposeFinal256ToQueryFold
        environment.terminal.deriveQueries environment.reader
        environment.inactiveRowGroups environment.inactiveGroupMasks
        environment.terminal.checkPow environment.terminal.semanticPoint
        environment.terminal.queryFold environment.terminal.trace
        environment.terminal.gamma environment.terminal.kappa
        environment.points environment.pointScales environment.terminal.dPower
        environment.terminal.gammaPowers environment.runningClaim weights =
          .ok (some (.Ok verified))) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace environment.reader values readerAfter ∧
      values.length = 282 ∧
      (∀ value ∈ values, CanonicalGeneratedQM31 value) ∧
      v6_onefold.V6FixedFieldReader.finish readerAfter = .ok (.Ok ()) := by
  let state : TerminalOuterState :=
    ({ start := 0#usize, «end» := v6_onefold.V6_POINT_CLAIM_ROWS },
      weights)
  have loopRun : loop (terminalOuterBody environment) state =
      .ok (some (.Ok verified)) := by
    exact run
  obtain ⟨trace⟩ := terminal_outer_loop_success_has_exact_trace
    environment state (some (.Ok verified)) loopRun
  obtain ⟨finalState, finalEquation⟩ :=
    terminal_outer_trace_exposes_final_body environment trace
  obtain ⟨weightsAfter, traceAfter, oodRun⟩ :=
    terminal_outer_body_done_accepted_exposes_ood_loop environment
      finalState verified finalEquation
  let innerEnvironment : TerminalReadEnvironment QueryFold DeriveQueries Trace :=
    { environment.terminal with trace := traceAfter }
  have exactOodRun :
      v6_transcript.finish_onefold_relation_loop0_loop0
        innerEnvironment.queryFoldInst innerEnvironment.deriveQueriesInst
        innerEnvironment.traceInst
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 0#i32, «end» := 2#i32 }
        environment.transcriptBefore innerEnvironment.workNonces
        innerEnvironment.c1Frontier innerEnvironment.c2Frontier
        innerEnvironment.workBits innerEnvironment.selector
        innerEnvironment.frontierNodeBytes innerEnvironment.queryBatchLabels
        innerEnvironment.shiftQueryBatchForTag73
        innerEnvironment.exposeFinal256ToQueryFold
        innerEnvironment.deriveQueries environment.reader
        innerEnvironment.checkPow innerEnvironment.semanticPoint
        innerEnvironment.queryFold innerEnvironment.trace
        innerEnvironment.gamma innerEnvironment.kappa innerEnvironment.dPower
        innerEnvironment.gammaPowers environment.runningClaim weightsAfter =
          .ok (some (.Ok verified)) := by
    simpa [innerEnvironment] using oodRun
  exact generated_terminal_ood_loop_success_reads_exactly_282_and_finishes
    innerEnvironment environment.transcriptBefore environment.reader
    environment.runningClaim weightsAfter verified exactOodRun

structure TerminalFinishEnvironment
    (QueryFold DeriveQueries Trace : Type) where
  queryFoldInst : core.ops.function.FnOnce QueryFold
    v6_transcript.V6QueryBatchView
    (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
      v6_onefold.V6WireError)
  deriveQueriesInst : core.ops.function.FnOnce DeriveQueries
    transcript.Transcript
    (core.result.Result
      (Array Std.U32 16#usize × Std.U8 × Std.Usize ×
        Array Std.U8 32#usize × transcript.Transcript)
      v6_transcript.V6TranscriptError)
  traceInst : core.ops.function.FnMut Trace
    v6_transcript.V6RelationDiagnosticPhase Unit
  transcriptBefore : transcript.Transcript
  workNonces : Array Std.U8 24#usize
  c1Frontier : Slice Std.U8
  c2Frontier : Slice Std.U8
  workBits : Array Std.U8 3#usize
  selector : Std.U8
  frontierNodeBytes : Std.Usize
  queryBatchLabels : Std.U8 × Std.U8
  shiftQueryBatchForTag73 : Bool
  exposeFinal256ToQueryFold : Bool
  deriveQueries : DeriveQueries
  reader : v6_onefold.V6FixedFieldReader
  inactiveRowGroups : Array Std.U8 64#usize
  inactiveGroupMasks : Slice Std.U16
  checkPow : Bool
  semanticPoint : Array field.QM31 10#usize
  pointClaims : Array (Array field.QM31 29#usize) 3#usize
  queryFold : QueryFold
  trace : Trace

def terminalFinish {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalFinishEnvironment QueryFold DeriveQueries Trace) :
    Result (core.result.Result v6_transcript.V6VerifiedTranscript
      v6_transcript.V6TranscriptError) :=
  v6_transcript.finish_onefold_relation
    environment.queryFoldInst environment.deriveQueriesInst
    environment.traceInst
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    environment.transcriptBefore environment.workNonces environment.c1Frontier
    environment.c2Frontier environment.workBits environment.selector
    environment.frontierNodeBytes environment.queryBatchLabels
    environment.shiftQueryBatchForTag73 environment.exposeFinal256ToQueryFold
    environment.deriveQueries environment.reader environment.inactiveRowGroups
    environment.inactiveGroupMasks environment.checkPow
    environment.semanticPoint environment.pointClaims environment.queryFold
    environment.trace

set_option maxHeartbeats 600000 in
theorem terminal_finish_success_exposes_initial_read_and_outer
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalFinishEnvironment QueryFold DeriveQueries Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : terminalFinish environment = .ok (.Ok verified)) :
    ∃ inactiveClaim readerAfterInitial,
      ∃ outerEnvironment : TerminalOuterEnvironment QueryFold DeriveQueries Trace,
      ∃ initialWeights,
      v6_onefold.V6FixedFieldReader.next_qm31 environment.reader =
        .ok (.Ok inactiveClaim, readerAfterInitial) ∧
      outerEnvironment.reader = readerAfterInitial ∧
      terminalOuterFinish outerEnvironment initialWeights =
        .ok (some (.Ok verified)) := by
  unfold terminalFinish at run
  unfold v6_transcript.finish_onefold_relation at run
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨traceStartPair, traceStartRun, run⟩
  rcases traceStartPair with ⟨_, traceAfterStart⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨batchNonce, batchNonceRun, run⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨batchWorkBits, batchWorkBitsRun, run⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨workPair, workRun, run⟩
  rcases workPair with ⟨workOutcome, transcriptAfterWork⟩
  rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
  rcases run with ⟨workFlow, workFlowRun, run⟩
  cases workFlow with
  | Break residual =>
    cases residual with
    | Ok impossible => cases impossible
    | Err error =>
      simp [
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run
  | Continue workValue =>
    simp only [bind_tc_ok] at run
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨gammaPair, gammaRun, run⟩
    rcases gammaPair with ⟨gammaOutcome, transcriptAfterGamma⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨mappedGamma, mappedGammaRun, run⟩
    rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
    rcases run with ⟨gammaFlow, gammaFlowRun, run⟩
    cases gammaFlow with
    | Break residual =>
      cases residual with
      | Ok impossible => cases impossible
      | Err error =>
        simp [
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at run
    | Continue gamma =>
      simp only [bind_tc_ok] at run
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨readPair, readRun, run⟩
      rcases readPair with ⟨readOutcome, readerAfterInitial⟩
      rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
      rcases run with ⟨readFlow, readFlowRun, run⟩
      cases readFlow with
      | Break residual =>
        cases residual with
        | Ok impossible => cases impossible
        | Err error =>
          simp [
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
            at run
      | Continue inactiveClaim =>
        have readOutcomeExact : readOutcome = .Ok inactiveClaim := by
          cases readOutcome with
          | Err wireError =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at readFlowRun
          | Ok actualValue =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at readFlowRun
            subst actualValue
            rfl
        simp only [bind_tc_ok] at run
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨mutableSlicePair, mutableSliceRun, run⟩
        rcases mutableSlicePair with ⟨mutableSlice, putMutableSlice⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨writtenSlice, writtenSliceRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨inactiveSlice, inactiveSliceRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨transcriptAfterInactive, absorbRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨kappaPair, kappaRun, run⟩
        rcases kappaPair with ⟨kappaOutcome, transcriptAfterKappa⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨mappedKappa, mappedKappaRun, run⟩
        rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
        rcases run with ⟨kappaFlow, kappaFlowRun, run⟩
        cases kappaFlow with
        | Break residual =>
          cases residual with
          | Ok impossible => cases impossible
          | Err error =>
            simp [
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from] at run
        | Continue kappa =>
          simp only [bind_tc_ok] at run
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨points, pointsRun, run⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨kappaSquared, squareRun, run⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨claimPowerTriple, claimPowerRun, run⟩
          rcases claimPowerTriple with
            ⟨combinedClaims, gammaPowers, dPower⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨batchedClaims, batchedClaimsRun, run⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨runningClaim, runningClaimRun, run⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨initialWeights, initialWeightsRun, run⟩
          rw [AspisV7Tag73AeneasExactLoopTrace.bind_eq_ok_iff] at run
          rcases run with ⟨pending, outerRun, run⟩
          cases pending with
          | none => simp at run
          | some outcome =>
            have outcomeExact : outcome = .Ok verified := by
              simpa using run
            subst outcome
            let terminalEnvironment :
                TerminalReadEnvironment QueryFold DeriveQueries Trace := {
              queryFoldInst := environment.queryFoldInst
              deriveQueriesInst := environment.deriveQueriesInst
              traceInst := environment.traceInst
              workNonces := environment.workNonces
              c1Frontier := environment.c1Frontier
              c2Frontier := environment.c2Frontier
              workBits := environment.workBits
              selector := environment.selector
              frontierNodeBytes := environment.frontierNodeBytes
              queryBatchLabels := environment.queryBatchLabels
              shiftQueryBatchForTag73 := environment.shiftQueryBatchForTag73
              exposeFinal256ToQueryFold :=
                environment.exposeFinal256ToQueryFold
              deriveQueries := environment.deriveQueries
              checkPow := environment.checkPow
              semanticPoint := environment.semanticPoint
              queryFold := environment.queryFold
              trace := traceAfterStart
              gamma := gamma
              kappa := kappa
              dPower := dPower
              gammaPowers := gammaPowers
            }
            let outerEnvironment :
                TerminalOuterEnvironment QueryFold DeriveQueries Trace := {
              terminal := terminalEnvironment
              transcriptBefore := transcriptAfterKappa
              reader := readerAfterInitial
              inactiveRowGroups := environment.inactiveRowGroups
              inactiveGroupMasks := environment.inactiveGroupMasks
              points := points
              pointScales := Array.make 3#usize
                [ field.QM31.ONE, kappa, kappaSquared ]
              runningClaim := runningClaim
            }
            have exactOuterRun :
                v6_transcript.finish_onefold_relation_loop0
                  terminalEnvironment.queryFoldInst
                  terminalEnvironment.deriveQueriesInst
                  terminalEnvironment.traceInst
                  v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                  { start := 0#usize,
                    «end» := v6_onefold.V6_POINT_CLAIM_ROWS }
                  transcriptAfterKappa terminalEnvironment.workNonces
                  terminalEnvironment.c1Frontier terminalEnvironment.c2Frontier
                  terminalEnvironment.workBits terminalEnvironment.selector
                  terminalEnvironment.frontierNodeBytes
                  terminalEnvironment.queryBatchLabels
                  terminalEnvironment.shiftQueryBatchForTag73
                  terminalEnvironment.exposeFinal256ToQueryFold
                  terminalEnvironment.deriveQueries readerAfterInitial
                  environment.inactiveRowGroups environment.inactiveGroupMasks
                  terminalEnvironment.checkPow terminalEnvironment.semanticPoint
                  terminalEnvironment.queryFold terminalEnvironment.trace gamma
                  kappa points
                  (Array.make 3#usize
                    [ field.QM31.ONE, kappa, kappaSquared ])
                  dPower gammaPowers runningClaim initialWeights =
                    .ok (some (.Ok verified)) := by
              simpa [terminalEnvironment] using outerRun
            have firstRead :
                v6_onefold.V6FixedFieldReader.next_qm31 environment.reader =
                  .ok (.Ok inactiveClaim, readerAfterInitial) := by
              rw [readOutcomeExact] at readRun
              simpa [
                v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31]
                using readRun
            exact ⟨inactiveClaim, readerAfterInitial, outerEnvironment,
              initialWeights, firstRead, rfl,
              by simpa [terminalOuterFinish, outerEnvironment,
                terminalEnvironment] using exactOuterRun⟩

theorem generated_terminal_success_reads_exactly_3
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalFinishEnvironment QueryFold DeriveQueries Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : terminalFinish environment = .ok (.Ok verified)) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace environment.reader values readerAfter ∧
      values.length = 3 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  obtain ⟨inactiveClaim, readerAfterInitial, outerEnvironment,
      initialWeights, firstRead, readerExact, outerRun⟩ :=
    terminal_finish_success_exposes_initial_read_and_outer environment
      verified run
  obtain ⟨readerAfter, outerValues, outerReads, outerLength,
      outerCanonical⟩ :=
    generated_terminal_outer_success_reads_exactly_2
      outerEnvironment initialWeights verified
      (by simpa [terminalOuterFinish] using outerRun)
  rw [readerExact] at outerReads
  let completeReads : SuccessfulFixedReaderTrace environment.reader
      (inactiveClaim :: outerValues) readerAfter :=
    .cons firstRead outerReads
  exact ⟨readerAfter, inactiveClaim :: outerValues, completeReads,
    by simp [outerLength], successful_trace_values_canonical completeReads⟩

theorem generated_terminal_success_reads_exactly_283_and_finishes
    {QueryFold DeriveQueries Trace : Type}
    (environment : TerminalFinishEnvironment QueryFold DeriveQueries Trace)
    (verified : v6_transcript.V6VerifiedTranscript)
    (run : terminalFinish environment = .ok (.Ok verified)) :
    ∃ readerAfter values,
      SuccessfulFixedReaderTrace environment.reader values readerAfter ∧
      values.length = 283 ∧
      (∀ value ∈ values, CanonicalGeneratedQM31 value) ∧
      v6_onefold.V6FixedFieldReader.finish readerAfter = .ok (.Ok ()) := by
  obtain ⟨inactiveClaim, readerAfterInitial, outerEnvironment,
      initialWeights, firstRead, readerExact, outerRun⟩ :=
    terminal_finish_success_exposes_initial_read_and_outer environment
      verified run
  obtain ⟨readerAfter, outerValues, outerReads, outerLength,
      outerCanonical, finishRun⟩ :=
    generated_terminal_outer_success_reads_exactly_282_and_finishes
      outerEnvironment initialWeights verified
      (by simpa [terminalOuterFinish] using outerRun)
  rw [readerExact] at outerReads
  let completeReads : SuccessfulFixedReaderTrace environment.reader
      (inactiveClaim :: outerValues) readerAfter :=
    .cons firstRead outerReads
  exact ⟨readerAfter, inactiveClaim :: outerValues, completeReads,
    by simp [outerLength], successful_trace_values_canonical completeReads,
    finishRun⟩

#print axioms terminal_read_body_cont_has_exact_read
#print axioms terminal_read_body_done_ok_measure_zero
#print axioms terminal_read_body_done_ok_exposes_fixed_tail
#print axioms terminal_read_loop_success_has_exact_trace
#print axioms terminal_read_trace_has_exact_reads
#print axioms terminal_read_trace_cont_count_exact
#print axioms terminal_read_trace_accepted_has_complete_fixed_tail
#print axioms generated_terminal_ood_loop_success_reads_exactly_2
#print axioms generated_terminal_ood_loop_success_reads_exactly_282_and_finishes
#print axioms terminal_outer_body_cont_decreases
#print axioms terminal_outer_loop_success_has_exact_trace
#print axioms terminal_outer_trace_exposes_final_body
#print axioms terminal_outer_body_done_accepted_exposes_ood_loop
#print axioms generated_terminal_outer_success_reads_exactly_2
#print axioms generated_terminal_outer_success_reads_exactly_282_and_finishes
#print axioms terminal_finish_success_exposes_initial_read_and_outer
#print axioms generated_terminal_success_reads_exactly_3
#print axioms generated_terminal_success_reads_exactly_283_and_finishes

end AspisV7Tag73GeneratedTerminalBridge
