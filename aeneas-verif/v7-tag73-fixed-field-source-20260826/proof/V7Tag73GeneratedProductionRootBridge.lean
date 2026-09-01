import V7Tag73GeneratedSemanticBridge
import V7Tag73GeneratedPointClaimsBridge
import V7Tag73GeneratedTerminalBridge

/-!
# Literal production-root fixed-field composition

This file composes the three generated decoder bridges through the actual
translated `verify_v7_compact_transcript_and_relation_prepared_with_hiding_context`
control flow.  Its public theorem starts only from literal production success
and constructs one ordered 641-value reader trace followed by the literal
successful `finish` call.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV7Tag73GeneratedProductionRootBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73GeneratedReaderBridge
open AspisV7Tag73GeneratedSemanticBridge
open AspisV7Tag73GeneratedPointClaimsBridge
open AspisV7Tag73GeneratedRelationFieldsBridge
open AspisV7Tag73GeneratedTerminalBridge

set_option maxHeartbeats 1200000 in
theorem generated_production_root_success_reads_exactly_641_and_finishes
    {TerminalCheck QueryFold : Type}
    (terminalCheckInst : core.ops.function.FnOnce TerminalCheck
      v6_transcript.V6SemanticView Bool)
    (queryFoldInst : core.ops.function.FnOnce QueryFold
      v6_transcript.V6QueryBatchView
      (core.result.Result v6_query_batch.V6AuthenticatedQueryBatch
        v6_onefold.V6WireError))
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : v7_onefold.V7CompactOneFoldWire)
    (context : v6_transcript.V6TranscriptContext)
    (hidingContext : state_only_hiding.StateOnlyHidingContext)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16)
    (checkPow : Bool) (terminalCheck : TerminalCheck)
    (queryFold : QueryFold)
    (output : v6_transcript.V6VerifiedTranscript)
    (run :
      v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
        terminalCheckInst queryFoldInst hash wire context hidingContext
        inactiveRowGroups inactiveGroupMasks checkPow terminalCheck queryFold =
          .ok (.Ok output)) :
    ∃ initial final values,
      v6_onefold.V6FixedFieldReader.new wire.fixed_fields_packed =
        .ok (.Ok initial) ∧
      SuccessfulFixedReaderTrace initial values final ∧
      v6_onefold.V6FixedFieldReader.finish final = .ok (.Ok ()) ∧
      wire.fixed_fields_packed.val.length = 9936 ∧
      values.length = 641 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  unfold
    v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
    at run
  generalize newRun :
      v6_onefold.V6FixedFieldReader.new wire.fixed_fields_packed =
        newResult at run
  cases newResult with
  | fail error => simp at run
  | div => simp at run
  | ok newOutcome =>
    cases newOutcome with
    | Err wireError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,
        v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
        at run
    | Ok initial =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
      generalize beginRun :
          v6_transcript.begin_v7_compact_transcript_with_hiding_context
            hash context wire hidingContext = beginResult at run
      cases beginResult with
      | fail error => simp at run
      | div => simp at run
      | ok beginOutcome =>
        cases beginOutcome with
        | Err transcriptError =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
        | Ok beginValue =>
          rcases beginValue with ⟨transcript1, lambda, chi, batching⟩
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize semanticRun :
              v6_transcript.verify_compact_semantic_sumcheck
                v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                transcript1 initial = semanticResult at run
          cases semanticResult with
          | fail error => simp at run
          | div => simp at run
          | ok semanticTriple =>
            rcases semanticTriple with ⟨semanticOutcome, transcript2, reader1⟩
            cases semanticOutcome with
            | Err transcriptError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
            | Ok semanticValue =>
              rcases semanticValue with
                ⟨eta, semanticPoint, semanticTerminal⟩
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              generalize pointRun :
                  v6_transcript.decode_and_absorb_point_claims
                    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                    transcript2 reader1 = pointResult at run
              cases pointResult with
              | fail error => simp at run
              | div => simp at run
              | ok pointTriple =>
                rcases pointTriple with ⟨pointOutcome, transcript3, reader2⟩
                cases pointOutcome with
                | Err transcriptError =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at run
                | Ok pointClaims =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok] at run
                  generalize terminalCheckRun :
                      terminalCheckInst.call_once terminalCheck
                        ({ lambda := lambda, chi := chi, batching := batching,
                           eta := eta, point := semanticPoint,
                           terminal_claim := semanticTerminal,
                           point_claims := pointClaims } :
                          v6_transcript.V6SemanticView) = terminalResult at run
                  cases terminalResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok terminalAccepted =>
                    cases terminalAccepted with
                    | false => simp at run
                    | true =>
                      let traceInst :=
                        v6_transcript.verify_v7_compact_transcript_and_relation_prepared_with_hiding_context.closure.Insts.CoreOpsFunctionFnMutTupleV6RelationDiagnosticPhaseTuple
                          terminalCheckInst queryFoldInst
                      let deriveInst :=
                        v6_transcript.finish_v7_compact_relation.closure.Insts.CoreOpsFunctionFnOnceTupleSharedTranscriptResultTupleArrayU3216U8UsizeArrayU832TranscriptV6TranscriptError
                          queryFoldInst traceInst
                      let terminalEnvironment :
                          TerminalFinishEnvironment QueryFold Unit Unit := {
                        queryFoldInst := queryFoldInst
                        deriveQueriesInst := deriveInst
                        traceInst := traceInst
                        transcriptBefore := transcript3
                        workNonces := wire.work_nonces
                        c1Frontier := wire.c1_frontier
                        c2Frontier := wire.c2_frontier
                        workBits := Array.make 3#usize [
                          v7_onefold.V7_COMPACT_BATCH_WORK_BITS,
                          v7_onefold.V7_COMPACT_FOLD_WORK_BITS,
                          v7_onefold.V7_COMPACT_FINAL_WORK_BITS]
                        selector := 0#u8
                        frontierNodeBytes := v7_merkle208.V7_MERKLE_DIGEST_BYTES
                        queryBatchLabels :=
                          (transcript.label.V7_QUERY_BATCH_CHALLENGE,
                            transcript.label.V7_QUERY_BATCH_CLAIM)
                        shiftQueryBatchForTag73 := true
                        exposeFinal256ToQueryFold := false
                        deriveQueries := ()
                        reader := reader2
                        inactiveRowGroups := inactiveRowGroups
                        inactiveGroupMasks := inactiveGroupMasks
                        checkPow := checkPow
                        semanticPoint := semanticPoint
                        pointClaims := pointClaims
                        queryFold := queryFold
                        trace := () }
                      have terminalRun :
                          terminalFinish terminalEnvironment =
                            .ok (.Ok output) := by
                        simpa [terminalFinish, terminalEnvironment, traceInst,
                          deriveInst,
                          v6_transcript.finish_v7_compact_relation] using run
                      obtain ⟨semanticValues, semanticReads, semanticLength,
                          semanticCanonical⟩ :=
                        generated_semantic_success_reads_exactly_271
                          transcript1 transcript2 initial reader1 eta
                          semanticPoint semanticTerminal semanticRun
                      obtain ⟨pointValues, pointReads, pointLength,
                          pointCanonical⟩ :=
                        generated_decode_and_absorb_point_claims_success_reads_exactly_87
                          transcript2 transcript3 reader1 reader2 pointClaims
                          pointRun
                      obtain ⟨final, terminalValues, terminalReads,
                          terminalLength, terminalCanonical, finishRun⟩ :=
                        generated_terminal_success_reads_exactly_283_and_finishes
                          terminalEnvironment output terminalRun
                      let completeReads : SuccessfulFixedReaderTrace initial
                          (semanticValues ++ (pointValues ++ terminalValues))
                          final :=
                        SuccessfulFixedReaderTrace.append semanticReads
                          (SuccessfulFixedReaderTrace.append pointReads
                            terminalReads)
                      have completeFacts :=
                        complete_successful_trace_has_exact_641_canonical_values
                          wire.fixed_fields_packed initial final
                          (semanticValues ++ (pointValues ++ terminalValues))
                          newRun completeReads finishRun
                      exact ⟨initial, final,
                        semanticValues ++ (pointValues ++ terminalValues),
                        rfl, completeReads, finishRun, completeFacts.1,
                        completeFacts.2.1, completeFacts.2.2⟩

#print axioms generated_production_root_success_reads_exactly_641_and_finishes

end AspisV7Tag73GeneratedProductionRootBridge
