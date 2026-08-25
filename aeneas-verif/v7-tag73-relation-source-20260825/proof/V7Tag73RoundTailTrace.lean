import V7Tag73RoundTailSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7Tag73FinishRelationUnrolledGenerated

namespace V7Tag73RoundTailTrace

/-- The exact arithmetic and transcript-challenge calls reached by one
successful execution of the Aeneas-extracted fixed rounds 1--3 tail.  Every
field is a call made by that same execution; no separately chosen relation
run or helper-result premise is admitted. -/
structure AcceptedRoundTailTrace
    {Trace : Type}
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript : _root_.transcript.Transcript)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (alpha : Array field.QM31 4#usize) (runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (foldedValues : Array field.QM31 256#usize)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (gamma kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (selector compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (semanticPoint : Array field.QM31 10#usize)
    (queryBatchChallenge : field.QM31)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (trace : Trace) (verified : v6_transcript.V6VerifiedTranscript) : Type where
  relationRowOne : Array field.QM31 6#usize
  polynomialOne : Array field.QM31 7#usize
  transcriptAbsorbOne : _root_.transcript.Transcript
  transcriptChallengeOne : _root_.transcript.Transcript
  alphaOne : field.QM31
  alphaReadOne : field.QM31
  alphaAfterOne : Array field.QM31 4#usize
  runningClaimOne : field.QM31
  weightsFoldOne : sumcheck.WeightAccumulator
  weightsMergeOne : sumcheck.WeightAccumulator
  foldedValuesOne : Array field.QM31 256#usize
  relationRowOneSuccess : relationFields.index_usize 1#usize = ok relationRowOne
  polynomialOneSuccess :
    v6_transcript.decode_compact_relation_polynomial relationRowOne runningClaim =
      ok polynomialOne
  absorbOneSuccess :
    v6_transcript.absorb_compact_relation_polynomial transcript 1#usize
        polynomialOne = ok transcriptAbsorbOne
  challengeOneSuccess :
    transcriptAbsorbOne.challenge_qm31 =
      ok (core.result.Result.Ok alphaOne, transcriptChallengeOne)
  alphaUpdateOneSuccess : alpha.update 1#usize alphaOne = ok alphaAfterOne
  alphaReadOneSuccess : alphaAfterOne.index_usize 1#usize = ok alphaReadOne
  evaluateOneSuccess :
    sumcheck.evaluate polynomialOne alphaReadOne = ok runningClaimOne
  weightsFoldOneSuccess :
    weights.fold_deferred_relation_arity4 alphaReadOne = ok weightsFoldOne
  weightsMergeOneSuccess :
    weightsFoldOne.merge_equal_multilinear_components 0#usize 2#usize =
      ok (true, weightsMergeOne)
  foldedValuesOneSuccess :
    v6_transcript.fold_values_prefix 256#usize foldedValues alphaReadOne =
      ok foldedValuesOne

  relationRowTwo : Array field.QM31 6#usize
  polynomialTwo : Array field.QM31 7#usize
  transcriptAbsorbTwo : _root_.transcript.Transcript
  transcriptChallengeTwo : _root_.transcript.Transcript
  alphaTwo : field.QM31
  alphaReadTwo : field.QM31
  alphaAfterTwo : Array field.QM31 4#usize
  runningClaimTwo : field.QM31
  weightsFoldTwo : sumcheck.WeightAccumulator
  foldedValuesTwo : Array field.QM31 256#usize
  relationRowTwoSuccess : relationFields.index_usize 2#usize = ok relationRowTwo
  polynomialTwoSuccess :
    v6_transcript.decode_compact_relation_polynomial relationRowTwo
        runningClaimOne = ok polynomialTwo
  absorbTwoSuccess :
    v6_transcript.absorb_compact_relation_polynomial transcriptChallengeOne
        2#usize polynomialTwo = ok transcriptAbsorbTwo
  challengeTwoSuccess :
    transcriptAbsorbTwo.challenge_qm31 =
      ok (core.result.Result.Ok alphaTwo, transcriptChallengeTwo)
  alphaUpdateTwoSuccess : alphaAfterOne.update 2#usize alphaTwo = ok alphaAfterTwo
  alphaReadTwoSuccess : alphaAfterTwo.index_usize 2#usize = ok alphaReadTwo
  evaluateTwoSuccess :
    sumcheck.evaluate polynomialTwo alphaReadTwo = ok runningClaimTwo
  weightsFoldTwoSuccess :
    weightsMergeOne.fold_deferred_relation_arity4 alphaReadTwo = ok weightsFoldTwo
  foldedValuesTwoSuccess :
    v6_transcript.fold_values_prefix 64#usize foldedValuesOne alphaReadTwo =
      ok foldedValuesTwo

  relationRowThree : Array field.QM31 6#usize
  polynomialThree : Array field.QM31 7#usize
  transcriptAbsorbThree : _root_.transcript.Transcript
  alphaThree : field.QM31
  alphaReadThree : field.QM31
  alphaAfterThree : Array field.QM31 4#usize
  runningClaimThree : field.QM31
  weightsFoldThree : sumcheck.WeightAccumulator
  foldedValuesThree : Array field.QM31 256#usize
  relationRowThreeSuccess : relationFields.index_usize 3#usize = ok relationRowThree
  polynomialThreeSuccess :
    v6_transcript.decode_compact_relation_polynomial relationRowThree
        runningClaimTwo = ok polynomialThree
  absorbThreeSuccess :
    v6_transcript.absorb_compact_relation_polynomial transcriptChallengeTwo
        3#usize polynomialThree = ok transcriptAbsorbThree
  challengeThreeSuccess :
    ∃ transcriptAfterThree,
      transcriptAbsorbThree.challenge_qm31 =
        ok (core.result.Result.Ok alphaThree, transcriptAfterThree)
  alphaUpdateThreeSuccess :
    alphaAfterTwo.update 3#usize alphaThree = ok alphaAfterThree
  alphaReadThreeSuccess :
    alphaAfterThree.index_usize 3#usize = ok alphaReadThree
  evaluateThreeSuccess :
    sumcheck.evaluate polynomialThree alphaReadThree = ok runningClaimThree
  weightsFoldThreeSuccess :
    weightsFoldTwo.fold_deferred_relation_arity4 alphaReadThree = ok weightsFoldThree
  foldedValuesThreeSuccess :
    v6_transcript.fold_values_prefix 16#usize foldedValuesTwo alphaReadThree =
      ok foldedValuesThree

  terminalPrefix : Slice field.QM31
  terminalDot : field.QM31
  terminalPrefixSuccess :
    core.array.Array.index
        (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31))
        foldedValuesThree { «end» := 4#usize } = ok terminalPrefix
  terminalDotSuccess :
    weightsFoldThree.dot terminalPrefix = ok terminalDot
  terminalNeSuccess :
    core.cmp.PartialEq.ne.trait_default
        field.QM31.Insts.CoreCmpPartialEqQM31 terminalDot runningClaimThree =
      ok false
  terminalExact : terminalDot = runningClaimThree
  foldedQuerySum : field.QM31
  foldedQuerySumSuccess :
    (do
      let iterator ←
        Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
          authenticatedQueries.values
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
        (BuiltinFnMut (field.QM31 × field.QM31) field.QM31) iterator
        field.QM31.ZERO (fun pair => field.QM31.add pair.1 pair.2)) =
      ok foldedQuerySum
  outputExact : verified = {
    gamma
    kappa
    alpha := alphaAfterThree
    queries
    selector
    compact_counter := compactCounter
    frontier_nodes := frontierNodes
    semantic_point := semanticPoint
    query_batch_challenge := queryBatchChallenge
    folded_query_sum := foldedQuerySum
    transcript_state_after_queries := transcriptStateAfterQueries
  }

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem match_bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (match input with
      | .ok value => next value
      | .fail error => .fail error
      | .div => .div) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp

private theorem bind_pair_eq_ok_iff {Left Right Output : Type}
    (input : Result (Left × Right))
    (next : Left → Right → Result Output) (output : Output) :
    (do
      let (left, right) ← input
      next left right) = ok output ↔
      ∃ left right, input = ok (left, right) ∧
        next left right = ok output := by
  cases input with
  | ok pair => cases pair <;> simp [Bind.bind, Aeneas.Std.bind]
  | fail error => simp [Bind.bind, Aeneas.Std.bind]
  | div => simp [Bind.bind, Aeneas.Std.bind]

private theorem match_bind_pair_eq_ok_iff {Left Right Output : Type}
    (input : Result (Left × Right))
    (next : Left → Right → Result Output) (output : Output) :
    (match input with
      | .ok (left, right) => next left right
      | .fail error => .fail error
      | .div => .div) = ok output ↔
      ∃ left right, input = ok (left, right) ∧
        next left right = ok output := by
  cases input with
  | ok pair => cases pair <;> simp
  | fail error => simp
  | div => simp

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- Successful execution of the actual extracted tail exposes all three
ordered relation rounds, the exact terminal dot equality, the query-value
fold, and the exact returned transcript from that same run. -/
theorem accepted_tail_exposes_exact_trace
    {Trace : Type}
    (traceInst : core.ops.function.FnMut Trace
      v6_transcript.V6RelationDiagnosticPhase Unit)
    (transcript : _root_.transcript.Transcript)
    (relationFields : Array (Array field.QM31 6#usize) 4#usize)
    (alpha : Array field.QM31 4#usize) (runningClaim : field.QM31)
    (weights : sumcheck.WeightAccumulator)
    (foldedValues : Array field.QM31 256#usize)
    (authenticatedQueries : v6_query_batch.V6AuthenticatedQueryBatch)
    (gamma kappa : field.QM31) (queries : Array Std.U32 16#usize)
    (selector compactCounter : Std.U8) (frontierNodes : Std.Usize)
    (semanticPoint : Array field.QM31 10#usize)
    (queryBatchChallenge : field.QM31)
    (transcriptStateAfterQueries : Array Std.U8 32#usize)
    (trace : Trace) (verified : v6_transcript.V6VerifiedTranscript)
    (hrun :
      v6_transcript.finish_onefold_relation_round_tail_extraction traceInst
        transcript relationFields alpha runningClaim weights foldedValues
        authenticatedQueries gamma kappa queries selector compactCounter
        frontierNodes semanticPoint queryBatchChallenge
        transcriptStateAfterQueries trace =
          ok (core.result.Result.Ok verified)) :
    Nonempty (AcceptedRoundTailTrace traceInst transcript relationFields alpha
      runningClaim weights foldedValues authenticatedQueries gamma kappa
      queries selector compactCounter frontierNodes semanticPoint
      queryBatchChallenge transcriptStateAfterQueries trace verified) := by
  simp only [v6_transcript.finish_onefold_relation_round_tail_extraction] at hrun
  rw [bind_eq_ok_iff] at hrun
  rcases hrun with ⟨relationRowOne, hrelationRowOne, hrun⟩
  rw [bind_eq_ok_iff] at hrun
  rcases hrun with ⟨polynomialOne, hpolynomialOne, hrun⟩
  rw [bind_eq_ok_iff] at hrun
  rcases hrun with ⟨transcriptAbsorbOne, habsorbOne, hrun⟩
  rw [bind_pair_eq_ok_iff] at hrun
  rcases hrun with ⟨challengeResultOne, transcriptChallengeOne,
    hchallengeOne, hrun⟩
  cases challengeResultOne with
  | Err error =>
      simp [core.result.Result.map_err,
        v6_transcript.finish_onefold_relation_round_tail_extraction.closure.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, Bind.bind, Aeneas.Std.bind] at hrun
  | Ok alphaOne =>
      simp only [core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch,
        Bind.bind, Aeneas.Std.bind] at hrun
      cases halphaUpdateOne : alpha.update 1#usize alphaOne <;>
        simp [halphaUpdateOne] at hrun
      rename_i alphaAfterOne
      cases halphaReadOne : alphaAfterOne.index_usize 1#usize <;>
        simp [halphaReadOne] at hrun
      rename_i alphaReadOne
      cases hevaluateOne : sumcheck.evaluate polynomialOne alphaReadOne <;>
        simp [hevaluateOne] at hrun
      rename_i runningClaimOne
      cases htracePolynomialOne : traceInst.call_mut trace
          v6_transcript.V6RelationDiagnosticPhase.RoundOnePolynomial <;>
        simp [htracePolynomialOne] at hrun
      rename_i tracePolynomialOnePair
      rcases tracePolynomialOnePair with
        ⟨tracePolynomialOneUnit, tracePolynomialOne⟩
      cases hweightsFoldOne :
          weights.fold_deferred_relation_arity4 alphaReadOne <;>
        simp [hweightsFoldOne] at hrun
      rename_i weightsFoldOne
      cases hweightsMergeOne :
          weightsFoldOne.merge_equal_multilinear_components 0#usize 2#usize <;>
        simp [hweightsMergeOne] at hrun
      rename_i mergeOnePair
      rcases mergeOnePair with ⟨mergeOne, weightsMergeOne⟩
      cases mergeOne <;> simp at hrun
      cases htraceWeightsOne : traceInst.call_mut tracePolynomialOne
          v6_transcript.V6RelationDiagnosticPhase.RoundOneWeights <;>
        simp [htraceWeightsOne] at hrun
      rename_i traceWeightsOnePair
      rcases traceWeightsOnePair with ⟨traceWeightsOneUnit, traceWeightsOne⟩
      cases hfoldedValuesOne : v6_transcript.fold_values_prefix 256#usize
          foldedValues alphaReadOne <;> simp [hfoldedValuesOne] at hrun
      rename_i foldedValuesOne
      cases htraceRoundOne : traceInst.call_mut traceWeightsOne
          v6_transcript.V6RelationDiagnosticPhase.RoundOne <;>
        simp [htraceRoundOne] at hrun
      rename_i traceRoundOnePair
      rcases traceRoundOnePair with ⟨traceRoundOneUnit, traceRoundOne⟩
      cases hrelationRowTwo : relationFields.index_usize 2#usize <;>
        simp [hrelationRowTwo] at hrun
      rename_i relationRowTwo
      cases hpolynomialTwo : v6_transcript.decode_compact_relation_polynomial
          relationRowTwo runningClaimOne <;> simp [hpolynomialTwo] at hrun
      rename_i polynomialTwo
      cases habsorbTwo : v6_transcript.absorb_compact_relation_polynomial
          transcriptChallengeOne 2#usize polynomialTwo <;>
        simp [habsorbTwo] at hrun
      rename_i transcriptAbsorbTwo
      cases hchallengeTwo : transcriptAbsorbTwo.challenge_qm31 <;>
        simp [hchallengeTwo] at hrun
      rename_i challengePairTwo
      rcases challengePairTwo with
        ⟨challengeResultTwo, transcriptChallengeTwo⟩
      cases challengeResultTwo with
      | Err error =>
          simp [core.result.Result.map_err,
            v6_transcript.finish_onefold_relation_round_tail_extraction.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, Bind.bind, Aeneas.Std.bind] at hrun
      | Ok alphaTwo =>
          cases halphaUpdateTwo : alphaAfterOne.update 2#usize alphaTwo <;>
            simp [halphaUpdateTwo] at hrun
          rename_i alphaAfterTwo
          cases halphaReadTwo : alphaAfterTwo.index_usize 2#usize <;>
            simp [halphaReadTwo] at hrun
          rename_i alphaReadTwo
          cases hevaluateTwo : sumcheck.evaluate polynomialTwo alphaReadTwo <;>
            simp [hevaluateTwo] at hrun
          rename_i runningClaimTwo
          cases htracePolynomialTwo : traceInst.call_mut traceRoundOne
              v6_transcript.V6RelationDiagnosticPhase.RoundTwoPolynomial <;>
            simp [htracePolynomialTwo] at hrun
          rename_i tracePolynomialTwoPair
          rcases tracePolynomialTwoPair with
            ⟨tracePolynomialTwoUnit, tracePolynomialTwo⟩
          cases hweightsFoldTwo :
              weightsMergeOne.fold_deferred_relation_arity4 alphaReadTwo <;>
            simp [hweightsFoldTwo] at hrun
          rename_i weightsFoldTwo
          cases htraceWeightsTwo : traceInst.call_mut tracePolynomialTwo
              v6_transcript.V6RelationDiagnosticPhase.RoundTwoWeights <;>
            simp [htraceWeightsTwo] at hrun
          rename_i traceWeightsTwoPair
          rcases traceWeightsTwoPair with
            ⟨traceWeightsTwoUnit, traceWeightsTwo⟩
          cases hfoldedValuesTwo : v6_transcript.fold_values_prefix 64#usize
              foldedValuesOne alphaReadTwo <;> simp [hfoldedValuesTwo] at hrun
          rename_i foldedValuesTwo
          cases htraceRoundTwo : traceInst.call_mut traceWeightsTwo
              v6_transcript.V6RelationDiagnosticPhase.RoundTwo <;>
            simp [htraceRoundTwo] at hrun
          rename_i traceRoundTwoPair
          rcases traceRoundTwoPair with ⟨traceRoundTwoUnit, traceRoundTwo⟩
          cases hrelationRowThree : relationFields.index_usize 3#usize <;>
            simp [hrelationRowThree] at hrun
          rename_i relationRowThree
          cases hpolynomialThree :
              v6_transcript.decode_compact_relation_polynomial relationRowThree
                runningClaimTwo <;> simp [hpolynomialThree] at hrun
          rename_i polynomialThree
          cases habsorbThree : v6_transcript.absorb_compact_relation_polynomial
              transcriptChallengeTwo 3#usize polynomialThree <;>
            simp [habsorbThree] at hrun
          rename_i transcriptAbsorbThree
          cases hchallengeThree : transcriptAbsorbThree.challenge_qm31 <;>
            simp [hchallengeThree] at hrun
          rename_i challengePairThree
          rcases challengePairThree with
            ⟨challengeResultThree, transcriptAfterThree⟩
          cases challengeResultThree with
          | Err error =>
              simp [core.result.Result.map_err,
                v6_transcript.finish_onefold_relation_round_tail_extraction.closure_2.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError.call_once,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from, Bind.bind, Aeneas.Std.bind] at hrun
          | Ok alphaThree =>
              cases halphaUpdateThree :
                  alphaAfterTwo.update 3#usize alphaThree <;>
                simp [halphaUpdateThree] at hrun
              rename_i alphaAfterThree
              cases halphaReadThree : alphaAfterThree.index_usize 3#usize <;>
                simp [halphaReadThree] at hrun
              rename_i alphaReadThree
              cases hevaluateThree :
                  sumcheck.evaluate polynomialThree alphaReadThree <;>
                simp [hevaluateThree] at hrun
              rename_i runningClaimThree
              cases htracePolynomialThree : traceInst.call_mut traceRoundTwo
                  v6_transcript.V6RelationDiagnosticPhase.RoundThreePolynomial <;>
                simp [htracePolynomialThree] at hrun
              rename_i tracePolynomialThreePair
              rcases tracePolynomialThreePair with
                ⟨tracePolynomialThreeUnit, tracePolynomialThree⟩
              cases hweightsFoldThree :
                  weightsFoldTwo.fold_deferred_relation_arity4 alphaReadThree <;>
                simp [hweightsFoldThree] at hrun
              rename_i weightsFoldThree
              cases htraceWeightsThree : traceInst.call_mut tracePolynomialThree
                  v6_transcript.V6RelationDiagnosticPhase.RoundThreeWeights <;>
                simp [htraceWeightsThree] at hrun
              rename_i traceWeightsThreePair
              rcases traceWeightsThreePair with
                ⟨traceWeightsThreeUnit, traceWeightsThree⟩
              cases hfoldedValuesThree : v6_transcript.fold_values_prefix
                  16#usize foldedValuesTwo alphaReadThree <;>
                simp [hfoldedValuesThree] at hrun
              rename_i foldedValuesThree
              cases htraceRoundThree : traceInst.call_mut traceWeightsThree
                  v6_transcript.V6RelationDiagnosticPhase.RoundThree <;>
                simp [htraceRoundThree] at hrun
              rename_i traceRoundThreePair
              rcases traceRoundThreePair with
                ⟨traceRoundThreeUnit, traceRoundThree⟩
              cases hterminalPrefix : core.array.Array.index
                  (core.ops.index.IndexSlice
                    (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31))
                  foldedValuesThree { «end» := 4#usize } with
              | fail error =>
                simp only [core.array.Array.index, core.ops.index.IndexSlice,
                  core.slice.index.Slice.index] at hterminalPrefix
                rw [hterminalPrefix] at hrun
                simp at hrun
              | div =>
                simp only [core.array.Array.index, core.ops.index.IndexSlice,
                  core.slice.index.Slice.index] at hterminalPrefix
                rw [hterminalPrefix] at hrun
                simp at hrun
              | ok terminalPrefix =>
                simp only [core.array.Array.index, core.ops.index.IndexSlice,
                  core.slice.index.Slice.index] at hterminalPrefix
                rw [hterminalPrefix] at hrun
                dsimp only at hrun
                cases hterminalDot : weightsFoldThree.dot terminalPrefix with
                | fail error =>
                  rw [hterminalDot] at hrun
                  simp at hrun
                | div =>
                  rw [hterminalDot] at hrun
                  simp at hrun
                | ok terminalDot =>
                  rw [hterminalDot] at hrun
                  dsimp only at hrun
                  cases hterminalNe : core.cmp.PartialEq.ne.trait_default
                      field.QM31.Insts.CoreCmpPartialEqQM31 terminalDot
                      runningClaimThree with
                  | fail error =>
                    rw [hterminalNe] at hrun
                    simp at hrun
                  | div =>
                    rw [hterminalNe] at hrun
                    simp at hrun
                  | ok terminalNe =>
                    rw [hterminalNe] at hrun
                    dsimp only at hrun
                    cases terminalNe with
                    | true => simp at hrun
                    | false =>
                      simp only [Bool.false_eq_true, if_false] at hrun
                      simp_all
                      cases htraceTerminal : traceInst.call_mut traceRoundThree
                          v6_transcript.V6RelationDiagnosticPhase.Terminal with
                      | fail error =>
                        rw [htraceTerminal] at hrun
                        simp at hrun
                      | div =>
                        rw [htraceTerminal] at hrun
                        simp at hrun
                      | ok traceTerminalPair =>
                        rw [htraceTerminal] at hrun
                        dsimp only at hrun
                        rcases traceTerminalPair with
                          ⟨traceTerminalUnit, traceAfterTerminal⟩
                        cases hqueryIterator :
                            Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
                              authenticatedQueries.values with
                        | fail error =>
                          rw [hqueryIterator] at hrun
                          simp at hrun
                        | div =>
                          rw [hqueryIterator] at hrun
                          simp at hrun
                        | ok queryIterator =>
                          rw [hqueryIterator] at hrun
                          dsimp only at hrun
                          cases hfoldedQuerySum :
                              core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
                                (BuiltinFnMut
                                  (field.QM31 × field.QM31) field.QM31)
                                queryIterator field.QM31.ZERO
                                (fun pair => field.QM31.add pair.1 pair.2) with
                          | fail error =>
                            rw [hfoldedQuerySum] at hrun
                            simp at hrun
                          | div =>
                            rw [hfoldedQuerySum] at hrun
                            simp at hrun
                          | ok foldedQuerySum =>
                            rw [hfoldedQuerySum] at hrun
                            dsimp only at hrun
                            have hterminalExact :=
                              V7Tag73RoundTailSourceBridge.qm31_ne_ok_false_iff_eq
                                terminalDot runningClaimThree
                            rw [hterminalNe] at hterminalExact
                            simp at hterminalExact
                            simp at hrun
                            subst verified
                            exact ⟨{
                relationRowOne := relationRowOne
                polynomialOne := polynomialOne
                transcriptAbsorbOne := transcriptAbsorbOne
                transcriptChallengeOne := transcriptChallengeOne
                alphaOne := alphaOne
                alphaReadOne := alphaReadOne
                alphaAfterOne := alphaAfterOne
                runningClaimOne := runningClaimOne
                weightsFoldOne := weightsFoldOne
                weightsMergeOne := weightsMergeOne
                foldedValuesOne := foldedValuesOne
                relationRowOneSuccess := hrelationRowOne
                polynomialOneSuccess := hpolynomialOne
                absorbOneSuccess := habsorbOne
                challengeOneSuccess := hchallengeOne
                alphaUpdateOneSuccess := halphaUpdateOne
                alphaReadOneSuccess := halphaReadOne
                evaluateOneSuccess := hevaluateOne
                weightsFoldOneSuccess := hweightsFoldOne
                weightsMergeOneSuccess := hweightsMergeOne
                foldedValuesOneSuccess := hfoldedValuesOne
                relationRowTwo := relationRowTwo
                polynomialTwo := polynomialTwo
                transcriptAbsorbTwo := transcriptAbsorbTwo
                transcriptChallengeTwo := transcriptChallengeTwo
                alphaTwo := alphaTwo
                alphaReadTwo := alphaReadTwo
                alphaAfterTwo := alphaAfterTwo
                runningClaimTwo := runningClaimTwo
                weightsFoldTwo := weightsFoldTwo
                foldedValuesTwo := foldedValuesTwo
                relationRowTwoSuccess := hrelationRowTwo
                polynomialTwoSuccess := hpolynomialTwo
                absorbTwoSuccess := habsorbTwo
                challengeTwoSuccess := hchallengeTwo
                alphaUpdateTwoSuccess := halphaUpdateTwo
                alphaReadTwoSuccess := halphaReadTwo
                evaluateTwoSuccess := hevaluateTwo
                weightsFoldTwoSuccess := hweightsFoldTwo
                foldedValuesTwoSuccess := hfoldedValuesTwo
                relationRowThree := relationRowThree
                polynomialThree := polynomialThree
                transcriptAbsorbThree := transcriptAbsorbThree
                alphaThree := alphaThree
                alphaReadThree := alphaReadThree
                alphaAfterThree := alphaAfterThree
                runningClaimThree := runningClaimThree
                weightsFoldThree := weightsFoldThree
                foldedValuesThree := foldedValuesThree
                relationRowThreeSuccess := hrelationRowThree
                polynomialThreeSuccess := hpolynomialThree
                absorbThreeSuccess := habsorbThree
                challengeThreeSuccess := ⟨transcriptAfterThree,
                  hchallengeThree⟩
                alphaUpdateThreeSuccess := halphaUpdateThree
                alphaReadThreeSuccess := halphaReadThree
                evaluateThreeSuccess := hevaluateThree
                weightsFoldThreeSuccess := hweightsFoldThree
                foldedValuesThreeSuccess := hfoldedValuesThree
                terminalPrefix := terminalPrefix
                terminalDot := terminalDot
                terminalPrefixSuccess := hterminalPrefix
                terminalDotSuccess := hterminalDot
                terminalNeSuccess := hterminalNe
                terminalExact := hterminalExact
                foldedQuerySum := foldedQuerySum
                foldedQuerySumSuccess := by
                  simp only [bind_eq_ok_iff]
                  exact ⟨queryIterator, hqueryIterator,
                    hfoldedQuerySum⟩
                outputExact := rfl } ⟩

#print axioms accepted_tail_exposes_exact_trace

end V7Tag73RoundTailTrace
