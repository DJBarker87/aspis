import V7Tag73GeneratedReaderBridge

/-!
# Literal generated semantic-sumcheck fixed-field bridge

This file closes the production `1 + 10 * 27` semantic fixed-field prefix.
The inner translated range loop is first tied directly to one successful
production `next_qm31` call on every continuing edge.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 40000

namespace AspisV7Tag73GeneratedSemanticBridge

open V7Tag73FixedFieldGenericNamespaceR1Generated
open AspisV7Tag73AeneasExactLoopTrace
open AspisV7Tag73GeneratedReaderBridge

private theorem bind_eq_ok_iff {Alpha Beta : Type} (input : Result Alpha)
    (next : Alpha → Result Beta) (output : Beta) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

abbrev SemanticResult :=
  field.QM31 × Array field.QM31 10#usize × field.QM31

abbrev SemanticPending :=
  Option (core.result.Result SemanticResult v6_transcript.V6TranscriptError)

abbrev SemanticInnerState :=
  core.ops.range.Range Std.Usize × v6_onefold.V6FixedFieldReader ×
    Array field.QM31 28#usize × Array Std.U8 433#usize ×
    Array Std.U64 4#usize

abbrev SemanticInnerOutput :=
  transcript.Transcript × v6_onefold.V6FixedFieldReader ×
    Array field.QM31 10#usize × field.QM31 × SemanticPending × Std.U32

def semanticInnerBody
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state : SemanticInnerState) :
    Result (ControlFlow SemanticInnerState SemanticInnerOutput) :=
  v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    transcriptBefore point runningClaim round pending state.1 state.2.1
    state.2.2.1 state.2.2.2.1 state.2.2.2.2

def semanticInnerMeasure (state : SemanticInnerState) : Nat :=
  state.1.end.val - state.1.start.val

theorem semantic_inner_body_cont_exact
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state next : SemanticInnerState)
    (run : semanticInnerBody transcriptBefore point runningClaim round pending
      state = .ok (.cont next)) :
    semanticInnerMeasure next + 1 = semanticInnerMeasure state ∧
    ∃ value,
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
          state.2.1 = .ok (.Ok value, next.2.1) := by
  unfold semanticInnerBody at run
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangeOutput =>
    rcases rangeOutput with ⟨item, rangeAfter⟩
    cases item with
    | none =>
      simp only [bind_tc_ok] at run
      generalize tail0Run :
          Array.index_usize state.2.2.2.2 0#usize = tail0Result at run
      cases tail0Result with
      | fail error => simp at run
      | div => simp at run
      | ok tail0 =>
        simp only [bind_tc_ok] at run
        generalize reduce0Run : field.M31.reduce_u64 tail0 = reduce0Result at run
        cases reduce0Result with
        | fail error => simp at run
        | div => simp at run
        | ok limb0 =>
          simp only [bind_tc_ok] at run
          generalize tail1Run :
              Array.index_usize state.2.2.2.2 1#usize = tail1Result at run
          cases tail1Result with
          | fail error => simp at run
          | div => simp at run
          | ok tail1 =>
            simp only [bind_tc_ok] at run
            generalize reduce1Run :
                field.M31.reduce_u64 tail1 = reduce1Result at run
            cases reduce1Result with
            | fail error => simp at run
            | div => simp at run
            | ok limb1 =>
              simp only [bind_tc_ok] at run
              generalize cm0Run :
                  field.CM31.new limb0 limb1 = cm0Result at run
              cases cm0Result with
              | fail error => simp at run
              | div => simp at run
              | ok cm0 =>
                simp only [bind_tc_ok] at run
                generalize tail2Run :
                    Array.index_usize state.2.2.2.2 2#usize = tail2Result at run
                cases tail2Result with
                | fail error => simp at run
                | div => simp at run
                | ok tail2 =>
                  simp only [bind_tc_ok] at run
                  generalize reduce2Run :
                      field.M31.reduce_u64 tail2 = reduce2Result at run
                  cases reduce2Result with
                  | fail error => simp at run
                  | div => simp at run
                  | ok limb2 =>
                    simp only [bind_tc_ok] at run
                    generalize tail3Run :
                        Array.index_usize state.2.2.2.2 3#usize =
                          tail3Result at run
                    cases tail3Result with
                    | fail error => simp at run
                    | div => simp at run
                    | ok tail3 =>
                      simp only [bind_tc_ok] at run
                      generalize reduce3Run :
                          field.M31.reduce_u64 tail3 = reduce3Result at run
                      cases reduce3Result with
                      | fail error => simp at run
                      | div => simp at run
                      | ok limb3 =>
                        simp only [bind_tc_ok] at run
                        generalize cm1Run :
                            field.CM31.new limb2 limb3 = cm1Result at run
                        cases cm1Result with
                        | fail error => simp at run
                        | div => simp at run
                        | ok cm1 =>
                          simp only [bind_tc_ok] at run
                          generalize subtractRun :
                              field.QM31.sub runningClaim
                                ({ c0 := cm0, c1 := cm1 } : field.QM31) =
                                  subtractResult at run
                          cases subtractResult with
                          | fail error => simp at run
                          | div => simp at run
                          | ok boundaryTail =>
                            simp only [bind_tc_ok] at run
                            generalize polynomialRun :
                                Array.update state.2.2.1 1#usize boundaryTail =
                                  polynomialResult at run
                            cases polynomialResult with
                            | fail error => simp at run
                            | div => simp at run
                            | ok polynomial =>
                              simp only [bind_tc_ok] at run
                              generalize boundaryRun :
                                  state_only_sumcheck.state_only_boundary_sum
                                    polynomial = boundaryResult at run
                              cases boundaryResult with
                              | fail error => simp at run
                              | div => simp at run
                              | ok boundary =>
                                simp only [bind_tc_ok] at run
                                generalize equalRun :
                                    field.QM31.Insts.CoreCmpPartialEqQM31.eq
                                      boundary runningClaim = equalResult at run
                                cases equalResult with
                                | fail error => simp at run
                                | div => simp at run
                                | ok equal =>
                                  cases equal with
                                  | false => simp [lift] at run
                                  | true =>
                                    simp only [lift, bind_tc_ok] at run
                                    generalize absorbRun :
                                        transcript.Transcript.absorb transcriptBefore
                                          transcript.label.V6_COMPACT_SEMANTIC_ROUND
                                          (Array.to_slice state.2.2.2.1) =
                                            absorbResult at run
                                    cases absorbResult with
                                    | fail error => simp at run
                                    | div => simp at run
                                    | ok transcriptAfterAbsorb =>
                                      simp only [bind_tc_ok] at run
                                      generalize challengeRun :
                                          transcript.Transcript.challenge_qm31
                                            transcriptAfterAbsorb =
                                              challengeResult at run
                                      cases challengeResult with
                                      | fail error => simp at run
                                      | div => simp at run
                                      | ok challengeOutput =>
                                        rcases challengeOutput with
                                          ⟨sampleResult, transcriptAfter⟩
                                        simp only [bind_tc_ok] at run
                                        generalize mapRun :
                                            core.result.Result.map_err
                                              (v6_transcript.verify_compact_semantic_sumcheck.closure_1.Insts.CoreOpsFunctionFnOnceTupleChallengeSampleExhaustedV6TranscriptError
                                                v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream)
                                              sampleResult () = mappedResult at run
                                        cases mappedResult with
                                        | fail error => simp at run
                                        | div => simp at run
                                        | ok mapped =>
                                          simp only [bind_tc_ok] at run
                                          generalize branchRun :
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                mapped = branchResult at run
                                          cases branchResult with
                                          | fail error => simp at run
                                          | div => simp at run
                                          | ok branch =>
                                            cases branch with
                                            | Continue challenge =>
                                              simp only [bind_tc_ok] at run
                                              generalize evaluateRun :
                                                  state_only_sumcheck.evaluate_state_only_polynomial
                                                    polynomial challenge =
                                                      evaluateResult at run
                                              cases evaluateResult with
                                              | fail error => simp at run
                                              | div => simp at run
                                              | ok evaluated =>
                                                simp only [bind_tc_ok] at run
                                                generalize pointRun :
                                                    Array.update point round challenge =
                                                      pointResult at run
                                                cases pointResult with
                                                | fail error => simp at run
                                                | div => simp at run
                                                | ok pointAfter => simp at run
                                            | Break residual =>
                                              simp only [bind_tc_ok] at run
                                              generalize residualRun :
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                    SemanticResult
                                                    (core.convert.FromSame
                                                      v6_transcript.V6TranscriptError)
                                                    residual = residualResult at run
                                              cases residualResult with
                                              | fail error => simp at run
                                              | div => simp at run
                                              | ok returned => simp at run
    | some sent =>
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl)
          (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have startsBeforeEnd : state.1.start.val < state.1.end.val := by
        by_contra notBefore
        simp [notBefore] at conditional
      simp [startsBeforeEnd] at conditional
      rcases conditional with ⟨_, startExact⟩
      simp only [bind_tc_ok] at run
      generalize coefficientRun : sent + 1#usize = coefficientResult at run
      cases coefficientResult with
      | fail error => simp at run
      | div => simp at run
      | ok coefficient =>
        simp only [bind_tc_ok] at run
        generalize readRun :
            v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
              state.2.1 = readResult at run
        cases readResult with
        | fail error => simp at run
        | div => simp at run
        | ok readOutput =>
          rcases readOutput with ⟨fixedResult, readerAfter⟩
          cases fixedResult with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
              at run
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              bind_tc_ok] at run
            generalize polynomialRun :
                Array.update state.2.2.1 coefficient
                  ({ c0 := { a := value.c0.a, b := value.c0.b },
                     c1 := { a := value.c1.a, b := value.c1.b } } : field.QM31) =
                  polynomialResult at run
            cases polynomialResult with
            | fail error => simp at run
            | div => simp at run
            | ok polynomialAfter =>
              simp only [bind_tc_ok] at run
              generalize offsetRun : sent * 16#usize = offsetResult at run
              cases offsetResult with
              | fail error => simp at run
              | div => simp at run
              | ok offset =>
                simp only [bind_tc_ok] at run
                generalize startRun : 1#usize + offset = startResult at run
                cases startResult with
                | fail error => simp at run
                | div => simp at run
                | ok start =>
                  simp only [bind_tc_ok] at run
                  generalize outerSliceRun :
                      core.array.Array.index_mut
                        (core.ops.index.IndexMutSlice
                          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8))
                        state.2.2.2.1 { start := start } = outerSliceResult at run
                  cases outerSliceResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok outerSliceOutput =>
                    rcases outerSliceOutput with ⟨outerSlice, outerBack⟩
                    simp only [bind_tc_ok] at run
                    generalize innerSliceRun :
                        core.slice.index.Slice.index_mut
                          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                          outerSlice { «end» := 16#usize } = innerSliceResult at run
                    cases innerSliceResult with
                    | fail error => simp at run
                    | div => simp at run
                    | ok innerSliceOutput =>
                      rcases innerSliceOutput with ⟨innerSlice, innerBack⟩
                      simp only [bind_tc_ok] at run
                      generalize writeRun :
                          field.QM31.write_le_bytes value innerSlice =
                            writeResult at run
                      cases writeResult with
                      | fail error => simp at run
                      | div => simp at run
                      | ok written =>
                        simp only [lift, bind_tc_ok] at run
                        generalize tail0Run :
                            Array.index_usize state.2.2.2.2 0#usize =
                              tail0Result at run
                        cases tail0Result with
                        | fail error => simp at run
                        | div => simp at run
                        | ok tail0 =>
                          simp only [bind_tc_ok] at run
                          generalize add0Run :
                              tail0 + core.convert.num.FromU64U32.from value.c0.a =
                                add0Result at run
                          cases add0Result with
                          | fail error => simp at run
                          | div => simp at run
                          | ok sum0 =>
                            simp only [bind_tc_ok] at run
                            generalize update0Run :
                                Array.update state.2.2.2.2 0#usize sum0 =
                                  update0Result at run
                            cases update0Result with
                            | fail error => simp at run
                            | div => simp at run
                            | ok tails1 =>
                              simp only [lift, bind_tc_ok] at run
                              generalize tail1Run :
                                  Array.index_usize tails1 1#usize =
                                    tail1Result at run
                              cases tail1Result with
                              | fail error => simp at run
                              | div => simp at run
                              | ok tail1 =>
                                simp only [bind_tc_ok] at run
                                generalize add1Run :
                                    tail1 + core.convert.num.FromU64U32.from value.c0.b =
                                      add1Result at run
                                cases add1Result with
                                | fail error => simp at run
                                | div => simp at run
                                | ok sum1 =>
                                  simp only [bind_tc_ok] at run
                                  generalize update1Run :
                                      Array.update tails1 1#usize sum1 =
                                        update1Result at run
                                  cases update1Result with
                                  | fail error => simp at run
                                  | div => simp at run
                                  | ok tails2 =>
                                    simp only [lift, bind_tc_ok] at run
                                    generalize tail2Run :
                                        Array.index_usize tails2 2#usize =
                                          tail2Result at run
                                    cases tail2Result with
                                    | fail error => simp at run
                                    | div => simp at run
                                    | ok tail2 =>
                                      simp only [bind_tc_ok] at run
                                      generalize add2Run :
                                          tail2 + core.convert.num.FromU64U32.from value.c1.a =
                                            add2Result at run
                                      cases add2Result with
                                      | fail error => simp at run
                                      | div => simp at run
                                      | ok sum2 =>
                                        simp only [bind_tc_ok] at run
                                        generalize update2Run :
                                            Array.update tails2 2#usize sum2 =
                                              update2Result at run
                                        cases update2Result with
                                        | fail error => simp at run
                                        | div => simp at run
                                        | ok tails3 =>
                                          simp only [lift, bind_tc_ok] at run
                                          generalize tail3Run :
                                              Array.index_usize tails3 3#usize =
                                                tail3Result at run
                                          cases tail3Result with
                                          | fail error => simp at run
                                          | div => simp at run
                                          | ok tail3 =>
                                            simp only [bind_tc_ok] at run
                                            generalize add3Run :
                                                tail3 + core.convert.num.FromU64U32.from value.c1.b =
                                                  add3Result at run
                                            cases add3Result with
                                            | fail error => simp at run
                                            | div => simp at run
                                            | ok sum3 =>
                                              simp only [bind_tc_ok] at run
                                              generalize update3Run :
                                                  Array.update tails3 3#usize sum3 =
                                                    update3Result at run
                                              cases update3Result with
                                              | fail error => simp at run
                                              | div => simp at run
                                              | ok tails4 =>
                                                simp at run
                                                subst next
                                                constructor
                                                · unfold semanticInnerMeasure
                                                  rw [endExact, startExact]
                                                  omega
                                                · exact ⟨value, by simpa using readRun⟩

theorem semantic_inner_body_done_no_pending_one_exact
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state : SemanticInnerState) (output : SemanticInnerOutput)
    (run : semanticInnerBody transcriptBefore point runningClaim round pending
      state = .ok (.done output))
    (oneFlag : output.2.2.2.2.2 = 1#u32) :
    output.2.1 = state.2.1 ∧ semanticInnerMeasure state = 0 ∧
      output.2.2.2.2.1 = pending := by
  unfold semanticInnerBody at run
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart, nextEnd⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨iteratorPair, iteratorRun, run⟩
    have iteratorPairExact : iteratorPair = (some state.1.start, nextIter) :=
      Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
    subst iteratorPair
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨coefficient, coefficientRun, run⟩
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨readerPair, readerRun, run⟩
    rcases readerPair with ⟨readerResult, readerAfter⟩
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨flow, flowRun, run⟩
    cases flow with
    | Continue value =>
      simp at run
      repeat'
        (rw [bind_eq_ok_iff] at run
         rcases run with ⟨_, _, run⟩)
      simp at run
    | Break residual =>
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨convertedError, convertedErrorRun, run⟩
      simp at run
      subst output
      simp at oneFlag
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨iteratorPair, iteratorRun, run⟩
    have iteratorPairExact : iteratorPair = (none, state.1) :=
      Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
    subst iteratorPair
    simp at run
    repeat'
      (rw [bind_eq_ok_iff] at run
       rcases run with ⟨_, _, run⟩)
    split at run
    all_goals try
      (repeat'
        (rw [bind_eq_ok_iff] at run
         rcases run with ⟨_, _, run⟩))
    all_goals simp at run
    all_goals try subst output
    · exact ⟨rfl, by unfold semanticInnerMeasure; omega, rfl⟩
    · simp at oneFlag

theorem semantic_inner_body_done_ok_implies_one
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state : SemanticInnerState) (output : SemanticInnerOutput)
    (run : semanticInnerBody transcriptBefore point runningClaim round pending
      state = .ok (.done output))
    (accepted : SemanticResult)
    (hasAccepted : output.2.2.2.2.1 = some (.Ok accepted)) :
    output.2.2.2.2.2 = 1#u32 := by
  unfold semanticInnerBody at run
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart, nextEnd⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨iteratorPair, iteratorRun, run⟩
    have iteratorPairExact : iteratorPair = (some state.1.start, nextIter) :=
      Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
    subst iteratorPair
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨coefficient, coefficientRun, run⟩
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨readerPair, readerRun, run⟩
    rcases readerPair with ⟨readerResult, readerAfter⟩
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨flow, flowRun, run⟩
    cases flow with
    | Continue value =>
      simp at run
      repeat'
        (rw [bind_eq_ok_iff] at run
         rcases run with ⟨_, _, run⟩)
      simp at run
    | Break residual =>
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨convertedError, convertedErrorRun, run⟩
      simp at run
      subst output
      cases readerResult with
      | Ok value =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
      | Err wireError =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
        subst residual
        simp [
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
          at convertedErrorRun
        subst convertedError
        simp at hasAccepted
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨iteratorPair, iteratorRun, run⟩
    have iteratorPairExact : iteratorPair = (none, state.1) :=
      Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
    subst iteratorPair
    simp at run
    repeat'
      (rw [bind_eq_ok_iff] at run
       rcases run with ⟨_, _, run⟩)
    split at run
    · repeat'
        (rw [bind_eq_ok_iff] at run
         rcases run with ⟨_, _, run⟩)
      simp at run
      subst output
      rfl
    · rw [bind_eq_ok_iff] at run
      rcases run with ⟨convertedError, convertedErrorRun, run⟩
      simp at run
      subst output
      casesm (core.result.Result field.QM31
        v6_transcript.V6TranscriptError)
      <;> try casesm (core.result.Result core.convert.Infallible
        v6_transcript.V6TranscriptError)
      <;> try casesm (core.result.Result SemanticResult
        v6_transcript.V6TranscriptError)
      <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]

theorem semantic_inner_body_done_ok_origin
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state : SemanticInnerState) (output : SemanticInnerOutput)
    (run : semanticInnerBody transcriptBefore point runningClaim round pending
      state = .ok (.done output))
    (accepted : SemanticResult)
    (hasAccepted : output.2.2.2.2.1 = some (.Ok accepted)) :
    pending = some (.Ok accepted) := by
  have oneFlag := semantic_inner_body_done_ok_implies_one transcriptBefore point
    runningClaim round pending state output run accepted hasAccepted
  have preserved :=
    (semantic_inner_body_done_no_pending_one_exact transcriptBefore point
      runningClaim round pending state output run oneFlag).2.2
  rw [hasAccepted] at preserved
  exact preserved.symm

theorem semantic_inner_body_cont_decreases
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state next : SemanticInnerState)
    (run : semanticInnerBody transcriptBefore point runningClaim round pending
      state = .ok (.cont next)) :
    semanticInnerMeasure next < semanticInnerMeasure state := by
  have exactStep :=
    (semantic_inner_body_cont_exact transcriptBefore point runningClaim round
      pending state next run).1
  omega

theorem semantic_inner_loop_success_has_exact_trace
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    (state : SemanticInnerState) (output : SemanticInnerOutput)
    (run :
      v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        state.1 transcriptBefore state.2.1 point runningClaim round
        state.2.2.1 state.2.2.2.1 state.2.2.2.2 pending = .ok output) :
    Nonempty
      (ExactLoopTrace
        (semanticInnerBody transcriptBefore point runningClaim round pending)
        state output) := by
  apply loop_success_has_exact_trace
    (semanticInnerBody transcriptBefore point runningClaim round pending)
    semanticInnerMeasure
    (semantic_inner_body_cont_decreases transcriptBefore point runningClaim
      round pending) state output
  exact run

theorem semantic_inner_trace_no_pending_one_has_reads
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    {state : SemanticInnerState} {output : SemanticInnerOutput}
    (trace : ExactLoopTrace
      (semanticInnerBody transcriptBefore point runningClaim round pending)
      state output)
    (oneFlag : output.2.2.2.2.2 = 1#u32) :
    ∃ values,
      SuccessfulFixedReaderTrace state.2.1 values output.2.1 ∧
      values.length = trace.contCount := by
  induction trace with
  | done equation =>
    have doneExact := semantic_inner_body_done_no_pending_one_exact
      transcriptBefore point runningClaim round pending _ _ equation
      oneFlag
    rw [doneExact.1]
    exact ⟨[], .nil _, rfl⟩
  | cont equation tail inductionHypothesis =>
    obtain ⟨value, read⟩ :=
      (semantic_inner_body_cont_exact transcriptBefore point runningClaim
        round pending _ _ equation).2
    obtain ⟨values, rest, lengthExact⟩ :=
      inductionHypothesis oneFlag
    refine ⟨value :: values, .cons read rest, ?_⟩
    change values.length + 1 = tail.contCount + 1
    omega

theorem semantic_inner_trace_no_pending_one_cont_count
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    {state : SemanticInnerState} {output : SemanticInnerOutput}
    (trace : ExactLoopTrace
      (semanticInnerBody transcriptBefore point runningClaim round pending)
      state output)
    (oneFlag : output.2.2.2.2.2 = 1#u32) :
    trace.contCount = semanticInnerMeasure state := by
  induction trace with
  | done equation =>
    have doneExact := semantic_inner_body_done_no_pending_one_exact
      transcriptBefore point runningClaim round pending _ _ equation
      oneFlag
    simpa [ExactLoopTrace.contCount] using doneExact.2.1.symm
  | cont equation tail inductionHypothesis =>
    have stepExact :=
      (semantic_inner_body_cont_exact transcriptBefore point runningClaim
        round pending _ _ equation).1
    simp only [ExactLoopTrace.contCount]
    rw [inductionHypothesis oneFlag]
    omega

theorem semantic_inner_trace_one_preserves_pending
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    {state : SemanticInnerState} {output : SemanticInnerOutput}
    (trace : ExactLoopTrace
      (semanticInnerBody transcriptBefore point runningClaim round pending)
      state output)
    (oneFlag : output.2.2.2.2.2 = 1#u32) :
    output.2.2.2.2.1 = pending := by
  induction trace with
  | done equation =>
    exact (semantic_inner_body_done_no_pending_one_exact transcriptBefore point
      runningClaim round pending _ _ equation oneFlag).2.2
  | cont equation tail inductionHypothesis =>
    exact inductionHypothesis oneFlag

theorem semantic_inner_trace_ok_origin
    (transcriptBefore : transcript.Transcript)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (round : Std.Usize) (pending : SemanticPending)
    {state : SemanticInnerState} {output : SemanticInnerOutput}
    (trace : ExactLoopTrace
      (semanticInnerBody transcriptBefore point runningClaim round pending)
      state output)
    (accepted : SemanticResult)
    (hasAccepted : output.2.2.2.2.1 = some (.Ok accepted)) :
    pending = some (.Ok accepted) := by
  induction trace with
  | done equation =>
    exact semantic_inner_body_done_ok_origin transcriptBefore point
      runningClaim round pending _ _ equation accepted hasAccepted
  | cont equation tail inductionHypothesis =>
    exact inductionHypothesis hasAccepted

theorem generated_semantic_inner_success_reads_exactly_26
    (transcriptBefore transcriptAfter : transcript.Transcript)
    (point pointAfter : Array field.QM31 10#usize)
    (runningClaim runningClaimAfter : field.QM31) (round : Std.Usize)
    (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (pending : SemanticPending)
    (polynomial : Array field.QM31 28#usize)
    (framed : Array Std.U8 433#usize)
    (tailLimbs : Array Std.U64 4#usize)
    (run :
      v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
        v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
        { start := 1#usize, «end» := 27#usize }
        transcriptBefore reader point runningClaim round polynomial framed
        tailLimbs pending =
          .ok (transcriptAfter, readerAfter, pointAfter, runningClaimAfter,
            pending, 1#u32)) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 26 ∧
      ∀ value ∈ values, CanonicalGeneratedQM31 value := by
  let state : SemanticInnerState :=
    ({ start := 1#usize, «end» := 27#usize }, reader, polynomial, framed,
      tailLimbs)
  obtain ⟨trace⟩ := semantic_inner_loop_success_has_exact_trace
    transcriptBefore point runningClaim round pending state
    (transcriptAfter, readerAfter, pointAfter, runningClaimAfter, pending,
      1#u32)
    run
  obtain ⟨values, reads, lengthExact⟩ :=
    semantic_inner_trace_no_pending_one_has_reads transcriptBefore point
      runningClaim round pending trace rfl
  refine ⟨values, reads, ?_, successful_trace_values_canonical reads⟩
  rw [lengthExact,
    semantic_inner_trace_no_pending_one_cont_count transcriptBefore point
      runningClaim round pending trace rfl]
  norm_num [state, semanticInnerMeasure]

private theorem fixedReaderTraceAppend
    {first middle final : v6_onefold.V6FixedFieldReader}
    {left right : List field.QM31}
    (leftTrace : SuccessfulFixedReaderTrace first left middle)
    (rightTrace : SuccessfulFixedReaderTrace middle right final) :
    SuccessfulFixedReaderTrace first (left ++ right) final := by
  induction leftTrace with
  | nil => simpa using rightTrace
  | cons read rest inductionHypothesis =>
    simpa using SuccessfulFixedReaderTrace.cons read
      (inductionHypothesis rightTrace)

abbrev SemanticOuterState :=
  core.ops.range.Range Std.Usize × transcript.Transcript ×
    v6_onefold.V6FixedFieldReader × Array field.QM31 10#usize ×
    field.QM31 × SemanticPending

abbrev SemanticOuterOutput :=
  transcript.Transcript × v6_onefold.V6FixedFieldReader × SemanticPending

def semanticOuterBody (eta : field.QM31) (state : SemanticOuterState) :
    Result (ControlFlow SemanticOuterState SemanticOuterOutput) :=
  v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
    eta state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2.1
    state.2.2.2.2.2

def semanticOuterMeasure (state : SemanticOuterState) : Nat :=
  state.1.end.val - state.1.start.val

theorem semantic_outer_body_cont_exact
    (eta : field.QM31) (state next : SemanticOuterState)
    (run : semanticOuterBody eta state = .ok (.cont next)) :
    semanticOuterMeasure next + 1 = semanticOuterMeasure state ∧
    ∃ values,
      SuccessfulFixedReaderTrace state.2.2.1 values next.2.2.1 ∧
      values.length = 27 ∧ next.2.2.2.2.2 = state.2.2.2.2.2 := by
  unfold semanticOuterBody at run
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0.body at run
  generalize rangeRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1 =
        rangeResult at run
  cases rangeResult with
  | fail error => simp at run
  | div => simp at run
  | ok rangeOutput =>
    rcases rangeOutput with ⟨item, rangeAfter⟩
    cases item with
    | none => simp at run
    | some round =>
      have rangeSpec :=
        core.iter.range.IteratorRange.next_UScalar_spec
          (ty := .Usize) (cloneInst := core.clone.CloneUsize)
          (partialOrdInst := core.cmp.PartialOrdUsize)
          (by intro value; rfl)
          (by intro left right; rfl) state.1
      rw [rangeRun] at rangeSpec
      simp only [WP.spec_ok] at rangeSpec
      rcases rangeSpec with ⟨conditional, endExact⟩
      have startsBeforeEnd : state.1.start.val < state.1.end.val := by
        by_contra notBefore
        simp [notBefore] at conditional
      simp [startsBeforeEnd] at conditional
      rcases conditional with ⟨_, startExact⟩
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨framedSlot, framedSlotRun, run⟩
      rcases framedSlot with ⟨framedByte, putFramedByte⟩
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨roundByte, roundByteRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨readerPair, readerRun, run⟩
      rcases readerPair with ⟨readerResult, readerAfter⟩
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨flow, flowRun, run⟩
      cases flow with
      | Break residual =>
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨convertedError, convertedErrorRun, run⟩
        simp at run
      | Continue value =>
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨polynomial, polynomialRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨q, qRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨framedWindowPair, framedWindowRun, run⟩
        rcases framedWindowPair with ⟨framedWindow, putFramedWindow⟩
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨encodedWindow, encodedWindowRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨limb0, limb0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨doubled0, doubled0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨limb1, limb1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨doubled1, doubled1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨limb2, limb2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨doubled2, doubled2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨limb3, limb3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨doubled3, doubled3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨innerOutput, innerRun, run⟩
        rcases innerOutput with
          ⟨transcriptAfter, readerAfterInner, pointAfter, claimAfter,
            pendingAfter, status⟩
        split at run
        · rename_i statusExact
          simp at run
          subst next
          have statusValue : status = 1#u32 := by
            change status = (1#32#uscalar : Std.U32) at statusExact
            calc
              status = (1#32#uscalar : Std.U32) := statusExact
              _ = 1#u32 := by
                apply UScalar.eq_of_val_eq
                rfl
          have innerRunOne :
              v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
                v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                { start := 1#usize,
                  «end» := v6_onefold.V6_SEMANTIC_SENT_VALUES }
                state.2.1 readerAfter state.2.2.2.1 state.2.2.2.2.1 round
                polynomial (putFramedWindow encodedWindow)
                (Array.make 4#usize [ doubled0, doubled1, doubled2, doubled3 ])
                state.2.2.2.2.2 =
                  .ok (transcriptAfter, readerAfterInner, pointAfter,
                    claimAfter, pendingAfter, 1#u32) := by
            simpa [statusValue] using innerRun
          obtain ⟨innerTrace⟩ := semantic_inner_loop_success_has_exact_trace
            state.2.1 state.2.2.2.1 state.2.2.2.2.1 round
            state.2.2.2.2.2
            ({ start := 1#usize, «end» := 27#usize }, readerAfter,
              polynomial, putFramedWindow encodedWindow,
              Array.make 4#usize
                [ doubled0, doubled1, doubled2, doubled3 ])
            (transcriptAfter, readerAfterInner, pointAfter, claimAfter,
              pendingAfter, 1#u32)
            (by simpa [v6_onefold.V6_SEMANTIC_SENT_VALUES] using innerRunOne)
          have pendingExact := semantic_inner_trace_one_preserves_pending
            state.2.1 state.2.2.2.1 state.2.2.2.2.1 round
            state.2.2.2.2.2 innerTrace rfl
          have pendingValue : pendingAfter = state.2.2.2.2.2 := by
            simpa using pendingExact
          have innerRunExact := innerRunOne
          rw [pendingValue] at innerRunExact
          obtain ⟨innerValues, innerReads, innerLength, innerCanonical⟩ :=
            generated_semantic_inner_success_reads_exactly_26
              state.2.1 transcriptAfter state.2.2.2.1 pointAfter
              state.2.2.2.2.1 claimAfter round readerAfter readerAfterInner
              state.2.2.2.2.2 polynomial (putFramedWindow encodedWindow)
              (Array.make 4#usize
                [ doubled0, doubled1, doubled2, doubled3 ])
              (by simpa [v6_onefold.V6_SEMANTIC_SENT_VALUES] using innerRunExact)
          cases readerResult with
          | Err wireError =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
          | Ok firstValue =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
            subst value
            have firstRead :
                v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
                    state.2.2.1 = .ok (.Ok firstValue, readerAfter) := by
              simpa using readerRun
            constructor
            · unfold semanticOuterMeasure
              rw [endExact, startExact]
              omega
            · refine ⟨firstValue :: innerValues,
                .cons firstRead innerReads, ?_, pendingExact⟩
              simp [innerLength]
        · cases pendingAfter <;> simp at run

theorem semantic_outer_body_done_ok_from_none_exact
    (eta : field.QM31) (state : SemanticOuterState)
    (output : SemanticOuterOutput)
    (run : semanticOuterBody eta state = .ok (.done output))
    (accepted : SemanticResult)
    (hasAccepted : output.2.2 = some (.Ok accepted))
    (noPending : state.2.2.2.2.2 = none) :
    output.2.1 = state.2.2.1 ∧ semanticOuterMeasure state = 0 := by
  unfold semanticOuterBody at run
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0.body at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart, nextEnd⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at run
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨framedSlot, framedSlotRun, run⟩
    rcases framedSlot with ⟨framedByte, putFramedByte⟩
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨roundByte, roundByteRun, run⟩
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨readerPair, readerRun, run⟩
    rcases readerPair with ⟨readerResult, readerAfter⟩
    simp at run
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨flow, flowRun, run⟩
    cases flow with
    | Break residual =>
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨convertedError, convertedErrorRun, run⟩
      simp at run
      subst output
      cases readerResult with
      | Ok value =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
      | Err wireError =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at flowRun
        subst residual
        simp [
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
          at convertedErrorRun
        subst convertedError
        simp at hasAccepted
    | Continue value =>
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨polynomial, polynomialRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨q, qRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨framedWindowPair, framedWindowRun, run⟩
      rcases framedWindowPair with ⟨framedWindow, putFramedWindow⟩
      simp at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨encodedWindow, encodedWindowRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨limb0, limb0Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨doubled0, doubled0Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨limb1, limb1Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨doubled1, doubled1Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨limb2, limb2Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨doubled2, doubled2Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨limb3, limb3Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨doubled3, doubled3Run, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨innerOutput, innerRun, run⟩
      rcases innerOutput with
        ⟨transcriptAfter, readerAfterInner, pointAfter, claimAfter,
          pendingAfter, status⟩
      split at run
      · simp at run
      · cases pendingAfter with
        | none =>
          simp at run
          subst output
          simp at hasAccepted
        | some pendingResult =>
          simp at run
          subst output
          have pendingAccepted : pendingResult = .Ok accepted := by
            simpa using hasAccepted
          subst pendingResult
          let exactInnerRange : core.ops.range.Range Std.Usize :=
            { start := 1#usize,
              «end» := v6_onefold.V6_SEMANTIC_SENT_VALUES }
          let exactInnerState : SemanticInnerState :=
            (exactInnerRange, readerAfter,
              polynomial, putFramedWindow encodedWindow,
              Array.make 4#usize
                [ doubled0, doubled1, doubled2, doubled3 ])
          obtain ⟨innerTrace⟩ := semantic_inner_loop_success_has_exact_trace
            state.2.1 state.2.2.2.1 state.2.2.2.2.1 state.1.start
            state.2.2.2.2.2 exactInnerState
            (transcriptAfter, readerAfterInner, pointAfter, claimAfter,
              some (.Ok accepted), status)
            (by simpa using innerRun)
          have origin := semantic_inner_trace_ok_origin state.2.1
            state.2.2.2.1 state.2.2.2.2.1 state.1.start
            state.2.2.2.2.2 innerTrace accepted rfl
          rw [noPending] at origin
          simp at origin
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [bind_eq_ok_iff] at run
    rcases run with ⟨iteratorPair, iteratorRun, run⟩
    have iteratorPairExact : iteratorPair = (none, state.1) :=
      Aeneas.Std.Result.ok.inj (iteratorRun.symm.trans nextRun)
    subst iteratorPair
    simp at run
    subst output
    exact ⟨rfl, by unfold semanticOuterMeasure; omega⟩

theorem semantic_outer_body_cont_decreases
    (eta : field.QM31) (state next : SemanticOuterState)
    (run : semanticOuterBody eta state = .ok (.cont next)) :
    semanticOuterMeasure next < semanticOuterMeasure state := by
  have exactStep := (semantic_outer_body_cont_exact eta state next run).1
  omega

theorem semantic_outer_loop_success_has_exact_trace
    (eta : field.QM31) (iter : core.ops.range.Range Std.Usize)
    (transcriptBefore : transcript.Transcript)
    (reader : v6_onefold.V6FixedFieldReader)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (pending : SemanticPending) (output : SemanticOuterOutput)
    (run :
      v6_transcript.verify_compact_semantic_sumcheck_loop0
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          iter transcriptBefore reader eta point runningClaim pending =
        .ok output) :
    Nonempty (ExactLoopTrace (semanticOuterBody eta)
      (iter, transcriptBefore, reader, point, runningClaim, pending)
      output) := by
  unfold v6_transcript.verify_compact_semantic_sumcheck_loop0 at run
  change loop (semanticOuterBody eta)
      (iter, transcriptBefore, reader, point, runningClaim, pending) =
        .ok output at run
  exact loop_success_has_exact_trace
    (semanticOuterBody eta) semanticOuterMeasure
    (semantic_outer_body_cont_decreases eta)
    (iter, transcriptBefore, reader, point, runningClaim, pending)
    output run

theorem semantic_outer_trace_from_none_has_reads
    (eta : field.QM31) {state : SemanticOuterState}
    {output : SemanticOuterOutput}
    (trace : ExactLoopTrace (semanticOuterBody eta) state output)
    (accepted : SemanticResult)
    (hasAccepted : output.2.2 = some (.Ok accepted))
    (noPending : state.2.2.2.2.2 = none) :
    ∃ values,
      SuccessfulFixedReaderTrace state.2.2.1 values output.2.1 ∧
      values.length = 27 * trace.contCount := by
  induction trace with
  | done equation =>
    obtain ⟨readerExact, _⟩ :=
      semantic_outer_body_done_ok_from_none_exact eta _ _ equation
        accepted hasAccepted noPending
    refine ⟨[], ?_, by simp [ExactLoopTrace.contCount]⟩
    rw [readerExact]
    exact .nil _
  | @cont current nextState finalOutput equation tail inductionHypothesis =>
    obtain ⟨_, roundValues, roundReads, roundLength, pendingExact⟩ :=
      semantic_outer_body_cont_exact eta current nextState equation
    have nextNoPending : nextState.2.2.2.2.2 = none := by
      rw [pendingExact, noPending]
    obtain ⟨tailValues, tailReads, tailLength⟩ :=
      inductionHypothesis hasAccepted nextNoPending
    refine ⟨roundValues ++ tailValues,
      fixedReaderTraceAppend roundReads tailReads, ?_⟩
    simp only [List.length_append, ExactLoopTrace.contCount]
    omega

theorem semantic_outer_trace_from_none_cont_count
    (eta : field.QM31) {state : SemanticOuterState}
    {output : SemanticOuterOutput}
    (trace : ExactLoopTrace (semanticOuterBody eta) state output)
    (accepted : SemanticResult)
    (hasAccepted : output.2.2 = some (.Ok accepted))
    (noPending : state.2.2.2.2.2 = none) :
    trace.contCount = semanticOuterMeasure state := by
  induction trace with
  | done equation =>
    have exhausted :=
      (semantic_outer_body_done_ok_from_none_exact eta _ _ equation
        accepted hasAccepted noPending).2
    simpa [ExactLoopTrace.contCount] using exhausted.symm
  | @cont current nextState finalOutput equation tail inductionHypothesis =>
    obtain ⟨measureExact, _, _, _, pendingExact⟩ :=
      semantic_outer_body_cont_exact eta current nextState equation
    have nextNoPending : nextState.2.2.2.2.2 = none := by
      rw [pendingExact, noPending]
    have tailCount := inductionHypothesis hasAccepted nextNoPending
    simp only [ExactLoopTrace.contCount]
    rw [tailCount]
    exact measureExact

theorem generated_semantic_outer_success_reads_exactly_270
    (eta : field.QM31) (transcriptBefore transcriptAfter : transcript.Transcript)
    (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (point : Array field.QM31 10#usize) (runningClaim : field.QM31)
    (accepted : SemanticResult)
    (run :
      v6_transcript.verify_compact_semantic_sumcheck_loop0
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          { start := 0#usize, «end» := v6_onefold.V6_SEMANTIC_ROUNDS }
          transcriptBefore reader eta point runningClaim none =
        .ok (transcriptAfter, readerAfter, some (.Ok accepted))) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 270 ∧
      (∀ value ∈ values, CanonicalGeneratedQM31 value) := by
  obtain ⟨trace⟩ := semantic_outer_loop_success_has_exact_trace eta
    { start := 0#usize, «end» := v6_onefold.V6_SEMANTIC_ROUNDS }
    transcriptBefore reader point runningClaim none
    (transcriptAfter, readerAfter, some (.Ok accepted)) run
  obtain ⟨values, reads, lengthExact⟩ :=
    semantic_outer_trace_from_none_has_reads eta trace accepted rfl rfl
  have countExact :=
    semantic_outer_trace_from_none_cont_count eta trace accepted rfl rfl
  refine ⟨values, reads, ?_, successful_trace_values_canonical reads⟩
  rw [lengthExact, countExact]
  norm_num [semanticOuterMeasure, v6_onefold.V6_SEMANTIC_ROUNDS]

theorem generated_semantic_success_reads_exactly_271
    (transcriptBefore transcriptAfter : transcript.Transcript)
    (reader readerAfter : v6_onefold.V6FixedFieldReader)
    (eta : field.QM31) (point : Array field.QM31 10#usize)
    (terminalClaim : field.QM31)
    (run :
      v6_transcript.verify_compact_semantic_sumcheck
          v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
          transcriptBefore reader =
        .ok (.Ok (eta, point, terminalClaim), transcriptAfter, readerAfter)) :
    ∃ values,
      SuccessfulFixedReaderTrace reader values readerAfter ∧
      values.length = 271 ∧
      (∀ value ∈ values, CanonicalGeneratedQM31 value) := by
  unfold v6_transcript.verify_compact_semantic_sumcheck at run
  generalize initialReadEquation :
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31
        reader = initialReadResult at run
  cases initialReadResult with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok initialReadPair =>
    rcases initialReadPair with ⟨initialOutcome, readerAfterInitial⟩
    cases initialOutcome with
    | Err wireError =>
      simp_all [Bind.bind, Aeneas.Std.bind,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,
        v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
    | Ok initialClaim =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
      generalize beginEquation :
          state_only_hiding.begin_state_only_masked_sumcheck
            transcriptBefore initialClaim = beginResult at run
      cases beginResult with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok beginPair =>
        rcases beginPair with ⟨beginOutcome, transcriptAfterBegin⟩
        cases beginOutcome with
        | Err scheduleError =>
          simp_all [Bind.bind, Aeneas.Std.bind, core.result.Result.map_err,
            v6_transcript.verify_compact_semantic_sumcheck.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError.call_once,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from]
        | Ok actualEta =>
          simp only [core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize outerEquation :
              v6_transcript.verify_compact_semantic_sumcheck_loop0
                v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
                { start := 0#usize,
                  «end» := v6_onefold.V6_SEMANTIC_ROUNDS }
                transcriptAfterBegin readerAfterInitial actualEta
                (Array.repeat 10#usize field.QM31.ZERO) initialClaim none =
                  outerResult at run
          cases outerResult with
          | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
          | div => simp_all [Bind.bind, Aeneas.Std.bind]
          | ok outerOutput =>
            rcases outerOutput with
              ⟨actualTranscript, actualReader, pending⟩
            cases pending with
            | none => simp_all [Bind.bind, Aeneas.Std.bind]
            | some payload =>
              cases payload with
              | Err transcriptError => simp_all
              | Ok accepted =>
                rcases accepted with
                  ⟨returnedEta, returnedPoint, returnedTerminal⟩
                have outputExact :
                    returnedEta = eta ∧ returnedPoint = point ∧
                    returnedTerminal = terminalClaim ∧
                    actualTranscript = transcriptAfter ∧
                    actualReader = readerAfter := by
                  simpa [Bind.bind, Aeneas.Std.bind, initialReadEquation,
                    beginEquation, outerEquation] using run
                rcases outputExact with
                  ⟨returnedEtaExact, returnedPointExact,
                    returnedTerminalExact, transcriptExact, readerExact⟩
                subst returnedEta
                subst returnedPoint
                subst returnedTerminal
                subst actualTranscript
                subst actualReader
                obtain ⟨outerValues, outerReads, outerLength, _⟩ :=
                  generated_semantic_outer_success_reads_exactly_270
                    actualEta transcriptAfterBegin transcriptAfter
                    readerAfterInitial readerAfter
                    (Array.repeat 10#usize field.QM31.ZERO) initialClaim
                    (eta, point, terminalClaim) outerEquation
                have firstRead :
                    v6_onefold.V6FixedFieldReader.next_qm31 reader =
                      .ok (.Ok initialClaim, readerAfterInitial) := by
                  simpa [
                    v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream.next_qm31]
                    using initialReadEquation
                let completeReads : SuccessfulFixedReaderTrace reader
                    (initialClaim :: outerValues) readerAfter :=
                  .cons firstRead outerReads
                exact ⟨initialClaim :: outerValues, completeReads,
                  by simp [outerLength],
                  successful_trace_values_canonical completeReads⟩

#print axioms semantic_outer_body_cont_exact
#print axioms semantic_outer_body_done_ok_from_none_exact
#print axioms semantic_outer_body_cont_decreases
#print axioms semantic_outer_loop_success_has_exact_trace
#print axioms semantic_outer_trace_from_none_has_reads
#print axioms semantic_outer_trace_from_none_cont_count
#print axioms generated_semantic_outer_success_reads_exactly_270
#print axioms generated_semantic_success_reads_exactly_271

#print axioms semantic_inner_body_cont_exact
#print axioms semantic_inner_body_done_no_pending_one_exact
#print axioms semantic_inner_body_done_ok_implies_one
#print axioms semantic_inner_body_done_ok_origin
#print axioms semantic_inner_body_cont_decreases
#print axioms semantic_inner_loop_success_has_exact_trace
#print axioms semantic_inner_trace_no_pending_one_has_reads
#print axioms semantic_inner_trace_no_pending_one_cont_count
#print axioms semantic_inner_trace_one_preserves_pending
#print axioms semantic_inner_trace_ok_origin
#print axioms generated_semantic_inner_success_reads_exactly_26

end AspisV7Tag73GeneratedSemanticBridge
