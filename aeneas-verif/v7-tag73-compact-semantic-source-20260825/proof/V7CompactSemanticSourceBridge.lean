import V7CompactSemanticChallengeOpaqueNoDedup.Funs

/-!
# Exact source trace for the Tag-73 compact semantic sumcheck

This file reasons about the direct Charon/Aeneas translation of
`verify_compact_semantic_sumcheck` from the frozen deployed source.  The
generated reader and both nested loops remain transparent.  SHA/transcript
sampling and the already-audited field primitives are typed callbacks.

The first layer below is deliberately generic: it turns a successful Aeneas
`loop` result into a finite, kernel-visible sequence of the exact generated
body equations, provided every continue edge decreases a natural measure.
Later lemmas instantiate that trace with the two production ranges.  This is
an execution trace of the translated Rust, not an independently asserted
correspondence predicate.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CompactSemanticFullGenerated

/- The control-trace proof intentionally treats already translated callees as
atomic steps.  They remain transparent in the generated source module and in
the separate value/framing proof; these local reducibility settings merely
prevent `simp_all` from inlining the complete field implementation while it
is proving range advancement. -/
attribute [local irreducible]
  V7CompactSemanticFullGenerated.field.M31.reduce_u64
  V7CompactSemanticFullGenerated.field.CM31.new
  V7CompactSemanticFullGenerated.field.QM31.Insts.CoreCmpPartialEqQM31.eq
  V7CompactSemanticFullGenerated.field.PreparedQm31Multiplier.new
  V7CompactSemanticFullGenerated.field.PreparedQm31Multiplier.mul
  V7CompactSemanticFullGenerated.field.qm31_sum_products3
  V7CompactSemanticFullGenerated.field.QM31.add
  V7CompactSemanticFullGenerated.field.QM31.sub
  V7CompactSemanticFullGenerated.field.QM31.mul
  V7CompactSemanticFullGenerated.field.QM31.square
  V7CompactSemanticFullGenerated.field.QM31.write_le_bytes
  V7CompactSemanticFullGenerated.state_only_hiding.begin_state_only_masked_sumcheck
  V7CompactSemanticFullGenerated.state_only_sumcheck.state_only_boundary_sum
  V7CompactSemanticFullGenerated.state_only_sumcheck.evaluate_state_only_polynomial
  V7CompactSemanticFullGenerated.transcript.Transcript.absorb
  V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace V7CompactSemanticSourceBridge

universe u v

@[simp] theorem prod_rec_eq_fst_snd
    {Alpha : Type u} {Beta : Type v} {Gamma : Sort*}
    (function : Alpha → Beta → Gamma) (pair : Alpha × Beta) :
    Prod.rec function pair = function pair.1 pair.2 := by
  cases pair
  rfl

@[simp] theorem let_prod_eq_fst_snd
    {Alpha : Type u} {Beta : Type v} {Gamma : Sort*}
    (function : Alpha → Beta → Gamma) (pair : Alpha × Beta) :
    (let (left, right) := pair; function left right) =
      function pair.1 pair.2 := by
  cases pair
  rfl

/-- Successful-result inversion without unfolding the continuation.  This
keeps the generated callee bodies opaque while exposing each literal Rust
`?` edge used by the range-decrease proof below. -/
theorem bind_eq_ok_iff {A B : Type} (input : Result A)
    (next : A → Result B) (output : B) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- A finite trace consisting only of equations for the actual generated
loop body.  A `done` equation terminates the trace; a `cont` equation records
the next translated state verbatim. -/
inductive ExactLoopTrace {State : Type u} {Output : Type v}
    (body : State → Result (ControlFlow State Output)) :
    State → Output → Type (max u v)
  | done {state output}
      (equation : body state = .ok (.done output)) :
      ExactLoopTrace body state output
  | cont {state next output}
      (equation : body state = .ok (.cont next))
      (tail : ExactLoopTrace body next output) :
      ExactLoopTrace body state output

/-- Number of literal generated continue edges in a finite exact trace. -/
def ExactLoopTrace.contCount
    {State : Type u} {Output : Type v}
    {body : State → Result (ControlFlow State Output)}
    {state : State} {output : Output} :
    ExactLoopTrace body state output → Nat
  | .done _ => 0
  | .cont _ tail => tail.contCount + 1

/-- Any successful generated loop whose continue edges strictly decrease a
natural measure has a finite exact-body trace.  The proof unfolds the Aeneas
partial fixpoint only along the successful execution and uses no property of
the body other than the explicit decrease theorem. -/
theorem loop_success_has_exact_trace
    {State Output : Type*}
    (body : State → Result (ControlFlow State Output))
    (measure : State → Nat)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state)
    (state : State) (output : Output)
    (run : loop body state = .ok output) :
    Nonempty (ExactLoopTrace body state output) := by
  rw [loop.eq_def] at run
  generalize bodyEquation : body state = bodyResult at run
  cases bodyResult with
  | fail error => simp [bodyEquation] at run
  | div => simp [bodyEquation] at run
  | ok flow =>
      cases flow with
      | done actualOutput =>
          simp only [bodyEquation, bind_tc_ok] at run
          injection run with outputEquation
          subst actualOutput
          exact ⟨.done bodyEquation⟩
      | cont next =>
          simp only [bodyEquation, bind_tc_ok] at run
          have smaller : measure next < measure state :=
            decreases state next bodyEquation
          obtain ⟨tail⟩ := loop_success_has_exact_trace
            body measure decreases next output run
          exact ⟨.cont bodyEquation tail⟩
termination_by measure state

abbrev RawQM31 := V7CompactSemanticFullGenerated.field.QM31
abbrev RawTranscript :=
  V7CompactSemanticFullGenerated.transcript.Transcript
abbrev RawReader :=
  V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader

/-- The exact mutable state threaded by the generated inner 26-value reader
loop for one compact round. -/
abbrev InnerState :=
  core.ops.range.Range Std.Usize ×
  Slice Std.U8 × Std.Usize × Std.U64 × Std.U8 × Std.Usize ×
  Array RawQM31 28#usize × Array Std.U8 433#usize × Array Std.U64 4#usize

abbrev InnerOutput :=
  RawTranscript × Slice Std.U8 × Std.Usize × Std.U64 × Std.U8 × Std.Usize ×
  Array RawQM31 10#usize × RawQM31 ×
  Option (core.result.Result
    (RawQM31 × Array RawQM31 10#usize × RawQM31)
    V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError) × Std.U32

noncomputable def innerBody
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) : Result (ControlFlow InnerState InnerOutput) :=
  V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    transcript point runningClaim round pendingReturn
    state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2.1
    state.2.2.2.2.2.1 state.2.2.2.2.2.2.1
    state.2.2.2.2.2.2.2.1 state.2.2.2.2.2.2.2.2

def innerMeasure (state : InnerState) : Nat :=
  state.1.end.val - state.1.start.val

/-- A continue edge of the literal inner body advances the Rust range by
exactly one. All decoder, framing, field and transcript calls remain the
generated calls; only their successful result shape is inverted here. -/
theorem inner_body_continue_measure_exact
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state next : InnerState)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.cont next)) :
    innerMeasure next + 1 = innerMeasure state := by
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [bind_eq_ok_iff] at run
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
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨coefficient, coefficientRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨readerPair, readerRun, run⟩
        rcases readerPair with ⟨readerResult, fields⟩
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨flow, flowRun, run⟩
        cases flow with
        | Continue value =>
            simp at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨updatedPolynomial, updatedPolynomialRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨scaledOffset, scaledOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨framedOffset, framedOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with
              ⟨⟨framedWindow, putFramedWindow⟩, framedWindowRun, run⟩
            simp_all
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨⟨qm31Slot, putQm31Slot⟩, qm31SlotRun, run⟩
            simp_all
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨encodedSlot, encodedSlotRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨limb0, limb0Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨acc0, acc0Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨sum0, sum0Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨tail1, tail1Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨limb1, limb1Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨acc1, acc1Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨sum1, sum1Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨tail2, tail2Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨limb2, limb2Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨acc2, acc2Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨sum2, sum2Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨tail3, tail3Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨limb3, limb3Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨acc3, acc3Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨sum3, sum3Run, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨tail4, tail4Run, run⟩
            simp at run
            subst next
            rcases pairExact with ⟨sentExact, iterExact⟩
            subst actualIter
            rcases nextSpec with ⟨nextStartVal, nextEndExact⟩
            have sentVal := congrArg (fun value : Std.Usize => value.val)
              sentExact
            have nextEndVal := congrArg (fun value : Std.Usize => value.val)
              nextEndExact
            unfold innerMeasure
            change nextIter.end.val - nextIter.start.val + 1 =
              state.1.end.val - state.1.start.val
            omega
        | Break residual =>
            simp at run
            repeat'
              (rw [bind_eq_ok_iff] at run
               rcases run with ⟨_, _, run⟩
               simp at run)
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
    generalize pairExact : (none, state.1) = pair at run
    rcases pair with ⟨actualOption, actualIter⟩
    cases actualOption with
    | none =>
        simp at pairExact
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb0, tailLimb0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced0, reduced0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb1, tailLimb1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced1, reduced1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨cm0, cm0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb2, tailLimb2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced2, reduced2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb3, tailLimb3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced3, reduced3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨cm1, cm1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨adjustedClaim, adjustedClaimRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨completedPolynomial, completedPolynomialRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨boundarySum, boundarySumRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨boundaryEqual, boundaryEqualRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨asserted, assertedRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨framedSlice, framedSliceRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨absorbedTranscript, absorbedTranscriptRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with
          ⟨⟨challengeResult, challengedTranscript⟩, challengeRun, run⟩
        simp_all
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨mappedChallenge, mappedChallengeRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨challengeFlow, challengeFlowRun, run⟩
        cases challengeFlow with
        | Continue challenge =>
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨nextClaim, nextClaimRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨nextPoint, nextPointRun, run⟩
            simp at run
        | Break residual =>
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨convertedError, convertedErrorRun, run⟩
            simp at run
    | some sent => simp at pairExact


/- Superseded pre-inversion proof retained temporarily for source-diff
provenance; it is not part of the compiled theorem surface.
/-- A continue edge of the literal inner body advances the Rust range by
exactly one.  All decoder, framing,
field and transcript calls are still the generated calls; their values are
irrelevant to this control-flow fact. -/
theorem inner_body_continue_measure_exact
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state next : InnerState)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.cont next)) :
    innerMeasure next + 1 = innerMeasure state := by
  exact inner_body_continue_measure_exact_core transcript point runningClaim
    round pendingReturn state next run
/- Superseded proof retained only until the focused production replay below
has confirmed the explicit inversion replacement.
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at run
    dsimp at run
    simp only [bind_tc_ok] at run
    simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok, bind_tc_fail,
      bind_tc_div, Aeneas.Std.Result.ok.injEq,
      Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure,
      prod_rec_eq_fst_snd, let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try dsimp at run <;>
        try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
          bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure,
          prod_rec_eq_fst_snd, let_prod_eq_fst_snd])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
      bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
      Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure]
    repeat'
      (split at run <;>
        try dsimp at run <;>
        try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
          bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
      bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
      Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure]
    repeat'
      (split at run <;>
        try dsimp at run <;>
        try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
          bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
    all_goals try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
      bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
      Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure]
    repeat'
      (split at run <;>
        try dsimp at run <;>
        try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
          bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd, innerMeasure])
    all_goals subst next
    all_goals simp [innerMeasure, nextEnd, nextStart]
    all_goals omega
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    dsimp at run
    simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok, bind_tc_fail,
      bind_tc_div, Aeneas.Std.Result.ok.injEq,
      Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq,
      prod_rec_eq_fst_snd, let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try dsimp at run <;>
        try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
          bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq,
          prod_rec_eq_fst_snd, let_prod_eq_fst_snd])
    all_goals try casesm
      (_ × V7CompactSemanticFullGenerated.transcript.Transcript)
    all_goals try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
      bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
      Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try dsimp at run <;>
        try simp_all only [Bind.bind, Aeneas.Std.bind, bind_tc_ok,
          bind_tc_fail, bind_tc_div, Aeneas.Std.Result.ok.injEq,
          Aeneas.Std.ControlFlow.cont.injEq, Prod.mk.injEq, let_prod_eq_fst_snd])
-/
-/

/-- Exact one-step range advancement supplies the well-founded decrease used
to expose the finite inner trace. -/
theorem inner_body_continue_decreases
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state next : InnerState)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.cont next)) :
    innerMeasure next < innerMeasure state := by
  have exactStep := inner_body_continue_measure_exact transcript point
    runningClaim round pendingReturn state next run
  omega

/-- A successful call to the literal generated inner loop exposes a finite
trace made solely of equations for that loop's generated body. -/
theorem inner_loop_success_has_exact_trace
    (iter : core.ops.range.Range Std.Usize)
    (transcript : RawTranscript) (slice : Slice Std.U8)
    (byteIndex : Std.Usize) (buffer : Std.U64)
    (bufferedBits : Std.U8) (remaining : Std.Usize)
    (point : Array RawQM31 10#usize) (runningClaim : RawQM31)
    (round : Std.Usize) (polynomial : Array RawQM31 28#usize)
    (framed : Array Std.U8 433#usize)
    (tailLimbs : Array Std.U64 4#usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (output : InnerOutput)
    (run :
      V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
        iter transcript slice byteIndex buffer bufferedBits remaining point
        runningClaim round polynomial framed tailLimbs pendingReturn =
          .ok output) :
    Nonempty (ExactLoopTrace
      (innerBody transcript point runningClaim round pendingReturn)
      (iter, slice, byteIndex, buffer, bufferedBits, remaining, polynomial,
        framed, tailLimbs)
      output) := by
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0
    at run
  change
    loop (innerBody transcript point runningClaim round pendingReturn)
      (iter, slice, byteIndex, buffer, bufferedBits, remaining, polynomial,
        framed, tailLimbs) = .ok output
    at run
  exact loop_success_has_exact_trace
    (innerBody transcript point runningClaim round pendingReturn)
    innerMeasure
    (inner_body_continue_decreases transcript point runningClaim round
      pendingReturn)
    (iter, slice, byteIndex, buffer, bufferedBits, remaining, polynomial,
      framed, tailLimbs)
    output run

/-- The pending return carried by an exact generated inner-loop output. -/
def innerPending : InnerOutput → Option
    (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError)
  | (_, _, _, _, _, _, _, _, pending, _) => pending

/-- The generated inner loop uses status one only for its normal exhausted
range path. -/
def innerStatus : InnerOutput → Std.U32
  | (_, _, _, _, _, _, _, _, _, status) => status

/- Explicit success-path inversions for the two pending-return properties.
They deliberately avoid the former monolithic simp proof term. -/
private theorem inner_body_done_status_one_core
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (normal : output.2.2.2.2.2.2.2.2.2 = 1#u32) :
    output.2.2.2.2.2.2.2.2.1 = pendingReturn ∧
      innerMeasure state = 0 := by
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [bind_eq_ok_iff] at run
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
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨coefficient, coefficientRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨readerPair, readerRun, run⟩
        rcases readerPair with ⟨readerResult, fields⟩
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨flow, flowRun, run⟩
        cases flow with
        | Continue value =>
            simp at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨updatedPolynomial, updatedPolynomialRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨scaledOffset, scaledOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨framedOffset, framedOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with
              ⟨⟨framedWindow, putFramedWindow⟩, framedWindowRun, run⟩
            simp_all
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨⟨qm31Slot, putQm31Slot⟩, qm31SlotRun, run⟩
            simp_all
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
            simp at normal
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
    generalize pairExact : (none, state.1) = pair at run
    rcases pair with ⟨actualOption, actualIter⟩
    cases actualOption with
    | none =>
        simp at pairExact
        subst actualIter
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb0, tailLimb0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced0, reduced0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb1, tailLimb1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced1, reduced1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨cm0, cm0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb2, tailLimb2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced2, reduced2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb3, tailLimb3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced3, reduced3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨cm1, cm1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨adjustedClaim, adjustedClaimRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨completedPolynomial, completedPolynomialRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨boundarySum, boundarySumRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨boundaryEqual, boundaryEqualRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨asserted, assertedRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨framedSlice, framedSliceRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨absorbedTranscript, absorbedTranscriptRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with
          ⟨⟨challengeResult, challengedTranscript⟩, challengeRun, run⟩
        simp_all
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨mappedChallenge, mappedChallengeRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨challengeFlow, challengeFlowRun, run⟩
        cases challengeFlow with
        | Continue challenge =>
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨nextClaim, nextClaimRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨nextPoint, nextPointRun, run⟩
            simp at run
            subst output
            constructor
            · rfl
            · unfold innerMeasure
              omega
        | Break residual =>
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨convertedError, convertedErrorRun, run⟩
            simp at run
            subst output
            simp at normal
    | some sent => simp at pairExact


private theorem inner_body_done_ok_origin_core
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted :
      output.2.2.2.2.2.2.2.2.1 = some (.Ok accepted)) :
    pendingReturn = some (.Ok accepted) := by
  unfold innerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [bind_eq_ok_iff] at run
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
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨coefficient, coefficientRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨readerPair, readerRun, run⟩
        rcases readerPair with ⟨readerResult, fields⟩
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨flow, flowRun, run⟩
        cases flow with
        | Continue value =>
            simp at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨updatedPolynomial, updatedPolynomialRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨scaledOffset, scaledOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨framedOffset, framedOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with
              ⟨⟨framedWindow, putFramedWindow⟩, framedWindowRun, run⟩
            simp_all
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨⟨qm31Slot, putQm31Slot⟩, qm31SlotRun, run⟩
            simp_all
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
                  V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
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
    generalize pairExact : (none, state.1) = pair at run
    rcases pair with ⟨actualOption, actualIter⟩
    cases actualOption with
    | none =>
        simp at pairExact
        subst actualIter
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb0, tailLimb0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced0, reduced0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb1, tailLimb1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced1, reduced1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨cm0, cm0Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb2, tailLimb2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced2, reduced2Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨tailLimb3, tailLimb3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨reduced3, reduced3Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨cm1, cm1Run, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨adjustedClaim, adjustedClaimRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨completedPolynomial, completedPolynomialRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨boundarySum, boundarySumRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨boundaryEqual, boundaryEqualRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨asserted, assertedRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨framedSlice, framedSliceRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨absorbedTranscript, absorbedTranscriptRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with
          ⟨⟨challengeResult, challengedTranscript⟩, challengeRun, run⟩
        simp_all
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨mappedChallenge, mappedChallengeRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨challengeFlow, challengeFlowRun, run⟩
        cases challengeFlow with
        | Continue challenge =>
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨nextClaim, nextClaimRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨nextPoint, nextPointRun, run⟩
            simp at run
            subst output
            exact hasAccepted
        | Break residual =>
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨convertedError, convertedErrorRun, run⟩
            simp at run
            subst output
            cases mappedChallenge with
            | Ok value =>
                simp [core.result.Result.Insts.CoreOpsTry.branch]
                  at challengeFlowRun
            | Err transcriptError =>
                simp [core.result.Result.Insts.CoreOpsTry.branch]
                  at challengeFlowRun
                subst residual
                simp [
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from]
                  at convertedErrorRun
                subst convertedError
                simp at hasAccepted
    | some sent => simp at pairExact



/-- Every `done` edge of the literal inner body satisfies both source-level
pending invariants needed by the outer proof: status one preserves the input
pending value, and an accepted `Ok` payload can only have been present at the
inner-loop entry.  Error exits may replace the pending value only by `Err`. -/
theorem inner_body_done_pending_safe
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output)) :
    (innerStatus output = 1#u32 →
      innerPending output = pendingReturn ∧ innerMeasure state = 0) ∧
      ∀ accepted,
        innerPending output = some (.Ok accepted) →
        pendingReturn = some (.Ok accepted) := by
  constructor
  · intro normal
    exact inner_body_done_status_one_core transcript point runningClaim round
      pendingReturn state output run normal
  · intro accepted hasAccepted
    exact inner_body_done_ok_origin_core transcript point runningClaim round
      pendingReturn state output run accepted hasAccepted
/- Superseded monolithic proof retained temporarily for source-diff
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
    simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind,
      prod_rec_eq_fst_snd, let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind,
          prod_rec_eq_fst_snd, let_prod_eq_fst_snd])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
    all_goals try simp_all
      [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind]
    repeat'
      (split at run <;>
        try simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Slice Std.U8))
    all_goals try simp_all
      [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind,
        prod_rec_eq_fst_snd, let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind,
          prod_rec_eq_fst_snd, let_prod_eq_fst_snd])
    all_goals try subst output
    all_goals try casesm
      (core.result.Result core.convert.Infallible v6_onefold.V6WireError)
    all_goals try casesm core.convert.Infallible
    all_goals try casesm
      (core.result.Result
        (RawQM31 × Array RawQM31 10#usize × RawQM31)
        v6_transcript.V6TranscriptError)
    all_goals try simp_all [innerPending, innerStatus,
      innerMeasure,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,
      v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind,
      prod_rec_eq_fst_snd, let_prod_eq_fst_snd]
    repeat'
      (split at run <;>
        try simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind,
          prod_rec_eq_fst_snd, let_prod_eq_fst_snd])
    all_goals try casesm (_ × RawTranscript)
    all_goals try simp_all
      [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind]
    repeat'
      (split at run <;>
        try simp_all [innerPending, innerStatus, Bind.bind, Aeneas.Std.bind])
    all_goals try subst output
    all_goals try casesm
      (core.result.Result core.convert.Infallible
        v6_transcript.V6TranscriptError)
    all_goals try casesm core.convert.Infallible
    all_goals try casesm
      (core.result.Result
        (RawQM31 × Array RawQM31 10#usize × RawQM31)
        v6_transcript.V6TranscriptError)
    all_goals try simp_all [innerPending, innerStatus,
      innerMeasure,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,
      v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
-/

/-- A status-one `done` edge of the literal inner body returns the same
pending value with which the 26-value loop was entered. -/
theorem inner_body_done_status_one_preserves_pending
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (normal : innerStatus output = 1#u32) :
    innerPending output = pendingReturn :=
  ((inner_body_done_pending_safe transcript point runningClaim round
    pendingReturn state output run).1 normal).1

/-- Status one also certifies that the exact inner range is exhausted. -/
theorem inner_body_done_status_one_exhausted
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (normal : innerStatus output = 1#u32) :
    innerMeasure state = 0 :=
  ((inner_body_done_pending_safe transcript point runningClaim round
    pendingReturn state output run).1 normal).2

/-- No exact `done` edge of the inner body can synthesize an accepted payload:
an `Ok` value at the output must equal the `Ok` value supplied on entry. -/
theorem inner_body_done_ok_origin
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (run : innerBody transcript point runningClaim round pendingReturn state =
      .ok (.done output))
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : innerPending output = some (.Ok accepted)) :
    pendingReturn = some (.Ok accepted) :=
  (inner_body_done_pending_safe transcript point runningClaim round
    pendingReturn state output run).2 accepted hasAccepted

/-- Status one at the end of any finite exact inner trace therefore preserves
the loop's fixed pending-return input. -/
theorem inner_trace_status_one_preserves_pending
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (trace : ExactLoopTrace
      (innerBody transcript point runningClaim round pendingReturn)
      state output)
    (normal : innerStatus output = 1#u32) :
    innerPending output = pendingReturn := by
  induction trace with
  | done equation =>
      exact inner_body_done_status_one_preserves_pending
        transcript point runningClaim round pendingReturn _ _ equation normal
  | cont _ tail inductionHypothesis =>
      exact inductionHypothesis normal

/-- The accepted-payload origin property is invariant over the entire exact
26-value inner trace. -/
theorem inner_trace_ok_origin
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (trace : ExactLoopTrace
      (innerBody transcript point runningClaim round pendingReturn)
      state output)
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : innerPending output = some (.Ok accepted)) :
    pendingReturn = some (.Ok accepted) := by
  induction trace with
  | done equation =>
      exact inner_body_done_ok_origin transcript point runningClaim round
        pendingReturn _ _ equation accepted hasAccepted
  | cont _ tail inductionHypothesis =>
      exact inductionHypothesis hasAccepted

/-- A status-one inner trace has exactly the number of continue edges encoded
by its incoming Rust range.  For the deployed `1..27` range this is 26. -/
theorem inner_trace_status_one_contCount_eq_measure
    (transcript : RawTranscript) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (round : Std.Usize)
    (pendingReturn : Option (core.result.Result
      (RawQM31 × Array RawQM31 10#usize × RawQM31)
      V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError))
    (state : InnerState) (output : InnerOutput)
    (trace : ExactLoopTrace
      (innerBody transcript point runningClaim round pendingReturn)
      state output)
    (normal : innerStatus output = 1#u32) :
    trace.contCount = innerMeasure state := by
  induction trace with
  | done equation =>
      have exhausted := inner_body_done_status_one_exhausted transcript point
        runningClaim round pendingReturn _ _ equation normal
      simpa [ExactLoopTrace.contCount] using exhausted.symm
  | cont equation tail inductionHypothesis =>
      have tailCount := inductionHypothesis normal
      simp only [ExactLoopTrace.contCount]
      rw [tailCount]
      exact inner_body_continue_measure_exact transcript point runningClaim
        round pendingReturn _ _ equation

abbrev AcceptedPayload :=
  core.result.Result
    (RawQM31 × Array RawQM31 10#usize × RawQM31)
    V7CompactSemanticFullGenerated.v6_transcript.V6TranscriptError

abbrev OuterState :=
  core.ops.range.Range Std.Usize × RawTranscript × Slice Std.U8 ×
  Std.Usize × Std.U64 × Std.U8 × Std.Usize ×
  Array RawQM31 10#usize × RawQM31 × Option AcceptedPayload

abbrev OuterOutput :=
  RawTranscript × Slice Std.U8 × Std.Usize × Std.U64 × Std.U8 ×
  Std.Usize × Option AcceptedPayload

noncomputable def outerBody (zero eta : RawQM31)
    (state : OuterState) : Result (ControlFlow OuterState OuterOutput) :=
  V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    eta state.1 state.2.1 state.2.2.1 state.2.2.2.1
    state.2.2.2.2.1 state.2.2.2.2.2.1 state.2.2.2.2.2.2.1
    state.2.2.2.2.2.2.2.1 state.2.2.2.2.2.2.2.2.1
    state.2.2.2.2.2.2.2.2.2

def outerMeasure (state : OuterState) : Nat :=
  state.1.end.val - state.1.start.val

/-- Pending payload carried by the generated outer-loop state. -/
def outerStatePending : OuterState → Option AcceptedPayload
  | (_, _, _, _, _, _, _, _, _, pending) => pending

/-- Pending payload exposed by a generated outer-loop terminal output. -/
def outerOutputPending : OuterOutput → Option AcceptedPayload
  | (_, _, _, _, _, _, pending) => pending

/-- A continue edge of the ten-round body preserves its pending payload.
The only non-syntactic step is the exact 26-value inner trace: the outer body
continues only at status one, where the inner source proof above preserves the
entry pending value. -/
theorem outer_body_cont_preserves_pending
    (zero eta : RawQM31) (state next : OuterState)
    (run : outerBody zero eta state = .ok (.cont next)) :
    outerStatePending next = outerStatePending state := by
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
    simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try casesm
      (_ × (_ → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending])
    all_goals try casesm (RawTranscript × _)
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending])
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
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending])
    all_goals try subst next
    all_goals try simp_all [outerStatePending]
    obtain ⟨innerTrace⟩ := inner_loop_success_has_exact_trace
      (run := by assumption)
    exact inner_trace_status_one_preserves_pending
      (trace := innerTrace) (normal := rfl)
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending]

/-- A terminal outer-body edge cannot invent an accepted payload.  Such a
payload is either the honest range-exhaustion result headed by the fixed
prefix `eta`, or it was already carried by the incoming pending slot. -/
theorem outer_body_done_ok_origin
    (zero eta : RawQM31) (state : OuterState) (output : OuterOutput)
    (run : outerBody zero eta state = .ok (.done output))
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : outerOutputPending output = some (.Ok accepted)) :
    (accepted.1 = eta ∧ outerMeasure state = 0) ∨
      outerStatePending state = some (.Ok accepted) := by
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
    simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
      outerOutputPending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
          outerOutputPending])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try casesm
      (_ × (_ → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
      outerOutputPending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
          outerOutputPending])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
      outerOutputPending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
          outerOutputPending])
    all_goals try casesm (RawTranscript × _)
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
      outerOutputPending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
          outerOutputPending])
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
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
      outerOutputPending]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerStatePending,
          outerOutputPending])
    all_goals try subst output
    all_goals try casesm
      (core.result.Result core.convert.Infallible v6_onefold.V6WireError)
    all_goals try casesm core.convert.Infallible
    all_goals try casesm AcceptedPayload
    all_goals try simp_all [outerStatePending, outerOutputPending,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
    obtain ⟨innerTrace⟩ := inner_loop_success_has_exact_trace
      (run := by assumption)
    exact Or.inr (inner_trace_ok_origin
      (trace := innerTrace) (accepted := accepted) (hasAccepted := rfl))
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    simp_all [Bind.bind, Aeneas.Std.bind]
    subst output
    rcases accepted with ⟨acceptedEta, acceptedPoint, acceptedClaim⟩
    simp_all [outerStatePending, outerOutputPending, outerMeasure]

/-- With an empty incoming pending slot, an accepted terminal edge is exactly
the exhausted-range branch. -/
theorem outer_body_done_ok_from_none_exhausted
    (zero eta : RawQM31) (state : OuterState) (output : OuterOutput)
    (run : outerBody zero eta state = .ok (.done output))
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : outerOutputPending output = some (.Ok accepted))
    (noPending : outerStatePending state = none) :
    outerMeasure state = 0 := by
  rcases outer_body_done_ok_origin zero eta state output run accepted
    hasAccepted with acceptedAtExhaustion | acceptedWasPending
  · exact acceptedAtExhaustion.2
  · rw [noPending] at acceptedWasPending
    simp at acceptedWasPending

/-- The accepted-payload origin invariant composes over an exact finite outer
trace.  A payload at the final output is headed by the fixed prefix eta unless
the identical payload was already pending at the trace's initial state. -/
theorem outer_trace_ok_origin
    (zero eta : RawQM31) (state : OuterState) (output : OuterOutput)
    (trace : ExactLoopTrace (outerBody zero eta) state output)
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : outerOutputPending output = some (.Ok accepted)) :
    accepted.1 = eta ∨
      outerStatePending state = some (.Ok accepted) := by
  induction trace with
  | done equation =>
      rcases outer_body_done_ok_origin zero eta _ _ equation accepted
        hasAccepted with acceptedAtExhaustion | acceptedWasPending
      · exact Or.inl acceptedAtExhaustion.1
      · exact Or.inr acceptedWasPending
  | cont equation tail inductionHypothesis =>
      rcases inductionHypothesis hasAccepted with
        acceptedFromEta | acceptedWasPending
      · exact Or.inl acceptedFromEta
      · exact Or.inr (by
          calc
            outerStatePending _ = outerStatePending _ :=
              (outer_body_cont_preserves_pending zero eta _ _ equation).symm
            _ = some (.Ok accepted) := acceptedWasPending)

private theorem outer_body_continue_measure_exact_core
    (zero eta : RawQM31) (state next : OuterState)
    (run : outerBody zero eta state = .ok (.cont next)) :
    outerMeasure next + 1 = outerMeasure state := by
  unfold outerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [bind_eq_ok_iff] at run
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
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨framedSlot, framedSlotRun, run⟩
        rcases framedSlot with ⟨framedByte, putFramedByte⟩
        simp at run
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨roundByte, roundByteRun, run⟩
        rw [bind_eq_ok_iff] at run
        rcases run with ⟨readerPair, readerRun, run⟩
        rcases readerPair with ⟨readerResult, fields⟩
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
            simp_all
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
              ⟨transcript1, s3, i17, i18, i19, i20, point1,
                runningClaim1, pendingReturn1, status⟩
            simp at run
            split at run
            · simp at run
              subst next
              rcases pairExact with ⟨roundExact, iterExact⟩
              subst actualIter
              rcases nextSpec with ⟨nextStartVal, nextEndExact⟩
              have roundVal := congrArg (fun value : Std.Usize => value.val)
                roundExact
              have nextEndVal := congrArg (fun value : Std.Usize => value.val)
                nextEndExact
              unfold outerMeasure
              change nextIter.end.val - nextIter.start.val + 1 =
                state.1.end.val - state.1.start.val
              omega
            · cases pendingReturn1 <;> simp at run
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
    generalize pairExact : (none, state.1) = pair at run
    rcases pair with ⟨actualOption, actualIter⟩
    cases actualOption with
    | none =>
        simp at pairExact
        subst actualIter
        simp at run
    | some round => simp at pairExact

/-- A continue edge of the production ten-round loop advances its literal
Rust range by exactly one.  The inner compact-reader loop may fail or
terminate the outer loop, but cannot manufacture a continue edge with a
different range. -/
theorem outer_body_continue_measure_exact
    (zero eta : RawQM31) (state next : OuterState)
    (run : outerBody zero eta state = .ok (.cont next)) :
    outerMeasure next + 1 = outerMeasure state :=
  outer_body_continue_measure_exact_core zero eta state next run
/- Superseded broad automation retained temporarily for source-diff
provenance; it is not part of the compiled theorem surface.
  unfold outerBody at run
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0.body
    at run
  by_cases active : state.1.start.val < state.1.end.val
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_some_spec state.1 active
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextStart,
        nextEnd⟩ := WP.spec_imp_exists nextSpec
    rw [optionExact] at nextRun
    rw [nextRun] at run
    simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure])
    all_goals try casesm (_ × v6_onefold.V6FixedFieldReader)
    all_goals try casesm
      (_ × (_ → Std.Array Std.U8 433#usize))
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure])
    all_goals try casesm
      (Slice Std.U8 × (Slice Std.U8 → Std.Array Std.U8 433#usize))
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure])
    all_goals try casesm (RawTranscript × _)
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure])
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
    all_goals try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure]
    repeat'
      (split at run <;>
        try simp_all [Bind.bind, Aeneas.Std.bind, outerMeasure])
    all_goals subst next
    all_goals simp [outerMeasure, nextEnd, nextStart]
    all_goals omega
  · have nextSpec :=
      core.iter.range.IteratorRange.next_Usize_none_spec state.1 (by omega)
    obtain ⟨⟨option, nextIter⟩, nextRun, optionExact, nextExact⟩ :=
      WP.spec_imp_exists nextSpec
    rw [optionExact, nextExact] at nextRun
    rw [nextRun] at run
    simp_all [Bind.bind, Aeneas.Std.bind]
-/

/-- The exact one-step measure equation gives the well-founded decrease used
to expose a finite trace from the translated Aeneas loop. -/
theorem outer_body_continue_decreases
    (zero eta : RawQM31) (state next : OuterState)
    (run : outerBody zero eta state = .ok (.cont next)) :
    outerMeasure next < outerMeasure state := by
  have exactStep := outer_body_continue_measure_exact zero eta state next run
  omega

/-- An accepted outer trace entered with no pending payload has exactly the
number of continue edges in its initial Rust range.  The deployed `0..10`
trace therefore has ten and only ten semantic rounds. -/
theorem outer_trace_from_none_contCount_eq_measure
    (zero eta : RawQM31) (state : OuterState) (output : OuterOutput)
    (trace : ExactLoopTrace (outerBody zero eta) state output)
    (accepted : RawQM31 × Array RawQM31 10#usize × RawQM31)
    (hasAccepted : outerOutputPending output = some (.Ok accepted))
    (noPending : outerStatePending state = none) :
    trace.contCount = outerMeasure state := by
  induction trace with
  | done equation =>
      have exhausted := outer_body_done_ok_from_none_exhausted zero eta _ _
        equation accepted hasAccepted noPending
      simpa [ExactLoopTrace.contCount] using exhausted.symm
  | @cont current nextState finalOutput equation tail inductionHypothesis =>
      have nextNoPending : outerStatePending nextState = none := by
        rw [outer_body_cont_preserves_pending zero eta current nextState
          equation, noPending]
      have tailCount := inductionHypothesis hasAccepted nextNoPending
      simp only [ExactLoopTrace.contCount]
      rw [tailCount]
      exact outer_body_continue_measure_exact zero eta current nextState
        equation

/-- A successful call to the generated ten-round loop likewise exposes the
exact generated outer-body trace. -/
theorem outer_loop_success_has_exact_trace
    (zero : RawQM31) (iter : core.ops.range.Range Std.Usize)
    (transcript : RawTranscript) (slice : Slice Std.U8)
    (byteIndex : Std.Usize) (buffer : Std.U64)
    (bufferedBits : Std.U8) (remaining : Std.Usize)
    (eta : RawQM31) (point : Array RawQM31 10#usize)
    (runningClaim : RawQM31) (pendingReturn : Option AcceptedPayload)
    (output : OuterOutput)
    (run :
      V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0
        iter transcript slice byteIndex buffer bufferedBits remaining eta
        point runningClaim pendingReturn = .ok output) :
    Nonempty (ExactLoopTrace (outerBody zero eta)
      (iter, transcript, slice, byteIndex, buffer, bufferedBits, remaining,
        point, runningClaim, pendingReturn)
      output) := by
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0
    at run
  change
    loop (outerBody zero eta)
      (iter, transcript, slice, byteIndex, buffer, bufferedBits, remaining,
        point, runningClaim, pendingReturn) = .ok output
    at run
  exact loop_success_has_exact_trace
    (outerBody zero eta) outerMeasure
    (outer_body_continue_decreases zero eta)
    (iter, transcript, slice, byteIndex, buffer, bufferedBits, remaining,
      point, runningClaim, pendingReturn)
    output run

/-! ## Accepted top-level call -/

/-- The exact successful source facts exposed by the generated top-level
compact semantic verifier.  In particular, the `outerRun` field is the
literal ten-round call made after the initial field read and masked-sumcheck
prefix; `outerTrace` is derived from that call rather than supplied by an
independent model.  `prefixEta` deliberately records the value passed into
the loop separately from the accepted payload's `eta`; their equality is a
consequence of completing the exact ten-round trace, not a premise hidden in
this wrapper. -/
structure AcceptedMainExecution
    (inputTranscript outputTranscript : RawTranscript)
    (inputFields outputFields : RawReader)
    (eta : RawQM31) (point : Array RawQM31 10#usize)
    (terminalClaim : RawQM31) : Type where
  initialClaim : RawQM31
  fieldsAfterInitial : RawReader
  transcriptAfterBegin : RawTranscript
  prefixEta : RawQM31
  zero : RawQM31
  initialRead :
    V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
        inputFields =
      .ok (.Ok initialClaim, fieldsAfterInitial)
  beginRun :
    state_only_hiding.begin_state_only_masked_sumcheck
        inputTranscript initialClaim =
      .ok (.Ok prefixEta, transcriptAfterBegin)
  zeroRun : zero = field.QM31.ZERO
  outerRun :
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0
        { start := 0#usize,
          «end» := V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_ROUNDS }
        transcriptAfterBegin fieldsAfterInitial.packed.bytes
        fieldsAfterInitial.packed.byte_index
        fieldsAfterInitial.packed.buffer
        fieldsAfterInitial.packed.buffered_bits
        fieldsAfterInitial.remaining prefixEta (Array.repeat 10#usize zero)
        initialClaim none =
      .ok (outputTranscript, outputFields.packed.bytes,
        outputFields.packed.byte_index, outputFields.packed.buffer,
        outputFields.packed.buffered_bits, outputFields.remaining,
        some (.Ok (eta, point, terminalClaim)))
  outerTrace : Nonempty (ExactLoopTrace (outerBody zero prefixEta)
    ({ start := 0#usize,
       «end» := V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_ROUNDS },
      transcriptAfterBegin, fieldsAfterInitial.packed.bytes,
      fieldsAfterInitial.packed.byte_index, fieldsAfterInitial.packed.buffer,
      fieldsAfterInitial.packed.buffered_bits, fieldsAfterInitial.remaining,
      Array.repeat 10#usize zero, initialClaim, none)
    (outputTranscript, outputFields.packed.bytes,
      outputFields.packed.byte_index, outputFields.packed.buffer,
      outputFields.packed.buffered_bits, outputFields.remaining,
      some (.Ok (eta, point, terminalClaim))))

/-- In every exact accepted execution, the eta returned in the accepted Rust
payload is precisely the eta sampled by the masked-sumcheck prefix and passed
unchanged to all ten semantic rounds. -/
theorem accepted_execution_prefix_eta_eq
    {inputTranscript outputTranscript : RawTranscript}
    {inputFields outputFields : RawReader}
    {eta : RawQM31} {point : Array RawQM31 10#usize}
    {terminalClaim : RawQM31}
    (execution : AcceptedMainExecution inputTranscript outputTranscript
      inputFields outputFields eta point terminalClaim) :
    execution.prefixEta = eta := by
  obtain ⟨trace⟩ := execution.outerTrace
  have origin := outer_trace_ok_origin
    (trace := trace)
    (accepted := (eta, point, terminalClaim))
    (hasAccepted := rfl)
  rcases origin with acceptedEta | alreadyPending
  · exact acceptedEta.symm
  · simp [outerStatePending] at alreadyPending

/-- A successful generated top-level result cannot bypass either reader,
prefix, or loop control flow.  It exposes the exact accepted outer trace and
preserves both the prefix eta and the accepted payload returned to the
production caller, leaving their source-derived equality to trace inversion. -/
theorem accepted_main_exposes_exact_outer_trace
    (inputTranscript outputTranscript : RawTranscript)
    (inputFields outputFields : RawReader)
    (eta : RawQM31) (point : Array RawQM31 10#usize)
    (terminalClaim : RawQM31)
    (run :
      V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck
          inputTranscript inputFields =
        .ok (.Ok (eta, point, terminalClaim), outputTranscript,
          outputFields)) :
    Nonempty (AcceptedMainExecution inputTranscript outputTranscript
      inputFields outputFields eta point terminalClaim) := by
  unfold
    V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck
    at run
  generalize initialReadEquation :
      V7CompactSemanticFullGenerated.v6_onefold.V6FixedFieldReader.next_qm31
        inputFields = initialReadResult at run
  cases initialReadResult with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok initialReadPair =>
      rcases initialReadPair with ⟨initialOutcome, fieldsAfterInitial⟩
      cases initialOutcome with
      | Err wireError =>
          simp_all [Bind.bind, Aeneas.Std.bind,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,
            v6_transcript.V6TranscriptError.Insts.CoreConvertFromV6WireError.from]
      | Ok initialClaim =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
            at run
          generalize beginEquation :
              state_only_hiding.begin_state_only_masked_sumcheck
                inputTranscript initialClaim = beginResult at run
          cases beginResult with
          | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
          | div => simp_all [Bind.bind, Aeneas.Std.bind]
          | ok beginPair =>
              rcases beginPair with ⟨beginOutcome, transcriptAfterBegin⟩
              cases beginOutcome with
              | Err scheduleError =>
                  simp_all [Bind.bind, Aeneas.Std.bind,
                    core.result.Result.map_err,
                    v6_transcript.verify_compact_semantic_sumcheck.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyHidingScheduleErrorV6TranscriptError.call_once,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from]
              | Ok actualEta =>
                  simp only [core.result.Result.map_err,
                    core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
                    at run
                  generalize outerEquation :
                      V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck_loop0
                        { start := 0#usize,
                          «end» :=
                            V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_ROUNDS }
                        transcriptAfterBegin
                        fieldsAfterInitial.packed.bytes
                        fieldsAfterInitial.packed.byte_index
                        fieldsAfterInitial.packed.buffer
                        fieldsAfterInitial.packed.buffered_bits
                        fieldsAfterInitial.remaining actualEta
                        (Array.repeat 10#usize field.QM31.ZERO) initialClaim
                        none = outerResult at run
                  cases outerResult with
                  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                  | div => simp_all [Bind.bind, Aeneas.Std.bind]
                  | ok outerOutput =>
                      rcases outerOutput with
                        ⟨actualTranscript, actualSlice, actualIndex,
                          actualBuffer, actualBits, actualRemaining, pending⟩
                      cases pending with
                      | none => simp_all [Bind.bind, Aeneas.Std.bind]
                      | some payload =>
                          cases payload with
                          | Err transcriptError => simp_all
                          | Ok accepted =>
                              rcases accepted with
                                ⟨returnedEta, returnedPoint,
                                  returnedTerminal⟩
                              have outputExact :
                                  returnedEta = eta ∧
                                    returnedPoint = point ∧
                                    returnedTerminal = terminalClaim ∧
                                    actualTranscript = outputTranscript ∧
                                    ({
                                      packed := {
                                        bytes := actualSlice
                                        byte_index := actualIndex
                                        buffer := actualBuffer
                                        buffered_bits := actualBits }
                                      remaining := actualRemaining } :
                                        RawReader) = outputFields := by
                                simpa [Bind.bind, Aeneas.Std.bind,
                                  initialReadEquation, beginEquation,
                                  outerEquation] using run
                              rcases outputExact with
                                ⟨returnedEtaExact, returnedPointExact,
                                  returnedTerminalExact, transcriptExact,
                                  fieldsExact⟩
                              subst returnedEta
                              subst returnedPoint
                              subst returnedTerminal
                              subst actualTranscript
                              cases fieldsExact
                              refine ⟨{
                                initialClaim := initialClaim
                                fieldsAfterInitial := fieldsAfterInitial
                                transcriptAfterBegin := transcriptAfterBegin
                                prefixEta := actualEta
                                zero := field.QM31.ZERO
                                initialRead := initialReadEquation
                                beginRun := beginEquation
                                zeroRun := rfl
                                outerRun := outerEquation
                                outerTrace := ?_ }⟩
                              exact outer_loop_success_has_exact_trace
                                field.QM31.ZERO
                                { start := 0#usize,
                                  «end» :=
                                    V7CompactSemanticFullGenerated.v6_onefold.V6_SEMANTIC_ROUNDS }
                                transcriptAfterBegin
                                fieldsAfterInitial.packed.bytes
                                fieldsAfterInitial.packed.byte_index
                                fieldsAfterInitial.packed.buffer
                                fieldsAfterInitial.packed.buffered_bits
                                fieldsAfterInitial.remaining actualEta
                                (Array.repeat 10#usize field.QM31.ZERO)
                                initialClaim none
                                (outputTranscript,
                                  actualSlice,
                                  actualIndex,
                                  actualBuffer,
                                  actualBits,
                                  actualRemaining,
                                  some (.Ok (eta, point, terminalClaim)))
                                outerEquation

/-- The successful production entrypoint exposes a single exact source
execution together with the derived equality between prefix eta and returned
eta.  The equality is not a wrapper premise. -/
theorem accepted_main_exposes_exact_prefix_eta
    (inputTranscript outputTranscript : RawTranscript)
    (inputFields outputFields : RawReader)
    (eta : RawQM31) (point : Array RawQM31 10#usize)
    (terminalClaim : RawQM31)
    (run :
      V7CompactSemanticFullGenerated.v6_transcript.verify_compact_semantic_sumcheck
          inputTranscript inputFields =
        .ok (.Ok (eta, point, terminalClaim), outputTranscript,
          outputFields)) :
    Nonempty { execution : AcceptedMainExecution inputTranscript
      outputTranscript inputFields outputFields eta point terminalClaim //
        execution.prefixEta = eta } := by
  obtain ⟨execution⟩ := accepted_main_exposes_exact_outer_trace
    inputTranscript outputTranscript inputFields outputFields eta point
    terminalClaim run
  exact ⟨⟨execution, accepted_execution_prefix_eta_eq execution⟩⟩

#print axioms loop_success_has_exact_trace
#print axioms inner_body_continue_measure_exact
#print axioms inner_body_continue_decreases
#print axioms inner_loop_success_has_exact_trace
#print axioms inner_body_done_pending_safe
#print axioms inner_body_done_status_one_preserves_pending
#print axioms inner_body_done_status_one_exhausted
#print axioms inner_body_done_ok_origin
#print axioms inner_trace_status_one_preserves_pending
#print axioms inner_trace_ok_origin
#print axioms inner_trace_status_one_contCount_eq_measure
#print axioms outer_body_cont_preserves_pending
#print axioms outer_body_done_ok_origin
#print axioms outer_body_done_ok_from_none_exhausted
#print axioms outer_trace_ok_origin
#print axioms outer_body_continue_measure_exact
#print axioms outer_body_continue_decreases
#print axioms outer_trace_from_none_contCount_eq_measure
#print axioms outer_loop_success_has_exact_trace
#print axioms accepted_execution_prefix_eta_eq
#print axioms accepted_main_exposes_exact_outer_trace
#print axioms accepted_main_exposes_exact_prefix_eta

end V7CompactSemanticSourceBridge
