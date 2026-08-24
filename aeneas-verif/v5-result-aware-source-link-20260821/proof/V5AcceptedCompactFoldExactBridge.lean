import V5AcceptedCompactExecutionExact
import V5CompactNewSourceUnroll
import V5CompactFinalReleasedBridge
import V5CompactFoldExactRootBridge
import V5CompactFoldExactUnrolledStateBridge

/-!
# Corrected compact-fold extraction in one accepted execution

This module closes the compact-fold source boundary left explicit by
`V5AcceptedCompactExecutionExact`.  It connects three representations of the
same released fold:

* the normalized, corrected Charon/Aeneas extraction;
* the source-shaped compact-fold wrapper used by the semantic proof; and
* the four successful fold calls recovered from one accepted relation trace.

The bridge is structural.  It does not assume an iterator equation or a
Rust-to-model oracle.
-/

namespace AspisV5AcceptedCompactFoldExactBridge

open Aeneas Aeneas.Std Result
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion
open AspisV5CompactCallerWrapperExact
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes
open AspisV5CompactFoldExactBlockBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev CallerRaw := AspisV5CompactCallerWrapperExact.CallerRaw
abbrev CallerBlock := AspisV5CompactCallerWrapperExact.CallerBlock
abbrev CallerState := AspisV5CompactCallerWrapperExact.CallerState

@[simp] theorem exactToLegacyRaw_callerToExactRaw
    (value : CallerRaw) :
    exactToLegacyRaw (callerToExactRaw value) = callerToFoldRaw value := by
  cases value <;> rfl

@[simp] theorem exactToLegacyBlock_callerBlockToExact
    (block : CallerBlock) :
    exactToLegacyBlock (callerBlockToExact block) =
      callerBlockToFold block := by
  cases block <;> rfl

@[simp] theorem exactToLegacyState_callerStateToExact
    (state : CallerState) :
    exactToLegacyState (callerStateToExact state) =
      callerStateToFold state := by
  cases state with
  | mk blocks deltaScale folds =>
    cases blocks with
    | mk values lengthExact =>
      simp only [exactToLegacyState, callerStateToExact,
        exactBlockArrayToLegacy, callerStateToFold]
      congr 1
      · apply Subtype.ext
        simp [List.map_map, Function.comp_def]

@[simp] theorem foldStateToCaller_exactToLegacyState
    (state : ExactState) :
    foldStateToCaller (exactToLegacyState state) =
      exactStateToCaller state := by
  cases state with
  | mk blocks deltaScale folds =>
    cases blocks with
    | mk values lengthExact =>
      simp only [foldStateToCaller, exactToLegacyState,
        exactBlockArrayToLegacy, exactStateToCaller]
      congr 1
      · apply Subtype.ext
        simp [List.map_map, Function.comp_def, foldBlockToCaller,
          exactToLegacyBlock, exactBlockToCaller, foldToCallerRaw,
          exactToLegacyRaw, exactToCallerRaw]

/-- A successful source-shaped fold is also a successful call of the clean,
corrected Aeneas extraction, with exactly the same caller-shaped output. -/
theorem exactExtractedCallerFold_success_of_corrected
    (state output : CallerState) (alpha : CallerRaw)
    (foldBound : state.folds.val < 4)
    (run : correctedCallerFold state alpha = .ok output) :
    exactExtractedCallerFold state alpha = .ok output := by
  have exactFoldBound : (callerStateToExact state).folds.val < 4 := by
    change state.folds.val < 4
    exact foldBound
  obtain ⟨folded, foldedRun, outputEq⟩ :=
    correctedCallerFold_success_exposes_subcall state output alpha run
  have sourceRun :
      V5CompactFoldSource.unrolledFold
          (callerStateToFold state) (callerToFoldRaw alpha) = .ok folded :=
    V5CompactFoldSource.fold_success_unrolled
      (callerStateToFold state) folded (callerToFoldRaw alpha)
      (by simpa using foldBound) foldedRun
  have transported :
      mapResult exactToLegacyState
          (AspisV5CompactFoldExactSource.unrolledFold
            (callerStateToExact state) (callerToExactRaw alpha)) =
        .ok folded := by
    rw [AspisV5CompactFoldExactUnrolledStateBridge.exact_unrolled_to_legacy
      (callerStateToExact state) (callerToExactRaw alpha)
      exactFoldBound]
    simpa using sourceRun
  generalize exactRun :
      AspisV5CompactFoldExactSource.unrolledFold
        (callerStateToExact state) (callerToExactRaw alpha) = exactResult
      at transported
  cases exactResult with
  | fail error => simp [mapResult] at transported
  | div => simp [mapResult] at transported
  | ok exactFolded =>
    have foldedExact : exactToLegacyState exactFolded = folded := by
      simpa [mapResult] using transported
    unfold exactExtractedCallerFold
    rw [AspisV5CompactFoldExactRootBridge.extracted_root_eq_unrolled
      (callerStateToExact state) (callerToExactRaw alpha)
      exactFoldBound]
    rw [exactRun]
    simp only [bind_tc_ok, Result.ok.injEq]
    rw [outputEq, ← foldedExact]
    exact (foldStateToCaller_exactToLegacyState exactFolded).symm

/-- After the documented accepted-caller write-back correction, the generated
legacy fold and the source-shaped wrapper are definitionally the same term. -/
theorem acceptedGeneratedFold_eq_corrected
    (state : FoldState) (alpha : FoldRaw) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
        state alpha = V5CompactFoldCorrectedWrapper.fold state alpha := by
  rfl

private theorem released_counter_of_delta_factor_success
    (folds : Std.U8) (alpha alpha2 output : FoldRaw)
    (run :
      (match folds with
        | 0#uscalar => ok V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE
        | 1#uscalar => ok V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE
        | 2#uscalar => ok alpha2
        | 3#uscalar => ok alpha
        | _ => fail Error.panic) = .ok output) :
    folds.val < 4 := by
  split at run <;> simp_all <;> decide

/-- Success of the source-shaped fold itself proves that its byte counter is
one of the four released values.  This fact comes from the checked source
match; it is not supplied by the theorem caller. -/
theorem correctedCallerFold_success_counter_bound
    (state output : CallerState) (alpha : CallerRaw)
    (run : correctedCallerFold state alpha = .ok output) :
    state.folds.val < 4 := by
  obtain ⟨folded, foldedRun, _⟩ :=
    correctedCallerFold_success_exposes_subcall state output alpha run
  unfold V5CompactFoldCorrectedWrapper.fold at foldedRun
  generalize alpha2Run :
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.square
        (callerToFoldRaw alpha) = alpha2Result at foldedRun
  cases alpha2Result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
  | ok alpha2 =>
    simp only [bind_tc_ok] at foldedRun
    generalize alpha3Run :
        V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul alpha2
          (callerToFoldRaw alpha) = alpha3Result at foldedRun
    cases alpha3Result with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
    | div => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
    | ok alpha3 =>
      simp only [bind_tc_ok] at foldedRun
      generalize prepared0Run :
          V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.new
            alpha3 = prepared0Result at foldedRun
      cases prepared0Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
      | div => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
      | ok prepared0 =>
        simp only [bind_tc_ok] at foldedRun
        generalize prepared1Run :
            V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.new
              alpha2 = prepared1Result at foldedRun
        cases prepared1Result with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
        | div => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
        | ok prepared1 =>
          simp only [bind_tc_ok] at foldedRun
          generalize prepared2Run :
              V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.new
                (callerToFoldRaw alpha) = prepared2Result at foldedRun
          cases prepared2Result with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
          | ok prepared2 =>
            simp only [bind_tc_ok,
              V5RelationCompactFoldGenerated.MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter]
                at foldedRun
            generalize loopRun :
                V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
                  { slice := Array.to_slice (callerStateToFold state).blocks }
                  (fun current => current) (callerStateToFold state).folds
                  (callerToFoldRaw alpha) alpha2 alpha3
                  (Array.make 3#usize [prepared0, prepared1, prepared2]) =
                    loopResult at foldedRun
            cases loopResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
            | div => simp [Bind.bind, Aeneas.Std.bind] at foldedRun
            | ok loopOutput =>
              rcases loopOutput with ⟨loopIndex, loopBack⟩
              simp only [bind_tc_ok] at foldedRun
              split at foldedRun <;> simp_all <;> decide

/-- One successful generated caller fold is simultaneously witnessed by the
corrected caller wrapper and by the normalized corrected Aeneas extraction. -/
structure ExactAndCorrectedFoldRun
    (state output : CallerState) (alpha : CallerRaw) : Prop where
  exactRun : exactExtractedCallerFold state alpha = .ok output
  correctedRun : correctedCallerFold state alpha = .ok output

theorem generated_fold_success_exact_and_corrected
    (state output : CallerState) (alpha : CallerRaw) (folded : FoldState)
    (run :
      V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
          (callerStateToFold state) (callerToFoldRaw alpha) =
        .ok folded)
    (outputExact : output = foldStateToCaller folded) :
    ExactAndCorrectedFoldRun state output alpha := by
  have correctedSubcall :
      V5CompactFoldCorrectedWrapper.fold
          (callerStateToFold state) (callerToFoldRaw alpha) =
        .ok folded := by
    rw [← acceptedGeneratedFold_eq_corrected]
    exact run
  have correctedRun : correctedCallerFold state alpha = .ok output := by
    unfold correctedCallerFold
    rw [correctedSubcall]
    simpa using outputExact.symm
  have foldBound := correctedCallerFold_success_counter_bound
    state output alpha correctedRun
  exact ⟨exactExtractedCallerFold_success_of_corrected state output alpha
    foldBound correctedRun, correctedRun⟩

/-- The four accepted fold calls, retaining both the normalized corrected
Aeneas result and the source-shaped caller result for each call. -/
structure AcceptedExactAndCorrectedFoldRuns
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array CallerRaw 4#usize}
    {alphas : Array CallerRaw 4#usize}
    {kappa inactiveClaim : CallerRaw}
    {roundChallenges : Array CallerRaw 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : CallerRaw}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) : Prop
    where
  fold0 : ExactAndCorrectedFoldRun trace.calls.compact trace.additive1
    (acceptedAlphaAt alphas 0)
  fold1 : ExactAndCorrectedFoldRun trace.additive1 trace.additive2
    (acceptedAlphaAt alphas 1)
  fold2 : ExactAndCorrectedFoldRun trace.additive2 trace.additive3
    (acceptedAlphaAt alphas 2)
  fold3 : ExactAndCorrectedFoldRun trace.additive3 trace.additive4
    (acceptedAlphaAt alphas 3)

/-- Every accepted trace retains all four exact-extraction results alongside
the corresponding source-shaped caller results. -/
theorem accepted_trace_exact_and_corrected_fold_runs
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array CallerRaw 4#usize}
    {alphas : Array CallerRaw 4#usize}
    {kappa inactiveClaim : CallerRaw}
    {roundChallenges : Array CallerRaw 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : CallerRaw}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    AcceptedExactAndCorrectedFoldRuns trace := by
  obtain ⟨calls⟩ := accepted_trace_exposes_compact_wrapper_subcalls trace
  have verified0 := generated_fold_success_exact_and_corrected
    trace.calls.compact trace.additive1 (acceptedAlphaAt alphas 0)
    calls.foldState1 calls.fold0Run calls.fold0Output
  have verified1 := generated_fold_success_exact_and_corrected
    trace.additive1 trace.additive2 (acceptedAlphaAt alphas 1)
    calls.foldState2 calls.fold1Run calls.fold1Output
  have verified2 := generated_fold_success_exact_and_corrected
    trace.additive2 trace.additive3 (acceptedAlphaAt alphas 2)
    calls.foldState3 calls.fold2Run calls.fold2Output
  have verified3 := generated_fold_success_exact_and_corrected
    trace.additive3 trace.additive4 (acceptedAlphaAt alphas 3)
    calls.foldState4 calls.fold3Run calls.fold3Output
  exact ⟨verified0, verified1, verified2, verified3⟩

/-- Every accepted relation trace supplies the four corrected compact-fold
equalities required by the maintained terminal-value theorem.  The exact
extraction results remain available in the retained run record above; no
source-equality premise remains. -/
theorem accepted_trace_compact_fold_source_equality
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array CallerRaw 4#usize}
    {alphas : Array CallerRaw 4#usize}
    {kappa inactiveClaim : CallerRaw}
    {roundChallenges : Array CallerRaw 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : CallerRaw}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    AspisV5AcceptedCompactExecutionExact.CompactFoldSourceEquality trace := by
  have verified := accepted_trace_exact_and_corrected_fold_runs trace
  exact ⟨verified.fold0.correctedRun, verified.fold1.correctedRun,
    verified.fold2.correctedRun, verified.fold3.correctedRun⟩

#print axioms exactExtractedCallerFold_success_of_corrected
#print axioms acceptedGeneratedFold_eq_corrected
#print axioms generated_fold_success_exact_and_corrected
#print axioms accepted_trace_exact_and_corrected_fold_runs
#print axioms accepted_trace_compact_fold_source_equality

end AspisV5AcceptedCompactFoldExactBridge
