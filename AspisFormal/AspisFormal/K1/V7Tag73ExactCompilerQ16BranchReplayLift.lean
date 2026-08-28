import AspisFormal.K1.V7Tag73ExactCompilerQ16BranchCoordinates
import AspisFormal.K1.V7Tag73SchedulerNativeQ16ForestReplay

/-!
# Lift exact q16 coordinates through an executable branch

The local source-anchored coordinate theorem is folded across every duplex
pair.  Both cached and fresh coordinates preserve the same chronological root
alignment, so the result applies without classifying who first queried a q16
coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerQ16BranchReplayLift

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeQ16Replay
open AspisK1.V7Tag73SchedulerNativeQ16ForestReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerQ16CoordinateStep

noncomputable section

/-- Fold the one-coordinate theorem across a complete output/advance chain. -/
theorem run_scheduler_native_q16_branch_tail_actual_chain
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerQ16CoordinateStep input) :
    ∀ {digest : Digest256} {outputs advances : List Digest256},
      GammaTableCoordinateChain (exactOperationalTable input) digest outputs
          advances →
      ∀ (state : SchedulerNativeQ16Cursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)),
        ExactCompilerRootQ16CursorAligned input state →
        ∃ final,
          runSchedulerNativeQ16BranchTail transitionFuel
              (outputs.zip advances) digest state = .ok final ∧
          Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  intro digest outputs advances chain
  induction chain with
  | done digest =>
      intro state aligned
      exact ⟨state, rfl, ⟨aligned⟩⟩
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      intro state aligned
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (q16OutputInput digest) output state aligned
          (by simpa [q16OutputInput, gammaOutputInput] using outputLookup)
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (q16AdvanceInput digest) advanced afterOutput
          outputAligned
          (by simpa [q16AdvanceInput, gammaAdvanceInput] using advanceLookup)
      obtain ⟨final, tailRun, finalAligned⟩ :=
        ih afterAdvance advanceAligned
      refine ⟨final, ?_, finalAligned⟩
      simp only [List.zip_cons_cons, runSchedulerNativeQ16BranchTail]
      rw [outputRun]
      simp only
      rw [advanceRun]
      exact tailRun

/-- A nonempty exact coordinate chain executes the branch-from-cursor entry
point and preserves source alignment. -/
theorem run_scheduler_native_q16_branch_from_cursor_actual_chain
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerQ16CoordinateStep input)
    (branch : SchedulerNativeQ16Branch) (forest : TotalQ16DuplexForest)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      branch.initialDigest outputs advances)
    (outputsPositive : outputs ≠ [])
    (pairsExact : q16BranchDuplexPairs branch forest = outputs.zip advances)
    (state : SchedulerNativeQ16Cursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (aligned : ExactCompilerRootQ16CursorAligned input state) :
    ∃ final,
      runSchedulerNativeQ16BranchFromCursor transitionFuel branch forest state =
        .ok final ∧
      Nonempty (ExactCompilerRootQ16CursorAligned input final) := by
  cases chain with
  | done digest =>
      exact (outputsPositive rfl).elim
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail =>
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (q16OutputInput branch.initialDigest) output
          state aligned
          (by simpa [q16OutputInput, gammaOutputInput] using outputLookup)
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (q16AdvanceInput branch.initialDigest) advanced
          afterOutput outputAligned
          (by simpa [q16AdvanceInput, gammaAdvanceInput] using advanceLookup)
      obtain ⟨final, tailRun, finalAligned⟩ :=
        run_scheduler_native_q16_branch_tail_actual_chain input coordinateStep
          tail afterAdvance advanceAligned
      refine ⟨final, ?_, finalAligned⟩
      unfold runSchedulerNativeQ16BranchFromCursor
      rw [pairsExact]
      simp only [List.zip_cons_cons]
      rw [outputRun]
      simp only
      rw [advanceRun]
      exact tailRun

#print axioms run_scheduler_native_q16_branch_tail_actual_chain
#print axioms run_scheduler_native_q16_branch_from_cursor_actual_chain

end

end AspisK1.V7Tag73ExactCompilerQ16BranchReplayLift
