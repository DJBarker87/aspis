import V5RelationCompactFoldGeneratedExact
import V5RelationCallerGenerated

/-!
# Corrected extracted compact fold in caller types

This module imports the explicitly namespaced 24 August 2026 extraction and
converts its input and output to the types used by the accepted relation
caller.  Keeping this wrapper separate prevents the older loop-induction
artifact from being selected accidentally by module-name resolution.
-/

namespace AspisV5CompactFoldExactCallerBridge

open Aeneas Aeneas.Std Result

abbrev CallerRaw := V5RelationCallerGenerated.aspis_core.field.QM31
abbrev CallerBlock :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev CallerState :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights

abbrev ExactRaw :=
  V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31
abbrev ExactBlock :=
  V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalBlock
abbrev ExactState :=
  V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights

def callerToExactRaw (value : CallerRaw) : ExactRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def exactToCallerRaw (value : ExactRaw) : CallerRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerBlockToExact (block : CallerBlock) : ExactBlock :=
  { scale := callerToExactRaw block.scale
    power_lo := callerToExactRaw block.power_lo
    power_hi := callerToExactRaw block.power_hi
    selector := block.selector }

def exactBlockToCaller (block : ExactBlock) : CallerBlock :=
  { scale := exactToCallerRaw block.scale
    power_lo := exactToCallerRaw block.power_lo
    power_hi := exactToCallerRaw block.power_hi
    selector := block.selector }

def callerStateToExact (state : CallerState) : ExactState :=
  { blocks := ⟨state.blocks.val.map callerBlockToExact,
      by simpa using state.blocks.property⟩
    delta_scale := callerToExactRaw state.delta_scale
    folds := state.folds }

def exactStateToCaller (state : ExactState) : CallerState :=
  { blocks := ⟨state.blocks.val.map exactBlockToCaller,
      by simpa using state.blocks.property⟩
    delta_scale := exactToCallerRaw state.delta_scale
    folds := state.folds }

/-- The corrected Aeneas root, expressed in the accepted caller's types. -/
def exactExtractedCallerFold (state : CallerState) (alpha : CallerRaw) :
    Result CallerState := do
  let folded ←
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.aeneas_extract_compact_fold
      (callerStateToExact state) (callerToExactRaw alpha)
  ok (exactStateToCaller folded)

/-- A successful corrected extraction exposes the exact generated root call
and its structural result. -/
theorem exactExtractedCallerFold_success_exposes_subcall
    (state output : CallerState) (alpha : CallerRaw)
    (run : exactExtractedCallerFold state alpha = .ok output) :
    ∃ folded : ExactState,
      V5RelationCompactFoldGeneratedExact.v5_cu_probe.aeneas_extract_compact_fold
          (callerStateToExact state) (callerToExactRaw alpha) = .ok folded ∧
      output = exactStateToCaller folded := by
  unfold exactExtractedCallerFold at run
  generalize subcall :
      V5RelationCompactFoldGeneratedExact.v5_cu_probe.aeneas_extract_compact_fold
        (callerStateToExact state) (callerToExactRaw alpha) = result at run
  cases result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok folded =>
    simp only [bind_tc_ok, Result.ok.injEq] at run
    exact ⟨folded, rfl, run.symm⟩

theorem exactToCallerRaw_callerToExactRaw (value : CallerRaw) :
    exactToCallerRaw (callerToExactRaw value) = value := by
  cases value <;> rfl

@[simp] theorem exactBlockToCaller_callerBlockToExact (block : CallerBlock) :
    exactBlockToCaller (callerBlockToExact block) = block := by
  cases block <;> simp [exactBlockToCaller, callerBlockToExact,
    exactToCallerRaw_callerToExactRaw]

theorem exactStateToCaller_callerStateToExact (state : CallerState) :
    exactStateToCaller (callerStateToExact state) = state := by
  cases state with
  | mk blocks deltaScale folds =>
    cases blocks with
    | mk values lengthExact =>
      simp only [exactStateToCaller, callerStateToExact]
      congr 1
      · apply Subtype.ext
        simp [List.map_map, Function.comp_def]

#print axioms exactExtractedCallerFold_success_exposes_subcall
#print axioms exactToCallerRaw_callerToExactRaw
#print axioms exactBlockToCaller_callerBlockToExact
#print axioms exactStateToCaller_callerStateToExact

end AspisV5CompactFoldExactCallerBridge
