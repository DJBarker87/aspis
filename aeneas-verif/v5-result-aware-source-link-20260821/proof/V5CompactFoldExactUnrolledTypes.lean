import V5CompactFoldExactCallerBridge
import V5CompactFoldExactSourceModel
import V5CompactFoldSourceModel

namespace AspisV5CompactFoldExactUnrolledTypes

open Aeneas Aeneas.Std Result
open AspisV5CompactFoldExactCallerBridge

abbrev LegacyRaw := V5RelationCompactFoldGenerated.aspis_core.field.QM31
abbrev ExactCM := V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31
abbrev LegacyCM := V5RelationCompactFoldGenerated.aspis_core.field.CM31
abbrev ExactPrepared :=
  V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier
abbrev LegacyPrepared :=
  V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev LegacyBlock :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev LegacyState :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights

def exactToLegacyCM (value : ExactCM) : LegacyCM :=
  { a := value.a, b := value.b }

def exactToLegacyRaw (value : ExactRaw) : LegacyRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def exactToLegacyBlock (block : ExactBlock) : LegacyBlock :=
  { scale := exactToLegacyRaw block.scale
    power_lo := exactToLegacyRaw block.power_lo
    power_hi := exactToLegacyRaw block.power_hi
    selector := block.selector }

@[simp] theorem exactToLegacyBlock_scale (block : ExactBlock) :
    (exactToLegacyBlock block).scale = exactToLegacyRaw block.scale := rfl

@[simp] theorem exactToLegacyBlock_power_lo (block : ExactBlock) :
    (exactToLegacyBlock block).power_lo = exactToLegacyRaw block.power_lo := rfl

@[simp] theorem exactToLegacyBlock_power_hi (block : ExactBlock) :
    (exactToLegacyBlock block).power_hi = exactToLegacyRaw block.power_hi := rfl

@[simp] theorem exactToLegacyBlock_selector (block : ExactBlock) :
    (exactToLegacyBlock block).selector = block.selector := rfl

def exactBlockArrayToLegacy {count : Std.Usize}
    (values : Array ExactBlock count) : Array LegacyBlock count :=
  ⟨values.val.map exactToLegacyBlock, by simpa using values.property⟩

def exactToLegacyState (state : ExactState) : LegacyState :=
  { blocks := exactBlockArrayToLegacy state.blocks
    delta_scale := exactToLegacyRaw state.delta_scale
    folds := state.folds }

@[simp] theorem exactToLegacyState_blocks (state : ExactState) :
    (exactToLegacyState state).blocks = exactBlockArrayToLegacy state.blocks := rfl

@[simp] theorem exactToLegacyState_delta_scale (state : ExactState) :
    (exactToLegacyState state).delta_scale =
      exactToLegacyRaw state.delta_scale := rfl

@[simp] theorem exactToLegacyState_folds (state : ExactState) :
    (exactToLegacyState state).folds = state.folds := rfl

def exactToLegacyPrepared (value : ExactPrepared) : LegacyPrepared :=
  { components := value.components }

def exactPreparedArrayToLegacy {count : Std.Usize}
    (values : Array ExactPrepared count) : Array LegacyPrepared count :=
  ⟨values.val.map exactToLegacyPrepared, by simpa using values.property⟩

def exactRawArrayToLegacy {count : Std.Usize}
    (values : Array ExactRaw count) : Array LegacyRaw count :=
  ⟨values.val.map exactToLegacyRaw, by simpa using values.property⟩

def callerToLegacyRaw (value : CallerRaw) : LegacyRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def legacyToCallerRaw (value : LegacyRaw) : CallerRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerBlockToLegacy (block : CallerBlock) : LegacyBlock :=
  { scale := callerToLegacyRaw block.scale
    power_lo := callerToLegacyRaw block.power_lo
    power_hi := callerToLegacyRaw block.power_hi
    selector := block.selector }

def legacyBlockToCaller (block : LegacyBlock) : CallerBlock :=
  { scale := legacyToCallerRaw block.scale
    power_lo := legacyToCallerRaw block.power_lo
    power_hi := legacyToCallerRaw block.power_hi
    selector := block.selector }

def callerStateToLegacy (state : CallerState) : LegacyState :=
  { blocks := ⟨state.blocks.val.map callerBlockToLegacy,
      by simpa using state.blocks.property⟩
    delta_scale := callerToLegacyRaw state.delta_scale
    folds := state.folds }

def legacyStateToCaller (state : LegacyState) : CallerState :=
  { blocks := ⟨state.blocks.val.map legacyBlockToCaller,
      by simpa using state.blocks.property⟩
    delta_scale := legacyToCallerRaw state.delta_scale
    folds := state.folds }

def exactUnrolledCallerFold (state : CallerState) (alpha : CallerRaw) :
    Result CallerState := do
  let folded ← AspisV5CompactFoldExactSource.unrolledFold
    (callerStateToExact state) (callerToExactRaw alpha)
  ok (exactStateToCaller folded)

def legacyUnrolledCallerFold (state : CallerState) (alpha : CallerRaw) :
    Result CallerState := do
  let folded ← V5CompactFoldSource.unrolledFold
    (callerStateToLegacy state) (callerToLegacyRaw alpha)
  ok (legacyStateToCaller folded)

end AspisV5CompactFoldExactUnrolledTypes
