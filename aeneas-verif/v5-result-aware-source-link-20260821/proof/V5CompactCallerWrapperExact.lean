import V5CompactNewFieldSemantics
import V5RelationCompactFoldFieldProjection
import V5CompactFinalFieldSemantics
import V5RelationCompactAdditiveDotExact
import V5AcceptedRelationRoundInversion
import V5CompactNewSourceUnroll
import V5CompactFinalReleasedBridge
import V5CompactFoldCorrectedWrapper
import V5CompactFoldProgramSemantics

/-!
# Exact structural semantics of the compact caller wrappers

The focused caller extraction delegates compact construction, folding, and
final-weight production to three separately extracted source units.  Those
calls use fresh Lean record types, so the caller contains structural
conversions at each boundary.  This file makes those conversions public,
proves that they preserve the maintained field projection and state metadata,
and recovers the exact delegated calls made by one accepted execution.
-/

namespace AspisV5CompactCallerWrapperExact

open Aeneas Aeneas.Std Result
open AspisV5RelationAcceptanceSourceProof
open AspisV5AcceptedRelationRoundInversion

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev CallerRaw := V5RelationCallerGenerated.aspis_core.field.QM31
abbrev CallerBlock :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev CallerState :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights

abbrev NewRaw := V5RelationCompactNewGenerated.aspis_core.field.QM31
abbrev NewBlock :=
  V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev NewState :=
  V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights

abbrev FoldRaw := V5RelationCompactFoldGenerated.aspis_core.field.QM31
abbrev FoldBlock :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev FoldState :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights

abbrev FinalRaw := V5RelationCompactFinalGenerated.aspis_core.field.QM31
abbrev FinalBlock :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev FinalState :=
  V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights

deriving instance Inhabited for
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalBlock
local instance : Inhabited FoldBlock :=
  ⟨{ scale := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
     power_lo := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
     power_hi := V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
     selector := 0#u8 }⟩
local instance : Inhabited FinalBlock :=
  AspisV5CompactFinalFieldSemantics.instInhabitedBlock
local instance : Inhabited NewRaw :=
  V5CompactScratchNew.instInhabitedRaw

def callerToK (value : CallerRaw) : K :=
  AspisV5RelationGeneratedFieldProjection.toMaintainedExact value

def CallerCanonical (value : CallerRaw) : Prop :=
  AspisV5RelationGeneratedFieldProjection.CanonicalQM31 value

def callerBlockAt (state : CallerState) (index : Fin 10) : CallerBlock :=
  state.blocks.val[index.val]!

def callerPointAt (point : Array CallerRaw 10#usize)
    (index : Fin 10) : CallerRaw :=
  point.val[index.val]!

def callerProjectBlock (block : CallerBlock) :
    AspisV5CompactTerminalOptimized.OptimizedBlock K :=
  { scale := callerToK block.scale
    powerLo := callerToK block.power_lo
    powerHi := callerToK block.power_hi
    selector := block.selector.val }

def callerProjectState (state : CallerState) :
    AspisV5CompactTerminalOptimized.OptimizedState K :=
  { blocks := fun index => callerProjectBlock (callerBlockAt state index)
    deltaScale := callerToK state.delta_scale }

def CallerCanonicalBlock (block : CallerBlock) : Prop :=
  CallerCanonical block.scale ∧ CallerCanonical block.power_lo ∧
    CallerCanonical block.power_hi

def CallerCanonicalState (state : CallerState) : Prop :=
  (∀ index : Fin 10, CallerCanonicalBlock (callerBlockAt state index)) ∧
    CallerCanonical state.delta_scale

def CallerCanonicalScales (state : CallerState) : Prop :=
  (∀ index : Fin 10, CallerCanonical (callerBlockAt state index).scale) ∧
    CallerCanonical state.delta_scale

def CallerReleasedSelectors (state : CallerState) : Prop :=
  ∀ index : Fin 10,
    (callerBlockAt state index).selector.val =
      AspisV5CompactTerminal.blockSelector index

def foldToK (value : FoldRaw) : K :=
  AspisV5RelationCompactFoldFieldProjection.toMaintainedExact value

@[simp] theorem sourceFoldToK_eq_foldToK (value : FoldRaw) :
    AspisV5CompactFoldStateSemantics.toK value = foldToK value := by
  rfl

def FoldCanonical (value : FoldRaw) : Prop :=
  AspisV5RelationCompactFoldFieldProjection.CanonicalQM31 value

def foldBlockAt (state : FoldState) (index : Fin 10) : FoldBlock :=
  state.blocks.val[index.val]!

def foldProjectBlock (block : FoldBlock) :
    AspisV5CompactTerminalOptimized.OptimizedBlock K :=
  { scale := foldToK block.scale
    powerLo := foldToK block.power_lo
    powerHi := foldToK block.power_hi
    selector := block.selector.val }

def foldProjectState (state : FoldState) :
    AspisV5CompactTerminalOptimized.OptimizedState K :=
  { blocks := fun index => foldProjectBlock (foldBlockAt state index)
    deltaScale := foldToK state.delta_scale }

@[simp] theorem sourceFoldProjectState_eq_foldProjectState
    (state : FoldState) :
    AspisV5CompactFoldStateSemantics.projectState state =
      foldProjectState state := by
  rfl

def FoldCanonicalBlock (block : FoldBlock) : Prop :=
  FoldCanonical block.scale ∧ FoldCanonical block.power_lo ∧
    FoldCanonical block.power_hi

def FoldCanonicalState (state : FoldState) : Prop :=
  (∀ index : Fin 10, FoldCanonicalBlock (foldBlockAt state index)) ∧
    FoldCanonical state.delta_scale

def callerToNewRaw (value : CallerRaw) : NewRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def newToCallerRaw (value : NewRaw) : CallerRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerArrayToNew {count : Std.Usize}
    (values : Array CallerRaw count) : Array NewRaw count :=
  ⟨values.val.map callerToNewRaw, by simpa using values.property⟩

def callerBlockToNew (block : CallerBlock) : NewBlock :=
  { scale := callerToNewRaw block.scale
    power_lo := callerToNewRaw block.power_lo
    power_hi := callerToNewRaw block.power_hi
    selector := block.selector }

def newBlockToCaller (block : NewBlock) : CallerBlock :=
  { scale := newToCallerRaw block.scale
    power_lo := newToCallerRaw block.power_lo
    power_hi := newToCallerRaw block.power_hi
    selector := block.selector }

def callerStateToNew (state : CallerState) : NewState :=
  { blocks := ⟨state.blocks.val.map callerBlockToNew,
      by simpa using state.blocks.property⟩
    delta_scale := callerToNewRaw state.delta_scale
    folds := state.folds }

def newStateToCaller (state : NewState) : CallerState :=
  { blocks := ⟨state.blocks.val.map newBlockToCaller,
      by simpa using state.blocks.property⟩
    delta_scale := newToCallerRaw state.delta_scale
    folds := state.folds }

def callerToFoldRaw (value : CallerRaw) : FoldRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def foldToCallerRaw (value : FoldRaw) : CallerRaw :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerBlockToFold (block : CallerBlock) : FoldBlock :=
  { scale := callerToFoldRaw block.scale
    power_lo := callerToFoldRaw block.power_lo
    power_hi := callerToFoldRaw block.power_hi
    selector := block.selector }

def foldBlockToCaller (block : FoldBlock) : CallerBlock :=
  { scale := foldToCallerRaw block.scale
    power_lo := foldToCallerRaw block.power_lo
    power_hi := foldToCallerRaw block.power_hi
    selector := block.selector }

def callerStateToFold (state : CallerState) : FoldState :=
  { blocks := ⟨state.blocks.val.map callerBlockToFold,
      by simpa using state.blocks.property⟩
    delta_scale := callerToFoldRaw state.delta_scale
    folds := state.folds }

def foldStateToCaller (state : FoldState) : CallerState :=
  { blocks := ⟨state.blocks.val.map foldBlockToCaller,
      by simpa using state.blocks.property⟩
    delta_scale := foldToCallerRaw state.delta_scale
    folds := state.folds }

def callerToFinalRaw (value : CallerRaw) : FinalRaw :=
  AspisV5RelationCompactAdditiveDotExact.rawToFinal value

def finalToCallerRaw (value : FinalRaw) : CallerRaw :=
  AspisV5RelationCompactAdditiveDotExact.finalToRaw value

def callerBlockToFinal (block : CallerBlock) : FinalBlock :=
  { scale := callerToFinalRaw block.scale
    power_lo := callerToFinalRaw block.power_lo
    power_hi := callerToFinalRaw block.power_hi
    selector := block.selector }

def callerStateToFinal (state : CallerState) : FinalState :=
  { blocks := ⟨state.blocks.val.map callerBlockToFinal,
      by simpa using state.blocks.property⟩
    delta_scale := callerToFinalRaw state.delta_scale
    folds := state.folds }

/-- The extracted constructor is definitionally the explicit constructor
program used by the field-semantics proof, after the separately checked loop
unrolling theorem. -/
theorem generatedNew_eq_constructorProgram
    (point : Array NewRaw 10#usize) (scale : NewRaw) :
    V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights.new
        point scale = V5CompactScratchNew.constructorProgram point scale := by
  rw [AspisV5CompactNewSourceUnroll.new_eq_unrolled]
  rfl

/-- Under the released ten-entry selector schedule, the extracted final
scatter is exactly the explicit final program used by the field-semantics
proof. -/
theorem generatedFinalWeights_eq_finalProgram
    (state : FinalState)
    (selectors : AspisV5CompactFinalFieldSemantics.ReleasedSelectors state) :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        state = AspisV5CompactFinalFieldSemantics.finalProgram state := by
  exact
    AspisV5CompactFinalReleasedBridge.generated_final_weights_eq_released_program
      state selectors

@[simp] theorem callerArrayToNew_pointAt
    (point : Array CallerRaw 10#usize) (index : Fin 10) :
    V5CompactScratchNew.pointAt (callerArrayToNew point) index =
      callerToNewRaw (callerPointAt point index) := by
  have sourceBound : index.val < point.val.length := by
    simpa [Array.length_eq] using index.isLt
  unfold V5CompactScratchNew.pointAt callerArrayToNew callerPointAt
  rw [List.getElem!_map_eq _ _ _ sourceBound]

private theorem fixedArray_getBang_eq_get
    {T : Type} [Inhabited T] {count : Std.Usize}
    (values : Array T count) (index : Fin count.val) :
    values.val[index.val]! = values.val[index.val] := by
  have lengthExact : values.val.length = count.val := Array.length_eq values
  have inBounds : index.val < values.val.length := by
    simpa only [lengthExact] using index.isLt
  apply List.getElem!_of_getElem?
  simp [inBounds]

/-- In bounds, `getElem!` cannot observe which default-value instance was
chosen.  This lets separately generated Aeneas modules share fixed-array
facts even though each module declares its own local `Inhabited` instance. -/
private theorem list_getBang_instance_independent
    {T : Type} (first second : Inhabited T)
    (values : List T) (index : Nat) (bound : index < values.length) :
    @getElem! (List T) Nat T (fun items position => position < items.length)
        List.instGetElem?NatLtLength first values index =
      @getElem! (List T) Nat T (fun items position => position < items.length)
        List.instGetElem?NatLtLength second values index := by
  have left :
      @getElem! (List T) Nat T
          (fun items position => position < items.length)
          List.instGetElem?NatLtLength first values index =
        values[index]'bound := by
    letI : Inhabited T := first
    exact getElem!_pos values index bound
  have right :
      @getElem! (List T) Nat T
          (fun items position => position < items.length)
          List.instGetElem?NatLtLength second values index =
        values[index]'bound := by
    letI : Inhabited T := second
    exact getElem!_pos values index bound
  exact left.trans right.symm

@[simp] theorem callerStateToNew_blockAt (state : CallerState)
    (index : Fin 10) :
    V5CompactScratchNew.blockAt (callerStateToNew state) index =
      callerBlockToNew (callerBlockAt state index) := by
  unfold V5CompactScratchNew.blockAt callerStateToNew callerBlockAt
  rw [List.getElem_map]
  rw [fixedArray_getBang_eq_get state.blocks index]

@[simp] theorem newStateToCaller_blockAt (state : NewState)
    (index : Fin 10) :
    callerBlockAt (newStateToCaller state) index =
      newBlockToCaller (V5CompactScratchNew.blockAt state index) := by
  unfold callerBlockAt
  rw [fixedArray_getBang_eq_get (newStateToCaller state).blocks index]
  unfold newStateToCaller V5CompactScratchNew.blockAt
  rw [List.getElem_map]

@[simp] theorem callerStateToFold_blockAt (state : CallerState)
    (index : Fin 10) :
    foldBlockAt (callerStateToFold state) index =
      callerBlockToFold (callerBlockAt state index) := by
  have sourceBound : index.val < state.blocks.val.length := by
    simpa [Array.length_eq] using index.isLt
  unfold foldBlockAt callerStateToFold callerBlockAt
  rw [List.getElem!_map_eq _ _ _ sourceBound]

@[simp] theorem foldStateToCaller_blockAt (state : FoldState)
    (index : Fin 10) :
    callerBlockAt (foldStateToCaller state) index =
      foldBlockToCaller (foldBlockAt state index) := by
  have sourceBound : index.val < state.blocks.val.length := by
    simpa [Array.length_eq] using index.isLt
  unfold callerBlockAt foldStateToCaller foldBlockAt
  rw [List.getElem!_map_eq _ _ _ sourceBound]

@[simp] theorem callerStateToFinal_blockAt (state : CallerState)
    (index : Fin 10) :
    AspisV5CompactFinalFieldSemantics.blockAt (callerStateToFinal state) index =
      callerBlockToFinal (callerBlockAt state index) := by
  have sourceBound : index.val < state.blocks.val.length := by
    simpa [Array.length_eq] using index.isLt
  unfold AspisV5CompactFinalFieldSemantics.blockAt callerStateToFinal
    callerBlockAt
  rw [List.getElem!_map_eq _ _ _ sourceBound]

@[simp] theorem new_roundtrip_left (value : CallerRaw) :
    newToCallerRaw (callerToNewRaw value) = value := by cases value <;> rfl

@[simp] theorem new_roundtrip_right (value : NewRaw) :
    callerToNewRaw (newToCallerRaw value) = value := by cases value <;> rfl

@[simp] theorem fold_roundtrip_left (value : CallerRaw) :
    foldToCallerRaw (callerToFoldRaw value) = value := by cases value <;> rfl

@[simp] theorem fold_roundtrip_right (value : FoldRaw) :
    callerToFoldRaw (foldToCallerRaw value) = value := by cases value <;> rfl

@[simp] theorem final_roundtrip_left (value : CallerRaw) :
    finalToCallerRaw (callerToFinalRaw value) = value := by cases value <;> rfl

@[simp] theorem final_roundtrip_right (value : FinalRaw) :
    callerToFinalRaw (finalToCallerRaw value) = value := by cases value <;> rfl

@[simp] theorem callerToNew_exact (value : CallerRaw) :
    V5CompactScratchNew.toExact (callerToNewRaw value) = callerToK value := by
  rfl

@[simp] theorem newToCaller_exact (value : NewRaw) :
    callerToK (newToCallerRaw value) = V5CompactScratchNew.toExact value := by
  rfl

@[simp] theorem callerToFold_exact (value : CallerRaw) :
    foldToK (callerToFoldRaw value) = callerToK value := by
  rfl

@[simp] theorem foldToCaller_exact (value : FoldRaw) :
    callerToK (foldToCallerRaw value) = foldToK value := by
  rfl

@[simp] theorem callerToFinal_exact (value : CallerRaw) :
    AspisV5CompactFinalFieldSemantics.toExact (callerToFinalRaw value) =
      callerToK value := by
  rfl

@[simp] theorem finalToCaller_exact (value : FinalRaw) :
    callerToK (finalToCallerRaw value) =
      AspisV5CompactFinalFieldSemantics.toExact value := by
  rfl

@[simp] theorem callerToNew_canonical (value : CallerRaw) :
    V5CompactScratchNew.Canonical (callerToNewRaw value) ↔
      CallerCanonical value := by
  rfl

@[simp] theorem newToCaller_canonical (value : NewRaw) :
    CallerCanonical (newToCallerRaw value) ↔
      V5CompactScratchNew.Canonical value := by
  rfl

@[simp] theorem callerToFold_canonical (value : CallerRaw) :
    FoldCanonical (callerToFoldRaw value) ↔ CallerCanonical value := by
  rfl

@[simp] theorem foldToCaller_canonical (value : FoldRaw) :
    CallerCanonical (foldToCallerRaw value) ↔ FoldCanonical value := by
  rfl

@[simp] theorem callerToFinal_canonical (value : CallerRaw) :
    AspisV5CompactFinalFieldSemantics.Canonical (callerToFinalRaw value) ↔
      CallerCanonical value := by
  rfl

@[simp] theorem finalToCaller_canonical (value : FinalRaw) :
    CallerCanonical (finalToCallerRaw value) ↔
      AspisV5CompactFinalFieldSemantics.Canonical value := by
  rfl

@[simp] theorem callerBlockToNew_project (block : CallerBlock) :
    V5CompactScratchNew.projectBlock (callerBlockToNew block) =
      callerProjectBlock block := by
  rfl

@[simp] theorem callerBlockToNew_selector (block : CallerBlock) :
    (callerBlockToNew block).selector = block.selector := by
  rfl

@[simp] theorem newBlockToCaller_selector (block : NewBlock) :
    (newBlockToCaller block).selector = block.selector := by
  rfl

@[simp] theorem newBlockToCaller_project (block : NewBlock) :
    callerProjectBlock (newBlockToCaller block) =
      V5CompactScratchNew.projectBlock block := by
  rfl

@[simp] theorem callerBlockToFold_project (block : CallerBlock) :
    foldProjectBlock (callerBlockToFold block) = callerProjectBlock block := by
  rfl

@[simp] theorem callerBlockToFold_selector (block : CallerBlock) :
    (callerBlockToFold block).selector = block.selector := by
  rfl

@[simp] theorem foldBlockToCaller_selector (block : FoldBlock) :
    (foldBlockToCaller block).selector = block.selector := by
  rfl

@[simp] theorem foldBlockToCaller_project (block : FoldBlock) :
    callerProjectBlock (foldBlockToCaller block) = foldProjectBlock block := by
  rfl

@[simp] theorem callerBlockToFinal_project (block : CallerBlock) :
    AspisV5CompactFinalFieldSemantics.projectBlock (callerBlockToFinal block) =
      callerProjectBlock block := by
  rfl

@[simp] theorem callerStateToNew_deltaScale (state : CallerState) :
    (callerStateToNew state).delta_scale =
      callerToNewRaw state.delta_scale := by
  rfl

@[simp] theorem newStateToCaller_deltaScale (state : NewState) :
    (newStateToCaller state).delta_scale =
      newToCallerRaw state.delta_scale := by
  rfl

@[simp] theorem callerStateToFold_deltaScale (state : CallerState) :
    (callerStateToFold state).delta_scale =
      callerToFoldRaw state.delta_scale := by
  rfl

@[simp] theorem foldStateToCaller_deltaScale (state : FoldState) :
    (foldStateToCaller state).delta_scale =
      foldToCallerRaw state.delta_scale := by
  rfl

@[simp] theorem callerStateToFinal_deltaScale (state : CallerState) :
    (callerStateToFinal state).delta_scale =
      callerToFinalRaw state.delta_scale := by
  rfl

@[simp] theorem callerBlockToFinal_scale (block : CallerBlock) :
    (callerBlockToFinal block).scale = callerToFinalRaw block.scale := by
  rfl

@[simp] theorem callerBlockToFinal_selector (block : CallerBlock) :
    (callerBlockToFinal block).selector = block.selector := by
  rfl

@[simp] theorem callerStateToNew_project (state : CallerState) :
    V5CompactScratchNew.projectState (callerStateToNew state) =
      callerProjectState state := by
  apply congrArg₂ (fun blocks deltaScale =>
    ({ blocks := blocks, deltaScale := deltaScale } :
      AspisV5CompactTerminalOptimized.OptimizedState K))
  · funext index
    simp [V5CompactScratchNew.projectState, callerProjectState]
  · rfl

@[simp] theorem newStateToCaller_project (state : NewState) :
    callerProjectState (newStateToCaller state) =
      V5CompactScratchNew.projectState state := by
  apply congrArg₂ (fun blocks deltaScale =>
    ({ blocks := blocks, deltaScale := deltaScale } :
      AspisV5CompactTerminalOptimized.OptimizedState K))
  · funext index
    simp [callerProjectState, V5CompactScratchNew.projectState]
  · rfl

@[simp] theorem callerStateToFold_project (state : CallerState) :
    foldProjectState (callerStateToFold state) = callerProjectState state := by
  apply congrArg₂ (fun blocks deltaScale =>
    ({ blocks := blocks, deltaScale := deltaScale } :
      AspisV5CompactTerminalOptimized.OptimizedState K))
  · funext index
    simp [foldProjectState, callerProjectState]
  · rfl

@[simp] theorem foldStateToCaller_project (state : FoldState) :
    callerProjectState (foldStateToCaller state) = foldProjectState state := by
  apply congrArg₂ (fun blocks deltaScale =>
    ({ blocks := blocks, deltaScale := deltaScale } :
      AspisV5CompactTerminalOptimized.OptimizedState K))
  · funext index
    simp [callerProjectState, foldProjectState]
  · rfl

@[simp] theorem callerStateToFinal_project (state : CallerState) :
    AspisV5CompactFinalFieldSemantics.projectState (callerStateToFinal state) =
      callerProjectState state := by
  apply congrArg₂ (fun blocks deltaScale =>
    ({ blocks := blocks, deltaScale := deltaScale } :
      AspisV5CompactTerminalOptimized.OptimizedState K))
  · funext index
    simp [AspisV5CompactFinalFieldSemantics.projectState, callerProjectState]
  · rfl

@[simp] theorem callerBlockToNew_canonical (block : CallerBlock) :
    V5CompactScratchNew.CanonicalBlock (callerBlockToNew block) ↔
      CallerCanonicalBlock block := by
  rfl

@[simp] theorem newBlockToCaller_canonical (block : NewBlock) :
    CallerCanonicalBlock (newBlockToCaller block) ↔
      V5CompactScratchNew.CanonicalBlock block := by
  rfl

@[simp] theorem callerBlockToFold_canonical (block : CallerBlock) :
    FoldCanonicalBlock (callerBlockToFold block) ↔
      CallerCanonicalBlock block := by
  rfl

@[simp] theorem foldBlockToCaller_canonical (block : FoldBlock) :
    CallerCanonicalBlock (foldBlockToCaller block) ↔
      FoldCanonicalBlock block := by
  rfl

@[simp] theorem callerStateToNew_canonical (state : CallerState) :
    V5CompactScratchNew.CanonicalState (callerStateToNew state) ↔
      CallerCanonicalState state := by
  simp [V5CompactScratchNew.CanonicalState, CallerCanonicalState]

@[simp] theorem newStateToCaller_canonical (state : NewState) :
    CallerCanonicalState (newStateToCaller state) ↔
      V5CompactScratchNew.CanonicalState state := by
  simp [CallerCanonicalState, V5CompactScratchNew.CanonicalState]

@[simp] theorem callerStateToFold_canonical (state : CallerState) :
    FoldCanonicalState (callerStateToFold state) ↔
      CallerCanonicalState state := by
  simp [FoldCanonicalState, CallerCanonicalState]

@[simp] theorem foldStateToCaller_canonical (state : FoldState) :
    CallerCanonicalState (foldStateToCaller state) ↔
      FoldCanonicalState state := by
  simp [CallerCanonicalState, FoldCanonicalState]

@[simp] theorem callerStateToFinal_canonicalScales (state : CallerState) :
    AspisV5CompactFinalFieldSemantics.CanonicalScales
        (callerStateToFinal state) ↔
      CallerCanonicalScales state := by
  simp [AspisV5CompactFinalFieldSemantics.CanonicalScales,
    CallerCanonicalScales]

@[simp] theorem callerStateToFinal_releasedSelectors (state : CallerState) :
    AspisV5CompactFinalFieldSemantics.ReleasedSelectors
        (callerStateToFinal state) ↔
      CallerReleasedSelectors state := by
  simp [AspisV5CompactFinalFieldSemantics.ReleasedSelectors,
    CallerReleasedSelectors]

@[simp] theorem callerStateToFold_releasedSelectors (state : CallerState) :
    AspisV5CompactFoldProgramSemantics.ReleasedSelectors
        (callerStateToFold state) ↔
      CallerReleasedSelectors state := by
  unfold AspisV5CompactFoldProgramSemantics.ReleasedSelectors
    CallerReleasedSelectors
  constructor
  · intro selectors index
    have selected := selectors index
    change (foldBlockAt (callerStateToFold state) index).selector.val =
      AspisV5CompactTerminal.blockSelector index at selected
    simpa only [callerStateToFold_blockAt, callerBlockToFold_selector]
      using selected
  · intro selectors index
    change (foldBlockAt (callerStateToFold state) index).selector.val =
      AspisV5CompactTerminal.blockSelector index
    simpa only [callerStateToFold_blockAt, callerBlockToFold_selector]
      using selectors index

@[simp] theorem foldStateToCaller_releasedSelectors (state : FoldState) :
    CallerReleasedSelectors (foldStateToCaller state) ↔
      AspisV5CompactFoldProgramSemantics.ReleasedSelectors state := by
  unfold AspisV5CompactFoldProgramSemantics.ReleasedSelectors
    CallerReleasedSelectors
  constructor
  · intro selectors index
    have selected := selectors index
    change (callerBlockAt (foldStateToCaller state) index).selector.val =
      AspisV5CompactTerminal.blockSelector index at selected
    have mapped : (foldBlockAt state index).selector.val =
        AspisV5CompactTerminal.blockSelector index := by
      simpa only [foldStateToCaller_blockAt, foldBlockToCaller_selector]
        using selected
    change (state.blocks.val[index.val]!).selector.val =
      AspisV5CompactTerminal.blockSelector index
    convert mapped using 1
    · apply congrArg (fun block : FoldBlock => block.selector.val)
      exact list_getBang_instance_independent _ _ state.blocks.val index.val
          (by simpa [Array.length_eq] using index.isLt)
  · intro selectors index
    have selected := selectors index
    have mapped : (foldBlockAt state index).selector.val =
        AspisV5CompactTerminal.blockSelector index := by
      change (state.blocks.val[index.val]!).selector.val =
        AspisV5CompactTerminal.blockSelector index at selected
      convert selected using 1
      · apply congrArg (fun block : FoldBlock => block.selector.val)
        exact list_getBang_instance_independent _ _ state.blocks.val index.val
            (by simpa [Array.length_eq] using index.isLt)
    change (callerBlockAt (foldStateToCaller state) index).selector.val =
      AspisV5CompactTerminal.blockSelector index
    simpa only [foldStateToCaller_blockAt, foldBlockToCaller_selector]
      using mapped

theorem callerCanonicalState_implies_canonicalScales
    (state : CallerState) (canonical : CallerCanonicalState state) :
    CallerCanonicalScales state := by
  exact ⟨fun index => (canonical.1 index).1, canonical.2⟩

/-- Equality with the released optimized run fixes every caller selector to
the released ten-entry selector schedule. -/
theorem callerReleasedSelectors_of_project_eq_optimizedRun
    (state : CallerState) (point : Fin 10 → K) (scale : K)
    (alphas : Fin 4 → K)
    (exact : callerProjectState state =
      AspisV5CompactTerminalOptimized.optimizedRun point scale alphas) :
    CallerReleasedSelectors state := by
  intro index
  have selectorExact := congrArg
    (fun projected => (projected.blocks index).selector) exact
  simpa [callerProjectState, callerProjectBlock,
    AspisV5CompactTerminalOptimized.optimizedRun,
    AspisV5CompactTerminalOptimized.optimizedFoldZero,
    AspisV5CompactTerminalOptimized.optimizedFoldOne,
    AspisV5CompactTerminalOptimized.optimizedFoldTwo,
    AspisV5CompactTerminalOptimized.optimizedFoldThree,
    AspisV5CompactTerminalOptimized.optimizedInit] using selectorExact

@[simp] theorem callerStateToNew_folds (state : CallerState) :
    (callerStateToNew state).folds = state.folds := by rfl

@[simp] theorem newStateToCaller_folds (state : NewState) :
    (newStateToCaller state).folds = state.folds := by rfl

@[simp] theorem callerStateToFold_folds (state : CallerState) :
    (callerStateToFold state).folds = state.folds := by rfl

@[simp] theorem foldStateToCaller_folds (state : FoldState) :
    (foldStateToCaller state).folds = state.folds := by rfl

@[simp] theorem callerStateToFinal_folds (state : CallerState) :
    (callerStateToFinal state).folds = state.folds := by rfl

/-- A successful caller constructor wrapper exposes its exact generated
constructor call and the structural state returned to the caller. -/
theorem caller_new_success_exposes_subcall
    (point : Array CallerRaw 10#usize) (scale : CallerRaw)
    (output : CallerState)
    (run : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.new
      point scale = .ok output) :
    ∃ state : NewState,
      V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights.new
          (callerArrayToNew point) (callerToNewRaw scale) = .ok state ∧
      output = newStateToCaller state := by
  unfold V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.new at run
  change
    (do
      let state ←
        V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights.new
          (callerArrayToNew point) (callerToNewRaw scale)
      ok (newStateToCaller state)) = .ok output at run
  generalize subcall :
      V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights.new
        (callerArrayToNew point) (callerToNewRaw scale) = result at run
  cases result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok state =>
    simp only [bind_tc_ok, Result.ok.injEq] at run
    exact ⟨state, rfl, run.symm⟩

/-- The caller's extracted constructor has the exact maintained initializer
semantics for every canonical ten-coordinate input and scale. -/
theorem caller_new_success_exact
    (point : Array CallerRaw 10#usize) (scale : CallerRaw)
    (output : CallerState)
    (pointCanonical : ∀ index : Fin 10,
      CallerCanonical (callerPointAt point index))
    (scaleCanonical : CallerCanonical scale)
    (run : V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.new
      point scale = .ok output) :
    CallerCanonicalState output ∧ output.folds = 0#u8 ∧
      callerProjectState output =
        AspisV5CompactTerminalOptimized.optimizedInit
          (fun index => callerToK (callerPointAt point index))
          (callerToK scale) := by
  obtain ⟨state, newRun, outputEq⟩ :=
    caller_new_success_exposes_subcall point scale output run
  have programRun := newRun
  rw [generatedNew_eq_constructorProgram] at programRun
  have newPointCanonical : ∀ index : Fin 10,
      V5CompactScratchNew.Canonical
        (V5CompactScratchNew.pointAt (callerArrayToNew point) index) := by
    intro index
    simpa using pointCanonical index
  have newScaleCanonical :
      V5CompactScratchNew.Canonical (callerToNewRaw scale) := by
    simpa using scaleCanonical
  have semantic := V5CompactScratchNew.constructorProgram_corresponds
    (callerArrayToNew point) (callerToNewRaw scale) state
    newPointCanonical newScaleCanonical programRun
  subst output
  refine ⟨(newStateToCaller_canonical state).2 semantic.1,
    by simpa using semantic.2.1, ?_⟩
  rw [newStateToCaller_project, semantic.2.2]
  congr 1
  funext index
  simp

/-- The caller-shaped form of the corrected compact fold.  The pinned caller
now uses this source-shaped iterator write-back after the documented
24 August 2026 integration correction. -/
def correctedCallerFold (state : CallerState) (alpha : CallerRaw) :
    Result CallerState := do
  let folded ← V5CompactFoldCorrectedWrapper.fold
    (callerStateToFold state) (callerToFoldRaw alpha)
  ok (foldStateToCaller folded)

/-- A successful corrected caller fold exposes the corrected source-shaped
subcall and the structural state returned to the caller. -/
theorem correctedCallerFold_success_exposes_subcall
    (state output : CallerState) (alpha : CallerRaw)
    (run : correctedCallerFold state alpha = .ok output) :
    ∃ folded : FoldState,
      V5CompactFoldCorrectedWrapper.fold
          (callerStateToFold state) (callerToFoldRaw alpha) = .ok folded ∧
      output = foldStateToCaller folded := by
  unfold correctedCallerFold at run
  change
    (do
      let folded ←
        V5CompactFoldCorrectedWrapper.fold
          (callerStateToFold state) (callerToFoldRaw alpha)
      ok (foldStateToCaller folded)) = .ok output at run
  generalize subcall :
      V5CompactFoldCorrectedWrapper.fold
        (callerStateToFold state) (callerToFoldRaw alpha) = result at run
  cases result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok folded =>
    simp only [bind_tc_ok, Result.ok.injEq] at run
    exact ⟨folded, rfl, run.symm⟩

/-- A successful call through the pinned generated caller exposes the exact
generated fold subcall and its structural result.  The generated fold includes
the documented source-shaped iterator write-back correction. -/
theorem caller_fold_success_exposes_subcall
    (state output : CallerState) (alpha : CallerRaw)
    (run :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.fold
        state alpha = .ok output) :
    ∃ folded : FoldState,
      V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
          (callerStateToFold state) (callerToFoldRaw alpha) = .ok folded ∧
      output = foldStateToCaller folded := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.fold
    at run
  change
    (do
      let folded ←
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
          (callerStateToFold state) (callerToFoldRaw alpha)
      ok (foldStateToCaller folded)) = .ok output at run
  generalize subcall :
      V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
        (callerStateToFold state) (callerToFoldRaw alpha) = result at run
  cases result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok folded =>
    simp only [bind_tc_ok, Result.ok.injEq] at run
    exact ⟨folded, rfl, run.symm⟩

/-- A successful caller fold has the exact maintained-field meaning of the
corresponding released fold counter.  The four counter-specific source
equalities are discharged inside `corrected_fold_corresponds`; no universal
256-way byte-counter reduction is needed. -/
theorem caller_fold_success_exact
    (state output : CallerState) (alpha : CallerRaw)
    (stateCanonical : CallerCanonicalState state)
    (selectors : CallerReleasedSelectors state)
    (alphaCanonical : CallerCanonical alpha)
    (foldBound : state.folds.val < 4)
    (run : correctedCallerFold state alpha = .ok output) :
    CallerCanonicalState output ∧ CallerReleasedSelectors output ∧
      output.folds.val = state.folds.val + 1 ∧
      callerProjectState output =
        AspisV5CompactFoldProgramSemantics.optimizedFoldFor state.folds.val
          (callerToK alpha) (callerProjectState state) := by
  obtain ⟨folded, foldedRun, outputEq⟩ :=
    correctedCallerFold_success_exposes_subcall state output alpha run
  have semantic :=
    AspisV5CompactFoldProgramSemantics.corrected_fold_corresponds
      (callerStateToFold state) (callerToFoldRaw alpha) folded
      ((callerStateToFold_canonical state).2 stateCanonical)
      ((callerStateToFold_releasedSelectors state).2 selectors)
      ((callerToFold_canonical alpha).2 alphaCanonical)
      (by simpa using foldBound) foldedRun
  subst output
  refine ⟨(foldStateToCaller_canonical folded).2 semantic.1,
    (foldStateToCaller_releasedSelectors folded).2 semantic.2.1, ?_, ?_⟩
  · simpa using semantic.2.2.1
  · rw [foldStateToCaller_project,
      ← sourceFoldProjectState_eq_foldProjectState,
      semantic.2.2.2, sourceFoldProjectState_eq_foldProjectState,
      callerStateToFold_project, sourceFoldToK_eq_foldToK,
      callerToFold_exact, callerStateToFold_folds]

/-- A successful caller dot wrapper exposes the exact final-weight subcall
and the exact fixed dot program.  Arithmetic semantics are supplied by
`V5RelationCompactAdditiveDotExact`. -/
theorem caller_dot_success_exposes_subcalls
    (state : CallerState) (values : Array CallerRaw 4#usize)
    (output : CallerRaw)
    (run :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
        state values = .ok output) :
    ∃ weights : Array FinalRaw 4#usize,
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
          (callerStateToFinal state) = .ok weights ∧
      AspisV5RelationCompactAdditiveDotExact.fourTermDotProgram
          weights values = .ok output := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.dot
    at run
  change
    (do
      let weights ←
        V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
          (callerStateToFinal state)
      AspisV5RelationCompactAdditiveDotExact.fourTermDotProgram weights values) =
        .ok output at run
  generalize finalCall :
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        (callerStateToFinal state) = result at run
  cases result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok weights =>
    simp only [bind_tc_ok] at run
    exact ⟨weights, rfl, run⟩

/-- A successful final-weight call returns canonical weights whose exact
values are the maintained optimized scatter of the caller state. -/
theorem caller_final_weights_success_exact
    (state : CallerState) (weights : Array FinalRaw 4#usize)
    (canonical : CallerCanonicalScales state)
    (selectors : CallerReleasedSelectors state)
    (run :
      V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        (callerStateToFinal state) = .ok weights) :
    (∀ index : Fin 4,
      AspisV5CompactFinalFieldSemantics.Canonical weights.val[index.val]!) ∧
      (fun index : Fin 4 =>
        AspisV5CompactFinalFieldSemantics.toExact weights.val[index.val]!) =
        AspisV5CompactTerminalOptimized.optimizedFinalWeights
          (callerProjectState state) := by
  have mappedSelectors :=
    (callerStateToFinal_releasedSelectors state).2 selectors
  have programRun := run
  rw [generatedFinalWeights_eq_finalProgram _ mappedSelectors] at programRun
  have mappedCanonical :=
    (callerStateToFinal_canonicalScales state).2 canonical
  have semantic := AspisV5CompactFinalFieldSemantics.finalProgram_corresponds
    (callerStateToFinal state) weights mappedCanonical programRun
  have scatter :=
    AspisV5CompactFinalFieldSemantics.optimizedFinalWeights_eq_exactOutput
      (callerStateToFinal state) mappedSelectors
  have semanticCanonical : ∀ index : Fin 4,
      AspisV5CompactFinalFieldSemantics.Canonical
        weights.val[index.val]! := by
    intro index
    convert semantic.1 index using 1
    exact list_getBang_instance_independent _ _ weights.val index.val
      (by simpa [Array.length_eq] using index.isLt)
  have semanticOutput :
      (fun index : Fin 4 =>
        AspisV5CompactFinalFieldSemantics.toExact
          weights.val[index.val]!) =
        AspisV5CompactFinalFieldSemantics.exactOutput
          (callerStateToFinal state) := by
    funext index
    convert congrFun semantic.2 index using 1
    congr 1
    exact list_getBang_instance_independent _ _ weights.val index.val
      (by simpa [Array.length_eq] using index.isLt)
  refine ⟨semanticCanonical, ?_⟩
  calc
    (fun index : Fin 4 =>
        AspisV5CompactFinalFieldSemantics.toExact weights.val[index.val]!) =
        AspisV5CompactFinalFieldSemantics.exactOutput
          (callerStateToFinal state) := semanticOutput
    _ = AspisV5CompactTerminalOptimized.optimizedFinalWeights
          (AspisV5CompactFinalFieldSemantics.projectState
            (callerStateToFinal state)) := scatter.symm
    _ = AspisV5CompactTerminalOptimized.optimizedFinalWeights
          (callerProjectState state) := by rw [callerStateToFinal_project]

/-- The exact delegated compact calls belonging to one accepted relation
execution. -/
structure AcceptedCompactWrapperSubcalls
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array CallerRaw 4#usize}
    {alphas : Array CallerRaw 4#usize}
    {kappa inactiveClaim : CallerRaw}
    {roundChallenges : Array CallerRaw 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : CallerRaw}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) : Type where
  initialState : NewState
  foldState1 : FoldState
  foldState2 : FoldState
  foldState3 : FoldState
  foldState4 : FoldState
  finalWeights : Array FinalRaw 4#usize
  initialRun :
    V5RelationCompactNewGenerated.v5_cu_probe.CompactBTerminalWeights.new
        (callerArrayToNew roundChallenges)
        (callerToNewRaw trace.calls.denseScale) = .ok initialState
  initialProgramRun :
    V5CompactScratchNew.constructorProgram
        (callerArrayToNew roundChallenges)
        (callerToNewRaw trace.calls.denseScale) = .ok initialState
  initialOutput : trace.calls.compact = newStateToCaller initialState
  fold0Run :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
        (callerStateToFold trace.calls.compact)
        (callerToFoldRaw (acceptedAlphaAt alphas 0)) = .ok foldState1
  fold0Output : trace.additive1 = foldStateToCaller foldState1
  fold1Run :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
        (callerStateToFold trace.additive1)
        (callerToFoldRaw (acceptedAlphaAt alphas 1)) = .ok foldState2
  fold1Output : trace.additive2 = foldStateToCaller foldState2
  fold2Run :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
        (callerStateToFold trace.additive2)
        (callerToFoldRaw (acceptedAlphaAt alphas 2)) = .ok foldState3
  fold2Output : trace.additive3 = foldStateToCaller foldState3
  fold3Run :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold
        (callerStateToFold trace.additive3)
        (callerToFoldRaw (acceptedAlphaAt alphas 3)) = .ok foldState4
  fold3Output : trace.additive4 = foldStateToCaller foldState4
  finalWeightsRun :
    V5RelationCompactFinalGenerated.v5_cu_probe.CompactBTerminalWeights.final_weights
        (callerStateToFinal trace.additive4) = .ok finalWeights
  dotProgramRun :
    AspisV5RelationCompactAdditiveDotExact.fourTermDotProgram
        finalWeights trace.finalCoefficients = .ok trace.additiveDot

/-- One accepted trace supplies all constructor, four fold, final-weight, and
dot wrapper subcalls without any caller-supplied source equality. -/
theorem accepted_trace_exposes_compact_wrapper_subcalls
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
    Nonempty (AcceptedCompactWrapperSubcalls trace) := by
  obtain ⟨initialState, initialRun, initialOutput⟩ :=
    caller_new_success_exposes_subcall roundChallenges trace.calls.denseScale
      trace.calls.compact trace.calls.compactSuccess
  obtain ⟨rounds⟩ := accepted_full_trace_exposes_four_round_executions trace
  have fold0Wrapper :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.fold
        trace.calls.compact (acceptedAlphaAt alphas 0) = .ok trace.additive1 := by
    simpa [productionAdditiveInst] using
      rounds.round0.polynomial.scalar.additiveFoldRun
  have fold1Wrapper :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.fold
        trace.additive1 (acceptedAlphaAt alphas 1) = .ok trace.additive2 := by
    simpa [productionAdditiveInst] using
      rounds.round1.polynomial.scalar.additiveFoldRun
  have fold2Wrapper :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.fold
        trace.additive2 (acceptedAlphaAt alphas 2) = .ok trace.additive3 := by
    simpa [productionAdditiveInst] using
      rounds.round2.polynomial.scalar.additiveFoldRun
  have fold3Wrapper :
      V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive.fold
        trace.additive3 (acceptedAlphaAt alphas 3) = .ok trace.additive4 := by
    simpa [productionAdditiveInst] using
      rounds.round3.polynomial.scalar.additiveFoldRun
  obtain ⟨foldState1, fold0Run, fold0Output⟩ :=
    caller_fold_success_exposes_subcall trace.calls.compact
      trace.additive1 (acceptedAlphaAt alphas 0) fold0Wrapper
  obtain ⟨foldState2, fold1Run, fold1Output⟩ :=
    caller_fold_success_exposes_subcall trace.additive1 trace.additive2
      (acceptedAlphaAt alphas 1) fold1Wrapper
  obtain ⟨foldState3, fold2Run, fold2Output⟩ :=
    caller_fold_success_exposes_subcall trace.additive2 trace.additive3
      (acceptedAlphaAt alphas 2) fold2Wrapper
  obtain ⟨foldState4, fold3Run, fold3Output⟩ :=
    caller_fold_success_exposes_subcall trace.additive3 trace.additive4
      (acceptedAlphaAt alphas 3) fold3Wrapper
  obtain ⟨finalWeights, finalWeightsRun, dotProgramRun⟩ :=
    caller_dot_success_exposes_subcalls trace.additive4
      trace.finalCoefficients trace.additiveDot trace.additiveDotSuccess
  have initialProgramRun := initialRun
  rw [generatedNew_eq_constructorProgram] at initialProgramRun
  exact ⟨{
    initialState := initialState
    foldState1 := foldState1
    foldState2 := foldState2
    foldState3 := foldState3
    foldState4 := foldState4
    finalWeights := finalWeights
    initialRun := initialRun
    initialProgramRun := initialProgramRun
    initialOutput := initialOutput
    fold0Run := fold0Run
    fold0Output := fold0Output
    fold1Run := fold1Run
    fold1Output := fold1Output
    fold2Run := fold2Run
    fold2Output := fold2Output
    fold3Run := fold3Run
    fold3Output := fold3Output
    finalWeightsRun := finalWeightsRun
    dotProgramRun := dotProgramRun }⟩

#print axioms caller_new_success_exposes_subcall
#print axioms caller_fold_success_exposes_subcall
#print axioms caller_fold_success_exact
#print axioms caller_dot_success_exposes_subcalls
#print axioms generatedNew_eq_constructorProgram
#print axioms generatedFinalWeights_eq_finalProgram
#print axioms caller_new_success_exact
#print axioms caller_final_weights_success_exact
#print axioms callerStateToNew_project
#print axioms callerStateToFold_project
#print axioms callerStateToFold_releasedSelectors
#print axioms callerStateToFinal_project
#print axioms callerStateToFinal_releasedSelectors
#print axioms accepted_trace_exposes_compact_wrapper_subcalls

end AspisV5CompactCallerWrapperExact
