import V5RelationCompactFoldGenerated
import V5RelationCompactFoldKernelProof
import V5CompactFoldCorrectedWrapper

/-!
# Explicit released compact-fold program

The extracted mutable iterator is reduced separately for each of the four
fold-counter values reachable in the released verifier.  This module contains
the common explicit ten-block program used by those four source equalities.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CompactFoldSource

open V5RelationCompactFoldGenerated
open AspisV5RelationCompactFoldKernelProof

abbrev Raw := aspis_core.field.QM31
abbrev Prepared := aspis_core.field.PreparedQm31Multiplier
abbrev Block := v5_cu_probe.CompactBTerminalBlock
abbrev State := v5_cu_probe.CompactBTerminalWeights

def foldBlock (folds : Std.U8) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) (block : Block) : Result Block :=
  match folds with
  | 0#uscalar => foldZeroBlock prepared block
  | 1#uscalar => foldOneBlock prepared block
  | 2#uscalar =>
      if (block.selector &&& 1#u8) = 0#u8 then
        foldTwoEvenBlock prepared block
      else foldTwoOddBlock prepared block
  | 3#uscalar =>
      match (Std.U8.wrapping_shr block.selector 1#u32 &&& 3#u8) with
      | 0#uscalar => foldThreeBlock aspis_core.field.QM31.ONE block
      | 1#uscalar => foldThreeBlock alpha3 block
      | 2#uscalar => foldThreeBlock alpha2 block
      | 3#uscalar => foldThreeBlock alpha block
      | _ => fail panic
  | _ => fail panic

def unrolledFold (state : State) (alpha : Raw) : Result State := do
  let alpha2 <- aspis_core.field.QM31.square alpha
  let alpha3 <- aspis_core.field.QM31.mul alpha2 alpha
  let prepared0 <- aspis_core.field.PreparedQm31Multiplier.new alpha3
  let prepared1 <- aspis_core.field.PreparedQm31Multiplier.new alpha2
  let prepared2 <- aspis_core.field.PreparedQm31Multiplier.new alpha
  let prepared := Array.make 3#usize [prepared0, prepared1, prepared2]
  let block0 <- Array.index_usize state.blocks 0#usize
  let output0 <- foldBlock state.folds alpha alpha2 alpha3 prepared block0
  let block1 <- Array.index_usize state.blocks 1#usize
  let output1 <- foldBlock state.folds alpha alpha2 alpha3 prepared block1
  let block2 <- Array.index_usize state.blocks 2#usize
  let output2 <- foldBlock state.folds alpha alpha2 alpha3 prepared block2
  let block3 <- Array.index_usize state.blocks 3#usize
  let output3 <- foldBlock state.folds alpha alpha2 alpha3 prepared block3
  let block4 <- Array.index_usize state.blocks 4#usize
  let output4 <- foldBlock state.folds alpha alpha2 alpha3 prepared block4
  let block5 <- Array.index_usize state.blocks 5#usize
  let output5 <- foldBlock state.folds alpha alpha2 alpha3 prepared block5
  let block6 <- Array.index_usize state.blocks 6#usize
  let output6 <- foldBlock state.folds alpha alpha2 alpha3 prepared block6
  let block7 <- Array.index_usize state.blocks 7#usize
  let output7 <- foldBlock state.folds alpha alpha2 alpha3 prepared block7
  let block8 <- Array.index_usize state.blocks 8#usize
  let output8 <- foldBlock state.folds alpha alpha2 alpha3 prepared block8
  let block9 <- Array.index_usize state.blocks 9#usize
  let output9 <- foldBlock state.folds alpha alpha2 alpha3 prepared block9
  let deltaFactor <-
    match state.folds with
    | 0#uscalar => ok aspis_core.field.QM31.ONE
    | 1#uscalar => ok aspis_core.field.QM31.ONE
    | 2#uscalar => ok alpha2
    | 3#uscalar => ok alpha
    | _ => fail panic
  let deltaHalf <- aspis_core.field.QM31.half deltaFactor
  let deltaQuarter <- aspis_core.field.QM31.half deltaHalf
  let deltaScale <- aspis_core.field.QM31.mul state.delta_scale deltaQuarter
  let folds <- lift (Std.U8.wrapping_add state.folds 1#u8)
  ok {
    blocks := Array.make 10#usize [output0, output1, output2, output3,
      output4, output5, output6, output7, output8, output9]
    delta_scale := deltaScale
    folds := folds }

end V5CompactFoldSource
