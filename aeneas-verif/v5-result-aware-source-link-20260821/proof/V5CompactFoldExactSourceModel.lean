import V5RelationCompactFoldGeneratedExact

/-! An explicit ten-block model in the corrected extraction's own types. -/

namespace AspisV5CompactFoldExactSource

open Aeneas Aeneas.Std Result
open V5RelationCompactFoldGeneratedExact

abbrev Raw := aspis_core.field.QM31
abbrev Prepared := aspis_core.field.PreparedQm31Multiplier
abbrev Block := v5_cu_probe.CompactBTerminalBlock
abbrev State := v5_cu_probe.CompactBTerminalWeights

def foldBlock (folds : Std.U8) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) (block : Block) : Result Block :=
  match folds with
  | 0#uscalar => do
      let product ← aspis_core.field.QM31.mul block.power_hi block.power_lo
      let sum ← aspis_core.field.qm31_sum_products3_prepared prepared
        (Array.make 3#usize [block.power_lo, block.power_hi, product])
      let factor ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE sum
      let powerLo ← aspis_core.field.QM31.square block.power_hi
      let powerHi ← aspis_core.field.QM31.square powerLo
      let half1 ← aspis_core.field.QM31.half factor
      let half2 ← aspis_core.field.QM31.half half1
      let scale ← aspis_core.field.QM31.mul block.scale half2
      ok { scale := scale, power_lo := powerLo, power_hi := powerHi,
           selector := block.selector }
  | 1#uscalar => do
      let product ← aspis_core.field.QM31.mul block.power_hi block.power_lo
      let sum ← aspis_core.field.qm31_sum_products3_prepared prepared
        (Array.make 3#usize [block.power_lo, block.power_hi, product])
      let lower ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE sum
      let lowerHalf ← aspis_core.field.QM31.half lower
      let lowerQuarter ← aspis_core.field.QM31.half lowerHalf
      let highSquare ← aspis_core.field.QM31.square block.power_hi
      let prepared0 ← Array.index_usize prepared 0#usize
      let prepared1 ← Array.index_usize prepared 1#usize
      let upperSum ← aspis_core.field.qm31_sum_products2_prepared
        (Array.make 2#usize [prepared0, prepared1])
        (Array.make 2#usize [block.power_lo, block.power_hi])
      let upper ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE upperSum
      let upperScaled ← aspis_core.field.QM31.mul highSquare upper
      let upperHalf ← aspis_core.field.QM31.half upperScaled
      let upperQuarter ← aspis_core.field.QM31.half upperHalf
      let scale ← aspis_core.field.QM31.mul block.scale lowerQuarter
      let powerLo ← aspis_core.field.QM31.mul block.scale upperQuarter
      ok { scale := scale, power_lo := powerLo,
           power_hi := aspis_core.field.QM31.ZERO,
           selector := block.selector }
  | 2#uscalar => do
      let lowBit ← lift (block.selector &&& 1#u8)
      let scale ←
        if lowBit = 0#u8 then
          let prepared0 ← Array.index_usize prepared 0#usize
          let product ← aspis_core.field.PreparedQm31Multiplier.mul
            prepared0 block.power_lo
          aspis_core.field.QM31.add block.scale product
        else
          let prepared1 ← Array.index_usize prepared 1#usize
          let prepared2 ← Array.index_usize prepared 2#usize
          aspis_core.field.qm31_sum_products2_prepared
            (Array.make 2#usize [prepared1, prepared2])
            (Array.make 2#usize [block.scale, block.power_lo])
      let half1 ← aspis_core.field.QM31.half scale
      let half2 ← aspis_core.field.QM31.half half1
      ok { scale := half2, power_lo := aspis_core.field.QM31.ZERO,
           power_hi := block.power_hi, selector := block.selector }
  | 3#uscalar => do
      let shifted ← lift (Std.U8.wrapping_shr block.selector 1#u32)
      let selector ← lift (shifted &&& 3#u8)
      let factor ←
        match selector with
        | 0#uscalar => ok aspis_core.field.QM31.ONE
        | 1#uscalar => ok alpha3
        | 2#uscalar => ok alpha2
        | 3#uscalar => ok alpha
        | _ => fail Error.panic
      let half1 ← aspis_core.field.QM31.half factor
      let half2 ← aspis_core.field.QM31.half half1
      let scale ← aspis_core.field.QM31.mul block.scale half2
      ok { scale := scale, power_lo := block.power_lo,
           power_hi := block.power_hi, selector := block.selector }
  | _ => fail Error.panic

def unrolledFold (state : State) (alpha : Raw) : Result State := do
  let alpha2 ← aspis_core.field.QM31.square alpha
  let alpha3 ← aspis_core.field.QM31.mul alpha2 alpha
  let prepared0 ← aspis_core.field.PreparedQm31Multiplier.new alpha3
  let prepared1 ← aspis_core.field.PreparedQm31Multiplier.new alpha2
  let prepared2 ← aspis_core.field.PreparedQm31Multiplier.new alpha
  let prepared := Array.make 3#usize [prepared0, prepared1, prepared2]
  let block0 ← Array.index_usize state.blocks 0#usize
  let output0 ← foldBlock state.folds alpha alpha2 alpha3 prepared block0
  let block1 ← Array.index_usize state.blocks 1#usize
  let output1 ← foldBlock state.folds alpha alpha2 alpha3 prepared block1
  let block2 ← Array.index_usize state.blocks 2#usize
  let output2 ← foldBlock state.folds alpha alpha2 alpha3 prepared block2
  let block3 ← Array.index_usize state.blocks 3#usize
  let output3 ← foldBlock state.folds alpha alpha2 alpha3 prepared block3
  let block4 ← Array.index_usize state.blocks 4#usize
  let output4 ← foldBlock state.folds alpha alpha2 alpha3 prepared block4
  let block5 ← Array.index_usize state.blocks 5#usize
  let output5 ← foldBlock state.folds alpha alpha2 alpha3 prepared block5
  let block6 ← Array.index_usize state.blocks 6#usize
  let output6 ← foldBlock state.folds alpha alpha2 alpha3 prepared block6
  let block7 ← Array.index_usize state.blocks 7#usize
  let output7 ← foldBlock state.folds alpha alpha2 alpha3 prepared block7
  let block8 ← Array.index_usize state.blocks 8#usize
  let output8 ← foldBlock state.folds alpha alpha2 alpha3 prepared block8
  let block9 ← Array.index_usize state.blocks 9#usize
  let output9 ← foldBlock state.folds alpha alpha2 alpha3 prepared block9
  let deltaFactor ←
    match state.folds with
    | 0#uscalar => ok aspis_core.field.QM31.ONE
    | 1#uscalar => ok aspis_core.field.QM31.ONE
    | 2#uscalar => ok alpha2
    | 3#uscalar => ok alpha
    | _ => fail Error.panic
  let deltaHalf ← aspis_core.field.QM31.half deltaFactor
  let deltaQuarter ← aspis_core.field.QM31.half deltaHalf
  let deltaScale ← aspis_core.field.QM31.mul state.delta_scale deltaQuarter
  let folds ← lift (Std.U8.wrapping_add state.folds 1#u8)
  ok {
    blocks := Array.make 10#usize [output0, output1, output2, output3,
      output4, output5, output6, output7, output8, output9]
    delta_scale := deltaScale
    folds := folds }

end AspisV5CompactFoldExactSource
