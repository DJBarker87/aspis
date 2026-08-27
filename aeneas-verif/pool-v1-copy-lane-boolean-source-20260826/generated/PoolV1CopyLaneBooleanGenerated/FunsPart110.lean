-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart109
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pool_v1_payment_copy_lane_boolean_extraction_v1]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 436:0-458:1
    Visibility: public -/
def
  pool_v1.payment_semantic_terminal.pool_v1_payment_copy_lane_boolean_extraction_v1
  (variant : Std.U8) (selected_row : Std.U16)
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31) (lambda : aspis_core.field.QM31)
  (chi : aspis_core.field.QM31) :
  Result (Option (aspis_core.field.QM31 × aspis_core.field.QM31))
  := do
  let i ← Std.lift (core.convert.num.FromUsizeU16.from selected_row)
  if i >= pool_v1.payment_semantic_terminal.POOL_V1_PAYMENT_TERMINAL_ROWS
  then ok none
  else
    match variant with
    | 0#uscalar =>
      let high := Array.repeat 64#usize aspis_core.field.QM31.ZERO
      let low := Array.repeat 16#usize aspis_core.field.QM31.ZERO
      let i1 ← selected_row >>> 4#u32
      let i2 ← Std.lift (core.convert.num.FromUsizeU16.from i1)
      let high1 ← Array.update high i2 aspis_core.field.QM31.ONE
      let i3 ← Std.lift (selected_row &&& 15#u16)
      let i4 ← Std.lift (core.convert.num.FromUsizeU16.from i3)
      let low1 ← Array.update low i4 aspis_core.field.QM31.ONE
      let p ←
        pool_v1.payment_semantic_terminal.copy_lane openings h1_z
          { high := high1, low := low1 } lambda chi
          pool_v1.payment_semantic_terminal.CompiledVariant.PrivateTransfer
      ok (some p)
    | 1#uscalar =>
      let high := Array.repeat 64#usize aspis_core.field.QM31.ZERO
      let low := Array.repeat 16#usize aspis_core.field.QM31.ZERO
      let i1 ← selected_row >>> 4#u32
      let i2 ← Std.lift (core.convert.num.FromUsizeU16.from i1)
      let high1 ← Array.update high i2 aspis_core.field.QM31.ONE
      let i3 ← Std.lift (selected_row &&& 15#u16)
      let i4 ← Std.lift (core.convert.num.FromUsizeU16.from i3)
      let low1 ← Array.update low i4 aspis_core.field.QM31.ONE
      let p ←
        pool_v1.payment_semantic_terminal.copy_lane openings h1_z
          { high := high1, low := low1 } lambda chi
          pool_v1.payment_semantic_terminal.CompiledVariant.Withdrawal
      ok (some p)
    | _ => ok none

end PoolV1CopyLaneBooleanGenerated
