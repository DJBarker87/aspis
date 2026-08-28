-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart45
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::copy_lane_for_registry]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 354:0-394:1 -/
def pool_v1.payment_semantic_terminal.copy_lane_for_registry
  {LINK_COUNT : Std.Usize} (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : pool_v1.payment_semantic_terminal.Selectors)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (patterns : Array
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern 13#usize)
  (links : Array pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentLink
  LINK_COUNT) (active_row_masks : Array Std.U16 64#usize) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  let patterns1 ←
    pool_v1.payment_semantic_terminal.pattern_values openings lambda patterns
  let a := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let a1 := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let a2 := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let a3 := Array.repeat 2#usize aspis_core.field.QM31.ZERO
  let (a4, a5, a6, a7) ←
    pool_v1.payment_semantic_terminal.copy_lane_for_registry_loop selectors
      links patterns1 a a1 a2 a3 0#usize
  let active ←
    pool_v1.payment_semantic_terminal.Selectors.copy_active selectors
      active_row_masks
  let q ←
    pool_v1.payment_semantic_terminal.copy_residual
      {
        producer_values := a4,
        producer_weights := a5,
        consumer_values := a6,
        consumer_weights := a7
      } h1_z chi
  let q1 ← aspis_core.field.QM31.mul active q
  ok (q1, active)

end PoolV1CopyLaneBooleanGenerated
