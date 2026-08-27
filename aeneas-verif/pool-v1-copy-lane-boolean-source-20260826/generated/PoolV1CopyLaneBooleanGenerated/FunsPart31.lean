-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart30
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::{aspis_statement::pool_v1::payment_semantic_terminal::Selectors}::copy_active]: loop body 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 252:8-258:9 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.Selectors.copy_active_loop.body
  (masks : Array Std.U16 64#usize)
  (self : pool_v1.payment_semantic_terminal.Selectors)
  (sum : aspis_core.field.QM31) (block : Std.Usize) :
  Result (ControlFlow (pool_v1.payment_semantic_terminal.Selectors ×
    aspis_core.field.QM31 × Std.Usize) aspis_core.field.QM31)
  := do
  if block < 64#usize
  then
    let mask ← Array.index_usize masks block
    let (self1, sum1) ←
      if mask != 0#u16
      then
        do
        let q ← Array.index_usize self.high block
        let q1 ←
          pool_v1.payment_semantic_terminal.selector_mask_sum_16 self.low mask
        let q2 ← aspis_core.field.QM31.mul q q1
        let sum2 ← aspis_core.field.QM31.add sum q2
        ok (self, sum2)
      else ok (self, sum)
    let block1 ← block + 1#usize
    ok (cont (self1, sum1, block1))
  else ok (done sum)

end PoolV1CopyLaneBooleanGenerated
