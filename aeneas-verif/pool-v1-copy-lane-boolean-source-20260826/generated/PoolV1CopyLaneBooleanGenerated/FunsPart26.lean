-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart25
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::selector_mask_sum_16]: loop 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 177:4-182:5 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop0
  (mask : Std.U16) (bit : Std.Usize) (population : Std.Usize) :
  Result Std.Usize
  := do
  loop
    (fun (bit1, population1) =>
      pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop0.body mask
      bit1 population1)
    (bit, population)

end PoolV1CopyLaneBooleanGenerated
