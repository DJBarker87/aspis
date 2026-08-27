-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart27
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::selector_mask_sum_16]: loop 1:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 186:4-196:5 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop1
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16)
  (bit : Std.Usize) (complement : Bool) (sum : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (bit1, complement1, sum1) =>
      pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop1.body values
      mask bit1 complement1 sum1)
    (bit, complement, sum)

end PoolV1CopyLaneBooleanGenerated
