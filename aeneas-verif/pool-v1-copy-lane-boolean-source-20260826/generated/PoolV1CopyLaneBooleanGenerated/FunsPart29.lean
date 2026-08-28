-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart28
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::selector_mask_sum_16]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 174:0-198:1 -/
def pool_v1.payment_semantic_terminal.selector_mask_sum_16
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16) :
  Result aspis_core.field.QM31
  := do
  let population ←
    pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop0 mask 0#usize
      0#usize
  let (complement, sum) ←
    if population > 8#usize
    then ok (true, aspis_core.field.QM31.ONE)
    else ok (false, aspis_core.field.QM31.ZERO)
  pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop1 values mask
    0#usize complement sum

end PoolV1CopyLaneBooleanGenerated
