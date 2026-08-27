-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart31
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::{aspis_statement::pool_v1::payment_semantic_terminal::Selectors}::copy_active]: loop 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 252:8-258:9 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.Selectors.copy_active_loop
  (self : pool_v1.payment_semantic_terminal.Selectors)
  (masks : Array Std.U16 64#usize) (sum : aspis_core.field.QM31)
  (block : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (self1, sum1, block1) =>
      pool_v1.payment_semantic_terminal.Selectors.copy_active_loop.body masks
      self1 sum1 block1)
    (self, sum, block)

end PoolV1CopyLaneBooleanGenerated
