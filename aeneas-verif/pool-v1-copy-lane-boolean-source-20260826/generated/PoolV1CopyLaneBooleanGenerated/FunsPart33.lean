-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart32
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::{aspis_statement::pool_v1::payment_semantic_terminal::Selectors}::copy_active]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 249:4-260:5 -/
@[reducible]
def pool_v1.payment_semantic_terminal.Selectors.copy_active
  (self : pool_v1.payment_semantic_terminal.Selectors)
  (masks : Array Std.U16 64#usize) :
  Result aspis_core.field.QM31
  := do
  pool_v1.payment_semantic_terminal.Selectors.copy_active_loop self masks
    aspis_core.field.QM31.ZERO 0#usize

end PoolV1CopyLaneBooleanGenerated
