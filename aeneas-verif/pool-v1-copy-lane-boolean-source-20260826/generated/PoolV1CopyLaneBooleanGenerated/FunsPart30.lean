-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart29
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::{aspis_statement::pool_v1::payment_semantic_terminal::Selectors}::row]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 237:4-240:5 -/
def pool_v1.payment_semantic_terminal.Selectors.row
  (self : pool_v1.payment_semantic_terminal.Selectors) (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  massert (row <
    pool_v1.payment_semantic_terminal.POOL_V1_PAYMENT_TERMINAL_ROWS)
  let i ← row >>> 4#u32
  let q ← Array.index_usize self.high i
  let i1 ← Std.lift (row &&& 15#usize)
  let q1 ← Array.index_usize self.low i1
  aspis_core.field.QM31.mul q q1

end PoolV1CopyLaneBooleanGenerated
