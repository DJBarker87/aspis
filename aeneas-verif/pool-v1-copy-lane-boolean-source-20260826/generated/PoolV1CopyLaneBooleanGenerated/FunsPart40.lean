-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart39
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]: loop 1:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 286:4-307:5 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.pattern_values_loop1
  (openings : Array aspis_core.field.QM31 16#usize)
  (patterns : Array
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern 13#usize)
  (powers : Array aspis_core.field.QM31 16#usize) (limb : Std.Usize)
  (result : Array aspis_core.field.QM31 13#usize) (pattern_index : Std.Usize) :
  Result (Array aspis_core.field.QM31 13#usize)
  := do
  loop
    (fun (limb1, result1, pattern_index1) =>
      pool_v1.payment_semantic_terminal.pattern_values_loop1.body openings
      patterns powers limb1 result1 pattern_index1)
    (limb, result, pattern_index)

end PoolV1CopyLaneBooleanGenerated
