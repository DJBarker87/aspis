-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart37
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]: loop 2:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 290:8-304:9 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.pattern_values_loop1_loop0
  (openings : Array aspis_core.field.QM31 16#usize)
  (powers : Array aspis_core.field.QM31 16#usize) (limb : Std.Usize)
  (pattern : pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern)
  (value : aspis_core.field.QM31) :
  Result (Std.Usize × aspis_core.field.QM31)
  := do
  loop
    (fun (limb1, value1) =>
      pool_v1.payment_semantic_terminal.pattern_values_loop1_loop0.body
      openings powers pattern limb1 value1)
    (limb, value)

end PoolV1CopyLaneBooleanGenerated
