-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart35
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]: loop 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 279:4-283:5 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.pattern_values_loop0
  (lambda : aspis_core.field.QM31)
  (powers : Array aspis_core.field.QM31 16#usize)
  (power : aspis_core.field.QM31) (limb : Std.Usize) :
  Result ((Array aspis_core.field.QM31 16#usize) × Std.Usize)
  := do
  loop
    (fun (powers1, power1, limb1) =>
      pool_v1.payment_semantic_terminal.pattern_values_loop0.body lambda
      powers1 power1 limb1)
    (powers, power, limb)

end PoolV1CopyLaneBooleanGenerated
