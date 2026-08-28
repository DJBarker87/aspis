-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart23
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::lift]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 169:0-171:1 -/
def pool_v1.payment_semantic_terminal.lift
  (value : aspis_core.field.M31) : Result aspis_core.field.QM31 := do
  let c ← aspis_core.field.CM31.from_m31 value
  aspis_core.field.QM31.from_cm31 c

end PoolV1CopyLaneBooleanGenerated
