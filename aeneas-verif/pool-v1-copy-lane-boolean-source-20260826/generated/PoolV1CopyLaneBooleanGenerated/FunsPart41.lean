-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart40
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 271:0-309:1 -/
def pool_v1.payment_semantic_terminal.pattern_values
  (openings : Array aspis_core.field.QM31 16#usize)
  (lambda : aspis_core.field.QM31)
  (patterns : Array
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern 13#usize) :
  Result (Array aspis_core.field.QM31 13#usize)
  := do
  let powers := Array.repeat 16#usize aspis_core.field.QM31.ZERO
  let (powers1, limb) ←
    pool_v1.payment_semantic_terminal.pattern_values_loop0 lambda powers lambda
      0#usize
  let result := Array.repeat 13#usize aspis_core.field.QM31.ZERO
  pool_v1.payment_semantic_terminal.pattern_values_loop1 openings patterns
    powers1 limb result 0#usize

end PoolV1CopyLaneBooleanGenerated
