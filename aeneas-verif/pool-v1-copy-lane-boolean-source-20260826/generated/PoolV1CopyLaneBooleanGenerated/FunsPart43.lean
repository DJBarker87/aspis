-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart42
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::accumulate_copy_endpoint]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 339:0-352:1 -/
def pool_v1.payment_semantic_terminal.accumulate_copy_endpoint
  (values : Array aspis_core.field.QM31 2#usize)
  (weights : Array aspis_core.field.QM31 2#usize)
  (endpoint : pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentEndpoint)
  (tag : Std.U32) (patterns : Array aspis_core.field.QM31 13#usize)
  (selectors : pool_v1.payment_semantic_terminal.Selectors) :
  Result ((Array aspis_core.field.QM31 2#usize) × (Array aspis_core.field.QM31
    2#usize))
  := do
  let i ← Std.lift (core.convert.num.FromUsizeU16.from endpoint.row)
  let selector ← pool_v1.payment_semantic_terminal.Selectors.row selectors i
  let slot ← Std.lift (core.convert.num.FromUsizeU8.from endpoint.slot)
  let q ← Array.index_usize weights slot
  let q1 ← aspis_core.field.QM31.add q selector
  let weights1 ← Array.update weights slot q1
  let q2 ← pool_v1.payment_semantic_terminal.lift tag
  let i1 ← Std.lift (core.convert.num.FromUsizeU8.from endpoint.pattern)
  let q3 ← Array.index_usize patterns i1
  let compressed ← aspis_core.field.QM31.add q2 q3
  let q4 ← Array.index_usize values slot
  let q5 ← aspis_core.field.QM31.mul selector compressed
  let q6 ← aspis_core.field.QM31.add q4 q5
  let values1 ← Array.update values slot q6
  ok (values1, weights1)

end PoolV1CopyLaneBooleanGenerated
