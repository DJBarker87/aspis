-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart43
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::copy_lane_for_registry]: loop body 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 372:4-391:5 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.copy_lane_for_registry_loop.body
  {LINK_COUNT : Std.Usize}
  (selectors : pool_v1.payment_semantic_terminal.Selectors)
  (links : Array pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentLink
  LINK_COUNT) (patterns : Array aspis_core.field.QM31 13#usize)
  (a : Array aspis_core.field.QM31 2#usize)
  (a1 : Array aspis_core.field.QM31 2#usize)
  (a2 : Array aspis_core.field.QM31 2#usize)
  (a3 : Array aspis_core.field.QM31 2#usize) (link_index : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 2#usize) × (Array
    aspis_core.field.QM31 2#usize) × (Array aspis_core.field.QM31 2#usize) ×
    (Array aspis_core.field.QM31 2#usize) × Std.Usize) ((Array
    aspis_core.field.QM31 2#usize) × (Array aspis_core.field.QM31 2#usize) ×
    (Array aspis_core.field.QM31 2#usize) × (Array aspis_core.field.QM31
    2#usize)))
  := do
  if link_index < LINK_COUNT
  then
    let link ← Array.index_usize links link_index
    let (a4, a5) ←
      pool_v1.payment_semantic_terminal.accumulate_copy_endpoint a a1
        link.producer link.tag patterns selectors
    let (a6, a7) ←
      pool_v1.payment_semantic_terminal.accumulate_copy_endpoint a2 a3
        link.consumer link.tag patterns selectors
    let link_index1 ← link_index + 1#usize
    ok (cont (a4, a5, a6, a7, link_index1))
  else ok (done (a, a1, a2, a3))

end PoolV1CopyLaneBooleanGenerated
