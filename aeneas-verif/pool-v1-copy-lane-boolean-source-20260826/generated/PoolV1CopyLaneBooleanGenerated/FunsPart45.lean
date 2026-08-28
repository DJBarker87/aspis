-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart44
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::copy_lane_for_registry]: loop 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 372:4-391:5 -/
@[rust_loop]
def pool_v1.payment_semantic_terminal.copy_lane_for_registry_loop
  {LINK_COUNT : Std.Usize}
  (selectors : pool_v1.payment_semantic_terminal.Selectors)
  (links : Array pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentLink
  LINK_COUNT) (patterns : Array aspis_core.field.QM31 13#usize)
  (a : Array aspis_core.field.QM31 2#usize)
  (a1 : Array aspis_core.field.QM31 2#usize)
  (a2 : Array aspis_core.field.QM31 2#usize)
  (a3 : Array aspis_core.field.QM31 2#usize) (link_index : Std.Usize) :
  Result ((Array aspis_core.field.QM31 2#usize) × (Array aspis_core.field.QM31
    2#usize) × (Array aspis_core.field.QM31 2#usize) × (Array
    aspis_core.field.QM31 2#usize))
  := do
  loop
    (fun (a4, a5, a6, a7, link_index1) =>
      pool_v1.payment_semantic_terminal.copy_lane_for_registry_loop.body
      selectors links patterns a4 a5 a6 a7 link_index1)
    (a, a1, a2, a3, link_index)

end PoolV1CopyLaneBooleanGenerated
