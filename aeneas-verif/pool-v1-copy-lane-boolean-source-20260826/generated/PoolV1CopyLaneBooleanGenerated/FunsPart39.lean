-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart38
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]: loop body 1:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 286:4-307:5 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.pattern_values_loop1.body
  (openings : Array aspis_core.field.QM31 16#usize)
  (patterns : Array
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern 13#usize)
  (powers : Array aspis_core.field.QM31 16#usize) (limb : Std.Usize)
  (result : Array aspis_core.field.QM31 13#usize) (pattern_index : Std.Usize) :
  Result (ControlFlow (Std.Usize × (Array aspis_core.field.QM31 13#usize) ×
    Std.Usize) (Array aspis_core.field.QM31 13#usize))
  := do
  if pattern_index < pool_v1.payment_semantic_terminal.COPY_PATTERN_COUNT
  then
    let pattern ← Array.index_usize patterns pattern_index
    let (limb1, value) ←
      pool_v1.payment_semantic_terminal.pattern_values_loop1_loop0 openings
        powers 0#usize pattern aspis_core.field.QM31.ZERO
    let a ← Array.update result pattern_index value
    let pattern_index1 ← pattern_index + 1#usize
    ok (cont (limb1, a, pattern_index1))
  else ok (done result)

end PoolV1CopyLaneBooleanGenerated
