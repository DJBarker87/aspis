-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart24
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::selector_mask_sum_16]: loop body 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 177:4-182:5 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop0.body
  (mask : Std.U16) (bit : Std.Usize) (population : Std.Usize) :
  Result (ControlFlow (Std.Usize × Std.Usize) Std.Usize)
  := do
  if bit < 16#usize
  then
    let i ← 1#u16 <<< bit
    let i1 ← Std.lift (mask &&& i)
    let population1 ←
      if i1 != 0#u16
      then population + 1#usize
      else ok population
    let bit1 ← bit + 1#usize
    ok (cont (bit1, population1))
  else ok (done population)

end PoolV1CopyLaneBooleanGenerated
