-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart26
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::selector_mask_sum_16]: loop body 1:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 186:4-196:5 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.selector_mask_sum_16_loop1.body
  (values : Array aspis_core.field.QM31 16#usize) (mask : Std.U16)
  (bit : Std.Usize) (complement : Bool) (sum : aspis_core.field.QM31) :
  Result (ControlFlow (Std.Usize × Bool × aspis_core.field.QM31)
    aspis_core.field.QM31)
  := do
  if bit < 16#usize
  then
    let i ← 1#u16 <<< bit
    let i1 ← Std.lift (mask &&& i)
    let (complement1, sum1) ←
      if (i1 != 0#u16) != complement
      then
        do
        let q ←
          if complement
          then
            do
            let q1 ← Array.index_usize values bit
            aspis_core.field.QM31.sub sum q1
          else
            do
            let q1 ← Array.index_usize values bit
            aspis_core.field.QM31.add sum q1
        ok (complement, q)
      else ok (complement, sum)
    let bit1 ← bit + 1#usize
    ok (cont (bit1, complement1, sum1))
  else ok (done sum)

end PoolV1CopyLaneBooleanGenerated
