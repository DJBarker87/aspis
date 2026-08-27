-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart34
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]: loop body 0:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 279:4-283:5 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.pattern_values_loop0.body
  (lambda : aspis_core.field.QM31)
  (powers : Array aspis_core.field.QM31 16#usize)
  (power : aspis_core.field.QM31) (limb : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 16#usize) ×
    aspis_core.field.QM31 × Std.Usize) ((Array aspis_core.field.QM31 16#usize)
    × Std.Usize))
  := do
  if limb < poseidon2.POSEIDON2_WIDTH
  then
    let a ← Array.update powers limb power
    let power1 ← aspis_core.field.QM31.mul power lambda
    let limb1 ← limb + 1#usize
    ok (cont (a, power1, limb1))
  else ok (done (powers, limb))

end PoolV1CopyLaneBooleanGenerated
