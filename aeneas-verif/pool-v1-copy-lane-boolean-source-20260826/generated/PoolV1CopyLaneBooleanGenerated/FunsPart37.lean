-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart36
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::pattern_values]: loop body 2:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 290:8-304:9 -/
@[rust_loop_body]
def pool_v1.payment_semantic_terminal.pattern_values_loop1_loop0.body
  (openings : Array aspis_core.field.QM31 16#usize)
  (powers : Array aspis_core.field.QM31 16#usize)
  (pattern : pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern)
  (limb : Std.Usize) (value : aspis_core.field.QM31) :
  Result (ControlFlow (Std.Usize × aspis_core.field.QM31) (Std.Usize ×
    aspis_core.field.QM31))
  := do
  if limb < poseidon2.POSEIDON2_WIDTH
  then
    let i ← Array.index_usize pattern.kinds limb
    match i with
    | 0#uscalar => let limb1 ← limb + 1#usize
                   ok (cont (limb1, value))
    | 1#uscalar =>
      let i1 ← Array.index_usize pattern.offsets limb
      let source ← pool_v1.payment_semantic_terminal.lift i1
      let q ← Array.index_usize powers limb
      let q1 ← aspis_core.field.QM31.mul q source
      let value1 ← aspis_core.field.QM31.add value q1
      let limb1 ← limb + 1#usize
      ok (cont (limb1, value1))
    | 2#uscalar =>
      let i1 ← Array.index_usize pattern.columns limb
      let i2 ← Std.lift (core.convert.num.FromUsizeU8.from i1)
      let q ← Array.index_usize openings i2
      let i3 ← Array.index_usize pattern.scales limb
      let q1 ← aspis_core.field.QM31.mul_m31 q i3
      let i4 ← Array.index_usize pattern.offsets limb
      let q2 ← pool_v1.payment_semantic_terminal.lift i4
      let source ← aspis_core.field.QM31.add q1 q2
      let q3 ← Array.index_usize powers limb
      let q4 ← aspis_core.field.QM31.mul q3 source
      let value1 ← aspis_core.field.QM31.add value q4
      let limb1 ← limb + 1#usize
      ok (cont (limb1, value1))
    | _ => fail panic
  else ok (done (limb, value))

end PoolV1CopyLaneBooleanGenerated
