-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart13
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::mul_by_r]:
    Source: 'crates/aspis-core/src/field.rs', lines 788:0-788:28
    Name pattern: [aspis_core::field::mul_by_r] -/
@[rust_fun "aspis_core::field::mul_by_r"]
def aspis_core.field.mul_by_r
  (x : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let m ← aspis_core.field.M31.double x.a
  let m1 ← aspis_core.field.M31.sub m x.b
  let m2 ← aspis_core.field.M31.double x.b
  let m3 ← aspis_core.field.M31.add x.a m2
  ok { a := m1, b := m3 }

end PoolV1CopyLaneBooleanGenerated
