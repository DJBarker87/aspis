-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart12
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::CM31}::mul_m31]:
    Source: 'crates/aspis-core/src/field.rs', lines 274:4-274:42
    Name pattern: [aspis_core::field::{aspis_core::field::CM31}::mul_m31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::mul_m31"]
def aspis_core.field.CM31.mul_m31
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.CM31
  := do
  let m ← aspis_core.field.M31.mul self.a rhs
  let m1 ← aspis_core.field.M31.mul self.b rhs
  ok { a := m, b := m1 }

end PoolV1CopyLaneBooleanGenerated
