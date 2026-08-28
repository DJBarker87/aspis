-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart18
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::QM31}::sub]:
    Source: 'crates/aspis-core/src/field.rs', lines 832:4-832:39
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::sub]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::sub"]
def aspis_core.field.QM31.sub
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let c ← aspis_core.field.CM31.sub self.c0 rhs.c0
  let c1 ← aspis_core.field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

end PoolV1CopyLaneBooleanGenerated
