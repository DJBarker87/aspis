-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart16
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_core::field::{aspis_core::field::QM31}::from_cm31]:
    Source: 'crates/aspis-core/src/field.rs', lines 819:4-819:38
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::from_cm31]
    Visibility: public -/
@[rust_fun "aspis_core::field::{aspis_core::field::QM31}::from_cm31"]
def aspis_core.field.QM31.from_cm31
  (c0 : aspis_core.field.CM31) : Result aspis_core.field.QM31 := do
  ok { c0, c1 := aspis_core.field.CM31.ZERO }

end PoolV1CopyLaneBooleanGenerated
