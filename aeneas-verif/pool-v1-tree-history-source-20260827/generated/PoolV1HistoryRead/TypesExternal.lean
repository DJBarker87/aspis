import PoolV1HistoryPersist.TypesExternal

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-! Reuse the identical executable Pubkey model from the persistence
translation so both focused source slices can be imported in one theorem. -/
