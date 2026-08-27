import PoolV1HistoryPersist.TypesExternal

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-!
The account gates only inspect AccountInfo value fields.  Reference counting
and interior-mutability operations are absent from this focused source graph,
so their carrier types have an exact value-only executable model here.
-/

@[reducible, rust_type "core::cell::RefCell"]
def core.cell.RefCell (T : Type) := T

@[reducible, rust_type "alloc::rc::Rc"]
def alloc.rc.Rc (T : Type) := T
