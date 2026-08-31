import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- The translated readonly helper never invokes RefCell or Rc operations. -/
@[reducible, rust_type "core::cell::RefCell"]
def core.cell.RefCell (T : Type) := T

@[reducible, rust_type "alloc::rc::Rc"]
def alloc.rc.Rc (T : Type) := T

@[reducible, rust_type "solana_pubkey::Pubkey"]
def solana_pubkey.Pubkey := Array Std.U8 32#usize
