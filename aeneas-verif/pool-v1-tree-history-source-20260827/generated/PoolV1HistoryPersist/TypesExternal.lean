import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-! Executable 32-byte representation of Solana's public-key value. -/

@[reducible, rust_type "solana_pubkey::Pubkey"]
def solana_pubkey.Pubkey := Array Std.U8 32#usize
