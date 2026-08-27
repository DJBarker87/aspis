import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-!
Executable interpretation of Solana's 32-byte public-key value for the
focused Pool V1 program afterimage extraction.
-/

@[reducible, rust_type "solana_pubkey::Pubkey"]
def solana_pubkey.Pubkey := Array Std.U8 32#usize
