import Aeneas

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-!
The focused helper neither reads nor mutates an `AccountInfo`; it only returns
the six shared references in their literal source order.  This concrete carrier
keeps that order observable without importing Solana's interior-borrow graph.
The whole-caller replay below translates the same helper with the production
`AccountInfo` type, so this carrier is not a semantic assumption about account
contents.
-/
@[rust_type "solana_account_info::AccountInfo" (mutRegions := #[0])]
structure solana_account_info.AccountInfo where
  identity : Nat

