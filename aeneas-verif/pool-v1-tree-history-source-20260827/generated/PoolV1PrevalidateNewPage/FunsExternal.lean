import Aeneas
import PoolV1PrevalidateNewPage.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1PrevalidateNewPage

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-!
Current Aeneas reaches an internal `Unreachable` while translating the
AccountInfo data borrow in this production function.  It is therefore the
single explicit source boundary for this focused token-constructor graph.
-/
axiom history.validate_new_page_account :
  solana_pubkey.Pubkey → solana_pubkey.Pubkey → Std.U64 →
    solana_account_info.AccountInfo →
      Result (core.result.Result Unit solana_program_error.ProgramError)
