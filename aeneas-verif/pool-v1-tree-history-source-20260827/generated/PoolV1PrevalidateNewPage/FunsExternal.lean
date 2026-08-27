import Aeneas
import PoolV1PrevalidateNewPage.Types
import PoolV1NormalizedNewPageData.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1PrevalidateNewPage

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

noncomputable section

/-!
The account-data borrow is the only Solana runtime boundary in this normalized
source composition.  Every Pool-specific step remains executable: the exact
source-closed owner/writable and PDA gates, the extracted 8,256-byte/all-zero
checker, and the production `Result` grammar.
-/

namespace SolanaAccountDataBorrow

axiom tryBorrowData :
  solana_account_info.AccountInfo →
    Result (core.result.Result (Slice Std.U8)
      solana_program_error.ProgramError)

end SolanaAccountDataBorrow

namespace SolanaPdaRuntime

axiom findProgramAddress :
  Slice (Slice Std.U8) → solana_pubkey.Pubkey →
    Result (solana_pubkey.Pubkey × Std.U8)

end SolanaPdaRuntime

def rootPageSeed : Slice Std.U8 :=
  Array.to_slice (Array.make 23#usize [
    97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8,
    112#u8, 111#u8, 111#u8, 108#u8, 45#u8,
    114#u8, 111#u8, 111#u8, 116#u8, 45#u8,
    112#u8, 97#u8, 103#u8, 101#u8, 45#u8, 118#u8, 49#u8 ])

def history.require_program_account
    (account : solana_account_info.AccountInfo)
    (programId : solana_pubkey.Pubkey) (writable : Bool) :
    Result (core.result.Result Unit solana_program_error.ProgramError) :=
  if decide (account.owner.val = programId.val)
  then
    if account.executable
    then .ok (.Err .InvalidAccountData)
    else if account.is_writable != writable
      then .ok (.Err .InvalidAccountData)
      else .ok (.Ok ())
  else .ok (.Err .IncorrectProgramId)

def history.pool_v1_root_page_address
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64) :
    Result (solana_pubkey.Pubkey × Std.U8) := do
  let pageNumberBytes ← lift (core.num.U64.to_le_bytes pageNumber)
  let seeds := Array.to_slice (Array.make 3#usize [
    rootPageSeed, pool.to_slice, Array.to_slice pageNumberBytes ])
  SolanaPdaRuntime.findProgramAddress seeds programId

def history.require_root_page_address
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (account : solana_account_info.AccountInfo) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let (expected, _) ← history.pool_v1_root_page_address
    programId pool pageNumber
  if decide (account.key.val = expected.val)
  then .ok (.Ok ())
  else .ok (.Err (.Custom 1095966722#u32))

def history.validate_new_page_account
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (account : solana_account_info.AccountInfo) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let ownerGate ← history.require_program_account account programId true
  match ownerGate with
  | .Err error => .ok (.Err error)
  | .Ok () => do
    let addressGate ← history.require_root_page_address
      programId pool pageNumber account
    match addressGate with
    | .Err error => .ok (.Err error)
    | .Ok () => do
      let borrowed ← SolanaAccountDataBorrow.tryBorrowData account
      match borrowed with
      | .Err error => .ok (.Err error)
      | .Ok data => do
        let valid ←
          PoolV1NormalizedNewPageData.normalized_validate_new_page_borrowed_data data
        if valid then .ok (.Ok ())
        else .ok (.Err solana_program_error.ProgramError.InvalidAccountData)
