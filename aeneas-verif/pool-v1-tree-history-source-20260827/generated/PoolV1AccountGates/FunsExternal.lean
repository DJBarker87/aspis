import Aeneas
import PoolV1AccountGates.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1AccountGates

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_PAGE_SEED"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_SEED :
    Result (Slice Std.U8) :=
  .ok (Array.to_slice (Array.make 23#usize [
    97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8,
    112#u8, 111#u8, 111#u8, 108#u8, 45#u8,
    114#u8, 111#u8, 111#u8, 116#u8, 45#u8,
    112#u8, 97#u8, 103#u8, 101#u8, 45#u8, 118#u8, 49#u8 ]))

@[rust_fun
  "solana_pubkey::{core::cmp::PartialEq<solana_pubkey::Pubkey, solana_pubkey::Pubkey>}::eq"]
def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
    (left right : solana_pubkey.Pubkey) : Result Bool :=
  .ok (decide (left.val = right.val))

@[rust_fun
  "solana_pubkey::{core::convert::AsRef<solana_pubkey::Pubkey, [u8]>}::as_ref"]
def solana_pubkey.Pubkey.Insts.CoreConvertAsRefSliceU8.as_ref
    (key : solana_pubkey.Pubkey) : Result (Slice Std.U8) :=
  .ok key.to_slice

/-!
Solana's PDA primitive is deliberately left at the exact runtime interface.
The source bridge below exposes its concrete returned address and proves that
successful Pool validation accepts only that address.
-/
@[rust_fun "solana_pubkey::{solana_pubkey::Pubkey}::find_program_address"]
axiom solana_pubkey.Pubkey.find_program_address :
  Slice (Slice Std.U8) → solana_pubkey.Pubkey →
    Result (solana_pubkey.Pubkey × Std.U8)
