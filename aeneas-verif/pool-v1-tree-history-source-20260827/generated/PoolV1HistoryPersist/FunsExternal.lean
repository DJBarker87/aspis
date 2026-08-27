import Aeneas
import PoolV1HistoryPersist.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1HistoryPersistGenerated

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

/-!
Transparent interpretations of every external value used by the focused root
page persistence extraction.
-/

@[rust_fun "aspis_core::field::{aspis_core::field::M31}::to_le_bytes"]
def aspis_core.field.M31.to_le_bytes
    (value : aspis_core.field.M31) : Result (Array Std.U8 4#usize) :=
  .ok (core.num.U32.to_le_bytes value)

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_PAGE_MAGIC"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_MAGIC
    : Result (Array Std.U8 4#usize) :=
  .ok (Array.make 4#usize [65#u8, 83#u8, 80#u8, 82#u8])

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_PAGE_VERSION"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_VERSION
    : Result Std.U8 :=
  .ok 1#u8

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_CAPACITY_LOG2"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY_LOG2
    : Result Std.U8 :=
  .ok 8#u8

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_CAPACITY"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_CAPACITY
    : Result Std.Usize :=
  .ok 256#usize

@[rust_const
  "aspis_statement::pool_v1::root_history::POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES"]
def aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
    : Result Std.Usize :=
  .ok 8256#usize

@[rust_fun
  "solana_pubkey::{core::convert::AsRef<solana_pubkey::Pubkey, [u8]>}::as_ref"]
def solana_pubkey.Pubkey.Insts.CoreConvertAsRefSliceU8.as_ref
    (key : solana_pubkey.Pubkey) : Result (Slice Std.U8) :=
  .ok key.to_slice
