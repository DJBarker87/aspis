import Aeneas
import V7RegistryV2ProductionReadonly.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

open V7RegistryV2ProductionReadonlyGenerated

@[rust_fun
  "solana_pubkey::{core::cmp::PartialEq<solana_pubkey::Pubkey, solana_pubkey::Pubkey>}::eq"]
def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq
    (left right : solana_pubkey.Pubkey) : Result Bool :=
  .ok (decide (left.val = right.val))
