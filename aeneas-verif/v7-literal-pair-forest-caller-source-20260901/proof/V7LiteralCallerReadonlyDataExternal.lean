import V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1

/-!
# Exact borrow-ready model for the production read-only account-data helper

Solana's literal `AccountInfo::try_borrow_data` returns
`Ref<'a, &'a mut [u8]>`.  Even after the production helper maps it to
`Ref<'a, [u8]>`, current Aeneas cannot synthesize the nested mutable
`RefCell` write-back graph.  This executable external definition therefore
models the exact production entry state used by the verifier: no outstanding
data borrow exists, the dynamic borrow succeeds, and the resulting guard views
the account's byte slice without mutation.

This is deliberately a named Solana entry-state/platform boundary.  It does
not claim that arbitrary host calls with an outstanding mutable borrow succeed.
The caller's parsing, authentication, verifier invocation, result construction,
and fail-closed branches remain in the translated graph.
-/

@[rust_fun
  "core::cell::{impl core::ops::deref::Deref<T> for core::cell::Ref<'_0, T>}::deref"]
def core.cell.Ref.Insts.CoreOpsDerefDeref.deref
    {T : Type} (value : core.cell.Ref T) : Result T :=
  ok value

@[rust_fun
  "aspis_verifier::v7_pair_forest_dispatch::borrow_readonly_account_data"]
def v7_pair_forest_dispatch.borrow_readonly_account_data
    (account : solana_account_info.AccountInfo) :
    Result (core.result.Result (core.cell.Ref (Slice Std.U8))
      solana_program_error.ProgramError) :=
  ok (.Ok account.data)

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
