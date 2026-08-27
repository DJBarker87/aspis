import PoolV1AccountGates.Funs

/-!
# Pool V1 literal account-gate source bridge

This file proves the exact owner, executable, writable and PDA-address facts
enforced by the three small production account gates.  The Solana PDA
primitive itself remains at its named runtime interface; successful source
validation is proved to accept only the address it returned.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace PoolV1AccountGatesBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1AccountGates

theorem pubkey_decide_true_iff
    (left right : solana_pubkey.Pubkey) :
    decide (left.val = right.val) = true ↔ left = right := by
  rw [decide_eq_true_eq]
  constructor
  · intro valuesEqual
    exact Subtype.ext valuesEqual
  · intro keysEqual
    cases keysEqual
    rfl

theorem require_program_account_success_exact
    (account : solana_account_info.AccountInfo)
    (programId : solana_pubkey.Pubkey) (writable : Bool)
    (run : history.require_program_account account programId writable =
      .ok (.Ok ())) :
    account.owner = programId ∧
      account.executable = false ∧ account.is_writable = writable := by
  unfold history.require_program_account at run
  simp [core.cmp.impls.PartialEqShared.ne,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
    pubkey_decide_true_iff] at run
  by_cases ownerValues : account.owner.val = programId.val
  · have ownerExact : account.owner = programId := Subtype.ext ownerValues
    simp [ownerValues] at run
    by_cases executableTrue : account.executable = true
    · simp [executableTrue] at run
    · have executableFalse : account.executable = false :=
        Bool.eq_false_of_not_eq_true executableTrue
      by_cases writableExact : account.is_writable = writable
      · exact ⟨ownerExact, executableFalse, writableExact⟩
      · simp [executableTrue, writableExact] at run
  · simp [ownerValues] at run

theorem require_program_owned_success_exact
    (account : solana_account_info.AccountInfo)
    (programId : solana_pubkey.Pubkey)
    (run : history.require_program_owned account programId = .ok (.Ok ())) :
    account.owner = programId ∧ account.executable = false := by
  unfold history.require_program_owned at run
  simp [core.cmp.impls.PartialEqShared.ne,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
    pubkey_decide_true_iff] at run
  by_cases ownerValues : account.owner.val = programId.val
  · have ownerExact : account.owner = programId := Subtype.ext ownerValues
    simp [ownerValues] at run
    exact ⟨ownerExact, run⟩
  · simp [ownerValues] at run

theorem require_root_page_address_success_exact
    (programId pool : solana_pubkey.Pubkey) (pageNumber : Std.U64)
    (account : solana_account_info.AccountInfo)
    (expected : solana_pubkey.Pubkey) (bump : Std.U8)
    (addressRun : history.pool_v1_root_page_address
      programId pool pageNumber = .ok (expected, bump))
    (run : history.require_root_page_address
      programId pool pageNumber account = .ok (.Ok ())) :
    account.key = expected := by
  unfold history.require_root_page_address at run
  rw [addressRun] at run
  simp [core.cmp.impls.PartialEqShared.ne,
    core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
    pubkey_decide_true_iff] at run
  by_contra keysDiffer
  have valuesDiffer : account.key.val ≠ expected.val := by
    intro valuesEqual
    exact keysDiffer (Subtype.ext valuesEqual)
  have impossible := run valuesDiffer
  simp [solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
    at impossible

#print axioms require_program_account_success_exact
#print axioms require_program_owned_success_exact
#print axioms require_root_page_address_success_exact

end PoolV1AccountGatesBridge
