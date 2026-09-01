import V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1

private def literalSixAccounts
    (proofAccount masterAccount checkpointAccount laneAccount registryAccount
      entryAccount : solana_account_info.AccountInfo) :
    Slice solana_account_info.AccountInfo :=
  ⟨[proofAccount, masterAccount, checkpointAccount, laneAccount,
      registryAccount, entryAccount], by scalar_tac⟩

theorem exact_six_account_refs_v1_literal_order
    (proofAccount masterAccount checkpointAccount laneAccount registryAccount
      entryAccount : solana_account_info.AccountInfo) :
    v7_pair_forest_dispatch.exact_six_account_refs_v1
        (literalSixAccounts proofAccount masterAccount checkpointAccount
          laneAccount registryAccount entryAccount) =
      .ok (proofAccount, masterAccount, checkpointAccount, laneAccount,
        registryAccount, entryAccount) := by
  have accountLength :
      Slice.len (literalSixAccounts proofAccount masterAccount checkpointAccount
        laneAccount registryAccount entryAccount) = 6#usize := by
    apply UScalar.eq_of_val_eq
    simp [literalSixAccounts]
  unfold v7_pair_forest_dispatch.exact_six_account_refs_v1
  simp only [accountLength]
  simp [literalSixAccounts, Slice.index_usize]

theorem exact_six_account_refs_v1_success_has_literal_order
    (accounts : Slice solana_account_info.AccountInfo)
    (proofAccount masterAccount checkpointAccount laneAccount registryAccount
      entryAccount : solana_account_info.AccountInfo)
    (accountValues : accounts.val =
      [proofAccount, masterAccount, checkpointAccount, laneAccount,
        registryAccount, entryAccount]) :
    v7_pair_forest_dispatch.exact_six_account_refs_v1 accounts =
      .ok (proofAccount, masterAccount, checkpointAccount, laneAccount,
        registryAccount, entryAccount) := by
  have accountsEq :
      accounts = literalSixAccounts proofAccount masterAccount checkpointAccount
        laneAccount registryAccount entryAccount := by
    apply Subtype.ext
    exact accountValues
  rw [accountsEq]
  exact exact_six_account_refs_v1_literal_order proofAccount masterAccount
    checkpointAccount laneAccount registryAccount entryAccount

#print axioms exact_six_account_refs_v1_literal_order
#print axioms exact_six_account_refs_v1_success_has_literal_order

end V7LiteralCallerExactSixAccountRefsLenPreflightSharedIndexCurrent309bR1
