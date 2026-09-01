import V7LiteralCallerReadonlyMetadataExternal

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1

theorem readonly_account_metadata_v1_exact
    (account : solana_account_info.AccountInfo) :
    v7_pair_forest_dispatch.readonly_account_metadata_v1 account =
      .ok {
        key := account.key
        owner := account.owner
        is_signer := account.is_signer
        is_writable := account.is_writable
        executable := account.executable
      } := by
  rfl

theorem readonly_account_metadata_v1_success_fields
    (account : solana_account_info.AccountInfo)
    (metadata : v7_pair_forest_dispatch.ReadonlyAccountMetadataV1)
    (accepted :
      v7_pair_forest_dispatch.readonly_account_metadata_v1 account =
        .ok metadata) :
    metadata.key = account.key ∧
      metadata.owner = account.owner ∧
      metadata.is_signer = account.is_signer ∧
      metadata.is_writable = account.is_writable ∧
      metadata.executable = account.executable := by
  rw [readonly_account_metadata_v1_exact] at accepted
  cases accepted
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms readonly_account_metadata_v1_exact
#print axioms readonly_account_metadata_v1_success_fields

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
