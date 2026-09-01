import V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1.Types
import V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1

/-!
The accepted whole-caller graph intentionally leaves this one accessor opaque
to avoid reintroducing Solana's interior-borrow graph.  Its implementation here
is not an assumption: it calls the independently translated literal production
helper and only changes the generated namespace of the returned structure.
-/
@[rust_fun
  "aspis_verifier::v7_pair_forest_dispatch::readonly_account_metadata_v1"]
def v7_pair_forest_dispatch.readonly_account_metadata_v1
    (account : solana_account_info.AccountInfo) :
    Result v7_pair_forest_dispatch.ReadonlyAccountMetadataV1 := do
  let metadata ←
    V7LiteralCallerReadonlyMetadataHelperCurrent309bR1.v7_pair_forest_dispatch.readonly_account_metadata_v1
      account
  ok {
    key := metadata.key
    owner := metadata.owner
    is_signer := metadata.is_signer
    is_writable := metadata.is_writable
    executable := metadata.executable
  }

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
