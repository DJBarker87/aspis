import V7LiteralCallerReadonlyDataExternal

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1

theorem borrow_readonly_account_data_borrow_ready_exact
    (account : solana_account_info.AccountInfo) :
    v7_pair_forest_dispatch.borrow_readonly_account_data account =
      .ok (.Ok account.data) := by
  rfl

theorem borrow_readonly_account_data_success_is_exact_view
    (account : solana_account_info.AccountInfo)
    (view : core.cell.Ref (Slice Std.U8))
    (accepted :
      v7_pair_forest_dispatch.borrow_readonly_account_data account =
        .ok (.Ok view)) :
    view = account.data := by
  rw [borrow_readonly_account_data_borrow_ready_exact] at accepted
  cases accepted
  rfl

theorem readonly_data_guard_deref_is_exact
    (view : core.cell.Ref (Slice Std.U8)) :
    core.cell.Ref.Insts.CoreOpsDerefDeref.deref view = .ok view := by
  rfl

#print axioms borrow_readonly_account_data_borrow_ready_exact
#print axioms borrow_readonly_account_data_success_is_exact_view
#print axioms readonly_data_guard_deref_is_exact

end V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1
