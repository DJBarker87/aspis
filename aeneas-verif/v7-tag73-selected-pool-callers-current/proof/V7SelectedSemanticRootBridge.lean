import V7Tag73SelectedSemanticLoopForm.Funs

/-!
# Selected Tag-73 Pool semantic-root source bridge

The imported definitions are the literal Charon/Aeneas translation of the two
production roots selected by the Pool verifier.  These lemmas expose the
important fail-closed control-flow fact: a successful root can only arise from
a successful `terminal_parts` evaluation.  In particular, neither the private
transfer nor withdrawal wrapper can turn an inner terminal error into an
accepted field value.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace AspisV7SelectedSemanticRootBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7Tag73SelectedSemanticLoopFormGenerated
open V7Tag73SelectedSemanticLoopFormGenerated.pool_v1
open V7Tag73SelectedSemanticLoopFormGenerated.pool_v1.pair_forest_semantic_terminal

theorem private_transfer_success_implies_terminal_parts_success
    (public1 : payment_relation.PoolV1PrivateTransferPublicV1)
    (transition : pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (claims : Array aspis_core.field.QM31 84#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (lambda chi theta : aspis_core.field.QM31)
    (zerocheckPoint : Array aspis_core.field.QM31 10#usize)
    (mu eta output : aspis_core.field.QM31)
    (run :
      pair_forest_semantic_terminal.evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1
          public1 transition claims point lambda chi theta zerocheckPoint mu eta =
        .ok (.Ok output)) :
    ∃ original c1 maskOnly g,
      pair_forest_semantic_terminal.terminal_parts
          {
            variant := pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer
            pool := public1.pool
            deployment_domain := public1.deployment_domain
            anchor := public1.anchor_root
            nullifier := public1.nullifier
            asset_id := public1.asset_id
            recipient := some public1.recipient_commitment
            change := public1.change_commitment
            withdrawal_amount := none
            transition := transition
          }
          claims point lambda chi theta zerocheckPoint mu =
        .ok (.Ok (original, c1, maskOnly, g)) := by
  simp only [
    pair_forest_semantic_terminal.evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
    pair_forest_semantic_terminal.private_public, bind_tc_ok] at run
  generalize partsRun : pair_forest_semantic_terminal.terminal_parts
      {
        variant := pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer
        pool := public1.pool
        deployment_domain := public1.deployment_domain
        anchor := public1.anchor_root
        nullifier := public1.nullifier
        asset_id := public1.asset_id
        recipient := some public1.recipient_commitment
        change := public1.change_commitment
        withdrawal_amount := none
        transition := transition
      }
      claims point lambda chi theta zerocheckPoint mu = partsResult at run ⊢
  cases partsResult with
  | fail error => simp at run
  | div => simp at run
  | ok inner =>
      cases inner with
      | Err terminalError =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at run
      | Ok parts =>
          rcases parts with ⟨original, c1, maskOnly, g⟩
          exact ⟨original, c1, maskOnly, g, rfl⟩

theorem withdrawal_success_implies_terminal_parts_success
    (public1 : payment_relation.PoolV1WithdrawalPublicV1)
    (transition : pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (claims : Array aspis_core.field.QM31 84#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (lambda chi theta : aspis_core.field.QM31)
    (zerocheckPoint : Array aspis_core.field.QM31 10#usize)
    (mu eta output : aspis_core.field.QM31)
    (run :
      pair_forest_semantic_terminal.evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1
          public1 transition claims point lambda chi theta zerocheckPoint mu eta =
        .ok (.Ok output)) :
    ∃ original c1 maskOnly g,
      pair_forest_semantic_terminal.terminal_parts
          {
            variant := pair_forest_semantic_terminal.CompiledVariant.Withdrawal
            pool := public1.pool
            deployment_domain := public1.deployment_domain
            anchor := public1.anchor_root
            nullifier := public1.nullifier
            asset_id := public1.asset_id
            recipient := none
            change := public1.change_commitment
            withdrawal_amount := some public1.amount
            transition := transition
          }
          claims point lambda chi theta zerocheckPoint mu =
        .ok (.Ok (original, c1, maskOnly, g)) := by
  simp only [
    pair_forest_semantic_terminal.evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1,
    pair_forest_semantic_terminal.withdrawal_public, bind_tc_ok] at run
  generalize partsRun : pair_forest_semantic_terminal.terminal_parts
      {
        variant := pair_forest_semantic_terminal.CompiledVariant.Withdrawal
        pool := public1.pool
        deployment_domain := public1.deployment_domain
        anchor := public1.anchor_root
        nullifier := public1.nullifier
        asset_id := public1.asset_id
        recipient := none
        change := public1.change_commitment
        withdrawal_amount := some public1.amount
        transition := transition
      }
      claims point lambda chi theta zerocheckPoint mu = partsResult at run ⊢
  cases partsResult with
  | fail error => simp at run
  | div => simp at run
  | ok inner =>
      cases inner with
      | Err terminalError =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at run
      | Ok parts =>
          rcases parts with ⟨original, c1, maskOnly, g⟩
          exact ⟨original, c1, maskOnly, g, rfl⟩

#print axioms private_transfer_success_implies_terminal_parts_success
#print axioms withdrawal_success_implies_terminal_parts_success

end AspisV7SelectedSemanticRootBridge
