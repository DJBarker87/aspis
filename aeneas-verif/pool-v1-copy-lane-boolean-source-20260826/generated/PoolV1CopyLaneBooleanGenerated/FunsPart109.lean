-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart108
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::copy_lane]:
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs', lines 396:0-426:1 -/
def pool_v1.payment_semantic_terminal.copy_lane
  (openings : Array aspis_core.field.QM31 16#usize)
  (h1_z : aspis_core.field.QM31)
  (selectors : pool_v1.payment_semantic_terminal.Selectors)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (variant : pool_v1.payment_semantic_terminal.CompiledVariant) :
  Result (aspis_core.field.QM31 × aspis_core.field.QM31)
  := do
  match variant with
  | pool_v1.payment_semantic_terminal.CompiledVariant.PrivateTransfer =>
    pool_v1.payment_semantic_terminal.copy_lane_for_registry openings h1_z
      selectors lambda chi
      pool_v1.payment_semantic_terminal.constants.PRIVATE_TRANSFER_COPY_PATTERNS
      pool_v1.payment_semantic_terminal.constants.PRIVATE_TRANSFER_COPY_LINKS
      pool_v1.payment_semantic_terminal.constants.PRIVATE_TRANSFER_ACTIVE_ROW_MASKS
  | pool_v1.payment_semantic_terminal.CompiledVariant.Withdrawal =>
    pool_v1.payment_semantic_terminal.copy_lane_for_registry openings h1_z
      selectors lambda chi
      pool_v1.payment_semantic_terminal.constants.WITHDRAWAL_COPY_PATTERNS
      pool_v1.payment_semantic_terminal.constants.WITHDRAWAL_COPY_LINKS
      pool_v1.payment_semantic_terminal.constants.WITHDRAWAL_ACTIVE_ROW_MASKS

end PoolV1CopyLaneBooleanGenerated
