-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart107
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::constants::PRIVATE_TRANSFER_ACTIVE_ROW_MASKS]
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs', lines 11:0-11:359 -/
@[irreducible]
def
  pool_v1.payment_semantic_terminal.constants.PRIVATE_TRANSFER_ACTIVE_ROW_MASKS
  : Array Std.U16 64#usize :=
  Array.make 64#usize [
    6144#u16, 6144#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 4097#u16, 6144#u16, 4097#u16, 2048#u16, 6145#u16,
    1#u16, 2048#u16, 6145#u16, 1#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16,
    0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16,
    0#u16, 255#u16, 255#u16, 255#u16, 255#u16, 255#u16, 213#u16, 0#u16, 0#u16,
    0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16, 0#u16
    ]

end PoolV1CopyLaneBooleanGenerated
