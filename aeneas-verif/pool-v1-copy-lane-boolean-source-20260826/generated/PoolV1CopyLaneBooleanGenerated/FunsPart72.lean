-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart71
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- Declaration-preserving elaboration split for generated WITHDRAWAL pattern 9. -/
def pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_09 :
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern :=
  {
      kinds :=
        (Array.make 16#usize [
          2#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns := pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_BASE_a10,
      scales :=
        (Array.make 16#usize [
          1#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
          0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
          ]),
      offsets := pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_BASE_a11
    }

end PoolV1CopyLaneBooleanGenerated
