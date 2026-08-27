-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart101
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- Declaration-preserving elaboration split for generated PRIVATE_TRANSFER pattern 8. -/
def pool_v1.payment_semantic_terminal.constants.generated_split.PRIVATE_TRANSFER_COPY_PATTERN_08 :
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern :=
  {
      kinds :=
        (Array.make 16#usize [
          2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          8#u8, 9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      scales :=
        (Array.make 16#usize [
          1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 0#u32, 0#u32,
          0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
          ]),
      offsets :=
        (Array.make 16#usize [
          0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 1051521018#u32,
          0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
          ])
    }

end PoolV1CopyLaneBooleanGenerated
