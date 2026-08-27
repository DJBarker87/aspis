-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart62
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- Declaration-preserving elaboration split for generated WITHDRAWAL pattern 0. -/
def pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_00 :
  pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentPattern :=
  {
      kinds := pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_BASE_a,
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 10#u8,
          11#u8, 12#u8, 13#u8, 14#u8, 15#u8
          ]),
      scales := pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_BASE_a1,
      offsets := pool_v1.payment_semantic_terminal.constants.generated_split.WITHDRAWAL_COPY_PATTERN_BASE_a2
    }

end PoolV1CopyLaneBooleanGenerated
