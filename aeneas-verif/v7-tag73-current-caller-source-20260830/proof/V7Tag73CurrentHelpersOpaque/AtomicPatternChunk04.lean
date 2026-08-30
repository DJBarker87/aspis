import V7Tag73CurrentHelpersOpaque.AtomicPatternChunk03

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_atomic_patterns

def pattern04 :
    aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern :=
  {
        kinds :=
          (Array.make 16#usize [
            2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ]),
        columns :=
          (Array.make 16#usize [
            8#u8, 9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 0#u8, 1#u8, 0#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ]),
        scales :=
          (Array.make 16#usize [
            1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 0#u32, 0#u32,
            0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
            ]),
        offsets := staged_atomic_patterns.a6
      }

end staged_atomic_patterns
end V7Tag73CurrentHelpersOpaque
