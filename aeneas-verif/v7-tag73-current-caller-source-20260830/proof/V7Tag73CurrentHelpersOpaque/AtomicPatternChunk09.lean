import V7Tag73CurrentHelpersOpaque.AtomicPatternChunk08

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_atomic_patterns

def pattern09 :
    aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern :=
  {
        kinds :=
          (Array.make 16#usize [
            2#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ]),
        columns := staged_atomic_patterns.a17,
        scales :=
          (Array.make 16#usize [
            1#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
            0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
            ]),
        offsets := staged_atomic_patterns.a18
      }

end staged_atomic_patterns
end V7Tag73CurrentHelpersOpaque
