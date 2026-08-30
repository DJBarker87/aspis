import V7Tag73CurrentHelpersOpaque.AtomicPatternChunk04

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_atomic_patterns

def pattern05 :
    aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern :=
  {
        kinds := staged_atomic_patterns.a7,
        columns :=
          (Array.make 16#usize [
            8#u8, 9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8, 8#u8, 9#u8,
            10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8
            ]),
        scales := staged_atomic_patterns.a8,
        offsets := staged_atomic_patterns.a9
      }

end staged_atomic_patterns
end V7Tag73CurrentHelpersOpaque
