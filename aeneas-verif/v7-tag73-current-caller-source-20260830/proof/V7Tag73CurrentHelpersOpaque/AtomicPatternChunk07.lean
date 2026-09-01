import V7Tag73CurrentHelpersOpaque.AtomicPatternChunk06

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_atomic_patterns

def pattern07 :
    aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern :=
  {
        kinds := staged_atomic_patterns.a13,
        columns :=
          (Array.make 16#usize [
            0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 10#u8,
            11#u8, 12#u8, 13#u8, 0#u8, 1#u8
            ]),
        scales := staged_atomic_patterns.a14,
        offsets := staged_atomic_patterns.a15
      }

end staged_atomic_patterns
end V7Tag73CurrentHelpersOpaque
