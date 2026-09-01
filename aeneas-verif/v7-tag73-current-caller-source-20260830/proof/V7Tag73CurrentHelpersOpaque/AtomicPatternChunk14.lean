import V7Tag73CurrentHelpersOpaque.AtomicPatternChunk13

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_atomic_patterns

def pattern14 :
    aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern :=
  {
        kinds :=
          (Array.make 16#usize [
            1#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ]),
        columns :=
          (Array.make 16#usize [
            0#u8, 8#u8, 9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8, 0#u8,
            0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
            ]),
        scales :=
          (Array.make 16#usize [
            0#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 1#u32, 0#u32,
            0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
            ]),
        offsets :=
          (Array.make 16#usize [
            1#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
            1051521018#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
            ])
      }

def patterns :
    Array aspis_statement.atomic_state_only_terminal.CompiledAtomicPattern 15#usize :=
  ⟨[
    pattern00,
    pattern01,
    pattern02,
    pattern03,
    pattern04,
    pattern05,
    pattern06,
    pattern07,
    pattern08,
    pattern09,
    pattern10,
    pattern11,
    pattern12,
    pattern13,
    pattern14
  ], by rfl⟩

end staged_atomic_patterns
end V7Tag73CurrentHelpersOpaque
