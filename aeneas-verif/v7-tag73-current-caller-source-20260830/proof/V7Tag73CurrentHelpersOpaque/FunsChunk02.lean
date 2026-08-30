import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk01
import V7Tag73CurrentHelpersOpaque.CircleTable_V6_CIRCLE_LOW6_WINDOW_Chunk03

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::circle_fri::V6_CIRCLE_LOW6_WINDOW]
    Source: '/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/target-normalized-r2/x86_64-unknown-linux-gnu/debug/build/aspis-core-4e5313882daeed0f/out/circle_tables.rs', lines 36284:0-36284:47
    Name pattern: [aspis_core::circle_fri::V6_CIRCLE_LOW6_WINDOW]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::circle_fri::V6_CIRCLE_LOW6_WINDOW"]
def aspis_core.circle_fri.V6_CIRCLE_LOW6_WINDOW
  : Array (Array Std.U32 2#usize) 64#usize :=
  staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk00) (staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk01)) (staged_circle_tables.append16 (staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk02) (staged_circle_tables.V6_CIRCLE_LOW6_WINDOW_chunk03))


end V7Tag73CurrentHelpersOpaque
