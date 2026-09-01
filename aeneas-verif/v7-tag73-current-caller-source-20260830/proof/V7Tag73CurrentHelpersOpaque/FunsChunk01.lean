import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk00
import V7Tag73CurrentHelpersOpaque.CircleTable_RATE512_CIRCLE_HIGH9_WINDOW_Chunk31

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW]
    Source: '/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/target-normalized-r2/x86_64-unknown-linux-gnu/debug/build/aspis-core-4e5313882daeed0f/out/circle_tables.rs', lines 36196:0-36196:54
    Name pattern: [aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW"]
def aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
  : Array (Array Std.U32 2#usize) 512#usize :=
  staged_circle_tables.append256 (staged_circle_tables.append128 (staged_circle_tables.append64 (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk00) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk01)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk02) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk03))) (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk04) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk05)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk06) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk07)))) (staged_circle_tables.append64 (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk08) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk09)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk10) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk11))) (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk12) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk13)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk14) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk15))))) (staged_circle_tables.append128 (staged_circle_tables.append64 (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk16) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk17)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk18) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk19))) (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk20) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk21)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk22) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk23)))) (staged_circle_tables.append64 (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk24) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk25)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk26) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk27))) (staged_circle_tables.append32 (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk28) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk29)) (staged_circle_tables.append16 (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk30) (staged_circle_tables.RATE512_CIRCLE_HIGH9_WINDOW_chunk31)))))


end V7Tag73CurrentHelpersOpaque
