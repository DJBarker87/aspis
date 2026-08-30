import V7Tag73CurrentHelpersOpaque.CircleTableSupport

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_circle_tables

def RATE512_CIRCLE_LOW8_WINDOW_chunk00 : Array (Array Std.U32 2#usize) 16#usize :=
  ⟨[
    circle_pair 1633461177#u32 574296567#u32,
    circle_pair 1242192167#u32 1322293366#u32,
    circle_pair 1139757936#u32 161139962#u32,
    circle_pair 2056541252#u32 1900478857#u32,
    circle_pair 1765678898#u32 2028236613#u32,
    circle_pair 1503715524#u32 748528002#u32,
    circle_pair 687167191#u32 1193781868#u32,
    circle_pair 1076514332#u32 1068664781#u32,
    circle_pair 2016807951#u32 234018695#u32,
    circle_pair 1210077794#u32 246102266#u32,
    circle_pair 1235766230#u32 338243230#u32,
    circle_pair 713314261#u32 425545952#u32,
    circle_pair 1300335129#u32 1837567123#u32,
    circle_pair 1032881673#u32 494228663#u32,
    circle_pair 342937346#u32 440901543#u32,
    circle_pair 346773666#u32 152947344#u32
  ], by rfl⟩

end staged_circle_tables
end V7Tag73CurrentHelpersOpaque
