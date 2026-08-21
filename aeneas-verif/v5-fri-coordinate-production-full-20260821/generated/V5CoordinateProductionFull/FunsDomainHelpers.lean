-- Deterministic low-memory proof view of the recorded Aeneas output.
import V5CoordinateProductionFull.FunsLowWindow

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section

namespace V5CoordinateSelectedProductionSource

/-- [aspis_core_parent_helper_extraction::circle_fri::bit_reverse_index]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 665:0-677:1
    Visibility: public -/
def circle_fri.bit_reverse_index
    (index : Std.Usize) (log_size : Std.U32) :
    Result (core.result.Result Std.Usize circle_fri.CircleFriError) := do
  let o ← core.num.Usize.checked_shl 1#usize log_size
  let r ←
    core.option.Option.ok_or o
      circle_fri.CircleFriError.InvalidBitReverseLength
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue value =>
    if index >= value then
      ok (.Err circle_fri.CircleFriError.BitReverseIndexOutOfRange)
    else if log_size = 0#u32 then
      ok (.Ok 0#usize)
    else
      let reversed ← core.num.Usize.reverse_bits index
      let shift ← core.num.Usize.BITS - log_size
      let result ← reversed >>> shift
      ok (.Ok result)
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Std.Usize (core.convert.FromSame circle_fri.CircleFriError) residual

/-- [aspis_core_parent_helper_extraction::circle_fri::half_odds_step_index]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 502:0-504:1 -/
def circle_fri.half_odds_step_index
    (log_size : Std.U32) : Result Std.U64 := do
  let shift ← params.CIRCLE_LOG_ORDER - log_size
  1#u64 <<< shift

/-- [aspis_core_parent_helper_extraction::circle_fri::half_odds_initial_index]:
    Source: '../../../crates/aspis-core/src/circle_fri.rs', lines 497:0-499:1 -/
def circle_fri.half_odds_initial_index
    (log_size : Std.U32) : Result Std.U64 := do
  let adjusted ← log_size + 2#u32
  let shift ← params.CIRCLE_LOG_ORDER - adjusted
  1#u64 <<< shift

end V5CoordinateSelectedProductionSource
