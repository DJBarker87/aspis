-- The two source constants that Aeneas leaves external are closed here by
-- their exact deployed values.  No sampler behavior is postulated.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import V7Tag73ChallengeQm31.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open V7Tag73ChallengeQm31Generated

namespace V7Tag73ChallengeQm31Generated

/-- Exact deployed Mersenne prime `2^31 - 1`. -/
@[rust_const "aspis_core::field::P"]
def aspis_core.field.P : Result Std.U32 := ok 2147483647#u32

/-- Exact deployed zero representation for the transparent `M31 = u32`. -/
@[rust_const "aspis_core::field::{aspis_core::field::M31}::ZERO"]
def aspis_core.field.M31.ZERO : Result aspis_core.field.M31 := ok 0#u32

end V7Tag73ChallengeQm31Generated
