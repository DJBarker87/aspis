import Aeneas.Std
import V5TranscriptPrimitivesGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error
open V5TranscriptPrimitivesGenerated

namespace V5TranscriptPrimitivesGenerated

/-- Exact pure meaning of Rust `u32::is_power_of_two`.  The upstream Aeneas
    library provides the same definition for `usize`; this extraction needs
    the `u32` instance used by the production query sampler. -/
@[rust_fun "core::num::{u32}::is_power_of_two"]
def core.num.U32.is_power_of_two (value : Std.U32) : Result Bool :=
  ok value.val.isPowerOfTwo

end V5TranscriptPrimitivesGenerated
