import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import V5PrefixMaskHelperGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5PrefixMaskHelperGenerated

def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      ok (.Err mapped)

/-- Exact behavior of `QM31::write_le_bytes` on the mutable output slice. -/
def aspis_core.field.QM31.write_le_bytes
    (value : aspis_core.field.QM31) (output : Slice Std.U8) :
    Result (Slice Std.U8) :=
  ok (output.setSlice! 0 value.val)

def aspis_core.transcript.Transcript.challenge_nonzero_qm31
    (transcript : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted) ×
      aspis_core.transcript.Transcript) :=
  let nextTranscript :=
    { transcript with events := transcript.events ++ [.squeezeNonzero] }
  match transcript.next with
  | some value => ok (.Ok value, nextTranscript)
  | none => ok (.Err (), nextTranscript)

def aspis_core.transcript.Transcript.absorb
    (transcript : aspis_core.transcript.Transcript) (label : Std.U8)
    (payload : Slice Std.U8) : Result aspis_core.transcript.Transcript :=
  ok { transcript with
    events := transcript.events ++ [.absorb label payload.val] }

def aspis_core.transcript.label.M31_STATE_ONLY_HIDING_MASK_CLAIM :
    Result Std.U8 :=
  ok 31#u8

end V5PrefixMaskHelperGenerated
