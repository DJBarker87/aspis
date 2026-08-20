import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import V5PrefixProgramHelpersGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5PrefixProgramHelpersGenerated

def aspis_core.transcript.label.M31_CIRCLE_ROUND_ROOT : Result Std.U8 :=
  ok 12#u8

def aspis_core.transcript.label.M31_CIRCLE_C2_ROOT : Result Std.U8 :=
  ok 13#u8

def aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE : Result Std.U8 :=
  ok 28#u8

def aspis_core.transcript.Transcript.absorb
    (transcript : aspis_core.transcript.Transcript) (label : Std.U8)
    (payload : Slice Std.U8) : Result aspis_core.transcript.Transcript :=
  ok { transcript with
    events := transcript.events ++ [.absorb label payload.val] }

def aspis_core.transcript.Transcript.grinding_ok
    (transcript : aspis_core.transcript.Transcript) (nonce : Std.U64)
    (bits : Std.U8) : Result Bool :=
  ok (transcript.workValid nonce bits)

end V5PrefixProgramHelpersGenerated
