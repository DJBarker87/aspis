import Aeneas.Std
import Zero.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5ZeroUnchangedGenerated

def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Std.Usize} (array : Array T N) :
    Result ((core.slice.iter.IterMut T) ×
      (core.slice.iter.IterMut T → Array T N)) :=
  ok ({ slice := Array.to_slice array },
    fun iter => Array.from_slice array iter.slice)

def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 :=
  ok ()

def aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUNDS :
    Result Std.Usize :=
  ok 10#usize

def aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_DEGREE :
    Result Std.Usize :=
  ok 27#usize

def aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_COEFFICIENTS :
    Result Std.Usize :=
  ok 28#usize

def aspis_core.state_only_sumcheck.STATE_ONLY_CONSTRAINT_REGISTRY_VERSION :
    Result Std.U8 :=
  ok 1#u8

def aspis_core.state_only_sumcheck.STATE_ONLY_RANDOMIZED_CONSTRAINT_LANES :
    Result Std.U8 :=
  ok 29#u8

def aspis_core.state_only_sumcheck.STATE_ONLY_SEMANTIC_SOURCE_LANES :
    Result Std.U16 :=
  ok 95#u16

def aspis_core.state_only_sumcheck.STATE_ONLY_COPY_LINKS : Result Std.U16 :=
  ok 102#u16

def aspis_core.state_only_sumcheck.STATE_ONLY_COPY_TUPLE_WIDTH : Result Std.U8 :=
  ok 17#u8

def aspis_core.state_only_sumcheck.STATE_ONLY_LAYOUT_FINGERPRINT :
    Result Std.U64 :=
  ok 1305398393059615024#u64

def aspis_core.state_only_sumcheck.STATE_ONLY_HIDING_FACTOR_FINGERPRINT :
    Result Std.U64 :=
  ok 1326066350596418299#u64

def aspis_core.transcript.Transcript.challenge_qm31
    (transcript : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted) ×
      aspis_core.transcript.Transcript) :=
  let nextTranscript :=
    { transcript with events := transcript.events ++ [.squeeze] }
  ok (.Ok (), nextTranscript)

def aspis_core.transcript.Transcript.absorb
    (transcript : aspis_core.transcript.Transcript) (label : Std.U8)
    (payload : Slice Std.U8) : Result aspis_core.transcript.Transcript :=
  ok { transcript with
    events := transcript.events ++ [.absorb label payload.val] }

def aspis_core.transcript.label.M31_STATE_ONLY_HELPER_SUM : Result Std.U8 :=
  ok 33#u8

def aspis_core.transcript.label.M31_STATE_ONLY_CONSTRAINT_REGISTRY :
    Result Std.U8 :=
  ok 32#u8

end V5ZeroUnchangedGenerated
