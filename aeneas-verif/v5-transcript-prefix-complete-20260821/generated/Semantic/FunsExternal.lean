import Aeneas.Std
import Semantic.Types

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5SemanticUnchangedGenerated

def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
    (_left _right : aspis_core.field.QM31) : Result Bool :=
  ok true

def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 :=
  ok ()

def aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_ROUND_BYTES :
    Result Std.Usize :=
  ok 448#usize

def aspis_core.state_only_sumcheck.STATE_ONLY_SUMCHECK_BYTES :
    Result Std.Usize :=
  ok 4480#usize

def
  aspis_core.state_only_sumcheck.StateOnlySumcheckVerifyError.Insts.CoreConvertFromChallengeSampleExhausted.from
    (_error : aspis_core.transcript.ChallengeSampleExhausted) :
    Result aspis_core.state_only_sumcheck.StateOnlySumcheckVerifyError :=
  ok .ChallengeSampleExhausted

/-- Arithmetic is erased in this successful-path event projection. -/
def aspis_core.state_only_sumcheck.state_only_boundary_sum
    (_polynomial : Array aspis_core.field.QM31 28#usize) :
    Result aspis_core.field.QM31 :=
  ok ()

/-- Arithmetic is erased in this successful-path event projection. -/
def aspis_core.state_only_sumcheck.evaluate_state_only_polynomial
    (_polynomial : Array aspis_core.field.QM31 28#usize)
    (_challenge : aspis_core.field.QM31) : Result aspis_core.field.QM31 :=
  ok ()

/-- The decoder's rejection and field-value behavior is proved elsewhere; the
event projection needs only that an accepted 448-byte round continues. -/
def aspis_core.state_only_sumcheck.decode_state_only_polynomial
    (_round : Std.Usize) (_encoded : Slice Std.U8) :
    Result (core.result.Result (Array aspis_core.field.QM31 28#usize)
      aspis_core.state_only_sumcheck.StateOnlySumcheckVerifyError) :=
  ok (.Ok (Array.repeat 28#usize ()))

def aspis_core.transcript.Transcript.challenge_qm31
    (transcript : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok (), { transcript with events := transcript.events ++ [.squeeze] })

def aspis_core.transcript.Transcript.absorb
    (transcript : aspis_core.transcript.Transcript) (label : Std.U8)
    (payload : Slice Std.U8) : Result aspis_core.transcript.Transcript :=
  ok { transcript with
    events := transcript.events ++ [.absorb label payload.val] }

def aspis_core.transcript.label.M31_STATE_ONLY_ZEROCHECK_SUMCHECK :
    Result Std.U8 :=
  ok 29#u8

end V5SemanticUnchangedGenerated
