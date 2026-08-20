import Aeneas.Std
import V5TranscriptTailGenerated.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

open V5TranscriptTailGenerated

namespace V5TranscriptTailGenerated

def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      ok (.Err mapped)

def Array.Insts.CoreConvertTryFromVecVec.try_from
    {T : Type} (_allocator : Type) (size : Std.Usize)
    (value : alloc.vec.Vec T) :
    Result (core.result.Result (Array T size) (alloc.vec.Vec T)) :=
  if hlength : value.val.length = size.val then
    ok (.Ok ⟨value.val, hlength⟩)
  else
    ok (.Err value)

def aspis_core.circle_hiding_prefix.PAYMENT_HIDING_QUERY_DRAW_LIMIT :
    Result Std.Usize :=
  ok 64#usize

def aspis_core.sumcheck.SUMCHECK_COEFFICIENTS : Result Std.Usize :=
  ok 7#usize

def aspis_core.transcript.label.M31_CIRCLE_FINAL_TENSOR_POLY :
    Result Std.U8 :=
  ok 19#u8

def aspis_core.transcript.label.M31_STATE_ONLY_QUERY_CANDIDATE :
    Result Std.U8 :=
  ok 44#u8

def aspis_core.transcript.Transcript.absorb
    (transcript : aspis_core.transcript.Transcript)
    (label : Std.U8) (payload : Slice Std.U8) :
    Result aspis_core.transcript.Transcript :=
  ok { transcript with
    events := transcript.events ++ [.absorb label payload.val] }

def aspis_core.transcript.Transcript.challenge_queries_without_replacement
    (transcript : aspis_core.transcript.Transcript)
    (count : Std.Usize) (bound : Std.U32) (drawLimit : Std.Usize) :
    Result ((core.result.Result (alloc.vec.Vec Std.U32)
      aspis_core.transcript.QuerySampleError) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok transcript.sampledQueries,
    { transcript with
      events := transcript.events ++ [.querySample count bound drawLimit] })

def v5_cu_probe.V5_CU_PROBE_QUERY_COUNT : Result Std.Usize :=
  ok 18#usize

def v5_cu_probe.QM31_BYTES : Result Std.Usize :=
  ok 16#usize

def v5_cu_probe.check_and_absorb_real_v5_final_nonce
    (transcript : aspis_core.transcript.Transcript) (nonce : Std.U64) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok (),
    { transcript with
      events := transcript.events ++ [.finalNonce nonce] })

def v5_cu_probe.decode_qm31
    (_bytes : Slice Std.U8) (index : Std.Usize) :
    Result (core.result.Result aspis_core.field.QM31
      solana_program_error.ProgramError) :=
  ok (.Ok index)

def v5_cu_probe.v5_query_selector_is_valid (selector : Std.U8) : Result Bool :=
  ok (decide (selector.val < 3))

end V5TranscriptTailGenerated
