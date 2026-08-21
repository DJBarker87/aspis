import Aeneas.Std
import V5TranscriptRelationHelper.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

open V5TranscriptRelationGenerated

namespace V5TranscriptRelationGenerated

def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      ok (.Err mapped)

def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
    (_left _right : aspis_core.field.QM31) : Result Bool :=
  ok true

def aspis_core.sumcheck.SUMCHECK_COEFFICIENTS : Result Std.Usize :=
  ok 7#usize

def aspis_core.transcript.label.M31_CIRCLE_OOD_VALUE : Result Std.U8 :=
  ok 16#u8

def aspis_core.transcript.label.M31_LINE_OOD_VALUE : Result Std.U8 :=
  ok 17#u8

private def pushEvent
    (transcript : aspis_core.transcript.Transcript)
    (event : RelationTranscriptEvent)
    (exactEvent : ExactRelationTranscriptEvent) :
    aspis_core.transcript.Transcript :=
  { events := transcript.events ++ [event]
    exactEvents := transcript.exactEvents ++ [exactEvent] }

def exactByteAt (bytes : List Std.U8) (index : Nat) : Std.U8 :=
  bytes[index]?.getD 0#u8

def exactBytesAt (width : Nat) (bytes : List Std.U8)
    (start : Nat) : List Std.U8 :=
  bytes.slice start (start + width)

def exact32At (bytes : List Std.U8) (start : Nat) :
    Array Std.U8 32#usize :=
  Array.make 32#usize
    (List.ofFn fun index : Fin 32 => exactByteAt bytes (start + index.val)) (by
      simp)

def aspis_core.transcript.Transcript.challenge_qm31
    (transcript : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.ChallengeSampleExhausted) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok [], pushEvent transcript .squeezeQm31 .squeezeQm31)

def aspis_core.transcript.Transcript.challenge_ood_qm31
    (transcript : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.field.QM31
      aspis_core.transcript.OodSampleError) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok [], pushEvent transcript .lineOodPoint .lineOodPoint)

def aspis_core.transcript.Transcript.challenge_secure_circle_point
    (transcript : aspis_core.transcript.Transcript) :
    Result ((core.result.Result aspis_core.circle.SecureCirclePoint
      aspis_core.transcript.CirclePointSampleError) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok { x := [], y := [] },
    pushEvent transcript .secureCirclePoint .secureCirclePoint)

def v5_cu_probe.QM31_BYTES : Result Std.Usize :=
  ok 16#usize

def v5_cu_probe.stress_qm31
    (parsed : v5_cu_probe.ParsedProbeData) (offset : Std.Usize) :
    Result (core.result.Result aspis_core.field.QM31
      solana_program_error.ProgramError) :=
  ok (.Ok (exactBytesAt 16 parsed.v5_relation_stress.val offset.val))

def v5_cu_probe.absorb_real_v5_ood
    (transcript : aspis_core.transcript.Transcript) (label : Std.U8)
    (round sample : Std.Usize) (value : aspis_core.field.QM31) :
    Result aspis_core.transcript.Transcript :=
  ok (pushEvent transcript (.absorbOod label.val round.val sample.val)
    (.absorbOod label.val round.val sample.val value))

def v5_cu_probe.absorb_real_v5_relation_sumcheck
    (transcript : aspis_core.transcript.Transcript) (round : Std.Usize)
    (polynomial : Slice Std.U8) : Result aspis_core.transcript.Transcript :=
  ok (pushEvent transcript (.relationSumcheck round.val)
    (.relationSumcheck round.val polynomial.val))

def v5_cu_probe.check_and_absorb_real_v5_fold_nonce
    (transcript : aspis_core.transcript.Transcript) (round : Std.Usize)
    (nonce : Std.U64) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) ×
      aspis_core.transcript.Transcript) :=
  ok (.Ok (), pushEvent transcript (.foldWork round.val nonce.val)
    (.foldWork round.val nonce.val))

def v5_cu_probe.verify_v5_relation_final_zero_tail
    (_relationFinal : Slice Std.U8) :
    Result (core.result.Result Unit solana_program_error.ProgramError) :=
  ok (.Ok ())

def v5_cu_probe.absorb_real_v5_round_root
    (transcript : aspis_core.transcript.Transcript) (rootIndex : Std.Usize)
    (root salt : Array Std.U8 32#usize) :
    Result aspis_core.transcript.Transcript :=
  ok (pushEvent transcript (.laterRoot (rootIndex.val - 1))
    (.laterRoot rootIndex.val root.val salt.val))

def v5_cu_probe.v5_public_fs_salt
    (wirePrefix : Slice Std.U8) (index : Std.Usize) :
    Result (Array Std.U8 32#usize) :=
  ok (exact32At wirePrefix.val (5863 + index.val * 32))

def v5_cu_probe.decode_qm31
    (_bytes : Slice Std.U8) (_index : Std.Usize) :
    Result (core.result.Result aspis_core.field.QM31
      solana_program_error.ProgramError) :=
  ok (.Ok [])

end V5TranscriptRelationGenerated
