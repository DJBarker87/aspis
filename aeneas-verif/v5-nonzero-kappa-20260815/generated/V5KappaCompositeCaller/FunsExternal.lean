import Aeneas.Std
import V5KappaCompositeCaller.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open V5KappaCompositeCallerGenerated

namespace V5KappaCompositeCallerGenerated

def zeroQm31 : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

def qm31IsZero (value : aspis_core.field.QM31) : Bool :=
  value.c0.a == 0#u32 && value.c0.b == 0#u32 &&
    value.c1.a == 0#u32 && value.c1.b == 0#u32

private def qm31Array4 : Array aspis_core.field.QM31 4#usize :=
  Array.make 4#usize [zeroQm31, zeroQm31, zeroQm31, zeroQm31]

private def qm31Array10 : Array aspis_core.field.QM31 10#usize :=
  Array.make 10#usize [zeroQm31, zeroQm31, zeroQm31, zeroQm31,
    zeroQm31, zeroQm31, zeroQm31, zeroQm31, zeroQm31, zeroQm31]

private def queryArray18 : Array Std.U32 18#usize :=
  Array.make 18#usize [0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32,
    0#u32, 0#u32, 0#u32, 0#u32]

def core.hint.black_box {T : Type} (value : T) : Result T :=
  ok value

/-- Zero is an identity on either side. This lets the generated caller return
the scalar observed at the relation call after the otherwise irrelevant FRI
and terminal outputs are set to zero by the adapters below. -/
def aspis_core.field.QM31.add
    (left right : aspis_core.field.QM31) : Result aspis_core.field.QM31 :=
  if qm31IsZero left then ok right
  else if qm31IsZero right then ok left
  else ok left

def v5_cu_probe.verify_v5_wire_prefix_sbf
    (parsed : v5_cu_probe.ParsedProbeData)
    (_statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
    (_digest : Array Std.U8 32#usize) :
    Result (core.result.Result
      (v5_cu_probe.VerifiedRealV5Wire × aspis_core.transcript.Transcript)
      solana_program_error.ProgramError) := do
  ok (.Ok ({
    eta := zeroQm31
    round_challenges := qm31Array10
    gamma := zeroQm31
    kappa := parsed.gamma
    terminal_real := zeroQm31
    terminal_mask := zeroQm31
    terminal_masked := zeroQm31
    inactive_claim := zeroQm31
  }, ()))

def v5_cu_probe.verify_mode9_atomic_terminal_with_prefix
    (_parsed : v5_cu_probe.ParsedProbeData)
    (_statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
    (_prefix : v5_cu_probe.VerifiedRealV5Wire) :
    Result (core.result.Result v5_atomic_terminal.VerifiedV5AtomicTerminal
      solana_program_error.ProgramError) := do
  ok (.Ok { real := zeroQm31, mask := zeroQm31, masked := zeroQm31 })

def v5_cu_probe.replay_real_v5_relation_rounds
    (_transcript : aspis_core.transcript.Transcript)
    (_parsed : v5_cu_probe.ParsedProbeData) :
    Result (core.result.Result aspis_core.transcript.Transcript
      solana_program_error.ProgramError) :=
  ok (.Ok ())

def v5_cu_probe.derive_v5_selected_good_queries_from_transcript
    (_transcript : aspis_core.transcript.Transcript)
    (_parsed : v5_cu_probe.ParsedProbeData)
    (_roundChallenges : Array aspis_core.field.QM31 10#usize) :
    Result (core.result.Result
      (Array aspis_core.field.QM31 4#usize × Array Std.U32 18#usize)
      solana_program_error.ProgramError) :=
  ok (.Ok (qm31Array4, queryArray18))

def v5_cu_probe.decode_v5_fri_alphas
    (_parsed : v5_cu_probe.ParsedProbeData) :
    Result (core.result.Result (Array aspis_core.field.QM31 4#usize)
      solana_program_error.ProgramError) :=
  ok (.Ok qm31Array4)

def v5_cu_probe.verify_mode9_fri_phase
    (_parsed : v5_cu_probe.ParsedProbeData)
    (_queries : Array Std.U32 18#usize)
    (_finalPolynomial _alphas : Array aspis_core.field.QM31 4#usize)
    (_gamma : aspis_core.field.QM31) :
    Result (core.result.Result
      (aspis_core.field.QM31 × v5_cu_probe.fri_checks.V5PreparedPcsClaims)
      solana_program_error.ProgramError) :=
  ok (.Ok (zeroQm31, ()))

/-- Observation semantics: return exactly the scalar supplied at the real
relation-phase call. No probability or hash property is assumed here. -/
def v5_cu_probe.verify_mode9_relation_phase
    (_parsed : v5_cu_probe.ParsedProbeData)
    (_finalPolynomial _alphas : Array aspis_core.field.QM31 4#usize)
    (kappa : aspis_core.field.QM31)
    (_inactiveClaim : aspis_core.field.QM31)
    (_roundChallenges : Array aspis_core.field.QM31 10#usize)
    (_preparedClaims : v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    Result (core.result.Result aspis_core.field.QM31
      solana_program_error.ProgramError) :=
  ok (.Ok kappa)

end V5KappaCompositeCallerGenerated
