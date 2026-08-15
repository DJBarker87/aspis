import Aeneas.Std
import V5KappaRelationCaller.Types

open Aeneas Aeneas.Std Result ControlFlow Error

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open V5KappaRelationCallerGenerated

namespace V5KappaRelationCallerGenerated

def core.result.Result.map_err
    {T E F O : Type} (inst : core.ops.function.FnOnce O E F) :
    core.result.Result T E → O → Result (core.result.Result T F)
  | .Ok value, _ => ok (.Ok value)
  | .Err error, closure => do
      let mapped ← inst.call_once closure error
      ok (.Err mapped)

def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
    (self other : aspis_core.field.QM31) : Result Bool := do
  ok (self.c0.a == other.c0.a && self.c0.b == other.c0.b &&
    self.c1.a == other.c1.a && self.c1.b == other.c1.b)

def packKappa (value : aspis_core.field.QM31) :
    aspis_core.sumcheck.WeightAccumulator :=
  (value.c0.a, value.c0.b, value.c1.a, value.c1.b)

def unpackKappa (value : aspis_core.sumcheck.WeightAccumulator) :
    aspis_core.field.QM31 :=
  { c0 := { a := value.1, b := value.2.1 },
    c1 := { a := value.2.2.1, b := value.2.2.2 } }

private def array4 (value : aspis_core.field.QM31) :
    Array aspis_core.field.QM31 4#usize :=
  Array.make 4#usize [value, value, value, value]

private def array10 (value : aspis_core.field.QM31) :
    Array aspis_core.field.QM31 10#usize :=
  Array.make 10#usize [value, value, value, value, value,
    value, value, value, value, value]

/-- Observation semantics for the opaque production helper: reject every
variant except the exact four-claim compact path, and retain every limb of its
`kappa` argument in `weights`. -/
def v5_cu_probe.prepare_relation_base_with_kappa_prepared
    (_parsed : v5_cu_probe.ParsedProbeData)
    (variant : v5_cu_probe.RelationVariant)
    (kappa inactiveClaim : aspis_core.field.QM31)
    (_preparedClaims : v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    Result (core.result.Result
      (v5_cu_probe.PreparedRelation ×
        Array aspis_core.field.QM31 10#usize × aspis_core.field.QM31)
      solana_program_error.ProgramError) := do
  match variant with
  | .FourClaimsCompact =>
      ok (.Ok (
        { weights := packKappa kappa,
          relation_value := inactiveClaim,
          alphas := array4 kappa,
          final_values := array4 kappa,
          extra_work := () },
        array10 kappa,
        kappa))
  | _ => ok (.Err solana_program_error.ProgramError.InvalidArgument)

def v5_cu_probe.CompactBTerminalWeights.new
    (_point : Array aspis_core.field.QM31 10#usize)
    (_scale : aspis_core.field.QM31) :
    Result v5_cu_probe.CompactBTerminalWeights :=
  ok ()

def
    v5_cu_probe.CompactBTerminalWeights.Insts.Aspis_verifier_kappa_caller_extractionV5_relation_stressV5RelationStressAdditive.fold
    (_self : v5_cu_probe.CompactBTerminalWeights)
    (_alpha : aspis_core.field.QM31) :
    Result v5_cu_probe.CompactBTerminalWeights :=
  ok ()

def
    v5_cu_probe.CompactBTerminalWeights.Insts.Aspis_verifier_kappa_caller_extractionV5_relation_stressV5RelationStressAdditive.dot
    (_self : v5_cu_probe.CompactBTerminalWeights)
    (_values : Array aspis_core.field.QM31 4#usize) :
    Result aspis_core.field.QM31 :=
  ok { c0 := { a := 0#u32, b := 0#u32 },
       c1 := { a := 0#u32, b := 0#u32 } }

/-- The second observation adapter returns the scalar stored by preparation.
It otherwise preserves the caller's `alphas`, allowing the final equality
check to succeed when the theorem supplies the same array. -/
def v5_relation_stress.verify_v5_relation_stress_with_additive
    {A : Type} (_inst : v5_relation_stress.V5RelationStressAdditive A)
    (weights : aspis_core.sumcheck.WeightAccumulator)
    (_relationValue : aspis_core.field.QM31)
    (alphas : Array aspis_core.field.QM31 4#usize)
    (_wire : Array Std.U8 928#usize) (_extra : A) :
    Result (core.result.Result v5_relation_stress.VerifiedV5RelationStress
      v5_relation_stress.V5RelationStressError) := do
  ok (.Ok {
    final_coefficients := alphas,
    terminal_claim := unpackKappa weights })

end V5KappaRelationCallerGenerated
