import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk43

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_terminal_parts_compiled_tag73]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1513:0-1530:1
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_terminal_parts_compiled_tag73] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_terminal_parts_compiled_tag73"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_terminal_parts_compiled_tag73
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (claims : Array aspis_core.field.QM31 84#usize)
  (point : Array aspis_core.field.QM31 10#usize)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (theta : aspis_core.field.QM31)
  (zerocheck_point : Array aspis_core.field.QM31 10#usize)
  (mu : aspis_core.field.QM31) :
  Result (core.result.Result (aspis_core.field.QM31 × (Array
    aspis_core.field.QM31 16#usize) × (Array aspis_core.field.QM31 10#usize)
    × aspis_core.field.QM31)
    aspis_statement.state_only_terminal.StateOnlyTerminalError)
  := do
  let r ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_composition_parts_compiled_v3
      statement claims point lambda chi theta
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (composition, c1, mask_only, g, h1_z, copy_active) := val
    let q ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE copy_active
    let inactive_h1 ← aspis_core.field.QM31.mul q h1_z
    let q1 ←
      aspis_statement.atomic_state_only_terminal.atomic_equality_value
        zerocheck_point point
    let q2 ← aspis_core.field.QM31.mul q1 composition
    let q3 ← aspis_core.field.QM31.mul mu h1_z
    let q4 ← aspis_core.field.QM31.add q2 q3
    let q5 ← aspis_core.field.QM31.mul mu mu
    let q6 ← aspis_core.field.QM31.mul q5 inactive_h1
    let original ← aspis_core.field.QM31.add q4 q6
    ok (core.result.Result.Ok (original, c1, mask_only, g))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (aspis_core.field.QM31 × (Array aspis_core.field.QM31 16#usize) ×
      (Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
      (core.convert.FromSame
      aspis_statement.state_only_terminal.StateOnlyTerminalError) residual

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_tag73]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 1628:0-1638:41
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_tag73]
    Visibility: public -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_selected_masked_terminal_value_compiled_tag73"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_selected_masked_terminal_value_compiled_tag73
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (claims : Array aspis_core.field.QM31 84#usize)
  (point : Array aspis_core.field.QM31 10#usize)
  (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31)
  (theta : aspis_core.field.QM31)
  (zerocheck_point : Array aspis_core.field.QM31 10#usize)
  (mu : aspis_core.field.QM31) (eta : aspis_core.field.QM31) :
  Result (core.result.Result aspis_core.field.QM31
    aspis_statement.state_only_terminal.StateOnlyTerminalError)
  := do
  let r ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_terminal_parts_compiled_tag73
      statement claims point lambda chi theta zerocheck_point mu
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (original, c1, mask_only, g) := val
    let mask ←
      aspis_core.state_only_hiding.state_only_selected_mask_value c1 mask_only
        g point
    let q ← aspis_core.field.QM31.mul eta original
    let q1 ← aspis_core.field.QM31.add mask q
    ok (core.result.Result.Ok q1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.field.QM31 (core.convert.FromSame
      aspis_statement.state_only_terminal.StateOnlyTerminalError) residual

/-- [aspis_verifier::v6_verifier::terminal_claims::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_verifier::v6_verifier::terminal_claims::closure<'_0>}::call_mut]:
    Source: 'programs/aspis-verifier/src/v6_verifier.rs', lines 58:25-62:5 -/
def
  v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : v6_verifier.terminal_claims.closure) (tupled_args : Std.Usize) :
  Result (aspis_core.field.QM31 × v6_verifier.terminal_claims.closure)
  := do
  let row ← tupled_args / 28#usize
  let column ← tupled_args % 28#usize
  let a ← Array.index_usize c row
  let q ← Array.index_usize a column
  ok (q, c)

/-- [aspis_verifier::v6_verifier::terminal_claims::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_verifier::v6_verifier::terminal_claims::closure<'_0>}::call_once]:
    Source: 'programs/aspis-verifier/src/v6_verifier.rs', lines 58:25-62:5 -/
def
  v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c : v6_verifier.terminal_claims.closure) (i : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let (q, _) ←
    v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_verifier::v6_verifier::terminal_claims::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::QM31> for aspis_verifier::v6_verifier::terminal_claims::closure<'_0>}]
    Source: 'programs/aspis-verifier/src/v6_verifier.rs', lines 58:25-62:5 -/
@[reducible]
def
  v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce v6_verifier.terminal_claims.closure Std.Usize
  aspis_core.field.QM31 := {
  call_once :=
    v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_verifier::v6_verifier::terminal_claims::{impl core::ops::function::FnMut<(usize,), aspis_core::field::QM31> for aspis_verifier::v6_verifier::terminal_claims::closure<'_0>}]
    Source: 'programs/aspis-verifier/src/v6_verifier.rs', lines 58:25-62:5 -/
@[reducible]
def
  v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut v6_verifier.terminal_claims.closure Std.Usize
  aspis_core.field.QM31 := {
  FnOnceInst :=
    v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_verifier::v6_verifier::terminal_claims]:
    Source: 'programs/aspis-verifier/src/v6_verifier.rs', lines 52:0-63:1 -/
def v6_verifier.terminal_claims
  (view : aspis_core.v6_transcript.V6SemanticView) :
  Result (Array aspis_core.field.QM31 84#usize)
  := do
  core.array.from_fn 84#usize
    v6_verifier.terminal_claims.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    view.point_claims

/-- [aspis_verifier::v7_verifier::{impl core::convert::From<aspis_core::v6_transcript::V6TranscriptError> for aspis_verifier::v7_verifier::V7VerifyError}::from]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 59:4-61:5
    Visibility: public -/
def v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError.from
  (error : aspis_core.v6_transcript.V6TranscriptError) :
  Result v7_verifier.V7VerifyError
  := do
  ok (v7_verifier.V7VerifyError.Transcript error)

/-- Trait implementation: [aspis_verifier::v7_verifier::{impl core::convert::From<aspis_core::v6_transcript::V6TranscriptError> for aspis_verifier::v7_verifier::V7VerifyError}]
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 58:0-62:1 -/
@[reducible]
def v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError :
  core.convert.From v7_verifier.V7VerifyError
  aspis_core.v6_transcript.V6TranscriptError := {
  «from» :=
    v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError.from
}

/-- [aspis_verifier::v7_verifier::{impl core::convert::From<aspis_core::v6_onefold::V6WireError> for aspis_verifier::v7_verifier::V7VerifyError}::from]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 65:4-67:5
    Visibility: public -/
def v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError.from
  (error : aspis_core.v6_onefold.V6WireError) :
  Result v7_verifier.V7VerifyError
  := do
  ok (v7_verifier.V7VerifyError.Query error)

/-- Trait implementation: [aspis_verifier::v7_verifier::{impl core::convert::From<aspis_core::v6_onefold::V6WireError> for aspis_verifier::v7_verifier::V7VerifyError}]
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 64:0-68:1 -/
@[reducible]
def v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError :
  core.convert.From v7_verifier.V7VerifyError aspis_core.v6_onefold.V6WireError
  := {
  «from» := v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError.from
}

/-- [aspis_verifier::v7_verifier::terminal_matches::{impl core::ops::function::FnOnce<(aspis_core::field::QM31,), bool> for aspis_verifier::v7_verifier::terminal_matches::closure<'_0, '_1>}::call_once]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 88:15-88:57 -/
def
  v7_verifier.terminal_matches.closure.Insts.CoreOpsFunctionFnOnceTupleQM31Bool.call_once
  (c : v7_verifier.terminal_matches.closure)
  (tupled_args : aspis_core.field.QM31) :
  Result Bool
  := do
  aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq tupled_args
    c.terminal_claim

/-- Trait implementation: [aspis_verifier::v7_verifier::terminal_matches::{impl core::ops::function::FnOnce<(aspis_core::field::QM31,), bool> for aspis_verifier::v7_verifier::terminal_matches::closure<'_0, '_1>}]
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 88:15-88:57 -/
@[reducible]
def
  v7_verifier.terminal_matches.closure.Insts.CoreOpsFunctionFnOnceTupleQM31Bool
  : core.ops.function.FnOnce v7_verifier.terminal_matches.closure
  aspis_core.field.QM31 Bool := {
  call_once :=
    v7_verifier.terminal_matches.closure.Insts.CoreOpsFunctionFnOnceTupleQM31Bool.call_once
}


end V7Tag73CurrentHelpersOpaque
