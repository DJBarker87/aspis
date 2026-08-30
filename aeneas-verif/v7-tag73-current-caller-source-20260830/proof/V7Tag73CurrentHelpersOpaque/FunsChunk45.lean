import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk44

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_verifier::v7_verifier::terminal_matches]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 76:0-89:1 -/
def v7_verifier.terminal_matches
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (view : aspis_core.v6_transcript.V6SemanticView) :
  Result Bool
  := do
  let a ← v6_verifier.terminal_claims view
  let r ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_selected_masked_terminal_value_compiled_tag73
      statement a view.point view.lambda view.chi view.batching.theta
      view.batching.zerocheck_point view.batching.mu view.eta
  core.result.Result.is_ok_and
    v7_verifier.terminal_matches.closure.Insts.CoreOpsFunctionFnOnceTupleQM31Bool
    r view

/-- [aspis_verifier::v7_verifier::authenticate_and_fold_queries]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 192:0-204:1 -/
def v7_verifier.authenticate_and_fold_queries
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
  (view : aspis_core.v6_transcript.V6QueryBatchView) :
  Result (core.result.Result
    aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
    aspis_core.v6_onefold.V6WireError)
  := do
  let r ← aspis_core.v6_onefold.prepare_v6_onefold_coordinates view.queries
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      aspis_core.v7_onefold.verify_and_gamma_combine_v7_openings hash wire
        view.queries view.gamma_powers
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a ←
        aspis_core.v6_onefold.fold_v6_onefold_queries val1 val view.alpha0
      ok (core.result.Result.Ok { values := a, line_x := val.line_x })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
        (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
      (core.convert.FromSame aspis_core.v6_onefold.V6WireError) residual

/-- [aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::{impl core::ops::function::FnOnce<(&'_ aspis_core::v6_transcript::V6QueryBatchView<'_>,), core::result::Result<aspis_core::v6_query_batch::V6AuthenticatedQueryBatch, aspis_core::v6_onefold::V6WireError>> for aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::closure#1<'_0, '_1, '_2>}::call_once]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 281:8-281:63 -/
def
  v7_verifier.verify_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError.call_once
  (c : v7_verifier.verify_v7_read_only_with_statement_digest.closure_1)
  (tupled_args : aspis_core.v6_transcript.V6QueryBatchView) :
  Result (core.result.Result
    aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
    aspis_core.v6_onefold.V6WireError)
  := do
  let (f, vcofw) := c
  v7_verifier.authenticate_and_fold_queries f vcofw tupled_args

/-- Trait implementation: [aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::{impl core::ops::function::FnOnce<(&'_ aspis_core::v6_transcript::V6QueryBatchView<'_>,), core::result::Result<aspis_core::v6_query_batch::V6AuthenticatedQueryBatch, aspis_core::v6_onefold::V6WireError>> for aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::closure#1<'_0, '_1, '_2>}]
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 281:8-281:63 -/
@[reducible]
def
  v7_verifier.verify_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
  : core.ops.function.FnOnce
  v7_verifier.verify_v7_read_only_with_statement_digest.closure_1
  aspis_core.v6_transcript.V6QueryBatchView (core.result.Result
  aspis_core.v6_query_batch.V6AuthenticatedQueryBatch
  aspis_core.v6_onefold.V6WireError) := {
  call_once :=
    v7_verifier.verify_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError.call_once
}

/-- [aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::{impl core::ops::function::FnOnce<(&'_ aspis_core::v6_transcript::V6SemanticView<'_>,), bool> for aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::closure<'_0>}::call_once]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 280:8-280:48 -/
def
  v7_verifier.verify_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool.call_once
  (c : v7_verifier.verify_v7_read_only_with_statement_digest.closure)
  (tupled_args : aspis_core.v6_transcript.V6SemanticView) :
  Result Bool
  := do
  v7_verifier.terminal_matches c tupled_args

/-- Trait implementation: [aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::{impl core::ops::function::FnOnce<(&'_ aspis_core::v6_transcript::V6SemanticView<'_>,), bool> for aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest::closure<'_0>}]
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 280:8-280:48 -/
@[reducible]
def
  v7_verifier.verify_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
  : core.ops.function.FnOnce
  v7_verifier.verify_v7_read_only_with_statement_digest.closure
  aspis_core.v6_transcript.V6SemanticView Bool := {
  call_once :=
    v7_verifier.verify_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool.call_once
}

/-- [aspis_verifier::v7_verifier::verify_v7_read_only_with_statement_digest]:
    Source: 'programs/aspis-verifier/src/v7_verifier.rs', lines 253:0-288:1
    Visibility: public -/
def v7_verifier.verify_v7_read_only_with_statement_digest
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (proof : Slice Std.U8) (frontier_nodes : Std.Usize)
  (program_id : solana_pubkey.Pubkey) (release_binding : Array Std.U8 32#usize)
  (attempt_id : solana_pubkey.Pubkey)
  (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
  (statement_digest : Array Std.U8 32#usize) (check_pow : Bool) :
  Result (core.result.Result v7_verifier.VerifiedV7ReadOnly
    v7_verifier.V7VerifyError)
  := do
  let inactive_row_groups ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_owned_v3
  let inactive_group_masks ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_owned_v3
  let r ←
    aspis_core.v7_onefold.V7CompactOneFoldWire.parse_deferred_canonicality
      proof frontier_nodes
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue vcofw =>
    let a ← solana_pubkey.Pubkey.to_bytes program_id
    let a1 ← solana_pubkey.Pubkey.to_bytes attempt_id
    let s ← Aeneas.Std.lift (Array.to_slice inactive_group_masks)
    let r1 ←
      aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared
        v7_verifier.verify_v7_read_only_with_statement_digest.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
        v7_verifier.verify_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
        hash vcofw
        { program_id := a, release_binding, statement_digest, attempt_id := a1
        } inactive_row_groups s check_pow statement (hash, vcofw)
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (core.result.Result.Ok
        { transcript := val, folded_query_sum := val.folded_query_sum })
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        v7_verifier.VerifiedV7ReadOnly
        v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError
        residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      v7_verifier.VerifiedV7ReadOnly
      v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError residual


end V7Tag73CurrentHelpersOpaque
