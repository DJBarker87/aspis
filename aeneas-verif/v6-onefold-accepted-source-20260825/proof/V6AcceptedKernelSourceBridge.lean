import V6AcceptedKernel.Funs

/-!
# Source-authentic result-flow bridge for the V6 accepted kernel

`V6AcceptedKernel.Funs` is the Charon/Aeneas translation of
`verify_v6_read_only_with_statement_digest_and_schedule`.  The opaque calls
below are deliberate interfaces: focused proofs cover the parser, transcript
driver, terminal evaluator, and authenticated query fold separately.  These
theorems establish that the translated production kernel has no alternative
success path around those interfaces and that its successful return contains
the transcript result verbatim.
-/

set_option autoImplicit false

namespace AspisV6AcceptedKernelSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V6AcceptedKernelGenerated

abbrev HashFn :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)
abbrev Wire := aspis_core.v6_onefold.V6OneFoldWire
abbrev Pubkey := solana_pubkey.Pubkey
abbrev Statement :=
  aspis_statement.atomic_statement.AtomicPaymentStatementV4
abbrev Transcript := aspis_core.v6_transcript.V6VerifiedTranscript
abbrev Verified := v6_verifier.VerifiedV6ReadOnly

noncomputable def transcriptCall
    (hash : HashFn) (wire : Wire)
    (programBytes releaseBinding statementDigest attemptBytes :
      Array Std.U8 32#usize)
    (selector : Std.U8) (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) :
    Result (core.result.Result Transcript
      aspis_core.v6_transcript.V6TranscriptError) :=
  aspis_core.v6_transcript.verify_v6_transcript_and_relation_prepared
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
    hash wire
    { program_id := programBytes
      release_binding := releaseBinding
      statement_digest := statementDigest
      attempt_id := attemptBytes }
    selector inactiveRowGroups inactiveGroupMasks checkPow statement
    (hash, wire)

/-- Successful opaque parser and transcript calls force the translated kernel
to return that exact transcript and its exact folded-query-sum projection. -/
theorem acceptedKernel_success_exact
    (hash : HashFn) (proof : Slice Std.U8)
    (c1FrontierNodes c2FrontierNodes : Std.Usize)
    (selector : Std.U8) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (wire : Wire) (programBytes attemptBytes : Array Std.U8 32#usize)
    (transcript : Transcript)
    (parserSuccess :
      aspis_core.v6_onefold.parse_v6_onefold_wire_deferred
          proof c1FrontierNodes c2FrontierNodes =
        .ok (.Ok wire))
    (programBytesExact :
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes)
    (attemptBytesExact :
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes)
    (transcriptSuccess :
      transcriptCall hash wire programBytes releaseBinding statementDigest
          attemptBytes selector inactiveRowGroups inactiveGroupMasks checkPow
          statement =
        .ok (.Ok transcript)) :
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule
        hash proof c1FrontierNodes c2FrontierNodes selector programId
        releaseBinding attemptId statement statementDigest inactiveRowGroups
        inactiveGroupMasks checkPow =
      .ok (.Ok {
        transcript := transcript
        folded_query_sum := transcript.folded_query_sum }) := by
  unfold
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule
  rw [parserSuccess]
  simp only [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [programBytesExact]
  simp only
  rw [attemptBytesExact]
  simp only
  unfold transcriptCall at transcriptSuccess
  rw [transcriptSuccess]

/-- A parser rejection cannot reach the transcript callback or a successful
kernel return; its exact wire error is wrapped as `V6VerifyError::Query`. -/
theorem acceptedKernel_parser_rejection_is_fail_closed
    (hash : HashFn) (proof : Slice Std.U8)
    (c1FrontierNodes c2FrontierNodes : Std.Usize)
    (selector : Std.U8) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (wireError : aspis_core.v6_onefold.V6WireError)
    (parserRejects :
      aspis_core.v6_onefold.parse_v6_onefold_wire_deferred
          proof c1FrontierNodes c2FrontierNodes =
        .ok (.Err wireError)) :
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule
        hash proof c1FrontierNodes c2FrontierNodes selector programId
        releaseBinding attemptId statement statementDigest inactiveRowGroups
        inactiveGroupMasks checkPow =
      .ok (.Err (.Query wireError)) := by
  simp [v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule,
    parserRejects, Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    v6_verifier.V6VerifyError.Insts.CoreConvertFromV6WireError.from]

/-- Once parsing succeeds, an exact transcript rejection is propagated as
`V6VerifyError::Transcript`; the wrapper cannot reinterpret it as success. -/
theorem acceptedKernel_transcript_rejection_is_fail_closed
    (hash : HashFn) (proof : Slice Std.U8)
    (c1FrontierNodes c2FrontierNodes : Std.Usize)
    (selector : Std.U8) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (wire : Wire) (programBytes attemptBytes : Array Std.U8 32#usize)
    (transcriptError : aspis_core.v6_transcript.V6TranscriptError)
    (parserSuccess :
      aspis_core.v6_onefold.parse_v6_onefold_wire_deferred
          proof c1FrontierNodes c2FrontierNodes =
        .ok (.Ok wire))
    (programBytesExact :
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes)
    (attemptBytesExact :
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes)
    (transcriptRejects :
      transcriptCall hash wire programBytes releaseBinding statementDigest
          attemptBytes selector inactiveRowGroups inactiveGroupMasks checkPow
          statement =
        .ok (.Err transcriptError)) :
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule
        hash proof c1FrontierNodes c2FrontierNodes selector programId
        releaseBinding attemptId statement statementDigest inactiveRowGroups
        inactiveGroupMasks checkPow =
      .ok (.Err (.Transcript transcriptError)) := by
  unfold
    v6_verifier.verify_v6_read_only_with_statement_digest_and_schedule
  rw [parserSuccess]
  simp only [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [programBytesExact]
  simp only
  rw [attemptBytesExact]
  simp only
  unfold transcriptCall at transcriptRejects
  rw [transcriptRejects]
  simp [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    v6_verifier.V6VerifyError.Insts.CoreConvertFromV6TranscriptError.from]

#print axioms acceptedKernel_success_exact
#print axioms acceptedKernel_parser_rejection_is_fail_closed
#print axioms acceptedKernel_transcript_rejection_is_fail_closed

end AspisV6AcceptedKernelSourceBridge
