import V7AcceptedKernel.Funs

/-!
# Source-translation bridge for the V7 extraction-only accepted kernel

`V7AcceptedKernel.Funs` is generated from the schedule-explicit extraction
wrapper recorded in `overlay/v7-aeneas-extraction-only.patch`.  It is not a
translation of the byte-identical deployed root: equivalence of the wrapper
to that root remains the explicitly named source-review boundary described in
the bundle README.  These theorems only establish the wrapper's exact result
flow across its opaque parser and transcript interfaces.
-/

set_option autoImplicit false

namespace AspisV7AcceptedKernelSourceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7AcceptedKernelGenerated

abbrev HashFn :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)
abbrev Wire := aspis_core.v7_onefold.V7CompactOneFoldWire
abbrev Pubkey := solana_pubkey.Pubkey
abbrev Statement :=
  aspis_statement.atomic_statement.AtomicPaymentStatementV4
abbrev Transcript := aspis_core.v6_transcript.V6VerifiedTranscript
abbrev Verified := v7_verifier.VerifiedV7ReadOnly

noncomputable def transcriptCall
    (hash : HashFn) (wire : Wire)
    (programBytes releaseBinding statementDigest attemptBytes :
      Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (statement : Statement) :
    Result (core.result.Result Transcript
      aspis_core.v6_transcript.V6TranscriptError) :=
  aspis_core.v6_transcript.verify_v7_compact_transcript_and_relation_prepared
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule.closure.Insts.CoreOpsFunctionFnOnceTupleSharedV6SemanticViewBool
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError
    hash wire
    { program_id := programBytes
      release_binding := releaseBinding
      statement_digest := statementDigest
      attempt_id := attemptBytes }
    inactiveRowGroups inactiveGroupMasks checkPow statement (hash, wire)

/-- Successful opaque parser and transcript calls force the translated
extraction wrapper to return that exact transcript and folded-query sum. -/
theorem acceptedKernel_success_exact
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (wire : Wire) (programBytes attemptBytes : Array Std.U8 32#usize)
    (transcript : Transcript)
    (parserSuccess :
      aspis_core.v7_onefold.parse_v7_compact_onefold_wire_deferred
          proof frontierNodes = .ok (.Ok wire))
    (programBytesExact :
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes)
    (attemptBytesExact :
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes)
    (transcriptSuccess :
      transcriptCall hash wire programBytes releaseBinding statementDigest
          attemptBytes inactiveRowGroups inactiveGroupMasks checkPow statement =
        .ok (.Ok transcript)) :
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule
        hash proof frontierNodes programId releaseBinding attemptId statement
        statementDigest inactiveRowGroups inactiveGroupMasks checkPow =
      .ok (.Ok {
        transcript := transcript
        folded_query_sum := transcript.folded_query_sum }) := by
  unfold
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule
  rw [parserSuccess]
  simp only [Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [programBytesExact]
  simp only
  rw [attemptBytesExact]
  simp only
  unfold transcriptCall at transcriptSuccess
  rw [transcriptSuccess]

/-- An exact parser rejection is propagated as `V7VerifyError::Query`; the
translated extraction wrapper has no alternate success path. -/
theorem acceptedKernel_parser_rejection_is_fail_closed
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (wireError : aspis_core.v6_onefold.V6WireError)
    (parserRejects :
      aspis_core.v7_onefold.parse_v7_compact_onefold_wire_deferred
          proof frontierNodes = .ok (.Err wireError)) :
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule
        hash proof frontierNodes programId releaseBinding attemptId statement
        statementDigest inactiveRowGroups inactiveGroupMasks checkPow =
      .ok (.Err (.Query wireError)) := by
  simp [v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule,
    parserRejects, Bind.bind, Aeneas.Std.bind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    v7_verifier.V7VerifyError.Insts.CoreConvertFromV6WireError.from]

/-- Once parsing succeeds, an exact transcript rejection is propagated as
`V7VerifyError::Transcript`; it cannot be reinterpreted as acceptance. -/
theorem acceptedKernel_transcript_rejection_is_fail_closed
    (hash : HashFn) (proof : Slice Std.U8)
    (frontierNodes : Std.Usize) (programId : Pubkey)
    (releaseBinding : Array Std.U8 32#usize) (attemptId : Pubkey)
    (statement : Statement) (statementDigest : Array Std.U8 32#usize)
    (inactiveRowGroups : Array Std.U8 64#usize)
    (inactiveGroupMasks : Slice Std.U16) (checkPow : Bool)
    (wire : Wire) (programBytes attemptBytes : Array Std.U8 32#usize)
    (transcriptError : aspis_core.v6_transcript.V6TranscriptError)
    (parserSuccess :
      aspis_core.v7_onefold.parse_v7_compact_onefold_wire_deferred
          proof frontierNodes = .ok (.Ok wire))
    (programBytesExact :
      solana_pubkey.Pubkey.to_bytes programId = .ok programBytes)
    (attemptBytesExact :
      solana_pubkey.Pubkey.to_bytes attemptId = .ok attemptBytes)
    (transcriptRejects :
      transcriptCall hash wire programBytes releaseBinding statementDigest
          attemptBytes inactiveRowGroups inactiveGroupMasks checkPow statement =
        .ok (.Err transcriptError)) :
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule
        hash proof frontierNodes programId releaseBinding attemptId statement
        statementDigest inactiveRowGroups inactiveGroupMasks checkPow =
      .ok (.Err (.Transcript transcriptError)) := by
  unfold
    v7_verifier.verify_v7_read_only_with_statement_digest_and_schedule
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
    v7_verifier.V7VerifyError.Insts.CoreConvertFromV6TranscriptError.from]

#print axioms acceptedKernel_success_exact
#print axioms acceptedKernel_parser_rejection_is_fail_closed
#print axioms acceptedKernel_transcript_rejection_is_fail_closed

end AspisV7AcceptedKernelSourceBridge
