import V5AcceptedRemainingWorkBridge

/-!
# Immediate transcript successors of accepted work checks

This file packages facts derived from one successful extracted production
call.  The batch work check is followed by the gamma challenge, each fold
work check is followed by the alpha challenge used for that round, and the
final work check is followed by the selector absorb and the exact accepted
query draw.
-/

namespace AspisV5AcceptedEntrySourceBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Aeneas Aeneas.Std Result ControlFlow Error

structure AcceptedCompositePostWorkSuccessors
    (parsed : EntryParsed)
    (verifiedPrefix : EntryVerifiedPrefix)
    (queries : Array Std.U32 18#usize) : Prop where
  requiredWork : AcceptedSixRequiredWork parsed
  batch : AcceptedBatchChallengeSuccessor parsed verifiedPrefix
  folds : AcceptedFourFoldChallengeSuccessors parsed
  finalQueries : AcceptedFinalQuerySuccessor parsed queries

theorem accepted_composite_call_facts_prove_post_work_successors
    (terminalBoundary : EntryTerminalBoundary)
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (verifiedPrefix : EntryVerifiedPrefix)
    (prefixTranscript : EntryTranscript)
    (verifiedTerminal : EntryVerifiedTerminal)
    (relationTranscript : EntryTranscript)
    (finalPolynomial : Array EntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (alphas : Array EntryQM31 4#usize)
    (friSum : EntryQM31)
    (preparedClaims : EntryPreparedClaims)
    (relationSum phaseSum : EntryQM31)
    (facts : AcceptedCompositeCallFacts terminalBoundary accountData parsed liveStatement
      statementDigest acceptedValue verifiedPrefix prefixTranscript
      verifiedTerminal relationTranscript finalPolynomial queries alphas friSum
      preparedClaims relationSum phaseSum) :
    AcceptedCompositePostWorkSuccessors parsed verifiedPrefix queries := by
  exact {
    requiredWork := accepted_call_facts_prove_six_work terminalBoundary accountData parsed
      liveStatement statementDigest acceptedValue verifiedPrefix
      prefixTranscript verifiedTerminal relationTranscript finalPolynomial
      queries alphas friSum preparedClaims relationSum phaseSum facts
    batch := accepted_prefix_has_batch_challenge_successor parsed liveStatement
      statementDigest V5AcceptedEntryGenerated.verify.sbf_hashv verifiedPrefix
      prefixTranscript facts.prefixSuccess
    folds := relation_success_has_four_fold_successors parsed prefixTranscript
      relationTranscript facts.relationSuccess
    finalQueries := selected_query_success_has_final_successor
      relationTranscript parsed verifiedPrefix.round_challenges finalPolynomial
      queries facts.querySuccess
  }

theorem accepted_composite_proves_post_work_successors
    (terminalBoundary : EntryTerminalBoundary)
    (accountData : Slice Std.U8) (parsed : EntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          terminalBoundary accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    ∃ verifiedPrefix prefixTranscript verifiedTerminal relationTranscript
        finalPolynomial queries alphas friSum preparedClaims relationSum phaseSum,
      AcceptedCompositeCallFacts terminalBoundary accountData parsed liveStatement statementDigest
        acceptedValue verifiedPrefix prefixTranscript verifiedTerminal
        relationTranscript finalPolynomial queries alphas friSum preparedClaims
        relationSum phaseSum ∧
      AcceptedCompositePostWorkSuccessors parsed verifiedPrefix queries := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, facts⟩ :=
    accepted_composite_builds_call_chain terminalBoundary accountData parsed liveStatement
      statementDigest acceptedValue success
  exact ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
    relationTranscript, finalPolynomial, queries, alphas, friSum,
    preparedClaims, relationSum, phaseSum, facts,
    accepted_composite_call_facts_prove_post_work_successors terminalBoundary accountData parsed
      liveStatement statementDigest acceptedValue verifiedPrefix
      prefixTranscript verifiedTerminal relationTranscript finalPolynomial
      queries alphas friSum preparedClaims relationSum phaseSum facts⟩

#print axioms accepted_composite_call_facts_prove_post_work_successors
#print axioms accepted_composite_proves_post_work_successors

end AspisV5AcceptedEntrySourceBridge
