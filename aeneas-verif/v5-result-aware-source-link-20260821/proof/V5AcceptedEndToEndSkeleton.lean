import V5AcceptedRelationPreparedAdapter
import V5AcceptedPostWorkSuccessors
import V5AcceptedTranscriptQueryBridge
import V5AcceptedOodMixProjection

/-!
# Evidence from one accepted released V5 spend

This file is the assembly point for the final accepted-execution theorem.  Its
first result packages only facts already obtained by inverting one successful
translated production call.  All witnesses are shared: none of the work,
query, FRI, or relation values can be chosen independently.

The final security theorem will be added here only after the remaining
source-to-model adapters derive their conclusions from this same package.
-/

namespace AspisV5AcceptedEndToEndSkeleton

open Aeneas Aeneas.Std Result
open AspisV5AcceptedCompositeExactEvidence
open AspisV5AcceptedEntrySourceBridge

abbrev AcceptedEntryParsed :=
  AspisV5AcceptedEntrySourceBridge.EntryParsed
abbrev AcceptedEntryQM31 :=
  AspisV5AcceptedEntrySourceBridge.EntryQM31
abbrev AcceptedEntryPreparedClaims :=
  AspisV5AcceptedEntrySourceBridge.EntryPreparedClaims
abbrev AcceptedEntryOpenings :=
  AspisV5AcceptedEntryFriPhaseBridge.EntryOpenings
abbrev AcceptedEntryFriSink :=
  AspisV5AcceptedEntryFriPhaseBridge.EntryFriSink

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Exact work, transcript-successor, FRI-call, and relation-call evidence from
one accepted production execution. -/
structure AcceptedCompositeDeterministicEvidence
    (accountData : Slice Std.U8)
    (parsed : AcceptedEntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : AcceptedEntryQM31)
    (verifiedPrefix : EntryVerifiedPrefix)
    (prefixTranscript : EntryTranscript)
    (verifiedTerminal : EntryVerifiedTerminal)
    (relationTranscript : EntryTranscript)
    (finalPolynomial : Array AcceptedEntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (alphas : Array AcceptedEntryQM31 4#usize)
    (friSum : AcceptedEntryQM31)
    (preparedClaims : AcceptedEntryPreparedClaims)
    (relationSum phaseSum : AcceptedEntryQM31)
    (openings : AcceptedEntryOpenings)
    (sink : AcceptedEntryFriSink)
    (relationOutput :
      V5RelationCallerGenerated.v5_relation_stress.VerifiedV5RelationStress) :
    Prop where
  exactExecution : AcceptedCompositeExactEvidence accountData parsed
    liveStatement statementDigest acceptedValue verifiedPrefix prefixTranscript
    verifiedTerminal relationTranscript finalPolynomial queries alphas friSum
    preparedClaims relationSum phaseSum openings sink
  postWork : AcceptedCompositePostWorkSuccessors parsed verifiedPrefix queries
  querySampler :
    AspisV5AcceptedTranscriptQueryBridge.AcceptedQuerySamplerEvidence
      parsed queries
  foldChallenges :
    AspisV5AcceptedTranscriptQueryBridge.AcceptedFoldChallengeProjection
      parsed alphas
  oodMixes :
    ∀ round : Fin 4, ∀ sample : Fin 2,
      AspisV5AcceptedOodMixProjection.AcceptedOodMixCall parsed round sample
  relationGate : AspisV5AcceptedRelationPreparedAdapter.AcceptedCallerRelationGate
    parsed finalPolynomial alphas
    verifiedPrefix.kappa verifiedPrefix.inactive_claim
    verifiedPrefix.round_challenges preparedClaims relationSum relationOutput

/-- A successful translated production call supplies all deterministic
same-run evidence currently available, without a source/model premise. -/
theorem accepted_composite_builds_deterministic_evidence
    (accountData : Slice Std.U8)
    (parsed : AcceptedEntryParsed)
    (liveStatement : EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : AcceptedEntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    ∃ verifiedPrefix prefixTranscript verifiedTerminal relationTranscript
        finalPolynomial queries alphas friSum preparedClaims relationSum
        phaseSum openings sink relationOutput,
      AcceptedCompositeDeterministicEvidence accountData parsed liveStatement
        statementDigest acceptedValue verifiedPrefix prefixTranscript
        verifiedTerminal relationTranscript finalPolynomial queries alphas
        friSum preparedClaims relationSum phaseSum openings sink
        relationOutput := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, openings, sink, relationOutput,
      exactExecution, relationGate⟩ :=
    AspisV5AcceptedRelationPreparedAdapter.accepted_composite_reaches_checked_relation_gate
      accountData parsed
      liveStatement statementDigest acceptedValue success
  let postWork :=
    accepted_composite_call_facts_prove_post_work_successors accountData parsed
      liveStatement statementDigest acceptedValue verifiedPrefix
      prefixTranscript verifiedTerminal relationTranscript finalPolynomial
      queries alphas friSum preparedClaims relationSum phaseSum
      exactExecution.compositeCalls
  let querySampler :=
    AspisV5AcceptedTranscriptQueryBridge.accepted_post_work_successors_build_exact_query_sampler
      parsed verifiedPrefix queries postWork
  let foldChallenges :=
    AspisV5AcceptedTranscriptQueryBridge.accepted_fold_successors_and_alpha_decode_are_same_values
      parsed alphas postWork.folds exactExecution.compositeCalls.alphaSuccess
  let oodMixes :=
    AspisV5AcceptedOodMixProjection.accepted_relation_success_has_eight_ood_mix_calls
      parsed prefixTranscript relationTranscript
      exactExecution.compositeCalls.relationSuccess
  exact ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
    relationTranscript, finalPolynomial, queries, alphas, friSum,
    preparedClaims, relationSum, phaseSum, openings, sink, relationOutput,
    { exactExecution := exactExecution
      postWork := postWork
      querySampler := querySampler
      foldChallenges := foldChallenges
      oodMixes := oodMixes
      relationGate := relationGate }⟩

#print axioms accepted_composite_builds_deterministic_evidence

end AspisV5AcceptedEndToEndSkeleton
