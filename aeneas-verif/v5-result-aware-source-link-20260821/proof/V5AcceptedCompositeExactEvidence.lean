import V5AcceptedWorkExecutionProjection
import V5AcceptedEntryFriPhaseBridge

/-!
# One accepted composite call exposes its exact work and FRI calls

This file packages facts already proved by inversion of the same generated
production composite body.  The witnesses below are shared: the polynomial,
queries, alphas, gamma, prepared claims, and FRI sum in the exact FRI call are
the values passed by that accepted composite execution.  The six exact work
calls come from the same top-level success.
-/

namespace AspisV5AcceptedCompositeExactEvidence

open Aeneas Aeneas.Std Result
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedEntryFriPhaseBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

structure AcceptedCompositeExactEvidence
    (accountData : Slice Std.U8)
    (parsed : AspisV5AcceptedEntrySourceBridge.EntryParsed)
    (liveStatement : AspisV5AcceptedEntrySourceBridge.EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : AspisV5AcceptedEntrySourceBridge.EntryQM31)
    (verifiedPrefix : AspisV5AcceptedEntrySourceBridge.EntryVerifiedPrefix)
    (prefixTranscript : AspisV5AcceptedEntrySourceBridge.EntryTranscript)
    (verifiedTerminal : AspisV5AcceptedEntrySourceBridge.EntryVerifiedTerminal)
    (relationTranscript : AspisV5AcceptedEntrySourceBridge.EntryTranscript)
    (finalPolynomial :
      Array AspisV5AcceptedEntrySourceBridge.EntryQM31 4#usize)
    (queries : Array Std.U32 18#usize)
    (alphas : Array AspisV5AcceptedEntrySourceBridge.EntryQM31 4#usize)
    (friSum : AspisV5AcceptedEntrySourceBridge.EntryQM31)
    (preparedClaims : AspisV5AcceptedEntrySourceBridge.EntryPreparedClaims)
    (relationSum phaseSum : AspisV5AcceptedEntrySourceBridge.EntryQM31)
    (openings : AspisV5AcceptedEntryFriPhaseBridge.EntryOpenings)
    (sink : AspisV5AcceptedEntryFriPhaseBridge.EntryFriSink) : Prop where
  compositeCalls : AcceptedCompositeCallFacts accountData parsed liveStatement
    statementDigest acceptedValue verifiedPrefix prefixTranscript
    verifiedTerminal relationTranscript finalPolynomial queries alphas friSum
    preparedClaims relationSum phaseSum
  exactWorkCalls : AcceptedGeneratedExactSixWorkCalls parsed
  exactFriCalls : AcceptedFriPhaseCallFacts parsed queries finalPolynomial
    alphas verifiedPrefix.gamma friSum preparedClaims openings sink

def AcceptedCompositeExactEvidenceExists
    (accountData : Slice Std.U8)
    (parsed : AspisV5AcceptedEntrySourceBridge.EntryParsed)
    (liveStatement : AspisV5AcceptedEntrySourceBridge.EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : AspisV5AcceptedEntrySourceBridge.EntryQM31) : Prop :=
  ∃ verifiedPrefix prefixTranscript verifiedTerminal relationTranscript
      finalPolynomial queries alphas friSum preparedClaims relationSum phaseSum
      openings sink,
    AcceptedCompositeExactEvidence accountData parsed liveStatement
      statementDigest acceptedValue verifiedPrefix prefixTranscript
      verifiedTerminal relationTranscript finalPolynomial queries alphas
      friSum preparedClaims relationSum phaseSum openings sink

/-- One successful generated composite call supplies the complete shared call
evidence.  No separately supplied parser, work, FRI, or value-flow premise is
needed. -/
theorem accepted_composite_builds_exact_evidence
    (accountData : Slice Std.U8)
    (parsed : AspisV5AcceptedEntrySourceBridge.EntryParsed)
    (liveStatement : AspisV5AcceptedEntrySourceBridge.EntryStatement)
    (statementDigest : Array Std.U8 32#usize)
    (acceptedValue : AspisV5AcceptedEntrySourceBridge.EntryQM31)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.verify_mode9_composite_with_live_statement
          accountData parsed liveStatement statementDigest =
        .ok (.Ok acceptedValue)) :
    AcceptedCompositeExactEvidenceExists accountData parsed liveStatement
      statementDigest acceptedValue := by
  obtain ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
      relationTranscript, finalPolynomial, queries, alphas, friSum,
      preparedClaims, relationSum, phaseSum, compositeFacts⟩ :=
    accepted_composite_builds_call_chain accountData parsed liveStatement
      statementDigest acceptedValue success
  obtain ⟨openings, sink, friFacts⟩ :=
    accepted_fri_phase_builds_exact_call parsed queries finalPolynomial alphas
      verifiedPrefix.gamma friSum preparedClaims compositeFacts.friSuccess
  refine ⟨verifiedPrefix, prefixTranscript, verifiedTerminal,
    relationTranscript, finalPolynomial, queries, alphas, friSum,
    preparedClaims, relationSum, phaseSum, openings, sink, ?_⟩
  exact {
    compositeCalls := compositeFacts
    exactWorkCalls := accepted_composite_proves_exact_six_work_calls
      accountData parsed liveStatement statementDigest acceptedValue success
    exactFriCalls := friFacts
  }

#print axioms accepted_composite_builds_exact_evidence

end AspisV5AcceptedCompositeExactEvidence
