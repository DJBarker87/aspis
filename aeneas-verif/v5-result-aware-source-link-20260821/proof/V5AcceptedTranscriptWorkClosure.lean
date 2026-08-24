import V5AcceptedSameRunRelationFriSnapshot
import V5AcceptedWorkExecutionProjection
import V5AcceptedPostWorkSuccessors
import V5AcceptedTranscriptQueryBridge
import V5AcceptedOodMixProjection
import AspisFormal.V5AcceptedExecutionDerivedQueries

/-!
# Transcript and work evidence from one accepted execution

This file packages the maintained transcript and positioned-work objects used
by the security reduction.  Their values come from one accepted composite
snapshot.  The package also retains the six exact generated grinding/absorb
calls, so the abstract work object is not detached from the production run
which supplied it.
-/

namespace AspisV5AcceptedTranscriptWorkClosure

open Aeneas Aeneas.Std Result
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedExecutionDerivedQueries
open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5NonceWorkAuthentication
open AspisV5RelationStressSourceBridge
open AspisV5TranscriptConnection

set_option autoImplicit false

abbrev AcceptedK := AspisV5FriAcceptedForestChecks.K

/-- The derived values used by the maintained reduction, fixed to the values
retained by one accepted production snapshot.  Fields which are not consumed
by `TranscriptExecutionProjection` are still populated deterministically from
the accepted prefix where available. -/
def acceptedDerivedValues
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData AcceptedK) :
    V5DerivedValues AcceptedK Unit where
  lambda := 0
  chi := 0
  theta := 0
  zerocheckPoint := fun _ => 0
  mu := 0
  eta := entryToK snapshot.verifiedPrefix.eta
  relationChallenge := fun coordinate =>
    entryToK snapshot.verifiedPrefix.round_challenges.val[coordinate.val]!
  gamma := entryToK snapshot.verifiedPrefix.gamma
  kappa := entryToK snapshot.verifiedPrefix.kappa
  oodPoint := fun _ _ => ()
  oodMix := data.relationTail.oodMixes
  foldChallenge := data.alphas
  queries := snapshot.queries.val.map UScalar.val

/-- The maintained driver result for exactly the input and derived values
selected by the accepted snapshot. -/
def acceptedDriverResult
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData AcceptedK) :
    V5TranscriptDriverResult AcceptedK Unit :=
  sourceShapedTranscriptDriver (snapshotTranscriptInput snapshot)
    (acceptedDerivedValues snapshot data)

/-- Positioned work inputs selected from the same accepted body. -/
def acceptedWorkInputs
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData AcceptedK) :
    PositionedWorkInputs WorkKind (SqueezeResult AcceptedK Unit) where
  stateBefore := fun kind => kind
  nonce := (snapshotTranscriptInput snapshot).nonce
  stateAfter := fun kind => kind
  nextResult
    | .batch => .field (acceptedDerivedValues snapshot data).gamma
    | .fold round =>
        .field ((acceptedDerivedValues snapshot data).foldChallenge round)
    | .finalQuery => .queries (acceptedDerivedValues snapshot data).queries

/-- Executable work operations at the six positions retained by the accepted
snapshot.  `grindingOK` records that this object is used only after the exact
generated calls in `AcceptedTranscriptWorkEvidence` have succeeded; the
cryptographic cost of finding their nonces remains a separate probability
assumption, as in the maintained security ledger. -/
def acceptedWorkFunctions
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData AcceptedK) :
    ExecutableWorkFunctions WorkKind (SqueezeResult AcceptedK Unit) where
  grindingOK := fun kind difficulty nonce =>
    difficulty = kind.difficulty ∧
      nonce = (snapshotTranscriptInput snapshot).nonce kind ∧
      AcceptedGeneratedExactSixWorkCalls parsed
  absorb := fun kind _ _ => kind
  executeNext := fun _ action =>
    match action with
    | .sampleGamma => .field (acceptedDerivedValues snapshot data).gamma
    | .sampleFoldAlpha round =>
        .field ((acceptedDerivedValues snapshot data).foldChallenge round)
    | .absorbSelectorThenSampleQ18 =>
        .queries (acceptedDerivedValues snapshot data).queries

/-- All transcript and work facts needed by the deterministic security
reduction, tied to the exact six generated work calls retained by the same
accepted snapshot. -/
structure AcceptedTranscriptWorkEvidence
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData AcceptedK)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks =
      some (snapshot.queries.val.map UScalar.val)) : Prop where
  exactGeneratedWork : AcceptedGeneratedExactSixWorkCalls parsed
  immediateSuccessors : AcceptedCompositePostWorkSuccessors parsed
    snapshot.verifiedPrefix snapshot.queries
  foldChallenges : AspisV5AcceptedTranscriptQueryBridge.AcceptedFoldChallengeProjection
    parsed snapshot.alphas
  oodMixCalls : ∀ round : Fin 4, ∀ sample : Fin 2,
    AspisV5AcceptedOodMixProjection.AcceptedOodMixCall parsed round sample
  transcriptProjection : TranscriptExecutionProjection
    (sourceMode9RelationInput data) (snapshotTranscriptInput snapshot)
    (acceptedDerivedValues snapshot data) (acceptedDriverResult snapshot data)
    (decodedQuerySet blocks (snapshot.queries.val.map UScalar.val) hdecode)
    (decodedQuerySchedule blocks (snapshot.queries.val.map UScalar.val) hdecode)
  workProjection : WorkExecutionProjection (snapshotTranscriptInput snapshot)
    (acceptedDerivedValues snapshot data) (acceptedWorkInputs snapshot data)
  workAccepted : ExecutableWorkAcceptance
    (acceptedWorkFunctions snapshot data) (acceptedWorkInputs snapshot data)

/-- Construct the complete maintained transcript/work evidence without a
caller-supplied projection or work-acceptance premise. -/
theorem accepted_snapshot_builds_transcript_work_evidence
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue)
    (data : SourceMode9CallerData AcceptedK)
    (blocks : List (FixedBytes 32))
    (hdecode : derive18Queries blocks =
      some (snapshot.queries.val.map UScalar.val)) :
    AcceptedTranscriptWorkEvidence snapshot data blocks hdecode := by
  refine {
    exactGeneratedWork := snapshot.evidence.exactWorkCalls
    immediateSuccessors := accepted_composite_call_facts_prove_post_work_successors
      accountData parsed liveStatement statementDigest acceptedValue
      snapshot.verifiedPrefix snapshot.prefixTranscript
      snapshot.verifiedTerminal snapshot.relationTranscript
      snapshot.finalPolynomial snapshot.queries snapshot.alphas snapshot.friSum
      snapshot.preparedClaims snapshot.relationSum snapshot.phaseSum
      snapshot.evidence.compositeCalls
    foldChallenges := ?_
    oodMixCalls := ?_
    transcriptProjection := ?_
    workProjection := ?_
    workAccepted := ?_
  }
  · exact
      AspisV5AcceptedTranscriptQueryBridge.accepted_fold_successors_and_alpha_decode_are_same_values
        parsed snapshot.alphas
        (accepted_composite_call_facts_prove_post_work_successors
          accountData parsed liveStatement statementDigest acceptedValue
          snapshot.verifiedPrefix snapshot.prefixTranscript
          snapshot.verifiedTerminal snapshot.relationTranscript
          snapshot.finalPolynomial snapshot.queries snapshot.alphas snapshot.friSum
          snapshot.preparedClaims snapshot.relationSum snapshot.phaseSum
          snapshot.evidence.compositeCalls).folds
        snapshot.evidence.compositeCalls.alphaSuccess
  · exact
      AspisV5AcceptedOodMixProjection.accepted_relation_success_has_eight_ood_mix_calls
        parsed snapshot.prefixTranscript snapshot.relationTranscript
        snapshot.evidence.compositeCalls.relationSuccess
  · constructor
    · rfl
    · intro round
      fin_cases round <;> rfl
    · intro round
      fin_cases round <;> rfl
    · intro round
      fin_cases round <;> rfl
    · exact decoded_query_positions_projection blocks
        (acceptedDerivedValues snapshot data) hdecode
    · rfl
  · constructor
    · rfl
    · rfl
    · intro round
      rfl
    · rfl
  · constructor
    intro kind
    exact ⟨⟨rfl, rfl, snapshot.evidence.exactWorkCalls⟩, rfl, by
      cases kind <;> rfl⟩

#print axioms accepted_snapshot_builds_transcript_work_evidence

end AspisV5AcceptedTranscriptWorkClosure
