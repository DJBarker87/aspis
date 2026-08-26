import AspisFormal.K1.V7Tag73ConcreteRestorationClient
import AspisFormal.K1.V7Tag73OracleTableProvenance

/-!
# Optional duplicate-free concrete Tag-73 restoration clients

Programming the same input twice into the *same mutated oracle value* is a
deterministic conflict, not a random-oracle bad event.  That observation does
not imply that repeated restoration requests are invalid: stored ancestor
nodes are immutable.  Repeating a root request recomputes the same clean root
prefix, while the first request's programmed entries live only in its newly
appended child.  Such repeated root forks are needed by ordinary multi-response
extraction.

This module gives the K1.2--K1.5 extractor an indexed client language in which
every adaptive continuation is statically forbidden from repeating a request.
Erasure produces the existing executable `ConcreteRestorationClient`; the
request-path theorem proves `Nodup` for every possible reply path.  It is an
optional restricted client language, not a K1.6 requirement and not the client
used to justify repeated extraction forks.  It also does not assert that
distinct requests have distinct squeeze states or SHA inputs.  The honest
criterion is local absence of both pair inputs in the concrete immutable
programming base; the residual ancestor-table case is classified by
`no_pair_segment_lookup_conflict_is_in_entry_table`.

The weaker and operationally appropriate scheduling condition is stated
separately below: root requests may repeat, while a child request may not fork
transition zero, because that transition is the replayed parent squeeze whose
pair is already present in the child's entry table.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73UniqueRestorationRequests

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73OracleTableProvenance

universe u

/-- An adaptive restoration client indexed by all requests already issued on
the current reply path.  The continuation receives the enlarged seen list,
so freshness is preserved under arbitrary replies. -/
inductive UniqueConcreteRestorationClient (Result : Type u) :
    List ConcreteRestorationRequest → Type u where
  | pure {seen : List ConcreteRestorationRequest} (result : Result) :
      UniqueConcreteRestorationClient Result seen
  | restore {seen : List ConcreteRestorationRequest}
      (request : ConcreteRestorationRequest)
      (fresh : request ∉ seen)
      (next : ConcreteRestorationReply →
        UniqueConcreteRestorationClient Result (request :: seen)) :
      UniqueConcreteRestorationClient Result seen

abbrev InitiallyUniqueConcreteRestorationClient (Result : Type u) :=
  UniqueConcreteRestorationClient Result []

/-- Proof-erasing interpretation into the existing operational client.  No
runtime behavior or reply branch is changed. -/
def UniqueConcreteRestorationClient.erase
    {seen : List ConcreteRestorationRequest} {Result : Type u} :
    UniqueConcreteRestorationClient Result seen →
      ConcreteRestorationClient Result
  | .pure result => .pure result
  | .restore request _fresh next =>
      .restore request (fun reply => (next reply).erase)

@[simp] theorem erase_pure
    {seen : List ConcreteRestorationRequest} {Result : Type u}
    (result : Result) :
    (UniqueConcreteRestorationClient.pure (seen := seen) result).erase =
      ConcreteRestorationClient.pure result := by
  rfl

@[simp] theorem erase_restore
    {seen : List ConcreteRestorationRequest} {Result : Type u}
    (request : ConcreteRestorationRequest) (fresh : request ∉ seen)
    (next : ConcreteRestorationReply →
      UniqueConcreteRestorationClient Result (request :: seen)) :
    (UniqueConcreteRestorationClient.restore request fresh next).erase =
      ConcreteRestorationClient.restore request
        (fun reply => (next reply).erase) := by
  rfl

/-- One concrete adaptive reply path through the indexed client. -/
inductive UniqueConcreteRestorationClient.RequestPath {Result : Type u} :
    {seen : List ConcreteRestorationRequest} →
      UniqueConcreteRestorationClient Result seen →
        List ConcreteRestorationRequest → Prop where
  | pure {seen : List ConcreteRestorationRequest} (result : Result) :
      RequestPath (.pure (seen := seen) result) []
  | restore
      {seen : List ConcreteRestorationRequest}
      {request : ConcreteRestorationRequest}
      {fresh : request ∉ seen}
      {next : ConcreteRestorationReply →
        UniqueConcreteRestorationClient Result (request :: seen)}
      (reply : ConcreteRestorationReply)
      {tail : List ConcreteRestorationRequest}
      (tailPath : RequestPath (next reply) tail) :
      RequestPath (.restore request fresh next) (request :: tail)

/-- Every request in a possible future path is fresh relative to the client's
current `seen` index, and the future path itself has no duplicates. -/
theorem request_path_nodup_and_fresh_from_seen
    {seen : List ConcreteRestorationRequest} {Result : Type u}
    {client : UniqueConcreteRestorationClient Result seen}
    {requests : List ConcreteRestorationRequest}
    (path : client.RequestPath requests) :
    requests.Nodup ∧ ∀ request ∈ requests, request ∉ seen := by
  induction path with
  | pure result => simp
  | @restore seen request fresh next reply tail tailPath ih =>
      rcases ih with ⟨tailNodup, tailFresh⟩
      have requestNotInTail : request ∉ tail := by
        intro member
        exact (tailFresh request member) (by simp)
      refine ⟨List.nodup_cons.mpr ⟨requestNotInTail, tailNodup⟩, ?_⟩
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · exact fresh
      · intro seenMember
        exact (tailFresh candidate tailMember) (by simp [seenMember])

/-- In particular, every adaptive path emitted from the empty seen index is
duplicate-free. -/
theorem initially_unique_request_path_is_nodup
    {Result : Type u}
    {client : InitiallyUniqueConcreteRestorationClient Result}
    {requests : List ConcreteRestorationRequest}
    (path : client.RequestPath requests) :
    requests.Nodup :=
  (request_path_nodup_and_fresh_from_seen path).1

/-- Segment-local no-pair scanning has one honest residual case even for a
first-time request: the lookup entry may have existed at machine entry.  This
corollary merely re-exports that operational classification next to the
duplicate-free client API; it does not assert that distinct requests have
fresh inputs. -/
theorem node_local_no_pair_conflict_is_ancestor_entry
    {Result : Type*} (controller : AdaptiveController)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (entryState : OracleState) (program : OracleMachine Result)
    (outputInput advanceInput input : ShaInput) (entry : TableEntry)
    (noPair : firstEitherInputOccurrence outputInput advanceInput
      (historySince entryState
        (runMachine controller limits actor fuel entryState program).oracle) =
          none)
    (isPairInput : input = outputInput ∨ input = advanceInput)
    (found : lookupEntry
      (runMachine controller limits actor fuel entryState program).oracle
        input = some entry) :
    entry ∈ entryState.table := by
  exact no_pair_segment_lookup_conflict_is_in_entry_table controller limits
    actor fuel entryState program outputInput advanceInput input entry noPair
      isPairInput found

/-! ## Why global request uniqueness is not a compiler hypothesis -/

/-- Appending a returned child cannot change preparation of a request into
the immutable root at index zero.  In particular the child table containing a
previously programmed pair is not substituted for the root programming base. -/
theorem appended_child_preserves_root_request_preparation
    {Statement Proof Payload : Type*}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (configuration : ConcreteRestorationConfiguration)
    (root child : ConcreteRestorationNode Statement Proof Payload)
    (transitionIndex : Nat) :
    let initial := initialRestorationAccumulatorFromRoot root
    let request : ConcreteRestorationRequest :=
      { nodeId := 0, verifierTransitionIndex := transitionIndex }
    prepareConcreteRestorationFromStartProgram startProgram configuration
        (initial.addNode child).2 request =
      prepareConcreteRestorationFromStartProgram startProgram configuration
        initial request := by
  dsimp only
  unfold prepareConcreteRestorationFromStartProgram
    ConcreteRestorationAccumulator.node?
    initialRestorationAccumulatorFromRoot
    ConcreteRestorationAccumulator.addNode
  rfl

/-- Oracle states are immutable values.  If programming a pair into one
ancestor base succeeds, two independent restorations that both restart from
that same unchanged base obtain the same successful programming result.  A
conflict arises only if a mutated descendant table is used as the next base. -/
theorem repeated_pair_programming_from_same_immutable_base_can_repeat
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (base afterBoth : OracleState) (outputInput advanceInput : ShaInput)
    (forkOutput forkAdvance : Digest256)
    (success : programConcretePair limits order base outputInput advanceInput
      forkOutput forkAdvance = .ready afterBoth) :
    programConcretePair limits order base outputInput advanceInput forkOutput
        forkAdvance = .ready afterBoth ∧
      programConcretePair limits order base outputInput advanceInput forkOutput
        forkAdvance = .ready afterBoth := by
  exact ⟨success, success⟩

/-! ## Minimal replay-base-safe request discipline -/

/-- Root nodes are immutable and may be forked repeatedly.  For a non-root
node, transition zero is the replayed parent squeeze and is therefore excluded
before pair programming.  This is strictly weaker than global request
uniqueness and permits all repeated root challenges needed by extraction. -/
def ReplayBaseSafeRequest (request : ConcreteRestorationRequest) : Prop :=
  request.nodeId = 0 ∨ request.verifierTransitionIndex ≠ 0

theorem root_restoration_request_is_replay_base_safe
    (transitionIndex : Nat) :
    ReplayBaseSafeRequest
      { nodeId := 0, verifierTransitionIndex := transitionIndex } := by
  exact Or.inl rfl

theorem replay_base_safe_child_excludes_transition_zero
    (request : ConcreteRestorationRequest)
    (safe : ReplayBaseSafeRequest request)
    (child : request.nodeId ≠ 0) :
    request.verifierTransitionIndex ≠ 0 := by
  exact safe.resolve_left child

/-- Structural certificate for an ordinary adaptive concrete client.  Every
future reply branch must retain the same local rule, but repeated root
requests and repeated request values in distinct branches remain allowed. -/
inductive ReplayBaseSafeConcreteClient {Result : Type u} :
    ConcreteRestorationClient Result → Prop where
  | pure (result : Result) :
      ReplayBaseSafeConcreteClient (.pure result)
  | restore (request : ConcreteRestorationRequest)
      (safe : ReplayBaseSafeRequest request)
      (next : ConcreteRestorationReply → ConcreteRestorationClient Result)
      (tails : ∀ reply, ReplayBaseSafeConcreteClient (next reply)) :
      ReplayBaseSafeConcreteClient (.restore request next)

/-- Every first request exposed by a structurally safe client satisfies the
minimal local scheduling rule. -/
theorem replay_base_safe_client_head
    {Result : Type u} (request : ConcreteRestorationRequest)
    (next : ConcreteRestorationReply → ConcreteRestorationClient Result)
    (safe : ReplayBaseSafeConcreteClient (.restore request next)) :
    ReplayBaseSafeRequest request := by
  cases safe
  assumption

#print axioms request_path_nodup_and_fresh_from_seen
#print axioms initially_unique_request_path_is_nodup
#print axioms node_local_no_pair_conflict_is_ancestor_entry
#print axioms appended_child_preserves_root_request_preparation
#print axioms repeated_pair_programming_from_same_immutable_base_can_repeat
#print axioms root_restoration_request_is_replay_base_safe
#print axioms replay_base_safe_child_excludes_transition_zero
#print axioms replay_base_safe_client_head

end AspisK1.V7Tag73UniqueRestorationRequests
