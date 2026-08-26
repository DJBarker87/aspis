import AspisFormal.K1.V7Tag73ConcreteRestorationClient
import AspisFormal.K1.V7Tag73OracleTableProvenance

/-!
# Duplicate-free concrete Tag-73 restoration clients

Replaying the same `(nodeId, verifierTransitionIndex)` twice is not a random
oracle bad event.  Once the first replay succeeds, its pair inputs have been
programmed, so the second attempt deterministically meets a defined input.

This module gives the K1.2--K1.5 extractor an indexed client language in which
every adaptive continuation is statically forbidden from repeating a request.
Erasure produces the existing executable `ConcreteRestorationClient`; the
request-path theorem proves `Nodup` for every possible reply path.  This does
not assert that distinct requests have distinct squeeze states or SHA inputs.
That remaining state/input provenance is exactly the ancestor-table case
classified by `no_pair_segment_lookup_conflict_is_in_entry_table`.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73UniqueRestorationRequests

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AtomicPairFork
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

#print axioms request_path_nodup_and_fresh_from_seen
#print axioms initially_unique_request_path_is_nodup
#print axioms node_local_no_pair_conflict_is_ancestor_entry

end AspisK1.V7Tag73UniqueRestorationRequests
