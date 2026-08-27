import AspisFormal.Pool.V7PairAppendAfterstateCorrect

/-!
# Pair Pool caller live-snapshot applicability gate

The merged-C1 verifier relation is parameterized by an exact live pair-tree
snapshot.  The one-terminal Pool caller may use its proof-carried ASJA
afterstate only if the snapshot supplied to that verifier is exactly the
snapshot decoded from the locked Pool account in the same transaction.

This file separates two facts which must not be conflated:

* the current Pool-side afterstate gate checks capacity, index progression and
  the canonical empty value in inactive frontier slots; and
* the missing caller gate must bind the verifier's proof snapshot to the exact
  account-derived source root and frontier.

The first gate is intentionally independent of the source root and frontier.
The countermodel below kernel-checks that it cannot imply the second.  The
positive capstone then states the smallest sufficient bridge: equality of the
proof-bound and account-derived live states transports the already-proved
exact pair transition to the locked Pool source.

This is an applicability/source-interface theorem.  It does not assert that
the current production Rust caller supplies the equality; it currently does
not pass the 800-byte `ASPLIVE1` snapshot (or an authenticated digest of it) to
the verifier CPI.
-/

set_option autoImplicit false

namespace AspisPool.V7PairCallerLiveSnapshotGate

open AspisPool.V7PairLeafOccupancy
open AspisPool.V7PairAppendAfterstateCorrect

/-- Pool-side checks which can be made from the locked cursor and returned
afterstate alone.  `inactive` abstracts the deployed per-level empty-root
check.  It depends on the candidate frontier and candidate index, but not on
the source root or source frontier. -/
def CurrentPoolAfterstateGate
    {Digest : Type}
    (capacity : Nat)
    (inactive : Nat → PairFrontier Digest → Prop)
    (source : PairLiveState Digest)
    (payload : PairAfterstatePayload Digest) : Prop :=
  source.nextPairIndex < capacity ∧
    payload.nextPairIndex = source.nextPairIndex + 1 ∧
    inactive payload.nextPairIndex payload.nextFrontier

/-- Equal cursors make the current Pool afterstate gate observationally
identical even when the two source roots or frontiers differ. -/
theorem current_pool_gate_ignores_source_root_and_frontier
    {Digest : Type}
    (capacity : Nat)
    (inactive : Nat → PairFrontier Digest → Prop)
    (left right : PairLiveState Digest)
    (payload : PairAfterstatePayload Digest)
    (sameIndex : left.nextPairIndex = right.nextPairIndex) :
    CurrentPoolAfterstateGate capacity inactive left payload ↔
      CurrentPoolAfterstateGate capacity inactive right payload := by
  simp only [CurrentPoolAfterstateGate, sameIndex]

/-- Concrete witness that cursor/afterstate-only checking cannot bind the live
root.  The same payload passes against two distinct source snapshots. -/
theorem current_pool_gate_does_not_determine_live_snapshot :
    ∃ (left right : PairLiveState Bool)
      (payload : PairAfterstatePayload Bool),
      left ≠ right ∧
      CurrentPoolAfterstateGate 2 (fun _ _ => True) left payload ∧
      CurrentPoolAfterstateGate 2 (fun _ _ => True) right payload := by
  let left : PairLiveState Bool :=
    { sequence := 0, nextPairIndex := 0, root := false, frontier := [] }
  let right : PairLiveState Bool :=
    { sequence := 0, nextPairIndex := 0, root := true, frontier := [] }
  let payload : PairAfterstatePayload Bool :=
    { nextPairIndex := 1, nextRoot := false, nextFrontier := [] }
  refine ⟨left, right, payload, ?_, ?_, ?_⟩
  · intro equal
    have rootEqual := congrArg (fun state : PairLiveState Bool => state.root) equal
    simp [left, right] at rootEqual
  · simp [CurrentPoolAfterstateGate, left, payload]
  · simp [CurrentPoolAfterstateGate, right, payload]

/-- Exact source/runtime obligation at the immediate verifier-CPI seam.  The
account-derived value must be constructed from the same locked Pool account
whose state is later written.  `proofBound` is the exact snapshot absorbed
before the C1 root by the selected verifier. -/
structure AuthenticatedLiveSnapshotBinding (Digest : Type) where
  accountDerived : PairLiveState Digest
  proofBound : PairLiveState Digest
  exact : proofBound = accountDerived

/-- Once the immediate verifier result is tied to the locked snapshot, its
exact transition theorem applies to that locked source without changing any
cryptographic premise. -/
theorem bound_snapshot_transports_exact_transition
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaf : PairLeaf K)
    (binding : AuthenticatedLiveSnapshotBinding Digest)
    (result : PairLiveState Digest)
    (proofExact : ExactPairAppendTransition parent emptyLeaf compressPair depth
      leaf binding.proofBound result) :
    ExactPairAppendTransition parent emptyLeaf compressPair depth leaf
      binding.accountDerived result := by
  simpa [binding.exact] using proofExact

/-- The authenticated ASJA payload reconstructs the complete exact result for
the locked Pool state, including its derived chronological sequence. -/
theorem bound_snapshot_payload_reconstructs_locked_result
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaf : PairLeaf K)
    (binding : AuthenticatedLiveSnapshotBinding Digest)
    (result : PairLiveState Digest)
    (proofExact : ExactPairAppendTransition parent emptyLeaf compressPair depth
      leaf binding.proofBound result) :
    applyPayload binding.accountDerived (payloadOf result) = result := by
  exact payload_reconstructs_exact_result parent emptyLeaf compressPair depth
    leaf binding.accountDerived result
      (bound_snapshot_transports_exact_transition parent emptyLeaf compressPair
        depth leaf binding result proofExact)

/-- Snapshot inequality is a fail-closed condition for the strengthened
caller contract. -/
def StrengthenedCallerAccepts
    {Digest : Type}
    (accountDerived proofBound : PairLiveState Digest) : Prop :=
  proofBound = accountDerived

theorem stale_or_substituted_snapshot_rejected
    {Digest : Type}
    (accountDerived proofBound : PairLiveState Digest)
    (different : proofBound ≠ accountDerived) :
    ¬ StrengthenedCallerAccepts accountDerived proofBound := by
  exact different

#print axioms current_pool_gate_ignores_source_root_and_frontier
#print axioms current_pool_gate_does_not_determine_live_snapshot
#print axioms bound_snapshot_transports_exact_transition
#print axioms bound_snapshot_payload_reconstructs_locked_result
#print axioms stale_or_substituted_snapshot_rejected

end AspisPool.V7PairCallerLiveSnapshotGate
