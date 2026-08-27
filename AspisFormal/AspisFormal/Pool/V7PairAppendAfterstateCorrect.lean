import AspisFormal.Pool.IncrementalMerkleV1
import AspisFormal.Pool.V7PoolRootRoleConcurrency

/-!
# Exact pair append to proof-carried afterstate

This file closes the pure mathematical boundary behind the one-transaction
`ASJA` result.  A candidate afterstate is valid only when it is the exact
binary-carry append of the proved output-pair digest from the fully bound live
frontier.  The current root, cursor, sequence, updated frontier and updated
root are all tied together in one relation.

The wire payload omits the root sequence: the Pool derives it from the locked
live state.  The final theorem proves that the three payload fields reconstruct
the complete certified live result, including that derived sequence.
-/

set_option autoImplicit false

namespace AspisPool.V7PairAppendAfterstateCorrect

open AspisPool.IncrementalMerkleV1
open AspisPool.V7PairLeafOccupancy
open AspisPool.V7PoolRootRoleConcurrency

abbrev PairFrontier (Digest : Type) := List (Option Digest)
abbrev PairLiveState (Digest : Type) :=
  LiveAppendState Digest (PairFrontier Digest)

/-- The exact three semantic fields carried by the 680-byte ASJA payload.
The eight-byte typed envelope is outside this pure model. -/
structure PairAfterstatePayload (Digest : Type) where
  nextPairIndex : Nat
  nextRoot : Digest
  nextFrontier : PairFrontier Digest
  deriving DecidableEq

/-- Reconstruct the full live result from a payload and the source state
locked by the terminal transaction.  Sequence is intentionally derived. -/
def applyPayload {Digest : Type}
    (source : PairLiveState Digest)
    (payload : PairAfterstatePayload Digest) : PairLiveState Digest where
  sequence := source.sequence + 1
  nextPairIndex := payload.nextPairIndex
  root := payload.nextRoot
  frontier := payload.nextFrontier

def payloadOf {Digest : Type}
    (result : PairLiveState Digest) : PairAfterstatePayload Digest where
  nextPairIndex := result.nextPairIndex
  nextRoot := result.root
  nextFrontier := result.frontier

/-- Literal production relation for one pair-leaf append.  In particular,
the result frontier is not merely well-formed metadata: it must be the exact
output of `appendCarry` from the bound source frontier. -/
def ExactPairAppendTransition
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaf : PairLeaf K)
    (source result : PairLiveState Digest) : Prop :=
  leaf.Valid ∧
    source.sequence = source.nextPairIndex ∧
    source.nextPairIndex = frontierValue source.frontier ∧
    source.frontier.length = depth ∧
    source.root = reconstructRoot parent emptyLeaf source.frontier ∧
    appendCarry parent (compressPair leaf) source.frontier =
      .more result.frontier ∧
    result.sequence = source.sequence + 1 ∧
    result.nextPairIndex = source.nextPairIndex + 1 ∧
    result.nextPairIndex = frontierValue result.frontier ∧
    result.root = reconstructRoot parent emptyLeaf result.frontier

/-- Canonical candidate result once the exact updated frontier has been
computed by binary carry. -/
def candidateResult {Digest : Type}
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (source : PairLiveState Digest)
    (updated : PairFrontier Digest) : PairLiveState Digest where
  sequence := source.sequence + 1
  nextPairIndex := source.nextPairIndex + 1
  root := reconstructRoot parent emptyLeaf updated
  frontier := updated

/-- A valid chronological frontier plus one successful carry constructs the
exact production afterstate relation. -/
theorem candidateResult_exact
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaves : List Digest)
    (leaf : PairLeaf K)
    (source : PairLiveState Digest)
    (updated : PairFrontier Digest)
    (validLeaf : leaf.Valid)
    (invariant : FrontierInvariant parent emptyLeaf depth leaves source.frontier)
    (sourceSequence : source.sequence = leaves.length)
    (sourceIndex : source.nextPairIndex = leaves.length)
    (sourceRoot : source.root = reconstructRoot parent emptyLeaf source.frontier)
    (carry : appendCarry parent (compressPair leaf) source.frontier =
      .more updated) :
    ExactPairAppendTransition parent emptyLeaf compressPair depth leaf source
      (candidateResult parent emptyLeaf source updated) := by
  rcases appendCarry_open_spec parent (compressPair leaf) source.frontier
      updated carry with ⟨updatedLength, updatedValue⟩
  refine ⟨validLeaf, sourceSequence.trans sourceIndex.symm, ?_,
    invariant.depth_eq, sourceRoot, carry, rfl, rfl, ?_, rfl⟩
  · exact sourceIndex.trans invariant.count_eq.symm
  · dsimp [candidateResult]
    rw [updatedValue, sourceIndex, invariant.count_eq]

/-- The result root certified by the transition is exactly the chronological
pair tree root after appending the proved pair digest. -/
theorem exact_transition_result_root_correct
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaves : List Digest)
    (leaf : PairLeaf K)
    (source result : PairLiveState Digest)
    (invariant : FrontierInvariant parent emptyLeaf depth leaves source.frontier)
    (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth leaf
      source result) :
    result.root = rootWithEmptySuffix parent emptyLeaf depth
      (leaves ++ [compressPair leaf]) := by
  have appendCorrect := append_correct parent emptyLeaf (compressPair leaf)
    depth leaves source.frontier result.frontier invariant exact.2.2.2.2.2.1
  exact exact.2.2.2.2.2.2.2.2.2.trans appendCorrect.2

/-- The exact transition supplies the index consequence consumed by the
existing atomic-settlement theorem. -/
theorem exact_transition_indices
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaf : PairLeaf K)
    (source result : PairLiveState Digest)
    (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth leaf
      source result) :
    result.sequence = source.sequence + 1 ∧
      result.nextPairIndex = source.nextPairIndex + 1 := by
  exact ⟨exact.2.2.2.2.2.2.1, exact.2.2.2.2.2.2.2.1⟩

/-- ASJA need not serialize sequence: after the verifier has established the
exact transition, applying its three-field payload to the locked source
reconstructs the complete certified result byte-for-byte at the semantic
level. -/
theorem payload_reconstructs_exact_result
    {K Digest : Type} [CommRing K]
    (parent : Digest → Digest → Digest)
    (emptyLeaf : Digest)
    (compressPair : PairLeaf K → Digest)
    (depth : Nat)
    (leaf : PairLeaf K)
    (source result : PairLiveState Digest)
    (exact : ExactPairAppendTransition parent emptyLeaf compressPair depth leaf
      source result) :
    applyPayload source (payloadOf result) = result := by
  cases source
  cases result
  simp only [applyPayload, payloadOf]
  congr
  exact exact.2.2.2.2.2.2.1.symm

#print axioms candidateResult_exact
#print axioms exact_transition_result_root_correct
#print axioms exact_transition_indices
#print axioms payload_reconstructs_exact_result

end AspisPool.V7PairAppendAfterstateCorrect
