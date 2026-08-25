import Mathlib
import AspisFormal.Pool.IncrementalMerkleV1
import AspisFormal.Pool.RootHistoryV1

/-!
# Pool V1 retained historical anchors

This module proves the P3a append-only fact independently of any concrete
hash: extending chronological root history cannot invalidate an earlier exact
sequence/root entry, and extending the leaf list preserves the complete old
leaf prefix.  Consequently a membership predicate already established at the
retained old root remains a valid historical authorization premise while
unrelated leaves and roots are appended.

The production bridge must show that successful Rust persistence extends the
root-page sequence by the exact post-append Poseidon-v3 roots.  Concrete
Poseidon-v3, account/PDA parsing, nullifier freshness and verifier acceptance
are deliberately outside this pure theorem.
-/

set_option autoImplicit false

namespace AspisPool.HistoricalAnchorV1

inductive TransitionKind where
  | privateTransfer
  | withdrawal
  deriving DecidableEq, Repr

/-- Semantic model of the exact 208-byte `ASPA` version-one envelope. -/
structure Envelope (Digest Binding : Type) where
  transitionKind : TransitionKind
  pool : Binding
  deploymentDomain : Binding
  anchorSequence : Nat
  anchorRoot : Digest
  nullifier : Digest
  verifierProfile : Binding
  verifierRelease : Binding
  deriving DecidableEq, Repr

/-- Exact sequence/root retention, expressed without a decidable equality on
roots.  The prefix length fixes the root's chronological sequence. -/
def RetainedAt {Root : Type} (history : List Root) (sequence : Nat)
    (root : Root) : Prop :=
  ∃ before after,
    history = before ++ root :: after ∧ before.length = sequence

/-- Extending append-only history preserves an earlier exact sequence/root. -/
theorem retainedAt_append {Root : Type} (history laterRoots : List Root)
    (sequence : Nat) (root : Root)
    (retained : RetainedAt history sequence root) :
    RetainedAt (history ++ laterRoots) sequence root := by
  rcases retained with ⟨before, after, historyEq, beforeLength⟩
  refine ⟨before, after ++ laterRoots, ?_, beforeLength⟩
  rw [historyEq]
  simp [List.append_assoc]

/-- One additional chronological root is the fundamental persistence step. -/
theorem retainedAt_append_one {Root : Type} (history : List Root)
    (sequence : Nat) (root nextRoot : Root)
    (retained : RetainedAt history sequence root) :
    RetainedAt (history ++ [nextRoot]) sequence root :=
  retainedAt_append history [nextRoot] sequence root retained

/-- Appending unrelated leaves and their roots preserves both the exact old
root-history anchor and the complete old chronological leaf prefix. -/
theorem retained_anchor_and_leaf_prefix_survive
    {Root Leaf : Type} (history laterRoots : List Root)
    (oldLeaves outputs : List Leaf) (sequence : Nat) (root : Root)
    (retained : RetainedAt history sequence root) :
    RetainedAt (history ++ laterRoots) sequence root ∧
      (oldLeaves ++ outputs).take oldLeaves.length = oldLeaves := by
  exact ⟨retainedAt_append history laterRoots sequence root retained,
    by simp⟩

/-- A membership fact is phrased at the retained root, not the current root.
Since neither that root nor the fact changes under append-only extension, an
already valid witness remains a valid historical-anchor premise. -/
theorem historical_membership_anchor_survives
    {Root Leaf Witness : Type}
    (opens : Root → Leaf → Witness → Prop)
    (history laterRoots : List Root) (sequence : Nat) (root : Root)
    (leaf : Leaf) (witness : Witness)
    (retained : RetainedAt history sequence root)
    (membership : opens root leaf witness) :
    RetainedAt (history ++ laterRoots) sequence root ∧
      opens root leaf witness := by
  exact ⟨retainedAt_append history laterRoots sequence root retained, membership⟩

/-- Exact common selection/identity fields that the Pool-side lookup compares
after decoding the versioned envelope. -/
def Binds {Digest Binding : Type} (envelope : Envelope Digest Binding)
    (kind : TransitionKind) (pool deploymentDomain : Binding)
    (sequence : Nat) (root nullifier : Digest)
    (profile release : Binding) : Prop :=
  envelope.transitionKind = kind ∧
  envelope.pool = pool ∧
  envelope.deploymentDomain = deploymentDomain ∧
  envelope.anchorSequence = sequence ∧
  envelope.anchorRoot = root ∧
  envelope.nullifier = nullifier ∧
  envelope.verifierProfile = profile ∧
  envelope.verifierRelease = release

/-- Successful envelope binding exposes every field exactly; no verifier
profile, release, transition kind or deployment domain is implicit. -/
theorem binds_exact {Digest Binding : Type} (envelope : Envelope Digest Binding)
    (kind : TransitionKind) (pool deploymentDomain : Binding)
    (sequence : Nat) (root nullifier : Digest)
    (profile release : Binding)
    (binding : Binds envelope kind pool deploymentDomain sequence root nullifier
      profile release) :
    envelope.transitionKind = kind ∧
      envelope.pool = pool ∧
      envelope.deploymentDomain = deploymentDomain ∧
      envelope.anchorSequence = sequence ∧
      envelope.anchorRoot = root ∧
      envelope.nullifier = nullifier ∧
      envelope.verifierProfile = profile ∧
      envelope.verifierRelease = release :=
  binding

/-- Named source boundary for P3a.  It does not assume concrete hashing; it
records exactly what the Rust/account bridge must establish about successful
history persistence and historical lookup. -/
structure SourceRefinementBoundary (Root : Type) where
  persistedHistory : List Root
  modelHistory : List Root
  historiesEqual : persistedHistory = modelHistory

#print axioms retainedAt_append
#print axioms retainedAt_append_one
#print axioms retained_anchor_and_leaf_prefix_survive
#print axioms historical_membership_anchor_survives
#print axioms binds_exact

end AspisPool.HistoricalAnchorV1
