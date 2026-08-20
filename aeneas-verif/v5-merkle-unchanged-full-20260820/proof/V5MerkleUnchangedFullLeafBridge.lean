import V5MerkleUnchangedFullHelperBridge

/-! Leaf-hash loop semantics for the unchanged full extraction. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullLeafBridge

open V5MerkleUnchangedFull
open AspisV5MerkleUnchangedFullHelperBridge
open AspisV5MerkleRustBridge

abbrev GeneratedDigest := Array Std.U8 32#usize
abbrev GeneratedDigestVec := alloc.vec.Vec GeneratedDigest

/-- Source body shared by the four syntactically duplicated leaf loops in
the generated helper. -/
noncomputable def generatedLeafBody
    (hash : GeneratedHash) (treeTag : Std.U8)
    (state : core.slice.iter.ChunksExact Std.U8 × GeneratedDigestVec) :
    Result (ControlFlow
      (core.slice.iter.ChunksExact Std.U8 × GeneratedDigestVec)
      GeneratedDigestVec) := do
  let (record?, iter') ← core.slice.iter.IteratorChunksExact.next state.1
  match record? with
  | none => ok (done state.2)
  | some record =>
    let digest ←
      aspis_core.state_only_private_merkle.private_leaf_hash_record
        hash treeTag record
    let level' ← alloc.vec.Vec.push state.2 digest
    ok (cont (iter', level'))

noncomputable def generatedLeafLoop
    (iter : core.slice.iter.ChunksExact Std.U8)
    (hash : GeneratedHash) (treeTag : Std.U8)
    (level : GeneratedDigestVec) : Result GeneratedDigestVec :=
  loop (generatedLeafBody hash treeTag) (iter, level)

theorem generated_loop0_eq_leaf_loop
    (iter : core.slice.iter.ChunksExact Std.U8)
    (hash : GeneratedHash) (treeTag : Std.U8)
    (level : GeneratedDigestVec) :
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop0
      iter hash treeTag level = generatedLeafLoop iter hash treeTag level := rfl

theorem generated_loop1_eq_leaf_loop
    (iter : core.slice.iter.ChunksExact Std.U8)
    (hash : GeneratedHash) (treeTag : Std.U8)
    (level : GeneratedDigestVec) :
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop1
      iter hash treeTag level = generatedLeafLoop iter hash treeTag level := rfl

theorem generated_loop2_eq_leaf_loop
    (iter : core.slice.iter.ChunksExact Std.U8)
    (hash : GeneratedHash) (treeTag : Std.U8)
    (level : GeneratedDigestVec) :
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop2
      iter hash treeTag level = generatedLeafLoop iter hash treeTag level := rfl

theorem generated_loop3_eq_leaf_loop
    (iter : core.slice.iter.ChunksExact Std.U8)
    (hash : GeneratedHash) (treeTag : Std.U8)
    (level : GeneratedDigestVec) :
    aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop3
      iter hash treeTag level = generatedLeafLoop iter hash treeTag level := rfl

/-- Exact finite trace of every record consumed by the extracted leaf loop. -/
inductive GeneratedLeafTrace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash) (treeTag : Std.U8) :
    core.slice.iter.ChunksExact Std.U8 → GeneratedDigestVec →
      GeneratedDigestVec → Prop
  | done (iter : core.slice.iter.ChunksExact Std.U8)
      (level : GeneratedDigestVec)
      (empty : iter.chunks = []) :
      GeneratedLeafTrace sha256 hash treeTag iter level level
  | step (iter iter' : core.slice.iter.ChunksExact Std.U8)
      (record : Slice Std.U8) (level level' finalLevel : GeneratedDigestVec)
      (digest : GeneratedDigest)
      (next_run : core.slice.iter.IteratorChunksExact.next iter =
        .ok (some record, iter'))
      (hash_run :
        aspis_core.state_only_private_merkle.private_leaf_hash_record
          hash treeTag record = .ok digest)
      (push_run : alloc.vec.Vec.push level digest = .ok level')
      (digest_eq : generatedArrayToDigest digest =
        (sha256MerkleHashing sha256).privateLeaf
          (generatedU8ToByte treeTag)
          (record.val.map generatedU8ToByte))
      (tail : GeneratedLeafTrace sha256 hash treeTag iter' level' finalLevel) :
      GeneratedLeafTrace sha256 hash treeTag iter level finalLevel

/-- A successful generated leaf loop has one exact trace node for every full
record chunk, and every appended digest is the maintained private-leaf hash
of exactly that chunk. -/
theorem generated_leaf_loop_success_yields_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (iter : core.slice.iter.ChunksExact Std.U8) (treeTag : Std.U8)
    (level finalLevel : GeneratedDigestVec)
    (hrun : generatedLeafLoop iter hash treeTag level = .ok finalLevel) :
    Nonempty (GeneratedLeafTrace sha256 hash treeTag iter level finalLevel) := by
  generalize hchunks : iter.chunks = chunks
  induction chunks generalizing iter level with
  | nil =>
      have hnext : core.slice.iter.IteratorChunksExact.next iter =
          .ok (none, iter) := by
        simp [core.slice.iter.IteratorChunksExact.next, hchunks]
      unfold generatedLeafLoop at hrun
      rw [loop.eq_def] at hrun
      unfold generatedLeafBody at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok] at hrun
      injection hrun with hfinal
      subst finalLevel
      exact ⟨GeneratedLeafTrace.done iter level hchunks⟩
  | cons record records ih =>
      let iter' : core.slice.iter.ChunksExact Std.U8 :=
        { chunks := records, remainder := iter.remainder }
      have hnext : core.slice.iter.IteratorChunksExact.next iter =
          .ok (some ⟨record.val, record.property⟩, iter') := by
        simp [core.slice.iter.IteratorChunksExact.next, hchunks, iter']
      unfold generatedLeafLoop at hrun
      rw [loop.eq_def] at hrun
      unfold generatedLeafBody at hrun
      simp only [hnext, Aeneas.Std.bind_tc_ok] at hrun
      generalize hleaf :
        aspis_core.state_only_private_merkle.private_leaf_hash_record hash treeTag
            ⟨record.val, record.property⟩ = leafResult at hrun
      cases leafResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok digest =>
        simp only [Aeneas.Std.bind_tc_ok] at hrun
        generalize hpush : alloc.vec.Vec.push level digest = pushResult at hrun
        cases pushResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok level' =>
          simp only [Aeneas.Std.bind_tc_ok] at hrun
          have htail : generatedLeafLoop iter' hash treeTag level' =
              .ok finalLevel := by
            exact hrun
          let tail := Classical.choice (ih iter' level' htail rfl)
          have hdigest := private_leaf_hash_record_exact sha256 hash hhash
            treeTag ⟨record.val, record.property⟩ digest hleaf
          exact ⟨GeneratedLeafTrace.step iter iter'
            ⟨record.val, record.property⟩ level level' finalLevel digest
            hnext hleaf hpush (by simpa [sha256MerkleHashing,
              hashInputBytes] using hdigest) tail⟩

theorem generated_loop0_success_yields_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (iter : core.slice.iter.ChunksExact Std.U8) (treeTag : Std.U8)
    (level finalLevel : GeneratedDigestVec)
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop0
        iter hash treeTag level = .ok finalLevel) :
    Nonempty (GeneratedLeafTrace sha256 hash treeTag iter level finalLevel) := by
  apply generated_leaf_loop_success_yields_trace sha256 hash hhash iter treeTag level
  rwa [← generated_loop0_eq_leaf_loop]

theorem generated_loop1_success_yields_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (iter : core.slice.iter.ChunksExact Std.U8) (treeTag : Std.U8)
    (level finalLevel : GeneratedDigestVec)
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop1
        iter hash treeTag level = .ok finalLevel) :
    Nonempty (GeneratedLeafTrace sha256 hash treeTag iter level finalLevel) := by
  apply generated_leaf_loop_success_yields_trace sha256 hash hhash iter treeTag level
  rwa [← generated_loop1_eq_leaf_loop]

theorem generated_loop2_success_yields_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (iter : core.slice.iter.ChunksExact Std.U8) (treeTag : Std.U8)
    (level finalLevel : GeneratedDigestVec)
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop2
        iter hash treeTag level = .ok finalLevel) :
    Nonempty (GeneratedLeafTrace sha256 hash treeTag iter level finalLevel) := by
  apply generated_leaf_loop_success_yields_trace sha256 hash hhash iter treeTag level
  rwa [← generated_loop2_eq_leaf_loop]

theorem generated_loop3_success_yields_trace
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (iter : core.slice.iter.ChunksExact Std.U8) (treeTag : Std.U8)
    (level finalLevel : GeneratedDigestVec)
    (hrun :
      aspis_core.state_only_private_openings.verify_state_only_private_opening_from_proof_with_topology_loop3
        iter hash treeTag level = .ok finalLevel) :
    Nonempty (GeneratedLeafTrace sha256 hash treeTag iter level finalLevel) := by
  apply generated_leaf_loop_success_yields_trace sha256 hash hhash iter treeTag level
  rwa [← generated_loop3_eq_leaf_loop]

#print axioms generated_leaf_loop_success_yields_trace
#print axioms generated_loop0_success_yields_trace
#print axioms generated_loop1_success_yields_trace
#print axioms generated_loop2_success_yields_trace
#print axioms generated_loop3_success_yields_trace

end AspisV5MerkleUnchangedFullLeafBridge
