import V7MerkleK12.Funs
import V7MerkleCaller.Funs
import V7DeferredParser.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Exact namespace bridge for the transparent V7 caller extraction

The focused caller extraction and the focused four-function Merkle extraction
translate overlapping production Rust bodies into distinct Lean namespaces.
The theorems below identify those duplicate generated computations from their
definitions.  They do not assume that the Rust and Lean implementations agree.

The independently pinned deferred-parser extraction likewise gives the same
Rust wire structure a distinct generated Lean name.  `deferredWireEquiv`
copies every generated field and has definitional two-sided inverses.  The
parser-facing query wrapper then invokes the translated production caller's
`V7CompactOneFoldWire.query`; it is not a handwritten query parser.
-/

namespace AspisV7MerkleCallerNamespaceBridge

theorem caller_dom_leaf_eq :
    V7MerkleCallerGenerated.state_only_private_merkle.DOM_LEAF =
      V7MerkleK12Generated.state_only_private_merkle.DOM_LEAF := by
  unfold V7MerkleCallerGenerated.state_only_private_merkle.DOM_LEAF
    V7MerkleK12Generated.state_only_private_merkle.DOM_LEAF
  rfl

theorem caller_digest_bytes_eq :
    V7MerkleCallerGenerated.v7_merkle208.V7_MERKLE_DIGEST_BYTES =
      V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES := by
  unfold V7MerkleCallerGenerated.v7_merkle208.V7_MERKLE_DIGEST_BYTES
    V7MerkleK12Generated.v7_merkle208.V7_MERKLE_DIGEST_BYTES
  rfl

theorem caller_dom_node_eq :
    V7MerkleCallerGenerated.v7_merkle208.DOM_NODE =
      V7MerkleK12Generated.v7_merkle208.DOM_NODE := by
  unfold V7MerkleCallerGenerated.v7_merkle208.DOM_NODE
    V7MerkleK12Generated.v7_merkle208.DOM_NODE
  rfl

theorem caller_windows_iterator_eq (T : Type) :
    V7MerkleCallerGenerated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice T =
      V7MerkleK12Generated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice T := by
  unfold V7MerkleCallerGenerated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
    V7MerkleK12Generated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
  rfl

theorem caller_private_leaf_hash_eq :
    V7MerkleCallerGenerated.state_only_private_merkle.private_leaf_hash =
      V7MerkleK12Generated.state_only_private_merkle.private_leaf_hash := by
  funext hash treeTag value salt
  unfold V7MerkleCallerGenerated.state_only_private_merkle.private_leaf_hash
    V7MerkleK12Generated.state_only_private_merkle.private_leaf_hash
  rw [caller_dom_leaf_eq]

theorem caller_truncate_sha256_v7_eq :
    V7MerkleCallerGenerated.v7_merkle208.truncate_sha256_v7 =
      V7MerkleK12Generated.v7_merkle208.truncate_sha256_v7 := by
  funext digest
  unfold V7MerkleCallerGenerated.v7_merkle208.truncate_sha256_v7
    V7MerkleK12Generated.v7_merkle208.truncate_sha256_v7
  rw [caller_digest_bytes_eq]

theorem caller_private_leaf_hash_v7_eq :
    V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 =
      V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7 := by
  funext hash treeTag value salt
  unfold V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7
    V7MerkleK12Generated.v7_merkle208.private_leaf_hash_v7
  rw [caller_private_leaf_hash_eq, caller_truncate_sha256_v7_eq]

theorem caller_node_hash_v7_eq :
    V7MerkleCallerGenerated.v7_merkle208.node_hash_v7 =
      V7MerkleK12Generated.v7_merkle208.node_hash_v7 := by
  funext hash left right
  unfold V7MerkleCallerGenerated.v7_merkle208.node_hash_v7
    V7MerkleK12Generated.v7_merkle208.node_hash_v7
  rw [caller_dom_node_eq, caller_digest_bytes_eq,
    caller_truncate_sha256_v7_eq]

theorem caller_verifier_closure_call_mut_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut := by
  funext closure entries
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_mut
  cases closure
  rfl

theorem caller_verifier_closure_call_once_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_once =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_once := by
  funext closure entries
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_once
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool.call_once
  rw [caller_verifier_closure_call_mut_eq]

theorem caller_verifier_closure_fn_once_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool := by
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
  rw [caller_verifier_closure_call_once_eq]

theorem caller_verifier_closure_fn_mut_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool := by
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
  rw [caller_verifier_closure_fn_once_eq,
    caller_verifier_closure_call_mut_eq]

theorem caller_verifier_inner_body_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body := by
  funext hash c1Nodes c2Nodes level next nodePos index
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
  rw [caller_digest_bytes_eq, caller_node_hash_v7_eq]

theorem caller_verifier_inner_loop_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0 =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0 := by
  funext hash c1Nodes c2Nodes level next nodePos index
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
  rw [caller_verifier_inner_body_eq]

theorem caller_verifier_outer_body_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body := by
  funext hash c1Nodes c2Nodes iter level next nodePos
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
  rw [caller_verifier_inner_loop_eq]
  rfl

theorem caller_verifier_outer_loop_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0 =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0 := by
  funext iter hash c1Nodes c2Nodes level next nodePos
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
  rw [caller_verifier_outer_body_eq]

/-- The caller's duplicate verifier is exactly the independently extracted
four-root verifier computation, after importing both generated namespaces. -/
theorem caller_verify_two_minimal_subtrees_v7_bytes_eq :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes =
      V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes := by
  funext hash roots depth entries nodeBytes level next
  unfold V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
  rw [caller_digest_bytes_eq, caller_verifier_closure_fn_mut_eq,
    caller_verifier_outer_loop_eq, caller_windows_iterator_eq]
  rfl

abbrev DeferredWire :=
  V7DeferredParserGenerated.v7_onefold.V7CompactOneFoldWire
abbrev CallerWire :=
  V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire

/-- Field-for-field transport of the same Rust wire structure from the
deferred-parser extraction namespace to the caller extraction namespace. -/
def deferredWireToCaller (wire : DeferredWire) : CallerWire where
  fixed_fields_packed := wire.fixed_fields_packed
  c1_root := wire.c1_root
  c2_root := wire.c2_root
  work_nonces := wire.work_nonces
  query_section := wire.query_section
  c1_frontier := wire.c1_frontier
  c2_frontier := wire.c2_frontier

def callerWireToDeferred (wire : CallerWire) : DeferredWire where
  fixed_fields_packed := wire.fixed_fields_packed
  c1_root := wire.c1_root
  c2_root := wire.c2_root
  work_nonces := wire.work_nonces
  query_section := wire.query_section
  c1_frontier := wire.c1_frontier
  c2_frontier := wire.c2_frontier

@[simp] theorem callerWireToDeferred_deferredWireToCaller
    (wire : DeferredWire) :
    callerWireToDeferred (deferredWireToCaller wire) = wire := by
  cases wire
  rfl

@[simp] theorem deferredWireToCaller_callerWireToDeferred
    (wire : CallerWire) :
    deferredWireToCaller (callerWireToDeferred wire) = wire := by
  cases wire
  rfl

/-- Exact equivalence between the two independently generated names of the
same production Rust structure. -/
def deferredWireEquiv : DeferredWire ≃ CallerWire where
  toFun := deferredWireToCaller
  invFun := callerWireToDeferred
  left_inv := callerWireToDeferred_deferredWireToCaller
  right_inv := deferredWireToCaller_callerWireToDeferred

@[simp] theorem deferredWireToCaller_fixed_fields_packed (wire : DeferredWire) :
    (deferredWireToCaller wire).fixed_fields_packed = wire.fixed_fields_packed := rfl
@[simp] theorem deferredWireToCaller_c1_root (wire : DeferredWire) :
    (deferredWireToCaller wire).c1_root = wire.c1_root := rfl
@[simp] theorem deferredWireToCaller_c2_root (wire : DeferredWire) :
    (deferredWireToCaller wire).c2_root = wire.c2_root := rfl
@[simp] theorem deferredWireToCaller_work_nonces (wire : DeferredWire) :
    (deferredWireToCaller wire).work_nonces = wire.work_nonces := rfl
@[simp] theorem deferredWireToCaller_query_section (wire : DeferredWire) :
    (deferredWireToCaller wire).query_section = wire.query_section := rfl
@[simp] theorem deferredWireToCaller_c1_frontier (wire : DeferredWire) :
    (deferredWireToCaller wire).c1_frontier = wire.c1_frontier := rfl
@[simp] theorem deferredWireToCaller_c2_frontier (wire : DeferredWire) :
    (deferredWireToCaller wire).c2_frontier = wire.c2_frontier := rfl

/-- Parser-facing query record.  It is populated only by mapping the output of
the translated production `V7CompactOneFoldWire.query` computation. -/
structure DeferredQueryRecord where
  c1_packed : Slice Std.U8
  c2_packed : Slice Std.U8
  salt : Array Std.U8 32#usize

def callerQueryRecordToDeferred
    (record : V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord) :
    DeferredQueryRecord where
  c1_packed := record.c1_packed
  c2_packed := record.c2_packed
  salt := record.salt

def mapCallerQueryResult :
    Result (Option V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord) →
      Result (Option DeferredQueryRecord)
  | .ok result => .ok (result.map callerQueryRecordToDeferred)
  | .fail error => .fail error
  | .div => .div

/-- The query operation exposed at the parser-wire type is definitionally a
field transport followed by the translated production caller query. -/
def deferredWireQuery (wire : DeferredWire) (ordinal : Std.Usize) :
    Result (Option DeferredQueryRecord) :=
  mapCallerQueryResult
    (V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query
      (deferredWireToCaller wire) ordinal)

theorem deferredWireQuery_is_translated_caller_query
    (wire : DeferredWire) (ordinal : Std.Usize) :
    deferredWireQuery wire ordinal =
      mapCallerQueryResult
        (V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query
          (deferredWireToCaller wire) ordinal) := by
  rfl

theorem deferredWireQuery_success_fields
    (wire : DeferredWire) (ordinal : Std.Usize)
    (callerRecord : V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord)
    (hrun :
      V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query
          (deferredWireToCaller wire) ordinal = .ok (some callerRecord)) :
    deferredWireQuery wire ordinal =
      .ok (some {
        c1_packed := callerRecord.c1_packed
        c2_packed := callerRecord.c2_packed
        salt := callerRecord.salt }) := by
  simp [deferredWireQuery, mapCallerQueryResult, hrun,
    callerQueryRecordToDeferred]

#print axioms caller_truncate_sha256_v7_eq
#print axioms caller_private_leaf_hash_v7_eq
#print axioms caller_node_hash_v7_eq
#print axioms caller_verify_two_minimal_subtrees_v7_bytes_eq
#print axioms deferredWireEquiv
#print axioms deferredWireQuery_is_translated_caller_query
#print axioms deferredWireQuery_success_fields

end AspisV7MerkleCallerNamespaceBridge
