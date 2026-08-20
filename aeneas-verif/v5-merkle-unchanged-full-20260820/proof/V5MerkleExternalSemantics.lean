import V5MerkleUnchangedFull.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5MerkleExternalSemantics

open V5MerkleUnchangedFull

/-! These lemmas make the handwritten standard-library boundary auditable.
They state the ordinary Rust behavior used by the unchanged Merkle extraction;
none is a cryptographic assumption. -/

section Option

theorem option_ok_or_some {T E : Type} (value : T) (error : E) :
    core.option.Option.ok_or (some value) error = ok (.Ok value) := by
  rfl

theorem option_ok_or_none {T E : Type} (error : E) :
    core.option.Option.ok_or (none : Option T) error = ok (.Err error) := by
  rfl

theorem option_copied {T : Type} (copy : core.marker.Copy T)
    (value : Option T) :
    core.option.OptionShared0T.copied copy value = ok value := by
  rfl

theorem option_try_some {T : Type} (value : T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (some value) =
      ok (.Continue value) := by
  rfl

theorem option_try_none {T : Type} :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch (none : Option T) =
      ok (.Break none) := by
  rfl

theorem option_from_none_residual (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = ok none := by
  rfl

theorem option_eq_none_none {T : Type} (eqT : core.cmp.PartialEq T T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq eqT none none =
      ok true := by
  rfl

theorem option_eq_some_some {T : Type} (eqT : core.cmp.PartialEq T T)
    (left right : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq eqT
        (some left) (some right) = eqT.eq left right := by
  rfl

theorem option_eq_mixed {T : Type} (eqT : core.cmp.PartialEq T T)
    (value : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq eqT
        (some value) none = ok false ∧
      core.option.Option.Insts.CoreCmpPartialEqOption.eq eqT
        none (some value) = ok false := by
  exact ⟨rfl, rfl⟩

end Option

section Result

theorem result_map_err_ok {T E F O : Type}
    (function : core.ops.function.FnOnce O E F) (value : T) (state : O) :
    core.result.Result.map_err function (.Ok value) state = ok (.Ok value) := by
  rfl

theorem result_map_err_err {T E F O : Type}
    (function : core.ops.function.FnOnce O E F) (error : E) (state : O)
    (mapped : F) (hcall : function.call_once state error = ok mapped) :
    core.result.Result.map_err function
        (.Err error : core.result.Result T E) state =
      ok (.Err mapped : core.result.Result T F) := by
  simp [core.result.Result.map_err, hcall]

end Result

section Vec

theorem vec_as_slice {T : Type} (A : Type) (value : alloc.vec.Vec T) :
    alloc.vec.Vec.as_slice A value = ok ⟨value.val, value.property⟩ := by
  rfl

theorem vec_clear {T : Type} (A : Type) (value : alloc.vec.Vec T) :
    alloc.vec.Vec.clear A value = ok (alloc.vec.Vec.new T) := by
  rfl

theorem vec_is_empty {T : Type} (A : Type) (value : alloc.vec.Vec T) :
    alloc.vec.Vec.is_empty A value = ok (decide (value.val = [])) := by
  rfl

end Vec

section SliceAndIterator

theorem slice_last {T : Type} (slice : Slice T) :
    core.slice.Slice.last slice = ok slice.val.getLast? := by
  rfl

theorem slice_windows_zero {T : Type} (slice : Slice T) :
    core.slice.Slice.windows slice 0#usize = fail .panic := by
  simp [core.slice.Slice.windows]

theorem slice_windows_nonzero {T : Type} (slice : Slice T)
    (width : Std.Usize) (hwidth : width ≠ 0#usize) :
    core.slice.Slice.windows slice width =
      ok { slice := slice, width := width, index := 0 } := by
  simp [core.slice.Slice.windows, hwidth]

theorem windows_next_some {T : Type} (slice : Slice T)
    (width : Std.Usize) (index : Nat)
    (hbound : index + width.val ≤ slice.val.length) :
    core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
        { slice := slice, width := width, index := index } =
      ok
        (some (core.slice.iter.Windows.windowAt slice index width.val),
          { slice := slice, width := width, index := index + 1 }) := by
  simp [
    core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
    hbound]

theorem windows_next_none {T : Type} (slice : Slice T)
    (width : Std.Usize) (index : Nat)
    (hbound : ¬ index + width.val ≤ slice.val.length) :
    core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
        { slice := slice, width := width, index := index } =
      ok (none, { slice := slice, width := width, index := index }) := by
  simp [
    core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
    hbound]

theorem iterator_find_empty {Self P Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (predicateFn : core.ops.function.FnMut P Item Bool)
    (self self' : Self) (predicate : P)
    (hnext : iterator.next self = ok (none, self')) :
    core.iter.traits.iterator.Iterator.find.default
        iterator predicateFn self predicate = ok (none, self') := by
  simp [core.iter.traits.iterator.Iterator.find.default, loop, hnext]

theorem iterator_find_first {Self P Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (predicateFn : core.ops.function.FnMut P Item Bool)
    (self self' : Self) (predicate predicate' : P) (item : Item)
    (hnext : iterator.next self = ok (some item, self'))
    (hpredicate : predicateFn.call_mut predicate item = ok (true, predicate')) :
    core.iter.traits.iterator.Iterator.find.default
        iterator predicateFn self predicate = ok (some item, self') := by
  simp [core.iter.traits.iterator.Iterator.find.default, loop, hnext,
    hpredicate]

theorem iterator_any_empty {Self P Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (predicateFn : core.ops.function.FnMut P Item Bool)
    (self self' : Self) (predicate : P)
    (hnext : iterator.next self = ok (none, self')) :
    core.iter.traits.iterator.Iterator.any.default
        iterator predicateFn self predicate = ok (false, self') := by
  simp [core.iter.traits.iterator.Iterator.any.default, loop, hnext]

theorem iterator_any_first {Self P Item : Type}
    (iterator : core.iter.traits.iterator.Iterator Self Item)
    (predicateFn : core.ops.function.FnMut P Item Bool)
    (self self' : Self) (predicate predicate' : P) (item : Item)
    (hnext : iterator.next self = ok (some item, self'))
    (hpredicate : predicateFn.call_mut predicate item = ok (true, predicate')) :
    core.iter.traits.iterator.Iterator.any.default
        iterator predicateFn self predicate = ok (true, self') := by
  simp [core.iter.traits.iterator.Iterator.any.default, loop, hnext,
    hpredicate]

end SliceAndIterator

section Queries

theorem circle_line_tags :
    aspis_core.circle_line_merkle.CIRCLE_LINE_TAGS =
      ok (Array.make 3#usize [65#u8, 66#u8, 67#u8]) := by
  rfl

theorem circle_layer_tags :
    aspis_core.circle_merkle.CIRCLE_C1_LAYER0_TAG = ok 64#u8 ∧
      aspis_core.circle_merkle.CIRCLE_C2_LAYER0_TAG = ok 192#u8 := by
  exact ⟨rfl, rfl⟩

theorem map_query_indices_fields
    (indices :
      V5MerkleQueryReuse.circle_line_merkle.CircleLineQueryIndices) :
    (mapQueryIndices indices).layer0 = indices.layer0 ∧
      (mapQueryIndices indices).later = indices.later := by
  exact ⟨rfl, rfl⟩

theorem derive_queries_ok (queries : Slice Std.U32) (count : Std.Usize)
    (indices :
      V5MerkleQueryReuse.circle_line_merkle.CircleLineQueryIndices)
    (hderive :
      V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count
          queries count = ok (.Ok indices)) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries count = ok (.Ok (mapQueryIndices indices)) := by
  simp [aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count,
    hderive]

theorem derive_queries_err (queries : Slice Std.U32) (count : Std.Usize)
    (error : V5MerkleQueryReuse.circle_line_merkle.CircleLineMerkleError)
    (hderive :
      V5MerkleQueryReuse.circle_line_merkle.derive_circle_line_query_indices_for_count
          queries count = ok (.Err error)) :
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries count = ok (.Err (mapQueryError error)) := by
  simp [aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count,
    hderive]

end Queries

#print axioms option_ok_or_some
#print axioms result_map_err_err
#print axioms windows_next_some
#print axioms iterator_find_first
#print axioms derive_queries_ok
#print axioms V5MerkleUnchangedFull.aspis_core.merkle.Radix4BinaryCapTopology.new
#print axioms V5MerkleUnchangedFull.aspis_core.state_only_private_openings.validate_shape
#print axioms V5MerkleUnchangedFull.private_openings.verify_v5_private_openings_from_proof

end V5MerkleExternalSemantics
