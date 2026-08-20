import V5RelationLinkedGroupedFold

namespace AspisV5RelationLinkedGroupedRows

open Aeneas Aeneas.Std Result ControlFlow

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

def releasedRowGroups64 : alloc.vec.Vec Std.U8 :=
  ⟨[0#u8, 0#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 2#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 2#u8,
    0#u8, 2#u8, 0#u8, 1#u8,
    1#u8, 3#u8, 3#u8, 3#u8,
    3#u8, 4#u8, 5#u8, 6#u8,
    6#u8, 6#u8, 6#u8, 6#u8,
    6#u8, 6#u8, 6#u8, 6#u8], by scalar_tac⟩

def releasedFirstTuples : List (List Std.U8) :=
  [[0#u8, 0#u8, 1#u8, 1#u8],
   [1#u8, 1#u8, 1#u8, 1#u8],
   [1#u8, 1#u8, 1#u8, 2#u8],
   [0#u8, 2#u8, 0#u8, 1#u8],
   [1#u8, 3#u8, 3#u8, 3#u8],
   [3#u8, 4#u8, 5#u8, 6#u8],
   [6#u8, 6#u8, 6#u8, 6#u8]]

def releasedRowGroups16 : alloc.vec.Vec Std.U8 :=
  ⟨[0#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 2#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 2#u8, 3#u8,
    4#u8, 5#u8, 6#u8, 6#u8], by scalar_tac⟩

def releasedSecondTuples : List (List Std.U8) :=
  [[0#u8, 1#u8, 1#u8, 1#u8],
   [1#u8, 2#u8, 1#u8, 1#u8],
   [1#u8, 1#u8, 2#u8, 3#u8],
   [4#u8, 5#u8, 6#u8, 6#u8]]

def releasedRowGroups4 : alloc.vec.Vec Std.U8 :=
  ⟨[0#u8, 1#u8, 2#u8, 3#u8], by scalar_tac⟩

def releasedRows64Iterator : core.slice.iter.ChunksExact Std.U8 :=
  let s := alloc.vec.Vec.deref releasedRowGroups64
  let hcs : (4#usize).val > 0 := by scalar_tac
  let result := List.toChunksExact (4#usize).val hcs s.val
  let sliceChunks := result.1.attach.map fun ⟨chunk, member⟩ =>
    ⟨chunk, by
      have := List.toChunksExact_chunk_length hcs s.val chunk member
      scalar_tac⟩
  { chunks := sliceChunks
    remainder := ⟨result.2, by
      have := List.toChunksExact_remainder_length hcs s.val
      scalar_tac⟩ }

def releasedRows16Iterator : core.slice.iter.ChunksExact Std.U8 :=
  let s := alloc.vec.Vec.deref releasedRowGroups16
  let hcs : (4#usize).val > 0 := by scalar_tac
  let result := List.toChunksExact (4#usize).val hcs s.val
  let sliceChunks := result.1.attach.map fun ⟨chunk, member⟩ =>
    ⟨chunk, by
      have := List.toChunksExact_chunk_length hcs s.val chunk member
      scalar_tac⟩
  { chunks := sliceChunks
    remainder := ⟨result.2, by
      have := List.toChunksExact_remainder_length hcs s.val
      scalar_tac⟩ }

private def slice4 (a b c d : Std.U8) : Slice Std.U8 :=
  ⟨[a, b, c, d], by scalar_tac⟩

def releasedRows64ExplicitIterator : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [
      slice4 0#u8 0#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 2#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 1#u8 2#u8,
      slice4 0#u8 2#u8 0#u8 1#u8,
      slice4 1#u8 3#u8 3#u8 3#u8,
      slice4 3#u8 4#u8 5#u8 6#u8,
      slice4 6#u8 6#u8 6#u8 6#u8,
      slice4 6#u8 6#u8 6#u8 6#u8]
    remainder := ⟨[], by scalar_tac⟩ }

def releasedRows16ExplicitIterator : core.slice.iter.ChunksExact Std.U8 :=
  { chunks := [
      slice4 0#u8 1#u8 1#u8 1#u8,
      slice4 1#u8 2#u8 1#u8 1#u8,
      slice4 1#u8 1#u8 2#u8 3#u8,
      slice4 4#u8 5#u8 6#u8 6#u8]
    remainder := ⟨[], by scalar_tac⟩ }

private theorem releasedRows64ChunkLists (positive : 0 < (4#usize).val) :
    List.toChunksExact (4#usize).val positive releasedRowGroups64.val =
      ([[0#u8, 0#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 2#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 1#u8, 2#u8],
        [0#u8, 2#u8, 0#u8, 1#u8],
        [1#u8, 3#u8, 3#u8, 3#u8],
        [3#u8, 4#u8, 5#u8, 6#u8],
        [6#u8, 6#u8, 6#u8, 6#u8],
        [6#u8, 6#u8, 6#u8, 6#u8]], []) := by
  have proofEq : positive = (by scalar_tac : 0 < (4#usize).val) :=
    Subsingleton.elim _ _
  subst positive
  simp [releasedRowGroups64, List.toChunksExact]

private theorem releasedRows16ChunkLists (positive : 0 < (4#usize).val) :
    List.toChunksExact (4#usize).val positive releasedRowGroups16.val =
      ([[0#u8, 1#u8, 1#u8, 1#u8],
        [1#u8, 2#u8, 1#u8, 1#u8],
        [1#u8, 1#u8, 2#u8, 3#u8],
        [4#u8, 5#u8, 6#u8, 6#u8]], []) := by
  have proofEq : positive = (by scalar_tac : 0 < (4#usize).val) :=
    Subsingleton.elim _ _
  subst positive
  simp [releasedRowGroups16, List.toChunksExact]

theorem releasedRows64ChunksExact :
    core.slice.Slice.chunks_exact (alloc.vec.Vec.deref releasedRowGroups64)
        4#usize = ok releasedRows64Iterator := by
  unfold core.slice.Slice.chunks_exact
  rw [dif_pos (by scalar_tac)]
  rfl

theorem releasedRows16ChunksExact :
    core.slice.Slice.chunks_exact (alloc.vec.Vec.deref releasedRowGroups16)
        4#usize = ok releasedRows16Iterator := by
  unfold core.slice.Slice.chunks_exact
  rw [dif_pos (by scalar_tac)]
  rfl

theorem releasedRows64IteratorValues :
    releasedRows64Iterator.chunks.map (fun chunk => chunk.val) =
      [[0#u8, 0#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 2#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 1#u8, 2#u8],
       [0#u8, 2#u8, 0#u8, 1#u8],
       [1#u8, 3#u8, 3#u8, 3#u8],
       [3#u8, 4#u8, 5#u8, 6#u8],
       [6#u8, 6#u8, 6#u8, 6#u8],
       [6#u8, 6#u8, 6#u8, 6#u8]] := by
  unfold releasedRows64Iterator
  have hchunks := congrArg (fun pair => pair.1)
    (releasedRows64ChunkLists (by scalar_tac : 0 < (4#usize).val))
  simpa [alloc.vec.Vec.deref] using hchunks

theorem releasedRows16IteratorValues :
    releasedRows16Iterator.chunks.map (fun chunk => chunk.val) =
      [[0#u8, 1#u8, 1#u8, 1#u8],
       [1#u8, 2#u8, 1#u8, 1#u8],
       [1#u8, 1#u8, 2#u8, 3#u8],
       [4#u8, 5#u8, 6#u8, 6#u8]] := by
  unfold releasedRows16Iterator
  have hchunks := congrArg (fun pair => pair.1)
    (releasedRows16ChunkLists (by scalar_tac : 0 < (4#usize).val))
  simpa [alloc.vec.Vec.deref] using hchunks

private theorem sliceListVal_injective {T : Type}
    {left right : List (Slice T)}
    (sameValues : left.map (fun slice => slice.val) =
      right.map (fun slice => slice.val)) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all
  | cons head tail induction =>
      cases right with
      | nil => simp at sameValues
      | cons head' tail' =>
          simp only [List.map_cons, List.cons.injEq] at sameValues
          obtain ⟨sameHead, sameTail⟩ := sameValues
          have headEq : head = head' := by
            apply Subtype.ext
            exact sameHead
          rw [headEq]
          exact congrArg (List.cons head') (induction sameTail)

private theorem releasedRows64IteratorRemainder :
    releasedRows64Iterator.remainder.val = [] := by
  unfold releasedRows64Iterator
  have hremainder := congrArg (fun pair => pair.2)
    (releasedRows64ChunkLists (by scalar_tac : 0 < (4#usize).val))
  simpa [alloc.vec.Vec.deref] using hremainder

private theorem releasedRows16IteratorRemainder :
    releasedRows16Iterator.remainder.val = [] := by
  unfold releasedRows16Iterator
  have hremainder := congrArg (fun pair => pair.2)
    (releasedRows16ChunkLists (by scalar_tac : 0 < (4#usize).val))
  simpa [alloc.vec.Vec.deref] using hremainder

private theorem chunksExact_ext {T : Type}
    {left right : core.slice.iter.ChunksExact T}
    (sameChunks : left.chunks = right.chunks)
    (sameRemainder : left.remainder = right.remainder) :
    left = right := by
  cases left
  cases right
  simp_all

theorem releasedRows64IteratorExplicit :
    releasedRows64Iterator = releasedRows64ExplicitIterator := by
  apply chunksExact_ext
  · apply sliceListVal_injective
    rw [releasedRows64IteratorValues]
    rfl
  · apply Subtype.ext
    exact releasedRows64IteratorRemainder

theorem releasedRows16IteratorExplicit :
    releasedRows16Iterator = releasedRows16ExplicitIterator := by
  apply chunksExact_ext
  · apply sliceListVal_injective
    rw [releasedRows16IteratorValues]
    rfl
  · apply Subtype.ext
    exact releasedRows16IteratorRemainder

theorem releasedRows64ChunksExactExplicit :
    core.slice.Slice.chunks_exact (alloc.vec.Vec.deref releasedRowGroups64)
        4#usize = ok releasedRows64ExplicitIterator := by
  rw [releasedRows64ChunksExact, releasedRows64IteratorExplicit]

theorem releasedRows16ChunksExactExplicit :
    core.slice.Slice.chunks_exact (alloc.vec.Vec.deref releasedRowGroups16)
        4#usize = ok releasedRows16ExplicitIterator := by
  rw [releasedRows16ChunksExact, releasedRows16IteratorExplicit]

theorem releasedFirstTupleCount : releasedFirstTuples.length = 7 := by rfl

theorem releasedSecondTupleCount : releasedSecondTuples.length = 4 := by rfl

end AspisV5RelationLinkedGroupedRows
