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

theorem releasedFirstTupleCount : releasedFirstTuples.length = 7 := by rfl

theorem releasedSecondTupleCount : releasedSecondTuples.length = 4 := by rfl

end AspisV5RelationLinkedGroupedRows
