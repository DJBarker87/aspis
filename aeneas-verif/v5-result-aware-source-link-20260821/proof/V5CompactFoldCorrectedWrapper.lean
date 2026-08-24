import V5RelationCompactFoldGenerated

/-!
# Correct compact-fold outer wrapper

The pinned extraction contains the complete mutable loop body, but the old
hand-written outer assembly anchored the returned write-back function in an
empty iterator.  `List.set` does not extend an empty list, so that assembly
discarded every block write and caused `Array.from_slice` to return the
original array.

This file leaves the generated artifact unchanged.  It records the failure in
a small theorem and defines the source-shaped assembly with the write-back
anchored in the original iterator.  The iterator index is irrelevant to the
array hand-back: only its reconstructed slice is consumed.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CompactFoldCorrectedWrapper

open V5RelationCompactFoldGenerated

abbrev Raw := aspis_core.field.QM31
abbrev Block := v5_cu_probe.CompactBTerminalBlock
abbrev State := v5_cu_probe.CompactBTerminalWeights
abbrev Iter := core.slice.iter.IterMut Block

def emptyTerminal : Iter :=
  { slice := Array.to_slice (Array.make 0#usize []) }

def oneWriteBack (replacement : Block) (iter : Iter) : Iter :=
  { iter with slice := iter.slice.setAtNat 0 replacement }

/-- The old empty anchor loses even one explicit block update.  This is the
minimal regression theorem for the proof-artifact bug; it says nothing about
the unchanged Rust implementation. -/
theorem empty_anchor_discards_one_write
    (blocks : Array Block 10#usize) (replacement : Block) :
    Array.from_slice blocks
      (oneWriteBack replacement emptyTerminal).slice = blocks := by
  simp [oneWriteBack, emptyTerminal, Slice.setAtNat, Array.to_slice,
    Array.from_slice, Array.make]

/-- Exact source-shaped assembly of `CompactBTerminalWeights::fold` around
the extracted loop. -/
def fold (self : State) (alpha : Raw) : Result State := do
  let alpha2 ← aspis_core.field.QM31.square alpha
  let alpha3 ← aspis_core.field.QM31.mul alpha2 alpha
  let prepared0 ← aspis_core.field.PreparedQm31Multiplier.new alpha3
  let prepared1 ← aspis_core.field.PreparedQm31Multiplier.new alpha2
  let prepared2 ← aspis_core.field.PreparedQm31Multiplier.new alpha
  let preparedPowers :=
    Array.make 3#usize [prepared0, prepared1, prepared2]
  let (iter, intoIterBack) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
      self.blocks
  let (_, loopBack) ←
    v5_cu_probe.CompactBTerminalWeights.fold_loop iter (fun current => current)
      self.folds alpha alpha2 alpha3 preparedPowers
  let blocks := intoIterBack (loopBack iter)
  let deltaFactor ←
    match self.folds with
    | 0#uscalar => ok aspis_core.field.QM31.ONE
    | 1#uscalar => ok aspis_core.field.QM31.ONE
    | 2#uscalar => ok alpha2
    | 3#uscalar => ok alpha
    | _ => fail panic
  let deltaHalf ← aspis_core.field.QM31.half deltaFactor
  let deltaQuarter ← aspis_core.field.QM31.half deltaHalf
  let deltaScale ←
    aspis_core.field.QM31.mul self.delta_scale deltaQuarter
  let folds ← lift (Std.U8.wrapping_add self.folds 1#u8)
  ok { blocks, delta_scale := deltaScale, folds }

end V5CompactFoldCorrectedWrapper
