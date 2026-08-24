import V5CompactFoldSourceModel

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5CompactFoldIteratorSemantics

open V5RelationCompactFoldGenerated
open AspisV5RelationCompactFoldKernelProof

abbrev Iter := core.slice.iter.IterMut

theorem next_in_bounds {T : Type} (iter : Iter T)
    (h : iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok
        (some iter.slice[iter.i],
          { iter with i := iter.i + 1 },
          fun iter' value =>
            match value with
            | none => iter'
            | some value =>
                { iter' with slice := iter'.slice.setAtNat iter.i value }) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_pos h]
  rfl

theorem next_exhausted {T : Type} (iter : Iter T)
    (h : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (none, iter, fun iter' _ => iter') := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_neg h]

abbrev Raw := V5RelationCompactFoldGenerated.aspis_core.field.QM31
abbrev Prepared :=
  V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier
abbrev Block :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalBlock
abbrev BlockIter := core.slice.iter.IterMut Block
abbrev Back := BlockIter → BlockIter
abbrev FoldFlow := ControlFlow (BlockIter × Back × Std.U8) (Std.U8 × Back)

def zeroBodyModel
    (prepared : Array Prepared 3#usize) (iter : BlockIter) (back : Back) :
    Result FoldFlow := do
  let (value, iterAfter, nextBack) ←
    core.slice.iter.IteratorIterMut.next iter
  match value with
  | none => ok (done (0#u8, fun output => back (nextBack output none)))
  | some block =>
      AspisV5RelationCompactFoldKernelProof.continueWith
        iterAfter nextBack back 0#u8
        (AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared block)

theorem generated_zero_body_eq_model
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back 0#u8 =
      zeroBodyModel prepared iter back := by
  unfold zeroBodyModel
  generalize nextRun :
    core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      simp only [bind_tc_fail]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      simp only [bind_tc_div]
      unfold
        V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold
            V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          rw [
            AspisV5RelationCompactFoldKernelProof.extracted_fold_zero_block_exact
              alpha alpha2 alpha3 prepared iter iterAfter nextBack back block
              nextRun,
            AspisV5RelationCompactFoldKernelProof.foldZeroStep_eq_continueWith]
          rfl

def zeroLoopBody (prepared : Array Prepared 3#usize)
    (state : BlockIter × Back × Std.U8) :
    Result (ControlFlow (BlockIter × Back × Std.U8) (Std.U8 × Back)) :=
  zeroBodyModel prepared state.1 state.2.1

def zeroBackN : Nat → Array Prepared 3#usize → BlockIter → Back →
    Result (Std.U8 × Back)
  | 0, _, _, back => ok (0#u8, back)
  | remaining + 1, prepared, iter, back => do
      let (value, iterAfter, nextBack) ←
        core.slice.iter.IteratorIterMut.next iter
      match value with
      | none => fail panic
      | some block =>
          let updated ←
            AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared block
          zeroBackN remaining prepared iterAfter
            (fun output => back (nextBack output (some updated)))

theorem zero_loop_eq_zeroBackN
    (remaining : Nat) (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    Aeneas.Std.loop (zeroLoopBody prepared) (iter, back, 0#u8) =
      zeroBackN remaining prepared iter back := by
  induction remaining generalizing iter back with
  | zero =>
      have exhausted : ¬ iter.i < iter.slice.len := by
        change ¬ iter.i < iter.slice.val.length
        omega
      rw [Aeneas.Std.loop.eq_def]
      simp only [zeroLoopBody, zeroBodyModel, next_exhausted iter exhausted,
        bind_tc_ok, zeroBackN]
  | succ remaining inductionHypothesis =>
      have inBounds : iter.i < iter.slice.len := by
        change iter.i < iter.slice.val.length
        omega
      have nextLength :
          ({ iter with i := iter.i + 1 } : BlockIter).i + remaining =
            ({ iter with i := iter.i + 1 } : BlockIter).slice.val.length := by
        simp only
        omega
      rw [Aeneas.Std.loop.eq_def]
      simp only [zeroLoopBody, zeroBodyModel, zeroBackN,
        next_in_bounds iter inBounds, bind_tc_ok]
      generalize blockRun :
        AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared
          iter.slice[iter.i] = blockResult
      cases blockResult with
      | fail error =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_fail]
      | div =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_div]
      | ok updated =>
          simp only [bind_tc_ok]
          exact inductionHypothesis
            ({ iter with i := iter.i + 1 })
            (fun (output : BlockIter) =>
              back
                ((fun (iter' : BlockIter) (value : Option Block) =>
                  match value with
                  | none => iter'
                  | some value =>
                      { iter' with
                        slice := iter'.slice.setAtNat iter.i value })
                output (some updated)))
            nextLength

def generatedZeroLoopBody
    (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (state : BlockIter × Back × Std.U8) :
    Result (ControlFlow (BlockIter × Back × Std.U8) (Std.U8 × Back)) :=
  V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
    alpha alpha2 alpha3 prepared state.1 state.2.1 state.2.2

theorem generated_zero_loop_eq_zeroBackN_aux
    (remaining : Nat) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    Aeneas.Std.loop
        (generatedZeroLoopBody alpha alpha2 alpha3 prepared)
        (iter, back, 0#u8) =
      zeroBackN remaining prepared iter back := by
  induction remaining generalizing iter back with
  | zero =>
      have exhausted : ¬ iter.i < iter.slice.len := by
        change ¬ iter.i < iter.slice.val.length
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedZeroLoopBody
      rw [generated_zero_body_eq_model]
      simp only [zeroBodyModel, next_exhausted iter exhausted, bind_tc_ok,
        zeroBackN]
  | succ remaining inductionHypothesis =>
      have inBounds : iter.i < iter.slice.len := by
        change iter.i < iter.slice.val.length
        omega
      have nextLength :
          ({ iter with i := iter.i + 1 } : BlockIter).i + remaining =
            ({ iter with i := iter.i + 1 } : BlockIter).slice.val.length := by
        simp only
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedZeroLoopBody
      rw [generated_zero_body_eq_model]
      simp only [zeroBodyModel, zeroBackN,
        next_in_bounds iter inBounds, bind_tc_ok]
      generalize blockRun :
        AspisV5RelationCompactFoldKernelProof.foldZeroBlock prepared
          iter.slice[iter.i] = blockResult
      cases blockResult with
      | fail error =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_fail]
      | div =>
          simp only [AspisV5RelationCompactFoldKernelProof.continueWith,
            bind_tc_div]
      | ok updated =>
          simp only [bind_tc_ok]
          exact inductionHypothesis
            ({ iter with i := iter.i + 1 })
            (fun (output : BlockIter) =>
              back
                ((fun (iter' : BlockIter) (value : Option Block) =>
                  match value with
                  | none => iter'
                  | some value =>
                      { iter' with
                        slice := iter'.slice.setAtNat iter.i value })
                output (some updated)))
            nextLength

theorem generated_zero_loop_eq_zeroBackN
    (remaining : Nat) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize)
    (iter : BlockIter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
        iter back 0#u8 alpha alpha2 alpha3 prepared =
      zeroBackN remaining prepared iter back := by
  unfold
    V5RelationCompactFoldGenerated.v5_cu_probe.CompactBTerminalWeights.fold_loop
  exact generated_zero_loop_eq_zeroBackN_aux remaining alpha alpha2 alpha3
    prepared iter back lengthExact

end V5CompactFoldIteratorSemantics
