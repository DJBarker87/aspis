import V5CompactFoldExactUnrolledStateBridge
import V5CompactFoldIteratorSemantics

namespace AspisV5CompactFoldExactIteratorBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5CompactFoldExactCallerBridge

abbrev Raw := ExactRaw
abbrev Prepared :=
  V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier
abbrev Block := ExactBlock
abbrev Iter := core.slice.iter.IterMut Block
abbrev Back := Iter → Iter
abbrev FoldFlow := ControlFlow (Iter × Back × Std.U8) (Std.U8 × Iter)

def sourceBodyModel (folds : Std.U8) (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) (iter : Iter) (back : Back) :
    Result FoldFlow := do
  let (value, iterAfter, nextBack) ←
    core.slice.iter.IteratorIterMut.next iter
  match value with
  | none => ok (done (folds, back (nextBack iterAfter none)))
  | some block => do
      let updated ← AspisV5CompactFoldExactSource.foldBlock folds alpha
        alpha2 alpha3 prepared block
      ok (cont (iterAfter,
        fun output => back (nextBack output (some updated)), folds))

private theorem generated_zero_body_eq_source
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back (0#8#uscalar : Std.U8) =
      sourceBodyModel (0#8#uscalar : Std.U8) alpha alpha2 alpha3 prepared
        iter back := by
  unfold sourceBodyModel
  generalize nextRun : core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
          rw [AspisV5CompactFoldExactSource.foldBlock.eq_1]
          simp only [if_neg (by decide : (0#u8 : Std.U8) ≠ 2#u8)]
          simp only [bind_assoc, bind_tc_ok]
          rw [show (0#u8 : Std.U8) = (0#8#uscalar : Std.U8) by decide]

private theorem generated_one_body_eq_source
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back (1#8#uscalar : Std.U8) =
      sourceBodyModel (1#8#uscalar : Std.U8) alpha alpha2 alpha3 prepared
        iter back := by
  unfold sourceBodyModel
  generalize nextRun : core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
          rw [AspisV5CompactFoldExactSource.foldBlock.eq_2]
          simp only [bind_assoc, bind_tc_ok]
          rw [show (1#u8 : Std.U8) = (1#8#uscalar : Std.U8) by decide]

private theorem generated_two_body_eq_source
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back (2#8#uscalar : Std.U8) =
      sourceBodyModel (2#8#uscalar : Std.U8) alpha alpha2 alpha3 prepared
        iter back := by
  unfold sourceBodyModel
  generalize nextRun : core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
          rw [AspisV5CompactFoldExactSource.foldBlock.eq_3]
          simp only [if_true]
          generalize bitRun : lift (block.selector &&& 1#u8) = bitResult
          cases bitResult with
          | fail error => simp only [bitRun, bind_tc_fail]
          | div => simp only [bitRun, bind_tc_div]
          | ok lowBit =>
              simp only [bitRun, bind_tc_ok]
              by_cases even : lowBit = 0#u8
              · simp only [if_pos even, bind_assoc, bind_tc_ok]
                rw [show (2#u8 : Std.U8) =
                  (2#8#uscalar : Std.U8) by decide]
              · simp only [if_neg even, bind_assoc, bind_tc_ok]
                rw [show (2#u8 : Std.U8) =
                  (2#8#uscalar : Std.U8) by decide]

private theorem generated_three_body_eq_source
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back (3#8#uscalar : Std.U8) =
      sourceBodyModel (3#8#uscalar : Std.U8) alpha alpha2 alpha3 prepared
        iter back := by
  unfold sourceBodyModel
  generalize nextRun : core.slice.iter.IteratorIterMut.next iter = nextResult
  cases nextResult with
  | fail error =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_fail]
  | div =>
      unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
      simp only [nextRun, bind_tc_div]
  | ok result =>
      rcases result with ⟨value, iterAfter, nextBack⟩
      cases value with
      | none =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
      | some block =>
          unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
          simp only [nextRun, bind_tc_ok]
          rw [AspisV5CompactFoldExactSource.foldBlock.eq_4]
          simp only [if_neg (by decide : (3#u8 : Std.U8) ≠ 2#u8)]
          generalize shiftedRun :
            lift (Std.U8.wrapping_shr block.selector 1#u32) = shiftedResult
          cases shiftedResult with
          | fail error => simp only [shiftedRun, bind_tc_fail]
          | div => simp only [shiftedRun, bind_tc_div]
          | ok shifted =>
              simp only [shiftedRun, bind_tc_ok]
              generalize selectorRun : lift (shifted &&& 3#u8) = selectorResult
              cases selectorResult with
              | fail error => simp only [selectorRun, bind_tc_fail]
              | div => simp only [selectorRun, bind_tc_div]
              | ok selector =>
                  simp only [selectorRun, bind_tc_ok]
                  split <;> simp_all only [bind_assoc, bind_tc_ok,
                    bind_tc_fail,
                    show (3#u8 : Std.U8) =
                      (3#8#uscalar : Std.U8) by decide]

theorem generated_body_eq_source
    (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
        alpha alpha2 alpha3 prepared iter back folds =
      sourceBodyModel folds alpha alpha2 alpha3 prepared iter back := by
  have foldCases : folds.val = 0 ∨ folds.val = 1 ∨ folds.val = 2 ∨
      folds.val = 3 := by omega
  rcases foldCases with foldValue | foldValue | foldValue | foldValue
  · have foldExact : folds = (0#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 0
      exact foldValue
    subst folds
    exact generated_zero_body_eq_source alpha alpha2 alpha3 prepared iter back
  · have foldExact : folds = (1#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 1
      exact foldValue
    subst folds
    exact generated_one_body_eq_source alpha alpha2 alpha3 prepared iter back
  · have foldExact : folds = (2#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 2
      exact foldValue
    subst folds
    exact generated_two_body_eq_source alpha alpha2 alpha3 prepared iter back
  · have foldExact : folds = (3#8#uscalar : Std.U8) := by
      apply UScalar.eq_of_val_eq
      change folds.val = 3
      exact foldValue
    subst folds
    exact generated_three_body_eq_source alpha alpha2 alpha3 prepared iter back

def sourceIterN : Nat → Std.U8 → Raw → Raw → Raw →
    Array Prepared 3#usize → Iter → Back → Result (Std.U8 × Iter)
  | 0, folds, _, _, _, _, iter, back => ok (folds, back iter)
  | remaining + 1, folds, alpha, alpha2, alpha3, prepared, iter, back => do
      let (value, iterAfter, nextBack) ←
        core.slice.iter.IteratorIterMut.next iter
      match value with
      | none => fail panic
      | some block => do
          let updated ← AspisV5CompactFoldExactSource.foldBlock folds alpha
            alpha2 alpha3 prepared block
          sourceIterN remaining folds alpha alpha2 alpha3 prepared iterAfter
            (fun output => back (nextBack output (some updated)))

def generatedLoopBody (alpha alpha2 alpha3 : Raw)
    (prepared : Array Prepared 3#usize) (state : Iter × Back × Std.U8) :
    Result FoldFlow :=
  V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop.body
    alpha alpha2 alpha3 prepared state.1 state.2.1 state.2.2

theorem generated_loop_eq_sourceIterN_aux
    (remaining : Nat) (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    Aeneas.Std.loop (generatedLoopBody alpha alpha2 alpha3 prepared)
        (iter, back, folds) =
      sourceIterN remaining folds alpha alpha2 alpha3 prepared iter back := by
  induction remaining generalizing iter back with
  | zero =>
      have exhausted : ¬ iter.i < iter.slice.len := by
        change ¬ iter.i < iter.slice.val.length
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedLoopBody
      rw [generated_body_eq_source folds foldBound]
      simp only [sourceBodyModel,
        V5CompactFoldIteratorSemantics.next_exhausted iter exhausted,
        bind_tc_ok, sourceIterN]
  | succ remaining inductionHypothesis =>
      have inBounds : iter.i < iter.slice.len := by
        change iter.i < iter.slice.val.length
        omega
      have nextLength :
          ({ iter with i := iter.i + 1 } : Iter).i + remaining =
            ({ iter with i := iter.i + 1 } : Iter).slice.val.length := by
        simp only
        omega
      rw [Aeneas.Std.loop.eq_def]
      unfold generatedLoopBody
      rw [generated_body_eq_source folds foldBound]
      simp only [sourceBodyModel, sourceIterN,
        V5CompactFoldIteratorSemantics.next_in_bounds iter inBounds,
        bind_tc_ok]
      generalize blockRun :
        AspisV5CompactFoldExactSource.foldBlock folds alpha alpha2 alpha3
          prepared iter.slice[iter.i] = blockResult
      cases blockResult with
      | fail error => simp only [bind_tc_fail]
      | div => simp only [bind_tc_div]
      | ok updated =>
          simp only [bind_tc_ok]
          exact inductionHypothesis
            ({ iter with i := iter.i + 1 })
            (fun output =>
              back
                ((fun (iter' : Iter) (value : Option Block) =>
                  match value with
                  | none => iter'
                  | some value =>
                      { iter' with
                        slice := iter'.slice.setAtNat iter.i value })
                output (some updated)))
            nextLength

theorem generated_loop_eq_sourceIterN
    (remaining : Nat) (folds : Std.U8) (foldBound : folds.val < 4)
    (alpha alpha2 alpha3 : Raw) (prepared : Array Prepared 3#usize)
    (iter : Iter) (back : Back)
    (lengthExact : iter.i + remaining = iter.slice.val.length) :
    V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop
        iter back folds alpha alpha2 alpha3 prepared =
      sourceIterN remaining folds alpha alpha2 alpha3 prepared iter back := by
  unfold V5RelationCompactFoldGeneratedExact.v5_cu_probe.CompactBTerminalWeights.fold_loop
  exact generated_loop_eq_sourceIterN_aux remaining folds foldBound alpha
    alpha2 alpha3 prepared iter back lengthExact

#print axioms generated_body_eq_source
#print axioms generated_loop_eq_sourceIterN

end AspisV5CompactFoldExactIteratorBridge
