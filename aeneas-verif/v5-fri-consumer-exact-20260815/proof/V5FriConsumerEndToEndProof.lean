import V5FriConsumerExactProof

/-!
# End-to-end proof for the unchanged production FRI consumer

This module peels the exact Charon/Aeneas translation of
`check_v5_fri_queries` from its public entry point through all four loops.
Successful acceptance yields the actual read performed at every enumerated
query position.  No model-side trace is substituted for the production loop
state.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5FriConsumerExactProof

open V5FriConsumerExact

@[simp] theorem from_residual_ne_ok
    {T E F : Type} (convert : core.convert.From F E)
    (residual : core.result.Result core.convert.Infallible E) (value : T) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T convert residual ≠ .ok (.Ok value) := by
  cases residual with
  | Ok impossible => exact core.convert.Infallible.rec _ impossible
  | Err error =>
    unfold core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    cases hconvert : convert.from error <;> simp [hconvert]

private theorem enumerate_slice_at_next_run
    {T : Type} [Inhabited T]
    (values : Slice T) (position : Std.Usize)
    (hposition : position.val < values.val.length) :
    ∃ nextPosition : Std.Usize,
      nextPosition.val = position.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter T)
          (enumerateSliceAt values position) =
        .ok (some (position, values[position.val]),
          enumerateSliceAt values nextPosition) := by
  have hactive : position.val < values.len.val := by simpa using hposition
  have hinner :
      (core.iter.traits.iterator.IteratorSliceIter T).next
          ({ slice := values, i := position.val } : core.slice.iter.Iter T) =
        .ok (some values[position.val],
          ({ slice := values, i := position.val + 1 } :
            core.slice.iter.Iter T)) := by
    change core.slice.iter.IteratorSliceIter.next
      ({ slice := values, i := position.val } : core.slice.iter.Iter T) = _
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dif_pos hactive]
  unfold enumerateSliceAt
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  rw [hinner]
  simp only [bind_tc_ok]
  have hadd := @UScalar.add_equiv .Usize position 1#usize
  split at hadd
  · rename_i nextPosition hcount
    refine ⟨nextPosition, hadd.2.1, ?_⟩
    simp only [hcount, bind_tc_ok]
    simp [hadd.2.1]
    rfl
  · simp [UScalar.inBounds] at hadd
    have hlength := Slice.length_ineq values
    exfalso
    scalar_tac
  · contradiction

theorem later_cont_iter_exact
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext iterOut :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried carriedOut ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext))
    (hrun :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer pending
          iter carried = .ok (.cont (iterOut, carriedOut))) :
    iterOut = iterNext := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  repeat' first
    | split at hrun
    | simp_all [Bind.bind, Aeneas.Std.bind, Std.lift,
        core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from]

theorem inner_active_body_ne_completed
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext)) :
    fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
        laterIndices finalPolynomial coordinates alphaPowers layer pending
        iter carried ≠ .ok (.done (coordinatesOut, pendingOut, 1#u32)) := by
  intro hrun
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  repeat' first
    | split at hrun
    | simp_all [Bind.bind, Aeneas.Std.bind, Std.lift,
        core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from]

theorem inner_completed_loop_head
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext))
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0 iter later
          laterIndices finalPolynomial coordinates alphaPowers layer carried
          pending = .ok (coordinatesOut, pendingOut, 1#u32)) :
    ∃ carriedNext,
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer pending
          iter carried = .ok (.cont (iterNext, carriedNext)) ∧
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0 iterNext later
          laterIndices finalPolynomial coordinates alphaPowers layer
          carriedNext pending = .ok (coordinatesOut, pendingOut, 1#u32) := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0 at hloop
  rw [loop.eq_def] at hloop
  simp only at hloop
  generalize hbody :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
        laterIndices finalPolynomial coordinates alphaPowers layer pending iter
        carried = bodyResult at hloop
  cases bodyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | ok flow =>
    cases flow with
    | cont nextState =>
      rcases nextState with ⟨nextIter, carriedNext⟩
      simp only [bind_tc_ok] at hloop
      have hiter := later_cont_iter_exact later laterIndices
        finalPolynomial coordinates alphaPowers layer pending iter iterNext
        nextIter carried carriedNext ordinal index hnext hbody
      subst nextIter
      refine ⟨carriedNext, ?_, hloop⟩
      simpa using hbody
    | done output =>
      rcases output with ⟨coordinatesDone, pendingDone, flagDone⟩
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at hloop
      have hflag : flagDone = 1#u32 := hloop.2.2
      have hdone :
          fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
            laterIndices finalPolynomial coordinates alphaPowers layer pending
            iter carried =
              .ok (.done (coordinatesDone, pendingDone, 1#u32)) := by
        simpa [hflag] using hbody
      exact (inner_active_body_ne_completed later laterIndices
        finalPolynomial coordinates coordinatesDone alphaPowers layer pending
        pendingDone iter iterNext carried ordinal index hnext hdone).elim

theorem later_completed_loop_reads_target
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize) (hlayer : layer < 2#usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (values : Slice Std.U32) (current target : Std.Usize)
    (carried : Std.Usize)
    (horder : current.val ≤ target.val)
    (htarget : target.val < values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0
          (enumerateSliceAt values current) later laterIndices finalPolynomial
          coordinates alphaPowers layer carried pending =
        .ok (coordinatesOut, pendingOut, 1#u32)) :
    ∃ carriedAt : Std.Usize, ∃ nextPosition : Std.Usize,
      nextPosition.val = target.val + 1 ∧
      Nonempty (LaterBodyReadEvidence later laterIndices layer target carriedAt
        values[target.val]) := by
  have hcurrent : current.val < values.val.length := by omega
  obtain ⟨nextPosition, hnextValue, hnext⟩ :=
    enumerate_slice_at_next_run values current hcurrent
  obtain ⟨carriedNext, hbody, hloopNext⟩ :=
    inner_completed_loop_head later laterIndices finalPolynomial
      coordinates coordinatesOut alphaPowers layer pending pendingOut
      (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
      carried current values[current.val] hnext hloop
  have hevidence := production_later_body_cont_reads later laterIndices
    finalPolynomial coordinates alphaPowers layer hlayer pending
    (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
    (enumerateSliceAt values nextPosition) carried carriedNext current
    values[current.val] hnext hbody
  by_cases heq : current.val = target.val
  · have hscalar : current = target := UScalar.eq_of_val_eq heq
    subst target
    exact ⟨carried, nextPosition, hnextValue, hevidence⟩
  · apply later_completed_loop_reads_target later laterIndices
      finalPolynomial coordinates coordinatesOut alphaPowers layer hlayer
      pending pendingOut values nextPosition target carriedNext
    · rw [hnextValue]
      omega
    · exact hloopNext
termination_by target.val - current.val
decreasing_by
  rw [hnextValue]
  omega

theorem terminal_completed_loop_reads_target
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize) (hlayer : ¬layer < 2#usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (values : Slice Std.U32) (current target : Std.Usize)
    (carried : Std.Usize)
    (horder : current.val ≤ target.val)
    (htarget : target.val < values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0
          (enumerateSliceAt values current) later laterIndices finalPolynomial
          coordinates alphaPowers layer carried pending =
        .ok (coordinatesOut, pendingOut, 1#u32)) :
    ∃ nextPosition : Std.Usize,
      nextPosition.val = target.val + 1 ∧
      Nonempty (TerminalBodyReadEvidence later layer target) := by
  have hcurrent : current.val < values.val.length := by omega
  obtain ⟨nextPosition, hnextValue, hnext⟩ :=
    enumerate_slice_at_next_run values current hcurrent
  obtain ⟨carriedNext, hbody, hloopNext⟩ :=
    inner_completed_loop_head later laterIndices finalPolynomial
      coordinates coordinatesOut alphaPowers layer pending pendingOut
      (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
      carried current values[current.val] hnext hloop
  have hevidence := production_terminal_body_cont_reads later laterIndices
    finalPolynomial coordinates alphaPowers layer hlayer pending
    (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
    (enumerateSliceAt values nextPosition) carried carriedNext current
    values[current.val] hnext hbody
  by_cases heq : current.val = target.val
  · have hscalar : current = target := UScalar.eq_of_val_eq heq
    subst target
    exact ⟨nextPosition, hnextValue, hevidence⟩
  · apply terminal_completed_loop_reads_target later laterIndices
      finalPolynomial coordinates coordinatesOut alphaPowers layer hlayer
      pending pendingOut values nextPosition target carriedNext
    · rw [hnextValue]
      omega
    · exact htarget
    · exact hloopNext
termination_by target.val - current.val
decreasing_by
  rw [hnextValue]
  omega

def range3At (start : Std.Usize) : core.ops.range.Range Std.Usize :=
  { start, «end» := 3#usize }

theorem range3_next_some
    (start : Std.Usize) (hstart : start.val < 3) :
    ∃ next : Std.Usize,
      next.val = start.val + 1 ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          (range3At start) = .ok (some start, range3At next) := by
  have hspec := core.iter.range.IteratorRange.next_Usize_some_spec
    (range3At start) (by simpa [range3At] using hstart)
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨⟨option, nextRange⟩, hnext, hoption, hnextStart, hnextEnd⟩
  subst option
  let next : Std.Usize := nextRange.start
  have hrange : nextRange = range3At next := by
    cases nextRange
    simp only [range3At, core.ops.range.Range.mk.injEq]
    exact ⟨rfl, hnextEnd⟩
  exact ⟨next, hnextStart, by simpa [range3At, hrange] using hnext⟩

theorem range3_next_none :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        (range3At 3#usize) = .ok (none, range3At 3#usize) := by
  have hspec := core.iter.range.IteratorRange.next_Usize_none_spec
    (range3At 3#usize) (by simp [range3At])
  rcases Aeneas.Std.WP.spec_imp_exists hspec with
    ⟨⟨option, nextRange⟩, hnext, hoption, hrange⟩
  simpa [hoption, hrange] using hnext

theorem slice_enumerate_run (values : Slice Std.U32) :
    (do
      let inner ← core.slice.Slice.iter values
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U32) inner) =
      .ok (enumerateSliceAt values 0#usize) := by
  simp [core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default,
    enumerateSliceAt]

theorem enumerate_slice_at_next_none
    (values : Slice Std.U32) (position : Std.Usize)
    (hposition : values.val.length ≤ position.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Std.U32)
        (enumerateSliceAt values position) =
      .ok (none, enumerateSliceAt values position) := by
  have hinner :
      (core.iter.traits.iterator.IteratorSliceIter Std.U32).next
          ({ slice := values, i := position.val } :
            core.slice.iter.Iter Std.U32) =
        .ok (none,
          ({ slice := values, i := position.val } :
            core.slice.iter.Iter Std.U32)) := by
    change core.slice.iter.IteratorSliceIter.next
      ({ slice := values, i := position.val } : core.slice.iter.Iter Std.U32) = _
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dif_neg (by simpa [Slice.len] using hposition)]
  unfold enumerateSliceAt
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  rw [hinner]
  rfl

theorem inner_completed_preserves_constants
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (values : Slice Std.U32) (current carried : Std.Usize)
    (hcurrent : current.val ≤ values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0
          (enumerateSliceAt values current) later laterIndices finalPolynomial
          coordinates alphaPowers layer carried pending =
        .ok (coordinatesOut, pendingOut, 1#u32)) :
    coordinatesOut = coordinates ∧ pendingOut = pending := by
  by_cases hactive : current.val < values.val.length
  · obtain ⟨nextPosition, hnextValue, hnext⟩ :=
      enumerate_slice_at_next_run values current hactive
    obtain ⟨carriedNext, _hbody, hloopNext⟩ :=
      inner_completed_loop_head later laterIndices finalPolynomial
        coordinates coordinatesOut alphaPowers layer pending pendingOut
        (enumerateSliceAt values current)
        (enumerateSliceAt values nextPosition) carried current
        values[current.val] hnext hloop
    apply inner_completed_preserves_constants later laterIndices
      finalPolynomial coordinates coordinatesOut alphaPowers layer pending
      pendingOut values nextPosition carriedNext
    · rw [hnextValue]
      omega
    · exact hloopNext
  · have hnone := enumerate_slice_at_next_none values current (by omega)
    unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0 at hloop
    rw [loop.eq_def] at hloop
    simp only at hloop
    unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hloop
    rw [hnone] at hloop
    simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at hloop
    exact ⟨hloop.1.symm, hloop.2.1.symm⟩
termination_by values.val.length - current.val
decreasing_by
  rw [hnextValue]
  omega

theorem inner_active_body_ne_accepting_done
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried ordinal : Std.Usize) (index : Std.U32)
    (sink : fri_checks.V5FriCheckSink) (flag : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext)) :
    fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
        laterIndices finalPolynomial coordinates alphaPowers layer pending
        iter carried ≠
      .ok (.done (coordinatesOut, some (.Ok sink), flag)) := by
  intro hrun
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  repeat' first
    | split at hrun
    | simp_all [Bind.bind, Aeneas.Std.bind, Std.lift,
        core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        from_residual_ne_ok]

theorem inner_accepting_result_has_completed_flag
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (values : Slice Std.U32) (current carried : Std.Usize)
    (sink : fri_checks.V5FriCheckSink) (flag : Std.U32)
    (hcurrent : current.val ≤ values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0
          (enumerateSliceAt values current) later laterIndices finalPolynomial
          coordinates alphaPowers layer carried none =
        .ok (coordinatesOut, some (.Ok sink), flag)) :
    flag = 1#u32 := by
  by_cases hactive : current.val < values.val.length
  · obtain ⟨nextPosition, hnextValue, hnext⟩ :=
      enumerate_slice_at_next_run values current hactive
    unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0 at hloop
    rw [loop.eq_def] at hloop
    simp only at hloop
    generalize hbody :
        fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer none
          (enumerateSliceAt values current) carried = bodyResult at hloop
    cases bodyResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
    | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
    | ok flow =>
      cases flow with
      | cont nextState =>
        rcases nextState with ⟨nextIter, carriedNext⟩
        simp only [bind_tc_ok] at hloop
        have hiter := later_cont_iter_exact later laterIndices
          finalPolynomial coordinates alphaPowers layer none
          (enumerateSliceAt values current)
          (enumerateSliceAt values nextPosition) nextIter carried carriedNext
          current values[current.val] hnext hbody
        subst nextIter
        apply inner_accepting_result_has_completed_flag later
          laterIndices finalPolynomial coordinates coordinatesOut alphaPowers
          layer values nextPosition carriedNext sink flag
        · rw [hnextValue]
          omega
        · exact hloop
      | done output =>
        rcases output with ⟨coordinatesDone, pendingDone, flagDone⟩
        simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at hloop
        have hpending : pendingDone = some (.Ok sink) := hloop.2.1
        have hdone :
            fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
              laterIndices finalPolynomial coordinates alphaPowers layer none
              (enumerateSliceAt values current) carried =
              .ok (.done (coordinatesDone, some (.Ok sink), flagDone)) := by
          simpa [hpending] using hbody
        exact (inner_active_body_ne_accepting_done later laterIndices
          finalPolynomial coordinates coordinatesDone alphaPowers layer none
          (enumerateSliceAt values current)
          (enumerateSliceAt values nextPosition) carried current
          values[current.val] sink flagDone hnext hdone).elim
  · have hnone := enumerate_slice_at_next_none values current (by omega)
    unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0 at hloop
    rw [loop.eq_def] at hloop
    simp only at hloop
    unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hloop
    rw [hnone] at hloop
    simp at hloop
termination_by values.val.length - current.val
decreasing_by
  rw [hnextValue]
  omega

theorem outer_body_cont_exposes_completed_inner
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (folded : aspis_core.field.QM31)
    (range rangeNext rangeOut : core.ops.range.Range Std.Usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (layer : Std.Usize)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some layer, rangeNext))
    (hrun :
      fri_checks.check_v5_fri_queries_loop0_loop0.body later laterIndices
          finalPolynomial alphaPowers folded range coordinates pending =
        .ok (.cont (rangeOut, coordinatesOut, pendingOut))) :
    rangeOut = rangeNext ∧
      ∃ indices : alloc.vec.Vec Std.U32,
        Array.index_usize laterIndices layer = .ok indices ∧
        fri_checks.check_v5_fri_queries_loop0_loop0_loop0
            (enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize)
            later laterIndices finalPolynomial coordinates alphaPowers layer
            0#usize pending = .ok (coordinatesOut, pendingOut, 1#u32) := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hindices : Array.index_usize laterIndices layer = indexResult
    at hrun
  cases indexResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok indices =>
    simp only [bind_tc_ok] at hrun
    generalize hslice :
        core.slice.Slice.iter (alloc.vec.Vec.deref indices) = sliceResult
      at hrun
    cases sliceResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok sliceIter =>
      simp only [bind_tc_ok] at hrun
      have hsliceExact : sliceIter =
          ({ slice := alloc.vec.Vec.deref indices, i := 0 } :
            core.slice.iter.Iter Std.U32) := by
        simpa [core.slice.Slice.iter] using hslice.symm
      subst sliceIter
      generalize henumerate :
          core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.iter.traits.iterator.IteratorSliceIter Std.U32)
            ({ slice := alloc.vec.Vec.deref indices, i := 0 } :
              core.slice.iter.Iter Std.U32) = enumerateResult at hrun
      cases enumerateResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok enumerated =>
        simp only [bind_tc_ok] at hrun
        have henumerateExact : enumerated =
            enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize := by
          simpa [core.iter.traits.iterator.Iterator.enumerate.trait_default,
            core.iter.traits.iterator.Iterator.enumerate.default,
            enumerateSliceAt] using henumerate.symm
        subst enumerated
        generalize hinner :
            fri_checks.check_v5_fri_queries_loop0_loop0_loop0
              (enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize)
              later laterIndices finalPolynomial coordinates alphaPowers layer
              0#usize pending = innerResult at hrun
        cases innerResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok output =>
          rcases output with ⟨coordinatesNext, pendingNext, flag⟩
          simp only [bind_tc_ok] at hrun
          split at hrun
          · rename_i hflag
            simp only [Result.ok.injEq, ControlFlow.cont.injEq,
              Prod.mk.injEq] at hrun
            rcases hrun with ⟨rfl, rfl, rfl⟩
            refine ⟨rfl, indices, ?_, ?_⟩
            · simpa using hindices
            · change fri_checks.check_v5_fri_queries_loop0_loop0_loop0
                (enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize)
                later laterIndices finalPolynomial coordinates alphaPowers
                layer 0#usize pending =
                  .ok (coordinatesNext, pendingNext, 1#32#uscalar)
              exact hinner
          · cases pendingNext <;> simp_all

theorem generated_u32_one_eq :
    (1#32#uscalar : Std.U32) = 1#u32 := by
  apply UScalar.eq_of_val_eq
  rfl

theorem outer_active_body_ne_accepting_done_from_none
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (folded : aspis_core.field.QM31)
    (range rangeNext : core.ops.range.Range Std.Usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (layer : Std.Usize) (sink : fri_checks.V5FriCheckSink)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some layer, rangeNext)) :
    fri_checks.check_v5_fri_queries_loop0_loop0.body later laterIndices
        finalPolynomial alphaPowers folded range coordinates none ≠
      .ok (.done (some (.Ok sink))) := by
  intro hrun
  unfold fri_checks.check_v5_fri_queries_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hindices : Array.index_usize laterIndices layer = indexResult
    at hrun
  cases indexResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok indices =>
    simp only [bind_tc_ok] at hrun
    generalize hslice :
        core.slice.Slice.iter (alloc.vec.Vec.deref indices) = sliceResult
      at hrun
    cases sliceResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok sliceIter =>
      simp only [bind_tc_ok] at hrun
      have hsliceExact : sliceIter =
          ({ slice := alloc.vec.Vec.deref indices, i := 0 } :
            core.slice.iter.Iter Std.U32) := by
        simpa [core.slice.Slice.iter] using hslice.symm
      subst sliceIter
      generalize henumerate :
          core.iter.traits.iterator.Iterator.enumerate.trait_default
            (core.iter.traits.iterator.IteratorSliceIter Std.U32)
            ({ slice := alloc.vec.Vec.deref indices, i := 0 } :
              core.slice.iter.Iter Std.U32) = enumerateResult at hrun
      cases enumerateResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok enumerated =>
        simp only [bind_tc_ok] at hrun
        have henumerateExact : enumerated =
            enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize := by
          simpa [core.iter.traits.iterator.Iterator.enumerate.trait_default,
            core.iter.traits.iterator.Iterator.enumerate.default,
            enumerateSliceAt] using henumerate.symm
        subst enumerated
        generalize hinner :
            fri_checks.check_v5_fri_queries_loop0_loop0_loop0
              (enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize)
              later laterIndices finalPolynomial coordinates alphaPowers layer
              0#usize none = innerResult at hrun
        cases innerResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok output =>
          rcases output with ⟨coordinatesNext, pendingNext, flag⟩
          simp only [bind_tc_ok] at hrun
          split at hrun
          · simp only [Result.ok.injEq] at hrun
            contradiction
          · rename_i hnotFlag
            have hpending : pendingNext = some (.Ok sink) := by
              cases hpendingNext : pendingNext with
              | none => simp [hpendingNext] at hrun
              | some result =>
                cases result with
                | Err error => simp [hpendingNext] at hrun
                | Ok value =>
                  simp only [hpendingNext, Result.ok.injEq,
                    ControlFlow.done.injEq, Option.some.injEq,
                    core.result.Result.Ok.injEq] at hrun
                  subst value
                  rfl
            have hinnerAccept :
                fri_checks.check_v5_fri_queries_loop0_loop0_loop0
                  (enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize)
                  later laterIndices finalPolynomial coordinates alphaPowers
                  layer 0#usize none =
                    .ok (coordinatesNext, some (.Ok sink), flag) := by
              simpa [hpending] using hinner
            have hflag := inner_accepting_result_has_completed_flag
              later laterIndices finalPolynomial coordinates coordinatesNext
              alphaPowers layer (alloc.vec.Vec.deref indices) 0#usize 0#usize
              sink flag (by simp) hinnerAccept
            apply hnotFlag
            exact hflag.trans generated_u32_one_eq

theorem outer_accepted_loop_head
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (folded : aspis_core.field.QM31)
    (range rangeNext : core.ops.range.Range Std.Usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (pending : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (layer : Std.Usize) (sink : fri_checks.V5FriCheckSink)
    (hpending : pending = none)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some layer, rangeNext))
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0 range later laterIndices
          finalPolynomial coordinates alphaPowers folded pending =
        .ok (some (.Ok sink))) :
    ∃ indices : alloc.vec.Vec Std.U32,
      Array.index_usize laterIndices layer = .ok indices ∧
      ∃ coordinatesNext pendingNext,
        fri_checks.check_v5_fri_queries_loop0_loop0_loop0
            (enumerateSliceAt (alloc.vec.Vec.deref indices) 0#usize)
            later laterIndices finalPolynomial coordinates alphaPowers layer
            0#usize pending = .ok (coordinatesNext, pendingNext, 1#u32) ∧
        pendingNext = none ∧
        fri_checks.check_v5_fri_queries_loop0_loop0 rangeNext later
            laterIndices finalPolynomial coordinatesNext alphaPowers folded
            pendingNext = .ok (some (.Ok sink)) := by
  subst pending
  unfold fri_checks.check_v5_fri_queries_loop0_loop0 at hloop
  rw [loop.eq_def] at hloop
  simp only at hloop
  generalize hbody :
      fri_checks.check_v5_fri_queries_loop0_loop0.body later laterIndices
        finalPolynomial alphaPowers folded range coordinates none =
          bodyResult at hloop
  cases bodyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | ok flow =>
    cases flow with
    | cont nextState =>
      rcases nextState with ⟨rangeOut, coordinatesNext, pendingNext⟩
      simp only [bind_tc_ok] at hloop
      obtain ⟨hrange, indices, hindices, hinner⟩ :=
        outer_body_cont_exposes_completed_inner later laterIndices
          finalPolynomial alphaPowers folded range rangeNext rangeOut
          coordinates coordinatesNext none pendingNext layer hnext hbody
      subst rangeOut
      have hconstants := inner_completed_preserves_constants later
        laterIndices finalPolynomial coordinates coordinatesNext alphaPowers
        layer none pendingNext (alloc.vec.Vec.deref indices) 0#usize 0#usize
        (by simp) hinner
      have hpendingNext : pendingNext = none := hconstants.2
      exact ⟨indices, hindices, coordinatesNext, pendingNext, hinner,
        hpendingNext, hloop⟩
    | done output =>
      simp only [bind_tc_ok, Result.ok.injEq] at hloop
      subst output
      exact (outer_active_body_ne_accepting_done_from_none later
        laterIndices finalPolynomial alphaPowers folded range rangeNext
        coordinates layer sink hnext hbody).elim

/-- The exact three later passes started by the production layer-zero loop.
The indices and coordinates are the values returned by the unchanged generated
program; no model-side schedule is substituted for them. -/
structure ThreeLaterPassRuns
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses) :
    Type where
  indices0 : alloc.vec.Vec Std.U32
  indices1 : alloc.vec.Vec Std.U32
  indices2 : alloc.vec.Vec Std.U32
  coordinates1 : aspis_core.circle_fri.DerivedCircleQueryFoldInverses
  coordinates2 : aspis_core.circle_fri.DerivedCircleQueryFoldInverses
  coordinates3 : aspis_core.circle_fri.DerivedCircleQueryFoldInverses
  indicesAt0 : Array.index_usize laterIndices 0#usize = .ok indices0
  indicesAt1 : Array.index_usize laterIndices 1#usize = .ok indices1
  indicesAt2 : Array.index_usize laterIndices 2#usize = .ok indices2
  run0 :
    fri_checks.check_v5_fri_queries_loop0_loop0_loop0
        (enumerateSliceAt (alloc.vec.Vec.deref indices0) 0#usize)
        later laterIndices finalPolynomial coordinates alphaPowers 0#usize
        0#usize none = .ok (coordinates1, none, 1#u32)
  run1 :
    fri_checks.check_v5_fri_queries_loop0_loop0_loop0
        (enumerateSliceAt (alloc.vec.Vec.deref indices1) 0#usize)
        later laterIndices finalPolynomial coordinates1 alphaPowers 1#usize
        0#usize none = .ok (coordinates2, none, 1#u32)
  run2 :
    fri_checks.check_v5_fri_queries_loop0_loop0_loop0
        (enumerateSliceAt (alloc.vec.Vec.deref indices2) 0#usize)
        later laterIndices finalPolynomial coordinates2 alphaPowers 2#usize
        0#usize none = .ok (coordinates3, none, 1#u32)

theorem outer_accepted_three_pass_runs
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (folded : aspis_core.field.QM31)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (sink : fri_checks.V5FriCheckSink)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0 (range3At 0#usize) later
          laterIndices finalPolynomial coordinates alphaPowers folded none =
        .ok (some (.Ok sink))) :
    Nonempty (ThreeLaterPassRuns later laterIndices finalPolynomial
      alphaPowers coordinates) := by
  obtain ⟨range1, hrange1Value, hrange0⟩ :=
    range3_next_some 0#usize (by simp)
  obtain ⟨indices0, hindices0, coordinates1, pending1, hrun0,
      hpending1, hloop1⟩ :=
    outer_accepted_loop_head later laterIndices finalPolynomial
      alphaPowers folded (range3At 0#usize) (range3At range1) coordinates none
      0#usize sink rfl hrange0 hloop
  subst pending1
  have hrange1 : range1 = 1#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hrange1Value
  subst range1
  obtain ⟨range2, hrange2Value, hrange1⟩ :=
    range3_next_some 1#usize (by simp)
  obtain ⟨indices1, hindices1, coordinates2, pending2, hrun1,
      hpending2, hloop2⟩ :=
    outer_accepted_loop_head later laterIndices finalPolynomial
      alphaPowers folded (range3At 1#usize) (range3At range2) coordinates1
      none 1#usize sink rfl hrange1 hloop1
  subst pending2
  have hrange2 : range2 = 2#usize := by
    apply UScalar.eq_of_val_eq
    simpa using hrange2Value
  subst range2
  obtain ⟨range3, hrange3Value, hrange2⟩ :=
    range3_next_some 2#usize (by simp)
  obtain ⟨indices2, hindices2, coordinates3, pending3, hrun2,
      hpending3, _hloop3⟩ :=
    outer_accepted_loop_head later laterIndices finalPolynomial
      alphaPowers folded (range3At 2#usize) (range3At range3) coordinates2
      none 2#usize sink rfl hrange2 hloop2
  subst pending3
  exact ⟨{
    indices0 := indices0
    indices1 := indices1
    indices2 := indices2
    coordinates1 := coordinates1
    coordinates2 := coordinates2
    coordinates3 := coordinates3
    indicesAt0 := hindices0
    indicesAt1 := hindices1
    indicesAt2 := hindices2
    run0 := hrun0
    run1 := hrun1
    run2 := hrun2 }⟩

/-- An accepted outer production loop reads every enumerated opening in all
three later passes.  The first two passes also read their requested parent
openings; the third reads the terminal opening before the final-polynomial
check. -/
def sliceValueAt (values : Slice Std.U32) (target : Std.Usize)
    (htarget : target.val < values.val.length) : Std.U32 :=
  values[target]'htarget

theorem outer_accepted_reads_every_later_target
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (folded : aspis_core.field.QM31)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (sink : fri_checks.V5FriCheckSink)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0 (range3At 0#usize) later
          laterIndices finalPolynomial coordinates alphaPowers folded none =
        .ok (some (.Ok sink))) :
    ∃ runs : ThreeLaterPassRuns later laterIndices finalPolynomial
        alphaPowers coordinates,
      (∀ (target : Std.Usize)
          (htarget : target.val <
            (alloc.vec.Vec.deref runs.indices0).val.length),
        ∃ (carriedAt nextPosition : Std.Usize),
          nextPosition.val = target.val + 1 ∧
          Nonempty (LaterBodyReadEvidence later laterIndices 0#usize target
            carriedAt (sliceValueAt
              (alloc.vec.Vec.deref runs.indices0) target htarget))) ∧
      (∀ (target : Std.Usize)
          (htarget : target.val <
            (alloc.vec.Vec.deref runs.indices1).val.length),
        ∃ (carriedAt nextPosition : Std.Usize),
          nextPosition.val = target.val + 1 ∧
          Nonempty (LaterBodyReadEvidence later laterIndices 1#usize target
            carriedAt (sliceValueAt
              (alloc.vec.Vec.deref runs.indices1) target htarget))) ∧
      (∀ target : Std.Usize,
        target.val < (alloc.vec.Vec.deref runs.indices2).val.length →
        ∃ nextPosition : Std.Usize,
          nextPosition.val = target.val + 1 ∧
          Nonempty (TerminalBodyReadEvidence later 2#usize target)) := by
  obtain ⟨runs⟩ := outer_accepted_three_pass_runs later laterIndices
    finalPolynomial alphaPowers folded coordinates sink hloop
  refine ⟨runs, ?_, ?_, ?_⟩
  · intro target htarget
    exact production_later_completed_loop_reads_target later laterIndices
      finalPolynomial coordinates runs.coordinates1 alphaPowers 0#usize
      (by simp) none none (alloc.vec.Vec.deref runs.indices0) 0#usize target
      0#usize (by simp) htarget runs.run0
  · intro target htarget
    exact production_later_completed_loop_reads_target later laterIndices
      finalPolynomial runs.coordinates1 runs.coordinates2 alphaPowers 1#usize
      (by simp) none none (alloc.vec.Vec.deref runs.indices1) 0#usize target
      0#usize (by simp) htarget runs.run1
  · intro target htarget
    exact production_terminal_completed_loop_reads_target later laterIndices
      finalPolynomial runs.coordinates2 runs.coordinates3 alphaPowers 2#usize
      (by simp) none none (alloc.vec.Vec.deref runs.indices2) 0#usize target
      0#usize (by simp) htarget runs.run2

/-- Acceptance of the production layer-zero loop forces it to exhaust its
actual iterator and then accept through the exact three-pass outer loop.
The folded accumulator is the value computed by the unchanged Rust path. -/
theorem layerZero_accepted_reaches_outer
    (openings : VerifiedOpenings) (c1Count c1Width : Std.Usize)
    (c1Offsets : OpeningOffsets) (c2Count c2Width : Std.Usize)
    (c2Offsets : OpeningOffsets) (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (claims powers : alloc.vec.Vec aspis_core.field.QM31)
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (values : Slice Std.U32) (current : Std.Usize)
    (folded : aspis_core.field.QM31) (carried : Std.Usize)
    (sink : fri_checks.V5FriCheckSink)
    (hcurrent : current.val ≤ values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0 openings
          (enumerateSliceAt values current) c1Count c1Width c1Offsets c2Count
          c2Width c2Offsets later laterIndices claims powers weights
          multipliers finalPolynomial coordinates alphaPowers folded carried =
        .ok (some (.Ok sink))) :
    ∃ foldedFinal : aspis_core.field.QM31,
      fri_checks.check_v5_fri_queries_loop0_loop0 (range3At 0#usize) later
          laterIndices finalPolynomial coordinates alphaPowers foldedFinal
          none = .ok (some (.Ok sink)) := by
  by_cases hactive : current.val < values.val.length
  · obtain ⟨nextPosition, hnextValue, hnext⟩ :=
      enumerate_slice_at_next_run values current hactive
    obtain ⟨foldedNext, carriedNext, _hbody, hloopNext, _hevidence⟩ :=
      production_layerZero_accepted_loop_head openings c1Count c1Width
        c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
        weights multipliers finalPolynomial coordinates alphaPowers
        (enumerateSliceAt values current)
        (enumerateSliceAt values nextPosition) folded carried current
        values[current.val] sink hnext hloop
    apply layerZero_accepted_reaches_outer openings c1Count c1Width
      c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
      weights multipliers finalPolynomial coordinates alphaPowers values
      nextPosition foldedNext carriedNext sink
    · rw [hnextValue]
      omega
    · exact hloopNext
  · have hnone := enumerate_slice_at_next_none values current
      (by omega)
    unfold fri_checks.check_v5_fri_queries_loop0 at hloop
    rw [loop.eq_def] at hloop
    simp only at hloop
    unfold fri_checks.check_v5_fri_queries_loop0.body at hloop
    rw [hnone] at hloop
    simp only [bind_tc_ok] at hloop
    generalize houter :
        fri_checks.check_v5_fri_queries_loop0_loop0
          { start := 0#usize, «end» := 3#usize } later laterIndices
          finalPolynomial coordinates alphaPowers folded none = outerResult
      at hloop
    cases outerResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
    | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
    | ok pending =>
      cases pending with
      | none => simp at hloop
      | some result =>
        simp only [bind_tc_ok, Result.ok.injEq, Option.some.injEq,
          core.result.Result.Ok.injEq] at hloop
        subst result
        exact ⟨folded, by simpa [range3At] using houter⟩
termination_by values.val.length - current.val
decreasing_by
  rw [hnextValue]
  omega

theorem top_level_acceptance_exposes_layerZero_loop
    (openings : VerifiedOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (alphas : Array aspis_core.field.QM31 4#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (inverse : aspis_core.field.M31 → aspis_core.field.M31)
    (sink : fri_checks.V5FriCheckSink)
    (haccept : fri_checks.check_v5_fri_queries openings prepared alphas
      finalPolynomial inverse = .ok (.Ok sink)) :
    ∃ (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
        (alphaPowers : Array
          (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
        (folded : aspis_core.field.QM31),
      fri_checks.check_v5_fri_queries_loop0 openings
          (enumerateSliceAt (alloc.vec.Vec.deref openings.indices.layer0)
            0#usize)
          openings.c1.count openings.c1.value_width openings.c1.offsets
          openings.c2.count openings.c2.value_width openings.c2.offsets
          openings.later openings.indices.later prepared.inner.claims
          prepared.inner.powers prepared.c1_weight_limbs
          prepared.c2_multipliers finalPolynomial coordinates alphaPowers
          folded 0#usize = .ok (some (.Ok sink)) := by
  unfold fri_checks.check_v5_fri_queries at haccept
  generalize hcps : fri_checks.V5_FRI_PCS_SHAPE = cpsResult at haccept
  cases cpsResult <;> simp [Bind.bind, Aeneas.Std.bind] at haccept
  repeat' first
    | split at haccept
    | simp_all [Bind.bind, Aeneas.Std.bind, Std.lift,
        core.result.Result.Insts.CoreOpsTry.branch,
        from_residual_ne_ok, core.slice.Slice.iter,
        core.iter.traits.iterator.Iterator.enumerate.trait_default,
        core.iter.traits.iterator.Iterator.enumerate.default,
        enumerateSliceAt]
  exact ⟨_, _, _, by assumption⟩

/-- Complete source-level evidence extracted from an accepted execution of
the unchanged Charon/Aeneas translation.  Every query position in each of
the four FRI passes has an exact production read witness. -/
structure AcceptedProductionFriExecution
    (openings : VerifiedOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink) : Type where
  coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses
  alphaPowers : Array
    (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize
  foldedStart : aspis_core.field.QM31
  foldedFinal : aspis_core.field.QM31
  layerZeroRun :
    fri_checks.check_v5_fri_queries_loop0 openings
        (enumerateSliceAt (alloc.vec.Vec.deref openings.indices.layer0)
          0#usize)
        openings.c1.count openings.c1.value_width openings.c1.offsets
        openings.c2.count openings.c2.value_width openings.c2.offsets
        openings.later openings.indices.later prepared.inner.claims
        prepared.inner.powers prepared.c1_weight_limbs prepared.c2_multipliers
        finalPolynomial coordinates alphaPowers foldedStart 0#usize =
      .ok (some (.Ok sink))
  outerRun :
    fri_checks.check_v5_fri_queries_loop0_loop0 (range3At 0#usize)
        openings.later openings.indices.later finalPolynomial coordinates
        alphaPowers foldedFinal none = .ok (some (.Ok sink))
  laterRuns : ThreeLaterPassRuns openings.later openings.indices.later
    finalPolynomial alphaPowers coordinates
  layerZeroReads :
    ∀ (target : Std.Usize)
      (htarget : target.val <
        (alloc.vec.Vec.deref openings.indices.layer0).val.length),
      ∃ (carriedAt nextPosition : Std.Usize),
        nextPosition.val = target.val + 1 ∧
        Nonempty (LayerZeroBodyReadEvidence openings openings.c1.count
          openings.c1.value_width openings.c1.offsets openings.c2.count
          openings.c2.value_width openings.c2.offsets openings.later
          openings.indices.later
          (enumerateSliceAt (alloc.vec.Vec.deref openings.indices.layer0)
            nextPosition)
          (enumerateSliceAt (alloc.vec.Vec.deref openings.indices.layer0)
            nextPosition)
          target carriedAt
          (sliceValueAt (alloc.vec.Vec.deref openings.indices.layer0)
            target htarget))
  later0Reads :
    ∀ (target : Std.Usize)
      (htarget : target.val <
        (alloc.vec.Vec.deref laterRuns.indices0).val.length),
      ∃ (carriedAt nextPosition : Std.Usize),
        nextPosition.val = target.val + 1 ∧
        Nonempty (LaterBodyReadEvidence openings.later openings.indices.later
          0#usize target carriedAt
          (sliceValueAt (alloc.vec.Vec.deref laterRuns.indices0)
            target htarget))
  later1Reads :
    ∀ (target : Std.Usize)
      (htarget : target.val <
        (alloc.vec.Vec.deref laterRuns.indices1).val.length),
      ∃ (carriedAt nextPosition : Std.Usize),
        nextPosition.val = target.val + 1 ∧
        Nonempty (LaterBodyReadEvidence openings.later openings.indices.later
          1#usize target carriedAt
          (sliceValueAt (alloc.vec.Vec.deref laterRuns.indices1)
            target htarget))
  later2Reads :
    ∀ (target : Std.Usize),
      target.val < (alloc.vec.Vec.deref laterRuns.indices2).val.length →
      ∃ nextPosition : Std.Usize,
        nextPosition.val = target.val + 1 ∧
        Nonempty (TerminalBodyReadEvidence openings.later 2#usize target)

/-- End-to-end unchanged-source theorem for the FRI consumer: successful
top-level acceptance entails the exact first pass, all three later passes,
and a production read witness for every enumerated query in each pass. -/
theorem unchanged_source_acceptance_yields_complete_fri_execution
    (openings : VerifiedOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (alphas : Array aspis_core.field.QM31 4#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (inverse : aspis_core.field.M31 → aspis_core.field.M31)
    (sink : fri_checks.V5FriCheckSink)
    (haccept : fri_checks.check_v5_fri_queries openings prepared alphas
      finalPolynomial inverse = .ok (.Ok sink)) :
    Nonempty (AcceptedProductionFriExecution openings prepared
      finalPolynomial sink) := by
  obtain ⟨coordinates, alphaPowers, foldedStart, hlayerZero⟩ :=
    top_level_acceptance_exposes_layerZero_loop openings prepared
      alphas finalPolynomial inverse sink haccept
  obtain ⟨foldedFinal, houter⟩ :=
    layerZero_accepted_reaches_outer openings openings.c1.count
      openings.c1.value_width openings.c1.offsets openings.c2.count
      openings.c2.value_width openings.c2.offsets openings.later
      openings.indices.later prepared.inner.claims prepared.inner.powers
      prepared.c1_weight_limbs prepared.c2_multipliers finalPolynomial
      coordinates alphaPowers (alloc.vec.Vec.deref openings.indices.layer0)
      0#usize foldedStart 0#usize sink (by simp) hlayerZero
  obtain ⟨laterRuns⟩ := outer_accepted_three_pass_runs
    openings.later openings.indices.later finalPolynomial alphaPowers
    foldedFinal coordinates sink houter
  refine ⟨{
    coordinates := coordinates
    alphaPowers := alphaPowers
    foldedStart := foldedStart
    foldedFinal := foldedFinal
    layerZeroRun := hlayerZero
    outerRun := houter
    laterRuns := laterRuns
    layerZeroReads := ?_
    later0Reads := ?_
    later1Reads := ?_
    later2Reads := ?_ }⟩
  · intro target htarget
    exact production_layerZero_accepted_loop_reads_target openings
      openings.c1.count openings.c1.value_width openings.c1.offsets
      openings.c2.count openings.c2.value_width openings.c2.offsets
      openings.later openings.indices.later prepared.inner.claims
      prepared.inner.powers prepared.c1_weight_limbs prepared.c2_multipliers
      finalPolynomial coordinates alphaPowers
      (alloc.vec.Vec.deref openings.indices.layer0) 0#usize target foldedStart
      0#usize sink (by simp) htarget hlayerZero
  · intro target htarget
    exact production_later_completed_loop_reads_target openings.later
      openings.indices.later finalPolynomial coordinates
      laterRuns.coordinates1 alphaPowers 0#usize (by simp) none none
      (alloc.vec.Vec.deref laterRuns.indices0) 0#usize target 0#usize
      (by simp) htarget laterRuns.run0
  · intro target htarget
    exact production_later_completed_loop_reads_target openings.later
      openings.indices.later finalPolynomial laterRuns.coordinates1
      laterRuns.coordinates2 alphaPowers 1#usize (by simp) none none
      (alloc.vec.Vec.deref laterRuns.indices1) 0#usize target 0#usize
      (by simp) htarget laterRuns.run1
  · intro target htarget
    exact production_terminal_completed_loop_reads_target openings.later
      openings.indices.later finalPolynomial laterRuns.coordinates2
      laterRuns.coordinates3 alphaPowers 2#usize (by simp) none none
      (alloc.vec.Vec.deref laterRuns.indices2) 0#usize target 0#usize
      (by simp) htarget laterRuns.run2

#print axioms unchanged_source_acceptance_yields_complete_fri_execution

end AspisV5FriConsumerExactProof
