import V5FriProductionDecoderCanonical

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriProductionDecoderEquality

open AspisV5FriProductionDecoderCanonical
open AspisV5FriTransparentHelperEquality
open AspisV5FriDecoderReferenceSemantics

private abbrev ExactQM31 := V5FriArithmeticExact.field.QM31
private abbrev ExactIter := core.slice.iter.IterMut ExactQM31
private abbrev ExactEnumerate := core.iter.adapters.enumerate.Enumerate ExactIter

def writeBackAt (position : Nat) (current : ExactEnumerate)
    (replacement : Option (Std.Usize × ExactQM31)) : ExactEnumerate :=
  { current with
    iter :=
      match replacement.map Prod.snd with
      | none => current.iter
      | some value =>
          { current.iter with
            slice := current.iter.slice.setAtNat position value } }

theorem iter_mut_next_active
    (iter : ExactIter) (hactive : iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (some iter.slice[iter.i], { iter with i := iter.i + 1 },
        fun current replacement =>
          match replacement with
          | none => current
          | some value =>
              { current with
                slice := current.slice.setAtNat iter.i value }) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_pos hactive]
  simp only
  congr 1
  congr 1
  congr 1
  funext current replacement
  cases replacement
  · rfl
  · cases current
    rfl

theorem iter_mut_next_done
    (iter : ExactIter) (hdone : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (none, iter, fun current _ => current) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_neg hdone]

theorem enumerate_next_active
    (state : ExactEnumerate) (nextCount : Std.Usize)
    (hactive : state.iter.i < state.iter.slice.len)
    (hcount : state.count + 1#usize = (.ok nextCount : Result Std.Usize)) :
    V5FriHelperTransparent.iterMutEnumerateNext state =
      .ok (some (state.count, state.iter.slice[state.iter.i]),
        { iter := { state.iter with i := state.iter.i + 1 },
          count := nextCount },
        writeBackAt state.iter.i) := by
  unfold V5FriHelperTransparent.iterMutEnumerateNext
  have hnext := iter_mut_next_active state.iter hactive
  rw [hnext]
  simp only [bind_tc_ok]
  rw [hcount]
  simp only [bind_tc_ok]
  rfl

theorem enumerate_next_done
    (state : ExactEnumerate)
    (hdone : ¬ state.iter.i < state.iter.slice.len) :
    V5FriHelperTransparent.iterMutEnumerateNext state =
      .ok (none, state, fun current _ => current) := by
  unfold V5FriHelperTransparent.iterMutEnumerateNext
  rw [iter_mut_next_done state.iter hdone]
  simp only [bind_tc_ok]

theorem usize_add_one_ok
    (current next : Std.Usize)
    (hvalue : current.val + 1 = next.val)
    (hbound : current.val + 1 < 2 ^ System.Platform.numBits) :
    current + 1#usize = (.ok next : Result Std.Usize) := by
  have hadd := @UScalar.add_equiv UScalarTy.Usize current 1#usize
  generalize heq : (current + 1#usize) = addResult at hadd ⊢
  cases addResult with
  | fail error =>
    exfalso
    apply hadd
    simpa using hbound
  | div => exact False.elim hadd
  | ok value =>
    have hvalue' : value.val = next.val := by
      calc
        value.val = current.val + (1#usize).val := hadd.2.1
        _ = current.val + 1 := by rfl
        _ = next.val := hvalue
    have : value = next := UScalar.val_eq_imp value next hvalue'
    simp [this]

@[simp] theorem array_make4_get0 {T : Type} (a b c d : T) :
    (Array.make 4#usize [a, b, c, d]).val[0] = a := by rfl

@[simp] theorem array_make4_get1 {T : Type} (a b c d : T) :
    (Array.make 4#usize [a, b, c, d]).val[1] = b := by rfl

@[simp] theorem array_make4_get2 {T : Type} (a b c d : T) :
    (Array.make 4#usize [a, b, c, d]).val[2] = c := by rfl

@[simp] theorem array_make4_get3 {T : Type} (a b c d : T) :
    (Array.make 4#usize [a, b, c, d]).val[3] = d := by rfl

def sourceDecodeWithModel {T : Type}
    (leaf : Slice Std.U8) (layer : Std.U8) (slot : Std.Usize)
    (onError :
      V5FriArithmeticExact.circle_query.CircleQueryError → T)
    (onSuccess : ExactQM31 → T) : Result T := do
  let decoded ← sourceDecodeOuter leaf layer slot
  match decoded with
  | .Err error => ok (onError error)
  | .Ok value => ok (onSuccess value)

theorem source_decode_body_of_some_model
    (toSliceBack : Slice ExactQM31 → Array ExactQM31 4#usize)
    (iterBack : core.slice.iter.IterMut ExactQM31 → Slice ExactQM31)
    (enumerateBack : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31) → core.slice.iter.IterMut ExactQM31)
    (leaf : Slice Std.U8) (layer : Std.U8)
    (iter iter1 : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31))
    (back : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31) →
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut ExactQM31))
    (nextBack : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31) → Option (Std.Usize × ExactQM31) →
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut ExactQM31))
    (slot : Std.Usize) (old : ExactQM31)
    (hnext : V5FriHelperTransparent.iterMutEnumerateNext iter =
      .ok (some (slot, old), iter1, nextBack)) :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body
        toSliceBack iterBack enumerateBack leaf layer iter back =
      sourceDecodeWithModel leaf layer slot
        (fun error => done (.Err error))
        (fun value => cont (iter1, (fun resumed =>
          back (nextBack resumed (some (slot, value)))))) := by
  unfold V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body
  rw [hnext]
  simp only [bind_tc_ok]
  unfold sourceDecodeWithModel sourceDecodeOuter sourceDecodeEncoded
  unfold V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES
  rw [source_decode_later_fnmut_eq_arithmetic]
  simp [Aeneas.Std.lift, core.slice.Slice.iter, Array.index_usize,
    V5FriHelperTransparent.aspis_core.field.CM31.new,
    V5FriArithmeticExact.field.CM31.new]

def sourceDecodeBodyModel
    (toSliceBack : Slice ExactQM31 → Array ExactQM31 4#usize)
    (iterBack : core.slice.iter.IterMut ExactQM31 → Slice ExactQM31)
    (enumerateBack : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31) → core.slice.iter.IterMut ExactQM31)
    (leaf : Slice Std.U8) (layer : Std.U8)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31))
    (back : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut ExactQM31) →
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut ExactQM31)) :
    Result (ControlFlow
      ((core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut ExactQM31)) ×
       (core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut ExactQM31) →
        core.iter.adapters.enumerate.Enumerate
          (core.slice.iter.IterMut ExactQM31)))
      (core.result.Result (Array ExactQM31 4#usize)
        V5FriArithmeticExact.circle_query.CircleQueryError)) := do
  let (item, iter1, nextBack) ←
    V5FriHelperTransparent.iterMutEnumerateNext iter
  match item with
  | none =>
    let iter2 := nextBack iter1 none
    let im := enumerateBack (back iter2)
    let s := iterBack im
    let values := toSliceBack s
    ok (done (.Ok values))
  | some (slot, _) =>
    sourceDecodeWithModel leaf layer slot
      (fun error => done (.Err error))
      (fun value => cont (iter1, (fun resumed =>
        back (nextBack resumed (some (slot, value))))))

theorem source_decode_body_eq_model :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body =
      sourceDecodeBodyModel := by
  funext toSliceBack iterBack enumerateBack leaf layer iter back
  generalize hnext : V5FriHelperTransparent.iterMutEnumerateNext iter = next
  cases next with
  | fail e =>
    unfold V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body
      sourceDecodeBodyModel
    rw [hnext]
    simp [Bind.bind, Aeneas.Std.bind]
  | div =>
    unfold V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body
      sourceDecodeBodyModel
    rw [hnext]
    simp [Bind.bind, Aeneas.Std.bind]
  | ok triple =>
    rcases triple with ⟨item, iter1, nextBack⟩
    cases item with
    | none =>
      unfold V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop.body
        sourceDecodeBodyModel
      rw [hnext]
      simp only [bind_tc_ok]
    | some pair =>
      rcases pair with ⟨slot, old⟩
      unfold sourceDecodeBodyModel
      rw [hnext]
      simp only [bind_tc_ok]
      exact source_decode_body_of_some_model toSliceBack iterBack
        enumerateBack leaf layer iter iter1 back nextBack slot old hnext

def sourceDecodeLeafModel
    (leaf : Slice Std.U8) (layer : Std.U8) :
    Result (core.result.Result (Array ExactQM31 4#usize)
      V5FriArithmeticExact.circle_query.CircleQueryError) := do
  let expected ←
    V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES
  let checked ←
    V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length leaf
      (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer) expected
  let flow ← core.result.Result.Insts.CoreOpsTry.branch checked
  match flow with
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array ExactQM31 4#usize)
      (core.convert.FromSame
        V5FriArithmeticExact.circle_query.CircleQueryError) residual
  | .Continue _ =>
    let values := Array.repeat 4#usize
      V5FriHelperTransparent.aspis_core.field.QM31.ZERO
    let (slice, toSliceBack) ← lift (Array.to_slice_mut values)
    let (iterMut, iterBack) ← core.slice.Slice.iter_mut slice
    let (iter, enumerateBack) ←
      V5FriHelperTransparent.iterMutEnumerate iterMut
    loop
      (fun (iter1, back1) => sourceDecodeBodyModel toSliceBack iterBack
        enumerateBack leaf layer iter1 back1)
      (iter, fun e => e)

theorem source_decode_later_leaf_eq_model
    (leaf : Slice Std.U8) (layer : Std.U8) :
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf leaf layer =
      sourceDecodeLeafModel leaf layer := by
  unfold V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf
    sourceDecodeLeafModel
  rw [show V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop =
      fun toSliceBack iterBack enumerateBack iter back leaf layer =>
        loop
          (fun (iter1, back1) => sourceDecodeBodyModel toSliceBack iterBack
            enumerateBack leaf layer iter1 back1)
          (iter, back) by
    funext toSliceBack iterBack enumerateBack iter back leaf layer
    unfold V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf_loop
    rw [source_decode_body_eq_model]]
  simp [V5FriHelperTransparent.aspis_core.field.QM31.ZERO]
  intro expected hExpected checked hChecked flow hFlow
  cases flow <;> rfl

def sourceDecodeLeafSlots
    (leaf : Slice Std.U8) (layer : Std.U8) :
    Result (core.result.Result (Array ExactQM31 4#usize)
      V5FriArithmeticExact.circle_query.CircleQueryError) := do
  let r0 ← sourceDecodeOuter leaf layer 0#usize
  let cf0 ← core.result.Result.Insts.CoreOpsTry.branch r0
  match cf0 with
  | .Continue v0 =>
    let r1 ← sourceDecodeOuter leaf layer 1#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | .Continue v1 =>
      let r2 ← sourceDecodeOuter leaf layer 2#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | .Continue v2 =>
        let r3 ← sourceDecodeOuter leaf layer 3#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | .Continue v3 => ok (.Ok (Array.make 4#usize [v0, v1, v2, v3]))
        | .Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (Array ExactQM31 4#usize) (core.convert.FromSame
              V5FriArithmeticExact.circle_query.CircleQueryError) residual
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (Array ExactQM31 4#usize) (core.convert.FromSame
            V5FriArithmeticExact.circle_query.CircleQueryError) residual
    | .Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (Array ExactQM31 4#usize) (core.convert.FromSame
          V5FriArithmeticExact.circle_query.CircleQueryError) residual
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Array ExactQM31 4#usize) (core.convert.FromSame
        V5FriArithmeticExact.circle_query.CircleQueryError) residual

theorem source_decode_leaf_model_success_calls
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (output : Array ExactQM31 4#usize)
    (hrun : sourceDecodeLeafModel (Array.to_slice leaf) layer =
      .ok (.Ok output)) :
    ∃ a0 a1 a2 a3 : ExactQM31,
      sourceDecodeOuter (Array.to_slice leaf) layer 0#usize = .ok (.Ok a0) ∧
      sourceDecodeOuter (Array.to_slice leaf) layer 1#usize = .ok (.Ok a1) ∧
      sourceDecodeOuter (Array.to_slice leaf) layer 2#usize = .ok (.Ok a2) ∧
      sourceDecodeOuter (Array.to_slice leaf) layer 3#usize = .ok (.Ok a3) ∧
      output.val = [a0, a1, a2, a3] := by
  unfold sourceDecodeLeafModel at hrun
  rw [show V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES =
      .ok 64#usize by
    unfold V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES
    have hspec := Std.Usize.mul_spec (x := 4#usize) (y := 16#usize)
      (by scalar_tac)
    obtain ⟨out, hout, hval⟩ := WP.spec_imp_exists hspec
    have : out = 64#usize := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    simpa [this] using hout] at hrun
  simp only [bind_tc_ok] at hrun
  have hcheck :
      V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length
        (Array.to_slice leaf)
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        64#usize = .ok (.Ok ()) := by
    unfold V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length
    simp [Array.to_slice]
  rw [hcheck] at hrun
  simp only [
    core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok,
    V5FriHelperTransparent.aspis_core.field.QM31.ZERO,
    V5FriHelperTransparent.iterMutEnumerate,
    core.slice.Slice.iter_mut,
    Array.to_slice_mut,
    Array.to_slice,
    Aeneas.Std.lift] at hrun
  let zero : ExactQM31 :=
    { c0 := { a := 0#u32, b := 0#u32 },
      c1 := { a := 0#u32, b := 0#u32 } }
  let state0 : ExactEnumerate :=
    { iter := { slice := (Array.repeat 4#usize zero).to_slice },
      count := 0#usize }
  change
    loop
      (fun (iter1, back1) => sourceDecodeBodyModel
        (Array.from_slice (Array.repeat 4#usize zero))
        (fun it => it.slice) (fun e => e.iter)
        (Array.to_slice leaf) layer iter1 back1)
      (state0, fun e => e) = .ok (.Ok output) at hrun
  rw [loop.eq_def] at hrun
  unfold sourceDecodeBodyModel at hrun
  have hactive0 : state0.iter.i < state0.iter.slice.len := by
    simp [state0, Array.repeat, Array.to_slice, Slice.len]
  have hcount0 :
      state0.count + 1#usize = (.ok 1#usize : Result Std.Usize) := by
    apply usize_add_one_ok
    · rfl
    · cases hbits : System.Platform.numBits_eq <;>
        simp_all [state0]
  have hnext0 := enumerate_next_active state0 1#usize hactive0 hcount0
  simp only [hnext0, bind_tc_ok] at hrun
  simp only [state0] at hrun
  unfold sourceDecodeWithModel at hrun
  generalize hcall0 :
      sourceDecodeOuter (Array.to_slice leaf) layer 0#usize = call0 at hrun
  cases call0 with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok decoded0 =>
    cases decoded0 with
    | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | Ok a0 =>
      simp only [bind_tc_ok] at hrun
      rw [loop.eq_def] at hrun
      let state1 : ExactEnumerate :=
        { iter :=
            { slice := (Array.repeat 4#usize zero).to_slice,
              i := 1 },
          count := 1#usize }
      have hactive1 : state1.iter.i < state1.iter.slice.len := by
        simp [state1, Array.repeat, Array.to_slice, Slice.len]
      have hcount1 :
          state1.count + 1#usize = (.ok 2#usize : Result Std.Usize) := by
        apply usize_add_one_ok
        · rfl
        · cases hbits : System.Platform.numBits_eq <;>
            simp_all [state1]
      have hnext1 := enumerate_next_active state1 2#usize hactive1 hcount1
      have hnext1' := hnext1
      simp only [state1] at hnext1'
      simp only [Prod.fst, Prod.snd, Nat.zero_add] at hrun
      simp only [hnext1', bind_tc_ok] at hrun
      simp only [state1, Nat.one_add] at hrun
      generalize hcall1 :
          sourceDecodeOuter (Array.to_slice leaf) layer 1#usize = call1 at hrun
      cases call1 with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok decoded1 =>
        cases decoded1 with
        | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | Ok a1 =>
          simp only [bind_tc_ok] at hrun
          rw [loop.eq_def] at hrun
          let state2 : ExactEnumerate :=
            { iter :=
                { slice := (Array.repeat 4#usize zero).to_slice,
                  i := 2 },
              count := 2#usize }
          have hactive2 : state2.iter.i < state2.iter.slice.len := by
            simp [state2, Array.repeat, Array.to_slice, Slice.len]
          have hcount2 :
              state2.count + 1#usize = (.ok 3#usize : Result Std.Usize) := by
            apply usize_add_one_ok
            · rfl
            · cases hbits : System.Platform.numBits_eq <;>
                simp_all [state2]
          have hnext2 := enumerate_next_active state2 3#usize hactive2 hcount2
          have hnext2' := hnext2
          simp only [state2] at hnext2'
          simp only [hnext2', bind_tc_ok] at hrun
          generalize hcall2 :
              sourceDecodeOuter (Array.to_slice leaf) layer 2#usize = call2 at hrun
          cases call2 with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok decoded2 =>
            cases decoded2 with
            | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | Ok a2 =>
              simp only [bind_tc_ok] at hrun
              rw [loop.eq_def] at hrun
              let state3 : ExactEnumerate :=
                { iter :=
                    { slice := (Array.repeat 4#usize zero).to_slice,
                      i := 3 },
                  count := 3#usize }
              have hactive3 : state3.iter.i < state3.iter.slice.len := by
                simp [state3, Array.repeat, Array.to_slice, Slice.len]
              have hcount3 :
                  state3.count + 1#usize =
                    (.ok 4#usize : Result Std.Usize) := by
                apply usize_add_one_ok
                · rfl
                · cases hbits : System.Platform.numBits_eq <;>
                    simp_all [state3]
              have hnext3 :=
                enumerate_next_active state3 4#usize hactive3 hcount3
              have hnext3' := hnext3
              simp only [state3] at hnext3'
              simp only [hnext3', bind_tc_ok] at hrun
              generalize hcall3 :
                  sourceDecodeOuter (Array.to_slice leaf) layer 3#usize = call3
                    at hrun
              cases call3 with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok decoded3 =>
                cases decoded3 with
                | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | Ok a3 =>
                  simp only [bind_tc_ok] at hrun
                  rw [loop.eq_def] at hrun
                  let state4 : ExactEnumerate :=
                    { iter :=
                        { slice := (Array.repeat 4#usize zero).to_slice,
                          i := 4 },
                      count := 4#usize }
                  have hdone4 :
                      ¬ state4.iter.i < state4.iter.slice.len := by
                    simp [state4, Array.repeat, Array.to_slice, Slice.len]
                  have hnext4 := enumerate_next_done state4 hdone4
                  have hnext4' := hnext4
                  simp only [state4] at hnext4'
                  simp only [hnext4', bind_tc_ok] at hrun
                  refine ⟨a0, a1, a2, a3, rfl, rfl, rfl, rfl, ?_⟩
                  injection hrun with houtput
                  injection houtput with harray
                  rw [← harray]
                  simp [writeBackAt, Array.from_slice, Slice.setAtNat,
                    Array.repeat, Array.to_slice]

theorem production_full_decoder_reference_equality
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (values : Array ExactQM31 4#usize)
    (h : V5FriArithmeticExact.circle_query.decode_later_leaf
      (Array.to_slice leaf) layer = .ok (.Ok values)) :
    ∃ refValues : Array RefQM31 4#usize,
      V5FriDecoderReference.decode_later_leaf_reference leaf layer =
          .ok (.Ok refValues) ∧
      values = refArrayToExact refValues := by
  rw [← source_decode_later_leaf_eq_arithmetic] at h
  rw [source_decode_later_leaf_eq_model] at h
  obtain ⟨a0, a1, a2, a3, h0, h1, h2, h3, hvalues⟩ :=
    source_decode_leaf_model_success_calls leaf layer values h
  have hu0 : Std.Usize.ofNatCore 0 (by scalar_tac) = 0#usize := by
    apply UScalar.eq_of_val_eq
    rfl

  have hu1 : Std.Usize.ofNatCore 1 (by scalar_tac) = 1#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have hu2 : Std.Usize.ofNatCore 2 (by scalar_tac) = 2#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have hu3 : Std.Usize.ofNatCore 3 (by scalar_tac) = 3#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have h0' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 0 (by scalar_tac)) = .ok (.Ok a0) := by
    rw [hu0]
    exact h0
  have h1' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 1 (by scalar_tac)) = .ok (.Ok a1) := by
    rw [hu1]
    exact h1
  have h2' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 2 (by scalar_tac)) = .ok (.Ok a2) := by
    rw [hu2]
    exact h2
  have h3' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 3 (by scalar_tac)) = .ok (.Ok a3) := by
    rw [hu3]
    exact h3
  obtain ⟨r0, hr0, ha0⟩ := source_decode_outer_success_reference leaf layer
    ⟨0, by decide⟩ a0 h0'
  obtain ⟨r1, hr1, ha1⟩ := source_decode_outer_success_reference leaf layer
    ⟨1, by decide⟩ a1 h1'
  obtain ⟨r2, hr2, ha2⟩ := source_decode_outer_success_reference leaf layer
    ⟨2, by decide⟩ a2 h2'
  obtain ⟨r3, hr3, ha3⟩ := source_decode_outer_success_reference leaf layer
    ⟨3, by decide⟩ a3 h3'
  let refValues : Array RefQM31 4#usize :=
    Array.make 4#usize [r0, r1, r2, r3]
  refine ⟨refValues, ?_, ?_⟩
  · unfold V5FriDecoderReference.decode_later_leaf_reference
    rw [← hu0, hr0]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [← hu1, hr1]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [← hu2, hr2]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [← hu3, hr3]
    rfl
  · apply Subtype.ext
    change values.val = (refArrayToExact refValues).val
    rw [hvalues]
    rw [ha0, ha1, ha2, ha3]
    change [refToExactQM31 r0, refToExactQM31 r1,
      refToExactQM31 r2, refToExactQM31 r3] =
      [refToExactQM31 r0, refToExactQM31 r1,
        refToExactQM31 r2, refToExactQM31 r3]
    rfl

def exactLimbs (value : ExactQM31) : Array Std.U32 4#usize :=
  Array.make 4#usize [value.c0.a, value.c0.b, value.c1.a, value.c1.b]

theorem selected_predicate_eq_later :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool =
      V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool := by
  unfold
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
    V5FriHelperTransparent.aspis_core.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
  congr 1

def sourceSelectedBodyModel
    (leaf : Slice Std.U8) (layer : Std.U8)
    (selectedSlot : Std.Usize)
    (iter : core.ops.range.Range Std.Usize)
    (selected : Array Std.U32 4#usize) :
    Result (ControlFlow
      ((core.ops.range.Range Std.Usize) × Array Std.U32 4#usize)
      (core.result.Result ExactQM31
        V5FriArithmeticExact.circle_query.CircleQueryError)) := do
  let (item, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match item with
  | none =>
    let i0 ← Array.index_usize selected 0#usize
    let i1 ← Array.index_usize selected 1#usize
    let c0 ← V5FriHelperTransparent.aspis_core.field.CM31.new i0 i1
    let i2 ← Array.index_usize selected 2#usize
    let i3 ← Array.index_usize selected 3#usize
    let c1 ← V5FriHelperTransparent.aspis_core.field.CM31.new i2 i3
    ok (done (.Ok { c0, c1 }))
  | some slot =>
    sourceDecodeWithModel leaf layer slot
      (fun error => done (.Err error))
      (fun value =>
        if slot = selectedSlot
        then cont (iter1, exactLimbs value)
        else cont (iter1, selected))

theorem source_selected_body_eq_model :
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop.body =
      sourceSelectedBodyModel := by
  funext leaf layer selectedSlot iter selected
  unfold
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop.body
    sourceSelectedBodyModel
  generalize hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok pair =>
    rcases pair with ⟨item, iter1⟩
    cases item with
    | none =>
      simp only [bind_tc_ok]
    | some slot =>
      simp only [bind_tc_ok]
      unfold sourceDecodeWithModel sourceDecodeOuter sourceDecodeEncoded
      unfold
        V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES
      rw [selected_predicate_eq_later]
      simp [exactLimbs,
        V5FriHelperTransparent.aspis_core.field.CM31.new]
      intro offset hoff finish hfinish encoded hencoded
        s0 hs0 r0 hr0 a0 ha0 i0 hi0
        s1 hs1 r1 hr1 a1 ha1 i1 hi1
        s2 hs2 r2 hr2 a2 ha2 i2 hi2
        s3 hs3 r3 hr3 a3 ha3 i3 hi3
      simp only [Aeneas.Std.lift, core.slice.Slice.iter, bind_tc_ok]
      generalize hany :
          core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
            V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
            ⟨Array.to_slice (Array.make 4#usize [i0, i1, i2, i3]), 0⟩ () =
          anyResult
      cases anyResult with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok pair =>
        rcases pair with ⟨nonCanonical, next⟩
        cases nonCanonical <;>
          simp_all [V5FriArithmeticExact.field.CM31.new, exactLimbs,
            Bind.bind, Aeneas.Std.bind]
        by_cases hslot : slot = selectedSlot <;> simp [hslot]

private theorem selected_range_next_0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 0#usize, «end» := 4#usize } =
      .ok (some 0#usize, { start := 1#usize, «end» := 4#usize }) := by
  have hmax : 0 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem selected_range_next_1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 1#usize, «end» := 4#usize } =
      .ok (some 1#usize, { start := 2#usize, «end» := 4#usize }) := by
  have hmax : 1 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem selected_range_next_2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 2#usize, «end» := 4#usize } =
      .ok (some 2#usize, { start := 3#usize, «end» := 4#usize }) := by
  have hmax : 2 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem selected_range_next_3 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 3#usize, «end» := 4#usize } =
      .ok (some 3#usize, { start := 4#usize, «end» := 4#usize }) := by
  have hmax : 3 < UScalar.max UScalarTy.Usize := by scalar_tac
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, hmax]

private theorem selected_range_next_4 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        { start := 4#usize, «end» := 4#usize } =
      .ok (none, { start := 4#usize, «end» := 4#usize }) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
    core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt]

@[simp] private theorem selected_usize_0 :
    Std.Usize.ofNatCore 0 (by scalar_tac) = 0#usize := by
  apply UScalar.eq_of_val_eq
  rfl

@[simp] private theorem selected_usize_1 :
    Std.Usize.ofNatCore 1 (by scalar_tac) = 1#usize := by
  apply UScalar.eq_of_val_eq
  rfl

@[simp] private theorem selected_usize_2 :
    Std.Usize.ofNatCore 2 (by scalar_tac) = 2#usize := by
  apply UScalar.eq_of_val_eq
  rfl

@[simp] private theorem selected_usize_3 :
    Std.Usize.ofNatCore 3 (by scalar_tac) = 3#usize := by
  apply UScalar.eq_of_val_eq
  rfl

theorem source_selected_loop_success_calls
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (selectedSlot : Fin 4) (value : ExactQM31)
    (hrun :
      loop
        (fun (state : core.ops.range.Range Std.Usize ×
            Array Std.U32 4#usize) =>
          sourceSelectedBodyModel (Array.to_slice leaf) layer
            (Std.Usize.ofNatCore selectedSlot.val (by scalar_tac))
            state.1 state.2)
        ({ start := 0#usize, «end» := 4#usize },
          Array.repeat 4#usize 0#u32) = .ok (.Ok value)) :
    ∃ a0 a1 a2 a3 : ExactQM31,
      sourceDecodeOuter (Array.to_slice leaf) layer 0#usize = .ok (.Ok a0) ∧
      sourceDecodeOuter (Array.to_slice leaf) layer 1#usize = .ok (.Ok a1) ∧
      sourceDecodeOuter (Array.to_slice leaf) layer 2#usize = .ok (.Ok a2) ∧
      sourceDecodeOuter (Array.to_slice leaf) layer 3#usize = .ok (.Ok a3) ∧
      value = (Array.make 4#usize [a0, a1, a2, a3]).val[selectedSlot.val]! := by
  fin_cases selectedSlot
  all_goals
    simp only [selected_usize_0, selected_usize_1,
      selected_usize_2, selected_usize_3] at hrun ⊢
    rw [loop.eq_def] at hrun
    unfold sourceSelectedBodyModel at hrun
    rw [selected_range_next_0] at hrun
    simp only [bind_tc_ok] at hrun
    unfold sourceDecodeWithModel at hrun
    generalize hcall0 :
        sourceDecodeOuter (Array.to_slice leaf) layer 0#usize = call0 at hrun
    cases call0 with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok decoded0 =>
      cases decoded0 with
      | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | Ok a0 =>
        simp only [bind_tc_ok] at hrun
        simp (discharger := scalar_tac) only [if_pos, if_neg] at hrun
        rw [loop.eq_def] at hrun
        rw [selected_range_next_1] at hrun
        simp only [bind_tc_ok] at hrun
        generalize hcall1 :
            sourceDecodeOuter (Array.to_slice leaf) layer 1#usize = call1
              at hrun
        cases call1 with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok decoded1 =>
          cases decoded1 with
          | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | Ok a1 =>
            simp only [bind_tc_ok] at hrun
            simp (discharger := scalar_tac) only [if_pos, if_neg] at hrun
            rw [loop.eq_def] at hrun
            rw [selected_range_next_2] at hrun
            simp only [bind_tc_ok] at hrun
            generalize hcall2 :
                sourceDecodeOuter (Array.to_slice leaf) layer 2#usize = call2
                  at hrun
            cases call2 with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok decoded2 =>
              cases decoded2 with
              | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | Ok a2 =>
                simp only [bind_tc_ok] at hrun
                simp (discharger := scalar_tac) only [if_pos, if_neg] at hrun
                rw [loop.eq_def] at hrun
                rw [selected_range_next_3] at hrun
                simp only [bind_tc_ok] at hrun
                generalize hcall3 :
                    sourceDecodeOuter (Array.to_slice leaf) layer 3#usize =
                      call3 at hrun
                cases call3 with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | ok decoded3 =>
                  cases decoded3 with
                  | Err error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | Ok a3 =>
                    simp only [bind_tc_ok] at hrun
                    simp (discharger := scalar_tac) only [if_pos, if_neg]
                      at hrun
                    rw [loop.eq_def] at hrun
                    rw [selected_range_next_4] at hrun
                    simp only [bind_tc_ok] at hrun
                    refine ⟨a0, a1, a2, a3, rfl, rfl, rfl, rfl, ?_⟩
                    simp [exactLimbs, Array.index_usize,
                      V5FriHelperTransparent.aspis_core.field.CM31.new]
                      at hrun
                    simpa using hrun.symm

theorem production_selected_decoder_reference_equality
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (slot : Fin 4) (value : ExactQM31)
    (h : V5FriArithmeticExact.circle_query.decode_selected_later_slot
      (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore slot.val (by scalar_tac)) = .ok (.Ok value)) :
    ∃ refValue : RefQM31,
      V5FriDecoderReference.decode_selected_later_slot_reference leaf layer
          (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
        .ok (.Ok refValue) ∧
      value = refToExactQM31 refValue := by
  rw [← source_decode_selected_later_slot_eq_arithmetic] at h
  unfold
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot
    at h
  rw [show V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES =
      .ok 64#usize by
    unfold V5FriHelperTransparent.aspis_core.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES
    have hspec := Std.Usize.mul_spec (x := 4#usize) (y := 16#usize)
      (by scalar_tac)
    obtain ⟨out, hout, hval⟩ := WP.spec_imp_exists hspec
    have : out = 64#usize := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    simpa [this] using hout] at h
  simp only [bind_tc_ok] at h
  have hcheck :
      V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length
        (Array.to_slice leaf)
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        64#usize = .ok (.Ok ()) := by
    unfold V5FriHelperTransparent.aspis_core.circle_query.check_leaf_length
    simp [Array.to_slice]
  rw [hcheck] at h
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
  have hslot :
      ¬ 4#usize ≤ Std.Usize.ofNatCore slot.val (by scalar_tac) := by
    scalar_tac
  rw [if_neg hslot] at h
  unfold
    V5FriHelperTransparent.aspis_core.circle_query.decode_selected_later_slot_loop
    at h
  rw [source_selected_body_eq_model] at h
  obtain ⟨a0, a1, a2, a3, h0, h1, h2, h3, hvalue⟩ :=
    source_selected_loop_success_calls leaf layer slot value h
  have h0' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 0 (by scalar_tac)) = .ok (.Ok a0) := by
    rw [selected_usize_0]
    exact h0
  have h1' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 1 (by scalar_tac)) = .ok (.Ok a1) := by
    rw [selected_usize_1]
    exact h1
  have h2' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 2 (by scalar_tac)) = .ok (.Ok a2) := by
    rw [selected_usize_2]
    exact h2
  have h3' : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore 3 (by scalar_tac)) = .ok (.Ok a3) := by
    rw [selected_usize_3]
    exact h3
  obtain ⟨r0, hr0, ha0⟩ := source_decode_outer_success_reference leaf layer
    ⟨0, by decide⟩ a0 h0'
  obtain ⟨r1, hr1, ha1⟩ := source_decode_outer_success_reference leaf layer
    ⟨1, by decide⟩ a1 h1'
  obtain ⟨r2, hr2, ha2⟩ := source_decode_outer_success_reference leaf layer
    ⟨2, by decide⟩ a2 h2'
  obtain ⟨r3, hr3, ha3⟩ := source_decode_outer_success_reference leaf layer
    ⟨3, by decide⟩ a3 h3'
  let refValues : Array RefQM31 4#usize :=
    Array.make 4#usize [r0, r1, r2, r3]
  have hrefFull :
      V5FriDecoderReference.decode_later_leaf_reference leaf layer =
        .ok (.Ok refValues) := by
    unfold V5FriDecoderReference.decode_later_leaf_reference
    rw [← selected_usize_0, hr0]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [← selected_usize_1, hr1]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [← selected_usize_2, hr2]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rw [← selected_usize_3, hr3]
    rfl
  let refValue : RefQM31 := refValues.val[slot.val]!
  refine ⟨refValue, ?_, ?_⟩
  · unfold V5FriDecoderReference.decode_selected_later_slot_reference
    rw [if_neg hslot]
    rw [hrefFull]
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    have hindex :
        Array.index_usize refValues
            (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
          .ok refValue := by
      unfold Array.index_usize refValue
      simp [slot.isLt]
    rw [hindex]
    simp only [bind_tc_ok]
  · calc
      value = (Array.make 4#usize [a0, a1, a2, a3]).val[slot.val]! :=
        hvalue
      _ = refToExactQM31 refValue := by
        fin_cases slot <;>
          simp [refValue, refValues, ha0, ha1, ha2, ha3]

/-- The production/reference equality record formerly supplied by callers is
now constructed from the two universal source proofs above. -/
theorem productionDecoderReferenceEquality :
    ProductionDecoderReferenceEquality where
  full := production_full_decoder_reference_equality
  selected := production_selected_decoder_reference_equality

#print axioms production_full_decoder_reference_equality
#print axioms production_selected_decoder_reference_equality
#print axioms productionDecoderReferenceEquality

end AspisV5FriProductionDecoderEquality
