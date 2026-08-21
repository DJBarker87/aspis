import V5AcceptedEntryGenerated.Entry

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5AcceptedEntryAlphaDecode

open V5AcceptedEntryGenerated

abbrev QM31 := V5AcceptedEntryGenerated.aspis_core.field.QM31
abbrev Parsed := V5AcceptedEntryGenerated.v5_cu_probe.ParsedProbeData
abbrev AlphaIter := core.slice.iter.IterMut QM31
abbrev AlphaEnumerate := core.iter.adapters.enumerate.Enumerate AlphaIter

def writeBackAt (position : Nat) (current : AlphaEnumerate)
    (replacement : Option (Std.Usize × QM31)) : AlphaEnumerate :=
  { current with
    iter :=
      match replacement.map Prod.snd with
      | none => current.iter
      | some value =>
          { current.iter with
            slice := current.iter.slice.setAtNat position value } }

theorem iter_mut_next_active
    (iter : AlphaIter) (hactive : iter.i < iter.slice.len) :
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
    (iter : AlphaIter) (hdone : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (none, iter, fun current _ => current) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_neg hdone]

theorem enumerate_next_active
    (state : AlphaEnumerate) (nextCount : Std.Usize)
    (hactive : state.iter.i < state.iter.slice.len)
    (hcount : state.count + 1#usize = (.ok nextCount : Result Std.Usize)) :
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next
        state =
      .ok (some (state.count, state.iter.slice[state.iter.i]),
        { iter := { state.iter with i := state.iter.i + 1 },
          count := nextCount },
        writeBackAt state.iter.i) := by
  unfold
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next
  have hnext := iter_mut_next_active state.iter hactive
  rw [hnext]
  simp only [bind_tc_ok]
  rw [hcount]
  simp only [bind_tc_ok]
  rfl

theorem enumerate_next_done
    (state : AlphaEnumerate)
    (hdone : ¬ state.iter.i < state.iter.slice.len) :
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next
        state = .ok (none, state, fun current _ => current) := by
  unfold
    V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.next
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

theorem decode_v5_fri_alphas_success_calls
    (parsed : Parsed) (output : Array QM31 4#usize)
    (hrun :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas parsed =
        .ok (.Ok output)) :
    ∃ zero a0 a1 a2 a3 : QM31,
      V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = .ok zero ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.relation_alphas 0#usize = .ok (.Ok a0) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.relation_alphas 1#usize = .ok (.Ok a1) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.relation_alphas 2#usize = .ok (.Ok a2) ∧
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.relation_alphas 3#usize = .ok (.Ok a3) ∧
      output.val = [a0, a1, a2, a3] := by
  unfold V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas at hrun
  generalize hzero :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = zeroResult
    at hrun
  cases zeroResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok zero =>
    simp only [bind_tc_ok] at hrun
    simp only [Aeneas.Std.lift, bind_tc_ok, Array.to_slice_mut,
      core.slice.Slice.iter_mut,
      V5AcceptedEntryGenerated.core.iter.adapters.enumerate.IteratorEnumerateMut.enumerate]
      at hrun
    let state0 : AlphaEnumerate :=
      { iter := { slice := (Array.repeat 4#usize zero).to_slice },
        count := 0#usize }
    change
      (do
        let x ←
          V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas_loop
            parsed state0 (fun e => e)
        match x.1 with
        | none =>
            .ok (core.result.Result.Ok
              ((Array.repeat 4#usize zero).from_slice x.2.iter.slice))
        | some result => .ok result) =
          .ok (core.result.Result.Ok output)
      at hrun
    unfold V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas_loop
      at hrun
    rw [loop.eq_def] at hrun
    unfold V5AcceptedEntryGenerated.v5_cu_probe.decode_v5_fri_alphas_loop.body
      at hrun
    have hactive0 : state0.iter.i < state0.iter.slice.len := by
      simp [state0, Array.repeat, Array.to_slice, Slice.len]
    have hcount0 :
        state0.count + 1#usize = (.ok 1#usize : Result Std.Usize) := by
      simp only [state0]
      have hadd :=
        @UScalar.add_equiv UScalarTy.Usize 0#usize 1#usize
      generalize heq : (0#usize + 1#usize) = addResult at hadd ⊢
      cases addResult with
      | fail error =>
        cases System.Platform.numBits_eq <;> simp_all [UScalar.inBounds]
      | div => simp at hadd
      | ok nextCount =>
        have hvalue : nextCount.val = (1#usize).val := by
          simpa using hadd.2.1
        have hnextCount : nextCount = 1#usize :=
          UScalar.val_eq_imp nextCount 1#usize hvalue
        simp [hnextCount]
    have hnext0 := enumerate_next_active state0 1#usize hactive0 hcount0
    simp only [hnext0, bind_tc_ok] at hrun
    simp only [state0] at hrun
    generalize hcall0 :
        V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
          parsed.relation_alphas 0#usize = call0
      at hrun
    cases call0 with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok decoded0 =>
      cases decoded0 with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame, Bind.bind, Aeneas.Std.bind] at hrun
      | Ok a0 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrun
        rw [loop.eq_def] at hrun
        let state1 : AlphaEnumerate :=
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
            V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
              parsed.relation_alphas 1#usize = call1
          at hrun
        cases call1 with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok decoded1 =>
          cases decoded1 with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              Bind.bind, Aeneas.Std.bind] at hrun
          | Ok a1 =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
              at hrun
            rw [loop.eq_def] at hrun
            let state2 : AlphaEnumerate :=
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
            have hnext2 :=
              enumerate_next_active state2 3#usize hactive2 hcount2
            have hnext2' := hnext2
            simp only [state2] at hnext2'
            simp only [hnext2', bind_tc_ok] at hrun
            generalize hcall2 :
                V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                  parsed.relation_alphas 2#usize = call2
              at hrun
            cases call2 with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
            | ok decoded2 =>
              cases decoded2 with
              | Err error =>
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  Bind.bind, Aeneas.Std.bind] at hrun
              | Ok a2 =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  bind_tc_ok] at hrun
                rw [loop.eq_def] at hrun
                let state3 : AlphaEnumerate :=
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
                    V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                      parsed.relation_alphas 3#usize = call3
                  at hrun
                cases call3 with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | ok decoded3 =>
                  cases decoded3 with
                  | Err error =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      Bind.bind, Aeneas.Std.bind] at hrun
                  | Ok a3 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      bind_tc_ok] at hrun
                    rw [loop.eq_def] at hrun
                    let state4 : AlphaEnumerate :=
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
                    refine ⟨zero, a0, a1, a2, a3, rfl, rfl, rfl, rfl,
                      rfl, ?_⟩
                    injection hrun with houtput
                    injection houtput with harray
                    rw [← harray]
                    simp [writeBackAt, Array.from_slice, Slice.setAtNat,
                      Array.repeat, Array.to_slice]

end AspisV5AcceptedEntryAlphaDecode
