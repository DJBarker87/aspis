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
    ∃ a0 a1 a2 a3 : QM31,
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
  generalize hcall0 :
      V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
        parsed.relation_alphas 0#usize = call0 at hrun
  cases call0 with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok decoded0 =>
    cases decoded0 with
    | Err error => simp at hrun
    | Ok a0 =>
      simp only [bind_tc_ok] at hrun
      generalize hcall1 :
          V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
            parsed.relation_alphas 1#usize = call1 at hrun
      cases call1 with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok decoded1 =>
        cases decoded1 with
        | Err error => simp at hrun
        | Ok a1 =>
          simp only [bind_tc_ok] at hrun
          generalize hcall2 :
              V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                parsed.relation_alphas 2#usize = call2 at hrun
          cases call2 with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok decoded2 =>
            cases decoded2 with
            | Err error => simp at hrun
            | Ok a2 =>
              simp only [bind_tc_ok] at hrun
              generalize hcall3 :
                  V5AcceptedEntryGenerated.v5_cu_probe.decode_qm31
                    parsed.relation_alphas 3#usize = call3 at hrun
              cases call3 with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok decoded3 =>
                cases decoded3 with
                | Err error => simp at hrun
                | Ok a3 =>
                  simp only [bind_tc_ok, Result.ok.injEq,
                    core.result.Result.Ok.injEq] at hrun
                  refine ⟨a0, a1, a2, a3, rfl, rfl, rfl, rfl, ?_⟩
                  simpa [Array.make] using congrArg (fun x => x.val) hrun.symm

end AspisV5AcceptedEntryAlphaDecode
