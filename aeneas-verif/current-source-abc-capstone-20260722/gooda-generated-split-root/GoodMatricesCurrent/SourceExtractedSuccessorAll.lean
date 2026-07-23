import GoodMatricesCurrent.SourceExtractedSuccessor

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedSuccessor

open GoodMatricesCurrent.SourceExtractedTerminalField
open AspisV5ComponentADeployedTerminalApplicability

private abbrev successorBody :=
  v5_cu_probe.good_gate_probe.binary_successor_point_loop.body

private abbrev successorLoop :=
  v5_cu_probe.good_gate_probe.binary_successor_point_loop

private theorem pred_lt_of_eq_sub_one {current next : Nat}
    (hpositive : 1 ≤ current) (hnext : next = current - 1) :
    next < current := by
  omega

private theorem eq_zero_of_not_one_le {value : Nat}
    (h : ¬ 1 ≤ value) : value = 0 := by
  omega

private theorem successorBody_done (point successor : LocalPoint)
    (carry : LocalQM31) (coordinate : Std.Usize)
    (hzero : coordinate.val = 0) :
    successorBody point successor carry coordinate = .ok (.done successor) := by
  have hcondition : ¬ coordinate > 0#usize := by
    intro hgt
    have hpositive := (UScalar.lt_equiv _ _).1 hgt
    rw [hzero] at hpositive
    exact (Nat.lt_irrefl 0) hpositive
  unfold successorBody
  unfold v5_cu_probe.good_gate_probe.binary_successor_point_loop.body
  rw [if_neg hcondition]

theorem successorBody_transition_spec (point : LocalPoint)
    (hpoint : CanonicalLocalPoint point)
    (successor : LocalPoint) (carry : LocalQM31) (coordinate : Std.Usize)
    (hstate : SuccessorInvariant (pointToExact point)
      successor carry coordinate) :
    ∃ flow,
      successorBody point successor carry coordinate = .ok flow ∧
      (match flow with
        | .done result => CanonicalLocalPoint result ∧
            pointToExact result = deployedSuccessorPoint (pointToExact point)
        | .cont next =>
            SuccessorInvariant (pointToExact point)
              next.1 next.2.1 next.2.2 ∧
            next.2.2.val < coordinate.val) := by
  by_cases hpositive : 1 ≤ coordinate.val
  · rcases successorBody_step point successor carry coordinate
      hpoint hstate hpositive with
      ⟨next, hbody, hcoordinate, hnext⟩
    refine ⟨ControlFlow.cont next, hbody, ?_⟩
    change SuccessorInvariant (pointToExact point)
      next.1 next.2.1 next.2.2 ∧
      next.2.2.val < coordinate.val
    exact ⟨hnext, pred_lt_of_eq_sub_one hpositive hcoordinate⟩
  · have hzero : coordinate.val = 0 :=
      eq_zero_of_not_one_le hpositive
    have hdone := successorBody_done point successor carry coordinate hzero
    refine ⟨ControlFlow.done successor, hdone, ?_⟩
    change CanonicalLocalPoint successor ∧
      pointToExact successor = deployedSuccessorPoint (pointToExact point)
    refine ⟨hstate.1, ?_⟩
    rw [← sourceSuccessor_eq_deployed]
    funext output
    apply hstate.2.2.2.2 output
    rw [hzero]
    exact Nat.zero_le output.val

theorem successorLoop_wp_spec (point : LocalPoint)
    (hpoint : CanonicalLocalPoint point) :
    Aeneas.Std.WP.spec
      (successorLoop point zeroPoint oneLocalQM31 10#usize)
      (fun result => CanonicalLocalPoint result ∧
        pointToExact result = deployedSuccessorPoint (pointToExact point)) := by
  have honeCanonical : CanonicalLocalQM31 oneLocalQM31 := by
    simpa [oneLocalQM31] using local_one_canonical
  have honeExact : qm31ToExact oneLocalQM31 = 1 := by
    simpa [oneLocalQM31] using local_one_exact
  have hten : (10#usize : Std.Usize).val = 10 := by rfl
  have hinitial : SuccessorInvariant (pointToExact point)
      zeroPoint oneLocalQM31 10#usize := by
    refine ⟨zeroPoint_canonical, honeCanonical, by simp, ?_, ?_⟩
    · rw [honeExact, hten, tailProduct_ten]
    · intro output houtput
      exact False.elim ((Nat.not_lt_of_ge houtput) output.isLt)
  unfold successorLoop
  unfold v5_cu_probe.good_gate_probe.binary_successor_point_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun state => state.2.2.val)
    (inv := fun state => SuccessorInvariant (pointToExact point)
      state.1 state.2.1 state.2.2)
  · rintro ⟨successor, carry, coordinate⟩ hstate
    simp only
    apply Aeneas.Std.WP.exists_imp_spec
    have htransition :=
      successorBody_transition_spec point hpoint successor carry coordinate hstate
    unfold successorBody at htransition
    rcases htransition with ⟨flow, hcall, hpost⟩
    refine ⟨flow, hcall, ?_⟩
    cases flow <;> exact hpost
  · exact hinitial

/-- Premise-free current-source correspondence for the authentic polynomial
binary-successor implementation. -/
theorem binary_successor_point_exact_spec (point : LocalPoint)
    (hpoint : CanonicalLocalPoint point) :
    ∃ result : LocalPoint,
      v5_cu_probe.good_gate_probe.binary_successor_point point = .ok result ∧
      CanonicalLocalPoint result ∧
      pointToExact result = deployedSuccessorPoint (pointToExact point) := by
  rcases Aeneas.Std.WP.spec_imp_exists
      (successorLoop_wp_spec point hpoint) with
    ⟨result, hloop, hcanonical, hexact⟩
  refine ⟨result, ?_, hcanonical, hexact⟩
  unfold v5_cu_probe.good_gate_probe.binary_successor_point
  rw [local_zero_call]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [local_one_call]
  simp only [Aeneas.Std.bind_tc_ok]
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  have hlen : (Array.to_slice point).len = 10#usize := by
    apply UScalar.val_eq_imp
    rw [Slice.len_val, Array.length_to_slice]
  rw [hlen]
  simpa only [successorLoop, zeroPoint, zeroLocalQM31, oneLocalQM31] using hloop

end GoodMatricesCurrent.SourceExtractedSuccessor
