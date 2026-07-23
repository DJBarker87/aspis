import GoodMatricesCurrent.SourceExtractedTerminalFieldAll

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedTerminalPrefixes

open GoodMatricesCurrent.SourceExtractedTerminalField

abbrev LocalPoint := Array LocalQM31 10#usize

def pointEntry (point : LocalPoint) (index : Fin 10) : LocalQM31 :=
  point.val[index.val]'(by rw [point.property]; exact index.isLt)

def pointToExact (point : LocalPoint) : Fin 10 → ExactQM31 :=
  fun index => qm31ToExact (pointEntry point index)

def CanonicalLocalPoint (point : LocalPoint) : Prop :=
  ∀ index : Fin 10, CanonicalLocalQM31 (pointEntry point index)

def oneLocalQM31 : LocalQM31 :=
  { c0 := { a := 1#u32, b := 0#u32 },
    c1 := { a := 0#u32, b := 0#u32 } }

theorem point_index_call (point : LocalPoint) (index : Std.Usize)
    (hindex : index.val < 10) :
    Array.index_usize point index =
      .ok (pointEntry point ⟨index.val, hindex⟩) := by
  exact Array.index_usize_eq_ok_of_getElem_eq point index
    (by rw [point.property]; exact hindex) _ rfl

/-- The current extracted prefix constructor computes exactly the row-prefix
factors for aligned p rows (`111`) and inactive b rows (`010`). -/
theorem deployed_three_bit_prefixes_exact_spec (point : LocalPoint)
    (hpoint : CanonicalLocalPoint point) :
    ∃ aPrefix bPrefix : LocalQM31,
      v5_cu_probe.good_gate_probe.deployed_three_bit_prefixes point =
        .ok (aPrefix, bPrefix) ∧
      CanonicalLocalQM31 aPrefix ∧
      CanonicalLocalQM31 bPrefix ∧
      qm31ToExact aPrefix =
        pointToExact point 0 * pointToExact point 1 * pointToExact point 2 ∧
      qm31ToExact bPrefix =
        pointToExact point 1 * (1 - pointToExact point 0) *
          (1 - pointToExact point 2) := by
  let p0 := pointEntry point 0
  let p1 := pointEntry point 1
  let p2 := pointEntry point 2
  have hp0 : CanonicalLocalQM31 p0 := hpoint 0
  have hp1 : CanonicalLocalQM31 p1 := hpoint 1
  have hp2 : CanonicalLocalQM31 p2 := hpoint 2
  have hp0Call : Array.index_usize point 0#usize = .ok p0 := by
    simpa [p0] using point_index_call point 0#usize (by simp)
  have hp1Call : Array.index_usize point 1#usize = .ok p1 := by
    simpa [p1] using point_index_call point 1#usize (by simp)
  have hp2Call : Array.index_usize point 2#usize = .ok p2 := by
    simpa [p2] using point_index_call point 2#usize (by simp)
  have honeCall : aspis_verifier.aspis_core.field.QM31.ONE =
      .ok oneLocalQM31 := by
    simpa [oneLocalQM31] using local_one_call
  have honeCanonical : CanonicalLocalQM31 oneLocalQM31 := by
    simpa [oneLocalQM31] using local_one_canonical
  have honeExact : qm31ToExact oneLocalQM31 = 1 := by
    simpa [oneLocalQM31] using local_one_exact
  rcases local_qm31_mul_corresponds p0 p2 hp0 hp2 with
    ⟨p0p2, hp0p2Call, hp0p2Canonical, hp0p2Exact⟩
  rcases local_prepared_new_corresponds p1 hp1 with
    ⟨preparedP1, hpreparedP1Call, hpreparedP1⟩
  rcases local_prepared_mul_corresponds preparedP1 p1 p0p2
      hpreparedP1 hp1 hp0p2Canonical with
    ⟨aPrefix, haCall, haCanonical, haExact⟩
  rcases local_qm31_sub_corresponds oneLocalQM31 p0
      honeCanonical hp0 with
    ⟨oneMinusP0, hsub0Call, hsub0Canonical, hsub0Exact⟩
  rcases local_qm31_sub_corresponds oneMinusP0 p2
      hsub0Canonical hp2 with
    ⟨oneMinusP0MinusP2, hsub2Call, hsub2Canonical, hsub2Exact⟩
  rcases local_qm31_add_corresponds oneMinusP0MinusP2 p0p2
      hsub2Canonical hp0p2Canonical with
    ⟨bOuter, hbOuterCall, hbOuterCanonical, hbOuterExact⟩
  rcases local_prepared_mul_corresponds preparedP1 p1 bOuter
      hpreparedP1 hp1 hbOuterCanonical with
    ⟨bPrefix, hbCall, hbCanonical, hbExact⟩
  refine ⟨aPrefix, bPrefix, ?_, haCanonical, hbCanonical, ?_, ?_⟩
  · unfold v5_cu_probe.good_gate_probe.deployed_three_bit_prefixes
    rw [hp0Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hp2Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hp0p2Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hp1Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hpreparedP1Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [haCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [honeCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsub0Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsub2Call]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hbOuterCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hbCall]
    simp only [Aeneas.Std.bind_tc_ok]
  · rw [haExact, hp0p2Exact]
    change _ = qm31ToExact p0 * qm31ToExact p1 * qm31ToExact p2
    ring
  · rw [hbExact, hbOuterExact, hsub2Exact, hsub0Exact, hp0p2Exact,
      honeExact]
    change _ = qm31ToExact p1 * (1 - qm31ToExact p0) *
      (1 - qm31ToExact p2)
    ring

def PreparedTerminalScalesFor
    (scales : v5_cu_probe.good_gate_probe.PreparedTerminalScales)
    (aPrefix bPrefix last : LocalQM31) : Prop :=
  ∃ aP aQ bP : LocalQM31,
    CanonicalLocalQM31 aP ∧ CanonicalLocalQM31 aQ ∧
    CanonicalLocalQM31 bP ∧
    qm31ToExact aP = qm31ToExact aPrefix * (1 - qm31ToExact last) ∧
    qm31ToExact aQ = qm31ToExact aPrefix * qm31ToExact last ∧
    qm31ToExact bP = qm31ToExact bPrefix * (1 - qm31ToExact last) ∧
    PreparedFor scales.a_p aP ∧ PreparedFor scales.a_q aQ ∧
    PreparedFor scales.b_p bP

/-- Exact source-extracted correspondence for the three prepared terminal
scales used by both the A and B matrix writers. -/
theorem prepared_terminal_scales_exact_spec (aPrefix bPrefix last : LocalQM31)
    (ha : CanonicalLocalQM31 aPrefix)
    (hb : CanonicalLocalQM31 bPrefix)
    (hlast : CanonicalLocalQM31 last) :
    ∃ scales,
      v5_cu_probe.good_gate_probe.prepared_terminal_scales
          aPrefix bPrefix last = .ok scales ∧
      PreparedTerminalScalesFor scales aPrefix bPrefix last := by
  have honeCall : aspis_verifier.aspis_core.field.QM31.ONE =
      .ok oneLocalQM31 := by
    simpa [oneLocalQM31] using local_one_call
  have honeCanonical : CanonicalLocalQM31 oneLocalQM31 := by
    simpa [oneLocalQM31] using local_one_canonical
  have honeExact : qm31ToExact oneLocalQM31 = 1 := by
    simpa [oneLocalQM31] using local_one_exact
  rcases local_qm31_sub_corresponds oneLocalQM31 last
      honeCanonical hlast with
    ⟨oneMinusLast, hsubCall, hsubCanonical, hsubExact⟩
  rcases local_qm31_mul_corresponds aPrefix oneMinusLast ha hsubCanonical with
    ⟨aP, haPCall, haPCanonical, haPExact⟩
  rcases local_prepared_new_corresponds aP haPCanonical with
    ⟨preparedAP, hpreparedAPCall, hpreparedAP⟩
  rcases local_qm31_mul_corresponds aPrefix last ha hlast with
    ⟨aQ, haQCall, haQCanonical, haQExact⟩
  rcases local_prepared_new_corresponds aQ haQCanonical with
    ⟨preparedAQ, hpreparedAQCall, hpreparedAQ⟩
  rcases local_qm31_mul_corresponds bPrefix oneMinusLast hb hsubCanonical with
    ⟨bP, hbPCall, hbPCanonical, hbPExact⟩
  rcases local_prepared_new_corresponds bP hbPCanonical with
    ⟨preparedBP, hpreparedBPCall, hpreparedBP⟩
  let scales : v5_cu_probe.good_gate_probe.PreparedTerminalScales :=
    { a_p := preparedAP, a_q := preparedAQ, b_p := preparedBP }
  refine ⟨scales, ?_, aP, aQ, bP, haPCanonical, haQCanonical,
    hbPCanonical, ?_, ?_, ?_, hpreparedAP, hpreparedAQ, hpreparedBP⟩
  · unfold v5_cu_probe.good_gate_probe.prepared_terminal_scales
    rw [honeCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hsubCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [haPCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hpreparedAPCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [haQCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hpreparedAQCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hbPCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [hpreparedBPCall]
    simp only [Aeneas.Std.bind_tc_ok]
    rfl
  · rw [haPExact, hsubExact, honeExact]
  · exact haQExact
  · rw [hbPExact, hsubExact, honeExact]

end GoodMatricesCurrent.SourceExtractedTerminalPrefixes
