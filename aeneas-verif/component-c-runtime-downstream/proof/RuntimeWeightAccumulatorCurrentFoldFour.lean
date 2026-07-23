import RuntimeWeightAccumulatorCurrentArithmetic

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorCurrentFoldFour

open ComponentCRuntimeCanonicalGenerated
open RuntimeWeightAccumulatorCurrentArithmetic

abbrev RawQM31 := aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

/-- The exact arithmetic subsequence executed by the distinct-four arm of
`fold_group_tuple`: coefficients are `1, alpha3, alpha2, alpha`, followed by
the two generated halvings. -/
def currentFoldFour
    (q0 q1 q2 q3 alpha alpha2 alpha3 : RawQM31) : Result RawQM31 := do
  let initial ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q0
  let p1 ← aspis_core.field.QM31.mul q1 alpha3
  let s1 ← aspis_core.field.QM31.add initial p1
  let p2 ← aspis_core.field.QM31.mul q2 alpha2
  let s2 ← aspis_core.field.QM31.add s1 p2
  let p3 ← aspis_core.field.QM31.mul q3 alpha
  let folded ← aspis_core.field.QM31.add s2 p3
  let half1 ← aspis_core.field.QM31.half folded
  aspis_core.field.QM31.half half1

/-- Direct current-universe Level-3 arithmetic for one supplied distinct-four
group tuple.  No semantic-faithfulness or cross-extraction premise occurs. -/
theorem current_fold_four_corresponds
    (q0 q1 q2 q3 alpha alpha2 alpha3 : RawQM31)
    (hq0 : CanonicalQM31 q0) (hq1 : CanonicalQM31 q1)
    (hq2 : CanonicalQM31 q2) (hq3 : CanonicalQM31 q3)
    (ha : CanonicalQM31 alpha) (ha2 : CanonicalQM31 alpha2)
    (ha3 : CanonicalQM31 alpha3) :
    ∃ out,
      currentFoldFour q0 q1 q2 q3 alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      (4 : ExactQM31) * qm31View out =
        qm31View q0 + qm31View alpha3 * qm31View q1 +
          qm31View alpha2 * qm31View q2 + qm31View alpha * qm31View q3 := by
  rcases current_qm31_add_corresponds aspis_core.field.QM31.ZERO q0
      current_qm31_zero_canonical hq0 with
    ⟨initial, hinitial, hcanInitial, hviewInitial⟩
  rcases current_qm31_mul_corresponds q1 alpha3 hq1 ha3 with
    ⟨p1, hp1, hcanP1, hviewP1⟩
  rcases current_qm31_add_corresponds initial p1 hcanInitial hcanP1 with
    ⟨s1, hs1, hcanS1, hviewS1⟩
  rcases current_qm31_mul_corresponds q2 alpha2 hq2 ha2 with
    ⟨p2, hp2, hcanP2, hviewP2⟩
  rcases current_qm31_add_corresponds s1 p2 hcanS1 hcanP2 with
    ⟨s2, hs2, hcanS2, hviewS2⟩
  rcases current_qm31_mul_corresponds q3 alpha hq3 ha with
    ⟨p3, hp3, hcanP3, hviewP3⟩
  rcases current_qm31_add_corresponds s2 p3 hcanS2 hcanP3 with
    ⟨folded, hfolded, hcanFolded, hviewFolded⟩
  rcases current_qm31_half_corresponds folded hcanFolded with
    ⟨half1, hhalf1, hcanHalf1, hviewHalf1⟩
  rcases current_qm31_half_corresponds half1 hcanHalf1 with
    ⟨out, hout, hcanOut, hviewOut⟩
  refine ⟨out, ?_, hcanOut, ?_⟩
  · simp [currentFoldFour, hinitial, hp1, hs1, hp2, hs2, hp3,
      hfolded, hhalf1, hout]
  · calc
      (4 : ExactQM31) * qm31View out =
          (qm31View out + qm31View out) +
            (qm31View out + qm31View out) := by ring
      _ = qm31View half1 + qm31View half1 := by rw [hviewOut]
      _ = qm31View folded := hviewHalf1
      _ = qm31View s2 + qm31View p3 := hviewFolded
      _ = (qm31View s1 + qm31View p2) + qm31View p3 := by rw [hviewS2]
      _ = ((qm31View initial + qm31View p1) + qm31View p2) +
          qm31View p3 := by rw [hviewS1]
      _ = (((qm31View aspis_core.field.QM31.ZERO + qm31View q0) +
          qm31View p1) + qm31View p2) + qm31View p3 := by
        rw [hviewInitial]
      _ = qm31View q0 + qm31View alpha3 * qm31View q1 +
          qm31View alpha2 * qm31View q2 +
          qm31View alpha * qm31View q3 := by
        rw [current_qm31_zero_view, hviewP1, hviewP2, hviewP3]
        ring

#print axioms current_fold_four_corresponds

end ComponentCRuntimeCanonicalGenerated.RuntimeWeightAccumulatorCurrentFoldFour
