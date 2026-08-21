import V5RelationLinkedGroupedRows

namespace AspisV5RelationLinkedGroupTuplePatterns

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

private theorem oneCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem zeroCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem addMaintainedCorresponds
    (left right : RawQM31)
    (leftCanonical : CanonicalQM31 left)
    (rightCanonical : CanonicalQM31 right) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.add left right = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left + toMaintainedExact right := by
  obtain ⟨out, run, canonical, exact⟩ :=
    generated_qm31_add_corresponds left right leftCanonical rightCanonical
  have maintained := congrArg oldQm31ToMaintained exact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_add] at maintained
  exact ⟨out, run, canonical, maintained⟩

private theorem mulMaintainedCorresponds
    (left right : RawQM31)
    (leftCanonical : CanonicalQM31 left)
    (rightCanonical : CanonicalQM31 right) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.mul left right = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left * toMaintainedExact right := by
  obtain ⟨out, run, canonical, exact⟩ :=
    generated_qm31_mul_corresponds left right leftCanonical rightCanonical
  have maintained := congrArg oldQm31ToMaintained exact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_mul] at maintained
  exact ⟨out, run, canonical, maintained⟩

private theorem halfMaintainedCorresponds
    (value : RawQM31) (canonical : CanonicalQM31 value) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.field.QM31.half value = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out + toMaintainedExact out =
        toMaintainedExact value := by
  obtain ⟨out, run, outCanonical, exact⟩ :=
    generated_qm31_half_corresponds value canonical
  have maintained := congrArg oldQm31ToMaintained exact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_add] at maintained
  exact ⟨out, run, outCanonical, maintained⟩

def quarterTwo
    (left right : RawQM31) : Result RawQM31 := do
  let sum0 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO left
  let sum1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add sum0 right
  let half1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half sum1
  V5RelationLinkedGenerated.aspis_core.field.QM31.half half1

theorem quarterTwoCorresponds
    (left right : RawQM31)
    (leftCanonical : CanonicalQM31 left)
    (rightCanonical : CanonicalQM31 right) :
    ∃ out,
      quarterTwo left right = ok out ∧
      CanonicalQM31 out ∧
      (4 : ExactQM31) * toMaintainedExact out =
        toMaintainedExact left + toMaintainedExact right := by
  obtain ⟨sum0, sum0Run, sum0Canonical, sum0Exact⟩ :=
    addMaintainedCorresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO left
      zeroCanonical leftCanonical
  obtain ⟨sum1, sum1Run, sum1Canonical, sum1Exact⟩ :=
    addMaintainedCorresponds sum0 right sum0Canonical rightCanonical
  obtain ⟨half1, half1Run, half1Canonical, half1Exact⟩ :=
    halfMaintainedCorresponds sum1 sum1Canonical
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    halfMaintainedCorresponds half1 half1Canonical
  refine ⟨out, ?_, outCanonical, ?_⟩
  · simp [quarterTwo, sum0Run, sum1Run, half1Run, outRun]
  · have zeroExact :
        toMaintainedExact
            V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = 0 := by
      rfl
    calc
      (4 : ExactQM31) * toMaintainedExact out =
          (toMaintainedExact out + toMaintainedExact out) +
            (toMaintainedExact out + toMaintainedExact out) := by ring
      _ = toMaintainedExact half1 + toMaintainedExact half1 := by
        rw [outExact]
      _ = toMaintainedExact sum1 := half1Exact
      _ = toMaintainedExact sum0 + toMaintainedExact right := sum1Exact
      _ = (toMaintainedExact
          V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO +
            toMaintainedExact left) + toMaintainedExact right := by
        rw [sum0Exact]
      _ = toMaintainedExact left + toMaintainedExact right := by
        rw [zeroExact]
        ring

def pairPairProgram
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (alpha alpha2 alpha3 : RawQM31) : Result RawQM31 := do
  let coefficient0 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
  let coefficient1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add
    alpha2 alpha
  let value0 ← Slice.index_usize groupValues (UScalar.cast .Usize group0)
  let value1 ← Slice.index_usize groupValues (UScalar.cast .Usize group1)
  let contribution0 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul
    value0 coefficient0
  let contribution1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul
    value1 coefficient1
  quarterTwo contribution0 contribution1

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem releasedPairPairSource :
    ∀ (groupValues : Slice RawQM31) (alpha alpha2 alpha3 : RawQM31),
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
        (Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8])
        groupValues alpha alpha2 alpha3 =
      pairPairProgram 0#u8 1#u8 groupValues alpha alpha2 alpha3 := by
  intro groupValues alpha alpha2 alpha3
  simp (config := { maxSteps := 1000000 })
    [V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple,
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0,
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0.body,
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0,
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop0.body,
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1,
    V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple_loop0_loop1.body,
    pairPairProgram, quarterTwo, loop.eq_1, Array.index_usize, Array.update,
    Slice.index_usize, UScalar.lt_equiv, Std.lift]

theorem pairPairProgramCorresponds
    (group0 group1 : Std.U8) (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group0) = ok value0)
    (value1Run :
      Slice.index_usize groupValues (UScalar.cast .Usize group1) = ok value1)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      pairPairProgram group0 group1 groupValues alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value0,
            toMaintainedExact value1, toMaintainedExact value1] index) := by
  obtain ⟨coefficient0, coefficient0Run, coefficient0Canonical,
      coefficient0Exact⟩ :=
    addMaintainedCorresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE alpha3
      oneCanonical alpha3Canonical
  obtain ⟨coefficient1, coefficient1Run, coefficient1Canonical,
      coefficient1Exact⟩ :=
    addMaintainedCorresponds alpha2 alpha alpha2Canonical alphaCanonical
  obtain ⟨contribution0, contribution0Run, contribution0Canonical,
      contribution0Exact⟩ :=
    mulMaintainedCorresponds value0 coefficient0 value0Canonical
      coefficient0Canonical
  obtain ⟨contribution1, contribution1Run, contribution1Canonical,
      contribution1Exact⟩ :=
    mulMaintainedCorresponds value1 coefficient1 value1Canonical
      coefficient1Canonical
  obtain ⟨out, quarterRun, outCanonical, quarterExact⟩ :=
    quarterTwoCorresponds contribution0 contribution1 contribution0Canonical
      contribution1Canonical
  refine ⟨out, ?_, outCanonical, ?_⟩
  · simp [pairPairProgram, coefficient0Run, coefficient1Run, value0Run,
      value1Run, contribution0Run, contribution1Run, quarterRun]
  · have oneExact :
        toMaintainedExact
            V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = 1 := by
      rfl
    have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
    apply (eq_div_iff fourNonzero).2
    simp
    calc
      toMaintainedExact out * 4 =
          (4 : ExactQM31) * toMaintainedExact out := by ring
      _ = toMaintainedExact contribution0 +
          toMaintainedExact contribution1 := quarterExact
      _ = toMaintainedExact value0 * toMaintainedExact coefficient0 +
          toMaintainedExact value1 * toMaintainedExact coefficient1 := by
        rw [contribution0Exact, contribution1Exact]
      _ = toMaintainedExact value0 *
            ((1 : ExactQM31) + toMaintainedExact alpha ^ 3) +
          toMaintainedExact value1 *
            (toMaintainedExact alpha ^ 2 + toMaintainedExact alpha) := by
        rw [coefficient0Exact, coefficient1Exact, oneExact, alpha2Exact,
          alpha3Exact]
      _ = toMaintainedExact value0 +
          toMaintainedExact alpha ^ 3 * toMaintainedExact value0 +
          toMaintainedExact alpha ^ 2 * toMaintainedExact value1 +
          toMaintainedExact alpha * toMaintainedExact value1 := by ring

theorem releasedPairPairCorresponds
    (groupValues : Slice RawQM31)
    (value0 value1 alpha alpha2 alpha3 : RawQM31)
    (value0Run : Slice.index_usize groupValues 0#usize = ok value0)
    (value1Run : Slice.index_usize groupValues 1#usize = ok value1)
    (value0Canonical : CanonicalQM31 value0)
    (value1Canonical : CanonicalQM31 value1)
    (alphaCanonical : CanonicalQM31 alpha)
    (alpha2Canonical : CanonicalQM31 alpha2)
    (alpha3Canonical : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out,
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_group_tuple
          (Array.make 4#usize [0#u8, 0#u8, 1#u8, 1#u8])
          groupValues alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact value0, toMaintainedExact value0,
            toMaintainedExact value1, toMaintainedExact value1] index) := by
  obtain ⟨out, run, canonical, exact⟩ :=
    pairPairProgramCorresponds 0#u8 1#u8 groupValues value0 value1 alpha
      alpha2 alpha3 (by simpa using value0Run) (by simpa using value1Run)
      value0Canonical value1Canonical alphaCanonical alpha2Canonical
      alpha3Canonical alpha2Exact alpha3Exact
  refine ⟨out, ?_, canonical, exact⟩
  rw [releasedPairPairSource]
  exact run

end AspisV5RelationLinkedGroupTuplePatterns
