import V5RelationLinkedFieldProjection
import AspisFormal.V5FriRelationCandidateBridge

/-!
# Exact arithmetic of one production dual-weight fibre

The dense and grouped relation-weight folds use the same seven-operation
kernel: three products, three additions, and two halvings.  This file proves
that exact extracted kernel is the maintained dual fold
`[1, alpha^3, alpha^2, alpha] / 4` on canonical QM31 values.
-/

namespace AspisV5RelationLinkedFoldArithmetic

open Aeneas Aeneas.Std Result
open AspisV5RelationLinkedFieldProjection

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def oldCm31ToMaintained
    (x : ComponentBRealEvaluatorProof.ExactCM31) :
    AspisV5ComponentCQM31TowerExact.CM31Exact := ⟨x.re, x.im⟩

def oldQm31ToMaintained
    (x : ComponentBRealEvaluatorProof.ExactQM31) : ExactQM31 :=
  ⟨oldCm31ToMaintained x.re, oldCm31ToMaintained x.im⟩

@[simp] theorem oldCm31ToMaintained_add
    (x y : ComponentBRealEvaluatorProof.ExactCM31) :
    oldCm31ToMaintained (x + y) =
      oldCm31ToMaintained x + oldCm31ToMaintained y := by
  ext <;> rfl

@[simp] theorem oldCm31ToMaintained_mul
    (x y : ComponentBRealEvaluatorProof.ExactCM31) :
    oldCm31ToMaintained (x * y) =
      oldCm31ToMaintained x * oldCm31ToMaintained y := by
  ext <;> simp [oldCm31ToMaintained]

@[simp] theorem oldQm31ToMaintained_add
    (x y : ComponentBRealEvaluatorProof.ExactQM31) :
    oldQm31ToMaintained (x + y) =
      oldQm31ToMaintained x + oldQm31ToMaintained y := by
  ext <;> rfl

@[simp] theorem oldQm31ToMaintained_sub
    (x y : ComponentBRealEvaluatorProof.ExactQM31) :
    oldQm31ToMaintained (x - y) =
      oldQm31ToMaintained x - oldQm31ToMaintained y := by
  rfl

@[simp] theorem oldQm31ToMaintained_mul
    (x y : ComponentBRealEvaluatorProof.ExactQM31) :
    oldQm31ToMaintained (x * y) =
      oldQm31ToMaintained x * oldQm31ToMaintained y := by
  rfl

@[simp] theorem oldQm31ToMaintained_toExact (x : RawQM31) :
    oldQm31ToMaintained (toExact x) = toMaintainedExact x := by
  rfl

def linkedFoldFour
    (q0 q1 q2 q3 alpha alpha2 alpha3 : RawQM31) : Result RawQM31 := do
  let p1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha3 q1
  let s1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add q0 p1
  let p2 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha2 q2
  let s2 ← V5RelationLinkedGenerated.aspis_core.field.QM31.add s1 p2
  let p3 ← V5RelationLinkedGenerated.aspis_core.field.QM31.mul alpha q3
  let folded ← V5RelationLinkedGenerated.aspis_core.field.QM31.add s2 p3
  let half1 ← V5RelationLinkedGenerated.aspis_core.field.QM31.half folded
  V5RelationLinkedGenerated.aspis_core.field.QM31.half half1

theorem linkedFoldFour_corresponds
    (q0 q1 q2 q3 alpha alpha2 alpha3 : RawQM31)
    (hq0 : CanonicalQM31 q0) (hq1 : CanonicalQM31 q1)
    (hq2 : CanonicalQM31 q2) (hq3 : CanonicalQM31 q3)
    (ha : CanonicalQM31 alpha) (ha2 : CanonicalQM31 alpha2)
    (ha3 : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3) :
    ∃ out : RawQM31,
      linkedFoldFour q0 q1 q2 q3 alpha alpha2 alpha3 = ok out ∧
      CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact q0, toMaintainedExact q1,
            toMaintainedExact q2, toMaintainedExact q3] index) := by
  obtain ⟨p1, hp1, hcp1, ep1⟩ :=
    generated_qm31_mul_corresponds alpha3 q1 ha3 hq1
  obtain ⟨s1, hs1, hcs1, es1⟩ :=
    generated_qm31_add_corresponds q0 p1 hq0 hcp1
  obtain ⟨p2, hp2, hcp2, ep2⟩ :=
    generated_qm31_mul_corresponds alpha2 q2 ha2 hq2
  obtain ⟨s2, hs2, hcs2, es2⟩ :=
    generated_qm31_add_corresponds s1 p2 hcs1 hcp2
  obtain ⟨p3, hp3, hcp3, ep3⟩ :=
    generated_qm31_mul_corresponds alpha q3 ha hq3
  obtain ⟨folded, hfolded, hcfolded, efolded⟩ :=
    generated_qm31_add_corresponds s2 p3 hcs2 hcp3
  obtain ⟨half1, hhalf1, hchalf1, ehalf1⟩ :=
    generated_qm31_half_corresponds folded hcfolded
  obtain ⟨out, hout, hcout, eout⟩ :=
    generated_qm31_half_corresponds half1 hchalf1
  refine ⟨out, ?_, hcout, ?_⟩
  · simp [linkedFoldFour, hp1, hs1, hp2, hs2, hp3, hfolded, hhalf1,
      hout]
  · have fourNonzero : (4 : ExactQM31) ≠ 0 := by decide
    apply (eq_div_iff fourNonzero).2
    simp
    have ep1M := congrArg oldQm31ToMaintained ep1
    have es1M := congrArg oldQm31ToMaintained es1
    have ep2M := congrArg oldQm31ToMaintained ep2
    have es2M := congrArg oldQm31ToMaintained es2
    have ep3M := congrArg oldQm31ToMaintained ep3
    have efoldedM := congrArg oldQm31ToMaintained efolded
    have ehalf1M := congrArg oldQm31ToMaintained ehalf1
    have eoutM := congrArg oldQm31ToMaintained eout
    simp only [oldQm31ToMaintained_toExact, oldQm31ToMaintained_add,
      oldQm31ToMaintained_mul] at ep1M es1M ep2M es2M ep3M efoldedM ehalf1M eoutM
    calc
      toMaintainedExact out * 4 =
          (toMaintainedExact out + toMaintainedExact out) +
            (toMaintainedExact out + toMaintainedExact out) := by ring
      _ = toMaintainedExact half1 + toMaintainedExact half1 := by
        rw [eoutM]
      _ = toMaintainedExact folded := ehalf1M
      _ = toMaintainedExact s2 + toMaintainedExact p3 := efoldedM
      _ = (toMaintainedExact s1 + toMaintainedExact p2) +
          toMaintainedExact p3 := by
        rw [es2M]
      _ = ((toMaintainedExact q0 + toMaintainedExact p1) +
          toMaintainedExact p2) + toMaintainedExact p3 := by
        rw [es1M]
      _ = toMaintainedExact q0 +
          toMaintainedExact alpha ^ 3 * toMaintainedExact q1 +
          toMaintainedExact alpha ^ 2 * toMaintainedExact q2 +
          toMaintainedExact alpha * toMaintainedExact q3 := by
        rw [ep1M, ep2M, ep3M, alpha2Exact, alpha3Exact]

theorem linkedFoldFour_success_exact
    (q0 q1 q2 q3 alpha alpha2 alpha3 out : RawQM31)
    (hq0 : CanonicalQM31 q0) (hq1 : CanonicalQM31 q1)
    (hq2 : CanonicalQM31 q2) (hq3 : CanonicalQM31 q3)
    (ha : CanonicalQM31 alpha) (ha2 : CanonicalQM31 alpha2)
    (ha3 : CanonicalQM31 alpha3)
    (alpha2Exact : toMaintainedExact alpha2 = toMaintainedExact alpha ^ 2)
    (alpha3Exact : toMaintainedExact alpha3 = toMaintainedExact alpha ^ 3)
    (success : linkedFoldFour q0 q1 q2 q3 alpha alpha2 alpha3 = ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        AspisV5FriRelationCandidateBridge.dualWeightFoldValue
          (toMaintainedExact alpha)
          (fun index => ![toMaintainedExact q0, toMaintainedExact q1,
            toMaintainedExact q2, toMaintainedExact q3] index) := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    linkedFoldFour_corresponds q0 q1 q2 q3 alpha alpha2 alpha3 hq0 hq1
      hq2 hq3 ha ha2 ha3 alpha2Exact alpha3Exact
  rw [success] at expectedRun
  cases expectedRun
  exact ⟨expectedCanonical, expectedExact⟩

#print axioms linkedFoldFour_corresponds
#print axioms linkedFoldFour_success_exact

end AspisV5RelationLinkedFoldArithmetic
