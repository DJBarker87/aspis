import V5RelationLinkedGroupedFold

/-!
# Maintained-field semantics of the released deferred binary low folds

`fold_binary_low_masks` is the only specialized arithmetic in the released
grouped relation component.  It delays two arity-four folds, builds the seven
fixed group values from the two saved challenges, and then lets the ordinary
grouped-row path finish the remaining two folds.

This file exposes small, reusable consequences of every successful primitive
field call in that helper.  The statements use the same maintained exact field
as the relation proof and therefore do not introduce an alternative arithmetic
model.
-/

namespace AspisV5RelationLinkedGroupedLowSemantics

open Aeneas Aeneas.Std Result ControlFlow
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedFoldArithmetic
open AspisV5RelationLinkedGroupedFold

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

private theorem zeroCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem oneCanonical :
    CanonicalQM31 V5RelationLinkedGenerated.aspis_core.field.QM31.ONE := by
  norm_num [CanonicalQM31, CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

@[simp] theorem zero_toMaintained :
    toMaintainedExact
        V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO = 0 := by
  rw [V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO]
  rfl

@[simp] theorem one_toMaintained :
    toMaintainedExact
        V5RelationLinkedGenerated.aspis_core.field.QM31.ONE = 1 := by
  rw [V5RelationLinkedGenerated.aspis_core.field.QM31.ONE]
  rfl

theorem add_run_corresponds
    (left right out : RawQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.add left right =
      ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left + toMaintainedExact right := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_add_corresponds left right hleft hright
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  have maintained := congrArg oldQm31ToMaintained expectedExact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_add] at maintained
  exact ⟨expectedCanonical, maintained⟩

theorem sub_run_corresponds
    (left right out : RawQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.sub left right =
      ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left - toMaintainedExact right := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_sub_corresponds left right hleft hright
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  have maintained := congrArg oldQm31ToMaintained expectedExact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_sub] at maintained
  exact ⟨expectedCanonical, maintained⟩

theorem mul_run_corresponds
    (left right out : RawQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.mul left right =
      ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact left * toMaintainedExact right := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_mul_corresponds left right hleft hright
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  have maintained := congrArg oldQm31ToMaintained expectedExact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_mul] at maintained
  exact ⟨expectedCanonical, maintained⟩

theorem square_run_corresponds
    (value out : RawQM31) (hvalue : CanonicalQM31 value)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.square value =
      ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out = toMaintainedExact value ^ 2 := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_square_corresponds value hvalue
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  have maintained := congrArg oldQm31ToMaintained expectedExact
  simp only [pow_two, oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_mul] at maintained
  exact ⟨expectedCanonical, by simpa [pow_two] using maintained⟩

theorem half_run_corresponds
    (value out : RawQM31) (hvalue : CanonicalQM31 value)
    (run : V5RelationLinkedGenerated.aspis_core.field.QM31.half value =
      ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out + toMaintainedExact out =
        toMaintainedExact value := by
  obtain ⟨expected, expectedRun, expectedCanonical, expectedExact⟩ :=
    generated_qm31_half_corresponds value hvalue
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  have maintained := congrArg oldQm31ToMaintained expectedExact
  simp only [oldQm31ToMaintained_toExact,
    oldQm31ToMaintained_add] at maintained
  exact ⟨expectedCanonical, maintained⟩

/-- Four successful source `half` calls divide by sixteen in the maintained
field.  The multiplicative form avoids any hidden nonzero premise. -/
theorem four_halves_correspond
    (raw half0 half1 half2 value : RawQM31)
    (hraw : CanonicalQM31 raw)
    (run0 : V5RelationLinkedGenerated.aspis_core.field.QM31.half raw = ok half0)
    (run1 : V5RelationLinkedGenerated.aspis_core.field.QM31.half half0 = ok half1)
    (run2 : V5RelationLinkedGenerated.aspis_core.field.QM31.half half1 = ok half2)
    (run3 : V5RelationLinkedGenerated.aspis_core.field.QM31.half half2 = ok value) :
    CanonicalQM31 value ∧
      (16 : ExactQM31) * toMaintainedExact value = toMaintainedExact raw := by
  obtain ⟨hhalf0, exact0⟩ := half_run_corresponds raw half0 hraw run0
  obtain ⟨hhalf1, exact1⟩ := half_run_corresponds half0 half1 hhalf0 run1
  obtain ⟨hhalf2, exact2⟩ := half_run_corresponds half1 half2 hhalf1 run2
  obtain ⟨hvalue, exact3⟩ := half_run_corresponds half2 value hhalf2 run3
  refine ⟨hvalue, ?_⟩
  calc
    (16 : ExactQM31) * toMaintainedExact value =
        8 * (toMaintainedExact value + toMaintainedExact value) := by ring
    _ = 8 * toMaintainedExact half2 := by rw [exact3]
    _ = 4 * (toMaintainedExact half2 + toMaintainedExact half2) := by ring
    _ = 4 * toMaintainedExact half1 := by rw [exact2]
    _ = 2 * (toMaintainedExact half1 + toMaintainedExact half1) := by ring
    _ = 2 * toMaintainedExact half0 := by rw [exact1]
    _ = toMaintainedExact half0 + toMaintainedExact half0 := by ring
    _ = toMaintainedExact raw := exact0

/-- Every arithmetic value cached by the released low-mask helper is the
expected maintained-field power or sum. -/
theorem released_binary_power_trace_corresponds
    (alpha0 alpha1 : RawQM31)
    (halpha0 : CanonicalQM31 alpha0) (halpha1 : CanonicalQM31 alpha1)
    (trace : ReleasedBinaryPowerTrace alpha0 alpha1) :
    CanonicalQM31 trace.alpha0Squared ∧
    CanonicalQM31 trace.alpha1Squared ∧
    CanonicalQM31 trace.alpha0Cubed ∧
    CanonicalQM31 trace.alpha1Cubed ∧
    CanonicalQM31 trace.cross ∧
    CanonicalQM31 trace.alpha0Total3 ∧
    CanonicalQM31 trace.alpha1Total3 ∧
    CanonicalQM31 trace.total ∧
    toMaintainedExact trace.alpha0Squared = toMaintainedExact alpha0 ^ 2 ∧
    toMaintainedExact trace.alpha1Squared = toMaintainedExact alpha1 ^ 2 ∧
    toMaintainedExact trace.alpha0Cubed = toMaintainedExact alpha0 ^ 3 ∧
    toMaintainedExact trace.alpha1Cubed = toMaintainedExact alpha1 ^ 3 ∧
    toMaintainedExact trace.cross =
      toMaintainedExact alpha1 ^ 2 * toMaintainedExact alpha0 ∧
    toMaintainedExact trace.alpha0Total3 =
      1 + toMaintainedExact alpha0 ^ 3 + toMaintainedExact alpha0 ^ 2 +
        toMaintainedExact alpha0 ∧
    toMaintainedExact trace.alpha1Total3 =
      1 + toMaintainedExact alpha1 ^ 3 + toMaintainedExact alpha1 ^ 2 +
        toMaintainedExact alpha1 ∧
    toMaintainedExact trace.total =
      (1 + toMaintainedExact alpha0 ^ 3 + toMaintainedExact alpha0 ^ 2 +
        toMaintainedExact alpha0) *
      (1 + toMaintainedExact alpha1 ^ 3 + toMaintainedExact alpha1 ^ 2 +
        toMaintainedExact alpha1) := by
  obtain ⟨hsq0, esq0⟩ :=
    square_run_corresponds alpha0 trace.alpha0Squared halpha0 trace.square0Run
  obtain ⟨hsq1, esq1⟩ :=
    square_run_corresponds alpha1 trace.alpha1Squared halpha1 trace.square1Run
  obtain ⟨hcube0, ecube0raw⟩ :=
    mul_run_corresponds trace.alpha0Squared alpha0 trace.alpha0Cubed
      hsq0 halpha0 trace.cube0Run
  obtain ⟨hcube1, ecube1raw⟩ :=
    mul_run_corresponds trace.alpha1Squared alpha1 trace.alpha1Cubed
      hsq1 halpha1 trace.cube1Run
  obtain ⟨hcross, ecrossRaw⟩ :=
    mul_run_corresponds trace.alpha1Squared alpha0 trace.cross
      hsq1 halpha0 trace.crossRun
  obtain ⟨ha00, ea00⟩ := add_run_corresponds _ _ trace.alpha0Total0
    zeroCanonical oneCanonical trace.add00Run
  obtain ⟨ha10, ea10⟩ := add_run_corresponds _ _ trace.alpha1Total0
    zeroCanonical oneCanonical trace.add10Run
  obtain ⟨ha01, ea01⟩ := add_run_corresponds _ _ trace.alpha0Total1
    ha00 hcube0 trace.add01Run
  obtain ⟨ha11, ea11⟩ := add_run_corresponds _ _ trace.alpha1Total1
    ha10 hcube1 trace.add11Run
  obtain ⟨ha02, ea02⟩ := add_run_corresponds _ _ trace.alpha0Total2
    ha01 hsq0 trace.add02Run
  obtain ⟨ha12, ea12⟩ := add_run_corresponds _ _ trace.alpha1Total2
    ha11 hsq1 trace.add12Run
  obtain ⟨ha03, ea03⟩ := add_run_corresponds _ _ trace.alpha0Total3
    ha02 halpha0 trace.add03Run
  obtain ⟨ha13, ea13⟩ := add_run_corresponds _ _ trace.alpha1Total3
    ha12 halpha1 trace.add13Run
  obtain ⟨htotal, etotalRaw⟩ := mul_run_corresponds
    trace.alpha0Total3 trace.alpha1Total3 trace.total ha03 ha13 trace.totalRun
  have ecube0 : toMaintainedExact trace.alpha0Cubed =
      toMaintainedExact alpha0 ^ 3 := by rw [ecube0raw, esq0]; ring
  have ecube1 : toMaintainedExact trace.alpha1Cubed =
      toMaintainedExact alpha1 ^ 3 := by rw [ecube1raw, esq1]; ring
  have ecross : toMaintainedExact trace.cross =
      toMaintainedExact alpha1 ^ 2 * toMaintainedExact alpha0 := by
    rw [ecrossRaw, esq1]
  have etotal0 : toMaintainedExact trace.alpha0Total3 =
      1 + toMaintainedExact alpha0 ^ 3 + toMaintainedExact alpha0 ^ 2 +
        toMaintainedExact alpha0 := by
    rw [ea03, ea02, ea01, ea00, zero_toMaintained, one_toMaintained,
      ecube0, esq0]
    ring
  have etotal1 : toMaintainedExact trace.alpha1Total3 =
      1 + toMaintainedExact alpha1 ^ 3 + toMaintainedExact alpha1 ^ 2 +
        toMaintainedExact alpha1 := by
    rw [ea13, ea12, ea11, ea10, zero_toMaintained, one_toMaintained,
      ecube1, esq1]
    ring
  refine ⟨hsq0, hsq1, hcube0, hcube1, hcross, ha03, ha13, htotal,
    esq0, esq1, ecube0, ecube1, ecross, etotal0, etotal1, ?_⟩
  rw [etotalRaw, etotal0, etotal1]

/-- A dense fixed-mask trace computes `(total - selectedBasisSum) / 16`. -/
theorem dense_mask_trace_corresponds
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (total : RawQM31) (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : DenseMaskValueTrace selected basis total values valuesOut)
    (htotal : CanonicalQM31 total)
    (hpartial : CanonicalQM31 trace.partialSum) :
    CanonicalQM31 trace.value ∧
      (16 : ExactQM31) * toMaintainedExact trace.value =
        toMaintainedExact total - toMaintainedExact trace.partialSum := by
  obtain ⟨hraw, eraw⟩ := sub_run_corresponds total trace.partialSum
    trace.raw htotal hpartial trace.subRun
  obtain ⟨hvalue, evalue⟩ := four_halves_correspond trace.raw trace.half0
    trace.half1 trace.half2 trace.value hraw trace.half0Run trace.half1Run
    trace.half2Run trace.half3Run
  exact ⟨hvalue, by rw [evalue, eraw]⟩

/-- A sparse fixed-mask trace computes `selectedBasisSum / 16`. -/
theorem sparse_mask_trace_corresponds
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (values valuesOut : alloc.vec.Vec RawQM31)
    (trace : SparseMaskValueTrace selected basis values valuesOut)
    (hpartial : CanonicalQM31 trace.partialSum) :
    CanonicalQM31 trace.value ∧
      (16 : ExactQM31) * toMaintainedExact trace.value =
        toMaintainedExact trace.partialSum := by
  exact four_halves_correspond trace.partialSum trace.half0 trace.half1
    trace.half2 trace.value hpartial trace.half0Run trace.half1Run
    trace.half2Run trace.half3Run

private theorem fixed_selected_run_unique
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (left right : RawQM31)
    (leftRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          selected basis = ok left)
    (rightRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          selected basis = ok right) :
    left = right := by
  rw [leftRun] at rightRun
  injection rightRun

private theorem zero_selected_body_active
    (basis : Array RawQM31 16#usize) (acc : RawQM31)
    (low next : Std.Usize)
    (active : low < 16#usize)
    (nextExact : Std.Usize.wrapping_add low 1#usize = next) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
        0#u16 basis acc low = ok (cont (acc, next)) := by
  unfold
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
  rw [if_pos active]
  simp only [Std.lift, bind_tc_ok]
  have bitAndZero :
      0#u16 &&& Std.U16.wrapping_shl 1#u16
          (V5RelationLinkedGenerated.usizeShiftCount low) = 0#u16 := by
    apply UScalar.val_eq_imp
    simp
  rw [bitAndZero]
  simp [nextExact]

private theorem zero_selected_body_done
    (basis : Array RawQM31 16#usize) (acc : RawQM31)
    (low : Std.Usize) (inactive : ¬ low < 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body
        0#u16 basis acc low = ok (done acc) := by
  simp [V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop.body,
    inactive]

theorem zero_selected_loop_exact
    (basis : Array RawQM31 16#usize) (acc : RawQM31)
    (low : Std.Usize) (hbound : low.val ≤ 16) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop
        0#u16 basis acc low = ok acc := by
  by_cases hmore : low.val < 16
  · have active : low < 16#usize := by
      rw [UScalar.lt_equiv]
      exact hmore
    let next := Std.Usize.wrapping_add low 1#usize
    have nextVal : next.val = low.val + 1 := by
      unfold next
      rw [Std.Usize.wrapping_add_val_eq]
      norm_num
      apply Nat.mod_eq_of_lt
      have hsize : 17 < Std.Usize.size := by
        have raw := (17#usize).hSize
        scalar_tac
      omega
    have bodyRun := zero_selected_body_active basis acc low next active rfl
    rw [V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop,
      Aeneas.Std.loop.eq_1]
    simp only
    rw [bodyRun]
    simp only
    exact zero_selected_loop_exact basis acc next (by omega)
  · have lowEq : low.val = 16 := by omega
    have inactive : ¬ low < 16#usize := by
      rw [UScalar.lt_equiv]
      norm_num
      exact Nat.le_of_not_gt hmore
    have bodyRun := zero_selected_body_done basis acc low inactive
    rw [V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis_loop,
      Aeneas.Std.loop.eq_1]
    simp only
    rw [bodyRun]
termination_by 16 - low.val
decreasing_by
  simp_wf
  have hmod : (low.val + 1) % Std.Usize.size = low.val + 1 := by
    simpa [next, Std.Usize.wrapping_add_val_eq] using nextVal
  rw [hmod]
  omega

theorem selected_zero_source_exact
    (basis : Array RawQM31 16#usize) :
    V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0#u16 basis =
      ok V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO := by
  unfold V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
  exact zero_selected_loop_exact basis
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO 0#usize (by decide)

theorem selected_zero_run_corresponds
    (basis : Array RawQM31 16#usize) (out : RawQM31)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
        0#u16 basis = ok out) :
    out = V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO ∧
      CanonicalQM31 out ∧ toMaintainedExact out = 0 := by
  have same := fixed_selected_run_unique 0#u16 basis out
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO run
    (selected_zero_source_exact basis)
  subst out
  exact ⟨rfl, zeroCanonical, zero_toMaintained⟩

theorem selected1800_run_corresponds
    (alpha0Cubed alpha0Squared alpha0 cross alpha1 out : RawQM31)
    (hcross : CanonicalQM31 cross) (halpha1 : CanonicalQM31 alpha1)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x1800#u16
          (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1) =
        ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        toMaintainedExact cross + toMaintainedExact alpha1 := by
  obtain ⟨sum11, run11, hsum11, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO cross
      zeroCanonical hcross
  obtain ⟨sum12, run12, hsum12, _⟩ :=
    generated_qm31_add_corresponds sum11 alpha1 hsum11 halpha1
  have sourceRun := releasedSelected1800Exact alpha0Cubed alpha0Squared
    alpha0 cross alpha1 sum11 sum12 run11 run12
  have same := fixed_selected_run_unique 0x1800#u16
    (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1)
    out sum12 run sourceRun
  subst out
  obtain ⟨_, exact11⟩ := add_run_corresponds _ _ sum11
    zeroCanonical hcross run11
  obtain ⟨_, exact12⟩ := add_run_corresponds _ _ sum12
    hsum11 halpha1 run12
  refine ⟨hsum12, ?_⟩
  rw [exact12, exact11, zero_toMaintained]
  ring

theorem selected1801_run_corresponds
    (alpha0Cubed alpha0Squared alpha0 cross alpha1 out : RawQM31)
    (hcross : CanonicalQM31 cross) (halpha1 : CanonicalQM31 alpha1)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x1801#u16
          (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1) =
        ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        1 + toMaintainedExact cross + toMaintainedExact alpha1 := by
  obtain ⟨sum0, run0, hsum0, _⟩ := generated_qm31_add_corresponds
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
    zeroCanonical oneCanonical
  obtain ⟨sum11, run11, hsum11, _⟩ :=
    generated_qm31_add_corresponds sum0 cross hsum0 hcross
  obtain ⟨sum12, run12, hsum12, _⟩ :=
    generated_qm31_add_corresponds sum11 alpha1 hsum11 halpha1
  have sourceRun := releasedSelected1801Exact alpha0Cubed alpha0Squared
    alpha0 cross alpha1 sum0 sum11 sum12 run0 run11 run12
  have same := fixed_selected_run_unique 0x1801#u16
    (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1)
    out sum12 run sourceRun
  subst out
  obtain ⟨_, exact0⟩ := add_run_corresponds _ _ sum0
    zeroCanonical oneCanonical run0
  obtain ⟨_, exact11⟩ := add_run_corresponds _ _ sum11
    hsum0 hcross run11
  obtain ⟨_, exact12⟩ := add_run_corresponds _ _ sum12
    hsum11 halpha1 run12
  refine ⟨hsum12, ?_⟩
  rw [exact12, exact11, exact0, zero_toMaintained, one_toMaintained]
  ring

theorem selected1001_run_corresponds
    (alpha0Cubed alpha0Squared alpha0 cross alpha1 out : RawQM31)
    (halpha1 : CanonicalQM31 alpha1)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x1001#u16
          (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1) =
        ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out = 1 + toMaintainedExact alpha1 := by
  obtain ⟨sum0, run0, hsum0, _⟩ := generated_qm31_add_corresponds
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
    zeroCanonical oneCanonical
  obtain ⟨sum12, run12, hsum12, _⟩ :=
    generated_qm31_add_corresponds sum0 alpha1 hsum0 halpha1
  have sourceRun := releasedSelected1001Exact alpha0Cubed alpha0Squared
    alpha0 cross alpha1 sum0 sum12 run0 run12
  have same := fixed_selected_run_unique 0x1001#u16
    (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1)
    out sum12 run sourceRun
  subst out
  obtain ⟨_, exact0⟩ := add_run_corresponds _ _ sum0
    zeroCanonical oneCanonical run0
  obtain ⟨_, exact12⟩ := add_run_corresponds _ _ sum12
    hsum0 halpha1 run12
  refine ⟨hsum12, ?_⟩
  rw [exact12, exact0, zero_toMaintained, one_toMaintained]
  ring

theorem selected000f_run_corresponds
    (alpha0Cubed alpha0Squared alpha0 cross alpha1 out : RawQM31)
    (hcube : CanonicalQM31 alpha0Cubed)
    (hsquare : CanonicalQM31 alpha0Squared)
    (halpha0 : CanonicalQM31 alpha0)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x000f#u16
          (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1) =
        ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out =
        1 + toMaintainedExact alpha0Cubed + toMaintainedExact alpha0Squared +
          toMaintainedExact alpha0 := by
  obtain ⟨sum0, run0, hsum0, _⟩ := generated_qm31_add_corresponds
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
    zeroCanonical oneCanonical
  obtain ⟨sum1, run1, hsum1, _⟩ :=
    generated_qm31_add_corresponds sum0 alpha0Cubed hsum0 hcube
  obtain ⟨sum2, run2, hsum2, _⟩ :=
    generated_qm31_add_corresponds sum1 alpha0Squared hsum1 hsquare
  obtain ⟨sum3, run3, hsum3, _⟩ :=
    generated_qm31_add_corresponds sum2 alpha0 hsum2 halpha0
  have sourceRun := releasedSelected000fExact alpha0Cubed alpha0Squared
    alpha0 cross alpha1 sum0 sum1 sum2 sum3 run0 run1 run2 run3
  have same := fixed_selected_run_unique 0x000f#u16
    (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1)
    out sum3 run sourceRun
  subst out
  obtain ⟨_, exact0⟩ := add_run_corresponds _ _ sum0
    zeroCanonical oneCanonical run0
  obtain ⟨_, exact1⟩ := add_run_corresponds _ _ sum1 hsum0 hcube run1
  obtain ⟨_, exact2⟩ := add_run_corresponds _ _ sum2 hsum1 hsquare run2
  obtain ⟨_, exact3⟩ := add_run_corresponds _ _ sum3 hsum2 halpha0 run3
  refine ⟨hsum3, ?_⟩
  rw [exact3, exact2, exact1, exact0, zero_toMaintained, one_toMaintained]
  ring

theorem selected0005_run_corresponds
    (alpha0Cubed alpha0Squared alpha0 cross alpha1 out : RawQM31)
    (hsquare : CanonicalQM31 alpha0Squared)
    (run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x0005#u16
          (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1) =
        ok out) :
    CanonicalQM31 out ∧
      toMaintainedExact out = 1 + toMaintainedExact alpha0Squared := by
  obtain ⟨sum0, run0, hsum0, _⟩ := generated_qm31_add_corresponds
    V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
    V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
    zeroCanonical oneCanonical
  obtain ⟨sum2, run2, hsum2, _⟩ :=
    generated_qm31_add_corresponds sum0 alpha0Squared hsum0 hsquare
  have sourceRun := releasedSelected0005Exact alpha0Cubed alpha0Squared
    alpha0 cross alpha1 sum0 sum2 run0 run2
  have same := fixed_selected_run_unique 0x0005#u16
    (releasedBasis alpha0Cubed alpha0Squared alpha0 cross alpha1)
    out sum2 run sourceRun
  subst out
  obtain ⟨_, exact0⟩ := add_run_corresponds _ _ sum0
    zeroCanonical oneCanonical run0
  obtain ⟨_, exact2⟩ := add_run_corresponds _ _ sum2 hsum0 hsquare run2
  refine ⟨hsum2, ?_⟩
  rw [exact2, exact0, zero_toMaintained, one_toMaintained]
  ring

def releasedLowTotal (alpha0 alpha1 : ExactQM31) : ExactQM31 :=
  (1 + alpha0 ^ 3 + alpha0 ^ 2 + alpha0) *
    (1 + alpha1 ^ 3 + alpha1 ^ 2 + alpha1)

/-- Numerators of the seven group values returned by the exact released
mask list.  The source divides each one by sixteen using four `half` calls. -/
def releasedLowNumerator (alpha0 alpha1 : ExactQM31) : Fin 7 → ExactQM31
  | 0 => releasedLowTotal alpha0 alpha1 - (alpha1 ^ 2 * alpha0 + alpha1)
  | 1 => releasedLowTotal alpha0 alpha1 - (1 + alpha1 ^ 2 * alpha0 + alpha1)
  | 2 => releasedLowTotal alpha0 alpha1 - (1 + alpha1)
  | 3 => 0
  | 4 => releasedLowTotal alpha0 alpha1 - (1 + alpha0 ^ 3 + alpha0 ^ 2 + alpha0)
  | 5 => releasedLowTotal alpha0 alpha1 - (1 + alpha0 ^ 2)
  | 6 => releasedLowTotal alpha0 alpha1

def releasedLowSevenValues
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨[value0, value1, value2, value3, value4, value5, value6], by scalar_tac⟩

structure ReleasedLowValuesSemantics
    (alpha0 alpha1 : RawQM31)
    (power : ReleasedBinaryPowerTrace alpha0 alpha1)
    (values : ReleasedMaskValuesTrace
      (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
        alpha1) power.total) : Prop where
  canonical0 : CanonicalQM31 values.trace0.value
  canonical1 : CanonicalQM31 values.trace1.value
  canonical2 : CanonicalQM31 values.trace2.value
  canonical3 : CanonicalQM31 values.trace3.value
  canonical4 : CanonicalQM31 values.trace4.value
  canonical5 : CanonicalQM31 values.trace5.value
  canonical6 : CanonicalQM31 values.trace6.value
  exact0 :
    (16 : ExactQM31) * toMaintainedExact values.trace0.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 0
  exact1 :
    (16 : ExactQM31) * toMaintainedExact values.trace1.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 1
  exact2 :
    (16 : ExactQM31) * toMaintainedExact values.trace2.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 2
  exact3 :
    (16 : ExactQM31) * toMaintainedExact values.trace3.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 3
  exact4 :
    (16 : ExactQM31) * toMaintainedExact values.trace4.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 4
  exact5 :
    (16 : ExactQM31) * toMaintainedExact values.trace5.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 5
  exact6 :
    (16 : ExactQM31) * toMaintainedExact values.trace6.value =
      releasedLowNumerator (toMaintainedExact alpha0)
        (toMaintainedExact alpha1) 6

set_option maxHeartbeats 2000000 in
/-- The seven actual source traces have precisely the seven released
two-fold numerators. -/
theorem released_low_values_trace_corresponds
    (alpha0 alpha1 : RawQM31)
    (halpha0 : CanonicalQM31 alpha0) (halpha1 : CanonicalQM31 alpha1)
    (power : ReleasedBinaryPowerTrace alpha0 alpha1)
    (values : ReleasedMaskValuesTrace
      (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
        alpha1) power.total) :
    ReleasedLowValuesSemantics alpha0 alpha1 power values := by
  rcases released_binary_power_trace_corresponds alpha0 alpha1 halpha0 halpha1
      power with
    ⟨hsq0, hsq1, hcube0, hcube1, hcross, htotal0, htotal1, htotal,
      esq0, esq1, ecube0, ecube1, ecross, etotal0, etotal1, etotal⟩
  obtain ⟨hp0, ep0⟩ := selected1800_run_corresponds
    power.alpha0Cubed power.alpha0Squared alpha0 power.cross alpha1
    values.trace0.partialSum hcross halpha1 values.trace0.sumRun
  obtain ⟨hp1, ep1⟩ := selected1801_run_corresponds
    power.alpha0Cubed power.alpha0Squared alpha0 power.cross alpha1
    values.trace1.partialSum hcross halpha1 values.trace1.sumRun
  obtain ⟨hp2, ep2⟩ := selected1001_run_corresponds
    power.alpha0Cubed power.alpha0Squared alpha0 power.cross alpha1
    values.trace2.partialSum halpha1 values.trace2.sumRun
  obtain ⟨p3eq, hp3, ep3⟩ := selected_zero_run_corresponds
    (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
      alpha1) values.trace3.partialSum values.trace3.sumRun
  obtain ⟨hp4, ep4⟩ := selected000f_run_corresponds
    power.alpha0Cubed power.alpha0Squared alpha0 power.cross alpha1
    values.trace4.partialSum hcube0 hsq0 halpha0 values.trace4.sumRun
  obtain ⟨hp5, ep5⟩ := selected0005_run_corresponds
    power.alpha0Cubed power.alpha0Squared alpha0 power.cross alpha1
    values.trace5.partialSum hsq0 values.trace5.sumRun
  obtain ⟨p6eq, hp6, ep6⟩ := selected_zero_run_corresponds
    (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0 power.cross
      alpha1) values.trace6.partialSum values.trace6.sumRun
  obtain ⟨hv0, ev0⟩ := dense_mask_trace_corresponds 0x1800#u16 _
    power.total values.values0 values.values1 values.trace0 htotal hp0
  obtain ⟨hv1, ev1⟩ := dense_mask_trace_corresponds 0x1801#u16 _
    power.total values.values1 values.values2 values.trace1 htotal hp1
  obtain ⟨hv2, ev2⟩ := dense_mask_trace_corresponds 0x1001#u16 _
    power.total values.values2 values.values3 values.trace2 htotal hp2
  obtain ⟨hv3, ev3⟩ := sparse_mask_trace_corresponds 0x0000#u16 _
    values.values3 values.values4 values.trace3 hp3
  obtain ⟨hv4, ev4⟩ := dense_mask_trace_corresponds 0x000f#u16 _
    power.total values.values4 values.values5 values.trace4 htotal hp4
  obtain ⟨hv5, ev5⟩ := dense_mask_trace_corresponds 0x0005#u16 _
    power.total values.values5 values.values6 values.trace5 htotal hp5
  obtain ⟨hv6, ev6⟩ := dense_mask_trace_corresponds 0x0000#u16 _
    power.total values.values6 values.values7 values.trace6 htotal hp6
  constructor <;> try assumption
  · simpa [releasedLowNumerator, releasedLowTotal, etotal, ep0, ecross]
      using ev0
  · simpa [releasedLowNumerator, releasedLowTotal, etotal, ep1, ecross]
      using ev1
  · simpa [releasedLowNumerator, releasedLowTotal, etotal, ep2]
      using ev2
  · simpa [releasedLowNumerator, ep3] using ev3
  · simpa [releasedLowNumerator, releasedLowTotal, etotal, ep4, ecube0,
      esq0] using ev4
  · simpa [releasedLowNumerator, releasedLowTotal, etotal, ep5, esq0]
      using ev5
  · simpa [releasedLowNumerator, releasedLowTotal, etotal, ep6] using ev6

private theorem vec_push_run_values
    (input output : alloc.vec.Vec RawQM31) (value : RawQM31)
    (hcapacity : input.val.length < Std.Usize.max)
    (run : alloc.vec.Vec.push input value = ok output) :
    output.val = input.val ++ [value] := by
  obtain ⟨expected, expectedRun, expectedValues⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec input value hcapacity)
  rw [run] at expectedRun
  injection expectedRun with same
  subst expected
  exact expectedValues

/-- The source trace's returned vector contains exactly its seven computed
values in release-mask order. -/
theorem released_low_values_vector_exact
    (basis : Array RawQM31 16#usize) (total : RawQM31)
    (values : ReleasedMaskValuesTrace basis total) :
    values.values7 = releasedLowSevenValues
      values.trace0.value values.trace1.value values.trace2.value
      values.trace3.value values.trace4.value values.trace5.value
      values.trace6.value := by
  have empty0 : values.values0.val = [] := by
    rw [values.initial]
    rfl
  have shape1 := vec_push_run_values values.values0 values.values1
    values.trace0.value (by
      rw [empty0]
      have h := (1#usize).hSize
      scalar_tac)
    values.trace0.pushRun
  have shape2 := vec_push_run_values values.values1 values.values2
    values.trace1.value (by
      rw [shape1, empty0]
      have h := (2#usize).hSize
      scalar_tac)
    values.trace1.pushRun
  have shape3 := vec_push_run_values values.values2 values.values3
    values.trace2.value (by
      rw [shape2, shape1, empty0]
      have h := (3#usize).hSize
      scalar_tac)
    values.trace2.pushRun
  have shape4 := vec_push_run_values values.values3 values.values4
    values.trace3.value
    (by
      rw [shape3, shape2, shape1, empty0]
      have h := (4#usize).hSize
      scalar_tac)
    values.trace3.pushRun
  have shape5 := vec_push_run_values values.values4 values.values5
    values.trace4.value
    (by
      rw [shape4, shape3, shape2, shape1, empty0]
      have h := (5#usize).hSize
      scalar_tac)
    values.trace4.pushRun
  have shape6 := vec_push_run_values values.values5 values.values6
    values.trace5.value
    (by
      rw [shape5, shape4, shape3, shape2, shape1, empty0]
      have h := (6#usize).hSize
      scalar_tac)
    values.trace5.pushRun
  have shape7 := vec_push_run_values values.values6 values.values7
    values.trace6.value
    (by
      rw [shape6, shape5, shape4, shape3, shape2, shape1, empty0]
      have h := (7#usize).hSize
      scalar_tac)
    values.trace6.pushRun
  apply Subtype.ext
  rw [shape7, shape6, shape5, shape4, shape3, shape2, shape1, empty0]
  rfl

#print axioms released_binary_power_trace_corresponds
#print axioms dense_mask_trace_corresponds
#print axioms sparse_mask_trace_corresponds
#print axioms selected1800_run_corresponds
#print axioms selected1801_run_corresponds
#print axioms selected1001_run_corresponds
#print axioms selected000f_run_corresponds
#print axioms selected0005_run_corresponds
#print axioms selected_zero_source_exact
#print axioms selected_zero_run_corresponds
#print axioms released_low_values_trace_corresponds
#print axioms released_low_values_vector_exact

end AspisV5RelationLinkedGroupedLowSemantics
