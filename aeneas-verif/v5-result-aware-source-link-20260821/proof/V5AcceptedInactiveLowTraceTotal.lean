import V5AcceptedInactiveInitialSemantics

/-!
# Total source trace for the released deferred low-mask helper

The existing low-mask proof gives exact semantics to every released source
trace.  This file proves the complementary totality fact: canonical challenge
inputs actually have such a trace, and therefore any successful call to the
deterministic extracted helper returns that traced seven-value vector.
-/

namespace AspisV5AcceptedInactiveLowTraceTotal

open Aeneas Aeneas.Std Result
open AspisV5RelationLinkedFieldProjection
open AspisV5RelationLinkedGroupedFold
open AspisV5RelationLinkedGroupedLowSemantics
open AspisV5AcceptedInactiveInitialSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationLinkedGenerated.aspis_core.field.QM31

local instance : Inhabited RawQM31 :=
  ⟨V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO⟩

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

private theorem releasedValuesCapacityRoom (n : Nat) (hn : n ≤ 7) :
    (alloc.vec.Vec.with_capacity RawQM31
        (Slice.len (alloc.vec.Vec.deref releasedMasks))).val.length + n <
      Std.Usize.max := by
  have hmax : 7 < Std.Usize.max := by
    rw [Std.Usize.max, Std.Usize.numBits, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with bits | bits <;>
      rw [bits] <;> norm_num
  change 0 + n < Std.Usize.max
  omega

/-- A dense-mask source step exists for canonical total and selected sum. -/
private theorem denseTraceExists
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (total partialSum : RawQM31) (values : alloc.vec.Vec RawQM31)
    (htotal : CanonicalQM31 total) (hpartial : CanonicalQM31 partialSum)
    (sumRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          selected basis = ok partialSum)
    (capacity : values.val.length < Std.Usize.max) :
    ∃ (valuesOut : alloc.vec.Vec RawQM31)
        (trace : DenseMaskValueTrace selected basis total values valuesOut),
      valuesOut.val = values.val ++ [trace.value] := by
  obtain ⟨raw, subRun, hraw, _⟩ :=
    generated_qm31_sub_corresponds total partialSum htotal hpartial
  obtain ⟨half0, half0Run, hhalf0, _⟩ :=
    generated_qm31_half_corresponds raw hraw
  obtain ⟨half1, half1Run, hhalf1, _⟩ :=
    generated_qm31_half_corresponds half0 hhalf0
  obtain ⟨half2, half2Run, hhalf2, _⟩ :=
    generated_qm31_half_corresponds half1 hhalf1
  obtain ⟨value, half3Run, _hvalue, _⟩ :=
    generated_qm31_half_corresponds half2 hhalf2
  obtain ⟨valuesOut, pushRun, valuesExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec values value capacity)
  let trace : DenseMaskValueTrace selected basis total values valuesOut := {
    partialSum := partialSum
    raw := raw
    half0 := half0
    half1 := half1
    half2 := half2
    value := value
    sumRun := sumRun
    subRun := subRun
    half0Run := half0Run
    half1Run := half1Run
    half2Run := half2Run
    half3Run := half3Run
    pushRun := pushRun }
  exact ⟨valuesOut, trace, valuesExact⟩

/-- A sparse-mask source step exists for a canonical selected sum. -/
private theorem sparseTraceExists
    (selected : Std.U16) (basis : Array RawQM31 16#usize)
    (partialSum : RawQM31) (values : alloc.vec.Vec RawQM31)
    (hpartial : CanonicalQM31 partialSum)
    (sumRun :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          selected basis = ok partialSum)
    (capacity : values.val.length < Std.Usize.max) :
    ∃ (valuesOut : alloc.vec.Vec RawQM31)
        (trace : SparseMaskValueTrace selected basis values valuesOut),
      valuesOut.val = values.val ++ [trace.value] := by
  obtain ⟨half0, half0Run, hhalf0, _⟩ :=
    generated_qm31_half_corresponds partialSum hpartial
  obtain ⟨half1, half1Run, hhalf1, _⟩ :=
    generated_qm31_half_corresponds half0 hhalf0
  obtain ⟨half2, half2Run, hhalf2, _⟩ :=
    generated_qm31_half_corresponds half1 hhalf1
  obtain ⟨value, half3Run, _hvalue, _⟩ :=
    generated_qm31_half_corresponds half2 hhalf2
  obtain ⟨valuesOut, pushRun, valuesExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec values value capacity)
  let trace : SparseMaskValueTrace selected basis values valuesOut := {
    partialSum := partialSum
    half0 := half0
    half1 := half1
    half2 := half2
    value := value
    sumRun := sumRun
    half0Run := half0Run
    half1Run := half1Run
    half2Run := half2Run
    half3Run := half3Run
    pushRun := pushRun }
  exact ⟨valuesOut, trace, valuesExact⟩

/-- All arithmetic cached before the released seven-mask loop exists for
canonical challenges. -/
theorem releasedBinaryPowerTrace_exists
    (alpha0 alpha1 : RawQM31)
    (halpha0 : CanonicalQM31 alpha0) (halpha1 : CanonicalQM31 alpha1) :
    ∃ trace : ReleasedBinaryPowerTrace alpha0 alpha1, True := by
  obtain ⟨alpha0Squared, square0Run, hsq0, _⟩ :=
    generated_qm31_square_corresponds alpha0 halpha0
  obtain ⟨alpha1Squared, square1Run, hsq1, _⟩ :=
    generated_qm31_square_corresponds alpha1 halpha1
  obtain ⟨alpha0Cubed, cube0Run, hcube0, _⟩ :=
    generated_qm31_mul_corresponds alpha0Squared alpha0 hsq0 halpha0
  obtain ⟨alpha1Cubed, cube1Run, hcube1, _⟩ :=
    generated_qm31_mul_corresponds alpha1Squared alpha1 hsq1 halpha1
  obtain ⟨cross, crossRun, _hcross, _⟩ :=
    generated_qm31_mul_corresponds alpha1Squared alpha0 hsq1 halpha0
  obtain ⟨alpha0Total0, add00Run, ha00, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
      zeroCanonical oneCanonical
  obtain ⟨alpha1Total0, add10Run, ha10, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
      zeroCanonical oneCanonical
  obtain ⟨alpha0Total1, add01Run, ha01, _⟩ :=
    generated_qm31_add_corresponds alpha0Total0 alpha0Cubed ha00 hcube0
  obtain ⟨alpha1Total1, add11Run, ha11, _⟩ :=
    generated_qm31_add_corresponds alpha1Total0 alpha1Cubed ha10 hcube1
  obtain ⟨alpha0Total2, add02Run, ha02, _⟩ :=
    generated_qm31_add_corresponds alpha0Total1 alpha0Squared ha01 hsq0
  obtain ⟨alpha1Total2, add12Run, ha12, _⟩ :=
    generated_qm31_add_corresponds alpha1Total1 alpha1Squared ha11 hsq1
  obtain ⟨alpha0Total3, add03Run, ha03, _⟩ :=
    generated_qm31_add_corresponds alpha0Total2 alpha0 ha02 halpha0
  obtain ⟨alpha1Total3, add13Run, ha13, _⟩ :=
    generated_qm31_add_corresponds alpha1Total2 alpha1 ha12 halpha1
  obtain ⟨total, totalRun, _htotal, _⟩ :=
    generated_qm31_mul_corresponds alpha0Total3 alpha1Total3 ha03 ha13
  exact ⟨{
    alpha0Squared := alpha0Squared
    alpha1Squared := alpha1Squared
    alpha0Cubed := alpha0Cubed
    alpha1Cubed := alpha1Cubed
    cross := cross
    square0Run := square0Run
    square1Run := square1Run
    cube0Run := cube0Run
    cube1Run := cube1Run
    crossRun := crossRun
    alpha0Total0 := alpha0Total0
    alpha0Total1 := alpha0Total1
    alpha0Total2 := alpha0Total2
    alpha0Total3 := alpha0Total3
    alpha1Total0 := alpha1Total0
    alpha1Total1 := alpha1Total1
    alpha1Total2 := alpha1Total2
    alpha1Total3 := alpha1Total3
    add00Run := add00Run
    add10Run := add10Run
    add01Run := add01Run
    add11Run := add11Run
    add02Run := add02Run
    add12Run := add12Run
    add03Run := add03Run
    add13Run := add13Run
    total := total
    totalRun := totalRun }, trivial⟩

/-- The complete released low-mask helper has a source trace for every pair
of canonical challenges.  The returned vector is also identified with the
seven trace values in exact release-mask order. -/
theorem releasedLowSourceTrace_exists
    (alpha0 alpha1 : RawQM31)
    (halpha0 : CanonicalQM31 alpha0) (halpha1 : CanonicalQM31 alpha1) :
    ∃ (power : ReleasedBinaryPowerTrace alpha0 alpha1)
        (values : ReleasedMaskValuesTrace
          (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0
            power.cross alpha1) power.total),
      ReleasedLowValuesSemantics alpha0 alpha1 power values ∧
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks
          (alloc.vec.Vec.deref releasedMasks) alpha0 alpha1 =
        ok values.values7 ∧
      values.values7 = releasedLowSevenValues
        values.trace0.value values.trace1.value values.trace2.value
        values.trace3.value values.trace4.value values.trace5.value
        values.trace6.value := by
  obtain ⟨power, _⟩ :=
    releasedBinaryPowerTrace_exists alpha0 alpha1 halpha0 halpha1
  obtain ⟨hsq0, hsq1, hcube0, _hcube1, hcross, _ha03, _ha13, htotal,
      _esq0, _esq1, _ecube0, _ecube1, _ecross, _etotal0, _etotal1,
      _etotal⟩ :=
    released_binary_power_trace_corresponds alpha0 alpha1 halpha0 halpha1
      power
  let basis := releasedBasis power.alpha0Cubed power.alpha0Squared alpha0
    power.cross alpha1

  obtain ⟨partial00, partial00Run, hpartial00, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO power.cross
      zeroCanonical hcross
  obtain ⟨partial0, partial0AddRun, hpartial0, _⟩ :=
    generated_qm31_add_corresponds partial00 alpha1 hpartial00 halpha1
  have partial0Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x1800#u16 basis = ok partial0 := by
    simpa [basis] using releasedSelected1800Exact power.alpha0Cubed
      power.alpha0Squared alpha0 power.cross alpha1 partial00 partial0
      partial00Run partial0AddRun

  obtain ⟨partial10, partial10Run, hpartial10, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
      zeroCanonical oneCanonical
  obtain ⟨partial11, partial11Run, hpartial11, _⟩ :=
    generated_qm31_add_corresponds partial10 power.cross hpartial10 hcross
  obtain ⟨partial1, partial1AddRun, hpartial1, _⟩ :=
    generated_qm31_add_corresponds partial11 alpha1 hpartial11 halpha1
  have partial1Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x1801#u16 basis = ok partial1 := by
    simpa [basis] using releasedSelected1801Exact power.alpha0Cubed
      power.alpha0Squared alpha0 power.cross alpha1 partial10 partial11
      partial1 partial10Run partial11Run partial1AddRun

  obtain ⟨partial20, partial20Run, hpartial20, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
      zeroCanonical oneCanonical
  obtain ⟨partial2, partial2AddRun, hpartial2, _⟩ :=
    generated_qm31_add_corresponds partial20 alpha1 hpartial20 halpha1
  have partial2Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x1001#u16 basis = ok partial2 := by
    simpa [basis] using releasedSelected1001Exact power.alpha0Cubed
      power.alpha0Squared alpha0 power.cross alpha1 partial20 partial2
      partial20Run partial2AddRun

  let partial3 := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have partial3Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x0000#u16 basis = ok partial3 := by
    simpa [partial3] using selected_zero_source_exact basis
  have hpartial3 : CanonicalQM31 partial3 := by
    exact zeroCanonical

  obtain ⟨partial40, partial40Run, hpartial40, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
      zeroCanonical oneCanonical
  obtain ⟨partial41, partial41Run, hpartial41, _⟩ :=
    generated_qm31_add_corresponds partial40 power.alpha0Cubed
      hpartial40 hcube0
  obtain ⟨partial42, partial42Run, hpartial42, _⟩ :=
    generated_qm31_add_corresponds partial41 power.alpha0Squared
      hpartial41 hsq0
  obtain ⟨partial4, partial4AddRun, hpartial4, _⟩ :=
    generated_qm31_add_corresponds partial42 alpha0 hpartial42 halpha0
  have partial4Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x000f#u16 basis = ok partial4 := by
    simpa [basis] using releasedSelected000fExact power.alpha0Cubed
      power.alpha0Squared alpha0 power.cross alpha1 partial40 partial41
      partial42 partial4 partial40Run partial41Run partial42Run
      partial4AddRun

  obtain ⟨partial50, partial50Run, hpartial50, _⟩ :=
    generated_qm31_add_corresponds
      V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
      V5RelationLinkedGenerated.aspis_core.field.QM31.ONE
      zeroCanonical oneCanonical
  obtain ⟨partial5, partial5AddRun, hpartial5, _⟩ :=
    generated_qm31_add_corresponds partial50 power.alpha0Squared
      hpartial50 hsq0
  have partial5Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x0005#u16 basis = ok partial5 := by
    simpa [basis] using releasedSelected0005Exact power.alpha0Cubed
      power.alpha0Squared alpha0 power.cross alpha1 partial50 partial5
      partial50Run partial5AddRun

  let partial6 := V5RelationLinkedGenerated.aspis_core.field.QM31.ZERO
  have partial6Run :
      V5RelationLinkedGenerated.aspis_core.sumcheck.sum_selected_binary_basis
          0x0000#u16 basis = ok partial6 := by
    simpa [partial6] using selected_zero_source_exact basis
  have hpartial6 : CanonicalQM31 partial6 := by
    exact zeroCanonical

  let values0 := alloc.vec.Vec.with_capacity RawQM31
    (Slice.len (alloc.vec.Vec.deref releasedMasks))
  have room0 : values0.val.length < Std.Usize.max := by
    simpa [values0] using releasedValuesCapacityRoom 0 (by omega)
  obtain ⟨values1, trace0, shape1⟩ := denseTraceExists 0x1800#u16
    basis power.total partial0 values0 htotal hpartial0 partial0Run room0
  have room1 : values1.val.length < Std.Usize.max := by
    rw [shape1]
    simpa [values0] using releasedValuesCapacityRoom 1 (by omega)
  obtain ⟨values2, trace1, shape2⟩ := denseTraceExists 0x1801#u16
    basis power.total partial1 values1 htotal hpartial1 partial1Run room1
  have room2 : values2.val.length < Std.Usize.max := by
    rw [shape2, shape1]
    simpa [values0, Nat.add_assoc] using
      releasedValuesCapacityRoom 2 (by omega)
  obtain ⟨values3, trace2, shape3⟩ := denseTraceExists 0x1001#u16
    basis power.total partial2 values2 htotal hpartial2 partial2Run room2
  have room3 : values3.val.length < Std.Usize.max := by
    rw [shape3, shape2, shape1]
    simpa [values0, Nat.add_assoc] using
      releasedValuesCapacityRoom 3 (by omega)
  obtain ⟨values4, trace3, shape4⟩ := sparseTraceExists 0x0000#u16
    basis partial3 values3 hpartial3 partial3Run room3
  have room4 : values4.val.length < Std.Usize.max := by
    rw [shape4, shape3, shape2, shape1]
    simpa [values0, Nat.add_assoc] using
      releasedValuesCapacityRoom 4 (by omega)
  obtain ⟨values5, trace4, shape5⟩ := denseTraceExists 0x000f#u16
    basis power.total partial4 values4 htotal hpartial4 partial4Run room4
  have room5 : values5.val.length < Std.Usize.max := by
    rw [shape5, shape4, shape3, shape2, shape1]
    simpa [values0, Nat.add_assoc] using
      releasedValuesCapacityRoom 5 (by omega)
  obtain ⟨values6, trace5, shape6⟩ := denseTraceExists 0x0005#u16
    basis power.total partial5 values5 htotal hpartial5 partial5Run room5
  have room6 : values6.val.length < Std.Usize.max := by
    rw [shape6, shape5, shape4, shape3, shape2, shape1]
    simpa [values0, Nat.add_assoc] using
      releasedValuesCapacityRoom 6 (by omega)
  obtain ⟨values7, trace6, _shape7⟩ := denseTraceExists 0x0000#u16
    basis power.total partial6 values6 htotal hpartial6 partial6Run room6

  let values : ReleasedMaskValuesTrace basis power.total := {
    values0 := values0
    values1 := values1
    values2 := values2
    values3 := values3
    values4 := values4
    values5 := values5
    values6 := values6
    values7 := values7
    initial := by rfl
    trace0 := trace0
    trace1 := trace1
    trace2 := trace2
    trace3 := trace3
    trace4 := trace4
    trace5 := trace5
    trace6 := trace6 }
  have semantics : ReleasedLowValuesSemantics alpha0 alpha1 power values :=
    released_low_values_trace_corresponds alpha0 alpha1 halpha0 halpha1
      power values
  refine ⟨power, values, semantics, ?_, ?_⟩
  · simpa [basis, values] using releasedFoldBinaryLowMasksSourceExact
      alpha0 alpha1 power values
  · exact released_low_values_vector_exact _ _ values

/-- Determinism turns any successful extracted call into the exact traced
seven-value output and its maintained two-fold semantics. -/
theorem releasedLowSourceSuccess_exposes_semantics
    (alpha0 alpha1 : RawQM31)
    (halpha0 : CanonicalQM31 alpha0) (halpha1 : CanonicalQM31 alpha1)
    (out : alloc.vec.Vec RawQM31)
    (success :
      V5RelationLinkedGenerated.aspis_core.sumcheck.fold_binary_low_masks
          (alloc.vec.Vec.deref releasedMasks) alpha0 alpha1 = ok out) :
    ∃ (power : ReleasedBinaryPowerTrace alpha0 alpha1)
        (values : ReleasedMaskValuesTrace
          (releasedBasis power.alpha0Cubed power.alpha0Squared alpha0
            power.cross alpha1) power.total),
      out = releasedLowSevenValues
        values.trace0.value values.trace1.value values.trace2.value
        values.trace3.value values.trace4.value values.trace5.value
        values.trace6.value ∧
      ReleasedLowValuesSemantics alpha0 alpha1 power values := by
  obtain ⟨power, values, semantics, sourceRun, vectorExact⟩ :=
    releasedLowSourceTrace_exists alpha0 alpha1 halpha0 halpha1
  rw [success] at sourceRun
  injection sourceRun with same
  subst out
  exact ⟨power, values, vectorExact, semantics⟩

#print axioms releasedBinaryPowerTrace_exists
#print axioms releasedLowSourceTrace_exists
#print axioms releasedLowSourceSuccess_exposes_semantics

end AspisV5AcceptedInactiveLowTraceTotal
