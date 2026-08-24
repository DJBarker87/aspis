import V5CompactFoldExactUnrolledTypes

namespace AspisV5CompactFoldExactFieldBridge

open Aeneas Aeneas.Std Result
open AspisV5CompactFoldExactCallerBridge
open AspisV5CompactFoldExactUnrolledTypes

private theorem P_eq_legacy :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.P =
      V5RelationCompactFoldGenerated.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.P
    V5RelationCompactFoldGenerated.aspis_core.field.P
  rfl

private theorem reduce_u64_eq_legacy (value : Std.U64) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.reduce_u64 value =
      V5RelationCompactFoldGenerated.aspis_core.field.reduce_u64 value := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.reduce_u64
    V5RelationCompactFoldGenerated.aspis_core.field.reduce_u64
  rw [P_eq_legacy]

private theorem m31_add_eq_legacy
    (left right :
      V5RelationCompactFoldGeneratedExact.aspis_core.field.M31) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add left right =
      V5RelationCompactFoldGenerated.aspis_core.field.M31.add left right := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.add
    V5RelationCompactFoldGenerated.aspis_core.field.M31.add
  rw [P_eq_legacy]

private theorem m31_sub_eq_legacy
    (left right :
      V5RelationCompactFoldGeneratedExact.aspis_core.field.M31) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.sub left right =
      V5RelationCompactFoldGenerated.aspis_core.field.M31.sub left right := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.sub
    V5RelationCompactFoldGenerated.aspis_core.field.M31.sub
  rw [P_eq_legacy]

private theorem m31_mul_eq_legacy
    (left right :
      V5RelationCompactFoldGeneratedExact.aspis_core.field.M31) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.mul left right =
      V5RelationCompactFoldGenerated.aspis_core.field.M31.mul left right := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.mul
    V5RelationCompactFoldGenerated.aspis_core.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [reduce_u64_eq_legacy]

private theorem m31_half_eq_legacy
    (value : V5RelationCompactFoldGeneratedExact.aspis_core.field.M31) :
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.half value =
      V5RelationCompactFoldGenerated.aspis_core.field.M31.half value := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.half
    V5RelationCompactFoldGenerated.aspis_core.field.M31.half
  rw [P_eq_legacy]

@[simp] theorem zero_to_legacy :
    exactToLegacyRaw
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ZERO =
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ZERO
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.ZERO
    exactToLegacyRaw
  rfl

@[simp] theorem one_to_legacy :
    exactToLegacyRaw
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE =
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE := by
  unfold V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.ONE
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.ONE
    exactToLegacyRaw
  rfl

theorem cm31_add_to_legacy (left right : ExactCM) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add
          left right
      ok (exactToLegacyCM output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.CM31.add
        (exactToLegacyCM left) (exactToLegacyCM right) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    m31_add_eq_legacy, exactToLegacyCM]

theorem add_to_legacy (left right : ExactRaw) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.add
          left right
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.add
        (exactToLegacyRaw left) (exactToLegacyRaw right) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    m31_add_eq_legacy, exactToLegacyRaw]

theorem half_to_legacy (value : ExactRaw) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.half value
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.half
        (exactToLegacyRaw value) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.half,
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.half,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.half,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.half,
    m31_half_eq_legacy, exactToLegacyRaw]

theorem mul_to_legacy (left right : ExactRaw) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.mul
          left right
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul
        (exactToLegacyRaw left) (exactToLegacyRaw right) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.mul,
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.mul,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.mul,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.mul,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.sub,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.sub,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.double,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.double,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.mul_by_r,
    V5RelationCompactFoldGenerated.aspis_core.field.mul_by_r,
    m31_add_eq_legacy, m31_sub_eq_legacy, m31_mul_eq_legacy,
    exactToLegacyRaw]

theorem prepared_new_to_legacy (value : ExactRaw) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier.new
          value
      ok (exactToLegacyPrepared output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.new
        (exactToLegacyRaw value) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier.new,
    V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.new,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    m31_add_eq_legacy, exactToLegacyPrepared, exactToLegacyRaw]

theorem prepared_mul_to_legacy (prepared : ExactPrepared) (value : ExactRaw) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier.mul
          prepared value
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.mul
        (exactToLegacyPrepared prepared) (exactToLegacyRaw value) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier.mul,
    V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.mul,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.sub,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.sub,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.double,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.double,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.mul_by_r,
    V5RelationCompactFoldGenerated.aspis_core.field.mul_by_r,
    m31_add_eq_legacy, m31_sub_eq_legacy, m31_mul_eq_legacy,
    exactToLegacyPrepared, exactToLegacyRaw]

theorem karatsuba_sums_to_legacy
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_from_karatsuba_channel_sums
          sums
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums
        sums := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_from_karatsuba_channel_sums,
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.reduce_u64,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.reduce_u64,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.sub,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.sub,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.double,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.double,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.mul_by_r,
    V5RelationCompactFoldGenerated.aspis_core.field.mul_by_r,
    reduce_u64_eq_legacy, m31_add_eq_legacy, m31_sub_eq_legacy,
    exactToLegacyRaw]

theorem square_to_legacy (value : ExactRaw) :
    (do
      let output ←
        V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.square value
      ok (exactToLegacyRaw output)) =
      V5RelationCompactFoldGenerated.aspis_core.field.QM31.square
        (exactToLegacyRaw value) := by
  simp [V5RelationCompactFoldGeneratedExact.aspis_core.field.QM31.square,
    V5RelationCompactFoldGenerated.aspis_core.field.QM31.square,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.square,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.square,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.mul,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.mul,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.double,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.double,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.CM31.add,
    V5RelationCompactFoldGenerated.aspis_core.field.CM31.add,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.M31.double,
    V5RelationCompactFoldGenerated.aspis_core.field.M31.double,
    V5RelationCompactFoldGeneratedExact.aspis_core.field.mul_by_r,
    V5RelationCompactFoldGenerated.aspis_core.field.mul_by_r,
    m31_add_eq_legacy, m31_sub_eq_legacy, m31_mul_eq_legacy,
    exactToLegacyRaw]

#print axioms square_to_legacy
#print axioms cm31_add_to_legacy
#print axioms add_to_legacy
#print axioms half_to_legacy
#print axioms mul_to_legacy
#print axioms prepared_new_to_legacy
#print axioms prepared_mul_to_legacy
#print axioms karatsuba_sums_to_legacy

end AspisV5CompactFoldExactFieldBridge
