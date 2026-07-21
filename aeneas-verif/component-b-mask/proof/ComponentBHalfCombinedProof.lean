import ComponentBEvaluatorFieldBridge

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBHalfCombinedProof

private theorem u32ShiftOneVal (x : Std.U32) :
    (Std.U32.wrapping_shr x 1#u32).val = x.val / 2 := by
  change (x.bv.ushiftRight (1 % 32)).toNat = x.bv.toNat / 2
  norm_num [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem u64ShiftOneVal (x : Std.U64) :
    (Std.U64.wrapping_shr x 1#u32).val = x.val / 2 := by
  change (x.bv.ushiftRight (1 % 64)).toNat = x.bv.toNat / 2
  norm_num [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private def oddHalfRaw (x : Std.U32) : Std.U32 :=
  UScalar.cast .U32
    (Std.U64.wrapping_shr
      (Std.U64.wrapping_add (UScalar.cast .U64 x)
        (UScalar.cast .U64 ComponentBGenerated.aspis_core.field.P)) 1#u32)

private theorem oddHalfRawVal (x : Std.U32) (hx : x.val < 2147483647) :
    (oddHalfRaw x).val = (x.val + 2147483647) / 2 := by
  let xu : Std.U64 := UScalar.cast .U64 x
  let pu : Std.U64 := UScalar.cast .U64 ComponentBGenerated.aspis_core.field.P
  let sum : Std.U64 := Std.U64.wrapping_add xu pu
  let half64 : Std.U64 := Std.U64.wrapping_shr sum 1#u32
  have hxu : xu.val = x.val := by
    exact U32.cast_U64_val_eq x
  have hpu : pu.val = 2147483647 := by
    unfold pu ComponentBGenerated.aspis_core.field.P
    norm_num
  have hsumBound : x.val + 2147483647 < UScalar.size .U64 := by
    have hsize : UScalar.size .U64 = 18446744073709551616 := by
      simp [U64.size, U64.numBits]
    rw [hsize]
    omega
  have hsum : sum.val = x.val + 2147483647 := by
    unfold sum
    rw [U64.wrapping_add_val_eq, Nat.mod_eq_of_lt]
    · rw [hxu, hpu]
    · simpa [hxu, hpu] using hsumBound
  have hhalf : half64.val = (x.val + 2147483647) / 2 := by
    rw [show half64.val = sum.val / 2 by exact u64ShiftOneVal sum, hsum]
  have hbound : half64.val < 2 ^ UScalarTy.U32.numBits := by
    rw [hhalf]
    norm_num
    omega
  have hcast := UScalar.cast_val_mod_pow_of_inBounds_eq .U32 half64 hbound
  unfold oddHalfRaw
  change (UScalar.cast .U32 half64).val = _
  rw [hcast, hhalf]

private theorem m31HalfEven
    (x : ComponentBGenerated.aspis_core.field.M31) (hx : x.val < 2147483647)
    (heven : x &&& 1#u32 = 0#u32) :
    ∃ half,
      ComponentBGenerated.aspis_core.field.M31.half x = ok half ∧
      half.val < 2147483647 ∧
      ComponentBGenerated.aspis_core.field.M31.add half half = ok x := by
  have hmod : x.val % 2 = 0 := by
    have hv := congrArg UScalar.val heven
    simpa only [UScalar.val_and, UScalar.ofNatCore_val_eq,
      Nat.and_one_is_mod] using hv
  let half : Std.U32 := Std.U32.wrapping_shr x 1#u32
  have hhalfVal : half.val = x.val / 2 := u32ShiftOneVal x
  have hdouble : half.val + half.val = x.val := by
    have hdecomp := Nat.mod_add_div x.val 2
    omega
  have hadd : Std.U32.wrapping_add half half = x := by
    apply UScalar.eq_of_val_eq
    rw [U32.wrapping_add_val_eq, Nat.mod_eq_of_lt]
    · exact hdouble
    · have := UScalar.hSize x
      omega
  have hnot : ¬ x >= ComponentBGenerated.aspis_core.field.P := by
    unfold ComponentBGenerated.aspis_core.field.P
    scalar_tac
  refine ⟨half, ?_, ?_, ?_⟩
  · unfold ComponentBGenerated.aspis_core.field.M31.half
    simp only [lift, bind_tc_ok]
    rw [if_pos heven]
  · rw [hhalfVal]
    omega
  · unfold ComponentBGenerated.aspis_core.field.M31.add
    rw [hadd]
    simp only [lift, bind_tc_ok]
    rw [if_neg hnot]

private theorem m31HalfOdd
    (x : ComponentBGenerated.aspis_core.field.M31) (hx : x.val < 2147483647)
    (hodd : x &&& 1#u32 ≠ 0#u32) :
    ∃ half,
      ComponentBGenerated.aspis_core.field.M31.half x = ok half ∧
      half.val < 2147483647 ∧
      ComponentBGenerated.aspis_core.field.M31.add half half = ok x := by
  have hmod : x.val % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x.val with hzero | hone
    · exfalso
      apply hodd
      apply UScalar.eq_of_val_eq
      simpa only [UScalar.val_and, UScalar.ofNatCore_val_eq,
        Nat.and_one_is_mod] using hzero
    · exact hone
  let half : Std.U32 := oddHalfRaw x
  have hhalfVal : half.val = (x.val + 2147483647) / 2 :=
    oddHalfRawVal x hx
  have hsumMod : (x.val + 2147483647) % 2 = 0 := by
    omega
  have hdouble : half.val + half.val = x.val + 2147483647 := by
    have hdecomp := Nat.mod_add_div (x.val + 2147483647) 2
    omega
  have hsumBound : x.val + 2147483647 < UScalar.size .U32 := by
    have hsize : UScalar.size .U32 = 4294967296 := by
      simp [U32.size, U32.numBits]
    rw [hsize]
    omega
  have haddVal :
      (Std.U32.wrapping_add half half).val = x.val + 2147483647 := by
    rw [U32.wrapping_add_val_eq, hdouble,
      Nat.mod_eq_of_lt hsumBound]
  have hge : Std.U32.wrapping_add half half >= ComponentBGenerated.aspis_core.field.P := by
    unfold ComponentBGenerated.aspis_core.field.P
    scalar_tac
  have hsub :
      (Std.U32.wrapping_add half half).wrapping_sub
        ComponentBGenerated.aspis_core.field.P = x := by
    apply UScalar.eq_of_val_eq
    rw [U32.wrapping_sub_val_eq, haddVal]
    have hsize : UScalar.size .U32 = 4294967296 := by
      simp [U32.size, U32.numBits]
    rw [hsize]
    unfold ComponentBGenerated.aspis_core.field.P
    norm_num
    rw [show x.val + 2147483647 + (4294967296 - 2147483647) =
        x.val + 4294967296 by omega]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨half, ?_, ?_, ?_⟩
  · unfold ComponentBGenerated.aspis_core.field.M31.half
    simp only [lift, bind_tc_ok]
    rw [if_neg hodd]
    rfl
  · rw [hhalfVal]
    omega
  · unfold ComponentBGenerated.aspis_core.field.M31.add
    simp only [lift, bind_tc_ok]
    rw [if_pos hge]
    rw [hsub]

/-- On every canonical raw M31 value, the actual extracted `half` followed by
    the actual extracted addition of the result to itself returns the input. -/
theorem generated_m31_half_doubles
    (x : ComponentBGenerated.aspis_core.field.M31) (hx : x.val < 2147483647) :
    ∃ half,
      ComponentBGenerated.aspis_core.field.M31.half x = ok half ∧
      ComponentBGenerated.aspis_core.field.M31.add half half = ok x := by
  by_cases heven : x &&& 1#u32 = 0#u32
  · obtain ⟨half, hhalf, _, hadd⟩ := m31HalfEven x hx heven
    exact ⟨half, hhalf, hadd⟩
  · obtain ⟨half, hhalf, _, hadd⟩ := m31HalfOdd x hx heven
    exact ⟨half, hhalf, hadd⟩

theorem generated_m31_half_doubles_canonical
    (x : ComponentBGenerated.aspis_core.field.M31) (hx : x.val < 2147483647) :
    ∃ half,
      ComponentBGenerated.aspis_core.field.M31.half x = ok half ∧
      half.val < 2147483647 ∧
      ComponentBGenerated.aspis_core.field.M31.add half half = ok x := by
  by_cases heven : x &&& 1#u32 = 0#u32
  · exact m31HalfEven x hx heven
  · exact m31HalfOdd x hx heven

def CanonicalQM31 (x : ComponentBGenerated.aspis_core.field.QM31) : Prop :=
  x.c0.a.val < 2147483647 ∧ x.c0.b.val < 2147483647 ∧
  x.c1.a.val < 2147483647 ∧ x.c1.b.val < 2147483647

/-- The actual extracted QM31 `half` is a right inverse of actual extracted
    doubling on every four-limb canonical QM31 value. -/
theorem generated_qm31_half_doubles
    (x : ComponentBGenerated.aspis_core.field.QM31) (hx : CanonicalQM31 x) :
    ∃ half,
      ComponentBGenerated.aspis_core.field.QM31.half x = ok half ∧
      ComponentBGenerated.aspis_core.field.QM31.add half half = ok x := by
  obtain ⟨h00, hh00, ha00⟩ := generated_m31_half_doubles x.c0.a hx.1
  obtain ⟨h01, hh01, ha01⟩ := generated_m31_half_doubles x.c0.b hx.2.1
  obtain ⟨h10, hh10, ha10⟩ := generated_m31_half_doubles x.c1.a hx.2.2.1
  obtain ⟨h11, hh11, ha11⟩ := generated_m31_half_doubles x.c1.b hx.2.2.2
  let half : ComponentBGenerated.aspis_core.field.QM31 :=
    ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
  refine ⟨half, ?_, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.half, ComponentBGenerated.aspis_core.field.CM31.half,
      hh00, hh01, hh10, hh11, half]
  · simp [ComponentBGenerated.aspis_core.field.QM31.add, ComponentBGenerated.aspis_core.field.CM31.add,
      ha00, ha01, ha10, ha11, half]

theorem generated_qm31_half_doubles_canonical
    (x : ComponentBGenerated.aspis_core.field.QM31) (hx : CanonicalQM31 x) :
    ∃ half,
      ComponentBGenerated.aspis_core.field.QM31.half x = ok half ∧
      CanonicalQM31 half ∧
      ComponentBGenerated.aspis_core.field.QM31.add half half = ok x := by
  obtain ⟨h00, hh00, hc00, ha00⟩ :=
    generated_m31_half_doubles_canonical x.c0.a hx.1
  obtain ⟨h01, hh01, hc01, ha01⟩ :=
    generated_m31_half_doubles_canonical x.c0.b hx.2.1
  obtain ⟨h10, hh10, hc10, ha10⟩ :=
    generated_m31_half_doubles_canonical x.c1.a hx.2.2.1
  obtain ⟨h11, hh11, hc11, ha11⟩ :=
    generated_m31_half_doubles_canonical x.c1.b hx.2.2.2
  let half : ComponentBGenerated.aspis_core.field.QM31 :=
    ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
  refine ⟨half, ?_, ?_, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.half, ComponentBGenerated.aspis_core.field.CM31.half,
      hh00, hh01, hh10, hh11, half]
  · exact ⟨hc00, hc01, hc10, hc11⟩
  · simp [ComponentBGenerated.aspis_core.field.QM31.add, ComponentBGenerated.aspis_core.field.CM31.add,
      ha00, ha01, ha10, ha11, half]

#print axioms generated_m31_half_doubles
#print axioms generated_qm31_half_doubles
#print axioms generated_m31_half_doubles_canonical
#print axioms generated_qm31_half_doubles_canonical

end ComponentBHalfCombinedProof
