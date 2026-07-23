import GoodMatricesCurrent.SourceExtractedField
import AspisFormal.V5GoodGateSparseShift
import Aeneas.Tactic.Step.DspecInduction

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.SourceExtractedFixedSupport

open AspisV5GoodGateSparseShift
open GoodMatricesCurrent.SourceExtractedField

private abbrev LocalM31 := aspis_verifier.aspis_core.field.M31
private abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
private abbrev LocalVector := Array LocalM31 48#usize

def arrayEntry (values : LocalVector) (index : Fin 48) : LocalM31 :=
  values.val[index.val]'(by
    rw [values.property]
    simpa using index.isLt)

def arrayToExact (values : LocalVector) : Fin 48 → ExactM31 :=
  fun index => m31ToExact (arrayEntry values index)

def CanonicalLocalVector (values : LocalVector) : Prop :=
  ∀ index : Fin 48, CanonicalLocalM31 (arrayEntry values index)

@[simp] theorem arrayEntry_set_same (values : LocalVector) (index : Std.Usize)
    (hindex : index.val < 48) (value : LocalM31) :
    arrayEntry (values.set index value) ⟨index.val, hindex⟩ = value := by
  unfold arrayEntry
  exact List.getElem_set_self (by
    simp only [List.length_set]
    rw [values.property]
    simpa using hindex)

@[simp] theorem arrayEntry_set_other (values : LocalVector) (index : Std.Usize)
    (value : LocalM31) (output : Fin 48) (hne : index.val ≠ output.val) :
    arrayEntry (values.set index value) output = arrayEntry values output := by
  unfold arrayEntry
  exact List.getElem_set_ne hne (by
    simp only [List.length_set]
    rw [values.property]
    simpa using output.isLt)

theorem canonical_set (values : LocalVector) (index : Std.Usize)
    (hindex : index.val < 48) (value : LocalM31)
    (hvalues : CanonicalLocalVector values)
    (hvalue : CanonicalLocalM31 value) :
    CanonicalLocalVector (values.set index value) := by
  intro output
  by_cases heq : index.val = output.val
  · have hout : output = ⟨index.val, hindex⟩ := Fin.ext heq.symm
    subst output
    simpa using hvalue
  · rw [arrayEntry_set_other values index value output heq]
    exact hvalues output

@[simp] theorem usize_wrapping_add_one_val (value : Std.Usize)
    (hvalue : value.val + 1 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 1#usize).val = value.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := by simp
  rw [hone]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

@[simp] theorem usize_wrapping_add_two_val (value : Std.Usize)
    (hvalue : value.val + 2 < Std.Usize.size) :
    (Std.Usize.wrapping_add value 2#usize).val = value.val + 2 := by
  rw [Std.Usize.wrapping_add_val_eq]
  have htwo : (2#usize : Std.Usize).val = 2 := by simp
  rw [htwo]
  apply Nat.mod_eq_of_lt
  simpa using hvalue

theorem carry_u32_val (carry : Std.Usize) (hcarry : carry.val < 48) :
    (⟨carry.bv.setWidth 32⟩ : Std.U32).val = carry.val := by
  change (carry.bv.setWidth 32).toNat = carry.val
  rw [BitVec.toNat_setWidth, Std.Usize.bv_toNat]
  apply Nat.mod_eq_of_lt
  omega

theorem usize_wrapping_shl_one_val (carry : Std.U32) (hcarry : carry.val < 7) :
    (Std.Usize.wrapping_shl 1#usize carry).val = 2 ^ carry.val := by
  unfold Std.Usize.wrapping_shl UScalar.wrapping_shl
  change (1 <<< (carry.val % System.Platform.numBits)) %
      2 ^ System.Platform.numBits = 2 ^ carry.val
  have hbits : carry.val % System.Platform.numBits = carry.val := by
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      omega
  rw [hbits, Nat.one_shiftLeft]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with hplatform | hplatform <;>
    simp [hplatform]
  all_goals interval_cases carry.val <;> norm_num

theorem usize_wrapping_sub_val_of_le (left right : Std.Usize)
    (hle : right.val ≤ left.val) :
    (Std.Usize.wrapping_sub left right).val = left.val - right.val := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hleft := left.hSize
  have hright := right.hSize
  have hrearrange :
      left.val + (UScalar.size .Usize - right.val) =
        (left.val - right.val) + UScalar.size .Usize := by
    omega
  rw [hrearrange]
  simp only [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem usize_wrapping_shr_one_val (index : Std.Usize) :
    (Std.Usize.wrapping_shr index 1#u32).val = index.val / 2 := by
  change index.bv.toNat >>> (1 % System.Platform.numBits) = index.val / 2
  rw [Std.Usize.bv_toNat, Nat.shiftRight_eq_div_pow]
  rcases System.Platform.numBits_eq with hplatform | hplatform <;>
    simp [hplatform]

@[simp] theorem usize_and_one_val (index : Std.Usize) :
    (index &&& 1#usize).val = index.val % 2 := by
  change index.val &&& 1 = index.val % 2
  exact Nat.and_one_is_mod index.val

theorem local_vector_add_at_spec (values : LocalVector) (target : Std.Usize)
    (coefficient : LocalM31) (htarget : target.val < 48)
    (hvalues : CanonicalLocalVector values)
    (hcoefficient : CanonicalLocalM31 coefficient) :
    Exists fun updated =>
      (do
        let current ← Array.index_usize values target
        let sum ← aspis_verifier.aspis_core.field.M31.add current coefficient
        Array.update values target sum) = .ok updated /\
      CanonicalLocalVector updated /\
      arrayToExact updated = arrayToExact values +
        Pi.single (⟨target.val, htarget⟩ : Fin 48) (m31ToExact coefficient) := by
  classical
  have hlength : target.val < values.length := by
    change target.val < values.val.length
    rw [values.property]
    simpa using htarget
  obtain ⟨current, hcurrent, hcurrentValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec values target hlength)
  have hcurrentCanonical : CanonicalLocalM31 current := by
    rw [hcurrentValue]
    exact hvalues ⟨target.val, htarget⟩
  obtain ⟨sum, hsum, hsumCanonical, hsumExact⟩ :=
    local_m31_add_exact_spec current coefficient hcurrentCanonical hcoefficient
  obtain ⟨updated, hupdated, hupdatedValue⟩ :=
    WP.spec_imp_exists (Array.update_spec values target sum hlength)
  refine ⟨updated, ?_, ?_, ?_⟩
  · simp only [hcurrent, Aeneas.Std.bind_tc_ok, hsum, hupdated]
  · rw [hupdatedValue]
    exact canonical_set values target htarget sum hvalues hsumCanonical
  · rw [hupdatedValue]
    funext output
    by_cases heq : output = ⟨target.val, htarget⟩
    · subst output
      simp only [Pi.add_apply, Pi.single_eq_same]
      rw [arrayToExact, arrayEntry_set_same]
      rw [hsumExact, hcurrentValue]
      rfl
    · have hne : target.val ≠ output.val := by
        intro hval
        apply heq
        exact Fin.ext hval.symm
      simp only [Pi.add_apply, Pi.single_eq_of_ne heq]
      rw [arrayToExact, arrayEntry_set_other values target sum output hne]
      simp [arrayToExact]

noncomputable def carrySum (index : Fin 47) (coefficient : ExactM31)
    (limit : Nat) : Fin 48 → ExactM31 :=
  ∑ carry ∈ Finset.Ico 1 limit,
    Pi.single (carryIndex index carry) (dyadic carry * coefficient)

theorem carrySum_one (index : Fin 47) (coefficient : ExactM31) :
    carrySum index coefficient 1 = 0 := by
  simp [carrySum]

theorem carrySum_succ (index : Fin 47) (coefficient : ExactM31)
    (limit : Nat) (hlimit : 1 ≤ limit) :
    carrySum index coefficient (limit + 1) =
      carrySum index coefficient limit +
        Pi.single (carryIndex index limit) (dyadic limit * coefficient) := by
  classical
  unfold carrySum
  rw [Finset.sum_Ico_succ_top hlimit]

theorem trailingOnes_lt_six (index : Nat) (hindex : index < 47) :
    trailingOnes index < 6 := by
  have htop := pow_trailingOnes_le_succ index
  by_contra hnot
  have hsix : 6 ≤ trailingOnes index := by omega
  have hpow : 2 ^ 6 ≤ 2 ^ trailingOnes index :=
    Nat.pow_le_pow_right (by omega) hsix
  norm_num at hpow
  omega

def InnerInvariant (base : Fin 48 → ExactM31) (index : Fin 47)
    (coefficient : ExactM31) (output : LocalVector) (carry : Std.Usize)
    (scaled : LocalM31) : Prop :=
  CanonicalLocalVector output /\
  CanonicalLocalM31 scaled /\
  1 ≤ carry.val /\
  arrayToExact output = base + carrySum index coefficient carry.val /\
  m31ToExact scaled = dyadic (carry.val - 1) * coefficient

private abbrev innerLoop :=
  v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0

private abbrev innerBody :=
  v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0.body

theorem innerBody_step (base : Fin 48 → ExactM31) (coefficient : ExactM31)
    (index trailing : Std.Usize) (output : LocalVector) (carry : Std.Usize)
    (scaled : LocalM31)
    (hindex : index.val < 47)
    (htrailing : trailing.val = trailingOnes index.val)
    (hcarry : carry.val ≤ trailing.val)
    (hinvariant : InnerInvariant base ⟨index.val, hindex⟩
      coefficient output carry scaled) :
    Exists fun state : LocalVector × Std.Usize × LocalM31 =>
      innerBody index trailing output carry scaled = .ok (.cont state) /\
      state.2.1.val = carry.val + 1 /\
      InnerInvariant base ⟨index.val, hindex⟩ coefficient
        state.1 state.2.1 state.2.2 := by
  rcases hinvariant with
    ⟨houtputCanonical, hscaledCanonical, hcarryPositive, houtputExact,
      hscaledExact⟩
  unfold innerBody
  unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0.body
  simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
  have hcontinue : carry <= trailing := (UScalar.le_equiv _ _).2 hcarry
  rw [if_pos hcontinue]
  obtain ⟨scaled1, hscaled1, hscaled1Canonical, hscaled1Exact⟩ :=
    local_m31_half_exact_spec scaled hscaledCanonical
  let carryU32 : Std.U32 := ⟨carry.bv.setWidth 32⟩
  have htrailBound : trailing.val < 6 := by
    rw [htrailing]
    exact trailingOnes_lt_six index.val hindex
  have hcarryBound : carry.val < 6 := by omega
  have hcarryU32 : carryU32.val = carry.val :=
    carry_u32_val carry (by omega)
  let shifted := Std.Usize.wrapping_shl 1#usize carryU32
  have hshifted : shifted.val = 2 ^ carry.val := by
    rw [usize_wrapping_shl_one_val carryU32 (by omega), hcarryU32]
  let offset := Std.Usize.wrapping_sub shifted 1#usize
  have hoffset : offset.val = 2 ^ carry.val - 1 := by
    rw [usize_wrapping_sub_val_of_le]
    · rw [hshifted]
      have hone : (1#usize : Std.Usize).val = 1 := by simp
      rw [hone]
    · have hone : (1#usize : Std.Usize).val = 1 := by simp
      rw [hone, hshifted]
      exact Nat.one_le_two_pow
  have hpowTop : 2 ^ carry.val ≤ index.val + 1 := by
    have hpowMono : 2 ^ carry.val ≤ 2 ^ trailingOnes index.val := by
      apply Nat.pow_le_pow_right (by omega)
      rw [← htrailing]
      exact hcarry
    exact hpowMono.trans (pow_trailingOnes_le_succ index.val)
  have hoffsetLe : offset.val ≤ index.val := by rw [hoffset]; omega
  let target := Std.Usize.wrapping_sub index offset
  have htarget : target.val = index.val - (2 ^ carry.val - 1) := by
    rw [usize_wrapping_sub_val_of_le index offset hoffsetLe, hoffset]
  have htargetBound : target.val < 48 := by rw [htarget]; omega
  obtain ⟨updated, hupdated, hupdatedCanonical, hupdatedExact⟩ :=
    local_vector_add_at_spec output target scaled1 htargetBound
      houtputCanonical hscaled1Canonical
  let carry1 := Std.Usize.wrapping_add carry 1#usize
  have hcarry1 : carry1.val = carry.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 48 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hplatform | hplatform <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hplatform]
    omega
  have htargetFin : (⟨target.val, htargetBound⟩ : Fin 48) =
      carryIndex ⟨index.val, hindex⟩ carry.val := by
    apply Fin.ext
    exact htarget
  have hscaled1Coefficient :
      m31ToExact scaled1 = dyadic carry.val * coefficient := by
    rw [hscaled1Exact, hscaledExact]
    calc
      (2 : ExactM31)⁻¹ * (dyadic (carry.val - 1) * coefficient) =
          ((2 : ExactM31)⁻¹ * dyadic (carry.val - 1)) * coefficient := by
            rw [mul_assoc]
      _ = dyadic ((carry.val - 1) + 1) * coefficient := by
        rw [dyadic_succ]
      _ = dyadic carry.val * coefficient := by
        congr 2
        omega
  have hupdatedInvariant :
      InnerInvariant base ⟨index.val, hindex⟩ coefficient
        updated carry1 scaled1 := by
    refine ⟨hupdatedCanonical, hscaled1Canonical, ?_, ?_, ?_⟩
    · rw [hcarry1]
      omega
    · rw [hupdatedExact, houtputExact, htargetFin, hscaled1Coefficient,
        hcarry1, carrySum_succ _ _ carry.val hcarryPositive]
      funext outputIndex
      simp only [Pi.add_apply]
      ring
    · rw [hcarry1]
      have hexponent : carry.val + 1 - 1 = carry.val := by omega
      rw [hexponent]
      exact hscaled1Coefficient
  refine ⟨(updated, carry1, scaled1), ?_, hcarry1, hupdatedInvariant⟩
  simp only [hscaled1]
  change (do
      let current ← Array.index_usize output target
      let sum ← aspis_verifier.aspis_core.field.M31.add current scaled1
      let updated1 ← Array.update output target sum
      let carry2 ← Aeneas.Std.lift (Std.Usize.wrapping_add carry 1#usize)
      .ok (ControlFlow.cont (updated1, carry2, scaled1))) = _
  have hupdated' :
      ((do
          let current ← Array.index_usize output target
          aspis_verifier.aspis_core.field.M31.add current scaled1) >>=
        Array.update output target) = .ok updated := by
    rw [Aeneas.Std.bind_assoc_eq]
    exact hupdated
  rw [← Aeneas.Std.bind_assoc_eq, ← Aeneas.Std.bind_assoc_eq]
  rw [hupdated']
  rfl

theorem innerLoop_spec (base : Fin 48 → ExactM31) (coefficient : ExactM31)
    (index trailing : Std.Usize) (output : LocalVector) (carry : Std.Usize)
    (scaled : LocalM31) (hindex : index.val < 47)
    (htrailing : trailing.val = trailingOnes index.val)
    (hupper : carry.val ≤ trailing.val + 1)
    (hinvariant : InnerInvariant base ⟨index.val, hindex⟩ coefficient
      output carry scaled) :
    Exists fun result : LocalVector × LocalM31 =>
      innerLoop output index trailing carry scaled = .ok result /\
      CanonicalLocalVector result.1 /\
      CanonicalLocalM31 result.2 /\
      arrayToExact result.1 = base +
        carrySum ⟨index.val, hindex⟩ coefficient (trailing.val + 1) /\
      m31ToExact result.2 = dyadic trailing.val * coefficient := by
  by_cases hcontinueNat : carry.val ≤ trailing.val
  · obtain ⟨state, hbody, hcarry1, hstateInvariant⟩ :=
      innerBody_step base coefficient index trailing output carry scaled
        hindex htrailing hcontinueNat hinvariant
    unfold innerBody at hbody
    have hstateUpper : state.2.1.val ≤ trailing.val + 1 := by
      rw [hcarry1]
      omega
    obtain ⟨result, hresult, hresultCanonical, hscaledCanonical,
        hresultExact, hscaledExact⟩ :=
      innerLoop_spec base coefficient index trailing state.1 state.2.1 state.2.2
        hindex htrailing hstateUpper hstateInvariant
    unfold innerLoop at hresult
    refine ⟨result, ?_, hresultCanonical, hscaledCanonical, hresultExact,
      hscaledExact⟩
    unfold innerLoop
    unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hresult
  · have hcarryFinal : carry.val = trailing.val + 1 := by omega
    rcases hinvariant with
      ⟨houtputCanonical, hscaledCanonical, _hcarryPositive,
        houtputExact, hscaledExact⟩
    have hcontinue : ¬ carry <= trailing := by
      intro hle
      exact hcontinueNat ((UScalar.le_equiv _ _).1 hle)
    have hbodyDone :
        innerBody index trailing output carry scaled =
          .ok (.done (output, scaled)) := by
      unfold innerBody
      unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0.body
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [if_neg hcontinue]
    unfold innerBody at hbodyDone
    refine ⟨(output, scaled), ?_, houtputCanonical, hscaledCanonical, ?_, ?_⟩
    · unfold innerLoop
      unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0
      rw [loop.eq_def]
      simp only
      rw [hbodyDone]
    · rw [hcarryFinal] at houtputExact
      exact houtputExact
    · rw [hcarryFinal] at hscaledExact
      have hexponent : trailing.val + 1 - 1 = trailing.val := by omega
      rw [hexponent] at hscaledExact
      exact hscaledExact
termination_by trailing.val + 1 - carry.val
decreasing_by
  rw [hcarry1]
  omega

theorem innerLoop_from_one_spec (index trailing : Std.Usize)
    (output : LocalVector) (coefficient : LocalM31)
    (hindex : index.val < 47)
    (htrailing : trailing.val = trailingOnes index.val)
    (houtput : CanonicalLocalVector output)
    (hcoefficient : CanonicalLocalM31 coefficient) :
    Exists fun result : LocalVector × LocalM31 =>
      innerLoop output index trailing 1#usize coefficient = .ok result /\
      CanonicalLocalVector result.1 /\
      CanonicalLocalM31 result.2 /\
      arrayToExact result.1 = arrayToExact output +
        carrySum ⟨index.val, hindex⟩ (m31ToExact coefficient)
          (trailing.val + 1) /\
      m31ToExact result.2 =
        dyadic trailing.val * m31ToExact coefficient := by
  have hinvariant : InnerInvariant (arrayToExact output)
      ⟨index.val, hindex⟩ (m31ToExact coefficient)
      output 1#usize coefficient := by
    refine ⟨houtput, hcoefficient, by simp, ?_, ?_⟩
    · simp [carrySum_one]
    · simp
  exact innerLoop_spec (arrayToExact output) (m31ToExact coefficient)
    index trailing output 1#usize coefficient hindex htrailing (by simp)
    hinvariant

/-- The production 24-byte lookup table is exactly the mathematical
`trailingOnes` recurrence at every reachable odd source index. -/
theorem trailing_table_spec (index : Std.Usize) (hindex : index.val < 47)
    (hodd : index.val % 2 ≠ 0) :
    Exists fun word : Std.U8 =>
      Array.index_usize
          v5_cu_probe.good_gate_probe.ODD_NATURAL_TRAILING_ONES
          (Std.Usize.wrapping_shr index 1#u32) = .ok word /\
      (core.convert.num.FromUsizeU8.from word).val =
        trailingOnes index.val := by
  have hhalf : (Std.Usize.wrapping_shr index 1#u32).val < 24 := by
    rw [usize_wrapping_shr_one_val]
    omega
  obtain ⟨word, hword, hvalue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec
      v5_cu_probe.good_gate_probe.ODD_NATURAL_TRAILING_ONES
      (Std.Usize.wrapping_shr index 1#u32) (by simpa using hhalf))
  refine ⟨word, hword, ?_⟩
  rw [hvalue]
  have hshrVal : (Std.Usize.wrapping_shr index 1#u32).val = index.val / 2 := by
    change index.bv.toNat >>> (1 % System.Platform.numBits) = index.val / 2
    rw [Std.Usize.bv_toNat, Nat.shiftRight_eq_div_pow]
    rcases System.Platform.numBits_eq with hp | hp <;> simp [hp]
  interval_cases hi : index.val <;>
    simp [v5_cu_probe.good_gate_probe.ODD_NATURAL_TRAILING_ONES,
      trailingOnes, hshrVal, hi] at hodd ⊢
  all_goals rfl

theorem carrySum_full (index : Fin 47) (coefficient : ExactM31) :
    carrySum index coefficient (trailingOnes index.val + 1) =
      ∑ carry ∈ Finset.range (trailingOnes index.val),
        Pi.single (carryIndex index (carry + 1))
          (dyadic (carry + 1) * coefficient) := by
  classical
  unfold carrySum
  rw [Finset.sum_Ico_eq_sum_range]
  have hsub : trailingOnes index.val + 1 - 1 = trailingOnes index.val := by
    omega
  rw [hsub]
  apply Finset.sum_congr rfl
  intro carry _
  simpa [Nat.add_comm]

theorem smul_sparse_single (target : Fin 48) (scalar coefficient : ExactM31) :
    coefficient • Pi.single target scalar =
      Pi.single target (scalar * coefficient) := by
  classical
  funext output
  by_cases heq : output = target
  · subst output
    simp [mul_comm]
  · simp [Pi.single_eq_of_ne heq]

theorem even_column_contribution (index : Fin 47) (coefficient : ExactM31)
    (heven : index.val % 2 = 0) :
    (Pi.single (successorIndex index) coefficient : Fin 48 → ExactM31) =
      coefficient • sparseBasis index := by
  classical
  rw [sparseBasis, if_pos heven, smul_sparse_single]
  simp

theorem odd_column_contribution (index : Fin 47) (coefficient : ExactM31)
    (hodd : index.val % 2 ≠ 0) :
    carrySum index coefficient (trailingOnes index.val + 1) +
        Pi.single (successorIndex index)
          (dyadic (trailingOnes index.val) * coefficient) =
      coefficient • sparseBasis index := by
  classical
  rw [carrySum_full, sparseBasis, if_neg hodd, smul_add,
    Finset.smul_sum]
  rw [smul_sparse_single]
  simp_rw [smul_sparse_single]
  ac_rfl

noncomputable def sourceTerm (input : LocalVector) (index : Nat) :
    Fin 48 → ExactM31 :=
  if hindex : index < 47 then
    arrayToExact input (sourceIndex ⟨index, hindex⟩) •
      sparseBasis ⟨index, hindex⟩
  else 0

noncomputable def shiftPrefix (input : LocalVector) (limit : Nat) :
    Fin 48 → ExactM31 :=
  ∑ index ∈ Finset.range limit, sourceTerm input index

theorem shiftPrefix_zero (input : LocalVector) : shiftPrefix input 0 = 0 := by
  simp [shiftPrefix]

theorem shiftPrefix_succ_general (input : LocalVector) (index : Nat) :
    shiftPrefix input (index + 1) =
      shiftPrefix input index + sourceTerm input index := by
  rw [shiftPrefix, Finset.sum_range_succ, shiftPrefix]

theorem shiftPrefix_succ (input : LocalVector) (index : Nat)
    (hindex : index < 47) :
    shiftPrefix input (index + 1) = shiftPrefix input index +
      arrayToExact input (sourceIndex ⟨index, hindex⟩) •
        sparseBasis ⟨index, hindex⟩ := by
  rw [shiftPrefix_succ_general, sourceTerm, dif_pos hindex]

theorem shiftPrefix_full (input : LocalVector) :
    shiftPrefix input 47 = sparseShift (arrayToExact input) := by
  unfold shiftPrefix sparseShift
  simp only [Fintype.linearCombination_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun index => sourceTerm input index) 47]
  apply Finset.sum_congr rfl
  intro index _
  have hindex : index.val < 47 := index.isLt
  simp only [sourceTerm, hindex, ↓reduceDIte, sourceIndex]

/-- Inputs reachable at production shift `shift`: the natural vector is
canonical, has the required alternating parity, and is supported below
`37 + shift`. -/
def FixedSupportInput (input : LocalVector) (shift : Nat) : Prop :=
  CanonicalLocalVector input /\
  shift ≤ 10 /\
  ∀ index : Fin 48,
    (index.val % 2 ≠ shift % 2 ∨ 37 + shift ≤ index.val) →
      arrayToExact input index = 0

theorem sourceTerm_zero_of_outside (input : LocalVector) (shift index : Nat)
    (hshape : FixedSupportInput input shift)
    (houtside : index % 2 ≠ shift % 2 ∨ 37 + shift ≤ index) :
    sourceTerm input index = 0 := by
  unfold sourceTerm
  split
  next hindex =>
    rw [hshape.2.2 (sourceIndex ⟨index, hindex⟩) (by
      simpa [sourceIndex] using houtside)]
    simp
  next => rfl

theorem shiftPrefix_constant (input : LocalVector) (start count : Nat)
    (hzero : ∀ index, start ≤ index → index < start + count →
      sourceTerm input index = 0) :
    shiftPrefix input (start + count) = shiftPrefix input start := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Nat.add_succ, shiftPrefix_succ_general, ih]
      · rw [hzero (start + count) (by omega) (by omega), add_zero]
      · intro index hstart hlt
        exact hzero index hstart (by omega)

theorem shiftPrefix_final_eq_full (input : LocalVector) (shift : Nat)
    (hshape : FixedSupportInput input shift) :
    shiftPrefix input (38 + shift) = sparseShift (arrayToExact input) := by
  have hshift : shift ≤ 10 := hshape.2.1
  have hfinal : shiftPrefix input (38 + shift) =
      shiftPrefix input (37 + shift) := by
    have hs := shiftPrefix_constant input (37 + shift) 1 (by
      intro index hlow hhigh
      apply sourceTerm_zero_of_outside input shift index hshape
      right
      exact hlow)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hfull : shiftPrefix input 47 = shiftPrefix input (37 + shift) := by
    have hcount : 37 + shift + (10 - shift) = 47 := by omega
    have hs := shiftPrefix_constant input (37 + shift) (10 - shift) (by
      intro index hlow hhigh
      apply sourceTerm_zero_of_outside input shift index hshape
      right
      exact hlow)
    rw [hcount] at hs
    exact hs
  rw [hfinal, ← hfull, shiftPrefix_full]

theorem m31ToExact_zero_word :
    m31ToExact (0#u32 : LocalM31) = 0 := by
  change ((0 : Nat) : ExactM31) = 0
  simp

theorem canonical_zero_word : CanonicalLocalM31 (0#u32 : LocalM31) := by
  change (0 : Nat) < AspisV5ComponentCQM31TowerExact.P
  norm_num [AspisV5ComponentCQM31TowerExact.P]

theorem repeated_zero_canonical :
    CanonicalLocalVector (Array.repeat 48#usize (0#u32 : LocalM31)) := by
  intro index
  unfold arrayEntry Array.repeat
  rw [List.getElem_replicate]
  exact canonical_zero_word

theorem repeated_zero_exact :
    arrayToExact (Array.repeat 48#usize (0#u32 : LocalM31)) = 0 := by
  funext index
  unfold arrayToExact arrayEntry Array.repeat
  rw [List.getElem_replicate]
  exact m31ToExact_zero_word

def OuterInvariant (input : LocalVector) (shift : Nat)
    (output : LocalVector) (index : Std.Usize) : Prop :=
  CanonicalLocalVector output /\
  index.val % 2 = shift % 2 /\
  index.val ≤ 38 + shift /\
  arrayToExact output = shiftPrefix input index.val

private abbrev outerLoop :=
  v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0

private abbrev outerBody :=
  v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0.body

theorem outerBody_step (input output : LocalVector) (shift : Nat)
    (supportEnd index : Std.Usize)
    (hshape : FixedSupportInput input shift)
    (hsupportEnd : supportEnd.val = 37 + shift)
    (hcontinueNat : index.val < supportEnd.val)
    (hinvariant : OuterInvariant input shift output index) :
    Exists fun state : LocalVector × Std.Usize =>
      outerBody input supportEnd output index = .ok (.cont state) /\
      state.2.val = index.val + 2 /\
      OuterInvariant input shift state.1 state.2 := by
  rcases hinvariant with
    ⟨houtputCanonical, hindexParity, hindexUpper, houtputExact⟩
  have hshift : shift ≤ 10 := hshape.2.1
  have hindex : index.val < 47 := by rw [hsupportEnd] at hcontinueNat; omega
  have hlength : index.val < input.length := by
    change index.val < input.val.length
    rw [input.property]
    simpa using (show index.val < 48 by omega)
  obtain ⟨coefficient, hcoefficient, hcoefficientValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec input index hlength)
  have hcoefficientCanonical : CanonicalLocalM31 coefficient := by
    rw [hcoefficientValue]
    exact hshape.1 (sourceIndex ⟨index.val, hindex⟩)
  have hcoefficientExact :
      m31ToExact coefficient =
        arrayToExact input (sourceIndex ⟨index.val, hindex⟩) := by
    rw [hcoefficientValue]
    rfl
  let index1 := Std.Usize.wrapping_add index 1#usize
  have hindex1 : index1.val = index.val + 1 := by
    apply usize_wrapping_add_one_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  have hindex1Bound : index1.val < 48 := by rw [hindex1]; omega
  let index2 := Std.Usize.wrapping_add index 2#usize
  have hindex2 : index2.val = index.val + 2 := by
    apply usize_wrapping_add_two_val
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  have hsourceIndex : (⟨index1.val, hindex1Bound⟩ : Fin 48) =
      successorIndex ⟨index.val, hindex⟩ := by
    apply Fin.ext
    exact hindex1
  have hcondition : index < supportEnd := by
    exact (UScalar.lt_equiv _ _).2 hcontinueNat
  have hskipParity : (index.val + 1) % 2 ≠ shift % 2 := by
    omega
  have hskip : sourceTerm input (index.val + 1) = 0 :=
    sourceTerm_zero_of_outside input shift (index.val + 1) hshape
      (Or.inl hskipParity)
  have hprefixSkip : shiftPrefix input (index.val + 1) =
      shiftPrefix input (index.val + 2) := by
    symm
    rw [shiftPrefix_succ_general, hskip, add_zero]
  by_cases heven : index.val % 2 = 0
  · have hbit : index &&& 1#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa [usize_and_one_val] using heven
    obtain ⟨updated, hupdated, hupdatedCanonical, hupdatedExact⟩ :=
      local_vector_add_at_spec output index1 coefficient hindex1Bound
        houtputCanonical hcoefficientCanonical
    have hnextInvariant : OuterInvariant input shift updated index2 := by
      refine ⟨hupdatedCanonical, ?_, ?_, ?_⟩
      · rw [hindex2]
        omega
      · rw [hindex2]
        rw [hsupportEnd] at hcontinueNat
        omega
      · rw [hupdatedExact, hsourceIndex,
          even_column_contribution ⟨index.val, hindex⟩
            (m31ToExact coefficient) heven,
          hcoefficientExact, houtputExact]
        rw [← shiftPrefix_succ input index.val hindex, hprefixSkip, hindex2]
    refine ⟨(updated, index2), ?_, hindex2, hnextInvariant⟩
    unfold outerBody
    unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0.body
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    rw [if_pos hcondition, hcoefficient]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [if_pos hbit]
    change (do
        let current ← Array.index_usize output index1
        let sum ← aspis_verifier.aspis_core.field.M31.add current coefficient
        let updated1 ← Array.update output index1 sum
        let index3 ← Aeneas.Std.lift (Std.Usize.wrapping_add index 2#usize)
        .ok (ControlFlow.cont (updated1, index3))) = _
    have hupdated' :
        ((do
            let current ← Array.index_usize output index1
            aspis_verifier.aspis_core.field.M31.add current coefficient) >>=
          Array.update output index1) = .ok updated := by
      rw [Aeneas.Std.bind_assoc_eq]
      exact hupdated
    rw [← Aeneas.Std.bind_assoc_eq, ← Aeneas.Std.bind_assoc_eq,
      hupdated']
    rfl
  · have hodd : index.val % 2 ≠ 0 := heven
    have hbit : index &&& 1#usize ≠ 0#usize := by
      intro equal
      have hval := congrArg UScalar.val equal
      simp [usize_and_one_val] at hval
      exact hodd hval
    obtain ⟨tableWord, htableWord, htableValue⟩ :=
      trailing_table_spec index hindex hodd
    let trailing := core.convert.num.FromUsizeU8.from tableWord
    have htrailing : trailing.val = trailingOnes index.val := by
      exact htableValue
    obtain ⟨innerResult, hinnerResult, hinnerCanonical, hscaledCanonical,
        hinnerExact, hscaledExact⟩ :=
      innerLoop_from_one_spec index trailing output coefficient hindex htrailing
        houtputCanonical hcoefficientCanonical
    unfold innerLoop at hinnerResult
    obtain ⟨updated, hupdated, hupdatedCanonical, hupdatedExact⟩ :=
      local_vector_add_at_spec innerResult.1 index1 innerResult.2 hindex1Bound
        hinnerCanonical hscaledCanonical
    have hnextInvariant : OuterInvariant input shift updated index2 := by
      refine ⟨hupdatedCanonical, ?_, ?_, ?_⟩
      · rw [hindex2]
        omega
      · rw [hindex2]
        rw [hsupportEnd] at hcontinueNat
        omega
      · rw [hupdatedExact, hsourceIndex, hscaledExact, htrailing,
          hinnerExact, htrailing]
        calc
          (arrayToExact output +
                carrySum ⟨index.val, hindex⟩ (m31ToExact coefficient)
                  (trailingOnes index.val + 1)) +
              Pi.single (successorIndex ⟨index.val, hindex⟩)
                (dyadic (trailingOnes index.val) * m31ToExact coefficient) =
              arrayToExact output +
                (carrySum ⟨index.val, hindex⟩ (m31ToExact coefficient)
                    (trailingOnes index.val + 1) +
                  Pi.single (successorIndex ⟨index.val, hindex⟩)
                    (dyadic (trailingOnes index.val) *
                      m31ToExact coefficient)) := by
                funext outputIndex
                simp only [Pi.add_apply]
                ring
          _ = arrayToExact output +
                m31ToExact coefficient • sparseBasis ⟨index.val, hindex⟩ := by
              rw [odd_column_contribution ⟨index.val, hindex⟩
                (m31ToExact coefficient) hodd]
          _ = shiftPrefix input (index.val + 1) := by
              rw [hcoefficientExact, houtputExact,
                ← shiftPrefix_succ input index.val hindex]
          _ = shiftPrefix input index2.val := by
              rw [hindex2, hprefixSkip]
    refine ⟨(updated, index2), ?_, hindex2, hnextInvariant⟩
    unfold outerBody
    unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0.body
    simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
    rw [if_pos hcondition, hcoefficient]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [if_neg hbit]
    rw [htableWord]
    simp only [Aeneas.Std.bind_tc_ok]
    change (do
        let trailing1 ← Aeneas.Std.lift trailing
        let inner ←
          v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0_loop0
            output index trailing1 1#usize coefficient
        let current ← Array.index_usize inner.1 index1
        let sum ← aspis_verifier.aspis_core.field.M31.add current inner.2
        let updated1 ← Array.update inner.1 index1 sum
        let index3 ← Aeneas.Std.lift (Std.Usize.wrapping_add index 2#usize)
        .ok (ControlFlow.cont (updated1, index3))) = _
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, hinnerResult]
    change (do
        let current ← Array.index_usize innerResult.1 index1
        let sum ← aspis_verifier.aspis_core.field.M31.add current innerResult.2
        let updated1 ← Array.update innerResult.1 index1 sum
        let index3 ← Aeneas.Std.lift (Std.Usize.wrapping_add index 2#usize)
        .ok (ControlFlow.cont (updated1, index3))) = _
    have hupdated' :
        ((do
            let current ← Array.index_usize innerResult.1 index1
            aspis_verifier.aspis_core.field.M31.add current innerResult.2) >>=
          Array.update innerResult.1 index1) = .ok updated := by
      rw [Aeneas.Std.bind_assoc_eq]
      exact hupdated
    rw [← Aeneas.Std.bind_assoc_eq, ← Aeneas.Std.bind_assoc_eq,
      hupdated']
    rfl

theorem outerLoop_spec (input output : LocalVector) (shift : Nat)
    (supportEnd index : Std.Usize)
    (hshape : FixedSupportInput input shift)
    (hsupportEnd : supportEnd.val = 37 + shift)
    (hinvariant : OuterInvariant input shift output index) :
    Exists fun result : LocalVector =>
      outerLoop input output supportEnd index = .ok result /\
      CanonicalLocalVector result /\
      arrayToExact result = sparseShift (arrayToExact input) := by
  by_cases hcontinueNat : index.val < supportEnd.val
  · obtain ⟨state, hbody, hindex2, hstateInvariant⟩ :=
      outerBody_step input output shift supportEnd index hshape hsupportEnd
        hcontinueNat hinvariant
    unfold outerBody at hbody
    obtain ⟨result, hresult, hresultCanonical, hresultExact⟩ :=
      outerLoop_spec input state.1 shift supportEnd state.2 hshape hsupportEnd
        hstateInvariant
    unfold outerLoop at hresult
    refine ⟨result, ?_, hresultCanonical, hresultExact⟩
    unfold outerLoop
    unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0
    rw [loop.eq_def]
    simp only
    rw [hbody]
    exact hresult
  · rcases hinvariant with
      ⟨houtputCanonical, hindexParity, hindexUpper, houtputExact⟩
    have hshift : shift ≤ 10 := hshape.2.1
    have hindexFinal : index.val = 38 + shift := by
      have hlower : 37 + shift ≤ index.val := by
        rw [← hsupportEnd]
        omega
      omega
    have hcondition : ¬ index < supportEnd := by
      intro hlt
      exact hcontinueNat ((UScalar.lt_equiv _ _).1 hlt)
    have hbodyDone : outerBody input supportEnd output index =
        .ok (.done output) := by
      unfold outerBody
      unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0.body
      simp only [Aeneas.Std.lift, Bind.bind, Aeneas.Std.bind]
      rw [if_neg hcondition]
    unfold outerBody at hbodyDone
    refine ⟨output, ?_, houtputCanonical, ?_⟩
    · unfold outerLoop
      unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support_loop0
      rw [loop.eq_def]
      simp only
      rw [hbodyDone]
    · rw [hindexFinal] at houtputExact
      rw [houtputExact]
      exact shiftPrefix_final_eq_full input shift hshape
termination_by 38 + shift - index.val
decreasing_by
  rw [hindex2]
  omega

/-- Exact production specialization: on every reachable support/parity state
and every production shift `0..10`, the authentic fixed-support Rust loop is
the independently defined sparse natural-basis multiplication by `X`. -/
theorem natural_mul_x_fixed_support_exact_spec (input : LocalVector)
    (shift : Std.Usize) (hshape : FixedSupportInput input shift.val) :
    Exists fun output : LocalVector =>
      v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support input shift =
        .ok output /\
      CanonicalLocalVector output /\
      arrayToExact output = sparseShift (arrayToExact input) := by
  have hshift : shift.val ≤ 10 := hshape.2.1
  let zero : LocalM31 := 0#u32
  let initial : LocalVector := Array.repeat 48#usize zero
  have hzeroResult : aspis_verifier.aspis_core.field.M31.ZERO = .ok zero := by
    unfold aspis_verifier.aspis_core.field.M31.ZERO zero
    rw [_root_.aspis_core.field.M31.ZERO]
  have hinitialCanonical : CanonicalLocalVector initial :=
    repeated_zero_canonical
  have hinitialExact : arrayToExact initial = 0 := repeated_zero_exact
  let intermediate := Std.Usize.wrapping_add
    v5_cu_probe.good_gate_probe.KERNEL_DEGREE shift
  have hintermediate : intermediate.val = 36 + shift.val := by
    unfold intermediate
    rw [v5_cu_probe.good_gate_probe.KERNEL_DEGREE,
      Std.Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    rw [UScalar.size_UScalarTyUsize]
    change 36 + shift.val < Std.Usize.size
    have hsize : 64 < Std.Usize.size := by
      rcases System.Platform.numBits_eq with hp | hp <;>
        norm_num [Std.Usize.size, Std.Usize.numBits, hp]
    omega
  let supportEnd := Std.Usize.wrapping_add intermediate 1#usize
  have hsupportEnd : supportEnd.val = 37 + shift.val := by
    unfold supportEnd
    rw [usize_wrapping_add_one_val]
    · omega
    · have hsize : 64 < Std.Usize.size := by
        rcases System.Platform.numBits_eq with hp | hp <;>
          norm_num [Std.Usize.size, Std.Usize.numBits, hp]
      rw [hintermediate]
      omega
  let start := shift &&& 1#usize
  have hstart : start.val = shift.val % 2 := by
    unfold start
    exact usize_and_one_val shift
  have hstartUpper : start.val ≤ 1 := by rw [hstart]; omega
  have hinitialPrefix : arrayToExact initial = shiftPrefix input start.val := by
    rw [hinitialExact]
    by_cases heven : shift.val % 2 = 0
    · have hstartZero : start.val = 0 := by rw [hstart, heven]
      rw [hstartZero, shiftPrefix_zero]
    · have hmod : shift.val % 2 = 1 := by omega
      have hstartOne : start.val = 1 := by rw [hstart, hmod]
      rw [hstartOne, shiftPrefix_succ_general, shiftPrefix_zero]
      rw [sourceTerm_zero_of_outside input shift.val 0 hshape]
      · simp
      · left
        omega
  have hinitialInvariant : OuterInvariant input shift.val initial start := by
    refine ⟨hinitialCanonical, ?_, ?_, hinitialPrefix⟩
    · rw [hstart]
      omega
    omega
  obtain ⟨output, houtput, houtputCanonical, houtputExact⟩ :=
    outerLoop_spec input initial shift.val supportEnd start hshape hsupportEnd
      hinitialInvariant
  unfold outerLoop at houtput
  refine ⟨output, ?_, houtputCanonical, houtputExact⟩
  unfold v5_cu_probe.good_gate_probe.natural_mul_x_fixed_support
  rw [hzeroResult]
  change outerLoop input initial
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_add
          v5_cu_probe.good_gate_probe.KERNEL_DEGREE shift) 1#usize)
      (shift &&& 1#usize) = .ok output
  exact houtput

theorem carryIndex_even_of_odd (source : Fin 47) (carry : Nat)
    (hsourceOdd : source.val % 2 ≠ 0) (hcarry : 1 ≤ carry)
    (hcarryTop : carry ≤ trailingOnes source.val) :
    (carryIndex source carry).val % 2 = 0 := by
  have hpow : 2 ^ carry ≤ source.val + 1 :=
    (Nat.pow_le_pow_right (by omega) hcarryTop).trans
      (pow_trailingOnes_le_succ source.val)
  have hoffsetLe : 2 ^ carry - 1 ≤ source.val := by omega
  have hpowEven : Even (2 ^ carry) := by
    rw [Nat.even_pow]
    constructor
    · exact ⟨1, by norm_num⟩
    · omega
  have hoffsetNotEven : ¬ Even (2 ^ carry - 1) := by
    intro hoffsetEven
    have hequiv := (Nat.even_sub Nat.one_le_two_pow).1 hoffsetEven
    exact Nat.not_even_one (hequiv.mp hpowEven)
  have hsourceNotEven : ¬ Even source.val := by
    intro hsourceEven
    exact hsourceOdd (Nat.even_iff.mp hsourceEven)
  have hdifferenceEven : Even (source.val - (2 ^ carry - 1)) :=
    (Nat.even_sub hoffsetLe).2 (iff_of_false hsourceNotEven hoffsetNotEven)
  change (source.val - (2 ^ carry - 1)) % 2 = 0
  exact Nat.even_iff.mp hdifferenceEven

theorem sparseBasis_zero_of_bad (source : Fin 47) (output : Fin 48)
    (hbad : output.val % 2 ≠ (source.val + 1) % 2 ∨
      source.val + 1 < output.val) :
    sparseBasis (K := ExactM31) source output = 0 := by
  classical
  by_cases heven : source.val % 2 = 0
  · rw [sparseBasis, if_pos heven]
    apply Pi.single_eq_of_ne
    intro heq
    have hvalue := congrArg Fin.val heq
    simp [successorIndex] at hvalue
    rcases hbad with hparity | habove
    · omega
    · omega
  · rw [sparseBasis, if_neg heven]
    simp only [Pi.add_apply, Finset.sum_apply]
    have hsuccessor : output ≠ successorIndex source := by
      intro heq
      have hvalue := congrArg Fin.val heq
      simp [successorIndex] at hvalue
      rcases hbad with hparity | habove
      · omega
      · omega
    rw [Pi.single_eq_of_ne hsuccessor, zero_add]
    apply Finset.sum_eq_zero
    intro carry hcarryMem
    rw [Pi.single_eq_of_ne]
    intro heq
    have hvalue := congrArg Fin.val heq
    have hcarryRange := Finset.mem_range.mp hcarryMem
    have hcarryTop : carry + 1 ≤ trailingOnes source.val := by omega
    have htargetParity := carryIndex_even_of_odd source (carry + 1)
      heven (by omega) hcarryTop
    rcases hbad with hparity | habove
    · rw [hvalue] at hparity
      have hnextParity : (source.val + 1) % 2 = 0 := by omega
      exact hparity (by omega)
    · have htargetLe : (carryIndex source (carry + 1)).val ≤ source.val := by
        change source.val - (2 ^ (carry + 1) - 1) ≤ source.val
        omega
      rw [hvalue] at habove
      omega

theorem sparseShift_shape (input : LocalVector) (shift : Nat)
    (hshape : FixedSupportInput input shift) (hshift : shift ≤ 9) :
    ∀ output : Fin 48,
      (output.val % 2 ≠ (shift + 1) % 2 ∨
          37 + (shift + 1) ≤ output.val) →
        sparseShift (arrayToExact input) output = 0 := by
  classical
  intro output hbad
  unfold sparseShift
  simp only [Fintype.linearCombination_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro source _
  by_cases hsource :
      source.val % 2 ≠ shift % 2 ∨ 37 + shift ≤ source.val
  · rw [hshape.2.2 (sourceIndex source) (by
      simpa [sourceIndex] using hsource)]
    simp
  · push_neg at hsource
    have hbasis : sparseBasis (K := ExactM31) source output = 0 := by
      apply sparseBasis_zero_of_bad source output
      rcases hbad with hparity | habove
      · left
        omega
      · right
        omega
    change arrayToExact input (sourceIndex source) *
      sparseBasis (K := ExactM31) source output = 0
    rw [hbasis, mul_zero]

theorem fixedSupportInput_of_exact_sparseShift (input output : LocalVector)
    (shift : Nat) (hshape : FixedSupportInput input shift) (hshift : shift ≤ 9)
    (hcanonical : CanonicalLocalVector output)
    (hexact : arrayToExact output = sparseShift (arrayToExact input)) :
    FixedSupportInput output (shift + 1) := by
  refine ⟨hcanonical, by omega, ?_⟩
  intro index hbad
  rw [hexact]
  exact sparseShift_shape input shift hshape hshift index hbad

end GoodMatricesCurrent.SourceExtractedFixedSupport
