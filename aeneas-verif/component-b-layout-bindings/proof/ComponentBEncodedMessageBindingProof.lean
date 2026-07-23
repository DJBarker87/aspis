import ComponentBLayoutBindingsProof
import AspisFormal.V5M31RawSubNeg
import Aeneas.Tactic.Step.StepStar

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators QuadraticAlgebra

namespace ComponentBEncodedMessageBindingProof

open ComponentBGenerated
open ComponentBLayoutBindingsProof
open AspisV5CompactTerminal

abbrev QM31 := ComponentBGenerated.aspis_core.field.QM31
abbrev ExactQM31 := ComponentBRealEvaluatorProof.ExactQM31
abbrev Mask := ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask

local instance : Inhabited QM31 :=
  ⟨ComponentBGenerated.aspis_core.field.QM31.ZERO⟩

def CanonicalMask (mask : Mask) : Prop :=
  ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 mask.initial_claim ∧
    ∀ round : Nat, round < 10 → ∀ coefficient : Nat, coefficient < 28 →
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31
        mask.zero_boundary_rounds.val[round]!.val[coefficient]!

def maskInitial (mask : Mask) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact mask.initial_claim

def maskTails (mask : Mask) (round : Round)
    (degree : TailDegree) : ExactQM31 :=
  ComponentBRealEvaluatorProof.generatedQm31ToExact
    mask.zero_boundary_rounds.val[round.val]!.val[degree.val + 1]!

def roundIndex (round : Std.Usize) (hround : round.val < 10) : Round :=
  ⟨round.val, by simpa [AspisV5SumcheckCommitment.roundCount] using hround⟩

def storedDegreeIndex (coefficient : Std.Usize)
    (hcoefficient : coefficient.val < 28) : StoredDegree :=
  ⟨coefficient.val, hcoefficient⟩

def roundUsize (round : Round) : Std.Usize :=
  Std.Usize.ofNatCore round.val (by
    have hsize : 11 < 2 ^ UScalarTy.Usize.numBits := by
      simpa using UScalar.hBounds (11#usize)
    have hround : round.val < 10 := by
      have h := round.isLt
      simpa only [AspisV5SumcheckCommitment.roundCount] using h
    omega)

@[simp] theorem roundUsize_val (round : Round) :
    (roundUsize round).val = round.val := by
  unfold roundUsize
  apply Std.Usize.ofNatCore_val_eq

def storedDegreeUsize (degree : StoredDegree) : Std.Usize :=
  Std.Usize.ofNatCore degree.val (by
    have hsize : 29 < 2 ^ UScalarTy.Usize.numBits := by
      simpa using UScalar.hBounds (29#usize)
    omega)

@[simp] theorem storedDegreeUsize_val (degree : StoredDegree) :
    (storedDegreeUsize degree).val = degree.val := by
  unfold storedDegreeUsize
  apply Std.Usize.ofNatCore_val_eq

theorem roundIndex_roundUsize (round : Round) :
    roundIndex (roundUsize round) (by
      have h := round.isLt
      rw [roundUsize_val]
      simpa only [AspisV5SumcheckCommitment.roundCount] using h) = round := by
  apply Fin.ext
  exact roundUsize_val round

theorem storedDegreeIndex_storedDegreeUsize (degree : StoredDegree) :
    storedDegreeIndex (storedDegreeUsize degree) (by exact degree.isLt) =
      degree := by
  apply Fin.ext
  exact storedDegreeUsize_val degree

private def tailPrefix (mask : Mask) (round : Nat) : Nat → ExactQM31
  | 0 => 0
  | count + 1 =>
      tailPrefix mask round count +
        ComponentBRealEvaluatorProof.generatedQm31ToExact
          mask.zero_boundary_rounds.val[round]!.val[count + 1]!

private theorem tailPrefix_eq_sum_range (mask : Mask) (round count : Nat) :
    tailPrefix mask round count =
      ∑ index ∈ Finset.range count,
        ComponentBRealEvaluatorProof.generatedQm31ToExact
          mask.zero_boundary_rounds.val[round]!.val[index + 1]! := by
  induction count with
  | zero => simp [tailPrefix]
  | succ count ih =>
      rw [tailPrefix, ih, Finset.sum_range_succ]

private theorem tailPrefix_twentySeven_eq_sum_tails
    (mask : Mask) (round : Round) :
    tailPrefix mask round.val 27 = ∑ degree, maskTails mask round degree := by
  rw [tailPrefix_eq_sum_range]
  let summand := fun degree : Nat =>
    ComponentBRealEvaluatorProof.generatedQm31ToExact
      mask.zero_boundary_rounds.val[round.val]!.val[degree + 1]!
  change (∑ degree ∈ Finset.range 27, summand degree) =
    ∑ degree : Fin 27, summand degree.val
  exact (Fin.sum_univ_eq_sum_range summand 27).symm

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

private theorem array_index_usize_run
    {T : Type} [Inhabited T] {n : Std.Usize}
    (values : Array T n) (index : Std.Usize)
    (hIndex : index.val < n.val) :
    values.index_usize index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  rw [hRun]
  congr
  rw [hValue]
  exact list_get_eq_getElemBang values.val index.val (by
    simpa [Array.length_eq] using hIndex)

private theorem wrapping_add_one_val (value : Std.Usize)
    (hvalue : value.val < 1024) :
    (value.wrapping_add 1#usize).val = value.val + 1 := by
  simp only [Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hsize : 1025 < Usize.size := by
    simpa using UScalar.hSize (1025#usize)
  norm_num
  omega

private theorem generated_add_spec
    (left right : QM31)
    (hleft : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 left)
    (hright : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 right) :
    ComponentBGenerated.aspis_core.field.QM31.add left right ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        ComponentBRealEvaluatorProof.generatedQm31ToExact left +
          ComponentBRealEvaluatorProof.generatedQm31ToExact right ⦄ := by
  obtain ⟨out, run, canonical, exact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_add_corresponds
      left right hleft hright
  rw [run]
  exact ⟨canonical, exact⟩

private theorem generated_wrapping_P_sub_val
    (value : ComponentBGenerated.aspis_core.field.M31)
    (hvalue : AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val) :
    (Std.U32.wrapping_sub ComponentBGenerated.aspis_core.field.P value).val =
      2147483647 - value.val := by
  rw [Std.U32.wrapping_sub_val_eq]
  have hsize : Std.U32.size = 2 ^ 32 := by
    norm_num [Std.U32.size, Std.U32.numBits]
  rw [UScalar.size_UScalarTyU32, hsize]
  have hP : ComponentBGenerated.aspis_core.field.P.val = 2147483647 := by
    unfold ComponentBGenerated.aspis_core.field.P
    rfl
  rw [hP]
  have hvalueLt : value.val < 2147483647 := by
    simpa [AspisAeneasCM31Multiplicative.CanonicalRawM31,
      AspisAeneasCM31Multiplicative.m31Modulus] using hvalue
  have hsmall : 2147483647 - value.val < 2 ^ 32 := by omega
  have hrearrange :
      2147483647 + (2 ^ 32 - value.val) =
        (2147483647 - value.val) + 2 ^ 32 := by
    omega
  change (2147483647 + (2 ^ 32 - value.val)) % 2 ^ 32 = _
  rw [hrearrange, Nat.add_mod_right, Nat.mod_eq_of_lt hsmall]

private theorem generated_m31_neg_spec
    (value : ComponentBGenerated.aspis_core.field.M31)
    (hvalue : AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val) :
    ComponentBGenerated.aspis_core.field.M31.neg value ⦃ out =>
      AspisAeneasCM31Multiplicative.CanonicalRawM31 out.val ∧
      ((out.val : Nat) : ComponentBRealEvaluatorProof.ExactM31) =
        -((value.val : Nat) : ComponentBRealEvaluatorProof.ExactM31) ⦄ := by
  unfold ComponentBGenerated.aspis_core.field.M31.neg
  by_cases hzero : value.val = 0
  · have hscalar : value = 0#u32 := by
      apply UScalar.eq_of_val_eq
      simpa using hzero
    rw [if_pos hscalar]
    simp only [WP.spec, WP.theta]
    refine ⟨?_, ?_⟩
    · norm_num [AspisAeneasCM31Multiplicative.CanonicalRawM31,
        AspisAeneasCM31Multiplicative.m31Modulus]
    · simp [hzero]
  · have hscalar : value ≠ 0#u32 := by
      intro h
      exact hzero (congrArg UScalar.val h)
    rw [if_neg hscalar]
    simp only [lift, bind_tc_ok, WP.spec, WP.theta]
    have hvalueLt : value.val < 2147483647 := by
      simpa [AspisAeneasCM31Multiplicative.CanonicalRawM31,
        AspisAeneasCM31Multiplicative.m31Modulus] using hvalue
    have hwrapped := generated_wrapping_P_sub_val value hvalue
    refine ⟨?_, ?_⟩
    · simp only [AspisAeneasCM31Multiplicative.CanonicalRawM31,
        AspisAeneasCM31Multiplicative.m31Modulus]
      rw [hwrapped]
      omega
    · have hraw :
          AspisV5M31RawSubNeg.rawM31Neg value.val =
            2147483647 - value.val := by
        rw [AspisV5M31RawSubNeg.rawM31Neg, if_neg hzero]
      have hexact := AspisV5M31RawSubNeg.residue_rawM31Neg
        (x := value.val) (by
          simpa [AspisV5ComponentCQM31RustFormulaSeam.CanonicalRawM31,
            AspisV5ComponentCQM31TowerExact.P] using hvalueLt)
      rw [hraw] at hexact
      rw [hwrapped]
      exact hexact

private theorem generated_cm31_neg_spec
    (value : ComponentBGenerated.aspis_core.field.CM31)
    (hvalue : ComponentBRealEvaluatorProof.GeneratedCanonicalCM31 value) :
    ComponentBGenerated.aspis_core.field.CM31.neg value ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalCM31 out ∧
      ComponentBRealEvaluatorProof.generatedCm31ToExact out =
        -ComponentBRealEvaluatorProof.generatedCm31ToExact value ⦄ := by
  obtain ⟨aOut, aRun, aCanonical, aExact⟩ :=
    WP.spec_imp_exists (generated_m31_neg_spec value.a hvalue.1)
  obtain ⟨bOut, bRun, bCanonical, bExact⟩ :=
    WP.spec_imp_exists (generated_m31_neg_spec value.b hvalue.2)
  unfold ComponentBGenerated.aspis_core.field.CM31.neg
  rw [aRun, bRun]
  simp only [bind_tc_ok, WP.spec, WP.theta]
  refine ⟨⟨aCanonical, bCanonical⟩, ?_⟩
  apply QuadraticAlgebra.ext
  · simpa [ComponentBRealEvaluatorProof.generatedCm31ToExact] using aExact
  · simpa [ComponentBRealEvaluatorProof.generatedCm31ToExact] using bExact

private theorem generated_neg_spec (value : QM31)
    (hvalue : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 value) :
    ComponentBGenerated.aspis_core.field.QM31.neg value ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        -ComponentBRealEvaluatorProof.generatedQm31ToExact value ⦄ := by
  obtain ⟨c0Out, c0Run, c0Canonical, c0Exact⟩ :=
    WP.spec_imp_exists (generated_cm31_neg_spec value.c0 hvalue.1)
  obtain ⟨c1Out, c1Run, c1Canonical, c1Exact⟩ :=
    WP.spec_imp_exists (generated_cm31_neg_spec value.c1 hvalue.2)
  unfold ComponentBGenerated.aspis_core.field.QM31.neg
  rw [c0Run, c1Run]
  simp only [bind_tc_ok, WP.spec, WP.theta]
  refine ⟨⟨c0Canonical, c1Canonical⟩, ?_⟩
  apply QuadraticAlgebra.ext
  · simpa [ComponentBRealEvaluatorProof.generatedQm31ToExact] using c0Exact
  · simpa [ComponentBRealEvaluatorProof.generatedQm31ToExact] using c1Exact

private theorem commitment_coefficient_sum_loop_spec
    (mask : Mask) (round : Std.Usize) (sum : QM31)
    (offset : Std.Usize) (hmask : CanonicalMask mask)
    (hround : round.val < 10) (hoffsetOne : 1 ≤ offset.val)
    (hoffsetBound : offset.val ≤ 28)
    (hsumCanonical :
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 sum)
    (hsumExact :
      ComponentBRealEvaluatorProof.generatedQm31ToExact sum =
        tailPrefix mask round.val (offset.val - 1)) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop
        mask round sum offset ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        tailPrefix mask round.val 27 ⦄ := by
  simp only [ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop]
  apply loop.spec_decr_nat
    (fun state => 28 - state.2.val)
    (fun state =>
      1 ≤ state.2.val ∧ state.2.val ≤ 28 ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 state.1 ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact state.1 =
        tailPrefix mask round.val (state.2.val - 1))
    (fun out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        tailPrefix mask round.val 27)
  · rintro ⟨current, currentOffset⟩
      ⟨hcurrentOne, hcurrentBound, hcurrentCanonical, hcurrentExact⟩
    have hcurrentOne' : 1 ≤ currentOffset.val := by
      simpa only using hcurrentOne
    have hcurrentBound' : currentOffset.val ≤ 28 := by
      simpa only using hcurrentBound
    unfold ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop.body
    by_cases hlt : currentOffset < 28#usize
    · rw [if_pos hlt]
      have hoffsetLt : currentOffset.val < 28 := hlt
      rw [array_index_usize_run mask.zero_boundary_rounds round hround]
      simp only [bind_tc_ok]
      rw [array_index_usize_run
        mask.zero_boundary_rounds.val[round.val]! currentOffset hoffsetLt]
      simp only [bind_tc_ok]
      have hcoefficientCanonical := hmask.2 round.val hround
        currentOffset.val hoffsetLt
      have hadd := generated_add_spec current
        mask.zero_boundary_rounds.val[round.val]!.val[currentOffset.val]!
        hcurrentCanonical hcoefficientCanonical
      obtain ⟨next, nextRun, nextCanonical, nextExact⟩ :=
        WP.spec_imp_exists hadd
      rw [nextRun]
      simp only [bind_tc_ok]
      have hnext := wrapping_add_one_val currentOffset (by omega)
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_, nextCanonical, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · rw [hnext]
        omega
      · rw [nextExact, hcurrentExact, hnext]
        have hsub : currentOffset.val + 1 - 1 = currentOffset.val := by
          omega
        rw [hsub]
        have hpred : currentOffset.val - 1 + 1 = currentOffset.val := by
          omega
        conv_rhs => rw [show currentOffset.val =
          (currentOffset.val - 1) + 1 by omega]
        rw [tailPrefix]
        rw [hpred]
      · rw [hnext]
        omega
    · rw [if_neg hlt]
      have hnotLt : ¬ currentOffset.val < 28 := by
        intro hsmall
        exact hlt hsmall
      have hoffsetEq : currentOffset.val = 28 := by
        omega
      simp only [WP.spec, WP.theta]
      refine ⟨hcurrentCanonical, ?_⟩
      rw [hcurrentExact, hoffsetEq]
  · simpa only [Prod.fst, Prod.snd] using
      And.intro hoffsetOne (And.intro hoffsetBound
        (And.intro hsumCanonical hsumExact))

private theorem exact_two_ne_zero : (2 : ExactQM31) ≠ 0 := by
  intro h
  have hre := congrArg QuadraticAlgebra.re h
  have hrere := congrArg QuadraticAlgebra.re hre
  change (2 : AspisAeneasCM31Exact.M31Exact) = 0 at hrere
  exact (by decide : (2 : AspisAeneasCM31Exact.M31Exact) ≠ 0) hrere

private theorem generated_half_ONE_spec :
    ComponentBGenerated.aspis_core.field.QM31.half
        ComponentBGenerated.aspis_core.field.QM31.ONE ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        AspisV5SumcheckCommitment.half ⦄ := by
  obtain ⟨halfValue, halfRun, halfCanonical, _⟩ :=
    ComponentBHalfCombinedProof.generated_qm31_half_doubles_canonical
      ComponentBGenerated.aspis_core.field.QM31.ONE (by
        simpa [ComponentBHalfCombinedProof.CanonicalQM31,
          ComponentBRealEvaluatorProof.GeneratedCanonicalQM31,
          ComponentBRealEvaluatorProof.GeneratedCanonicalCM31,
          AspisAeneasCM31Multiplicative.CanonicalRawM31,
          AspisAeneasCM31Multiplicative.m31Modulus] using
            ComponentBLayoutBindingsProof.generated_ONE_canonical)
  rw [halfRun]
  have halfExact :=
    ComponentBMaintainedTerminalBridge.generated_half_exact
      ComponentBGenerated.aspis_core.field.QM31.ONE halfValue
      exact_two_ne_zero
      ComponentBLayoutBindingsProof.generated_ONE_canonical halfRun
  refine ⟨halfExact.1, ?_⟩
  rw [halfExact.2, ComponentBLayoutBindingsProof.generated_ONE_exact]
  exact mul_one _

private theorem generated_mul_spec
    (left right : QM31)
    (hleft : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 left)
    (hright : ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 right) :
    ComponentBGenerated.aspis_core.field.QM31.mul left right ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        ComponentBRealEvaluatorProof.generatedQm31ToExact left *
          ComponentBRealEvaluatorProof.generatedQm31ToExact right ⦄ := by
  obtain ⟨out, run, canonical, exact⟩ :=
    ComponentBRealEvaluatorProof.generated_qm31_mul_corresponds
      left right hleft hright
  rw [run]
  exact ⟨canonical, exact⟩

/-- The source-authentic accessor computes precisely the maintained stored
coefficient: coefficient zero is the negative tail sum times one half, while
coefficients one through 27 are the corresponding sampled tails. -/
theorem extracted_commitment_coefficient_eq_storedCoefficient
    (mask : Mask) (round coefficient : Std.Usize)
    (hmask : CanonicalMask mask)
    (hround : round.val < 10) (hcoefficient : coefficient.val < 28) :
    ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient
        mask round coefficient ⦃ out =>
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        storedCoefficient (maskTails mask)
          (roundIndex round hround,
            storedDegreeIndex coefficient hcoefficient) ⦄ := by
  unfold ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient
  by_cases hzeroVal : coefficient.val = 0
  · have hzero : coefficient = 0#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hzeroVal
    rw [if_pos hzero]
    have hloop := commitment_coefficient_sum_loop_spec mask round
      ComponentBGenerated.aspis_core.field.QM31.ZERO 1#usize hmask hround
      (by decide) (by decide)
      ComponentBLayoutBindingsProof.generated_ZERO_canonical (by
        rw [ComponentBLayoutBindingsProof.generated_ZERO_exact]
        rfl)
    obtain ⟨tailSum, tailRun, tailCanonical, tailExact⟩ :=
      WP.spec_imp_exists hloop
    rw [tailRun]
    simp only [bind_tc_ok]
    have hneg := generated_neg_spec tailSum tailCanonical
    obtain ⟨negative, negativeRun, negativeCanonical, negativeExact⟩ :=
      WP.spec_imp_exists hneg
    rw [negativeRun]
    simp only [bind_tc_ok]
    have hhalf := generated_half_ONE_spec
    obtain ⟨halfValue, halfRun, halfCanonical, halfExact⟩ :=
      WP.spec_imp_exists hhalf
    rw [halfRun]
    simp only [bind_tc_ok]
    have hproduct := generated_mul_spec negative halfValue
      negativeCanonical halfCanonical
    obtain ⟨product, productRun, productCanonical, productExact⟩ :=
      WP.spec_imp_exists hproduct
    rw [productRun]
    simp only [WP.spec, WP.theta]
    refine ⟨productCanonical, ?_⟩
    rw [productExact, negativeExact, halfExact, tailExact]
    have htail : tailPrefix mask round.val 27 =
        ∑ degree, maskTails mask (roundIndex round hround) degree := by
      simpa [roundIndex] using
        tailPrefix_twentySeven_eq_sum_tails mask (roundIndex round hround)
    rw [htail]
    have hdegree : storedDegreeIndex coefficient hcoefficient = 0 := by
      apply Fin.ext
      exact hzeroVal
    rw [hdegree, storedCoefficient_zero]
  · have hzero : coefficient ≠ 0#usize := by
      intro h
      exact hzeroVal (congrArg UScalar.val h)
    rw [if_neg hzero]
    rw [array_index_usize_run mask.zero_boundary_rounds round hround]
    simp only [bind_tc_ok]
    rw [array_index_usize_run
      mask.zero_boundary_rounds.val[round.val]! coefficient hcoefficient]
    simp only [WP.spec, WP.theta]
    have hcanonical := hmask.2 round.val hround coefficient.val hcoefficient
    refine ⟨hcanonical, ?_⟩
    let tailDegree : TailDegree :=
      ⟨coefficient.val - 1, by
        simp only [AspisV5SumcheckCommitment.tailCount]
        omega⟩
    have hdegreeSucc :
        storedDegreeIndex coefficient hcoefficient =
          tailDegree.succ := by
      apply Fin.ext
      simp only [tailDegree, storedDegreeIndex, Fin.val_succ]
      omega
    rw [hdegreeSucc, storedCoefficient_succ]
    unfold maskTails tailDegree
    simp only [roundIndex]
    congr 2
    omega

private theorem wrapping_mul_val_of_lt (left right : Std.Usize)
    (h : left.val * right.val < Usize.size) :
    (left.wrapping_mul right).val = left.val * right.val := by
  simp only [Usize.wrapping_mul_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

private theorem b_block_row_spec
    (round offset : Std.Usize) (hround : round.val < 10)
    (hoffset : offset.val < 28) :
    ∃ row,
      ComponentBGenerated.v5_mask.spend_messages.b_block_row round offset =
        ok row ∧
      row.val = coefficientRow
        (roundIndex round hround, storedDegreeIndex offset hoffset) ∧
      row.val < 1024 := by
  let roundFin : Round := roundIndex round hround
  have hroundFinEq : roundFin = roundIndex round hround := rfl
  have hread := array_index_usize_run
    ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS
    round hround
  let block := ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCKS.val[
    round.val]!
  have hblock : block.val = blockSelector roundFin := by
    exact ComponentBLayoutBindingsProof.generated_round_block_value roundFin
  have hsize : 1025 < Usize.size := by
    simpa using UScalar.hSize (1025#usize)
  have hmulBound : block.val * 32 < Usize.size := by
    have hselector := blockSelector_le_thirty roundFin
    rw [hblock]
    omega
  have hmulRaw := wrapping_mul_val_of_lt block 32#usize (by
    norm_num
    exact hmulBound)
  have hmul : (block.wrapping_mul 32#usize).val = block.val * 32 := by
    simpa using hmulRaw
  have haddBound :
      (block.wrapping_mul 32#usize).val + offset.val < Usize.size := by
    rw [hmul]
    have hselector := blockSelector_le_thirty roundFin
    rw [hblock]
    omega
  have hadd := ComponentBLayoutBindingsProof.wrapping_add_val_of_lt
    (block.wrapping_mul 32#usize) offset haddBound
  let row := (block.wrapping_mul 32#usize).wrapping_add offset
  refine ⟨row, ?_, ?_, ?_⟩
  · unfold ComponentBGenerated.v5_mask.spend_messages.b_block_row
    rw [hread]
    simp only [bind_tc_ok, lift,
      ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_BLOCK_ROWS]
    rfl
  · unfold row
    rw [hadd, hmul, hblock]
    simp only [coefficientRow_val, storedDegreeIndex]
    rw [← hroundFinEq]
    omega
  · unfold row
    rw [hadd, hmul, hblock]
    have hselector := blockSelector_le_thirty roundFin
    omega

private theorem encode_inner_target_spec
    (mask : Mask) (values : Array QM31 1024#usize)
    (round offset target : Std.Usize)
    (hmask : CanonicalMask mask) (hround : round.val < 10)
    (hoffset : offset.val ≤ 28) (htarget : target.val < 28)
    (baseline : ExactQM31)
    (hvalue :
      exactArrayAt values
          (coefficientRow
            (roundIndex round hround,
              storedDegreeIndex target htarget)).val =
        if offset.val ≤ target.val then baseline
        else storedCoefficient (maskTails mask)
          (roundIndex round hround,
            storedDegreeIndex target htarget)) :
    ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0
        mask values round offset ⦃ out =>
      exactArrayAt out
          (coefficientRow
            (roundIndex round hround,
              storedDegreeIndex target htarget)).val =
        storedCoefficient (maskTails mask)
          (roundIndex round hround,
            storedDegreeIndex target htarget) ⦄ := by
  simp only [ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state => 28 - state.2.val)
    (fun state =>
      state.2.val ≤ 28 ∧
      exactArrayAt state.1
          (coefficientRow
            (roundIndex round hround,
              storedDegreeIndex target htarget)).val =
        if state.2.val ≤ target.val then baseline
        else storedCoefficient (maskTails mask)
          (roundIndex round hround,
            storedDegreeIndex target htarget))
    (fun out =>
      exactArrayAt out
          (coefficientRow
            (roundIndex round hround,
              storedDegreeIndex target htarget)).val =
        storedCoefficient (maskTails mask)
          (roundIndex round hround,
            storedDegreeIndex target htarget))
  · rintro ⟨current, currentOffset⟩ ⟨hcurrentOffset, hcurrentValue⟩
    have hcurrentOffset' : currentOffset.val ≤ 28 := by
      simpa only using hcurrentOffset
    have hcurrentValue' :
        exactArrayAt current
            (coefficientRow
              (roundIndex round hround,
                storedDegreeIndex target htarget)).val =
          if currentOffset.val ≤ target.val then baseline
          else storedCoefficient (maskTails mask)
            (roundIndex round hround,
              storedDegreeIndex target htarget) := by
      simpa only using hcurrentValue
    unfold ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0.body
    simp only [ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS]
    by_cases hlt : currentOffset < 28#usize
    · rw [if_pos hlt]
      have hcurrentLt : currentOffset.val < 28 := hlt
      have hcoefficient :=
        extracted_commitment_coefficient_eq_storedCoefficient
          mask round currentOffset hmask hround hcurrentLt
      obtain ⟨coefficient, coefficientRun, coefficientCanonical,
        coefficientExact⟩ := WP.spec_imp_exists hcoefficient
      rw [coefficientRun]
      simp only [bind_tc_ok]
      obtain ⟨row, rowRun, rowExact, rowBound⟩ :=
        b_block_row_spec round currentOffset hround hcurrentLt
      rw [rowRun]
      simp only [bind_tc_ok]
      have hupdate := Array.update_spec current row coefficient (by
        simpa [Array.length_eq] using rowBound)
      obtain ⟨updated, updatedRun, updatedEq⟩ := WP.spec_imp_exists hupdate
      rw [updatedRun]
      simp only [bind_tc_ok, lift]
      subst updated
      have hnext := wrapping_add_one_val currentOffset (by omega)
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · by_cases hsame : target.val = currentOffset.val
        · have hpairs :
              (roundIndex round hround,
                  storedDegreeIndex target htarget) =
                (roundIndex round hround,
                  storedDegreeIndex currentOffset hcurrentLt) := by
            exact Prod.ext (by rfl) (Fin.ext hsame)
          have hrow :
              (coefficientRow
                (roundIndex round hround,
                  storedDegreeIndex target htarget)).val =
                row.val := by
            rw [rowExact]
            exact congrArg Fin.val (congrArg coefficientRow hpairs)
          unfold exactArrayAt
          rw [hrow, ComponentBLayoutBindingsProof.array_set_get_same
            current row coefficient rowBound, coefficientExact]
          rw [if_neg (by rw [hnext, hsame]; omega)]
          rw [hpairs]
        · have hrowNe :
              (coefficientRow
                (roundIndex round hround,
                  storedDegreeIndex target htarget)).val ≠
                row.val := by
            rw [rowExact]
            intro equal
            have pairEqual := coefficientRow_injective (Fin.ext equal)
            exact hsame (congrArg (fun pair => pair.2.val) pairEqual)
          unfold exactArrayAt
          rw [ComponentBLayoutBindingsProof.array_set_get_ne
            current row coefficient _ hrowNe]
          change exactArrayAt current _ = _
          rw [hcurrentValue']
          by_cases hbefore : currentOffset.val < target.val
          · rw [if_pos (by omega), if_pos (by rw [hnext]; omega)]
          · rw [if_neg (by omega), if_neg (by rw [hnext]; omega)]
      · rw [hnext]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta, WP.wp_return]
      have hoffsetEq : currentOffset.val = 28 := by
        have hnot : ¬ currentOffset.val < 28 := by
          intro hsmall
          exact hlt hsmall
        omega
      rw [hcurrentValue', if_neg (by rw [hoffsetEq]; omega)]
  · exact ⟨hoffset, hvalue⟩

private theorem encode_inner_preserve_spec
    (mask : Mask) (values : Array QM31 1024#usize)
    (round offset : Std.Usize) (query : Row)
    (hmask : CanonicalMask mask) (hround : round.val < 10)
    (hoffset : offset.val ≤ 28)
    (hquery : ∀ degree : StoredDegree,
      query ≠ coefficientRow (roundIndex round hround, degree))
    (baseline : ExactQM31)
    (hvalue : exactArrayAt values query.val = baseline) :
    ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0
        mask values round offset ⦃ out =>
      exactArrayAt out query.val = baseline ⦄ := by
  simp only [ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0]
  apply loop.spec_decr_nat
    (fun state => 28 - state.2.val)
    (fun state => state.2.val ≤ 28 ∧
      exactArrayAt state.1 query.val = baseline)
    (fun out => exactArrayAt out query.val = baseline)
  · rintro ⟨current, currentOffset⟩ ⟨hcurrentOffset, hcurrentValue⟩
    have hcurrentOffset' : currentOffset.val ≤ 28 := by
      simpa only using hcurrentOffset
    have hcurrentValue' : exactArrayAt current query.val = baseline := by
      simpa only using hcurrentValue
    unfold ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0.body
    simp only [ComponentBGenerated.v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS]
    by_cases hlt : currentOffset < 28#usize
    · rw [if_pos hlt]
      have hcurrentLt : currentOffset.val < 28 := hlt
      have hcoefficient :=
        extracted_commitment_coefficient_eq_storedCoefficient
          mask round currentOffset hmask hround hcurrentLt
      obtain ⟨coefficient, coefficientRun, _, _⟩ :=
        WP.spec_imp_exists hcoefficient
      rw [coefficientRun]
      simp only [bind_tc_ok]
      obtain ⟨row, rowRun, rowExact, rowBound⟩ :=
        b_block_row_spec round currentOffset hround hcurrentLt
      rw [rowRun]
      simp only [bind_tc_ok]
      have hupdate := Array.update_spec current row coefficient (by
        simpa [Array.length_eq] using rowBound)
      obtain ⟨updated, updatedRun, updatedEq⟩ := WP.spec_imp_exists hupdate
      rw [updatedRun]
      simp only [bind_tc_ok]
      subst updated
      have hnext := wrapping_add_one_val currentOffset (by omega)
      have hrowNe : query.val ≠ row.val := by
        rw [rowExact]
        intro equal
        apply hquery (storedDegreeIndex currentOffset hcurrentLt)
        exact Fin.ext equal
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · unfold exactArrayAt
        rw [ComponentBLayoutBindingsProof.array_set_get_ne
          current row coefficient query.val hrowNe]
        exact hcurrentValue'
      · rw [hnext]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta, WP.wp_return]
      exact hcurrentValue'
  · exact ⟨hoffset, hvalue⟩

private theorem encode_outer_target_spec
    (mask : Mask) (values : Array QM31 1024#usize)
    (currentRound targetRound targetDegree : Std.Usize)
    (hmask : CanonicalMask mask) (hcurrentRound : currentRound.val ≤ 10)
    (htargetRound : targetRound.val < 10)
    (htargetDegree : targetDegree.val < 28)
    (baseline : ExactQM31)
    (hvalue :
      exactArrayAt values
          (coefficientRow
            (roundIndex targetRound htargetRound,
              storedDegreeIndex targetDegree htargetDegree)).val =
        if currentRound.val ≤ targetRound.val then baseline
        else storedCoefficient (maskTails mask)
          (roundIndex targetRound htargetRound,
            storedDegreeIndex targetDegree htargetDegree)) :
    ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0
        mask values currentRound ⦃ out =>
      exactArrayAt out
          (coefficientRow
            (roundIndex targetRound htargetRound,
              storedDegreeIndex targetDegree htargetDegree)).val =
        storedCoefficient (maskTails mask)
          (roundIndex targetRound htargetRound,
            storedDegreeIndex targetDegree htargetDegree) ⦄ := by
  simp only [ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0]
  apply loop.spec_decr_nat
    (fun state => 10 - state.2.val)
    (fun state => state.2.val ≤ 10 ∧
      exactArrayAt state.1
          (coefficientRow
            (roundIndex targetRound htargetRound,
              storedDegreeIndex targetDegree htargetDegree)).val =
        if state.2.val ≤ targetRound.val then baseline
        else storedCoefficient (maskTails mask)
          (roundIndex targetRound htargetRound,
            storedDegreeIndex targetDegree htargetDegree))
    (fun out =>
      exactArrayAt out
          (coefficientRow
            (roundIndex targetRound htargetRound,
              storedDegreeIndex targetDegree htargetDegree)).val =
        storedCoefficient (maskTails mask)
          (roundIndex targetRound htargetRound,
            storedDegreeIndex targetDegree htargetDegree))
  · rintro ⟨current, round⟩ ⟨hroundBound, hcurrentValue⟩
    have hroundBound' : round.val ≤ 10 := by simpa only using hroundBound
    have hcurrentValue' :
        exactArrayAt current
            (coefficientRow
              (roundIndex targetRound htargetRound,
                storedDegreeIndex targetDegree htargetDegree)).val =
          if round.val ≤ targetRound.val then baseline
          else storedCoefficient (maskTails mask)
            (roundIndex targetRound htargetRound,
              storedDegreeIndex targetDegree htargetDegree) := by
      simpa only using hcurrentValue
    unfold ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0.body
    by_cases hlt : round < 10#usize
    · rw [if_pos hlt]
      have hroundLt : round.val < 10 := hlt
      by_cases hsame : round.val = targetRound.val
      · have hroundIndexEq :
            roundIndex round hroundLt =
              roundIndex targetRound htargetRound := by
          apply Fin.ext
          exact hsame
        have hinner := encode_inner_target_spec mask current round 0#usize
          targetDegree hmask hroundLt (by decide) htargetDegree baseline (by
            rw [hroundIndexEq]
            rw [hcurrentValue', if_pos (by omega)]
            rw [if_pos (by norm_num)])
        obtain ⟨updated, updatedRun, updatedValue⟩ := WP.spec_imp_exists hinner
        have updatedValue' :
            exactArrayAt updated
                (coefficientRow
                  (roundIndex targetRound htargetRound,
                    storedDegreeIndex targetDegree htargetDegree)).val =
              storedCoefficient (maskTails mask)
                (roundIndex targetRound htargetRound,
                  storedDegreeIndex targetDegree htargetDegree) := by
          simpa only [hroundIndexEq] using updatedValue
        rw [updatedRun]
        simp only [bind_tc_ok, lift]
        have hnext := wrapping_add_one_val round (by omega)
        simp only [WP.spec, WP.theta]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hnext]
          omega
        · rw [updatedValue', if_neg (by rw [hnext, hsame]; omega)]
        · rw [hnext]
          omega
      · have houtside : ∀ degree : StoredDegree,
            coefficientRow
                (roundIndex targetRound htargetRound,
                  storedDegreeIndex targetDegree htargetDegree) ≠
              coefficientRow (roundIndex round hroundLt, degree) := by
          intro degree equal
          have pairEqual := coefficientRow_injective equal
          apply hsame
          exact congrArg (fun pair => pair.1.val) pairEqual |>.symm
        have hinner := encode_inner_preserve_spec mask current round 0#usize
          (coefficientRow
            (roundIndex targetRound htargetRound,
              storedDegreeIndex targetDegree htargetDegree))
          hmask hroundLt (by decide) houtside _ hcurrentValue'
        obtain ⟨updated, updatedRun, updatedValue⟩ := WP.spec_imp_exists hinner
        rw [updatedRun]
        simp only [bind_tc_ok, lift]
        have hnext := wrapping_add_one_val round (by omega)
        simp only [WP.spec, WP.theta]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hnext]
          omega
        · rw [updatedValue]
          by_cases hbefore : round.val < targetRound.val
          · rw [if_pos (by omega), if_pos (by rw [hnext]; omega)]
          · rw [if_neg (by omega), if_neg (by rw [hnext]; omega)]
        · rw [hnext]
          omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta, WP.wp_return]
      have hroundEq : round.val = 10 := by
        have hnot : ¬ round.val < 10 := by
          intro hsmall
          exact hlt hsmall
        omega
      rw [hcurrentValue', if_neg (by rw [hroundEq]; omega)]
  · exact ⟨hcurrentRound, hvalue⟩

private theorem encode_outer_preserve_spec
    (mask : Mask) (values : Array QM31 1024#usize)
    (currentRound : Std.Usize) (query : Row)
    (hmask : CanonicalMask mask) (hcurrentRound : currentRound.val ≤ 10)
    (hquery : ∀ (round : Round) (degree : StoredDegree),
      query ≠ coefficientRow (round, degree))
    (baseline : ExactQM31)
    (hvalue : exactArrayAt values query.val = baseline) :
    ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0
        mask values currentRound ⦃ out =>
      exactArrayAt out query.val = baseline ⦄ := by
  simp only [ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0]
  apply loop.spec_decr_nat
    (fun state => 10 - state.2.val)
    (fun state => state.2.val ≤ 10 ∧
      exactArrayAt state.1 query.val = baseline)
    (fun out => exactArrayAt out query.val = baseline)
  · rintro ⟨current, round⟩ ⟨hroundBound, hcurrentValue⟩
    have hroundBound' : round.val ≤ 10 := by simpa only using hroundBound
    have hcurrentValue' : exactArrayAt current query.val = baseline := by
      simpa only using hcurrentValue
    unfold ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0.body
    by_cases hlt : round < 10#usize
    · rw [if_pos hlt]
      have hroundLt : round.val < 10 := hlt
      have hinner := encode_inner_preserve_spec mask current round 0#usize query
        hmask hroundLt (by decide)
        (fun degree => hquery (roundIndex round hroundLt) degree)
        baseline hcurrentValue'
      obtain ⟨updated, updatedRun, updatedValue⟩ := WP.spec_imp_exists hinner
      rw [updatedRun]
      simp only [bind_tc_ok, lift]
      have hnext := wrapping_add_one_val round (by omega)
      simp only [WP.spec, WP.theta]
      exact ⟨⟨by rw [hnext]; omega, updatedValue⟩, by rw [hnext]; omega⟩
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta, WP.wp_return]
      exact hcurrentValue'
  · exact ⟨hcurrentRound, hvalue⟩

theorem coefficientRow_outside_pad (index : CoefficientIndex) :
    (coefficientRow index).val < 224 ∨ 479 ≤ (coefficientRow index).val := by
  rcases index with ⟨round, degree⟩
  fin_cases round <;>
    simp only [coefficientRow_val, blockSelector] <;> norm_num <;> omega

private theorem encode_pad_preserve_spec
    (pads : Array QM31 255#usize)
    (values : Array QM31 1024#usize) (offset : Std.Usize)
    (query : Row) (hoffset : offset.val ≤ 255)
    (hquery : query.val < 224 ∨ 479 ≤ query.val)
    (baseline : ExactQM31)
    (hvalue : exactArrayAt values query.val = baseline) :
    ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop1
        pads values offset ⦃ out =>
      exactArrayAt out query.val = baseline ⦄ := by
  simp only [ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop1]
  apply loop.spec_decr_nat
    (fun state => 255 - state.2.val)
    (fun state => state.2.val ≤ 255 ∧
      exactArrayAt state.1 query.val = baseline)
    (fun out => exactArrayAt out query.val = baseline)
  · rintro ⟨current, currentOffset⟩ ⟨hcurrentOffset, hcurrentValue⟩
    have hcurrentOffset' : currentOffset.val ≤ 255 := by
      simpa only using hcurrentOffset
    have hcurrentValue' : exactArrayAt current query.val = baseline := by
      simpa only using hcurrentValue
    unfold ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop1.body
    simp only [ComponentBGenerated.v5_mask.spend_messages.V5_B_PAD_COORDINATES]
    by_cases hlt : currentOffset < 255#usize
    · rw [if_pos hlt]
      have hcurrentLt : currentOffset.val < 255 := hlt
      rw [array_index_usize_run pads currentOffset hcurrentLt]
      simp only [bind_tc_ok, lift,
        ComponentBGenerated.v5_mask.spend_messages.V5_B_PAD_START]
      let row : Std.Usize := Std.Usize.wrapping_add 224#usize currentOffset
      have hsize : 1025 < Usize.size := by
        simpa using UScalar.hSize (1025#usize)
      have hrowVal : row.val = 224 + currentOffset.val := by
        unfold row
        apply ComponentBLayoutBindingsProof.wrapping_add_val_of_lt
        norm_num
        omega
      have hrowBound : row.val < 1024 := by rw [hrowVal]; omega
      have hupdate := Array.update_spec current row
        pads.val[currentOffset.val]! (by
          simpa [Array.length_eq] using hrowBound)
      obtain ⟨updated, updatedRun, updatedEq⟩ := WP.spec_imp_exists hupdate
      rw [updatedRun]
      simp only [bind_tc_ok]
      subst updated
      have hnext := wrapping_add_one_val currentOffset (by omega)
      have hrowNe : query.val ≠ row.val := by
        rw [hrowVal]
        rcases hquery with hlow | hhigh <;> omega
      simp only [WP.spec, WP.theta]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hnext]
        omega
      · unfold exactArrayAt
        change ComponentBRealEvaluatorProof.generatedQm31ToExact
          (current.set row pads.val[currentOffset.val]!).val[query.val]! =
            baseline
        rw [ComponentBLayoutBindingsProof.array_set_get_ne
          current row pads.val[currentOffset.val]! query.val hrowNe]
        exact hcurrentValue'
      · rw [hnext]
        omega
    · rw [if_neg hlt]
      simp only [WP.spec, WP.theta, WP.wp_return]
      exact hcurrentValue'
  · exact ⟨hoffset, hvalue⟩

/-- The three deterministic write phases before the pivot correction preserve
the initial claim and install every maintained stored coefficient exactly.
Pads may be arbitrary: their physical interval is disjoint from terminal
support. -/
theorem extracted_encode_prefix_support
    (mask : Mask) (pads : Array QM31 255#usize)
    (hmask : CanonicalMask mask) :
    ∃ initialized afterCoefficients afterPads,
      Array.update
          (Array.repeat 1024#usize
            ComponentBGenerated.aspis_core.field.QM31.ZERO)
          ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
          mask.initial_claim = ok initialized ∧
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0
          mask initialized 0#usize = ok afterCoefficients ∧
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop1
          pads afterCoefficients 0#usize = ok afterPads ∧
      exactArrayAt afterPads initialRow.val = maskInitial mask ∧
      ∀ index : CoefficientIndex,
        exactArrayAt afterPads (coefficientRow index).val =
          storedCoefficient (maskTails mask) index := by
  let zeroValues := Array.repeat 1024#usize
    ComponentBGenerated.aspis_core.field.QM31.ZERO
  have hinitialBound :
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW.val <
        1024 := by
    norm_num [ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW]
  have hinitialUpdate := Array.update_spec zeroValues
    ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
    mask.initial_claim (by
      simpa [Array.length_eq] using hinitialBound)
  obtain ⟨initialized, initializedRun, initializedEq⟩ :=
    WP.spec_imp_exists hinitialUpdate
  subst initialized
  have hinitialRow :
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW.val =
        initialRow.val := by
    norm_num [ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW,
      initialRow]
  have initializedInitial :
      exactArrayAt
          (zeroValues.set
            ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
            mask.initial_claim) initialRow.val = maskInitial mask := by
    unfold exactArrayAt maskInitial
    rw [← hinitialRow,
      ComponentBLayoutBindingsProof.array_set_get_same zeroValues
        ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
        mask.initial_claim hinitialBound]
  have initializedCoefficient : ∀ index : CoefficientIndex,
      exactArrayAt
          (zeroValues.set
            ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
            mask.initial_claim) (coefficientRow index).val = 0 := by
    intro index
    have hne : (coefficientRow index).val ≠
        ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW.val := by
      rw [hinitialRow]
      intro equal
      exact coefficientRow_ne_initial index (Fin.ext equal)
    unfold exactArrayAt zeroValues
    rw [ComponentBLayoutBindingsProof.array_set_get_ne _ _ _ _ hne]
    rw [ComponentBLayoutBindingsProof.array_repeat_get_bang 1024#usize
      ComponentBGenerated.aspis_core.field.QM31.ZERO
      (coefficientRow index).val (coefficientRow index).isLt]
    exact ComponentBLayoutBindingsProof.generated_ZERO_exact
  have houterInitial := encode_outer_preserve_spec mask
    (zeroValues.set
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
      mask.initial_claim) 0#usize initialRow hmask (by decide)
    (fun round degree => (coefficientRow_ne_initial (round, degree)).symm)
    (maskInitial mask) initializedInitial
  obtain ⟨afterCoefficients, outerRun, afterCoefficientsInitial⟩ :=
    WP.spec_imp_exists houterInitial
  have afterCoefficientsCoefficient : ∀ index : CoefficientIndex,
      exactArrayAt afterCoefficients (coefficientRow index).val =
        storedCoefficient (maskTails mask) index := by
    intro index
    rcases index with ⟨round, degree⟩
    have htarget := encode_outer_target_spec mask
      (zeroValues.set
        ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
        mask.initial_claim)
      0#usize (roundUsize round) (storedDegreeUsize degree)
      hmask (by decide) (by
        have h := round.isLt
        rw [roundUsize_val]
        simpa only [AspisV5SumcheckCommitment.roundCount] using h)
      (by exact degree.isLt) 0 (by
        rw [roundIndex_roundUsize, storedDegreeIndex_storedDegreeUsize]
        rw [if_pos (by norm_num)]
        exact initializedCoefficient (round, degree))
    obtain ⟨candidate, candidateRun, candidateValue⟩ :=
      WP.spec_imp_exists htarget
    have hc : candidate = afterCoefficients :=
      Result.ok.inj (candidateRun.symm.trans outerRun)
    subst candidate
    simpa [roundIndex_roundUsize,
      storedDegreeIndex_storedDegreeUsize] using candidateValue
  have hpadInitial := encode_pad_preserve_spec pads afterCoefficients 0#usize
    initialRow (by decide) (Or.inr (by norm_num [initialRow]))
    (maskInitial mask) afterCoefficientsInitial
  obtain ⟨afterPads, padRun, afterPadsInitial⟩ :=
    WP.spec_imp_exists hpadInitial
  have afterPadsCoefficient : ∀ index : CoefficientIndex,
      exactArrayAt afterPads (coefficientRow index).val =
        storedCoefficient (maskTails mask) index := by
    intro index
    have hpad := encode_pad_preserve_spec pads afterCoefficients 0#usize
      (coefficientRow index) (by decide) (coefficientRow_outside_pad index)
      (storedCoefficient (maskTails mask) index)
      (afterCoefficientsCoefficient index)
    obtain ⟨candidate, candidateRun, candidateValue⟩ :=
      WP.spec_imp_exists hpad
    have hc : candidate = afterPads :=
      Result.ok.inj (candidateRun.symm.trans padRun)
    simpa only [hc] using candidateValue
  exact ⟨zeroValues.set
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
      mask.initial_claim,
    afterCoefficients, afterPads,
    initializedRun, outerRun, padRun, afterPadsInitial,
    afterPadsCoefficient⟩

private theorem encode_success_values_eq_pivot_update
    (mask : Mask) (pads : Array QM31 255#usize) (pivotPad : QM31)
    (initialized afterCoefficients afterPads : Array QM31 1024#usize)
    (lane : ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane)
    (initializedRun :
      Array.update
          (Array.repeat 1024#usize
            ComponentBGenerated.aspis_core.field.QM31.ZERO)
          ComponentBGenerated.v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
          mask.initial_claim = ok initialized)
    (outerRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop0
        mask initialized 0#usize = ok afterCoefficients)
    (padRun :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode_loop1
        pads afterCoefficients 0#usize = ok afterPads)
    (run :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = ok (.Ok lane)) :
    ∃ pivotValue,
      lane.values = afterPads.set
        ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW
        pivotValue := by
  unfold ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode at run
  generalize hinactive :
      ComponentBGenerated.v5_mask.spend_messages.atomic_inactive
        ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW =
          inactiveResult at run
  cases inactiveResult with
  | fail error => simp at run
  | div => simp at run
  | ok inactive =>
    cases inactive with
    | false => simp at run
    | true =>
      simp only [bind_tc_ok, if_true,
        ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.impl.initial_claim]
        at run
      rw [initializedRun] at run
      simp only [bind_tc_ok] at run
      rw [outerRun] at run
      simp only [bind_tc_ok] at run
      rw [padRun] at run
      simp only [bind_tc_ok, lift] at run
      generalize hsum :
          ComponentBGenerated.v5_mask.spend_messages.atomic_inactive_sum_qm31
            (Array.to_slice afterPads) = firstSum at run
      cases firstSum with
      | fail error => simp at run
      | div => simp at run
      | ok firstOption =>
        cases firstOption with
        | none =>
          simp at run
        | some inactiveWithoutPivot =>
          simp only [bind_tc_ok] at run
          generalize hneg :
              ComponentBGenerated.aspis_core.field.QM31.neg
                inactiveWithoutPivot = negativeResult at run
          cases negativeResult with
          | fail error => simp at run
          | div => simp at run
          | ok negative =>
            simp only [bind_tc_ok] at run
            generalize hadd :
                ComponentBGenerated.aspis_core.field.QM31.add pivotPad negative =
                  addResult at run
            cases addResult with
            | fail error => simp at run
            | div => simp at run
            | ok pivotValue =>
              simp only [bind_tc_ok] at run
              have hupdate := Array.update_spec afterPads
                ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW
                pivotValue (by
                  norm_num [Array.length_eq,
                    ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW])
              obtain ⟨updated, updatedRun, updatedEq⟩ :=
                WP.spec_imp_exists hupdate
              rw [updatedRun] at run
              subst updated
              simp only [bind_tc_ok] at run
              generalize hsum2 :
                  ComponentBGenerated.v5_mask.spend_messages.atomic_inactive_sum_qm31
                    (Array.to_slice
                      (afterPads.set
                        ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW
                        pivotValue)) = secondSum at run
              cases secondSum with
              | fail error => simp at run
              | div => simp at run
              | ok secondOption =>
                cases secondOption with
                | none => simp at run
                | some total =>
                  simp only [bind_tc_ok] at run
                  generalize heq :
                      ComponentBGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
                        total pivotPad = eqResult at run
                  cases eqResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok equal =>
                    cases equal with
                    | false => simp at run
                    | true =>
                      simp only [bind_tc_ok, if_true, Result.ok.injEq,
                        core.result.Result.Ok.injEq] at run
                      subst lane
                      exact ⟨pivotValue, rfl⟩

/-- Every successful source-authentic encoder run preserves the maintained
terminal support.  The pivot correction may change row 993, but that row is
disjoint from both the initial claim and all 280 stored coefficients. -/
theorem extracted_encode_success_terminal_support
    (mask : Mask) (pads : Array QM31 255#usize) (pivotPad : QM31)
    (lane : ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane)
    (hmask : CanonicalMask mask)
    (run :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = ok (.Ok lane)) :
    exactArrayAt lane.values initialRow.val = maskInitial mask ∧
      ∀ index : CoefficientIndex,
        exactArrayAt lane.values (coefficientRow index).val =
          storedCoefficient (maskTails mask) index := by
  obtain ⟨initialized, afterCoefficients, afterPads, initializedRun,
    outerRun, padRun, hinitial, hcoefficients⟩ :=
      extracted_encode_prefix_support mask pads hmask
  obtain ⟨pivotValue, hlane⟩ := encode_success_values_eq_pivot_update
    mask pads pivotPad initialized afterCoefficients afterPads lane
    initializedRun outerRun padRun run
  rw [hlane]
  constructor
  · unfold exactArrayAt
    rw [ComponentBLayoutBindingsProof.array_set_get_ne
      afterPads
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW
      pivotValue initialRow.val (by
        norm_num [initialRow,
          ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW])]
    exact hinitial
  · intro index
    unfold exactArrayAt
    rw [ComponentBLayoutBindingsProof.array_set_get_ne
      afterPads
      ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW
      pivotValue (coefficientRow index).val (by
        have hlt := coefficientRow_lt_initial index
        norm_num [initialRow,
          ComponentBGenerated.v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW]
          at hlt ⊢
        omega)]
    exact hcoefficients index

/-- The authentic encoded lane and the maintained sparse `rowMessage` agree
after applying the deployed terminal covector.  This is intentionally a
weighted equality: arbitrary pad coordinates and the inactive pivot may
differ outside terminal support. -/
theorem extracted_component_b_encode_weighted_rowMessage
    (point : Round → ExactQM31)
    (mask : Mask) (pads : Array QM31 255#usize) (pivotPad : QM31)
    (lane : ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane)
    (hmask : CanonicalMask mask)
    (run :
      ComponentBGenerated.v5_mask.spend_messages.V5StructuredBLane.encode
        mask pads pivotPad = ok (.Ok lane))
    (row : Row) :
    terminalWeights point 1 row * exactArrayAt lane.values row.val =
      terminalWeights point 1 row *
        rowMessage (maskInitial mask) (maskTails mask) row := by
  obtain ⟨hinitialValue, hcoefficientValue⟩ :=
    extracted_encode_success_terminal_support mask pads pivotPad lane hmask run
  by_cases hinitial : row = initialRow
  · subst row
    rw [hinitialValue, rowMessage_at_initial]
  · by_cases hcoefficient : ∃ index : CoefficientIndex,
        row = coefficientRow index
    · obtain ⟨index, hrow⟩ := hcoefficient
      subst row
      rw [hcoefficientValue index, rowMessage_at_coefficient]
    · have houtside : ∀ index : CoefficientIndex,
          row ≠ coefficientRow index := by
        intro index equal
        exact hcoefficient ⟨index, equal⟩
      have hzero : terminalWeights point 1 row = 0 :=
        ComponentBLayoutBindingsProof.terminalWeights_eq_zero_of_outside
          point row hinitial houtside
      calc
        terminalWeights point 1 row * exactArrayAt lane.values row.val =
            0 * exactArrayAt lane.values row.val :=
          congrArg (fun weight => weight * exactArrayAt lane.values row.val) hzero
        _ = 0 := zero_mul _
        _ = 0 * rowMessage (maskInitial mask) (maskTails mask) row :=
          (zero_mul _).symm
        _ = terminalWeights point 1 row *
            rowMessage (maskInitial mask) (maskTails mask) row :=
          congrArg
            (fun weight => weight *
              rowMessage (maskInitial mask) (maskTails mask) row)
            hzero.symm
