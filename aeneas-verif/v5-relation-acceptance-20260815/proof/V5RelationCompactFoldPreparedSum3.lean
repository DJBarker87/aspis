import V5RelationCompactFoldPreparedSum
import SumProductsFullCorrespondence

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8000

/-!
# Exact semantics of the production prepared three-product sum

The production FRI fold uses the same fixed three-by-three Karatsuba channel
accumulator as the independently proved generic small-product helper.  Its
left channel matrix has simply been cached in a
`PreparedQm31Multiplier`.  This file identifies the generated loops and then
reuses their already proved no-overflow and reconstruction arithmetic.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace AspisV5RelationCompactFoldPreparedSum3

open AspisV5RelationCompactFoldFieldProjection
open AspisV5RelationCompactFoldPreparedSum

namespace Fresh
abbrev M31 := V5RelationCompactFoldGenerated.aspis_core.field.M31
abbrev CM31 := V5RelationCompactFoldGenerated.aspis_core.field.CM31
abbrev QM31 := V5RelationCompactFoldGenerated.aspis_core.field.QM31
abbrev Prepared :=
  V5RelationCompactFoldGenerated.aspis_core.field.PreparedQm31Multiplier

end Fresh

abbrev ExactM31 := ComponentBRealEvaluatorProof.ExactM31
abbrev ExactCM31 := AspisV5ComponentCQM31TowerExact.CM31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def canonicalM31 (value : Fresh.M31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val

def canonicalCM31 (value : Fresh.CM31) : Prop :=
  AspisV5RelationCompactFoldFieldProjection.CanonicalCM31 value

def canonicalQM31 (value : Fresh.QM31) : Prop :=
  AspisV5RelationCompactFoldFieldProjection.CanonicalQM31 value

def cm31View (value : Fresh.CM31) : ExactCM31 := rawCM31ToExact value

def qm31View (value : Fresh.QM31) : ExactQM31 := toMaintainedExact value

instance : Inhabited Fresh.CM31 := ⟨⟨0#u32, 0#u32⟩⟩
instance : Inhabited Fresh.QM31 := ⟨⟨default, default⟩⟩
instance : Inhabited Fresh.Prepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩

private theorem prepared_channel_body_eq_existing
    (left : Array Fresh.Prepared 3#usize) (index : Std.Usize)
    (prepared : Fresh.Prepared)
    (hprepared : Array.index_usize left index = ok prepared)
    (rightComponents : Array (Array Fresh.M31 3#usize) 3#usize)
    (component : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body
        left index rightComponents component iter sums =
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0.body
        prepared.components rightComponents component iter sums := by
  unfold
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0.body
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0.body
  generalize hnext :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp
  | div => simp
  | ok pair =>
    rcases pair with ⟨slot, iterNext⟩
    cases slot <;> simp [hprepared]

private theorem prepared_channel_loop_eq_existing
    (left : Array Fresh.Prepared 3#usize) (index : Std.Usize)
    (prepared : Fresh.Prepared)
    (hprepared : Array.index_usize left index = ok prepared)
    (rightComponents : Array (Array Fresh.M31 3#usize) 3#usize)
    (component : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0
        iter left sums index rightComponents component =
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0
        iter sums prepared.components rightComponents component := by
  unfold
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0_loop0
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0_loop0
  apply congrArg (fun body => loop body (iter, sums))
  funext state
  rcases state with ⟨iterState, sumsState⟩
  exact prepared_channel_body_eq_existing left index prepared hprepared
    rightComponents component iterState sumsState

private theorem prepared_component_body_eq_existing
    (left : Array Fresh.Prepared 3#usize) (index : Std.Usize)
    (prepared : Fresh.Prepared)
    (hprepared : Array.index_usize left index = ok prepared)
    (rightComponents : Array (Array Fresh.M31 3#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body
        left index rightComponents iter sums =
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0.body
        prepared.components rightComponents iter sums := by
  unfold
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0.body
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0.body
  generalize hnext :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = next
  cases next with
  | fail error => simp
  | div => simp
  | ok pair =>
    rcases pair with ⟨slot, iterNext⟩
    cases slot with
    | none => simp
    | some component =>
      simp only [bind_tc_ok]
      rw [prepared_channel_loop_eq_existing left index prepared hprepared
        rightComponents component
        { start := 0#usize, «end» := 3#usize } sums]

private theorem prepared_component_loop_eq_existing
    (left : Array Fresh.Prepared 3#usize) (index : Std.Usize)
    (prepared : Fresh.Prepared)
    (hprepared : Array.index_usize left index = ok prepared)
    (rightComponents : Array (Array Fresh.M31 3#usize) 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
        iter left sums index rightComponents =
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0
        iter sums prepared.components rightComponents := by
  unfold
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels_loop0
  apply congrArg (fun body => loop body (iter, sums))
  funext state
  rcases state with ⟨iterState, sumsState⟩
  exact prepared_component_body_eq_existing left index prepared hprepared
    rightComponents iterState sumsState

/-- A cached-left production accumulation has exactly the already proved
nine-channel postcondition.  This is a theorem about the generated prepared
loop, not an assumed helper result. -/
theorem prepared_component_loop_corresponds
    (left : Array Fresh.Prepared 3#usize) (index : Std.Usize)
    (prepared : Fresh.Prepared)
    (hprepared : Array.index_usize left index = ok prepared)
    (rightComponents : Array (Array Fresh.M31 3#usize) 3#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (AspisLane5QM31SumProductsProof.matrixCell sums row channel).val +
        (AspisLane5QM31SumProductsProof.channelM31 prepared.components
          row channel).val *
        (AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val <
        AspisLane5QM31SumProductsProof.u64Cardinality) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left sums index
        rightComponents
      ⦃ out => AspisLane5QM31SumProductsProof.ComponentUpdateInvariant
        sums out prepared.components rightComponents 3 ⦄ := by
  rw [prepared_component_loop_eq_existing left index prepared hprepared]
  exact AspisLane5QM31SumProductsProof.generated_component_loop_corresponds
    sums prepared.components rightComponents hNoOverflow

def exactCMChannel (x : ExactCM31) (channel : Nat) : ExactM31 :=
  if channel = 0 then x.re else if channel = 1 then x.im else x.re + x.im

def exactQMComponent (x : ExactQM31) (component : Nat) : ExactCM31 :=
  if component = 0 then x.re else if component = 1 then x.im else x.re + x.im

def exactInputChannel (x : ExactQM31) (component channel : Nat) : ExactM31 :=
  exactCMChannel (exactQMComponent x component) channel

def PreparedRepresents (prepared : Fresh.Prepared) (value : ExactQM31) : Prop :=
  ∀ component, component < 3 → ∀ channel, channel < 3 →
    canonicalM31
      (AspisLane5QM31SumProductsProof.channelM31 prepared.components
        component channel) ∧
    (((AspisLane5QM31SumProductsProof.channelM31 prepared.components
        component channel).val : Nat) : ExactM31) =
      exactInputChannel value component channel

def preparedComponentMatrix
    (q : Fresh.QM31) (qsum : Fresh.CM31) (m0 m1 m2 : Fresh.M31) :
    Array (Array Fresh.M31 3#usize) 3#usize :=
  Array.make 3#usize [
    Array.make 3#usize [q.c0.a, q.c0.b, m0],
    Array.make 3#usize [q.c1.a, q.c1.b, m1],
    Array.make 3#usize [qsum.a, qsum.b, m2]
  ]

private theorem prepared_component_matrix_canonical
    (q : Fresh.QM31) (qsum : Fresh.CM31) (m0 m1 m2 : Fresh.M31)
    (hq : canonicalQM31 q) (hqsum : canonicalCM31 qsum)
    (hm0 : canonicalM31 m0) (hm1 : canonicalM31 m1)
    (hm2 : canonicalM31 m2) :
    AspisLane5QM31SumProductsProof.CanonicalChannelMatrix
      (preparedComponentMatrix q qsum m0 m1 m2) := by
  rcases hq with ⟨⟨hc0a, hc0b⟩, ⟨hc1a, hc1b⟩⟩
  rcases hqsum with ⟨hsuma, hsumb⟩
  intro component hComponent channel hChannel
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals
    simp only [AspisLane5QM31SumProductsProof.channelM31,
      preparedComponentMatrix, Aeneas.Std.Array.make]
  all_goals assumption

private theorem prepared_component_matrix_exact
    (q : Fresh.QM31) (qsum : Fresh.CM31) (m0 m1 m2 : Fresh.M31)
    (hqsum : cm31View qsum = cm31View q.c0 + cm31View q.c1)
    (hm0 : ((m0.val : Nat) : ExactM31) =
      (q.c0.a.val : ExactM31) + (q.c0.b.val : ExactM31))
    (hm1 : ((m1.val : Nat) : ExactM31) =
      (q.c1.a.val : ExactM31) + (q.c1.b.val : ExactM31))
    (hm2 : ((m2.val : Nat) : ExactM31) =
      (qsum.a.val : ExactM31) + (qsum.b.val : ExactM31)) :
    ∀ component, component < 3 → ∀ channel, channel < 3 →
      (((AspisLane5QM31SumProductsProof.channelM31
        (preparedComponentMatrix q qsum m0 m1 m2)
        component channel).val : Nat) : ExactM31) =
          exactInputChannel (qm31View q) component channel := by
  intro component hComponent channel hChannel
  have hqsumRe := congrArg (fun x : ExactCM31 => x.re) hqsum
  have hqsumIm := congrArg (fun x : ExactCM31 => x.im) hqsum
  change ((qsum.a.val : Nat) : ExactM31) =
    (q.c0.a.val : ExactM31) + (q.c1.a.val : ExactM31) at hqsumRe
  change ((qsum.b.val : Nat) : ExactM31) =
    (q.c0.b.val : ExactM31) + (q.c1.b.val : ExactM31) at hqsumIm
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals
    simp only [AspisLane5QM31SumProductsProof.channelM31,
      preparedComponentMatrix, Aeneas.Std.Array.make]
  all_goals
    simp [exactInputChannel, exactQMComponent, exactCMChannel,
      qm31View, cm31View,
      AspisV5RelationCompactFoldFieldProjection.toMaintainedExact]
      at hqsum ⊢
  all_goals try exact hm0
  all_goals try exact hm1
  all_goals try rw [hm2]
  all_goals try rw [hqsumRe]
  all_goals try rw [hqsumIm]

def CanonicalQM31Array3 (values : Array Fresh.QM31 3#usize) : Prop :=
  ∀ index, index < 3 → canonicalQM31 values.val[index]!

def PreparedArrayRepresents
    (prepared : Array Fresh.Prepared 3#usize)
    (values : Nat → ExactQM31) : Prop :=
  ∀ index, index < 3 → PreparedRepresents prepared.val[index]! (values index)

def exactPreparedChannelDot
    (leftValues : Nat → ExactQM31)
    (right : Array Fresh.QM31 3#usize)
    (processed row channel : Nat) : ExactM31 :=
  ∑ index ∈ Finset.range processed,
    exactInputChannel (leftValues index) row channel *
      exactInputChannel (qm31View right.val[index]!) row channel

def PreparedOuterInvariant
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (leftValues : Nat → ExactQM31)
    (right : Array Fresh.QM31 3#usize)
    (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (AspisLane5QM31SumProductsProof.matrixCell current row channel).val ≤
        processed * AspisLane5QM31SumProductsProof.channelProductBound ∧
    (((AspisLane5QM31SumProductsProof.matrixCell current row channel).val : Nat) :
        ExactM31) =
      exactPreparedChannelDot leftValues right processed row channel

private theorem list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

theorem generated_array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := list_get_eq_getElemBang values.val index.val hArrayBound
  simpa [hValue, hElem] using hRun

private theorem prepared_outer_body_active
    (left : Array Fresh.Prepared 3#usize)
    (right : Array Fresh.QM31 3#usize)
    (leftValues : Nat → ExactQM31)
    (iter : core.ops.range.Range Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (hActive : iter.start.val < iter.end.val)
    (hEnd : iter.end.val = 3)
    (hLeft : PreparedArrayRepresents left leftValues)
    (hRight : CanonicalQM31Array3 right)
    (hInvariant : PreparedOuterInvariant current leftValues right
      iter.start.val) :
    ∃ iter' out,
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0.body
          left right iter current = ok (cont (iter', out)) ∧
      iter'.start.val = iter.start.val + 1 ∧
      iter'.end.val = iter.end.val ∧
      PreparedOuterInvariant out leftValues right (iter.start.val + 1) := by
  unfold PreparedArrayRepresents at hLeft
  unfold CanonicalQM31Array3 at hRight
  have hNextSpec :=
    core.iter.range.IteratorRange.next_Usize_some_spec iter hActive
  obtain ⟨⟨option, iter'⟩, hNext, hOption, hNextStart, hNextEnd⟩ :=
    Aeneas.Std.WP.spec_imp_exists hNextSpec
  rw [hOption] at hNext
  have hIndex : iter.start.val < 3 := by omega
  let prepared : Fresh.Prepared := left.val[iter.start.val]!
  let q : Fresh.QM31 := right.val[iter.start.val]!
  have hPreparedIndex := generated_array_index_run left iter.start hIndex
  have hRightIndex := generated_array_index_run right iter.start hIndex
  have hPrepared : PreparedRepresents prepared (leftValues iter.start.val) :=
    hLeft iter.start.val hIndex
  have hq : canonicalQM31 q := hRight iter.start.val hIndex
  rcases generated_cm31_add_corresponds q.c0 q.c1 hq.1 hq.2 with
    ⟨rightSum, hRightSum, hRightSumCanonical, hRightSumExact⟩
  rcases generated_m31_add_corresponds q.c0.a q.c0.b hq.1.1 hq.1.2 with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases generated_m31_add_corresponds q.c1.a q.c1.b hq.2.1 hq.2.2 with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases generated_m31_add_corresponds rightSum.a rightSum.b
      hRightSumCanonical.1 hRightSumCanonical.2 with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  let rightComponents := preparedComponentMatrix q rightSum m0 m1 m2
  have hRightComponentsCanonical :
      AspisLane5QM31SumProductsProof.CanonicalChannelMatrix rightComponents :=
    prepared_component_matrix_canonical q rightSum m0 m1 m2 hq
      hRightSumCanonical hm0Canonical hm1Canonical hm2Canonical
  have hRightComponentsExact := prepared_component_matrix_exact q rightSum
    m0 m1 m2 hRightSumExact hm0Exact hm1Exact hm2Exact
  have hNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (AspisLane5QM31SumProductsProof.matrixCell current row channel).val +
        (AspisLane5QM31SumProductsProof.channelM31 prepared.components
          row channel).val *
        (AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val <
        AspisLane5QM31SumProductsProof.u64Cardinality := by
    intro row hRow channel hChannel
    have hCurrent := (hInvariant row hRow channel hChannel).1
    have hLeftCanonical := (hPrepared row hRow channel hChannel).1
    have hRightCanonical :=
      hRightComponentsCanonical row hRow channel hChannel
    change (AspisLane5QM31SumProductsProof.channelM31 prepared.components
      row channel).val < AspisLane5QM31SumProductsProof.m31Modulus at hLeftCanonical
    change (AspisLane5QM31SumProductsProof.channelM31 rightComponents
      row channel).val < AspisLane5QM31SumProductsProof.m31Modulus at hRightCanonical
    have hLeftLe :
        (AspisLane5QM31SumProductsProof.channelM31 prepared.components
          row channel).val ≤
          AspisLane5QM31SumProductsProof.m31Modulus - 1 := by omega
    have hRightLe :
        (AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val ≤
          AspisLane5QM31SumProductsProof.m31Modulus - 1 := by omega
    have hProduct :
        (AspisLane5QM31SumProductsProof.channelM31 prepared.components
          row channel).val *
        (AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val ≤
          AspisLane5QM31SumProductsProof.channelProductBound := by
      unfold AspisLane5QM31SumProductsProof.channelProductBound
      simpa [pow_two] using Nat.mul_le_mul hLeftLe hRightLe
    calc
      (AspisLane5QM31SumProductsProof.matrixCell current row channel).val +
          (AspisLane5QM31SumProductsProof.channelM31 prepared.components
            row channel).val *
          (AspisLane5QM31SumProductsProof.channelM31 rightComponents
            row channel).val
          ≤ iter.start.val *
              AspisLane5QM31SumProductsProof.channelProductBound +
              AspisLane5QM31SumProductsProof.channelProductBound :=
            le_trans (Nat.add_le_add hCurrent hProduct) (le_refl _)
      _ = (iter.start.val + 1) *
          AspisLane5QM31SumProductsProof.channelProductBound := by ring
      _ ≤ 4 * AspisLane5QM31SumProductsProof.channelProductBound := by
        apply Nat.mul_le_mul_right
        omega
      _ < AspisLane5QM31SumProductsProof.u64Cardinality :=
        AspisLane5QM31SumProductsProof.four_channel_products_fit_u64
  have hComponentSpec := prepared_component_loop_corresponds left iter.start
    prepared hPreparedIndex rightComponents current hNoOverflow
  obtain ⟨out, hComponentRun, hComponentPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists hComponentSpec
  have hOutInvariant :
      PreparedOuterInvariant out leftValues right (iter.start.val + 1) := by
    intro row hRow channel hChannel
    have hOld := hInvariant row hRow channel hChannel
    have hStep := hComponentPost row hRow channel hChannel
    simp only [show row < 3 from hRow, if_pos] at hStep
    have hLeftExact := (hPrepared row hRow channel hChannel).2
    have hRightExact :=
      hRightComponentsExact row hRow channel hChannel
    have hRightExact' :
        (((AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val : Nat) : ExactM31) =
          exactInputChannel (qm31View right.val[iter.start.val]!)
            row channel := by
      simpa [q, rightComponents] using hRightExact
    have hLeftCanonical := (hPrepared row hRow channel hChannel).1
    have hRightCanonical :=
      hRightComponentsCanonical row hRow channel hChannel
    change (AspisLane5QM31SumProductsProof.channelM31 prepared.components
      row channel).val < AspisLane5QM31SumProductsProof.m31Modulus at hLeftCanonical
    change (AspisLane5QM31SumProductsProof.channelM31 rightComponents
      row channel).val < AspisLane5QM31SumProductsProof.m31Modulus at hRightCanonical
    have hLeftLe :
        (AspisLane5QM31SumProductsProof.channelM31 prepared.components
          row channel).val ≤
          AspisLane5QM31SumProductsProof.m31Modulus - 1 := by omega
    have hRightLe :
        (AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val ≤
          AspisLane5QM31SumProductsProof.m31Modulus - 1 := by omega
    have hProduct :
        (AspisLane5QM31SumProductsProof.channelM31 prepared.components
          row channel).val *
        (AspisLane5QM31SumProductsProof.channelM31 rightComponents
          row channel).val ≤
          AspisLane5QM31SumProductsProof.channelProductBound := by
      unfold AspisLane5QM31SumProductsProof.channelProductBound
      simpa [pow_two] using Nat.mul_le_mul hLeftLe hRightLe
    constructor
    · rw [hStep]
      calc
        (AspisLane5QM31SumProductsProof.matrixCell current row channel).val +
            (AspisLane5QM31SumProductsProof.channelM31 prepared.components
              row channel).val *
            (AspisLane5QM31SumProductsProof.channelM31 rightComponents
              row channel).val
            ≤ iter.start.val *
                AspisLane5QM31SumProductsProof.channelProductBound +
                AspisLane5QM31SumProductsProof.channelProductBound :=
              Nat.add_le_add hOld.1 hProduct
        _ = (iter.start.val + 1) *
            AspisLane5QM31SumProductsProof.channelProductBound := by ring
    · rw [hStep, Nat.cast_add, Nat.cast_mul, hLeftExact, hRightExact',
        hOld.2]
      simp [exactPreparedChannelDot, Finset.sum_range_succ]
  refine ⟨iter', out, ?_, hNextStart, congrArg UScalar.val hNextEnd,
    hOutInvariant⟩
  unfold V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0.body
  rw [hNext]
  simp only [bind_tc_ok]
  rw [hRightIndex]
  simp only [bind_tc_ok]
  rw [hRightSum]
  simp only [bind_tc_ok]
  rw [hm0]
  simp only [bind_tc_ok]
  rw [hm1]
  simp only [bind_tc_ok]
  rw [hm2]
  simp only [bind_tc_ok]
  change
    (do
      let sums1 ←
        V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0_loop0
          { start := 0#usize, «end» := 3#usize } left current iter.start
          rightComponents
      ok (cont (iter', sums1))) = ok (cont (iter', out))
  rw [hComponentRun]
  simp only [bind_tc_ok]

private theorem prepared_outer_body_done
    (left : Array Fresh.Prepared 3#usize)
    (right : Array Fresh.QM31 3#usize)
    (iter : core.ops.range.Range Std.Usize)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (hDone : ¬ iter.start.val < iter.end.val) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0.body
        left right iter current = ok (done current) := by
  have hNextSpec := core.iter.range.IteratorRange.next_Usize_none_spec iter
    (by omega)
  obtain ⟨⟨option, iter'⟩, hNext, hOption, hIter⟩ :=
    Aeneas.Std.WP.spec_imp_exists hNextSpec
  rw [hOption, hIter] at hNext
  unfold V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0.body
  rw [hNext]
  simp only [bind_tc_ok]

/-- The extracted fixed three-product outer loop accumulates the exact nine
Karatsuba channels represented by its prepared left inputs. -/
theorem prepared_outer_loop_corresponds
    (left : Array Fresh.Prepared 3#usize)
    (right : Array Fresh.QM31 3#usize)
    (leftValues : Nat → ExactQM31)
    (initial : Array (Array Std.U64 3#usize) 3#usize)
    (hLeft : PreparedArrayRepresents left leftValues)
    (hRight : CanonicalQM31Array3 right)
    (hInitial : PreparedOuterInvariant initial leftValues right 0) :
    V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0
        { start := 0#usize, «end» := 3#usize } left right initial
      ⦃ out => PreparedOuterInvariant out leftValues right 3 ⦄ := by
  simp only [V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0]
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize ×
      Array (Array Std.U64 3#usize) 3#usize => 3 - state.1.start.val)
    (fun state => state.1.end.val = 3 ∧ state.1.start.val ≤ 3 ∧
      PreparedOuterInvariant state.2 leftValues right state.1.start.val)
    (fun out => PreparedOuterInvariant out leftValues right 3)
  · rintro ⟨iter, current⟩ ⟨hEnd, hStart, hInvariant⟩
    dsimp only at hEnd hStart hInvariant ⊢
    by_cases hActive : iter.start.val < iter.end.val
    · obtain ⟨iter', out, hBody, hNextStart, hNextEnd, hOut⟩ :=
        prepared_outer_body_active left right leftValues iter current hActive
          hEnd hLeft hRight hInvariant
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hNextEnd]
        exact hEnd
      · rw [hNextStart]
        omega
      · rw [hNextStart]
        exact hOut
      · rw [hNextStart]
        omega
    · have hAtEnd : iter.start.val = 3 := by omega
      rw [prepared_outer_body_done left right iter current hActive]
      simpa [hAtEnd] using hInvariant
  · exact ⟨by norm_num, by norm_num, hInitial⟩

def reconstructCMExact (row : Array Std.U64 3#usize) : ExactCM31 :=
  ⟨(((AspisLane5QM31SumProductsProof.rowCell row 0).val : Nat) : ExactM31) -
      ((AspisLane5QM31SumProductsProof.rowCell row 1).val : ExactM31),
    (((AspisLane5QM31SumProductsProof.rowCell row 2).val : Nat) : ExactM31) -
      ((AspisLane5QM31SumProductsProof.rowCell row 0).val : ExactM31) -
      ((AspisLane5QM31SumProductsProof.rowCell row 1).val : ExactM31)⟩

def reconstructQMExact
    (sums : Array (Array Std.U64 3#usize) 3#usize) : ExactQM31 :=
  let m0 := reconstructCMExact sums.val[(0#usize).val]!
  let m1 := reconstructCMExact sums.val[(1#usize).val]!
  let m2 := reconstructCMExact sums.val[(2#usize).val]!
  ⟨m0 + AspisV5ComponentCQM31TowerExact.qm31R * m1,
    m2 - m0 - m1⟩

private theorem reconstruct_closure_corresponds
    (channels : Array Std.U64 3#usize) :
    ∃ out : Fresh.CM31,
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
          () channels = ok out ∧
      canonicalCM31 out ∧
      cm31View out = reconstructCMExact channels := by
  have h0 := generated_array_index_run channels 0#usize (by norm_num)
  have h1 := generated_array_index_run channels 1#usize (by norm_num)
  have h2 := generated_array_index_run channels 2#usize (by norm_num)
  rcases generated_m31_reduce_u64_corresponds
      (AspisLane5QM31SumProductsProof.rowCell channels 0) with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases generated_m31_reduce_u64_corresponds
      (AspisLane5QM31SumProductsProof.rowCell channels 1) with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases generated_m31_reduce_u64_corresponds
      (AspisLane5QM31SumProductsProof.rowCell channels 2) with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  rcases generated_m31_sub_corresponds m0 m1 hm0Canonical hm1Canonical with
    ⟨real, hreal, hrealCanonical, hrealExact⟩
  rcases generated_m31_sub_corresponds m2 m0 hm2Canonical hm0Canonical with
    ⟨imag0, himag0, himag0Canonical, himag0Exact⟩
  rcases generated_m31_sub_corresponds imag0 m1 himag0Canonical hm1Canonical with
    ⟨imag, himag, himagCanonical, himagExact⟩
  have hm0Run : V5RelationCompactFoldGenerated.aspis_core.field.M31.reduce_u64
      channels.val[(0#usize).val]! = ok m0 := by
    simpa [AspisLane5QM31SumProductsProof.rowCell] using hm0
  have hm1Run : V5RelationCompactFoldGenerated.aspis_core.field.M31.reduce_u64
      channels.val[(1#usize).val]! = ok m1 := by
    simpa [AspisLane5QM31SumProductsProof.rowCell] using hm1
  have hm2Run : V5RelationCompactFoldGenerated.aspis_core.field.M31.reduce_u64
      channels.val[(2#usize).val]! = ok m2 := by
    simpa [AspisLane5QM31SumProductsProof.rowCell] using hm2
  refine ⟨⟨real, imag⟩, ?_, ⟨hrealCanonical, himagCanonical⟩, ?_⟩
  · unfold V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
    rw [h0]
    simp only [bind_tc_ok]
    rw [hm0Run]
    simp only [bind_tc_ok]
    rw [h1]
    simp only [bind_tc_ok]
    rw [hm1Run]
    simp only [bind_tc_ok]
    rw [h2]
    simp only [bind_tc_ok]
    rw [hm2Run]
    simp only [bind_tc_ok]
    rw [hreal]
    simp only [bind_tc_ok]
    rw [himag0]
    simp only [bind_tc_ok]
    rw [himag]
    simp only [bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change ((real.val : Nat) : ExactM31) =
        (((AspisLane5QM31SumProductsProof.rowCell channels 0).val : Nat) :
            ExactM31) -
          ((AspisLane5QM31SumProductsProof.rowCell channels 1).val : ExactM31)
      rw [hrealExact, hm0Exact, hm1Exact]
    · change ((imag.val : Nat) : ExactM31) =
        (((AspisLane5QM31SumProductsProof.rowCell channels 2).val : Nat) :
            ExactM31) -
          ((AspisLane5QM31SumProductsProof.rowCell channels 0).val : ExactM31) -
          ((AspisLane5QM31SumProductsProof.rowCell channels 1).val : ExactM31)
      rw [himagExact, himag0Exact, hm0Exact, hm1Exact, hm2Exact]

/-- The generated reconstruction reduces all nine accumulated channels and
performs the exact CM31/QM31 Karatsuba reconstruction. -/
theorem reconstruction_corresponds
    (sums : Array (Array Std.U64 3#usize) 3#usize) :
    ∃ out : Fresh.QM31,
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums sums =
        ok out ∧
      canonicalQM31 out ∧
      qm31View out = reconstructQMExact sums := by
  have hrow0 := generated_array_index_run sums 0#usize (by norm_num)
  have hrow1 := generated_array_index_run sums 1#usize (by norm_num)
  have hrow2 := generated_array_index_run sums 2#usize (by norm_num)
  rcases reconstruct_closure_corresponds sums.val[(0#usize).val]! with
    ⟨m0, hm0, hm0Canonical, hm0Exact⟩
  rcases reconstruct_closure_corresponds sums.val[(1#usize).val]! with
    ⟨m1, hm1, hm1Canonical, hm1Exact⟩
  rcases reconstruct_closure_corresponds sums.val[(2#usize).val]! with
    ⟨m2, hm2, hm2Canonical, hm2Exact⟩
  simp only [cm31View] at hm0Exact hm1Exact hm2Exact
  rcases generated_mul_by_r_corresponds m1 hm1Canonical with
    ⟨rm1, hrm1, hrm1Canonical, hrm1Exact⟩
  rcases generated_cm31_add_corresponds m0 rm1 hm0Canonical hrm1Canonical with
    ⟨low, hlow, hlowCanonical, hlowExact⟩
  rcases generated_cm31_sub_corresponds m2 m0 hm2Canonical hm0Canonical with
    ⟨high0, hhigh0, hhigh0Canonical, hhigh0Exact⟩
  rcases generated_cm31_sub_corresponds high0 m1 hhigh0Canonical hm1Canonical with
    ⟨high, hhigh, hhighCanonical, hhighExact⟩
  refine ⟨⟨low, high⟩, ?_, ⟨hlowCanonical, hhighCanonical⟩, ?_⟩
  · unfold V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums
    rw [hrow0]
    simp only [bind_tc_ok]
    rw [hm0]
    simp only [bind_tc_ok]
    rw [hrow1]
    simp only [bind_tc_ok]
    rw [hm1]
    simp only [bind_tc_ok]
    rw [hrow2]
    simp only [bind_tc_ok]
    rw [hm2]
    simp only [bind_tc_ok]
    rw [hrm1]
    simp only [bind_tc_ok]
    rw [hlow]
    simp only [bind_tc_ok]
    rw [hhigh0]
    simp only [bind_tc_ok]
    rw [hhigh]
    simp only [bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change rawCM31ToExact low =
        reconstructCMExact sums.val[(0#usize).val]! +
          AspisV5ComponentCQM31TowerExact.qm31R *
            reconstructCMExact sums.val[(1#usize).val]!
      rw [hlowExact, hrm1Exact, hm0Exact, hm1Exact]
    · change rawCM31ToExact high =
        reconstructCMExact sums.val[(2#usize).val]! -
          reconstructCMExact sums.val[(0#usize).val]! -
          reconstructCMExact sums.val[(1#usize).val]!
      rw [hhighExact, hhigh0Exact, hm0Exact, hm1Exact, hm2Exact]

def reconstructExactChannels
    (channels : Nat → Nat → ExactM31) : ExactQM31 :=
  let component := fun row =>
    (⟨channels row 0 - channels row 1,
      channels row 2 - channels row 0 - channels row 1⟩ : ExactCM31)
  let m0 := component 0
  let m1 := component 1
  let m2 := component 2
  ⟨m0 + AspisV5ComponentCQM31TowerExact.qm31R * m1,
    m2 - m0 - m1⟩

def exactPreparedProductDot
    (leftValues : Nat → ExactQM31)
    (right : Array Fresh.QM31 3#usize) : ExactQM31 :=
  ∑ index ∈ Finset.range 3,
    leftValues index * qm31View right.val[index]!

private theorem reconstruct_exact_channels_add
    (f g : Nat → Nat → ExactM31) :
    reconstructExactChannels (fun row channel => f row channel + g row channel) =
      reconstructExactChannels f + reconstructExactChannels g := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add]
      simp [reconstructExactChannels,
        AspisV5ComponentCQM31TowerExact.qm31R]
      ring
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      simp [reconstructExactChannels,
        AspisV5ComponentCQM31TowerExact.qm31R]
      ring
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.re_add]
      simp [reconstructExactChannels,
        AspisV5ComponentCQM31TowerExact.qm31R]
      ring
    · simp only [QuadraticAlgebra.im_add]
      simp [reconstructExactChannels,
        AspisV5ComponentCQM31TowerExact.qm31R]
      ring

private theorem reconstruct_exact_channels_zero :
    reconstructExactChannels (fun _ _ => 0) = 0 := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp [reconstructExactChannels,
      AspisV5ComponentCQM31TowerExact.qm31R]

private theorem reconstruct_exact_channels_finset_sum
    (s : Finset Nat) (f : Nat → Nat → Nat → ExactM31) :
    reconstructExactChannels (fun row channel =>
      ∑ index ∈ s, f index row channel) =
      ∑ index ∈ s, reconstructExactChannels (f index) := by
  induction s using Finset.induction_on with
  | empty => simpa using reconstruct_exact_channels_zero
  | @insert index s hFresh ih =>
      simp only [Finset.sum_insert hFresh]
      rw [reconstruct_exact_channels_add, ih]

private theorem reconstruct_single_product_eq_mul
    (left right : ExactQM31) :
    reconstructExactChannels (fun row channel =>
      exactInputChannel left row channel *
        exactInputChannel right row channel) = left * right := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, AspisV5ComponentCQM31TowerExact.qm31R]
      ring
    · simp only [QuadraticAlgebra.re_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, AspisV5ComponentCQM31TowerExact.qm31R]
      ring
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.im_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, AspisV5ComponentCQM31TowerExact.qm31R]
      ring
    · simp only [QuadraticAlgebra.im_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, AspisV5ComponentCQM31TowerExact.qm31R]
      ring

theorem exact_prepared_channel_sum_eq_dot
    (leftValues : Nat → ExactQM31)
    (right : Array Fresh.QM31 3#usize) :
    reconstructExactChannels (fun row channel =>
      exactPreparedChannelDot leftValues right 3 row channel) =
      exactPreparedProductDot leftValues right := by
  unfold exactPreparedChannelDot exactPreparedProductDot
  rw [reconstruct_exact_channels_finset_sum]
  apply Finset.sum_congr rfl
  intro index hIndex
  exact reconstruct_single_product_eq_mul
    (leftValues index) (qm31View right.val[index]!)

private theorem reconstruct_qm_exact_eq_dot
    (leftValues : Nat → ExactQM31)
    (right : Array Fresh.QM31 3#usize)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hChannels : PreparedOuterInvariant sums leftValues right 3) :
    reconstructQMExact sums = exactPreparedProductDot leftValues right := by
  have h00 := (hChannels 0 (by omega) 0 (by omega)).2
  have h01 := (hChannels 0 (by omega) 1 (by omega)).2
  have h02 := (hChannels 0 (by omega) 2 (by omega)).2
  have h10 := (hChannels 1 (by omega) 0 (by omega)).2
  have h11 := (hChannels 1 (by omega) 1 (by omega)).2
  have h12 := (hChannels 1 (by omega) 2 (by omega)).2
  have h20 := (hChannels 2 (by omega) 0 (by omega)).2
  have h21 := (hChannels 2 (by omega) 1 (by omega)).2
  have h22 := (hChannels 2 (by omega) 2 (by omega)).2
  unfold AspisLane5QM31SumProductsProof.matrixCell at h00 h01 h02 h10 h11 h12 h20 h21 h22
  norm_num at h00 h01 h02 h10 h11 h12 h20 h21 h22
  have hReconstruct : reconstructQMExact sums =
      reconstructExactChannels (fun row channel =>
        exactPreparedChannelDot leftValues right 3 row channel) := by
    unfold reconstructQMExact reconstructCMExact reconstructExactChannels
    norm_num
    rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
    simp
  rw [hReconstruct, exact_prepared_channel_sum_eq_dot]

private theorem zero_channel_cell
    (row channel : Nat) (hRow : row < 3) (hChannel : channel < 3) :
    AspisLane5QM31SumProductsProof.matrixCell
        AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix row channel =
      0#u64 := by
  have hRow' : row < (3#usize).val := by simpa using hRow
  have hChannel' : channel < (3#usize).val := by simpa using hChannel
  unfold AspisLane5QM31SumProductsProof.matrixCell
    AspisLane5QM31SumProductsProof.rowCell
    AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix
  rw [Array.repeat_val, List.getElem!_replicate _ hRow']
  rw [Array.repeat_val, List.getElem!_replicate _ hChannel']

theorem zero_prepared_outer_invariant
    (leftValues : Nat → ExactQM31)
    (right : Array Fresh.QM31 3#usize) :
    PreparedOuterInvariant
      AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix
      leftValues right 0 := by
  intro row hRow channel hChannel
  rw [zero_channel_cell row channel hRow hChannel]
  simp [exactPreparedChannelDot]

/-- Arbitrary canonical inputs to the extracted prepared three-product helper
return their exact QM31 dot product.  The prepared cache relation is proved
separately by the source constructor theorem used by each FRI caller. -/
theorem qm31_sum_products3_prepared_corresponds
    (left : Array Fresh.Prepared 3#usize)
    (right : Array Fresh.QM31 3#usize)
    (leftValues : Nat → ExactQM31)
    (hLeft : PreparedArrayRepresents left leftValues)
    (hRight : CanonicalQM31Array3 right) :
    ∃ out : Fresh.QM31,
      V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared left right =
        ok out ∧
      canonicalQM31 out ∧
      qm31View out = exactPreparedProductDot leftValues right := by
  have hOuterSpec := prepared_outer_loop_corresponds left right leftValues
    AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix hLeft hRight
    (zero_prepared_outer_invariant leftValues right)
  obtain ⟨sums, hOuterRun, hChannels⟩ :=
    Aeneas.Std.WP.spec_imp_exists hOuterSpec
  rcases reconstruction_corresponds sums with
    ⟨out, hReconstruct, hCanonical, hExact⟩
  refine ⟨out, ?_, hCanonical, ?_⟩
  · unfold V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared
    change
      (do
        let sums1 ←
          V5RelationCompactFoldGenerated.aspis_core.field.qm31_sum_products3_prepared_loop0
            { start := 0#usize, «end» := 3#usize } left right
            AspisLane5QM31SumProductsProof.zeroU64ChannelMatrix
        V5RelationCompactFoldGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums sums1) =
        ok out
    rw [hOuterRun]
    simp only [bind_tc_ok]
    rw [hReconstruct]
  · rw [hExact, reconstruct_qm_exact_eq_dot leftValues right sums hChannels]

end AspisV5RelationCompactFoldPreparedSum3

#print axioms AspisV5RelationCompactFoldPreparedSum3.prepared_component_loop_corresponds
#print axioms AspisV5RelationCompactFoldPreparedSum3.prepared_outer_loop_corresponds
#print axioms AspisV5RelationCompactFoldPreparedSum3.reconstruction_corresponds
#print axioms AspisV5RelationCompactFoldPreparedSum3.qm31_sum_products3_prepared_corresponds
