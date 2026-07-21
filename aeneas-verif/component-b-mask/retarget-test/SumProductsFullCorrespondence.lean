import SumProductsComponentLoop

/-!
# The generated outer input loop and public small-sum wrappers

This file composes the already-proved generated channel and component loops
through the source-authentic outer input loop.  It deliberately keeps the
generated fixed arrays opaque until their two bounded indices are split; this
avoids the `getElem!` simplifier cycle that blocked the earlier attempt.
-/

open Aeneas Aeneas.Std Result ControlFlow
open scoped BigOperators

namespace AspisLane5QM31SumProductsProof

instance : Inhabited RustM31 := ⟨0#u32⟩
instance : Inhabited RustCM31 := ⟨⟨0#u32, 0#u32⟩⟩
instance : Inhabited RustQM31 := ⟨⟨default, default⟩⟩

def generatedComponentMatrix
    (q : RustQM31) (qsum : RustCM31) (m0 m1 m2 : RustM31) :
    Array (Array RustM31 3#usize) 3#usize :=
  Array.make 3#usize [
    Array.make 3#usize [q.c0.a, q.c0.b, m0],
    Array.make 3#usize [q.c1.a, q.c1.b, m1],
    Array.make 3#usize [qsum.a, qsum.b, m2]
  ]

def exactCMChannel (x : CM31Exact) (channel : Nat) : M31Exact :=
  if channel = 0 then x.re else if channel = 1 then x.im else x.re + x.im

def exactQMComponent (x : QM31Exact) (component : Nat) : CM31Exact :=
  if component = 0 then x.re else if component = 1 then x.im else x.re + x.im

def exactInputChannel (q : RustQM31) (component channel : Nat) : M31Exact :=
  exactCMChannel (exactQMComponent (qm31ToExact q) component) channel

private theorem generated_component_matrix_canonical
    (q : RustQM31) (qsum : RustCM31) (m0 m1 m2 : RustM31)
    (hq : CanonicalQM31 q)
    (hqsum : CanonicalCM31 qsum)
    (hm0 : CanonicalRawM31 m0.val)
    (hm1 : CanonicalRawM31 m1.val)
    (hm2 : CanonicalRawM31 m2.val) :
    CanonicalChannelMatrix (generatedComponentMatrix q qsum m0 m1 m2) := by
  rcases hq with ⟨⟨hc0a, hc0b⟩, ⟨hc1a, hc1b⟩⟩
  rcases hqsum with ⟨hsuma, hsumb⟩
  intro component hComponent channel hChannel
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals
    simp only [channelM31, generatedComponentMatrix, Aeneas.Std.Array.make]
  all_goals assumption

private theorem generated_component_matrix_exact
    (q : RustQM31) (qsum : RustCM31) (m0 m1 m2 : RustM31)
    (hqsumExact : cm31ToExact qsum = cm31ToExact q.c0 + cm31ToExact q.c1)
    (hm0Exact : ((m0.val : Nat) : M31Exact) =
      ((q.c0.a.val : Nat) : M31Exact) + ((q.c0.b.val : Nat) : M31Exact))
    (hm1Exact : ((m1.val : Nat) : M31Exact) =
      ((q.c1.a.val : Nat) : M31Exact) + ((q.c1.b.val : Nat) : M31Exact))
    (hm2Exact : ((m2.val : Nat) : M31Exact) =
      ((qsum.a.val : Nat) : M31Exact) + ((qsum.b.val : Nat) : M31Exact)) :
    ∀ component, component < 3 → ∀ channel, channel < 3 →
      (((channelM31 (generatedComponentMatrix q qsum m0 m1 m2)
        component channel).val : Nat) : M31Exact) =
        exactInputChannel q component channel := by
  intro component hComponent channel hChannel
  have hqsumRe := congrArg (fun x : CM31Exact => x.re) hqsumExact
  have hqsumIm := congrArg (fun x : CM31Exact => x.im) hqsumExact
  change (((qsum.a.val : Nat) : M31Exact) =
    ((q.c0.a.val : Nat) : M31Exact) +
      ((q.c1.a.val : Nat) : M31Exact)) at hqsumRe
  change (((qsum.b.val : Nat) : M31Exact) =
    ((q.c0.b.val : Nat) : M31Exact) +
      ((q.c1.b.val : Nat) : M31Exact)) at hqsumIm
  have hc : component = 0 ∨ component = 1 ∨ component = 2 := by omega
  have hh : channel = 0 ∨ channel = 1 ∨ channel = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
  all_goals
    simp only [channelM31, generatedComponentMatrix, Aeneas.Std.Array.make]
  all_goals
    simp [exactInputChannel, exactQMComponent, exactCMChannel, qm31ToExact,
      cm31ToExact] at hqsumExact ⊢
  all_goals try exact hm0Exact
  all_goals try exact hm1Exact
  all_goals try rw [hm2Exact]
  all_goals try rw [hqsumRe]
  all_goals try rw [hqsumIm]

private theorem fresh_P_eq_existing :
    ComponentBGenerated.aspis_core.field.P =
      AspisCoreCM31Multiplicative.field.P := by
  apply UScalar.eq_of_val_eq
  unfold ComponentBGenerated.aspis_core.field.P
    AspisCoreCM31Multiplicative.field.P
  rfl

private theorem fresh_m31_add_eq_existing (a b : RustM31) :
    ComponentBGenerated.aspis_core.field.M31.add a b =
      AspisCoreCM31Multiplicative.field.M31.add a b := by
  unfold ComponentBGenerated.aspis_core.field.M31.add
    AspisCoreCM31Multiplicative.field.M31.add
  rw [fresh_P_eq_existing]

private theorem fresh_m31_add_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      ComponentBGenerated.aspis_core.field.M31.add a b = ok out ∧
      CanonicalRawM31 out.val ∧
      (((out.val : Nat) : M31Exact) =
        ((a.val : Nat) : M31Exact) + ((b.val : Nat) : M31Exact)) := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      a b ha hb with ⟨out, hout, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [fresh_m31_add_eq_existing]
  exact hout

private theorem fresh_cm31_add_corresponds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      ComponentBGenerated.aspis_core.field.CM31.add x y = ok out ∧
      CanonicalCM31 out ∧
      cm31ToExact out = cm31ToExact x + cm31ToExact y := by
  rcases fresh_m31_add_corresponds x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, hexactA⟩
  rcases fresh_m31_add_corresponds x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, hexactB⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩, ?_⟩
  · simp [ComponentBGenerated.aspis_core.field.CM31.add,
      hcallA, hcallB]
  · apply QuadraticAlgebra.ext
    · exact hexactA
    · exact hexactB

def CanonicalQM31Array {N : Std.Usize} (values : Array RustQM31 N) : Prop :=
  ∀ index, index < N.val → CanonicalQM31 values.val[index]!

def exactChannelDot {N : Std.Usize}
    (left right : Array RustQM31 N) (processed row channel : Nat) : M31Exact :=
  ∑ index ∈ Finset.range processed,
    exactInputChannel left.val[index]! row channel *
      exactInputChannel right.val[index]! row channel

def OuterChannelInvariant {N : Std.Usize}
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (left right : Array RustQM31 N) (processed : Nat) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell current row channel).val ≤ processed * channelProductBound ∧
    (((matrixCell current row channel).val : Nat) : M31Exact) =
      exactChannelDot left right processed row channel

private theorem fresh_list_get_eq_getElemBang
    {T : Type} [Inhabited T]
    (values : List T) (index : Nat) (hIndex : index < values.length) :
    values[index] = values[index]! := by
  symm
  apply List.getElem!_of_getElem?
  simp [hIndex]

private theorem fresh_generated_array_index_run
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (index : Std.Usize) (hIndex : index.val < N.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hRun, hValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hArrayBound : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hElem := fresh_list_get_eq_getElemBang values.val index.val hArrayBound
  simpa [hValue, hElem] using hRun

def SingleProductPost
    (before after : Array (Array Std.U64 3#usize) 3#usize)
    (left right : RustQM31) : Prop :=
  ∀ row, row < 3 → ∀ channel, channel < 3 →
    (matrixCell after row channel).val ≤
        (matrixCell before row channel).val + channelProductBound ∧
    (((matrixCell after row channel).val : Nat) : M31Exact) =
      (((matrixCell before row channel).val : Nat) : M31Exact) +
        exactInputChannel left row channel *
          exactInputChannel right row channel

/-- The actual extracted per-pair helper adds exactly one product to every
Karatsuba channel.  The only arithmetic premise is the source's four-product
`u64` headroom bound specialized to the caller's current accumulator. -/
theorem extracted_qm31_accumulate_product_channels_corresponds
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (left right : RustQM31)
    (hLeft : CanonicalQM31 left) (hRight : CanonicalQM31 right)
    (hSpace : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell current row channel).val + channelProductBound <
        u64Cardinality) :
    ∃ out,
      ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels
          current left right = ok out ∧
      SingleProductPost current out left right := by
  rcases fresh_cm31_add_corresponds left.c0 left.c1 hLeft.1 hLeft.2 with
    ⟨leftSum, hLeftSum, hLeftSumCanonical, hLeftSumExact⟩
  rcases fresh_cm31_add_corresponds right.c0 right.c1 hRight.1 hRight.2 with
    ⟨rightSum, hRightSum, hRightSumCanonical, hRightSumExact⟩
  rcases fresh_m31_add_corresponds left.c0.a left.c0.b hLeft.1.1 hLeft.1.2 with
    ⟨lm0, hLm0, hLm0Canonical, hLm0Exact⟩
  rcases fresh_m31_add_corresponds left.c1.a left.c1.b hLeft.2.1 hLeft.2.2 with
    ⟨lm1, hLm1, hLm1Canonical, hLm1Exact⟩
  rcases fresh_m31_add_corresponds leftSum.a leftSum.b
      hLeftSumCanonical.1 hLeftSumCanonical.2 with
    ⟨lm2, hLm2, hLm2Canonical, hLm2Exact⟩
  rcases fresh_m31_add_corresponds right.c0.a right.c0.b
      hRight.1.1 hRight.1.2 with
    ⟨rm0, hRm0, hRm0Canonical, hRm0Exact⟩
  rcases fresh_m31_add_corresponds right.c1.a right.c1.b
      hRight.2.1 hRight.2.2 with
    ⟨rm1, hRm1, hRm1Canonical, hRm1Exact⟩
  rcases fresh_m31_add_corresponds rightSum.a rightSum.b
      hRightSumCanonical.1 hRightSumCanonical.2 with
    ⟨rm2, hRm2, hRm2Canonical, hRm2Exact⟩
  let leftComponents := generatedComponentMatrix left leftSum lm0 lm1 lm2
  let rightComponents := generatedComponentMatrix right rightSum rm0 rm1 rm2
  have hLeftComponentsCanonical : CanonicalChannelMatrix leftComponents :=
    generated_component_matrix_canonical left leftSum lm0 lm1 lm2 hLeft
      hLeftSumCanonical hLm0Canonical hLm1Canonical hLm2Canonical
  have hRightComponentsCanonical : CanonicalChannelMatrix rightComponents :=
    generated_component_matrix_canonical right rightSum rm0 rm1 rm2 hRight
      hRightSumCanonical hRm0Canonical hRm1Canonical hRm2Canonical
  have hLeftComponentsExact := generated_component_matrix_exact left leftSum
    lm0 lm1 lm2 hLeftSumExact hLm0Exact hLm1Exact hLm2Exact
  have hRightComponentsExact := generated_component_matrix_exact right rightSum
    rm0 rm1 rm2 hRightSumExact hRm0Exact hRm1Exact hRm2Exact
  have hNoOverflow : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell current row channel).val +
        (channelM31 leftComponents row channel).val *
        (channelM31 rightComponents row channel).val < u64Cardinality := by
    intro row hRow channel hChannel
    have hl := hLeftComponentsCanonical row hRow channel hChannel
    have hr := hRightComponentsCanonical row hRow channel hChannel
    change (channelM31 leftComponents row channel).val < m31Modulus at hl
    change (channelM31 rightComponents row channel).val < m31Modulus at hr
    have hlle : (channelM31 leftComponents row channel).val ≤
        m31Modulus - 1 := by omega
    have hrle : (channelM31 rightComponents row channel).val ≤
        m31Modulus - 1 := by omega
    have hProduct :
        (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val ≤
            channelProductBound := by
      unfold channelProductBound
      simpa [pow_two] using Nat.mul_le_mul hlle hrle
    exact lt_of_le_of_lt (Nat.add_le_add_left hProduct _) (hSpace row hRow channel hChannel)
  have hComponentSpec := generated_component_loop_corresponds current
    leftComponents rightComponents hNoOverflow
  obtain ⟨out, hComponentRun, hComponentPost⟩ :=
    Aeneas.Std.WP.spec_imp_exists hComponentSpec
  have hPost : SingleProductPost current out left right := by
    intro row hRow channel hChannel
    have hInner := hComponentPost row hRow channel hChannel
    simp only [show row < 3 from hRow, if_pos] at hInner
    have hLeftExact :
        (((channelM31 leftComponents row channel).val : Nat) : M31Exact) =
          exactInputChannel left row channel := by
      simpa [leftComponents] using
        hLeftComponentsExact row hRow channel hChannel
    have hRightExact :
        (((channelM31 rightComponents row channel).val : Nat) : M31Exact) =
          exactInputChannel right row channel := by
      simpa [rightComponents] using
        hRightComponentsExact row hRow channel hChannel
    have hl := hLeftComponentsCanonical row hRow channel hChannel
    have hr := hRightComponentsCanonical row hRow channel hChannel
    change (channelM31 leftComponents row channel).val < m31Modulus at hl
    change (channelM31 rightComponents row channel).val < m31Modulus at hr
    have hlle : (channelM31 leftComponents row channel).val ≤
        m31Modulus - 1 := by omega
    have hrle : (channelM31 rightComponents row channel).val ≤
        m31Modulus - 1 := by omega
    have hProduct :
        (channelM31 leftComponents row channel).val *
          (channelM31 rightComponents row channel).val ≤
            channelProductBound := by
      unfold channelProductBound
      simpa [pow_two] using Nat.mul_le_mul hlle hrle
    constructor
    · rw [hInner]
      exact Nat.add_le_add_left hProduct _
    · rw [hInner, Nat.cast_add, Nat.cast_mul, hLeftExact, hRightExact]
  refine ⟨out, ?_, hPost⟩
  unfold
    ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels
  rw [hLeftSum]
  simp only [bind_tc_ok]
  rw [hRightSum]
  simp only [bind_tc_ok]
  rw [hLm0]
  simp only [bind_tc_ok]
  rw [hLm1]
  simp only [bind_tc_ok]
  rw [hLm2]
  simp only [bind_tc_ok]
  rw [hRm0]
  simp only [bind_tc_ok]
  rw [hRm1]
  simp only [bind_tc_ok]
  rw [hRm2]
  simp only [bind_tc_ok]
  simpa [leftComponents, rightComponents, generatedComponentMatrix] using
    hComponentRun

theorem usize_wrapping_add_one_val_small
    (index : Std.Usize) (hIndex : index.val < 4) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;>
    simp_all [Usize.size, Usize.numBits] <;> omega

private theorem generated_outer_body_active
    {N : Std.Usize} (left right : Array RustQM31 N)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize) (hIndex : index.val < N.val)
    (hN : N.val ≤ 4)
    (hLeftCanonical : CanonicalQM31Array left)
    (hRightCanonical : CanonicalQM31Array right)
    (hInvariant : OuterChannelInvariant current left right index.val) :
    ∃ next out,
      ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
          left right current index = ok (cont (out, next)) ∧
      next.val = index.val + 1 ∧
      OuterChannelInvariant out left right (index.val + 1) := by
  let ql : RustQM31 := left.val[index.val]!
  let qr : RustQM31 := right.val[index.val]!
  have hLeftIndex := fresh_generated_array_index_run left index hIndex
  have hRightIndex := fresh_generated_array_index_run right index hIndex
  have hql : CanonicalQM31 ql := hLeftCanonical index.val hIndex
  have hqr : CanonicalQM31 qr := hRightCanonical index.val hIndex
  have hSpace : ∀ row, row < 3 → ∀ channel, channel < 3 →
      (matrixCell current row channel).val + channelProductBound <
        u64Cardinality := by
    intro row hRow channel hChannel
    have hBound := (hInvariant row hRow channel hChannel).1
    have hCount : index.val + 1 ≤ 4 := by omega
    calc
      (matrixCell current row channel).val + channelProductBound
          ≤ index.val * channelProductBound + channelProductBound :=
            Nat.add_le_add_right hBound _
      _ = (index.val + 1) * channelProductBound := by ring
      _ ≤ 4 * channelProductBound :=
        Nat.mul_le_mul_right channelProductBound hCount
      _ < u64Cardinality := four_channel_products_fit_u64
  rcases extracted_qm31_accumulate_product_channels_corresponds current ql qr
      hql hqr hSpace with ⟨out, hHelperRun, hHelperPost⟩
  let next := Std.Usize.wrapping_add index 1#usize
  have hNextVal : next.val = index.val + 1 :=
    usize_wrapping_add_one_val_small index (by omega)
  have hOutInvariant : OuterChannelInvariant out left right (index.val + 1) := by
    intro row hRow channel hChannel
    have hOld := hInvariant row hRow channel hChannel
    have hStep := hHelperPost row hRow channel hChannel
    constructor
    · exact le_trans hStep.1 (by
        calc
          (matrixCell current row channel).val + channelProductBound
              ≤ index.val * channelProductBound + channelProductBound :=
                Nat.add_le_add_right hOld.1 _
          _ = (index.val + 1) * channelProductBound := by ring)
    · rw [hStep.2, hOld.2]
      simp [exactChannelDot, ql, qr, Finset.sum_range_succ]
  refine ⟨next, out, ?_, hNextVal, hOutInvariant⟩
  unfold
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
  simp only [show index < N from hIndex, if_pos]
  rw [hLeftIndex]
  simp only [bind_tc_ok]
  rw [hRightIndex]
  simp only [bind_tc_ok]
  change
    (do
      let sums1 ←
        ComponentBGenerated.aspis_core.field.qm31_accumulate_product_channels
          current ql qr
      let index1 ← lift (Std.Usize.wrapping_add index 1#usize)
      ok (cont (sums1, index1))) = ok (cont (out, next))
  rw [hHelperRun]
  simp only [bind_tc_ok, Std.lift]
  rfl

private theorem generated_outer_body_done
    {N : Std.Usize} (left right : Array RustQM31 N)
    (current : Array (Array Std.U64 3#usize) 3#usize)
    (index : Std.Usize) (hDone : ¬ index.val < N.val) :
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
        left right current index = ok (done current) := by
  unfold
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop.body
  simp [hDone]

/-- Direct invariant for the actual generated indexed outer loop. -/
theorem generated_outer_loop_corresponds
    {N : Std.Usize} (left right : Array RustQM31 N)
    (initial : Array (Array Std.U64 3#usize) 3#usize)
    (hN : N.val ≤ 4)
    (hLeftCanonical : CanonicalQM31Array left)
    (hRightCanonical : CanonicalQM31Array right)
    (hInitial : OuterChannelInvariant initial left right 0) :
    ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop
        left right initial 0#usize
      ⦃ out => OuterChannelInvariant out left right N.val ⦄ := by
  simp only [ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop]
  apply loop.spec_decr_nat
    (fun state : Array (Array Std.U64 3#usize) 3#usize × Std.Usize =>
      N.val - state.2.val)
    (fun state => state.2.val ≤ N.val ∧
      OuterChannelInvariant state.1 left right state.2.val)
    (fun out => OuterChannelInvariant out left right N.val)
  · rintro ⟨current, index⟩ ⟨hIndexLe, hInvariant⟩
    dsimp only at hIndexLe hInvariant ⊢
    by_cases hActive : index.val < N.val
    · obtain ⟨next, out, hBody, hNext, hOut⟩ :=
        generated_outer_body_active left right current index hActive hN
          hLeftCanonical hRightCanonical hInvariant
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hNext]
        omega
      · rw [hNext]
        exact hOut
      · rw [hNext]
        omega
    · have hAtEnd : index.val = N.val := by omega
      rw [generated_outer_body_done left right current index hActive]
      simpa [hAtEnd] using hInvariant
  · exact ⟨by norm_num, hInitial⟩

private theorem zero_u64_channel_cell_indexed
    (row channel : Nat) (hRow : row < 3) (hChannel : channel < 3) :
    matrixCell zeroU64ChannelMatrix row channel = 0#u64 := by
  have hRow' : row < (3#usize).val := by simpa using hRow
  have hChannel' : channel < (3#usize).val := by simpa using hChannel
  unfold matrixCell rowCell zeroU64ChannelMatrix
  rw [Array.repeat_val, List.getElem!_replicate _ hRow']
  rw [Array.repeat_val, List.getElem!_replicate _ hChannel']

theorem zero_outer_invariant
    {N : Std.Usize} (left right : Array RustQM31 N) :
    OuterChannelInvariant zeroU64ChannelMatrix left right 0 := by
  intro row hRow channel hChannel
  rw [zero_u64_channel_cell_indexed row channel hRow hChannel]
  simp [exactChannelDot]

def reconstructExactChannels (channels : Nat → Nat → M31Exact) : QM31Exact :=
  let component := fun row => (
    ⟨channels row 0 - channels row 1,
      channels row 2 - channels row 0 - channels row 1⟩ : CM31Exact)
  let m0 := component 0
  let m1 := component 1
  let m2 := component 2
  ⟨m0 + qm31R * m1, m2 - m0 - m1⟩

def exactSmallProductSum {N : Std.Usize}
    (left right : Array RustQM31 N) : QM31Exact :=
  reconstructExactChannels (fun row channel =>
    exactChannelDot left right N.val row channel)

def exactProductDot {N : Std.Usize}
    (left right : Array RustQM31 N) : QM31Exact :=
  ∑ index ∈ Finset.range N.val,
    qm31ToExact left.val[index]! * qm31ToExact right.val[index]!

private theorem reconstruct_exact_channels_add
    (f g : Nat → Nat → M31Exact) :
    reconstructExactChannels (fun row channel => f row channel + g row channel) =
      reconstructExactChannels f + reconstructExactChannels g := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add]
      simp [reconstructExactChannels, qm31R]
      ring
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      simp [reconstructExactChannels, qm31R]
      ring
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.re_add]
      simp [reconstructExactChannels, qm31R]
      ring
    · simp only [QuadraticAlgebra.im_add]
      simp [reconstructExactChannels, qm31R]
      ring

private theorem reconstruct_exact_channels_zero :
    reconstructExactChannels (fun _ _ => 0) = 0 := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp [reconstructExactChannels, qm31R]

private theorem reconstruct_exact_channels_finset_sum
    (s : Finset Nat) (f : Nat → Nat → Nat → M31Exact) :
    reconstructExactChannels (fun row channel =>
      ∑ index ∈ s, f index row channel) =
      ∑ index ∈ s, reconstructExactChannels (f index) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using reconstruct_exact_channels_zero
  | @insert index s hFresh ih =>
      simp only [Finset.sum_insert hFresh]
      rw [reconstruct_exact_channels_add, ih]

private theorem reconstruct_single_product_eq_mul (left right : RustQM31) :
    reconstructExactChannels (fun row channel =>
      exactInputChannel left row channel *
        exactInputChannel right row channel) =
      qm31ToExact left * qm31ToExact right := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, qm31ToExact, cm31ToExact, qm31R]
      ring
    · simp only [QuadraticAlgebra.re_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, qm31ToExact, cm31ToExact, qm31R]
      ring
  · apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.im_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, qm31ToExact, cm31ToExact, qm31R]
      ring
    · simp only [QuadraticAlgebra.im_mul]
      simp [reconstructExactChannels, exactInputChannel, exactQMComponent,
        exactCMChannel, qm31ToExact, cm31ToExact, qm31R]
      ring

theorem exact_small_product_sum_eq_dot
    {N : Std.Usize} (left right : Array RustQM31 N) :
    exactSmallProductSum left right = exactProductDot left right := by
  unfold exactSmallProductSum exactProductDot exactChannelDot
  rw [reconstruct_exact_channels_finset_sum]
  apply Finset.sum_congr rfl
  intro index hIndex
  exact reconstruct_single_product_eq_mul left.val[index]! right.val[index]!

private theorem reconstruct_qm_exact_eq_exact_small_sum
    {N : Std.Usize} (left right : Array RustQM31 N)
    (sums : Array (Array Std.U64 3#usize) 3#usize)
    (hChannels : OuterChannelInvariant sums left right N.val) :
    reconstructQMExact sums = exactSmallProductSum left right := by
  have h00 := (hChannels 0 (by omega) 0 (by omega)).2
  have h01 := (hChannels 0 (by omega) 1 (by omega)).2
  have h02 := (hChannels 0 (by omega) 2 (by omega)).2
  have h10 := (hChannels 1 (by omega) 0 (by omega)).2
  have h11 := (hChannels 1 (by omega) 1 (by omega)).2
  have h12 := (hChannels 1 (by omega) 2 (by omega)).2
  have h20 := (hChannels 2 (by omega) 0 (by omega)).2
  have h21 := (hChannels 2 (by omega) 1 (by omega)).2
  have h22 := (hChannels 2 (by omega) 2 (by omega)).2
  unfold matrixCell at h00 h01 h02 h10 h11 h12 h20 h21 h22
  norm_num at h00 h01 h02 h10 h11 h12 h20 h21 h22
  unfold reconstructQMExact exactSmallProductSum reconstructCMExact
    reconstructExactChannels
  norm_num
  rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
  simp

/-- Arbitrary-input end-to-end correspondence for the extracted generic
small-product function on its exact overflow-safe domain. -/
theorem extracted_qm31_sum_products_small_corresponds
    {N : Std.Usize} (left right : Array RustQM31 N)
    (hN : N.val ≤ 4)
    (hLeft : CanonicalQM31Array left)
    (hRight : CanonicalQM31Array right) :
    ∃ out : RustQM31,
      ComponentBGenerated.aspis_core.field.qm31_sum_products_small
          left right = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = exactProductDot left right := by
  have hOuterSpec := generated_outer_loop_corresponds left right
    zeroU64ChannelMatrix hN hLeft hRight (zero_outer_invariant left right)
  obtain ⟨sums, hOuterRun, hChannels⟩ :=
    Aeneas.Std.WP.spec_imp_exists hOuterSpec
  rcases extracted_qm31_from_karatsuba_channel_sums_corresponds sums with
    ⟨out, hReconstruct, hCanonical, hExact⟩
  refine ⟨out, ?_, hCanonical, ?_⟩
  · unfold ComponentBGenerated.aspis_core.field.qm31_sum_products_small
    change
      (do
        let sums1 ←
          ComponentBGenerated.aspis_core.field.qm31_sum_products_small_loop
            left right zeroU64ChannelMatrix 0#usize
        ComponentBGenerated.aspis_core.field.qm31_from_karatsuba_channel_sums
          sums1) = ok out
    rw [hOuterRun]
    simp only [bind_tc_ok]
    rw [hReconstruct]
  · rw [hExact, reconstruct_qm_exact_eq_exact_small_sum left right sums hChannels,
      exact_small_product_sum_eq_dot]

theorem extracted_qm31_sum_products3_corresponds
    (left right : Array RustQM31 3#usize)
    (hLeft : CanonicalQM31Array left)
    (hRight : CanonicalQM31Array right) :
    ∃ out : RustQM31,
      ComponentBGenerated.aspis_core.field.qm31_sum_products3 left right =
          ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = exactProductDot left right := by
  simpa [ComponentBGenerated.aspis_core.field.qm31_sum_products3] using
    extracted_qm31_sum_products_small_corresponds left right (by norm_num)
      hLeft hRight

#print axioms extracted_qm31_accumulate_product_channels_corresponds
#print axioms usize_wrapping_add_one_val_small
#print axioms generated_outer_loop_corresponds
#print axioms zero_outer_invariant
#print axioms exact_small_product_sum_eq_dot
#print axioms extracted_qm31_sum_products_small_corresponds
#print axioms extracted_qm31_sum_products3_corresponds

end AspisLane5QM31SumProductsProof
