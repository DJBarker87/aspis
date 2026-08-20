import Coordinates.Funs
import V5FriCoordinateFieldSemantics
import V5FriBatchInverseMathematics

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 12000

/-!
# Exact source semantics of the V5 batch-inverse loops

This file follows the two translated Rust loops which implement Montgomery
batch inversion.  The first loop stores every prefix product.  The second
walks backwards, multiplies each stored prefix by the common backend value and
the appropriate suffix, and writes the result in place.  The production
first-entry check then validates all returned inverses.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCoordinateInverseLoops

open AspisV5FriCoordinateFieldSemantics
open AspisV5FriBatchInverseMathematics
open AspisCircleGroupOrder

namespace Coordinate
open V5FriCoordinateAdapter

abbrev M31 := aspis_core.field.M31
abbrev M31Vec := alloc.vec.Vec M31

end Coordinate

instance : Inhabited Coordinate.M31 := ⟨0#u32⟩

def CanonicalVec (values : Coordinate.M31Vec) : Prop :=
  ∀ index, index < values.val.length → canonicalM31 values.val[index]!

private theorem getElemBang_eq_getElem {T : Type*} [Inhabited T]
    (values : List T) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

def prefixProduct (denominators : Coordinate.M31Vec) (count : Nat) : ZMod P :=
  ((denominators.val.take count).map m31Value).prod

def suffixProduct (denominators : Coordinate.M31Vec) (start : Nat) : ZMod P :=
  ((denominators.val.drop start).map m31Value).prod

private theorem wrapping_add_one_exact (index : Std.Usize)
    (hindex : index.val < Std.Usize.max) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone, UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem wrapping_sub_one_exact (index : Std.Usize)
    (hindex : 0 < index.val) :
    (Std.Usize.wrapping_sub index 1#usize).val = index.val - 1 := by
  rw [Std.Usize.wrapping_sub_val_eq]
  have hone : (1#usize : Std.Usize).val = 1 := rfl
  rw [hone]
  have hsize := index.hSize
  have hrearrange :
      index.val + (UScalar.size .Usize - 1) =
        (index.val - 1) + UScalar.size .Usize := by omega
  rw [hrearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem canonical_set
    (values : Coordinate.M31Vec) (index : Std.Usize)
    (value : Coordinate.M31)
    (hvalues : CanonicalVec values)
    (hindex : index.val < values.val.length)
    (hvalue : canonicalM31 value) :
    CanonicalVec (values.set index value) := by
  intro slot hslot
  have hlength : (values.val.set index.val value).length =
      values.val.length := List.length_set
  change slot < (values.val.set index.val value).length at hslot
  change canonicalM31 (values.val.set index.val value)[slot]!
  have hslotOld : slot < values.val.length := by
    simpa [alloc.vec.Vec.set_val_eq, hlength] using hslot
  rw [getElemBang_eq_getElem (values.val.set index.val value) slot
      (by simpa [alloc.vec.Vec.set_val_eq] using hslot)]
  rw [List.getElem_set]
  by_cases heq : index.val = slot
  · simp [heq, hvalue]
  · simp [heq]
    have hold := hvalues slot hslotOld
    rwa [getElemBang_eq_getElem values.val slot hslotOld] at hold

private theorem prefixProduct_succ
    (denominators : Coordinate.M31Vec) (index : Nat)
    (hindex : index < denominators.val.length) :
    prefixProduct denominators (index + 1) =
      prefixProduct denominators index *
        m31Value denominators.val[index]! := by
  unfold prefixProduct
  have htake := List.take_concat_get' denominators.val index hindex
  change
    ((denominators.val.take (index + 1)).map m31Value).prod =
      ((denominators.val.take index).map m31Value).prod *
        m31Value denominators.val[index]!
  rw [← htake, List.map_append, List.prod_append]
  simp [List.getElem!_eq_getElem?_getD, hindex]

private def PrefixInvariant
    (denominators : Coordinate.M31Vec)
    (state : Coordinate.M31Vec × Coordinate.M31 × Std.Usize) : Prop :=
  state.2.2.val ≤ denominators.val.length ∧
  state.1.val.length = denominators.val.length ∧
  CanonicalVec state.1 ∧
  canonicalM31 state.2.1 ∧
  m31Value state.2.1 = prefixProduct denominators state.2.2.val ∧
  ∀ index, index < state.2.2.val →
    m31Value state.1.val[index]! = prefixProduct denominators index

private def PrefixPost
    (denominators : Coordinate.M31Vec)
    (out : Coordinate.M31Vec × Coordinate.M31) : Prop :=
  out.1.val.length = denominators.val.length ∧
  CanonicalVec out.1 ∧
  canonicalM31 out.2 ∧
  m31Value out.2 = prefixProduct denominators denominators.val.length ∧
  ∀ index, index < denominators.val.length →
    m31Value out.1.val[index]! = prefixProduct denominators index

/-- The translated forward loop stores the exact product preceding every
denominator and returns the product of the complete list. -/
theorem prefix_loop_exact
    (denominators flat : Coordinate.M31Vec)
    (accumulator : Coordinate.M31) (index : Std.Usize)
    (hdenominators : CanonicalVec denominators)
    (hinvariant : PrefixInvariant denominators (flat, accumulator, index)) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17
        denominators flat accumulator index
      ⦃ out => PrefixPost denominators out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17
  apply loop.spec_decr_nat
    (fun state => denominators.val.length - state.2.2.val)
    (PrefixInvariant denominators)
    (PrefixPost denominators)
  · rintro ⟨current, currentAccumulator, currentIndex⟩ hstate
    rcases hstate with
      ⟨hindexLe, hlength, hcanonical, haccCanonical, haccValue,
        hprefix⟩
    simp only at hindexLe hlength hcanonical haccCanonical haccValue hprefix
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop17.body
    by_cases hactive : currentIndex.val < denominators.val.length
    · have hcondition :
          currentIndex < alloc.vec.Vec.len denominators := by
        simpa [UScalar.lt_equiv] using hactive
      have hflatBound : currentIndex.val < current.val.length := by
        rwa [hlength]
      have hindexSmall : currentIndex.val < Std.Usize.max := by
        have hdenomMax := denominators.property
        omega
      have hdenominatorCanonical :
          canonicalM31 denominators.val[currentIndex.val]! := by
        exact hdenominators currentIndex.val hactive
      obtain ⟨product, hmul, hproductCanonical, hproductValue⟩ :=
        mul_produces_canonical currentAccumulator
          denominators.val[currentIndex.val]!
          haccCanonical hdenominatorCanonical
      have hnextValue := wrapping_add_one_exact currentIndex hindexSmall
      have hindexMut := alloc.vec.Vec.index_mut_usize_spec current currentIndex
        hflatBound
      obtain ⟨⟨old, back⟩, hindexMutRun, _hold, hback⟩ :=
        Aeneas.Std.WP.spec_imp_exists hindexMut
      have hdenomRead := alloc.vec.Vec.index_usize_spec denominators
        currentIndex hactive
      obtain ⟨denominator, hdenomRun, hdenominator⟩ :=
        Aeneas.Std.WP.spec_imp_exists hdenomRead
      have hdenominatorEq : denominator =
          denominators.val[currentIndex.val]! := by
        rw [hdenominator,
          getElemBang_eq_getElem denominators.val currentIndex.val hactive]
      subst denominator
      let nextIndex := Std.Usize.wrapping_add currentIndex 1#usize
      let next := current.set currentIndex currentAccumulator
      simp only [if_pos hcondition]
      rw [alloc.vec.Vec.index_mut_slice_index, hindexMutRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hdenomRun]
      simp only [bind_tc_ok]
      rw [hdenominatorEq]
      rw [hmul]
      simp only [bind_tc_ok, Std.lift]
      rw [hback]
      simp only [WP.spec_ok]
      have hnextIndex : nextIndex.val = currentIndex.val + 1 :=
        hnextValue
      have hnextLength : next.val.length = denominators.val.length := by
        simp [next, hlength]
      have hnextCanonical : CanonicalVec next :=
        canonical_set current currentIndex currentAccumulator hcanonical
          hflatBound haccCanonical
      change PrefixInvariant denominators (next, product, nextIndex) ∧
        denominators.val.length - nextIndex.val <
          denominators.val.length - currentIndex.val
      refine ⟨?_, by rw [hnextIndex]; omega⟩
      unfold PrefixInvariant
      simp only
      refine ⟨by omega, hnextLength, hnextCanonical,
        hproductCanonical, ?_, ?_⟩
      · rw [hnextIndex, prefixProduct_succ denominators currentIndex.val
          hactive, ← haccValue]
        change m31Value product =
          m31Value currentAccumulator *
            m31Value denominators.val[currentIndex.val]!
        exact hproductValue
      · intro slot hslot
        change m31Value next.val[slot]! = prefixProduct denominators slot
        by_cases heq : slot = currentIndex.val
        · subst slot
          unfold next
          simp only [alloc.vec.Vec.getElem!_Nat_eq,
            alloc.vec.Vec.set_val_eq, List.getElem!_eq_getElem?_getD]
          simp [hflatBound]
          exact haccValue
        · have hslotOld : slot < currentIndex.val := by omega
          have hslotBound : slot < current.val.length := by omega
          have hslotSetBound :
              slot < (current.val.set currentIndex.val currentAccumulator).length :=
            by simpa using hslotBound
          have hset :
              (current.val.set currentIndex.val currentAccumulator)[slot]! =
                current.val[slot]! := by
            have hne : currentIndex.val ≠ slot := by
              intro hsame
              exact heq hsame.symm
            rw [getElemBang_eq_getElem _ _ hslotSetBound,
              getElemBang_eq_getElem _ _ hslotBound, List.getElem_set]
            simp [hne]
          change m31Value
              (current.val.set currentIndex.val currentAccumulator)[slot]! =
            prefixProduct denominators slot
          rw [hset]
          exact hprefix slot hslotOld
    · have hdone : currentIndex.val = denominators.val.length := by omega
      have hcondition :
          ¬ currentIndex < alloc.vec.Vec.len denominators := by
        simpa [UScalar.lt_equiv] using hactive
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at haccValue hprefix
      exact ⟨hlength, hcanonical, haccCanonical, haccValue, hprefix⟩
  · exact hinvariant

private theorem suffixProduct_at
    (denominators : Coordinate.M31Vec) (index : Nat)
    (hindex : index < denominators.val.length) :
    suffixProduct denominators index =
      m31Value denominators.val[index]! *
        suffixProduct denominators (index + 1) := by
  unfold suffixProduct
  change
    ((denominators.val.drop index).map m31Value).prod =
      m31Value denominators.val[index]! *
        ((denominators.val.drop (index + 1)).map m31Value).prod
  have hmappedIndex :
      index < (denominators.val.map m31Value).length := by
    simpa using hindex
  simp only [List.map_drop]
  rw [List.drop_eq_getElem_cons hmappedIndex]
  simp [getElemBang_eq_getElem denominators.val index hindex]

private def SuffixInvariant
    (denominators : Coordinate.M31Vec) (backend : ZMod P)
    (state : Coordinate.M31Vec × Coordinate.M31 × Std.Usize) : Prop :=
  state.2.2.val ≤ denominators.val.length ∧
  state.1.val.length = denominators.val.length ∧
  CanonicalVec state.1 ∧
  canonicalM31 state.2.1 ∧
  m31Value state.2.1 =
    backend * suffixProduct denominators state.2.2.val ∧
  (∀ index, index < state.2.2.val →
    m31Value state.1.val[index]! = prefixProduct denominators index) ∧
  (∀ index, state.2.2.val ≤ index →
      index < denominators.val.length →
    m31Value state.1.val[index]! =
      prefixProduct denominators index * backend *
        suffixProduct denominators (index + 1))

private def SuffixPost
    (denominators : Coordinate.M31Vec) (backend : ZMod P)
    (out : Coordinate.M31Vec) : Prop :=
  out.val.length = denominators.val.length ∧
  CanonicalVec out ∧
  ∀ index, index < denominators.val.length →
    m31Value out.val[index]! =
      prefixProduct denominators index * backend *
        suffixProduct denominators (index + 1)

/-- The translated backward loop writes the common-backend form of every
inverse output. -/
theorem suffix_loop_exact
    (denominators flat : Coordinate.M31Vec)
    (accumulatorInverse : Coordinate.M31) (suffix : Std.Usize)
    (backend : ZMod P)
    (hdenominators : CanonicalVec denominators)
    (hinvariant :
      SuffixInvariant denominators backend
        (flat, accumulatorInverse, suffix)) :
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18
        denominators flat accumulatorInverse suffix
      ⦃ out => SuffixPost denominators backend out ⦄ := by
  unfold
    V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18
  apply loop.spec_decr_nat
    (fun state => state.2.2.val)
    (SuffixInvariant denominators backend)
    (SuffixPost denominators backend)
  · rintro ⟨current, currentAccumulator, currentSuffix⟩ hstate
    rcases hstate with
      ⟨hsuffixLe, hlength, hcanonical, haccCanonical, haccValue,
        hprefix, houtput⟩
    simp only at hsuffixLe hlength hcanonical haccCanonical haccValue hprefix houtput
    unfold
      V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle_loop18.body
    simp only
    by_cases hactive : 0 < currentSuffix.val
    · have hcondition : currentSuffix > 0#usize := by scalar_tac
      let previous := Std.Usize.wrapping_sub currentSuffix 1#usize
      have hpreviousValue : previous.val = currentSuffix.val - 1 :=
        wrapping_sub_one_exact currentSuffix hactive
      have hpreviousLtSuffix : previous.val < currentSuffix.val := by
        rw [hpreviousValue]
        omega
      have hpreviousBound : previous.val < denominators.val.length := by omega
      have hflatBound : previous.val < current.val.length := by
        rwa [hlength]
      have hprefixCanonical : canonicalM31 current.val[previous.val]! :=
        hcanonical previous.val hflatBound
      have hdenominatorCanonical :
          canonicalM31 denominators.val[previous.val]! :=
        hdenominators previous.val hpreviousBound
      obtain ⟨written, hwrittenRun, hwrittenCanonical, hwrittenValue⟩ :=
        mul_produces_canonical current.val[previous.val]!
          currentAccumulator hprefixCanonical haccCanonical
      obtain ⟨nextAccumulator, hnextAccumulatorRun,
          hnextAccumulatorCanonical, hnextAccumulatorValue⟩ :=
        mul_produces_canonical currentAccumulator
          denominators.val[previous.val]!
          haccCanonical hdenominatorCanonical
      have hprefixRead := alloc.vec.Vec.index_usize_spec current previous
        hflatBound
      obtain ⟨prefixRaw, hprefixRun, hprefixRawEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists hprefixRead
      have hprefixRawBang : prefixRaw = current.val[previous.val]! := by
        rw [hprefixRawEq,
          getElemBang_eq_getElem current.val previous.val hflatBound]
      subst prefixRaw
      have hindexMut := alloc.vec.Vec.index_mut_usize_spec current previous
        hflatBound
      obtain ⟨⟨old, back⟩, hindexMutRun, _hold, hback⟩ :=
        Aeneas.Std.WP.spec_imp_exists hindexMut
      have hdenomRead := alloc.vec.Vec.index_usize_spec denominators previous
        hpreviousBound
      obtain ⟨denominatorRaw, hdenomRun, hdenominatorRawEq⟩ :=
        Aeneas.Std.WP.spec_imp_exists hdenomRead
      have hdenominatorRawBang : denominatorRaw =
          denominators.val[previous.val]! := by
        rw [hdenominatorRawEq,
          getElemBang_eq_getElem denominators.val previous.val
            hpreviousBound]
      subst denominatorRaw
      have hwrittenRunRaw :
          V5FriCoordinateAdapter.aspis_core.field.M31.mul
              current.val[previous.val] currentAccumulator = ok written := by
        rw [hprefixRawBang]
        exact hwrittenRun
      have hnextAccumulatorRunRaw :
          V5FriCoordinateAdapter.aspis_core.field.M31.mul
              currentAccumulator denominators.val[previous.val] =
            ok nextAccumulator := by
        rw [hdenominatorRawBang]
        exact hnextAccumulatorRun
      let next := current.set previous written
      simp only [if_pos hcondition, Std.lift, bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hprefixRun]
      simp only [bind_tc_ok]
      rw [hwrittenRunRaw]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_mut_slice_index, hindexMutRun]
      simp only [bind_tc_ok]
      rw [alloc.vec.Vec.index_slice_index, hdenomRun]
      simp only [bind_tc_ok, hdenominatorRawBang]
      rw [hnextAccumulatorRun]
      simp only [bind_tc_ok]
      rw [hback]
      simp only [WP.spec_ok]
      change
        SuffixInvariant denominators backend
            (next, nextAccumulator, previous) ∧
          previous.val < currentSuffix.val
      refine ⟨?_, hpreviousLtSuffix⟩
      have hnextLength : next.val.length = denominators.val.length := by
        simp [next, hlength]
      have hnextCanonical : CanonicalVec next :=
        canonical_set current previous written hcanonical hflatBound
          hwrittenCanonical
      unfold SuffixInvariant
      simp only
      refine ⟨by omega, hnextLength, hnextCanonical,
        hnextAccumulatorCanonical, ?_, ?_, ?_⟩
      · have hpreviousSucc : previous.val + 1 = currentSuffix.val := by
          omega
        rw [hnextAccumulatorValue, haccValue,
          suffixProduct_at denominators previous.val hpreviousBound,
          hpreviousSucc]
        ring
      · intro slot hslot
        have hslotOld : slot < currentSuffix.val := by omega
        have hslotBound : slot < current.val.length := by omega
        have hslotSetBound :
            slot < (current.val.set previous.val written).length := by
          simpa using hslotBound
        have hne : previous.val ≠ slot := by omega
        have hset :
            (current.val.set previous.val written)[slot]! =
              current.val[slot]! := by
          rw [getElemBang_eq_getElem _ _ hslotSetBound,
            getElemBang_eq_getElem _ _ hslotBound, List.getElem_set]
          simp [hne]
        change m31Value
            (current.val.set previous.val written)[slot]! =
          prefixProduct denominators slot
        rw [hset]
        exact hprefix slot hslotOld
      · intro slot hslotLower hslotUpper
        by_cases heq : slot = previous.val
        · subst slot
          have hpreviousSucc : previous.val + 1 = currentSuffix.val := by
            omega
          change m31Value
              (current.val.set previous.val written)[previous.val]! =
            prefixProduct denominators previous.val * backend *
              suffixProduct denominators (previous.val + 1)
          have hsetBound : previous.val <
              (current.val.set previous.val written).length := by
            simpa using hflatBound
          rw [getElemBang_eq_getElem _ _ hsetBound, List.getElem_set]
          simp
          rw [hwrittenValue,
            hprefix previous.val hpreviousLtSuffix, haccValue,
            hpreviousSucc]
          ring
        · have hslotOldLower : currentSuffix.val ≤ slot := by omega
          have hslotCurrentBound : slot < current.val.length := by
            rwa [hlength]
          have hslotSetBound : slot <
              (current.val.set previous.val written).length := by
            simpa using hslotCurrentBound
          have hne : previous.val ≠ slot := by
            intro hsame
            exact heq hsame.symm
          have hset :
              (current.val.set previous.val written)[slot]! =
                current.val[slot]! := by
            rw [getElemBang_eq_getElem _ _ hslotSetBound,
              getElemBang_eq_getElem _ _ hslotCurrentBound,
              List.getElem_set]
            simp [hne]
          change m31Value
              (current.val.set previous.val written)[slot]! =
            prefixProduct denominators slot * backend *
              suffixProduct denominators (slot + 1)
          rw [hset]
          exact houtput slot hslotOldLower hslotUpper
    · have hdone : currentSuffix.val = 0 := by omega
      have hcondition : ¬ currentSuffix > 0#usize := by scalar_tac
      simp only [if_neg hcondition, WP.spec_ok]
      rw [hdone] at houtput
      exact ⟨hlength, hcanonical, fun index hindex =>
        houtput index (Nat.zero_le index) hindex⟩
  · exact hinvariant

private theorem prefix_suffix_product
    (denominators : Coordinate.M31Vec) (count : Nat)
    (hcount : count ≤ denominators.val.length) :
    prefixProduct denominators count * suffixProduct denominators count =
      prefixProduct denominators denominators.val.length := by
  unfold prefixProduct suffixProduct
  have hsplit := List.take_append_drop count denominators.val
  have htakeAll : denominators.val.take denominators.val.length =
      denominators.val := List.take_length
  rw [htakeAll]
  rw [← List.prod_append, ← List.map_append]
  rw [hsplit]

private theorem entry_prefix_suffix_product
    (denominators : Coordinate.M31Vec) (index : Nat)
    (hindex : index < denominators.val.length) :
    prefixProduct denominators index *
          m31Value denominators.val[index]! *
        suffixProduct denominators (index + 1) =
      prefixProduct denominators denominators.val.length := by
  rw [← prefixProduct_succ denominators index hindex]
  exact prefix_suffix_product denominators (index + 1) (by omega)

/-- Once the source-level first-entry product check succeeds, every value
written by the backward loop is the exact field inverse of the denominator
in the same slot.  The injected inversion backend is not assumed correct. -/
theorem checked_suffix_outputs_are_exact_inverses
    (denominators output : Coordinate.M31Vec) (backend : ZMod P)
    (hpost : SuffixPost denominators backend output)
    (hnonempty : 0 < denominators.val.length)
    (hfirst :
      m31Value denominators.val[0]! * m31Value output.val[0]! = 1) :
    ∀ index, index < denominators.val.length →
      m31Value output.val[index]! =
        (m31Value denominators.val[index]!)⁻¹ := by
  intro index hindex
  rcases hpost with ⟨hlength, _hcanonical, houtput⟩
  have hcommon (slot : Nat) (hslot : slot < denominators.val.length) :
      m31Value denominators.val[slot]! * m31Value output.val[slot]! =
        prefixProduct denominators denominators.val.length * backend := by
    rw [houtput slot hslot]
    rw [← entry_prefix_suffix_product denominators slot hslot]
    ring
  have hproduct :
      m31Value denominators.val[index]! * m31Value output.val[index]! = 1 := by
    rw [hcommon index hindex, ← hcommon 0 hnonempty]
    exact hfirst
  have hnonzero : m31Value denominators.val[index]! ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hproduct
    exact zero_ne_one hproduct
  apply mul_left_cancel₀ hnonzero
  rw [hproduct, mul_inv_cancel₀ hnonzero]

/-- The exact extracted M31 multiplication used by the production check is
enough to discharge the field-level first-entry premise above. -/
theorem checked_suffix_outputs_from_source_product
    (denominators output : Coordinate.M31Vec) (backend : ZMod P)
    (hdenominators : CanonicalVec denominators)
    (hpost : SuffixPost denominators backend output)
    (hnonempty : 0 < denominators.val.length)
    (hsourceCheck :
      V5FriCoordinateAdapter.aspis_core.field.M31.mul
          denominators.val[0]! output.val[0]! =
        .ok V5FriCoordinateAdapter.aspis_core.field.M31.ONE) :
    ∀ index, index < denominators.val.length →
      m31Value output.val[index]! =
        (m31Value denominators.val[index]!)⁻¹ := by
  have houtputCanonical : canonicalM31 output.val[0]! :=
    hpost.2.1 0 (by simpa [hpost.1] using hnonempty)
  have hcheck := mul_corresponds
    denominators.val[0]! output.val[0]!
    V5FriCoordinateAdapter.aspis_core.field.M31.ONE
    (hdenominators 0 hnonempty) houtputCanonical hsourceCheck
  have hone :
      m31Value V5FriCoordinateAdapter.aspis_core.field.M31.ONE = 1 := by
    rfl
  apply checked_suffix_outputs_are_exact_inverses denominators output backend
    hpost hnonempty
  rw [← hcheck.2, hone]

#print axioms prefix_loop_exact
#print axioms suffix_loop_exact
#print axioms checked_suffix_outputs_from_source_product

end AspisV5FriCoordinateInverseLoops
