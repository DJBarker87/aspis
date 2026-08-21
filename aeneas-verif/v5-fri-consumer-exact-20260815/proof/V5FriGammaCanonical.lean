import V5FriTransparentHelperEquality
import V5FriConsumerDecoderBridge
import V5FriDecoderReferenceSemantics
import V5FriDot16ReferenceSemantics

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

/-!
# Canonical outputs of the production layer-zero FRI combination

The consumer extraction originally left four field operations opaque.  Its
external declarations now transport the separately translated unchanged
source bodies.  This file proves the representation facts needed by the
accepted-execution theorem directly from successful calls.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriGammaCanonical

open AspisV5FriArithmeticSemantics
open AspisV5FriConsumerDecoderBridge
open AspisV5FriConsumerValueSemantics
open AspisV5FriDecoderReferenceSemantics
open AspisV5FriDot16ReferenceSemantics
open AspisV5FriFoldSemantics
open AspisV5FriPreparedSumSemantics
open AspisV5FriTransparentHelperEquality
open V5FriConsumerExact

namespace Dot16

open V5FriDot16ReferenceGenerated

private instance : Inhabited
    V5FriDot16ReferenceGenerated.aspis_core.field.QM31 :=
  ⟨⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩⟩

private theorem slot_dot_success_canonical
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize) (slot : Std.Usize)
    (hslot : slot.val < 4)
    (value : V5FriDot16ReferenceGenerated.aspis_core.field.QM31)
    (invalid : Std.U32)
  (hslotCall : V5FriDot16ReferenceGenerated.slot_dot weights bytes slot =
      .ok (value, invalid)) :
    ∀ limb, limb < 4 →
      AspisV5FriDot16ReferenceSemantics.canonicalM31
        (AspisV5FriDot16ReferenceSemantics.qm31Limb value limb) := by
  let b0 := rawBlockArray weights bytes slot.val (0#usize).val
  let b1 := rawBlockArray weights bytes slot.val (4#usize).val
  let b2 := rawBlockArray weights bytes slot.val (8#usize).val
  let b3 := rawBlockArray weights bytes slot.val (12#usize).val
  have hb0 := block4_runs weights bytes slot 0#usize hslot (by norm_num)
  have hb1 := block4_runs weights bytes slot 4#usize hslot (by norm_num)
  have hb2 := block4_runs weights bytes slot 8#usize hslot (by norm_num)
  have hb3 := block4_runs weights bytes slot 12#usize hslot (by norm_num)
  rcases reduce4_corresponds b0 b1 b2 b3 0#usize (by norm_num) with
    ⟨m0, hm0, hm0Canonical, _⟩
  rcases reduce4_corresponds b0 b1 b2 b3 1#usize (by norm_num) with
    ⟨m1, hm1, hm1Canonical, _⟩
  rcases reduce4_corresponds b0 b1 b2 b3 2#usize (by norm_num) with
    ⟨m2, hm2, hm2Canonical, _⟩
  rcases reduce4_corresponds b0 b1 b2 b3 3#usize (by norm_num) with
    ⟨m3, hm3, hm3Canonical, _⟩
  let expected : V5FriDot16ReferenceGenerated.aspis_core.field.QM31 :=
    { c0 := { a := m0, b := m1 }, c1 := { a := m2, b := m3 } }
  let expectedError : Std.U32 :=
    (((blockInvalid bytes slot.val 0 |||
      blockInvalid bytes slot.val 4) |||
      blockInvalid bytes slot.val 8) |||
      blockInvalid bytes slot.val 12)
  have hrun : ∃ error,
      V5FriDot16ReferenceGenerated.slot_dot weights bytes slot =
        .ok (expected, error) := by
    refine ⟨expectedError, ?_⟩
    unfold V5FriDot16ReferenceGenerated.slot_dot
    rw [hb0, hb1, hb2, hb3]
    simp only [bind_tc_ok]
    rw [hm0, hm1, hm2, hm3]
    simp only [bind_tc_ok,
      V5FriDot16ReferenceGenerated.aspis_core.field.CM31.new]
    rfl
  rcases hrun with ⟨error, hrun⟩
  have hvalue : value = expected := by
    have hpairs := Result.ok.inj (hslotCall.symm.trans hrun)
    exact congrArg Prod.fst hpairs
  subst value
  intro limb hlimb
  have hi : limb = 0 ∨ limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact hm0Canonical
  · exact hm1Canonical
  · exact hm2Canonical
  · exact hm3Canonical

theorem indexed_dot16_success_canonical
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Array Std.U8 256#usize)
    (output : Array
      V5FriDot16ReferenceGenerated.aspis_core.field.QM31 4#usize)
    (hcall : V5FriDot16ReferenceGenerated.indexed_dot16 weights bytes =
      .ok (some output)) :
    ∀ slot, slot < 4 → ∀ limb, limb < 4 →
      AspisV5FriDot16ReferenceSemantics.canonicalM31
        (AspisV5FriDot16ReferenceSemantics.qm31Limb
          output.val[slot]! limb) := by
  unfold V5FriDot16ReferenceGenerated.indexed_dot16 at hcall
  generalize h0 : V5FriDot16ReferenceGenerated.slot_dot weights bytes 0#usize =
      result0 at hcall
  cases result0 with
  | fail error => simp [h0, Bind.bind, Aeneas.Std.bind] at hcall
  | div => simp [h0, Bind.bind, Aeneas.Std.bind] at hcall
  | ok pair0 =>
    rcases pair0 with ⟨v0, e0⟩
    simp only [h0, bind_tc_ok] at hcall
    generalize h1 : V5FriDot16ReferenceGenerated.slot_dot weights bytes 1#usize =
        result1 at hcall
    cases result1 with
    | fail error => simp [h1, Bind.bind, Aeneas.Std.bind] at hcall
    | div => simp [h1, Bind.bind, Aeneas.Std.bind] at hcall
    | ok pair1 =>
      rcases pair1 with ⟨v1, e1⟩
      simp only [h1, bind_tc_ok] at hcall
      generalize h2 : V5FriDot16ReferenceGenerated.slot_dot weights bytes 2#usize =
          result2 at hcall
      cases result2 with
      | fail error => simp [h2, Bind.bind, Aeneas.Std.bind] at hcall
      | div => simp [h2, Bind.bind, Aeneas.Std.bind] at hcall
      | ok pair2 =>
        rcases pair2 with ⟨v2, e2⟩
        simp only [h2, bind_tc_ok] at hcall
        generalize h3 : V5FriDot16ReferenceGenerated.slot_dot weights bytes
            3#usize = result3 at hcall
        cases result3 with
        | fail error => simp [h3, Bind.bind, Aeneas.Std.bind] at hcall
        | div => simp [h3, Bind.bind, Aeneas.Std.bind] at hcall
        | ok pair3 =>
          rcases pair3 with ⟨v3, e3⟩
          simp only [h3, bind_tc_ok] at hcall
          simp only [Std.lift, bind_tc_ok] at hcall
          have hzero : (((e0 ||| e1) ||| e2) ||| e3) = 0#u32 := by
            by_contra hne
            simp [hne] at hcall
          simp only [if_pos hzero, Result.ok.injEq,
            Option.some.injEq] at hcall
          have hout : output = Array.make 4#usize [v0, v1, v2, v3] :=
            hcall.symm
          have hc0 := slot_dot_success_canonical weights bytes 0#usize
            (by norm_num) v0 e0 h0
          have hc1 := slot_dot_success_canonical weights bytes 1#usize
            (by norm_num) v1 e1 h1
          have hc2 := slot_dot_success_canonical weights bytes 2#usize
            (by norm_num) v2 e2 h2
          have hc3 := slot_dot_success_canonical weights bytes 3#usize
            (by norm_num) v3 e3 h3
          subst output
          intro slot hslot limb hlimb
          have hs : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
          rcases hs with rfl | rfl | rfl | rfl
          · exact hc0 limb hlimb
          · exact hc1 limb hlimb
          · exact hc2 limb hlimb
          · exact hc3 limb hlimb

end Dot16

theorem arithmetic_prepared_dot_success_canonical
    (left : Array V5FriArithmeticExact.field.PreparedQm31Multiplier 3#usize)
    (right : Array V5FriArithmeticExact.field.QM31 3#usize)
    (output : V5FriArithmeticExact.field.QM31)
    (hcall :
      V5FriArithmeticExact.field.qm31_sum_products3_prepared left right =
        .ok output) :
    canonicalQM31 output := by
  unfold V5FriArithmeticExact.field.qm31_sum_products3_prepared at hcall
  generalize hloop :
      V5FriArithmeticExact.field.qm31_sum_products3_prepared_loop0
        { start := 0#usize, «end» := 3#usize } left right
        (Array.repeat 3#usize (Array.repeat 3#usize 0#u64)) = loopResult
    at hcall
  cases loopResult with
  | fail error => simp [hloop, Bind.bind, Aeneas.Std.bind] at hcall
  | div => simp [hloop, Bind.bind, Aeneas.Std.bind] at hcall
  | ok sums =>
    simp only [hloop, bind_tc_ok] at hcall
    rcases reconstruction_corresponds sums with
      ⟨expected, hexpected, hcanonical, _⟩
    rw [hexpected] at hcall
    have houtput : expected = output := Result.ok.inj hcall
    exact houtput ▸ hcanonical

theorem consumer_decode_success_canonical
    (bytes : Slice Std.U8) (value : aspis_core.field.QM31)
    (hcall : aspis_core.field.QM31.from_le_bytes bytes = .ok (some value)) :
    canonicalQM31 (toExactQM31 value) := by
  have href := consumer_qm31_decode_success_reference bytes value hcall
  have hcanonical := ref_qm31_decode_success_canonical bytes
    (consumerToRefQM31 value) href
  exact hcanonical

theorem consumer_prepared_dot_success_canonical
    (left : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize)
    (output : aspis_core.field.QM31)
    (hcall : aspis_core.field.qm31_sum_products3_prepared left right =
      .ok output) :
    canonicalQM31 (toExactQM31 output) := by
  unfold aspis_core.field.qm31_sum_products3_prepared
    V5FriConsumerExact.HelperTransport.preparedDot at hcall
  generalize hsource :
      V5FriHelperTransparent.aspis_core.field.qm31_sum_products3_prepared
        (V5FriConsumerExact.HelperTransport.mapArray
          V5FriConsumerExact.HelperTransport.toSourcePrepared left)
        (V5FriConsumerExact.HelperTransport.mapArray
          V5FriConsumerExact.HelperTransport.toSourceQM31 right) = sourceResult
      at hcall
  cases sourceResult with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
  | ok sourceOutput =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
      subst output
      have hcanonical := arithmetic_prepared_dot_success_canonical
        (V5FriConsumerExact.HelperTransport.mapArray
          V5FriConsumerExact.HelperTransport.toSourcePrepared left)
        (V5FriConsumerExact.HelperTransport.mapArray
          V5FriConsumerExact.HelperTransport.toSourceQM31 right)
        sourceOutput (by simpa only [source_sum_eq_arithmetic] using hsource)
      simpa using hcanonical

theorem consumer_add_success_canonical
    (left right output : aspis_core.field.QM31)
    (hleft : canonicalQM31 (toExactQM31 left))
    (hright : canonicalQM31 (toExactQM31 right))
    (hcall : aspis_core.field.QM31.add left right = .ok output) :
    canonicalQM31 (toExactQM31 output) := by
  unfold aspis_core.field.QM31.add V5FriConsumerExact.HelperTransport.add at hcall
  generalize hsource :
      V5FriHelperTransparent.aspis_core.field.QM31.add
        (V5FriConsumerExact.HelperTransport.toSourceQM31 left)
        (V5FriConsumerExact.HelperTransport.toSourceQM31 right) = sourceResult
      at hcall
  cases sourceResult with
  | fail error => simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
  | div => simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
  | ok sourceOutput =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
      subst output
      rw [source_qm31_add_eq_arithmetic] at hsource
      rcases qm31_add_corresponds
          (V5FriConsumerExact.HelperTransport.toSourceQM31 left)
          (V5FriConsumerExact.HelperTransport.toSourceQM31 right)
          (by simpa using hleft) (by simpa using hright) with
        ⟨expected, hexpected, hcanonical, _⟩
      rw [hexpected] at hsource
      have : sourceOutput = expected := Result.ok.inj hsource.symm
      subst sourceOutput
      exact hcanonical

theorem consumer_dot16_success_canonical
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (bytes : Slice Std.U8)
    (output : Array aspis_core.field.QM31 4#usize)
    (hcall :
      aspis_core.field.qm31_m31_dot4_prepared_limbs_4b_bytes weights bytes =
        .ok (some output)) :
    CanonicalQM31Array4 (mapArray toExactQM31 output) := by
  unfold aspis_core.field.qm31_m31_dot4_prepared_limbs_4b_bytes
    V5FriConsumerExact.HelperTransport.dot4PreparedLimbs4bBytes at hcall
  split at hcall
  · unfold V5FriConsumerExact.HelperTransport.dot16 at hcall
    split at hcall
    · rename_i hbytes
      generalize href : V5FriDot16ReferenceGenerated.indexed_dot16 weights
          ⟨bytes.val, by simpa [hbytes]⟩ = referenceResult at hcall
      cases referenceResult with
      | fail error =>
        simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
      | div => simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
      | ok option =>
        cases option with
        | none =>
          simp [V5FriConsumerExact.HelperTransport.mapResult] at hcall
        | some referenceOutput =>
          simp only [V5FriConsumerExact.HelperTransport.mapResult, Option.map]
            at hcall
          have hout : output =
              V5FriConsumerExact.HelperTransport.mapArray
                V5FriConsumerExact.HelperTransport.fromDot16QM31
                referenceOutput := by
            exact Option.some.inj (Result.ok.inj hcall).symm
          subst output
          have hcanonical := Dot16.indexed_dot16_success_canonical weights
            ⟨bytes.val, by simpa [hbytes]⟩ referenceOutput href
          intro slot hslot
          have h0 := hcanonical slot hslot 0 (by norm_num)
          have h1 := hcanonical slot hslot 1 (by norm_num)
          have h2 := hcanonical slot hslot 2 (by norm_num)
          have h3 := hcanonical slot hslot 3 (by norm_num)
          rw [mapArray_entry4 toExactQM31 _ ⟨slot, hslot⟩]
          have hentry :
              (V5FriConsumerExact.HelperTransport.mapArray
                V5FriConsumerExact.HelperTransport.fromDot16QM31
                referenceOutput).val[slot]! =
                V5FriConsumerExact.HelperTransport.fromDot16QM31
                  referenceOutput.val[slot]! := by
            simp [V5FriConsumerExact.HelperTransport.mapArray, hslot]
          rw [hentry]
          simpa [
            V5FriConsumerExact.HelperTransport.fromDot16QM31,
            toExactQM31, toExactCM31, canonicalQM31, canonicalCM31,
            AspisV5FriArithmeticSemantics.canonicalM31,
            AspisAeneasCM31Multiplicative.CanonicalRawM31,
            AspisV5FriDot16ReferenceSemantics.canonicalM31,
            AspisV5FriDot16ReferenceSemantics.modulus,
            AspisAeneasM31ReduceU64.m31Modulus,
            AspisAeneasCM31Multiplicative.m31Modulus,
            AspisV5FriDot16ReferenceSemantics.qm31Limb] using
              And.intro (And.intro h0 h1) (And.intro h2 h3)
    · simp at hcall
  · simp at hcall

private abbrev ConsumerQM31 := V5FriConsumerExact.aspis_core.field.QM31
private abbrev ConsumerIter := core.slice.iter.IterMut ConsumerQM31
private abbrev ConsumerEnumerate :=
  core.iter.adapters.enumerate.Enumerate ConsumerIter

def consumerWriteBackAt (position : Nat) (current : ConsumerEnumerate)
    (replacement : Option (Std.Usize × ConsumerQM31)) : ConsumerEnumerate :=
  { current with
    iter :=
      match replacement.map Prod.snd with
      | none => current.iter
      | some value =>
          { current.iter with
            slice := current.iter.slice.setAtNat position value } }

theorem consumer_iter_mut_next_active
    (iter : ConsumerIter) (hactive : iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (some iter.slice[iter.i], { iter with i := iter.i + 1 },
        fun current replacement =>
          match replacement with
          | none => current
          | some value =>
              { current with
                slice := current.slice.setAtNat iter.i value }) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_pos hactive]
  simp only
  congr 1
  congr 1
  congr 1
  funext current replacement
  cases replacement
  · rfl
  · cases current
    rfl

theorem consumer_iter_mut_next_done
    (iter : ConsumerIter) (hdone : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (none, iter, fun current _ => current) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_neg hdone]

theorem consumer_enumerate_next_active
    (state : ConsumerEnumerate) (nextCount : Std.Usize)
    (hactive : state.iter.i < state.iter.slice.len)
    (hcount : state.count + 1#usize = (.ok nextCount : Result Std.Usize)) :
    V5FriConsumerExact.iterMutEnumerateNext state =
      .ok (some (state.count, state.iter.slice[state.iter.i]),
        { iter := { state.iter with i := state.iter.i + 1 },
          count := nextCount },
        consumerWriteBackAt state.iter.i) := by
  unfold V5FriConsumerExact.iterMutEnumerateNext
  have hnext := consumer_iter_mut_next_active state.iter hactive
  rw [hnext]
  simp only [bind_tc_ok]
  rw [hcount]
  simp only [bind_tc_ok]
  rfl

theorem consumer_enumerate_next_done
    (state : ConsumerEnumerate)
    (hdone : ¬ state.iter.i < state.iter.slice.len) :
    V5FriConsumerExact.iterMutEnumerateNext state =
      .ok (none, state, fun current _ => current) := by
  unfold V5FriConsumerExact.iterMutEnumerateNext
  rw [consumer_iter_mut_next_done state.iter hdone]
  simp only [bind_tc_ok]

theorem consumer_usize_add_one_ok
    (current next : Std.Usize)
    (hvalue : current.val + 1 = next.val)
    (hbound : current.val + 1 < 2 ^ System.Platform.numBits) :
    current + 1#usize = (.ok next : Result Std.Usize) := by
  have hadd := @UScalar.add_equiv UScalarTy.Usize current 1#usize
  generalize heq : (current + 1#usize) = addResult at hadd ⊢
  cases addResult with
  | fail error =>
    exfalso
    apply hadd
    simpa using hbound
  | div => exact False.elim hadd
  | ok value =>
    have hvalue' : value.val = next.val := by
      calc
        value.val = current.val + (1#usize).val := hadd.2.1
        _ = current.val + 1 := by rfl
        _ = next.val := hvalue
    have : value = next := UScalar.val_eq_imp value next hvalue'
    simp [this]

def runGammaFinalLoop
    (initial : Array ConsumerQM31 4#usize)
    (multipliers : Array
      V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier 3#usize)
    (helperValues : Array (Array ConsumerQM31 3#usize) 4#usize) :
    Result (Array ConsumerQM31 4#usize) := do
  let (slice, toSliceBack) ← lift (Array.to_slice_mut initial)
  let (iterMut, iterMutBack) ← core.slice.Slice.iter_mut slice
  let (iter, enumerateBack) ← V5FriConsumerExact.iterMutEnumerate iterMut
  let (finished, back) ←
    V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop1
      iter (fun state => state) multipliers helperValues
  let resumed := back finished
  let iterMut1 := enumerateBack resumed
  let slice1 := iterMutBack iterMut1
  ok (toSliceBack slice1)

private abbrev HelperRow := Array ConsumerQM31 3#usize
private abbrev HelperValues := Array HelperRow 4#usize
private abbrev HelperIter := core.slice.iter.IterMut HelperRow
private abbrev HelperEnumerate :=
  core.iter.adapters.enumerate.Enumerate HelperIter

def helperWriteBackAt (position : Nat) (current : HelperEnumerate)
    (replacement : Option (Std.Usize × HelperRow)) : HelperEnumerate :=
  { current with
    iter :=
      match replacement.map Prod.snd with
      | none => current.iter
      | some value =>
          { current.iter with
            slice := current.iter.slice.setAtNat position value } }

theorem helper_iter_mut_next_active
    (iter : HelperIter) (hactive : iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (some iter.slice[iter.i], { iter with i := iter.i + 1 },
        fun current replacement =>
          match replacement with
          | none => current
          | some value =>
              { current with
                slice := current.slice.setAtNat iter.i value }) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_pos hactive]
  simp only
  congr 1
  congr 1
  congr 1
  funext current replacement
  cases replacement
  · rfl
  · cases current
    rfl

theorem helper_iter_mut_next_done
    (iter : HelperIter) (hdone : ¬ iter.i < iter.slice.len) :
    core.slice.iter.IteratorIterMut.next iter =
      .ok (none, iter, fun current _ => current) := by
  unfold core.slice.iter.IteratorIterMut.next
  rw [dif_neg hdone]

theorem helper_enumerate_next_active
    (state : HelperEnumerate) (nextCount : Std.Usize)
    (hactive : state.iter.i < state.iter.slice.len)
    (hcount : state.count + 1#usize = (.ok nextCount : Result Std.Usize)) :
    V5FriConsumerExact.iterMutEnumerateNext state =
      .ok (some (state.count, state.iter.slice[state.iter.i]),
        { iter := { state.iter with i := state.iter.i + 1 },
          count := nextCount },
        helperWriteBackAt state.iter.i) := by
  unfold V5FriConsumerExact.iterMutEnumerateNext
  rw [helper_iter_mut_next_active state.iter hactive]
  simp only [bind_tc_ok]
  rw [hcount]
  simp only [bind_tc_ok]
  rfl

theorem helper_enumerate_next_done
    (state : HelperEnumerate)
    (hdone : ¬ state.iter.i < state.iter.slice.len) :
    V5FriConsumerExact.iterMutEnumerateNext state =
      .ok (none, state, fun current _ => current) := by
  unfold V5FriConsumerExact.iterMutEnumerateNext
  rw [helper_iter_mut_next_done state.iter hdone]
  simp only [bind_tc_ok]

def pendingNeverOk
    (pending : Option (core.result.Result (Array ConsumerQM31 4#usize)
      V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError)) :
    Prop :=
  match pending with
  | none => True
  | some (.Err _) => True
  | some (.Ok _) => False

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

theorem gamma_c2_inner_body_success
    (state : HelperEnumerate)
    (currentBack : HelperEnumerate → HelperEnumerate)
    (c2Leaf : Slice Std.U8) (helper : Std.Usize)
    (flow : ControlFlow
      (HelperEnumerate × (HelperEnumerate → HelperEnumerate))
      ((Option (core.result.Result (Array ConsumerQM31 4#usize)
        V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError))
        × HelperEnumerate))
    (hRun :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0.body
        c2Leaf helper state currentBack = .ok flow) :
    match flow with
    | .done result => pendingNeverOk result.1
    | .cont next =>
        next.1.iter.slice.len - next.1.iter.i <
          state.iter.slice.len - state.iter.i := by
  by_cases hactive : state.iter.i < state.iter.slice.len
  · generalize hcount : state.count + 1#usize = countResult
    cases countResult with
    | fail error =>
      unfold
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0.body
        V5FriConsumerExact.iterMutEnumerateNext at hRun
      rw [helper_iter_mut_next_active state.iter hactive] at hRun
      simp [hcount, Bind.bind, Aeneas.Std.bind] at hRun
    | div =>
      unfold
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0.body
        V5FriConsumerExact.iterMutEnumerateNext at hRun
      rw [helper_iter_mut_next_active state.iter hactive] at hRun
      simp [hcount, Bind.bind, Aeneas.Std.bind] at hRun
    | ok nextCount =>
      have hnext := helper_enumerate_next_active state nextCount
        hactive hcount
      unfold
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0.body
        at hRun
      rw [hnext] at hRun
      simp only [bind_tc_ok] at hRun
      simp only [Std.lift, bind_tc_ok] at hRun
      generalize hslice :
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) c2Leaf
            { start := _, «end» := _ } = sliceResult at hRun
      cases sliceResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
      | ok selected =>
        simp only [bind_tc_ok] at hRun
        generalize hdecode :
            V5FriConsumerExact.aspis_core.field.QM31.from_le_bytes selected =
              decodeResult at hRun
        cases decodeResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
        | ok decoded =>
          cases decoded with
          | none =>
            simp [V5FriConsumerExact.core.option.Option.ok_or,
              pendingNeverOk] at hRun
            symm at hRun
            subst flow
            trivial
          | some value =>
            simp [V5FriConsumerExact.core.option.Option.ok_or] at hRun
            generalize hindex :
                Array.index_mut_usize state.iter.slice[state.iter.i] helper =
                  indexResult at hRun
            cases indexResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
            | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
            | ok pair =>
              rcases pair with ⟨old, indexBack⟩
              simp only [bind_tc_ok] at hRun
              have hflow := Result.ok.inj hRun
              symm at hflow
              subst flow
              simp only
              omega
  · unfold
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0.body
      at hRun
    rw [helper_enumerate_next_done state hactive] at hRun
    simp only [bind_tc_ok] at hRun
    have hflow := Result.ok.inj hRun
    symm at hflow
    subst flow
    trivial

theorem gamma_c2_inner_loop_success
    (state : HelperEnumerate)
    (currentBack : HelperEnumerate → HelperEnumerate)
    (c2Leaf : Slice Std.U8) (helper : Std.Usize)
    (pending : Option (core.result.Result (Array ConsumerQM31 4#usize)
      V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError))
    (finished : HelperEnumerate)
    (hRun :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0
        state currentBack c2Leaf helper = .ok (pending, finished)) :
    pendingNeverOk pending := by
  unfold
    V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0
    at hRun
  rw [loop.eq_def] at hRun
  simp only [Prod.fst, Prod.snd] at hRun
  generalize hbody :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0.body
        c2Leaf helper state currentBack = bodyResult at hRun
  cases bodyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
  | ok flow =>
    have hstep := gamma_c2_inner_body_success
      state currentBack c2Leaf helper flow hbody
    simp only [bind_tc_ok] at hRun
    cases flow with
    | done result =>
      have heq := Result.ok.inj hRun
      cases heq
      exact hstep
    | cont next =>
      change
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0
          next.1 next.2 c2Leaf helper = .ok (pending, finished) at hRun
      exact gamma_c2_inner_loop_success
        next.1 next.2 c2Leaf helper pending finished hRun
termination_by state.iter.slice.len.val - state.iter.i
decreasing_by exact hstep

theorem gamma_c2_outer_body_success
    (iter : core.ops.range.Range Std.Usize)
    (helperValues : HelperValues) (c2Leaf : Slice Std.U8)
    (flow : ControlFlow
      (core.ops.range.Range Std.Usize × HelperValues)
      (HelperValues × Option (core.result.Result
        (Array ConsumerQM31 4#usize)
        V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError)))
    (hRun :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0.body
        c2Leaf iter helperValues = .ok flow) :
    match flow with
    | .done result => pendingNeverOk result.2
    | .cont next =>
        next.1.end.val - next.1.start.val <
          iter.end.val - iter.start.val := by
  by_cases hactive : iter.start.val < iter.end.val
  · have hspec := core.iter.range.IteratorRange.next_Usize_some_spec
      iter hactive
    obtain ⟨⟨option, iterNext⟩, hnext, hoption, hnextStart, hnextEnd⟩ :=
      Aeneas.Std.WP.spec_imp_exists hspec
    rw [hoption] at hnext
    unfold
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0.body
      at hRun
    rw [hnext] at hRun
    simp only [bind_tc_ok, Aeneas.Std.lift, Array.to_slice_mut,
      Array.to_slice, core.slice.Slice.iter_mut,
      V5FriConsumerExact.iterMutEnumerate] at hRun
    let state0 : HelperEnumerate :=
      { iter := { slice := helperValues.to_slice }, count := 0#usize }
    change
      (do
        let result ←
          V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0
            state0 (fun state => state) c2Leaf iter.start
        match result.1 with
        | none =>
          ok (cont (iterNext,
            Array.from_slice helperValues result.2.iter.slice))
        | some value =>
          ok (done
            (Array.from_slice helperValues result.2.iter.slice, result.1))) =
        .ok flow at hRun
    generalize hinner :
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0_loop0
          state0 (fun state => state) c2Leaf iter.start = innerResult at hRun
    cases innerResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
    | ok pair =>
      rcases pair with ⟨pending, finished⟩
      simp only [bind_tc_ok] at hRun
      have hpending := gamma_c2_inner_loop_success
        state0 (fun state => state) c2Leaf iter.start pending finished hinner
      cases pending with
      | none =>
        have hflow := Result.ok.inj hRun
        symm at hflow
        subst flow
        simp only
        rw [hnextStart, hnextEnd]
        omega
      | some result =>
        cases result with
        | Err error =>
          have hflow := Result.ok.inj hRun
          symm at hflow
          subst flow
          trivial
        | Ok value =>
          simp [pendingNeverOk] at hpending
  · have hspec := core.iter.range.IteratorRange.next_Usize_none_spec
      iter (by omega)
    obtain ⟨⟨option, iterNext⟩, hnext, hoption, hsame⟩ :=
      Aeneas.Std.WP.spec_imp_exists hspec
    rw [hoption, hsame] at hnext
    unfold
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0.body
      at hRun
    rw [hnext] at hRun
    simp only [bind_tc_ok] at hRun
    have hflow := Result.ok.inj hRun
    symm at hflow
    subst flow
    trivial

theorem gamma_c2_outer_loop_success
    (iter : core.ops.range.Range Std.Usize)
    (helperValues output : HelperValues) (c2Leaf : Slice Std.U8)
    (pending : Option (core.result.Result (Array ConsumerQM31 4#usize)
      V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError))
    (hRun :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0
        iter c2Leaf helperValues = .ok (output, pending)) :
    pendingNeverOk pending := by
  unfold V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0
    at hRun
  rw [loop.eq_def] at hRun
  simp only [Prod.fst, Prod.snd] at hRun
  generalize hbody :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0.body
        c2Leaf iter helperValues = bodyResult at hRun
  cases bodyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
  | ok flow =>
    have hstep := gamma_c2_outer_body_success
      iter helperValues c2Leaf flow hbody
    simp only [bind_tc_ok] at hRun
    cases flow with
    | done result =>
      have heq := Result.ok.inj hRun
      cases heq
      exact hstep
    | cont next =>
      change
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0
          next.1 c2Leaf next.2 = .ok (output, pending) at hRun
      exact gamma_c2_outer_loop_success
        next.1 next.2 output c2Leaf pending hRun
termination_by iter.end.val - iter.start.val
decreasing_by exact hstep

theorem runGammaFinalLoop_success_canonical
    (initial combined : Array ConsumerQM31 4#usize)
    (multipliers : Array
      V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier 3#usize)
    (helperValues : Array (Array ConsumerQM31 3#usize) 4#usize)
    (hInitial : CanonicalQM31Array4 (mapArray toExactQM31 initial))
    (hRun : runGammaFinalLoop initial multipliers helperValues = .ok combined) :
    CanonicalQM31Array4 (mapArray toExactQM31 combined) := by
  unfold runGammaFinalLoop at hRun
  simp only [V5FriConsumerExact.iterMutEnumerate,
    core.slice.Slice.iter_mut, Array.to_slice_mut, Array.to_slice,
    Aeneas.Std.lift, bind_tc_ok] at hRun
  let state0 : ConsumerEnumerate :=
    { iter := { slice := initial.to_slice }, count := 0#usize }
  change
    (do
      let (finished, back) ←
        V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop1
          state0 (fun state => state) multipliers helperValues
      ok (Array.from_slice initial (back finished).iter.slice)) =
      .ok combined at hRun
  generalize hloop :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop1
        state0 (fun state => state) multipliers helperValues = loopResult
    at hRun
  cases loopResult with
  | fail error => simp [hloop, Bind.bind, Aeneas.Std.bind] at hRun
  | div => simp [hloop, Bind.bind, Aeneas.Std.bind] at hRun
  | ok pair =>
    rcases pair with ⟨finished, back⟩
    simp only [hloop, bind_tc_ok] at hRun
    unfold
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop1
      at hloop
    rw [loop.eq_def] at hloop
    unfold
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop1.body
      at hloop
    have hactive0 : state0.iter.i < state0.iter.slice.len := by
      simp [state0, Array.to_slice, Slice.len]
    have hcount0 :
        state0.count + 1#usize = (.ok 1#usize : Result Std.Usize) := by
      apply consumer_usize_add_one_ok
      · rfl
      · cases hbits : System.Platform.numBits_eq <;> simp_all [state0]
    have hnext0 :=
      consumer_enumerate_next_active state0 1#usize hactive0 hcount0
    simp only [hnext0, bind_tc_ok] at hloop
    simp only [state0] at hloop
    have hindex0 :
        Array.index_usize helperValues 0#usize =
          .ok helperValues.val[0]! := by
      simp [Array.index_usize]
    rw [hindex0] at hloop
    simp only [bind_tc_ok] at hloop
    generalize hdot0 :
        V5FriConsumerExact.aspis_core.field.qm31_sum_products3_prepared
          multipliers helperValues.val[0]! = dotResult0 at hloop
    cases dotResult0 with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
    | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
    | ok q0 =>
      simp only [bind_tc_ok] at hloop
      have hq0 := consumer_prepared_dot_success_canonical
        multipliers helperValues.val[0]! q0 hdot0
      generalize hadd0 :
          V5FriConsumerExact.aspis_core.field.QM31.add
            initial.to_slice[0] q0 = addResult0 at hloop
      cases addResult0 with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
      | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
      | ok value0 =>
        simp only [bind_tc_ok] at hloop
        have hinitial0 := hInitial 0 (by norm_num)
        rw [mapArray_entry4 toExactQM31 initial ⟨0, by norm_num⟩]
          at hinitial0
        have hadd0' :
            V5FriConsumerExact.aspis_core.field.QM31.add
              initial.val[0]! q0 = .ok value0 := by
          simpa [Array.to_slice] using hadd0
        have hvalue0 := consumer_add_success_canonical
          initial.val[0]! q0 value0 hinitial0 hq0 hadd0'
        rw [loop.eq_def] at hloop
        let state1 : ConsumerEnumerate :=
          { iter := { slice := initial.to_slice, i := 1 }, count := 1#usize }
        have hactive1 : state1.iter.i < state1.iter.slice.len := by
          simp [state1, Array.to_slice, Slice.len]
        have hcount1 :
            state1.count + 1#usize = (.ok 2#usize : Result Std.Usize) := by
          apply consumer_usize_add_one_ok
          · rfl
          · cases hbits : System.Platform.numBits_eq <;> simp_all [state1]
        have hnext1 :=
          consumer_enumerate_next_active state1 2#usize hactive1 hcount1
        have hnext1' := hnext1
        simp only [state1] at hnext1'
        simp only [Prod.fst, Prod.snd, Nat.zero_add] at hloop
        simp only [hnext1', bind_tc_ok] at hloop
        simp only [state1, Nat.one_add] at hloop
        have hindex1 :
            Array.index_usize helperValues 1#usize =
              .ok helperValues.val[1]! := by
          simp [Array.index_usize]
        rw [hindex1] at hloop
        simp only [bind_tc_ok] at hloop
        generalize hdot1 :
            V5FriConsumerExact.aspis_core.field.qm31_sum_products3_prepared
              multipliers helperValues.val[1]! = dotResult1 at hloop
        cases dotResult1 with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
        | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
        | ok q1 =>
          simp only [bind_tc_ok] at hloop
          have hq1 := consumer_prepared_dot_success_canonical
            multipliers helperValues.val[1]! q1 hdot1
          generalize hadd1 :
              V5FriConsumerExact.aspis_core.field.QM31.add
                initial.to_slice[1] q1 = addResult1 at hloop
          cases addResult1 with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
          | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
          | ok value1 =>
            simp only [bind_tc_ok] at hloop
            have hinitial1 := hInitial 1 (by norm_num)
            rw [mapArray_entry4 toExactQM31 initial ⟨1, by norm_num⟩]
              at hinitial1
            have hadd1' :
                V5FriConsumerExact.aspis_core.field.QM31.add
                  initial.val[1]! q1 = .ok value1 := by
              simpa [Array.to_slice] using hadd1
            have hvalue1 := consumer_add_success_canonical
              initial.val[1]! q1 value1 hinitial1 hq1 hadd1'
            rw [loop.eq_def] at hloop
            let state2 : ConsumerEnumerate :=
              { iter := { slice := initial.to_slice, i := 2 },
                count := 2#usize }
            have hactive2 : state2.iter.i < state2.iter.slice.len := by
              simp [state2, Array.to_slice, Slice.len]
            have hcount2 :
                state2.count + 1#usize = (.ok 3#usize : Result Std.Usize) := by
              apply consumer_usize_add_one_ok
              · rfl
              · cases hbits : System.Platform.numBits_eq <;>
                  simp_all [state2]
            have hnext2 :=
              consumer_enumerate_next_active state2 3#usize hactive2 hcount2
            have hnext2' := hnext2
            simp only [state2] at hnext2'
            simp only [hnext2', bind_tc_ok] at hloop
            have hindex2 :
                Array.index_usize helperValues 2#usize =
                  .ok helperValues.val[2]! := by
              simp [Array.index_usize]
            rw [hindex2] at hloop
            simp only [bind_tc_ok] at hloop
            generalize hdot2 :
                V5FriConsumerExact.aspis_core.field.qm31_sum_products3_prepared
                  multipliers helperValues.val[2]! = dotResult2 at hloop
            cases dotResult2 with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
            | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
            | ok q2 =>
              simp only [bind_tc_ok] at hloop
              have hq2 := consumer_prepared_dot_success_canonical
                multipliers helperValues.val[2]! q2 hdot2
              generalize hadd2 :
                  V5FriConsumerExact.aspis_core.field.QM31.add
                    initial.to_slice[2] q2 = addResult2 at hloop
              cases addResult2 with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
              | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
              | ok value2 =>
                simp only [bind_tc_ok] at hloop
                have hinitial2 := hInitial 2 (by norm_num)
                rw [mapArray_entry4 toExactQM31 initial ⟨2, by norm_num⟩]
                  at hinitial2
                have hadd2' :
                    V5FriConsumerExact.aspis_core.field.QM31.add
                      initial.val[2]! q2 = .ok value2 := by
                  simpa [Array.to_slice] using hadd2
                have hvalue2 := consumer_add_success_canonical
                  initial.val[2]! q2 value2 hinitial2 hq2 hadd2'
                rw [loop.eq_def] at hloop
                let state3 : ConsumerEnumerate :=
                  { iter := { slice := initial.to_slice, i := 3 },
                    count := 3#usize }
                have hactive3 : state3.iter.i < state3.iter.slice.len := by
                  simp [state3, Array.to_slice, Slice.len]
                have hcount3 :
                    state3.count + 1#usize =
                      (.ok 4#usize : Result Std.Usize) := by
                  apply consumer_usize_add_one_ok
                  · rfl
                  · cases hbits : System.Platform.numBits_eq <;>
                      simp_all [state3]
                have hnext3 := consumer_enumerate_next_active state3 4#usize
                  hactive3 hcount3
                have hnext3' := hnext3
                simp only [state3] at hnext3'
                simp only [hnext3', bind_tc_ok] at hloop
                have hindex3 :
                    Array.index_usize helperValues 3#usize =
                      .ok helperValues.val[3]! := by
                  simp [Array.index_usize]
                rw [hindex3] at hloop
                simp only [bind_tc_ok] at hloop
                generalize hdot3 :
                    V5FriConsumerExact.aspis_core.field.qm31_sum_products3_prepared
                      multipliers helperValues.val[3]! = dotResult3 at hloop
                cases dotResult3 with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
                | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
                | ok q3 =>
                  simp only [bind_tc_ok] at hloop
                  have hq3 := consumer_prepared_dot_success_canonical
                    multipliers helperValues.val[3]! q3 hdot3
                  generalize hadd3 :
                      V5FriConsumerExact.aspis_core.field.QM31.add
                        initial.to_slice[3] q3 = addResult3 at hloop
                  cases addResult3 with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
                  | ok value3 =>
                    simp only [bind_tc_ok] at hloop
                    have hinitial3 := hInitial 3 (by norm_num)
                    rw [mapArray_entry4 toExactQM31 initial ⟨3, by norm_num⟩]
                      at hinitial3
                    have hadd3' :
                        V5FriConsumerExact.aspis_core.field.QM31.add
                          initial.val[3]! q3 = .ok value3 := by
                      simpa [Array.to_slice] using hadd3
                    have hvalue3 := consumer_add_success_canonical
                      initial.val[3]! q3 value3 hinitial3 hq3 hadd3'
                    rw [loop.eq_def] at hloop
                    let state4 : ConsumerEnumerate :=
                      { iter := { slice := initial.to_slice, i := 4 },
                        count := 4#usize }
                    have hdone4 :
                        ¬ state4.iter.i < state4.iter.slice.len := by
                      simp [state4, Array.to_slice, Slice.len]
                    have hnext4 := consumer_enumerate_next_done state4 hdone4
                    have hnext4' := hnext4
                    simp only [state4] at hnext4'
                    simp only [hnext4', bind_tc_ok] at hloop
                    let finalBack : ConsumerEnumerate → ConsumerEnumerate :=
                      fun state =>
                        consumerWriteBackAt 0
                          (consumerWriteBackAt 1
                            (consumerWriteBackAt 2
                              (consumerWriteBackAt 3 state
                                (some (3#usize, value3)))
                              (some (2#usize, value2)))
                            (some (1#usize, value1)))
                          (some (0#usize, value0))
                    have hpair : (state4, finalBack) = (finished, back) := by
                      exact Result.ok.inj hloop
                    have hfinished : finished = state4 :=
                      (congrArg Prod.fst hpair).symm
                    have hback : back = finalBack :=
                      (congrArg Prod.snd hpair).symm
                    subst finished
                    subst back
                    have hcombined :
                        Array.from_slice initial (finalBack state4).iter.slice =
                          combined := Result.ok.inj hRun
                    rw [← hcombined]
                    intro index hindex
                    have hi : index = 0 ∨ index = 1 ∨ index = 2 ∨
                        index = 3 := by omega
                    rcases hi with rfl | rfl | rfl | rfl
                    · simpa [CanonicalQM31Array4, mapArray, finalBack, state4,
                        consumerWriteBackAt, Array.from_slice,
                        Slice.setAtNat, Array.to_slice] using hvalue0
                    · simpa [CanonicalQM31Array4, mapArray, finalBack, state4,
                        consumerWriteBackAt, Array.from_slice,
                        Slice.setAtNat, Array.to_slice] using hvalue1
                    · simpa [CanonicalQM31Array4, mapArray, finalBack, state4,
                        consumerWriteBackAt, Array.from_slice,
                        Slice.setAtNat, Array.to_slice] using hvalue2
                    · simpa [CanonicalQM31Array4, mapArray, finalBack, state4,
                        consumerWriteBackAt, Array.from_slice,
                        Slice.setAtNat, Array.to_slice] using hvalue3

theorem gamma_combine_success_canonical
    (c1Leaf c2Leaf : Slice Std.U8)
    (prepared : V5FriConsumerExact.fri_checks.V5PreparedPcsClaims)
    (combined : Array ConsumerQM31 4#usize)
    (hRun :
      V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact
        c1Leaf c2Leaf prepared = .ok (.Ok combined)) :
    CanonicalQM31Array4 (mapArray toExactQM31 combined) := by
  unfold V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact at hRun
  generalize hc1Expected :
      Array.index_usize
        V5FriConsumerExact.private_openings.V5_PRIVATE_VALUE_WIDTHS 0#usize =
        c1ExpectedResult at hRun
  cases c1ExpectedResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
  | ok c1Expected =>
    simp only [bind_tc_ok] at hRun
    generalize hc2Expected :
        Array.index_usize
          V5FriConsumerExact.private_openings.V5_PRIVATE_VALUE_WIDTHS 1#usize =
          c2ExpectedResult at hRun
    cases c2ExpectedResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
    | ok c2Expected =>
      simp only [bind_tc_ok] at hRun
      by_cases hc1Length : Slice.len c1Leaf != c1Expected
      · rw [if_pos hc1Length] at hRun
        simp at hRun
      · rw [if_neg hc1Length] at hRun
        by_cases hc2Length : Slice.len c2Leaf != c2Expected
        · rw [if_pos hc2Length] at hRun
          simp at hRun
        · rw [if_neg hc2Length] at hRun
          generalize hc1Dot :
              V5FriConsumerExact.aspis_core.field.qm31_m31_dot4_prepared_limbs_4b_bytes
                prepared.c1_weight_limbs c1Leaf = c1DotResult at hRun
          cases c1DotResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
          | ok c1Option =>
            cases c1Option with
            | none =>
              simp [V5FriConsumerExact.core.option.Option.ok_or_else,
                V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePcsDecodeError.call_once]
                at hRun
              generalize hfirst :
                  V5FriConsumerExact.fri_checks.first_noncanonical_m31_offset
                    c1Leaf = firstResult at hRun
              cases firstResult <;> simp [Bind.bind, Aeneas.Std.bind] at hRun
            | some initial =>
              have hinitial := consumer_dot16_success_canonical
                prepared.c1_weight_limbs c1Leaf initial hc1Dot
              simp [V5FriConsumerExact.core.option.Option.ok_or_else] at hRun
              generalize hzero :
                  V5FriConsumerExact.aspis_core.field.QM31.ZERO = zeroResult
                  at hRun
              cases zeroResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
              | ok zero =>
                simp only [bind_tc_ok] at hRun
                let helperValues : HelperValues :=
                  Array.repeat 4#usize (Array.repeat 3#usize zero)
                generalize houter :
                    V5FriConsumerExact.fri_checks.gamma_combine_v5_layer0_exact_loop0
                      { start := 0#usize,
                        «end» := V5FriConsumerExact.fri_checks.V5_FRI_C2_COLUMNS }
                      c2Leaf helperValues = outerResult at hRun
                cases outerResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hRun
                | div => simp [Bind.bind, Aeneas.Std.bind] at hRun
                | ok pair =>
                  rcases pair with ⟨helperValues1, pending⟩
                  simp only [bind_tc_ok] at hRun
                  have hpending := gamma_c2_outer_loop_success
                    { start := 0#usize,
                      «end» := V5FriConsumerExact.fri_checks.V5_FRI_C2_COLUMNS }
                    helperValues helperValues1 c2Leaf pending houter
                  cases pending with
                  | none =>
                    simp only at hRun
                    have hwrapped :
                      (do
                        let combined' ← runGammaFinalLoop initial
                          prepared.c2_multipliers helperValues1
                        ok (core.result.Result.Ok combined' :
                          core.result.Result (Array ConsumerQM31 4#usize)
                            V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError)) =
                        .ok (core.result.Result.Ok combined :
                          core.result.Result (Array ConsumerQM31 4#usize)
                            V5FriConsumerExact.aspis_core.circle_pcs_shape.CirclePcsDecodeError) := by
                      simpa [runGammaFinalLoop] using hRun
                    generalize hfinal :
                        runGammaFinalLoop initial prepared.c2_multipliers
                          helperValues1 = finalResult at hwrapped
                    cases finalResult with
                    | fail error =>
                      simp [Bind.bind, Aeneas.Std.bind] at hwrapped
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hwrapped
                    | ok output =>
                      have houterEq := Result.ok.inj hwrapped
                      have houtput : output = combined :=
                        core.result.Result.Ok.inj houterEq
                      rw [← houtput]
                      exact runGammaFinalLoop_success_canonical
                        initial output prepared.c2_multipliers helperValues1
                        hinitial hfinal
                  | some result =>
                    cases result with
                    | Err error => simp at hRun
                    | Ok value => simp [pendingNeverOk] at hpending

#print axioms consumer_decode_success_canonical
#print axioms consumer_prepared_dot_success_canonical
#print axioms consumer_add_success_canonical
#print axioms consumer_dot16_success_canonical

end AspisV5FriGammaCanonical
