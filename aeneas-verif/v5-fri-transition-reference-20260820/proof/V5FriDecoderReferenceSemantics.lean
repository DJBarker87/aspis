import V5FriDecoderReference.Funs
import V5FriTransitionSemantics

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriDecoderReferenceSemantics

open AspisV5FriArithmeticSemantics
open AspisV5FriTransitionSemantics

namespace Ref
open V5FriDecoderReference

abbrev M31 := aspis_core.field.M31
abbrev CM31 := aspis_core.field.CM31
abbrev QM31 := aspis_core.field.QM31
abbrev Error := aspis_core.circle_query.CircleQueryError

end Ref

namespace Exact
open V5FriArithmeticExact

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31

end Exact

def refToExactCM31 (value : Ref.CM31) : Exact.CM31 :=
  { a := value.a, b := value.b }

def refToExactQM31 (value : Ref.QM31) : Exact.QM31 :=
  { c0 := refToExactCM31 value.c0, c1 := refToExactCM31 value.c1 }

instance : Inhabited Ref.CM31 :=
  ⟨{ a := 0#u32, b := 0#u32 }⟩

instance : Inhabited Ref.QM31 :=
  ⟨{ c0 := default, c1 := default }⟩

@[simp] theorem ref_option_from_residual_none (T : Type) :
    V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = .ok none := rfl

private theorem usize_mul_4_16 :
    (4#usize * 16#usize : Result Std.Usize) = .ok 64#usize := by
  have hspec := Std.Usize.mul_spec (x := 4#usize) (y := 16#usize)
    (by scalar_tac)
  obtain ⟨value, hcall, hvalue⟩ := WP.spec_imp_exists hspec
  have hresult : value = 64#usize := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  rw [hcall, hresult]

theorem ref_m31_decode_success_canonical
    (bytes : Array Std.U8 4#usize) (value : Ref.M31)
    (hdecode :
      V5FriDecoderReference.aspis_core.field.M31.from_le_bytes bytes =
        .ok (some value)) :
    canonicalM31 value := by
  unfold V5FriDecoderReference.aspis_core.field.M31.from_le_bytes at hdecode
  simp_all only [Std.lift, bind_tc_ok]
  let raw := core.num.U32.from_le_bytes bytes
  by_cases hge : raw >= V5FriDecoderReference.aspis_core.field.P
  · simp_all [raw, hge]
  · simp_all [raw, hge]
    subst value
    unfold canonicalM31 AspisAeneasCM31Multiplicative.CanonicalRawM31
    have hlt : raw.val <
        V5FriDecoderReference.aspis_core.field.P.val := by
      simpa only [UScalar.lt_equiv] using hge
    simpa [raw, V5FriDecoderReference.aspis_core.field.P,
      AspisCoreCM31Multiplicative.field.P] using hlt

theorem ref_cm31_decode_success_canonical
    (bytes : Slice Std.U8) (value : Ref.CM31)
    (hdecode :
      V5FriDecoderReference.aspis_core.field.CM31.from_le_bytes bytes =
        .ok (some value)) :
    canonicalCM31 (refToExactCM31 value) := by
  unfold V5FriDecoderReference.aspis_core.field.CM31.from_le_bytes at hdecode
  generalize hs0 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 4#usize } = s0 at hdecode
  cases s0 with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok s0 =>
    generalize ha0 :
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s0 =
          a0Result at hdecode
    cases a0Result with
    | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok a0Result =>
      cases a0Result with
      | Err error =>
        simp_all [V5FriDecoderReference.core.result.Result.ok,
          V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          Bind.bind, Aeneas.Std.bind]
      | Ok a0 =>
        simp_all only [V5FriDecoderReference.core.result.Result.ok,
          V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          bind_tc_ok]
        generalize hm0 :
            V5FriDecoderReference.aspis_core.field.M31.from_le_bytes a0 =
              m0Result at hdecode
        cases m0Result with
        | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
        | div => simp_all [Bind.bind, Aeneas.Std.bind]
        | ok m0Option =>
          cases m0Option with
          | none => simp_all [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              Bind.bind, Aeneas.Std.bind]
          | some m0 =>
            simp_all only [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              bind_tc_ok]
            generalize hs1 :
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 4#usize, «end» := 8#usize } = s1 at hdecode
            cases s1 with
            | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
            | div => simp_all [Bind.bind, Aeneas.Std.bind]
            | ok s1 =>
              generalize ha1 :
                  core.array.TryFromArrayCopySlice.try_from 4#usize
                    core.marker.CopyU8 s1 = a1Result at hdecode
              cases a1Result with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok a1Result =>
                cases a1Result with
                | Err error =>
                  simp_all [V5FriDecoderReference.core.result.Result.ok,
                    V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                    Bind.bind, Aeneas.Std.bind]
                | Ok a1 =>
                  simp_all only [V5FriDecoderReference.core.result.Result.ok,
                    V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                    bind_tc_ok]
                  generalize hm1 :
                      V5FriDecoderReference.aspis_core.field.M31.from_le_bytes a1 =
                        m1Result at hdecode
                  cases m1Result with
                  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                  | div => simp_all [Bind.bind, Aeneas.Std.bind]
                  | ok m1Option =>
                    cases m1Option with
                    | none =>
                      simp_all [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        Bind.bind, Aeneas.Std.bind]
                    | some m1 =>
                      simp_all only [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        bind_tc_ok]
                      injection hdecode with hvalue
                      have hvalue' : value = { a := m0, b := m1 } :=
                        Option.some.inj hvalue.symm
                      subst value
                      exact ⟨ref_m31_decode_success_canonical a0 m0 hm0,
                        ref_m31_decode_success_canonical a1 m1 hm1⟩

theorem ref_qm31_decode_success_canonical
    (bytes : Slice Std.U8) (value : Ref.QM31)
    (hdecode :
      V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    canonicalQM31 (refToExactQM31 value) := by
  unfold V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes at hdecode
  generalize hfirst :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 8#usize } = first at hdecode
  cases first with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok first =>
    generalize hc0 :
        V5FriDecoderReference.aspis_core.field.CM31.from_le_bytes first =
          c0Result at hdecode
    cases c0Result with
    | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok c0Option =>
      cases c0Option with
      | none => simp_all [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          Bind.bind, Aeneas.Std.bind]
      | some c0 =>
        simp_all only [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          bind_tc_ok]
        generalize hsecond :
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
              { start := 8#usize, «end» := 16#usize } = second at hdecode
        cases second with
        | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
        | div => simp_all [Bind.bind, Aeneas.Std.bind]
        | ok second =>
          generalize hc1 :
              V5FriDecoderReference.aspis_core.field.CM31.from_le_bytes second =
                c1Result at hdecode
          cases c1Result with
          | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
          | div => simp_all [Bind.bind, Aeneas.Std.bind]
          | ok c1Option =>
            cases c1Option with
            | none => simp_all [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                Bind.bind, Aeneas.Std.bind]
            | some c1 =>
              simp_all only [V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok]
              injection hdecode with hvalue
              have hvalue' : value = { c0 := c0, c1 := c1 } :=
                Option.some.inj hvalue.symm
              subst value
              exact ⟨ref_cm31_decode_success_canonical first c0 hc0,
                ref_cm31_decode_success_canonical second c1 hc1⟩

theorem reference_leaf_success_calls
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (values : Array Ref.QM31 4#usize)
    (hdecode : V5FriDecoderReference.decode_later_leaf_reference leaf layer =
      .ok (.Ok values)) :
    ∃ v0 v1 v2 v3 : Ref.QM31,
      V5FriDecoderReference.decode_later_slot_reference leaf layer 0#usize =
          .ok (.Ok v0) ∧
      V5FriDecoderReference.decode_later_slot_reference leaf layer 1#usize =
          .ok (.Ok v1) ∧
      V5FriDecoderReference.decode_later_slot_reference leaf layer 2#usize =
          .ok (.Ok v2) ∧
      V5FriDecoderReference.decode_later_slot_reference leaf layer 3#usize =
          .ok (.Ok v3) ∧
      values = Array.make 4#usize [v0, v1, v2, v3] := by
  unfold V5FriDecoderReference.decode_later_leaf_reference at hdecode
  generalize h0 :
      V5FriDecoderReference.decode_later_slot_reference leaf layer 0#usize =
        r0 at hdecode
  cases r0 with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok result0 =>
    cases result0 with
    | Err error =>
      simp_all [Bind.bind, Aeneas.Std.bind,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    | Ok v0 =>
      simp_all only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
      generalize h1 :
          V5FriDecoderReference.decode_later_slot_reference leaf layer 1#usize =
            r1 at hdecode
      cases r1 with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok result1 =>
        cases result1 with
        | Err error =>
          simp_all [Bind.bind, Aeneas.Std.bind,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok v1 =>
          simp_all only [bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch]
          generalize h2 :
              V5FriDecoderReference.decode_later_slot_reference leaf layer
                2#usize = r2 at hdecode
          cases r2 with
          | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
          | div => simp_all [Bind.bind, Aeneas.Std.bind]
          | ok result2 =>
            cases result2 with
            | Err error =>
              simp_all [Bind.bind, Aeneas.Std.bind,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            | Ok v2 =>
              simp_all only [bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch]
              generalize h3 :
                  V5FriDecoderReference.decode_later_slot_reference leaf layer
                    3#usize = r3 at hdecode
              cases r3 with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok result3 =>
                cases result3 with
                | Err error =>
                  simp_all [Bind.bind, Aeneas.Std.bind,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                | Ok v3 =>
                  simp_all only [bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTry.branch]
                  injection hdecode with hvalues
                  exact ⟨v0, v1, v2, v3, rfl, rfl, rfl, rfl,
                    core.result.Result.Ok.inj hvalues.symm⟩

theorem reference_leaf_success_slot
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (values : Array Ref.QM31 4#usize)
    (hdecode : V5FriDecoderReference.decode_later_leaf_reference leaf layer =
      .ok (.Ok values)) (slot : Fin 4) :
    V5FriDecoderReference.decode_later_slot_reference leaf layer
        (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
      .ok (.Ok values.val[slot.val]!) := by
  obtain ⟨v0, v1, v2, v3, h0, h1, h2, h3, hvalues⟩ :=
    reference_leaf_success_calls leaf layer values hdecode
  subst values
  fin_cases slot <;> assumption

theorem reference_slot_success_layer_independent
    (leaf : Array Std.U8 64#usize) (layer otherLayer : Std.U8)
    (slot : Std.Usize) (value : Ref.QM31)
    (hdecode : V5FriDecoderReference.decode_later_slot_reference leaf layer slot =
      .ok (.Ok value)) :
    V5FriDecoderReference.decode_later_slot_reference leaf otherLayer slot =
      .ok (.Ok value) := by
  unfold V5FriDecoderReference.decode_later_slot_reference at hdecode ⊢
  unfold
    V5FriDecoderReference.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES
    at hdecode ⊢
  simp_all only [Std.lift, bind_tc_ok]
  generalize hs :
      core.slice.index.SliceIndexRangeUsizeSlice.index
        { start := Std.Usize.wrapping_mul slot 16#usize,
          «end» := Std.Usize.wrapping_add
            (Std.Usize.wrapping_mul slot 16#usize) 16#usize }
        (Array.to_slice leaf) =
        sliceResult at hdecode ⊢
  cases sliceResult with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok bytes =>
    generalize hvalue :
        V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes bytes =
          decoded at hdecode ⊢
    cases decoded with
    | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok option =>
      cases option <;>
        simp_all [V5FriDecoderReference.core.option.Option.ok_or,
          Bind.bind, Aeneas.Std.bind]

theorem reference_slot_success_canonical
    (leaf : Array Std.U8 64#usize) (layer : Std.U8) (slot : Std.Usize)
    (value : Ref.QM31)
    (hdecode : V5FriDecoderReference.decode_later_slot_reference leaf layer slot =
      .ok (.Ok value)) :
    canonicalQM31 (refToExactQM31 value) := by
  unfold V5FriDecoderReference.decode_later_slot_reference at hdecode
  unfold
    V5FriDecoderReference.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES
    at hdecode
  simp_all only [Std.lift, bind_tc_ok]
  generalize hs :
      core.slice.index.SliceIndexRangeUsizeSlice.index
        { start := Std.Usize.wrapping_mul slot 16#usize,
          «end» := Std.Usize.wrapping_add
            (Std.Usize.wrapping_mul slot 16#usize) 16#usize }
        (Array.to_slice leaf) = sliceResult at hdecode
  cases sliceResult with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok bytes =>
    generalize hvalue :
        V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes bytes =
          decoded at hdecode
    cases decoded with
    | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok option =>
      cases option with
      | none =>
        simp_all [V5FriDecoderReference.core.option.Option.ok_or,
          Bind.bind, Aeneas.Std.bind]
      | some decodedValue =>
        simp_all [V5FriDecoderReference.core.option.Option.ok_or,
          Bind.bind, Aeneas.Std.bind]
        simpa using ref_qm31_decode_success_canonical bytes value hvalue

def referenceDecoded (leaf : Slice Std.U8) (slot : Fin 4) : ExactQM31 :=
  if hlength : leaf.val.length = 64 then
    let fixed : Array Std.U8 64#usize := ⟨leaf.val, by simpa using hlength⟩
    match V5FriDecoderReference.decode_later_slot_reference fixed 0#u8
        (Std.Usize.ofNatCore slot.val (by scalar_tac)) with
    | .ok (.Ok value) => qm31View (refToExactQM31 value)
    | _ => 0
  else 0

theorem referenceDecoded_of_success
    (leaf : Array Std.U8 64#usize) (layer : Std.U8) (slot : Fin 4)
    (value : Ref.QM31)
    (hdecode : V5FriDecoderReference.decode_later_slot_reference leaf layer
      (Std.Usize.ofNatCore slot.val (by scalar_tac)) = .ok (.Ok value)) :
    referenceDecoded (Array.to_slice leaf) slot =
      qm31View (refToExactQM31 value) := by
  have hzero := reference_slot_success_layer_independent leaf layer 0#u8
    (Std.Usize.ofNatCore slot.val (by scalar_tac)) value hdecode
  simp [referenceDecoded, Array.to_slice, hzero]

theorem reference_selected_success
    (leaf : Array Std.U8 64#usize) (layer : Std.U8) (slot : Fin 4)
    (value : Ref.QM31)
    (hdecode :
      V5FriDecoderReference.decode_selected_later_slot_reference leaf layer
        (Std.Usize.ofNatCore slot.val (by scalar_tac)) = .ok (.Ok value)) :
    ∃ values : Array Ref.QM31 4#usize,
      V5FriDecoderReference.decode_later_leaf_reference leaf layer =
          .ok (.Ok values) ∧
      values.val[slot.val]! = value := by
  unfold V5FriDecoderReference.decode_selected_later_slot_reference at hdecode
  have hnotge :
      ¬ 4#usize ≤ Std.Usize.ofNatCore slot.val (by scalar_tac) := by
    scalar_tac
  rw [if_neg hnotge] at hdecode
  generalize hleaf :
      V5FriDecoderReference.decode_later_leaf_reference leaf layer =
        result at hdecode
  cases result with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok result =>
    cases result with
    | Err error =>
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Aeneas.Std.bind]
    | Ok values =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
        at hdecode
      have hindex :
          Array.index_usize values
              (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
            .ok values.val[slot.val]! := by
        simp [Array.index_usize, slot.isLt]
      rw [hindex] at hdecode
      simp only [bind_tc_ok] at hdecode
      injection hdecode with hvalue
      exact ⟨values, rfl, core.result.Result.Ok.inj hvalue⟩

theorem exact_check_leaf_length_success
    (leaf : Slice Std.U8) (kind : V5FriArithmeticExact.circle_query.CircleQueryLeaf)
    (expected : Std.Usize)
    (hcheck :
      V5FriArithmeticExact.circle_query.check_leaf_length leaf kind expected =
        .ok (.Ok ())) :
    Slice.len leaf = expected := by
  unfold V5FriArithmeticExact.circle_query.check_leaf_length at hcheck
  by_cases hne : Slice.len leaf ≠ expected
  · simp [hne] at hcheck
  · exact Decidable.not_not.mp hne

theorem production_full_decoder_success_length
    (leaf : Slice Std.U8) (layer : Std.U8)
    (values : Array Exact.QM31 4#usize)
    (hdecode :
      V5FriArithmeticExact.circle_query.decode_later_leaf leaf layer =
        .ok (.Ok values)) :
    leaf.val.length = 64 := by
  unfold V5FriArithmeticExact.circle_query.decode_later_leaf at hdecode
  rw [show V5FriArithmeticExact.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES =
      .ok 64#usize by
        unfold V5FriArithmeticExact.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES
        exact usize_mul_4_16] at hdecode
  simp only [bind_tc_ok] at hdecode
  generalize hcheck :
      V5FriArithmeticExact.circle_query.check_leaf_length leaf
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        64#usize = checked at hdecode
  cases checked with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok checked =>
    cases checked with
    | Err error =>
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Aeneas.Std.bind]
    | Ok unit =>
      rcases unit with ⟨⟩
      have hlen := exact_check_leaf_length_success leaf
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        64#usize hcheck
      exact congrArg UScalar.val hlen

theorem production_selected_decoder_success_length
    (leaf : Slice Std.U8) (layer : Std.U8) (slot : Fin 4)
    (value : Exact.QM31)
    (hdecode :
      V5FriArithmeticExact.circle_query.decode_selected_later_slot leaf layer
        (Std.Usize.ofNatCore slot.val (by scalar_tac)) = .ok (.Ok value)) :
    leaf.val.length = 64 := by
  unfold V5FriArithmeticExact.circle_query.decode_selected_later_slot at hdecode
  rw [show V5FriArithmeticExact.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES =
      .ok 64#usize by
        unfold V5FriArithmeticExact.circle_query.CIRCLE_QUERY_LATER_LEAF_BYTES
        exact usize_mul_4_16] at hdecode
  simp only [bind_tc_ok] at hdecode
  generalize hcheck :
      V5FriArithmeticExact.circle_query.check_leaf_length leaf
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        64#usize = checked at hdecode
  cases checked with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok checked =>
    cases checked with
    | Err error =>
      simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        Bind.bind, Aeneas.Std.bind]
    | Ok unit =>
      rcases unit with ⟨⟩
      have hlen := exact_check_leaf_length_success leaf
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        64#usize hcheck
      exact congrArg UScalar.val hlen

def refArrayToExact
    (values : Array Ref.QM31 4#usize) : Array Exact.QM31 4#usize :=
  ⟨values.val.map refToExactQM31, by simpa using values.property⟩

@[simp] theorem refArrayToExact_entry
    (values : Array Ref.QM31 4#usize) (slot : Fin 4) :
    (refArrayToExact values).val[slot.val]! =
      refToExactQM31 values.val[slot.val]! := by
  simp [refArrayToExact, slot.isLt]

theorem refArrayToExact_entry_nat
    (values : Array Ref.QM31 4#usize) (index : Nat) (hindex : index < 4) :
    (refArrayToExact values).val[index]! =
      refToExactQM31 values.val[index]! := by
  simp [refArrayToExact, hindex]

/- Kani proves the two Rust functions equal for every 64-byte input and every
selected slot below four.  This record is only the translation/tool boundary:
it transports successful literal decoder calls between the independent
Aeneas snapshots.  It states no canonicality or mathematical byte meaning. -/
structure ProductionDecoderReferenceEquality : Prop where
  full : ∀ leaf layer values,
    V5FriArithmeticExact.circle_query.decode_later_leaf
        (Array.to_slice leaf) layer = .ok (.Ok values) →
      ∃ refValues,
        V5FriDecoderReference.decode_later_leaf_reference leaf layer =
            .ok (.Ok refValues) ∧
        values = refArrayToExact refValues
  selected : ∀ leaf layer (slot : Fin 4) value,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot
        (Array.to_slice leaf) layer
        (Std.Usize.ofNatCore slot.val (by scalar_tac)) = .ok (.Ok value) →
      ∃ refValue,
        V5FriDecoderReference.decode_selected_later_slot_reference leaf layer
            (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
          .ok (.Ok refValue) ∧
        value = refToExactQM31 refValue

theorem production_decoders_have_reference_semantics
    (hsource : ProductionDecoderReferenceEquality) :
    LaterLeafDecoderSemantics referenceDecoded := by
  constructor
  · intro leaf layer values hdecode
    have hlength := production_full_decoder_success_length leaf layer values
      hdecode
    let fixed : Array Std.U8 64#usize :=
      ⟨leaf.val, by simpa using hlength⟩
    have hslice : Array.to_slice fixed = leaf := by
      apply Subtype.ext
      rfl
    have hfixed :
        V5FriArithmeticExact.circle_query.decode_later_leaf
            (Array.to_slice fixed) layer = .ok (.Ok values) := by
      rw [hslice]
      exact hdecode
    obtain ⟨refValues, href, hvalues⟩ :=
      hsource.full fixed layer values hfixed
    subst values
    constructor
    · intro index hindex
      let slot : Fin 4 := ⟨index, hindex⟩
      have hslot := reference_leaf_success_slot fixed layer refValues href slot
      change canonicalQM31 (refArrayToExact refValues).val[index]!
      rw [refArrayToExact_entry_nat refValues index hindex]
      exact reference_slot_success_canonical fixed layer
        (Std.Usize.ofNatCore slot.val (by scalar_tac))
        refValues.val[slot.val]! hslot
    · intro slot
      have hslot := reference_leaf_success_slot fixed layer refValues href slot
      have hdecoded := referenceDecoded_of_success fixed layer slot
        refValues.val[slot.val]! hslot
      rw [hslice] at hdecoded
      change qm31View ((refArrayToExact refValues).val[slot.val]!) =
        referenceDecoded leaf slot
      rw [refArrayToExact_entry]
      exact hdecoded.symm
  · intro leaf layer slot value hdecode
    have hlength := production_selected_decoder_success_length leaf layer slot
      value hdecode
    let fixed : Array Std.U8 64#usize :=
      ⟨leaf.val, by simpa using hlength⟩
    have hslice : Array.to_slice fixed = leaf := by
      apply Subtype.ext
      rfl
    have hfixed :
        V5FriArithmeticExact.circle_query.decode_selected_later_slot
            (Array.to_slice fixed) layer
            (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
          .ok (.Ok value) := by
      rw [hslice]
      exact hdecode
    obtain ⟨refValue, href, hvalue⟩ :=
      hsource.selected fixed layer slot value hfixed
    subst value
    obtain ⟨refValues, hleaf, hentry⟩ :=
      reference_selected_success fixed layer slot refValue href
    have hslot := reference_leaf_success_slot fixed layer refValues hleaf slot
    rw [hentry] at hslot
    constructor
    · exact reference_slot_success_canonical fixed layer
        (Std.Usize.ofNatCore slot.val (by scalar_tac)) refValue hslot
    · have hdecoded := referenceDecoded_of_success fixed layer slot refValue
        hslot
      rw [hslice] at hdecoded
      exact hdecoded.symm

#print axioms ref_qm31_decode_success_canonical
#print axioms reference_leaf_success_slot
#print axioms production_decoders_have_reference_semantics

end AspisV5FriDecoderReferenceSemantics
