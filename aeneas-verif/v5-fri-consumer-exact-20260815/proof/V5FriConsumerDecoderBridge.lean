import V5FriByteDecoderSource.Funs
import V5FriDecoderReference.Funs
import CheckV5FriQueries.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriConsumerDecoderBridge

namespace Ref
abbrev CM31 := V5FriDecoderReference.aspis_core.field.CM31
abbrev QM31 := V5FriDecoderReference.aspis_core.field.QM31
end Ref

namespace Decoder
abbrev CM31 := V5FriByteDecoderSource.aspis_core.field.CM31
abbrev QM31 := V5FriByteDecoderSource.aspis_core.field.QM31
end Decoder

def toRefCM31 (value : Decoder.CM31) : Ref.CM31 :=
  ⟨value.a, value.b⟩

def toRefQM31 (value : Decoder.QM31) : Ref.QM31 :=
  ⟨toRefCM31 value.c0, toRefCM31 value.c1⟩

def consumerToRefCM31
    (value : V5FriConsumerExact.aspis_core.field.CM31) : Ref.CM31 :=
  ⟨value.a, value.b⟩

def consumerToRefQM31
    (value : V5FriConsumerExact.aspis_core.field.QM31) : Ref.QM31 :=
  ⟨consumerToRefCM31 value.c0, consumerToRefCM31 value.c1⟩

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .fail error => .fail error
  | .div => .div
  | .ok value => .ok (f value)

@[simp] theorem source_option_from_residual_none (T : Type) :
    V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = .ok none := rfl

@[simp] theorem reference_option_from_residual_none (T : Type) :
    V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = .ok none := rfl

theorem m31_decode_eq (bytes : Array Std.U8 4#usize) :
    V5FriByteDecoderSource.aspis_core.field.M31.from_le_bytes bytes =
      V5FriDecoderReference.aspis_core.field.M31.from_le_bytes bytes := by
  unfold V5FriByteDecoderSource.aspis_core.field.M31.from_le_bytes
    V5FriDecoderReference.aspis_core.field.M31.from_le_bytes
  unfold V5FriByteDecoderSource.aspis_core.field.P
    V5FriDecoderReference.aspis_core.field.P
  rfl

theorem cm31_decode_success_ref (bytes : Slice Std.U8)
    (value : Decoder.CM31)
    (hdecode : V5FriByteDecoderSource.aspis_core.field.CM31.from_le_bytes bytes =
      .ok (some value)) :
    V5FriDecoderReference.aspis_core.field.CM31.from_le_bytes bytes =
      .ok (some (toRefCM31 value)) := by
  unfold V5FriByteDecoderSource.aspis_core.field.CM31.from_le_bytes at hdecode
  unfold V5FriDecoderReference.aspis_core.field.CM31.from_le_bytes
  simp_rw [← m31_decode_eq]
  generalize hs0 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 4#usize } = s0 at hdecode ⊢
  cases s0 with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok s0 =>
    generalize ha0 :
        core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s0 =
          a0Result at hdecode ⊢
    cases a0Result with
    | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok a0Result =>
      cases a0Result with
      | Err error =>
        simp_all [V5FriByteDecoderSource.core.result.Result.ok,
          V5FriDecoderReference.core.result.Result.ok,
          V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          Bind.bind, Aeneas.Std.bind]
      | Ok a0 =>
        simp_all only [V5FriByteDecoderSource.core.result.Result.ok,
          V5FriDecoderReference.core.result.Result.ok,
          V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          bind_tc_ok]
        generalize hm0 :
            V5FriByteDecoderSource.aspis_core.field.M31.from_le_bytes a0 = m0Result
              at hdecode ⊢
        cases m0Result with
        | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
        | div => simp_all [Bind.bind, Aeneas.Std.bind]
        | ok m0Option =>
          cases m0Option with
          | none =>
            simp_all [V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              Bind.bind, Aeneas.Std.bind]
          | some m0 =>
            simp_all only [
              V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
              bind_tc_ok]
            generalize hs1 :
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 4#usize, «end» := 8#usize } = s1 at hdecode ⊢
            cases s1 with
            | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
            | div => simp_all [Bind.bind, Aeneas.Std.bind]
            | ok s1 =>
              generalize ha1 :
                  core.array.TryFromArrayCopySlice.try_from 4#usize
                    core.marker.CopyU8 s1 = a1Result at hdecode ⊢
              cases a1Result with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok a1Result =>
                cases a1Result with
                | Err error =>
                  simp_all [V5FriByteDecoderSource.core.result.Result.ok,
                    V5FriDecoderReference.core.result.Result.ok,
                    V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                    V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                    Bind.bind, Aeneas.Std.bind]
                | Ok a1 =>
                  simp_all only [V5FriByteDecoderSource.core.result.Result.ok,
                    V5FriDecoderReference.core.result.Result.ok,
                    V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                    V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                    bind_tc_ok]
                  generalize hm1 :
                      V5FriByteDecoderSource.aspis_core.field.M31.from_le_bytes a1 = m1Result
                        at hdecode ⊢
                  cases m1Result with
                  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                  | div => simp_all [Bind.bind, Aeneas.Std.bind]
                  | ok m1Option =>
                    cases m1Option with
                    | none =>
                      simp_all [V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        Bind.bind, Aeneas.Std.bind]
                    | some m1 =>
                      simp_all only [
                        V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        bind_tc_ok]
                      injection hdecode with hvalue
                      have hvalue' : value = { a := m0, b := m1 } :=
                        Option.some.inj hvalue.symm
                      subst value
                      rfl

theorem qm31_decode_success_ref (bytes : Slice Std.U8)
    (value : Decoder.QM31)
    (hdecode : V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes bytes =
      .ok (some value)) :
    V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes bytes =
      .ok (some (toRefQM31 value)) := by
  unfold V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes at hdecode
  unfold V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes
  generalize hfirst :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 8#usize } = first at hdecode ⊢
  cases first with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok first =>
    generalize hc0 :
        V5FriByteDecoderSource.aspis_core.field.CM31.from_le_bytes first = c0Result at hdecode
    cases c0Result with
    | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok c0Option =>
      cases c0Option with
      | none =>
        simp_all [V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          Bind.bind, Aeneas.Std.bind]
      | some c0 =>
        simp only [bind_tc_ok] at hdecode ⊢
        rw [hc0] at hdecode
        simp only [
          V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          bind_tc_ok] at hdecode
        have href0 := cm31_decode_success_ref first c0 hc0
        rw [href0]
        simp only [
          V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          bind_tc_ok]
        generalize hsecond :
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
              { start := 8#usize, «end» := 16#usize } = second at hdecode ⊢
        cases second with
        | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
        | div => simp_all [Bind.bind, Aeneas.Std.bind]
        | ok second =>
          generalize hc1 :
              V5FriByteDecoderSource.aspis_core.field.CM31.from_le_bytes second = c1Result
                at hdecode
          cases c1Result with
          | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
          | div => simp_all [Bind.bind, Aeneas.Std.bind]
          | ok c1Option =>
            cases c1Option with
            | none =>
              simp_all [
                V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                Bind.bind, Aeneas.Std.bind]
            | some c1 =>
              simp only [bind_tc_ok] at hdecode ⊢
              rw [hc1] at hdecode
              simp only [
                V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok] at hdecode
              have href1 := cm31_decode_success_ref second c1 hc1
              rw [href1]
              simp only [
                V5FriDecoderReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok]
              injection hdecode with hvalue
              have hvalue' : value = { c0 := c0, c1 := c1 } :=
                Option.some.inj hvalue.symm
              subst value
              rfl

/-- A successful selected-value decode in the consumer extraction is the
same successful byte decode in the independent reference extraction.  The
consumer call is now a transparent transport of the production decoder, so
this theorem has no source-code equality premise. -/
theorem consumer_qm31_decode_success_reference
    (bytes : Slice Std.U8)
    (value : V5FriConsumerExact.aspis_core.field.QM31)
    (hdecode :
      V5FriConsumerExact.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    V5FriDecoderReference.aspis_core.field.QM31.from_le_bytes bytes =
      .ok (some (consumerToRefQM31 value)) := by
  unfold V5FriConsumerExact.aspis_core.field.QM31.from_le_bytes at hdecode
  unfold V5FriConsumerExact.HelperTransport.fromLeBytes at hdecode
  generalize hsource :
      V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes bytes = sourceResult
        at hdecode
  cases sourceResult with
  | fail error =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hdecode
  | div =>
      simp [V5FriConsumerExact.HelperTransport.mapResult] at hdecode
  | ok option =>
      cases option with
      | none =>
          simp [V5FriConsumerExact.HelperTransport.mapResult] at hdecode
      | some decoded =>
          simp only [V5FriConsumerExact.HelperTransport.mapResult,
            Option.map] at hdecode
          have hvalue : value =
              V5FriConsumerExact.HelperTransport.fromDecoderQM31 decoded := by
            exact Option.some.inj (Result.ok.inj hdecode).symm
          subst value
          simpa [consumerToRefQM31, consumerToRefCM31,
            V5FriConsumerExact.HelperTransport.fromDecoderQM31,
            V5FriConsumerExact.HelperTransport.fromDecoderCM31,
            toRefQM31, toRefCM31] using
            qm31_decode_success_ref bytes decoded hsource

#print axioms consumer_qm31_decode_success_reference

end AspisV5FriConsumerDecoderBridge
