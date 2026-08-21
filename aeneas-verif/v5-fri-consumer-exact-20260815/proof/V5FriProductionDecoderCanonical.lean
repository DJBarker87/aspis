import V5FriTransparentHelperEquality
import V5FriConsumerDecoderBridge
import V5FriDecoderReferenceSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriProductionDecoderCanonical

private abbrev ExactQM31 := V5FriArithmeticExact.field.QM31

def sourceDecodeEncoded
    (encoded : Slice Std.U8) (layer : Std.U8) (offset : Std.Usize) :
    Result (core.result.Result ExactQM31
      V5FriArithmeticExact.circle_query.CircleQueryError) := do
  let s0 ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 0#usize, «end» := 4#usize }
  let r0 ← core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s0
  let a0 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r0
  let i0 ← lift (core.num.U32.from_le_bytes a0)
  let s1 ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 4#usize, «end» := 8#usize }
  let r1 ← core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s1
  let a1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r1
  let i1 ← lift (core.num.U32.from_le_bytes a1)
  let s2 ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 8#usize, «end» := 12#usize }
  let r2 ← core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s2
  let a2 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r2
  let i2 ← lift (core.num.U32.from_le_bytes a2)
  let s3 ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 12#usize, «end» := 16#usize }
  let r3 ← core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s3
  let a3 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r3
  let i3 ← lift (core.num.U32.from_le_bytes a3)
  let limbIter ← core.slice.Slice.iter
    (Array.to_slice (Array.make 4#usize [i0, i1, i2, i3]))
  let (nonCanonical, _) ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
      limbIter ()
  if nonCanonical then
    ok (.Err
      (V5FriArithmeticExact.circle_query.CircleQueryError.NonCanonicalQm31
        (V5FriArithmeticExact.circle_query.CircleQueryLeaf.Later layer)
        offset))
  else
    let c0 ← V5FriArithmeticExact.field.CM31.new i0 i1
    let c1 ← V5FriArithmeticExact.field.CM31.new i2 i3
    ok (.Ok { c0, c1 })

theorem slice_range_success_facts
    {α : Type} (input output : Slice α) (start finish : Std.Usize)
    (hrun : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice α) input
      { start := start, «end» := finish } = .ok output) :
    start ≤ finish ∧ finish ≤ input.length ∧
      output.val = input.val.slice start.val finish.val := by
  rw [Slice.index_SliceIndexRangeUsizeSliceInst] at hrun
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hrun
  split at hrun
  · rename_i hbounds
    exact ⟨hbounds.1, hbounds.2,
      congrArg Subtype.val (Result.ok.inj hrun).symm⟩
  · simp_all

theorem slice_range_eq_ok
    {α : Type} (input output : Slice α) (start finish : Std.Usize)
    (hstart : start ≤ finish) (hfinish : finish ≤ input.length)
    (hval : output.val = input.val.slice start.val finish.val) :
    core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice α) input
      { start := start, «end» := finish } = .ok output := by
  rw [Slice.index_SliceIndexRangeUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  rw [if_pos ⟨hstart, hfinish⟩]
  apply congrArg Result.ok
  apply Subtype.ext
  exact hval.symm

abbrev DecoderQM31 := V5FriByteDecoderSource.aspis_core.field.QM31

def decoderToExact (value : DecoderQM31) : ExactQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b },
    c1 := { a := value.c1.a, b := value.c1.b } }

theorem decoder_m31_of_canonical
    (bytes : Array Std.U8 4#usize)
    (hcanonical : core.num.U32.from_le_bytes bytes <
      V5FriArithmeticExact.field.P) :
    V5FriByteDecoderSource.aspis_core.field.M31.from_le_bytes bytes =
      .ok (some (core.num.U32.from_le_bytes bytes)) := by
  unfold V5FriByteDecoderSource.aspis_core.field.M31.from_le_bytes
  have hnot : ¬ core.num.U32.from_le_bytes bytes >=
      V5FriByteDecoderSource.aspis_core.field.P := by
    unfold V5FriArithmeticExact.field.P at hcanonical
    unfold V5FriByteDecoderSource.aspis_core.field.P
    scalar_tac
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [if_neg hnot]

structure SourceFourDecodeWitness
    (encoded : Slice Std.U8) (value : ExactQM31) where
  s0 : Slice Std.U8
  s1 : Slice Std.U8
  s2 : Slice Std.U8
  s3 : Slice Std.U8
  a0 : Array Std.U8 4#usize
  a1 : Array Std.U8 4#usize
  a2 : Array Std.U8 4#usize
  a3 : Array Std.U8 4#usize
  hs0 : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 0#usize, «end» := 4#usize } = .ok s0
  hs1 : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 4#usize, «end» := 8#usize } = .ok s1
  hs2 : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 8#usize, «end» := 12#usize } = .ok s2
  hs3 : core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
    { start := 12#usize, «end» := 16#usize } = .ok s3
  ha0 : core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s0 = .ok (.Ok a0)
  ha1 : core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s1 = .ok (.Ok a1)
  ha2 : core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s2 = .ok (.Ok a2)
  ha3 : core.array.TryFromArrayCopySlice.try_from 4#usize
    core.marker.CopyU8 s3 = .ok (.Ok a3)
  encoded_length : 16 ≤ encoded.val.length
  s0_val : s0.val = encoded.val.slice 0 4
  s1_val : s1.val = encoded.val.slice 4 8
  s2_val : s2.val = encoded.val.slice 8 12
  s3_val : s3.val = encoded.val.slice 12 16
  canonical :
    core.num.U32.from_le_bytes a0 < V5FriArithmeticExact.field.P ∧
    core.num.U32.from_le_bytes a1 < V5FriArithmeticExact.field.P ∧
    core.num.U32.from_le_bytes a2 < V5FriArithmeticExact.field.P ∧
    core.num.U32.from_le_bytes a3 < V5FriArithmeticExact.field.P
  value_eq : value = {
    c0 := { a := core.num.U32.from_le_bytes a0,
            b := core.num.U32.from_le_bytes a1 },
    c1 := { a := core.num.U32.from_le_bytes a2,
            b := core.num.U32.from_le_bytes a3 }}

theorem any_four_false_canonical
    (i0 i1 i2 i3 : Std.U32)
    (next : core.slice.iter.Iter Std.U32)
    (hany :
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
        V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
        ⟨Array.to_slice (Array.make 4#usize [i0, i1, i2, i3]), 0⟩ () =
          .ok (false, next)) :
    i0 < V5FriArithmeticExact.field.P ∧
    i1 < V5FriArithmeticExact.field.P ∧
    i2 < V5FriArithmeticExact.field.P ∧
    i3 < V5FriArithmeticExact.field.P := by
  simp [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any,
    core.slice.iter.Iter.anyAux,
    core.slice.iter.IteratorSliceIter.next,
    V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut,
    Array.to_slice, Array.make] at hany
  split at hany <;> simp_all
  split at hany <;> simp_all
  split at hany <;> simp_all
  split at hany <;> simp_all
  rename_i h0 h1 h2 h3
  change (↑i1 : Nat) < ↑V5FriArithmeticExact.field.P at h1
  change (↑i2 : Nat) < ↑V5FriArithmeticExact.field.P at h2
  change (↑i3 : Nat) < ↑V5FriArithmeticExact.field.P at h3
  exact ⟨h1, h2, h3⟩

noncomputable def source_decode_encoded_success_witness
    (encoded : Slice Std.U8) (layer : Std.U8) (offset : Std.Usize)
    (value : ExactQM31)
    (hdecode : sourceDecodeEncoded encoded layer offset = .ok (.Ok value)) :
    SourceFourDecodeWitness encoded value := by
  unfold sourceDecodeEncoded at hdecode
  generalize hs0 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
        { start := 0#usize, «end» := 4#usize } = rs0 at hdecode
  cases rs0 with
  | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok s0 =>
    generalize ha0 :
        core.array.TryFromArrayCopySlice.try_from 4#usize
          core.marker.CopyU8 s0 = ra0 at hdecode
    cases ra0 with
    | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
    | div => simp_all [Bind.bind, Aeneas.Std.bind]
    | ok ra0 =>
      cases ra0 with
      | Err e => simp_all [core.result.Result.unwrap, Bind.bind, Aeneas.Std.bind]
      | Ok a0 =>
        simp only [core.result.Result.unwrap, bind_tc_ok, Aeneas.Std.lift] at hdecode
        generalize hs1 :
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
              { start := 4#usize, «end» := 8#usize } = rs1 at hdecode
        cases rs1 with
        | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
        | div => simp_all [Bind.bind, Aeneas.Std.bind]
        | ok s1 =>
          generalize ha1 :
              core.array.TryFromArrayCopySlice.try_from 4#usize
                core.marker.CopyU8 s1 = ra1 at hdecode
          cases ra1 with
          | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
          | div => simp_all [Bind.bind, Aeneas.Std.bind]
          | ok ra1 =>
            cases ra1 with
            | Err e => simp_all [core.result.Result.unwrap, Bind.bind, Aeneas.Std.bind]
            | Ok a1 =>
              simp only [core.result.Result.unwrap, bind_tc_ok, Aeneas.Std.lift] at hdecode
              generalize hs2 :
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
                    { start := 8#usize, «end» := 12#usize } = rs2 at hdecode
              cases rs2 with
              | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok s2 =>
                generalize ha2 :
                    core.array.TryFromArrayCopySlice.try_from 4#usize
                      core.marker.CopyU8 s2 = ra2 at hdecode
                cases ra2 with
                | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
                | div => simp_all [Bind.bind, Aeneas.Std.bind]
                | ok ra2 =>
                  cases ra2 with
                  | Err e => simp_all [core.result.Result.unwrap, Bind.bind, Aeneas.Std.bind]
                  | Ok a2 =>
                    simp only [core.result.Result.unwrap, bind_tc_ok, Aeneas.Std.lift] at hdecode
                    generalize hs3 :
                        core.slice.index.Slice.index
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
                          { start := 12#usize, «end» := 16#usize } = rs3 at hdecode
                    cases rs3 with
                    | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
                    | div => simp_all [Bind.bind, Aeneas.Std.bind]
                    | ok s3 =>
                      generalize ha3 :
                          core.array.TryFromArrayCopySlice.try_from 4#usize
                            core.marker.CopyU8 s3 = ra3 at hdecode
                      cases ra3 with
                      | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
                      | div => simp_all [Bind.bind, Aeneas.Std.bind]
                      | ok ra3 =>
                        cases ra3 with
                        | Err e =>
                          simp_all [core.result.Result.unwrap, Bind.bind, Aeneas.Std.bind]
                        | Ok a3 =>
                          simp only [core.result.Result.unwrap, bind_tc_ok,
                            Aeneas.Std.lift, core.slice.Slice.iter] at hdecode
                          generalize hany :
                              core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
                                V5FriArithmeticExact.circle_query.decode_later_leaf.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool
                                ⟨Array.to_slice (Array.make 4#usize
                                  [core.num.U32.from_le_bytes a0,
                                   core.num.U32.from_le_bytes a1,
                                   core.num.U32.from_le_bytes a2,
                                   core.num.U32.from_le_bytes a3]), 0⟩ () =
                                rany at hdecode
                          cases rany with
                          | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
                          | div => simp_all [Bind.bind, Aeneas.Std.bind]
                          | ok pair =>
                            rcases pair with ⟨nonCanonical, next⟩
                            cases nonCanonical with
                            | true => simp_all [Bind.bind, Aeneas.Std.bind]
                            | false =>
                              simp only [Bool.false_eq_true, if_false,
                                V5FriArithmeticExact.field.CM31.new,
                                bind_tc_ok] at hdecode
                              have hcanonical := any_four_false_canonical
                                (core.num.U32.from_le_bytes a0)
                                (core.num.U32.from_le_bytes a1)
                                (core.num.U32.from_le_bytes a2)
                                (core.num.U32.from_le_bytes a3) next hany
                              have hsf0 := slice_range_success_facts encoded s0
                                0#usize 4#usize hs0
                              have hsf1 := slice_range_success_facts encoded s1
                                4#usize 8#usize hs1
                              have hsf2 := slice_range_success_facts encoded s2
                                8#usize 12#usize hs2
                              have hsf3 := slice_range_success_facts encoded s3
                                12#usize 16#usize hs3
                              simp [ha0, ha1, ha2, ha3, hany,
                                V5FriArithmeticExact.field.CM31.new] at hdecode
                              refine {
                                s0 := s0, s1 := s1, s2 := s2, s3 := s3,
                                a0 := a0, a1 := a1, a2 := a2, a3 := a3,
                                hs0 := hs0, hs1 := hs1, hs2 := hs2, hs3 := hs3,
                                ha0 := ha0, ha1 := ha1, ha2 := ha2, ha3 := ha3,
                                encoded_length := by simpa using hsf3.2.1,
                                s0_val := hsf0.2.2,
                                s1_val := hsf1.2.2,
                                s2_val := hsf2.2.2,
                                s3_val := hsf3.2.2,
                                canonical := hcanonical,
                                value_eq := ?_ }
                              exact hdecode.symm

theorem byte_decoder_success_of_witness
    (encoded : Slice Std.U8) (value : ExactQM31)
    (w : SourceFourDecodeWitness encoded value) :
    ∃ decoded : DecoderQM31,
      V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes encoded =
          .ok (some decoded) ∧
      value = decoderToExact decoded := by
  have hlen := w.encoded_length
  let first : Slice Std.U8 :=
    ⟨encoded.val.slice 0 8, by scalar_tac⟩
  let second : Slice Std.U8 :=
    ⟨encoded.val.slice 8 16, by scalar_tac⟩
  have hfirst :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
        { start := 0#usize, «end» := 8#usize } = .ok first := by
    apply slice_range_eq_ok
    · scalar_tac
    · change 8 ≤ encoded.val.length
      omega
    · rfl
  have hsecond :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) encoded
        { start := 8#usize, «end» := 16#usize } = .ok second := by
    apply slice_range_eq_ok
    · scalar_tac
    · change 16 ≤ encoded.val.length
      exact w.encoded_length
    · rfl
  have hfirst0 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) first
        { start := 0#usize, «end» := 4#usize } = .ok w.s0 := by
    apply slice_range_eq_ok
    · scalar_tac
    · change 4 ≤ first.val.length
      simp [first, List.slice]
      omega
    · rw [w.s0_val]
      simp_scalar
      simp [first, List.slice, List.take_take]
  have hfirst1 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) first
        { start := 4#usize, «end» := 8#usize } = .ok w.s1 := by
    apply slice_range_eq_ok
    · scalar_tac
    · change 8 ≤ first.val.length
      simp [first, List.slice]
      omega
    · rw [w.s1_val]
      simp_scalar
      simp [first, List.slice, List.drop_take, List.take_take]
  have hsecond0 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) second
        { start := 0#usize, «end» := 4#usize } = .ok w.s2 := by
    apply slice_range_eq_ok
    · scalar_tac
    · change 4 ≤ second.val.length
      simp [second, List.slice]
      omega
    · rw [w.s2_val]
      simp_scalar
      simp [second, List.slice, List.take_take, List.drop_drop]
  have hsecond1 :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) second
        { start := 4#usize, «end» := 8#usize } = .ok w.s3 := by
    apply slice_range_eq_ok
    · scalar_tac
    · change 8 ≤ second.val.length
      simp [second, List.slice]
      omega
    · rw [w.s3_val]
      simp_scalar
      simp [second, List.slice, List.drop_take, List.take_take,
        List.drop_drop]
  have hm0 := decoder_m31_of_canonical w.a0 w.canonical.1
  have hm1 := decoder_m31_of_canonical w.a1 w.canonical.2.1
  have hm2 := decoder_m31_of_canonical w.a2 w.canonical.2.2.1
  have hm3 := decoder_m31_of_canonical w.a3 w.canonical.2.2.2
  let decoded : DecoderQM31 := {
    c0 := { a := core.num.U32.from_le_bytes w.a0,
            b := core.num.U32.from_le_bytes w.a1 },
    c1 := { a := core.num.U32.from_le_bytes w.a2,
            b := core.num.U32.from_le_bytes w.a3 }}
  refine ⟨decoded, ?_, ?_⟩
  · unfold V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes
    rw [hfirst]
    simp only [bind_tc_ok]
    unfold V5FriByteDecoderSource.aspis_core.field.CM31.from_le_bytes
    rw [hfirst0]
    simp only [bind_tc_ok]
    rw [w.ha0]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.result.Result.ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hm0]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hfirst1]
    simp only [bind_tc_ok]
    rw [w.ha1]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.result.Result.ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hm1]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hsecond]
    simp only [bind_tc_ok]
    rw [hsecond0]
    simp only [bind_tc_ok]
    rw [w.ha2]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.result.Result.ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hm2]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hsecond1]
    simp only [bind_tc_ok]
    rw [w.ha3]
    simp only [bind_tc_ok,
      V5FriByteDecoderSource.core.result.Result.ok,
      V5FriByteDecoderSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
    rw [hm3]
    rfl
  · exact w.value_eq

def sourceDecodeOuter
    (leaf : Slice Std.U8) (layer : Std.U8) (slot : Std.Usize) :
    Result (core.result.Result ExactQM31
      V5FriArithmeticExact.circle_query.CircleQueryError) := do
  let offset ← lift (Std.Usize.wrapping_mul slot 16#usize)
  let finish ← lift (Std.Usize.wrapping_add offset 16#usize)
  let encoded ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) leaf
    { start := offset, «end» := finish }
  sourceDecodeEncoded encoded layer offset

abbrev RefQM31 := V5FriDecoderReference.aspis_core.field.QM31

theorem source_decode_outer_success_reference
    (leaf : Array Std.U8 64#usize) (layer : Std.U8)
    (slot : Fin 4) (value : ExactQM31)
    (hdecode : sourceDecodeOuter (Array.to_slice leaf) layer
      (Std.Usize.ofNatCore slot.val (by scalar_tac)) = .ok (.Ok value)) :
    ∃ refValue : RefQM31,
      V5FriDecoderReference.decode_later_slot_reference leaf layer
          (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
        .ok (.Ok refValue) ∧
      value = AspisV5FriDecoderReferenceSemantics.refToExactQM31 refValue := by
  unfold sourceDecodeOuter at hdecode
  simp only [Aeneas.Std.lift, bind_tc_ok] at hdecode
  let offset := Std.Usize.wrapping_mul
    (Std.Usize.ofNatCore slot.val (by scalar_tac)) 16#usize
  let finish := Std.Usize.wrapping_add offset 16#usize
  generalize hslice :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
        (Array.to_slice leaf) { start := offset, «end» := finish } =
      sliceResult at hdecode
  cases sliceResult with
  | fail e => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok encoded =>
    simp only [bind_tc_ok] at hdecode
    let witness := source_decode_encoded_success_witness encoded layer offset
      value hdecode
    obtain ⟨decoded, hbyte, hvalue⟩ :=
      byte_decoder_success_of_witness encoded value witness
    have href :=
      AspisV5FriConsumerDecoderBridge.qm31_decode_success_ref
        encoded decoded hbyte
    refine ⟨AspisV5FriConsumerDecoderBridge.toRefQM31 decoded, ?_, ?_⟩
    · unfold V5FriDecoderReference.decode_later_slot_reference
      unfold V5FriDecoderReference.aspis_core.circle_query.CIRCLE_QUERY_QM31_BYTES
      simp only [Aeneas.Std.lift, bind_tc_ok]
      have harraySlice :
          core.array.Array.index
            (core.ops.index.IndexSlice
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) leaf
            { start := offset, «end» := finish } = .ok encoded := by
        change core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
          (Array.to_slice leaf) { start := offset, «end» := finish } =
            .ok encoded
        exact hslice
      rw [harraySlice]
      simp only [bind_tc_ok]
      rw [href]
      rfl
    · exact hvalue.trans (by rfl)

end AspisV5FriProductionDecoderCanonical
