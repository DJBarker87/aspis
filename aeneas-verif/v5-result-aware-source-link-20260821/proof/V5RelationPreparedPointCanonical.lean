import V5RelationPreparedPointVectors
import V5RelationPrepareCanonicalProof

/-!
# Canonical decoded relation points

This file follows the translated byte decoder used by relation preparation.
It proves that every limb in each of the three decoded ten-coordinate points
passed the production modulus check, then transfers that fact to the exact
vectors retained in the preparation trace.
-/

namespace AspisV5RelationPreparedPointCanonical

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisV5RelationPrepareLogLenProof.Prepare
open AspisV5RelationPreparedPointVectors
open AspisV5RelationPrepareCanonicalProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev PrepareQM31 := V5RelationPrepareGenerated.aspis_core.field.QM31

private instance : Inhabited PrepareQM31 :=
  ⟨V5RelationPrepareGenerated.aspis_core.field.QM31.ZERO⟩

private theorem optionResidualNone (T : Type) :
    V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = .ok none := rfl

/-- A limb returned by the preparation extraction's own decoder is below the
Mersenne-prime modulus. -/
theorem prepareM31DecodeCanonical
    (bytes : Array Std.U8 4#usize)
    (value : V5RelationPrepareGenerated.aspis_core.field.M31)
    (run :
      V5RelationPrepareGenerated.aspis_core.field.M31.from_le_bytes bytes =
        .ok (some value)) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val := by
  unfold V5RelationPrepareGenerated.aspis_core.field.M31.from_le_bytes at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  split at run
  next atLeastModulus => simp at run
  next belowModulus =>
    simp only [Result.ok.injEq, Option.some.injEq] at run
    subst value
    unfold AspisAeneasCM31Multiplicative.CanonicalRawM31
    have belowModulusVal : (core.num.U32.from_le_bytes bytes).val <
        V5RelationPrepareGenerated.aspis_core.field.P.val := by
      change ¬ (core.num.U32.from_le_bytes bytes).val ≥
        V5RelationPrepareGenerated.aspis_core.field.P.val at belowModulus
      omega
    simpa [AspisAeneasCM31Multiplicative.m31Modulus,
      AspisV5ComponentCRejectionSampler.rawCandidateCount,
      V5RelationPrepareGenerated.aspis_core.field.P] using belowModulusVal

/-- Both limbs of a successfully decoded preparation CM31 are canonical. -/
theorem prepareCM31DecodeCanonical
    (bytes : Slice Std.U8)
    (value : V5RelationPrepareGenerated.aspis_core.field.CM31)
    (run :
      V5RelationPrepareGenerated.aspis_core.field.CM31.from_le_bytes bytes =
        .ok (some value)) :
    AspisV5RelationPrepareFieldProjection.CanonicalCM31 value := by
  unfold V5RelationPrepareGenerated.aspis_core.field.CM31.from_le_bytes at run
  generalize firstSliceEquation :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 4#usize } = firstSlice at run
  cases firstSlice with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok firstSlice =>
      generalize firstArrayEquation :
          core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
            firstSlice = firstArrayResult at run
      cases firstArrayResult with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok firstArrayResult =>
          cases firstArrayResult with
          | Err error =>
              simp_all [V5RelationPrepareGenerated.core.result.Result.ok,
                V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                optionResidualNone,
                Bind.bind, Aeneas.Std.bind]
          | Ok firstArray =>
              simp_all only [V5RelationPrepareGenerated.core.result.Result.ok,
                V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok]
              generalize firstM31Equation :
                  V5RelationPrepareGenerated.aspis_core.field.M31.from_le_bytes
                    firstArray = firstM31Result at run
              cases firstM31Result with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok firstM31Option =>
                  cases firstM31Option with
                  | none =>
                      simp_all [
                        V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        optionResidualNone,
                        Bind.bind, Aeneas.Std.bind]
                  | some firstM31 =>
                      simp_all only [
                        V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        bind_tc_ok]
                      generalize secondSliceEquation :
                          core.slice.index.Slice.index
                            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                            bytes { start := 4#usize, «end» := 8#usize } =
                              secondSlice at run
                      cases secondSlice with
                      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                      | div => simp_all [Bind.bind, Aeneas.Std.bind]
                      | ok secondSlice =>
                          generalize secondArrayEquation :
                              core.array.TryFromArrayCopySlice.try_from 4#usize
                                core.marker.CopyU8 secondSlice =
                                  secondArrayResult at run
                          cases secondArrayResult with
                          | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                          | div => simp_all [Bind.bind, Aeneas.Std.bind]
                          | ok secondArrayResult =>
                              cases secondArrayResult with
                              | Err error =>
                                  simp_all [V5RelationPrepareGenerated.core.result.Result.ok,
                                    V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                    optionResidualNone,
                                    Bind.bind, Aeneas.Std.bind]
                              | Ok secondArray =>
                                  simp_all only [V5RelationPrepareGenerated.core.result.Result.ok,
                                    V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                    bind_tc_ok]
                                  generalize secondM31Equation :
                                      V5RelationPrepareGenerated.aspis_core.field.M31.from_le_bytes
                                        secondArray = secondM31Result at run
                                  cases secondM31Result with
                                  | fail error =>
                                      simp_all [Bind.bind, Aeneas.Std.bind]
                                  | div =>
                                      simp_all [Bind.bind, Aeneas.Std.bind]
                                  | ok secondM31Option =>
                                      cases secondM31Option with
                                      | none =>
                                          simp_all [
                                            V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                            optionResidualNone,
                                            Bind.bind, Aeneas.Std.bind]
                                      | some secondM31 =>
                                          simp_all only [
                                            V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                            bind_tc_ok]
                                          injection run with valueEquation
                                          have valueExact : value =
                                              { a := firstM31,
                                                b := secondM31 } :=
                                            Option.some.inj valueEquation.symm
                                          subst value
                                          exact ⟨
                                            prepareM31DecodeCanonical firstArray
                                              firstM31 firstM31Equation,
                                            prepareM31DecodeCanonical secondArray
                                              secondM31 secondM31Equation⟩

/-- All four limbs of a successfully decoded preparation QM31 are canonical. -/
theorem prepareQM31DecodeCanonical
    (bytes : Slice Std.U8) (value : PrepareQM31)
    (run :
      V5RelationPrepareGenerated.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    PrepareCanonicalQM31 value := by
  unfold V5RelationPrepareGenerated.aspis_core.field.QM31.from_le_bytes at run
  generalize firstSliceEquation :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 8#usize } = firstSlice at run
  cases firstSlice with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok firstSlice =>
      generalize firstCM31Equation :
          V5RelationPrepareGenerated.aspis_core.field.CM31.from_le_bytes
            firstSlice = firstCM31Result at run
      cases firstCM31Result with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok firstCM31Option =>
          cases firstCM31Option with
          | none =>
              simp_all [
                V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                optionResidualNone,
                Bind.bind, Aeneas.Std.bind]
          | some firstCM31 =>
              simp_all only [
                V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok]
              generalize secondSliceEquation :
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 8#usize, «end» := 16#usize } =
                      secondSlice at run
              cases secondSlice with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok secondSlice =>
                  generalize secondCM31Equation :
                      V5RelationPrepareGenerated.aspis_core.field.CM31.from_le_bytes
                        secondSlice = secondCM31Result at run
                  cases secondCM31Result with
                  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                  | div => simp_all [Bind.bind, Aeneas.Std.bind]
                  | ok secondCM31Option =>
                      cases secondCM31Option with
                      | none =>
                          simp_all [
                            V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                            optionResidualNone,
                            Bind.bind, Aeneas.Std.bind]
                      | some secondCM31 =>
                          simp_all only [
                            V5RelationPrepareGenerated.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                            bind_tc_ok]
                          injection run with valueEquation
                          have valueExact : value =
                              { c0 := firstCM31, c1 := secondCM31 } :=
                            Option.some.inj valueEquation.symm
                          subst value
                          have firstCanonical :=
                            prepareCM31DecodeCanonical firstSlice firstCM31
                              firstCM31Equation
                          have secondCanonical :=
                            prepareCM31DecodeCanonical secondSlice secondCM31
                              secondCM31Equation
                          exact ⟨firstCanonical.1, firstCanonical.2,
                            secondCanonical.1, secondCanonical.2⟩

/-- Successful `decode_qm31` execution in the preparation extraction returns
a canonical field element. -/
theorem prepareDecodeQm31Canonical
    (bytes : Slice Std.U8) (index : Std.Usize) (value : PrepareQM31)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.decode_qm31 bytes index =
        .ok (.Ok value)) :
    PrepareCanonicalQM31 value := by
  unfold V5RelationPrepareGenerated.v5_cu_probe.decode_qm31 at success
  generalize hmul :
      Usize.checked_mul index
        V5RelationPrepareGenerated.v5_cu_probe.QM31_BYTES = mulResult at success
  cases mulResult with
  | none =>
      simp [Std.lift, V5RelationPrepareGenerated.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from] at success
  | some offset =>
      simp only [Aeneas.Std.lift,
        V5RelationPrepareGenerated.core.option.Option.ok_or,
        bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
        at success
      generalize sliceEquation :
          core.slice.Slice.get
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
            { start := offset,
              «end» := Std.Usize.wrapping_add offset
                V5RelationPrepareGenerated.v5_cu_probe.QM31_BYTES } =
            selectedOption at success
      cases selectedOption with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok selectedOption =>
          cases selectedOption with
          | none =>
              simp [V5RelationPrepareGenerated.core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at success
          | some selected =>
              simp only [V5RelationPrepareGenerated.core.option.Option.ok_or,
                bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
                at success
              generalize decodeEquation :
                  V5RelationPrepareGenerated.aspis_core.field.QM31.from_le_bytes
                    selected = decodedOption at success
              cases decodedOption with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok decodedOption =>
                  cases decodedOption with
                  | none =>
                      simp [V5RelationPrepareGenerated.core.option.Option.ok_or]
                        at success
                  | some decoded =>
                      simp only [bind_tc_ok,
                        V5RelationPrepareGenerated.core.option.Option.ok_or]
                        at success
                      have decodedExact : decoded = value :=
                        core.result.Result.Ok.inj (Result.ok.inj success)
                      subst value
                      exact prepareQM31DecodeCanonical selected decoded
                        decodeEquation

/-- Every entry of a fixed preparation array is represented below the base
field modulus. -/
def PrepareCanonicalArray {count : Std.Usize}
    (values : Array PrepareQM31 count) : Prop :=
  ∀ index : Fin count.val, PrepareCanonicalQM31 values.val[index.val]!

private theorem prepareSameErrorResidual
    {T E : Type} (error : E) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T (core.convert.FromSame E) (.Err error) =
      .ok (.Err error) := by
  rfl

/-- A successful execution of the exact ten-call relation-point wrapper
returns ten canonical QM31 values.  This follows the translated wrapper call
by call; it does not assume a property of an abstract parser. -/
theorem prepareRelationPointDecodeCanonical
    (parsed : V5RelationPrepareGenerated.v5_cu_probe.ParsedProbeData)
    (pointIndex : Std.Usize)
    (output : Array PrepareQM31 10#usize)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.decode_relation_point_for_extraction
          parsed pointIndex = .ok (.Ok output)) :
    PrepareCanonicalArray output := by
  unfold
    V5RelationPrepareGenerated.v5_cu_probe.decode_relation_point_for_extraction
    at success
  simp only [Aeneas.Std.lift, bind_tc_ok] at success
  generalize baseEquation :
      Std.Usize.wrapping_mul pointIndex
        (UScalar.cast .Usize
          V5RelationPrepareGenerated.v5_cu_probe.V5_CU_PROBE_RELATION_LOG_ROWS) =
        base at success
  cases h0 : V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
      parsed.relation_points base with
  | fail error => simp [h0] at success
  | div => simp [h0] at success
  | ok decoded0 =>
      cases decoded0 with
      | Err error =>
          simp [h0, core.result.Result.Insts.CoreOpsTry.branch,
            prepareSameErrorResidual] at success
      | Ok value0 =>
          simp only [h0, core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok] at success
          have canonical0 := prepareDecodeQm31Canonical
            parsed.relation_points base value0 h0
          cases h1 : V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
              parsed.relation_points
              (Std.Usize.wrapping_add base 1#usize) with
          | fail error => simp [h1] at success
          | div => simp [h1] at success
          | ok decoded1 =>
              cases decoded1 with
              | Err error =>
                  simp [h1, core.result.Result.Insts.CoreOpsTry.branch,
                    prepareSameErrorResidual] at success
              | Ok value1 =>
                  simp only [h1, core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok] at success
                  have canonical1 := prepareDecodeQm31Canonical
                    parsed.relation_points
                    (Std.Usize.wrapping_add base 1#usize)
                    value1 h1
                  cases h2 : V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                      parsed.relation_points
                      (Std.Usize.wrapping_add base 2#usize) with
                  | fail error => simp [h2] at success
                  | div => simp [h2] at success
                  | ok decoded2 =>
                      cases decoded2 with
                      | Err error =>
                          simp [h2, core.result.Result.Insts.CoreOpsTry.branch,
                            prepareSameErrorResidual] at success
                      | Ok value2 =>
                          simp only [h2,
                            core.result.Result.Insts.CoreOpsTry.branch,
                            bind_tc_ok] at success
                          have canonical2 := prepareDecodeQm31Canonical
                            parsed.relation_points
                            (Std.Usize.wrapping_add base 2#usize) value2 h2
                          cases h3 :
                              V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                parsed.relation_points
                                (Std.Usize.wrapping_add base 3#usize) with
                          | fail error => simp [h3] at success
                          | div => simp [h3] at success
                          | ok decoded3 =>
                              cases decoded3 with
                              | Err error =>
                                  simp [h3,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    prepareSameErrorResidual] at success
                              | Ok value3 =>
                                  simp only [h3,
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    bind_tc_ok] at success
                                  have canonical3 := prepareDecodeQm31Canonical
                                    parsed.relation_points
                                    (Std.Usize.wrapping_add base 3#usize)
                                    value3 h3
                                  cases h4 :
                                      V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                        parsed.relation_points
                                        (Std.Usize.wrapping_add base 4#usize) with
                                  | fail error => simp [h4] at success
                                  | div => simp [h4] at success
                                  | ok decoded4 =>
                                      cases decoded4 with
                                      | Err error =>
                                          simp [h4,
                                            core.result.Result.Insts.CoreOpsTry.branch,
                                            prepareSameErrorResidual] at success
                                      | Ok value4 =>
                                          simp only [h4,
                                            core.result.Result.Insts.CoreOpsTry.branch,
                                            bind_tc_ok] at success
                                          have canonical4 :=
                                            prepareDecodeQm31Canonical
                                              parsed.relation_points
                                              (Std.Usize.wrapping_add base
                                                4#usize) value4 h4
                                          cases h5 :
                                              V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                parsed.relation_points
                                                (Std.Usize.wrapping_add base
                                                  5#usize) with
                                          | fail error => simp [h5] at success
                                          | div => simp [h5] at success
                                          | ok decoded5 =>
                                              cases decoded5 with
                                              | Err error =>
                                                  simp [h5,
                                                    core.result.Result.Insts.CoreOpsTry.branch,
                                                    prepareSameErrorResidual]
                                                    at success
                                              | Ok value5 =>
                                                  simp only [h5,
                                                    core.result.Result.Insts.CoreOpsTry.branch,
                                                    bind_tc_ok] at success
                                                  have canonical5 :=
                                                    prepareDecodeQm31Canonical
                                                      parsed.relation_points
                                                      (Std.Usize.wrapping_add
                                                        base 5#usize) value5 h5
                                                  cases h6 :
                                                      V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                        parsed.relation_points
                                                        (Std.Usize.wrapping_add
                                                          base 6#usize) with
                                                  | fail error =>
                                                      simp [h6] at success
                                                  | div => simp [h6] at success
                                                  | ok decoded6 =>
                                                      cases decoded6 with
                                                      | Err error =>
                                                          simp [h6,
                                                            core.result.Result.Insts.CoreOpsTry.branch,
                                                            prepareSameErrorResidual]
                                                            at success
                                                      | Ok value6 =>
                                                          simp only [h6,
                                                            core.result.Result.Insts.CoreOpsTry.branch,
                                                            bind_tc_ok]
                                                            at success
                                                          have canonical6 :=
                                                            prepareDecodeQm31Canonical
                                                              parsed.relation_points
                                                              (Std.Usize.wrapping_add
                                                                base 6#usize)
                                                              value6 h6
                                                          cases h7 :
                                                              V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                parsed.relation_points
                                                                (Std.Usize.wrapping_add
                                                                  base 7#usize) with
                                                          | fail error =>
                                                              simp [h7] at success
                                                          | div =>
                                                              simp [h7] at success
                                                          | ok decoded7 =>
                                                              cases decoded7 with
                                                              | Err error =>
                                                                  simp [h7,
                                                                    core.result.Result.Insts.CoreOpsTry.branch,
                                                                    prepareSameErrorResidual]
                                                                    at success
                                                              | Ok value7 =>
                                                                  simp only [h7,
                                                                    core.result.Result.Insts.CoreOpsTry.branch,
                                                                    bind_tc_ok]
                                                                    at success
                                                                  have canonical7 :=
                                                                    prepareDecodeQm31Canonical
                                                                      parsed.relation_points
                                                                      (Std.Usize.wrapping_add
                                                                        base 7#usize)
                                                                      value7 h7
                                                                  cases h8 :
                                                                      V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                        parsed.relation_points
                                                                        (Std.Usize.wrapping_add
                                                                          base 8#usize) with
                                                                  | fail error =>
                                                                      simp [h8]
                                                                        at success
                                                                  | div =>
                                                                      simp [h8]
                                                                        at success
                                                                  | ok decoded8 =>
                                                                      cases decoded8 with
                                                                      | Err error =>
                                                                          simp [h8,
                                                                            core.result.Result.Insts.CoreOpsTry.branch,
                                                                            prepareSameErrorResidual]
                                                                            at success
                                                                      | Ok value8 =>
                                                                          simp only [h8,
                                                                            core.result.Result.Insts.CoreOpsTry.branch,
                                                                            bind_tc_ok]
                                                                            at success
                                                                          have canonical8 :=
                                                                            prepareDecodeQm31Canonical
                                                                              parsed.relation_points
                                                                              (Std.Usize.wrapping_add
                                                                                base 8#usize)
                                                                              value8 h8
                                                                          cases h9 :
                                                                              V5RelationPrepareGenerated.v5_cu_probe.decode_qm31
                                                                                parsed.relation_points
                                                                                (Std.Usize.wrapping_add
                                                                                  base 9#usize) with
                                                                          | fail error =>
                                                                              simp [h9]
                                                                                at success
                                                                          | div =>
                                                                              simp [h9]
                                                                                at success
                                                                          | ok decoded9 =>
                                                                              cases decoded9 with
                                                                              | Err error =>
                                                                                  simp [h9,
                                                                                    core.result.Result.Insts.CoreOpsTry.branch,
                                                                                    prepareSameErrorResidual]
                                                                                    at success
                                                                              | Ok value9 =>
                                                                                  simp only [h9,
                                                                                    core.result.Result.Insts.CoreOpsTry.branch,
                                                                                    bind_tc_ok,
                                                                                    Result.ok.injEq,
                                                                                    core.result.Result.Ok.injEq]
                                                                                    at success
                                                                                  have canonical9 :=
                                                                                    prepareDecodeQm31Canonical
                                                                                      parsed.relation_points
                                                                                      (Std.Usize.wrapping_add
                                                                                        base 9#usize)
                                                                                      value9 h9
                                                                                  subst output
                                                                                  intro index
                                                                                  fin_cases index
                                                                                  · simpa [Array.make] using canonical0
                                                                                  · simpa [Array.make] using canonical1
                                                                                  · simpa [Array.make] using canonical2
                                                                                  · simpa [Array.make] using canonical3
                                                                                  · simpa [Array.make] using canonical4
                                                                                  · simpa [Array.make] using canonical5
                                                                                  · simpa [Array.make] using canonical6
                                                                                  · simpa [Array.make] using canonical7
                                                                                  · simpa [Array.make] using canonical8
                                                                                  · simpa [Array.make] using canonical9

/-- Indexwise canonicality for the dynamically sized vectors carried by the
translated accumulator. -/
def PrepareCanonicalList (values : List PrepareQM31) : Prop :=
  ∀ index, index < values.length → PrepareCanonicalQM31 values[index]!

/-- The three arrays retained by one successful preparation and the exact
vectors copied from them are all canonical. -/
theorem preparedPointVectorsCanonical
    {kappa inactiveClaim : PrepareQM31}
    {preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation}
    (trace : PrepareRelationArithmeticTrace kappa inactiveClaim
      preparedClaims relation) :
    PrepareCanonicalArray trace.point0 ∧
      PrepareCanonicalArray trace.point1 ∧
      PrepareCanonicalArray trace.point2 ∧
      PrepareCanonicalList trace.pointVec0.val ∧
      PrepareCanonicalList trace.pointVec1.val ∧
      PrepareCanonicalList trace.pointVec2.val := by
  have array0 := prepareRelationPointDecodeCanonical trace.parsed 0#usize
    trace.point0 trace.point0DecodeRun
  have array1 := prepareRelationPointDecodeCanonical trace.parsed 1#usize
    trace.point1 trace.point1DecodeRun
  have array2 := prepareRelationPointDecodeCanonical trace.parsed 2#usize
    trace.point2 trace.point2DecodeRun
  have vectors := preparedPointVectorsExact trace
  refine ⟨array0, array1, array2, ?_, ?_, ?_⟩
  · intro index bound
    have bound10 : index < 10 := by
      simpa [vectors.2.2.2.1] using bound
    rw [vectors.1]
    exact array0 ⟨index, bound10⟩
  · intro index bound
    have bound10 : index < 10 := by
      simpa [vectors.2.2.2.2.1] using bound
    rw [vectors.2.1]
    exact array1 ⟨index, bound10⟩
  · intro index bound
    have bound10 : index < 10 := by
      simpa [vectors.2.2.2.2.2] using bound
    rw [vectors.2.2.1]
    exact array2 ⟨index, bound10⟩

#print axioms prepareM31DecodeCanonical
#print axioms prepareCM31DecodeCanonical
#print axioms prepareQM31DecodeCanonical
#print axioms prepareDecodeQm31Canonical
#print axioms prepareRelationPointDecodeCanonical
#print axioms preparedPointVectorsCanonical

end AspisV5RelationPreparedPointCanonical
