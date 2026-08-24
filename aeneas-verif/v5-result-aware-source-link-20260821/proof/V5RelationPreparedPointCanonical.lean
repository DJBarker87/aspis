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

#print axioms prepareM31DecodeCanonical
#print axioms prepareCM31DecodeCanonical
#print axioms prepareQM31DecodeCanonical
#print axioms prepareDecodeQm31Canonical

end AspisV5RelationPreparedPointCanonical
