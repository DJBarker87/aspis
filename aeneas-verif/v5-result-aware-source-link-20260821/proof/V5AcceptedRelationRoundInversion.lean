import V5RelationAcceptanceSourceProof
import V5AcceptedRelationRoundProjection

/-!
# Inverting an accepted production relation round

The generated relation verifier implements each round as two nested fixed
loops.  This file recovers the successful scalar calls from those loops.  It
starts with the seven-coefficient loop: acceptance exposes the exact completed
polynomial, its boundary check, its evaluation, and both weight folds.
-/

namespace AspisV5AcceptedRelationRoundInversion

open Aeneas Aeneas.Std Result ControlFlow Error
open V5RelationFullGenerated
open AspisV5RelationFullSourceProof
open AspisV5RelationFullSuccessInversion
open AspisV5RelationAcceptanceSourceProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev RawQM31 := V5RelationFullGenerated.aspis_core.field.QM31
abbrev Verified :=
  V5RelationFullGenerated.relation_stress.VerifiedV5RelationStress
abbrev VError :=
  V5RelationFullGenerated.relation_stress.V5RelationStressError

@[simp] theorem relation_option_from_residual_none (T : Type) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
        T none = .ok none := rfl

/-- A value returned by the translated production M31 byte decoder is below
the field modulus.  This is recovered from the decoder's own rejection
branch, rather than assumed at the model boundary. -/
theorem accepted_m31_decode_is_canonical
    (bytes : Array Std.U8 4#usize)
    (value : V5RelationFullGenerated.aspis_core.field.M31)
    (run :
      V5RelationFullGenerated.aspis_core.field.M31.from_le_bytes bytes =
        .ok (some value)) :
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.val := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.from_le_bytes at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  split at run
  next atLeastModulus => simp at run
  next belowModulus =>
    simp only [Result.ok.injEq, Option.some.injEq] at run
    subst value
    unfold AspisAeneasCM31Multiplicative.CanonicalRawM31
    have belowModulusVal : (core.num.U32.from_le_bytes bytes).val <
        V5RelationFullGenerated.aspis_core.field.P.val := by
      change ¬ (core.num.U32.from_le_bytes bytes).val ≥
        V5RelationFullGenerated.aspis_core.field.P.val at belowModulus
      omega
    simpa [AspisAeneasCM31Multiplicative.m31Modulus,
      AspisV5ComponentCRejectionSampler.rawCandidateCount,
      V5RelationFullGenerated.aspis_core.field.P] using belowModulusVal

/-- Both M31 limbs returned by the translated CM31 decoder passed that same
production rejection check. -/
theorem accepted_cm31_decode_is_canonical
    (bytes : Slice Std.U8)
    (value : V5RelationFullGenerated.aspis_core.field.CM31)
    (run :
      V5RelationFullGenerated.aspis_core.field.CM31.from_le_bytes bytes =
        .ok (some value)) :
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31 value := by
  unfold V5RelationFullGenerated.aspis_core.field.CM31.from_le_bytes at run
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
              simp_all [core.result.Result.ok,
                core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                Bind.bind, Aeneas.Std.bind]
          | Ok firstArray =>
              simp_all only [core.result.Result.ok,
                core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                bind_tc_ok]
              generalize firstM31Equation :
                  V5RelationFullGenerated.aspis_core.field.M31.from_le_bytes
                    firstArray = firstM31Result at run
              cases firstM31Result with
              | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
              | div => simp_all [Bind.bind, Aeneas.Std.bind]
              | ok firstM31Option =>
                  cases firstM31Option with
                  | none =>
                      simp_all [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        Bind.bind, Aeneas.Std.bind]
                  | some firstM31 =>
                      simp_all only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
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
                                  simp_all [core.result.Result.ok,
                                    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                    Bind.bind, Aeneas.Std.bind]
                              | Ok secondArray =>
                                  simp_all only [core.result.Result.ok,
                                    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                    bind_tc_ok]
                                  generalize secondM31Equation :
                                      V5RelationFullGenerated.aspis_core.field.M31.from_le_bytes
                                        secondArray = secondM31Result at run
                                  cases secondM31Result with
                                  | fail error =>
                                      simp_all [Bind.bind, Aeneas.Std.bind]
                                  | div =>
                                      simp_all [Bind.bind, Aeneas.Std.bind]
                                  | ok secondM31Option =>
                                      cases secondM31Option with
                                      | none =>
                                          simp_all [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                            Bind.bind, Aeneas.Std.bind]
                                      | some secondM31 =>
                                          simp_all only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                                            bind_tc_ok]
                                          injection run with valueEquation
                                          have valueExact : value =
                                              { a := firstM31,
                                                b := secondM31 } :=
                                            Option.some.inj valueEquation.symm
                                          subst value
                                          exact ⟨
                                            accepted_m31_decode_is_canonical
                                              firstArray firstM31 firstM31Equation,
                                            accepted_m31_decode_is_canonical
                                              secondArray secondM31
                                              secondM31Equation⟩

/-- All four M31 limbs returned by the translated QM31 decoder are canonical. -/
theorem accepted_qm31_decode_is_canonical
    (bytes : Slice Std.U8) (value : RawQM31)
    (run :
      V5RelationFullGenerated.aspis_core.field.QM31.from_le_bytes bytes =
        .ok (some value)) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31 value := by
  unfold V5RelationFullGenerated.aspis_core.field.QM31.from_le_bytes at run
  generalize firstSliceEquation :
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
        { start := 0#usize, «end» := 8#usize } = firstSlice at run
  cases firstSlice with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok firstSlice =>
      generalize firstCM31Equation :
          V5RelationFullGenerated.aspis_core.field.CM31.from_le_bytes
            firstSlice = firstCM31Result at run
      cases firstCM31Result with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok firstCM31Option =>
          cases firstCM31Option with
          | none =>
              simp_all [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                Bind.bind, Aeneas.Std.bind]
          | some firstCM31 =>
              simp_all only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
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
                      V5RelationFullGenerated.aspis_core.field.CM31.from_le_bytes
                        secondSlice = secondCM31Result at run
                  cases secondCM31Result with
                  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
                  | div => simp_all [Bind.bind, Aeneas.Std.bind]
                  | ok secondCM31Option =>
                      cases secondCM31Option with
                      | none =>
                          simp_all [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                            Bind.bind, Aeneas.Std.bind]
                      | some secondCM31 =>
                          simp_all only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                            bind_tc_ok]
                          injection run with valueEquation
                          have valueExact : value =
                              { c0 := firstCM31, c1 := secondCM31 } :=
                            Option.some.inj valueEquation.symm
                          subst value
                          exact ⟨
                            accepted_cm31_decode_is_canonical firstSlice
                              firstCM31 firstCM31Equation,
                            accepted_cm31_decode_is_canonical secondSlice
                              secondCM31 secondCM31Equation⟩

/-- A successful translated relation-tail decoder call returns a canonical
QM31 value. -/
theorem accepted_decode_qm31_is_canonical
    (bytes : Array Std.U8 928#usize) (offset : Std.Usize)
    (value : RawQM31)
    (run :
      V5RelationFullGenerated.relation_stress.decode_qm31 bytes offset =
        .ok (.Ok value)) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31 value := by
  unfold V5RelationFullGenerated.relation_stress.decode_qm31 at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  generalize sliceEquation :
      core.array.Array.index
        (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
        { start := offset,
          «end» := Std.Usize.wrapping_add offset
            V5RelationFullGenerated.relation_stress.QM31_BYTES } =
        sliceResult at run
  cases sliceResult with
  | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
  | div => simp_all [Bind.bind, Aeneas.Std.bind]
  | ok selected =>
      simp only [bind_tc_ok] at run
      generalize decodeEquation :
          V5RelationFullGenerated.aspis_core.field.QM31.from_le_bytes
            selected = decodeResult at run
      cases decodeResult with
      | fail error => simp_all [Bind.bind, Aeneas.Std.bind]
      | div => simp_all [Bind.bind, Aeneas.Std.bind]
      | ok decodedOption =>
          cases decodedOption with
          | none => simp_all [core.option.Option.ok_or]
          | some decoded =>
              simp only [core.option.Option.ok_or] at run
              have decodedExact : decoded = value :=
                core.result.Result.Ok.inj (Result.ok.inj run)
              subst value
              exact accepted_qm31_decode_is_canonical selected decoded
                decodeEquation

/-- The production indexed wrapper only computes the byte offset before
calling `decode_qm31`, so its successful result is canonical as well. -/
theorem accepted_decode_indexed_is_canonical
    (bytes : Array Std.U8 928#usize) (offset index : Std.Usize)
    (value : RawQM31)
    (run :
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        index = .ok (.Ok value)) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31 value := by
  unfold V5RelationFullGenerated.relation_stress.decode_indexed at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  exact accepted_decode_qm31_is_canonical bytes
    (Std.Usize.wrapping_add offset
      (Std.Usize.wrapping_mul index
        V5RelationFullGenerated.relation_stress.QM31_BYTES)) value run

/-- Calls made when the generated seven-coefficient loop completes a
successful round. -/
structure AcceptedPolynomialExecution {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (additive nextAdditive : A) : Type where
  polynomial : Array RawQM31 7#usize
  boundaryRun :
    V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum polynomial =
      .ok claim
  evaluateRun :
    V5RelationFullGenerated.aspis_core.sumcheck.evaluate polynomial alpha =
      .ok nextClaim
  weightFoldRun :
    aspis_core.sumcheck.WeightAccumulator.fold weights alpha = .ok nextWeights
  additiveFoldRun : additiveInst.fold additive alpha = .ok nextAdditive

def initialPolynomialIterator :
    V5MutableEnumerateSupport.MutEnumerate RawQM31 :=
  { iter := { slice := (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1 }
    count := 0#usize }

/-- The exact innermost call made after the two OOD samples have completed. -/
noncomputable def concretePolynomialLoopCall {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim : RawQM31) (bytes : Array Std.U8 928#usize)
    (additive : A) (round : Std.Usize) (alpha : RawQM31) :=
  V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
    additiveInst
    (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2
    (fun iterator => iterator.slice)
    (fun enumerated => enumerated.iter)
    initialPolynomialIterator (fun e => e) weights claim bytes additive round
    alpha none

/-- The scalar calls plus the exact concrete loop invocation that produced
them.  Keeping the invocation lets later proofs recover all seven successful
decoder calls without inserting a caller-equality premise. -/
structure AcceptedConcretePolynomialExecution {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (round : Std.Usize) : Type where
  scalar : AcceptedPolynomialExecution additiveInst weights nextWeights
    claim nextClaim alpha additive nextAdditive
  concreteRun : concretePolynomialLoopCall additiveInst weights claim bytes
    additive round alpha =
      .ok (nextWeights, nextClaim, nextAdditive, none, 1#u32)

/-- The first active coefficient of an accepted concrete polynomial loop was
read successfully from the production decoder. -/
theorem accepted_concrete_polynomial_exposes_first_read
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (round : Std.Usize)
    (trace : AcceptedConcretePolynomialExecution additiveInst weights
      nextWeights claim nextClaim alpha bytes additive nextAdditive round) :
    ∃ offset value,
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
        .ok offset ∧
      V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
        (Std.Usize.wrapping_add
          (Std.Usize.wrapping_mul round
            V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
          0#usize) = .ok (.Ok value) := by
  have run := trace.concreteRun
  unfold concretePolynomialLoopCall initialPolynomialIterator at run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
    at run
  have inBounds0 :
      (0 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 0 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    have specification := Std.Usize.add_spec (x := 0#usize) (y := 1#usize)
      (by scalar_tac)
    obtain ⟨computed, computedRun, computedVal⟩ :=
      WP.spec_imp_exists specification
    have computedExact : computed = 1#usize := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    rw [computedRun, computedExact]
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds0, count0Next,
    Aeneas.Std.lift, bind_tc_ok] at run
  generalize offsetEquation :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
        offsetResult at run
  cases offsetResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok offset =>
      simp only [bind_tc_ok] at run
      generalize readEquation :
          V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
            (Std.Usize.wrapping_add
              (Std.Usize.wrapping_mul round
                V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
              0#usize) = readResult at run
      cases readResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok decoded =>
          cases decoded with
          | Err decodeError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
          | Ok value =>
              exact ⟨offset, value, rfl, readEquation⟩

private theorem usizeAddExactPolynomial (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have specification := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨computed, computedRun, computedVal⟩ :=
    WP.spec_imp_exists specification
  have computedExact : computed = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [computedRun, computedExact]

/-- The seven exact wire reads made by one accepted polynomial loop. -/
structure AcceptedSevenPolynomialReads
    (bytes : Array Std.U8 928#usize) (round : Std.Usize) : Type where
  offset : Std.Usize
  value0 : RawQM31
  value1 : RawQM31
  value2 : RawQM31
  value3 : RawQM31
  value4 : RawQM31
  value5 : RawQM31
  value6 : RawQM31
  offsetRun :
    V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
      .ok offset
  read0 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        0#usize) = .ok (.Ok value0)
  read1 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        1#usize) = .ok (.Ok value1)
  read2 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        2#usize) = .ok (.Ok value2)
  read3 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        3#usize) = .ok (.Ok value3)
  read4 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        4#usize) = .ok (.Ok value4)
  read5 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        5#usize) = .ok (.Ok value5)
  read6 :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
        6#usize) = .ok (.Ok value6)

/-- Acceptance exposes all seven successful production decoder calls, in
wire order, from the same concrete mutable-loop execution. -/
theorem accepted_concrete_polynomial_exposes_seven_reads
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (round : Std.Usize)
    (trace : AcceptedConcretePolynomialExecution additiveInst weights
      nextWeights claim nextClaim alpha bytes additive nextAdditive round) :
    Nonempty (AcceptedSevenPolynomialReads bytes round) := by
  have run := trace.concreteRun
  unfold concretePolynomialLoopCall initialPolynomialIterator at run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
    at run
  have inBounds0 :
      (0 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 0 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds1 :
      (1 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 1 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds2 :
      (2 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 2 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds3 :
      (3 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 3 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds4 :
      (4 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 4 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds5 :
      (5 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 5 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds6 :
      (6 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 6 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count1Next : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count2Next : 2#usize + 1#usize = ok 3#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count3Next : 3#usize + 1#usize = ok 4#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count4Next : 4#usize + 1#usize = ok 5#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count5Next : 5#usize + 1#usize = ok 6#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count6Next : 6#usize + 1#usize = ok 7#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds0, count0Next,
    Aeneas.Std.lift, bind_tc_ok] at run
  generalize offsetEquation :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
        offsetResult at run
  cases offsetResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok offset =>
      simp only [bind_tc_ok] at run
      generalize read0Equation :
          V5RelationFullGenerated.relation_stress.decode_indexed bytes offset
            (Std.Usize.wrapping_add
              (Std.Usize.wrapping_mul round
                V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
              0#usize) = read0Result at run
      cases read0Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok decoded0 =>
          cases decoded0 with
          | Err decodeError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
          | Ok value0 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              rw [Aeneas.Std.loop.eq_def] at run
              simp only at run
              simp [
                V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
                V5MutableEnumerateSupport.next,
                core.slice.iter.IteratorIterMut.next, inBounds1, count1Next,
                Aeneas.Std.lift, bind_tc_ok, offsetEquation] at run
              generalize read1Equation :
                  V5RelationFullGenerated.relation_stress.decode_indexed bytes
                    offset
                    (Std.Usize.wrapping_add
                      (Std.Usize.wrapping_mul round
                        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                      1#usize) = read1Result at run
              cases read1Result with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok decoded1 =>
                  cases decoded1 with
                  | Err decodeError =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at run
                  | Ok value1 =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok] at run
                      rw [Aeneas.Std.loop.eq_def] at run
                      simp only at run
                      simp [
                        V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
                        V5MutableEnumerateSupport.next,
                        core.slice.iter.IteratorIterMut.next, inBounds2,
                        count2Next, Aeneas.Std.lift, bind_tc_ok,
                        offsetEquation] at run
                      generalize read2Equation :
                          V5RelationFullGenerated.relation_stress.decode_indexed
                            bytes offset
                            (Std.Usize.wrapping_add
                              (Std.Usize.wrapping_mul round
                                V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                              2#usize) = read2Result at run
                      cases read2Result with
                      | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at run
                      | div => simp [Bind.bind, Aeneas.Std.bind] at run
                      | ok decoded2 =>
                          cases decoded2 with
                          | Err decodeError =>
                              simp [core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                core.convert.FromSame.from] at run
                          | Ok value2 =>
                              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                bind_tc_ok] at run
                              rw [Aeneas.Std.loop.eq_def] at run
                              simp only at run
                              simp [
                                V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
                                V5MutableEnumerateSupport.next,
                                core.slice.iter.IteratorIterMut.next,
                                inBounds3, count3Next, Aeneas.Std.lift,
                                bind_tc_ok, offsetEquation] at run
                              generalize read3Equation :
                                  V5RelationFullGenerated.relation_stress.decode_indexed
                                    bytes offset
                                    (Std.Usize.wrapping_add
                                      (Std.Usize.wrapping_mul round
                                        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                                      3#usize) = read3Result at run
                              cases read3Result with
                              | fail error =>
                                  simp [Bind.bind, Aeneas.Std.bind] at run
                              | div =>
                                  simp [Bind.bind, Aeneas.Std.bind] at run
                              | ok decoded3 =>
                                  cases decoded3 with
                                  | Err decodeError =>
                                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                        core.convert.FromSame.from] at run
                                  | Ok value3 =>
                                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                        bind_tc_ok] at run
                                      rw [Aeneas.Std.loop.eq_def] at run
                                      simp only at run
                                      simp [
                                        V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
                                        V5MutableEnumerateSupport.next,
                                        core.slice.iter.IteratorIterMut.next,
                                        inBounds4, count4Next, Aeneas.Std.lift,
                                        bind_tc_ok, offsetEquation] at run
                                      generalize read4Equation :
                                          V5RelationFullGenerated.relation_stress.decode_indexed
                                            bytes offset
                                            (Std.Usize.wrapping_add
                                              (Std.Usize.wrapping_mul round
                                                V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                                              4#usize) = read4Result at run
                                      cases read4Result with
                                      | fail error =>
                                          simp [Bind.bind, Aeneas.Std.bind] at run
                                      | div =>
                                          simp [Bind.bind, Aeneas.Std.bind] at run
                                      | ok decoded4 =>
                                          cases decoded4 with
                                          | Err decodeError =>
                                              simp [core.result.Result.Insts.CoreOpsTry.branch,
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                core.convert.FromSame.from] at run
                                          | Ok value4 =>
                                              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                                bind_tc_ok] at run
                                              rw [Aeneas.Std.loop.eq_def] at run
                                              simp only at run
                                              simp [
                                                V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
                                                V5MutableEnumerateSupport.next,
                                                core.slice.iter.IteratorIterMut.next,
                                                inBounds5, count5Next,
                                                Aeneas.Std.lift, bind_tc_ok,
                                                offsetEquation] at run
                                              generalize read5Equation :
                                                  V5RelationFullGenerated.relation_stress.decode_indexed
                                                    bytes offset
                                                    (Std.Usize.wrapping_add
                                                      (Std.Usize.wrapping_mul round
                                                        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                                                      5#usize) = read5Result at run
                                              cases read5Result with
                                              | fail error =>
                                                  simp [Bind.bind,
                                                    Aeneas.Std.bind] at run
                                              | div =>
                                                  simp [Bind.bind,
                                                    Aeneas.Std.bind] at run
                                              | ok decoded5 =>
                                                  cases decoded5 with
                                                  | Err decodeError =>
                                                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                        core.convert.FromSame.from]
                                                        at run
                                                  | Ok value5 =>
                                                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                                        bind_tc_ok] at run
                                                      rw [Aeneas.Std.loop.eq_def]
                                                        at run
                                                      simp only at run
                                                      simp [
                                                        V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
                                                        V5MutableEnumerateSupport.next,
                                                        core.slice.iter.IteratorIterMut.next,
                                                        inBounds6, count6Next,
                                                        Aeneas.Std.lift,
                                                        bind_tc_ok,
                                                        offsetEquation] at run
                                                      generalize read6Equation :
                                                          V5RelationFullGenerated.relation_stress.decode_indexed
                                                            bytes offset
                                                            (Std.Usize.wrapping_add
                                                              (Std.Usize.wrapping_mul round
                                                                V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                                                              6#usize) =
                                                            read6Result at run
                                                      cases read6Result with
                                                      | fail error =>
                                                          simp [Bind.bind,
                                                            Aeneas.Std.bind]
                                                            at run
                                                      | div =>
                                                          simp [Bind.bind,
                                                            Aeneas.Std.bind]
                                                            at run
                                                      | ok decoded6 =>
                                                          cases decoded6 with
                                                          | Err decodeError =>
                                                              simp [core.result.Result.Insts.CoreOpsTry.branch,
                                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                                core.convert.FromSame.from]
                                                                at run
                                                          | Ok value6 =>
                                                              exact ⟨{
                                                                offset := offset
                                                                value0 := value0
                                                                value1 := value1
                                                                value2 := value2
                                                                value3 := value3
                                                                value4 := value4
                                                                value5 := value5
                                                                value6 := value6
                                                                offsetRun := offsetEquation
                                                                read0 := read0Equation
                                                                read1 := read1Equation
                                                                read2 := read2Equation
                                                                read3 := read3Equation
                                                                read4 := read4Equation
                                                                read5 := read5Equation
                                                                read6 := read6Equation }⟩

/-- The seven decoded values together with the exact terminal calls made on
that reconstructed polynomial. -/
structure AcceptedExactPolynomialExecution {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (round : Std.Usize) : Type where
  reads : AcceptedSevenPolynomialReads bytes round
  boundaryRun :
    V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum
      (sevenValues reads.value0 reads.value1 reads.value2 reads.value3
        reads.value4 reads.value5 reads.value6) = .ok claim
  evaluateRun :
    V5RelationFullGenerated.aspis_core.sumcheck.evaluate
      (sevenValues reads.value0 reads.value1 reads.value2 reads.value3
        reads.value4 reads.value5 reads.value6) alpha = .ok nextClaim
  weightFoldRun :
    aspis_core.sumcheck.WeightAccumulator.fold weights alpha =
      .ok nextWeights
  additiveFoldRun : additiveInst.fold additive alpha = .ok nextAdditive

/-- Acceptance of the concrete mutable loop identifies not just its seven
wire reads but the exact reconstructed polynomial consumed by the boundary
and evaluation kernels. -/
theorem accepted_concrete_polynomial_exposes_exact_execution
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (round : Std.Usize)
    (trace : AcceptedConcretePolynomialExecution additiveInst weights
      nextWeights claim nextClaim alpha bytes additive nextAdditive round) :
    Nonempty (AcceptedExactPolynomialExecution additiveInst weights
      nextWeights claim nextClaim alpha bytes additive nextAdditive round) := by
  obtain ⟨reads⟩ := accepted_concrete_polynomial_exposes_seven_reads
    additiveInst weights nextWeights claim nextClaim alpha bytes additive
      nextAdditive round trace
  have run := trace.concreteRun
  unfold concretePolynomialLoopCall initialPolynomialIterator at run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
    at run
  have inBounds0 :
      (0 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 0 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds1 :
      (1 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 1 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds2 :
      (2 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 2 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds3 :
      (3 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 3 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds4 :
      (4 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 4 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds5 :
      (5 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 5 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have inBounds6 :
      (6 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change 6 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have exhausted :
      ¬ (7 : Nat) < (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1.val.length := by
    change ¬ 7 < (Array.repeat 7#usize
      V5RelationFullGenerated.aspis_core.field.QM31.ZERO).val.length
    rw [Array.repeat_val]
    decide
  have count0Next : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count1Next : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count2Next : 2#usize + 1#usize = ok 3#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count3Next : 3#usize + 1#usize = ok 4#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count4Next : 4#usize + 1#usize = ok 5#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count5Next : 5#usize + 1#usize = ok 6#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  have count6Next : 6#usize + 1#usize = ok 7#usize := by
    apply usizeAddExactPolynomial <;> scalar_tac
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds0, count0Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read0,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds1, count1Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read1,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds2, count2Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read2,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds3, count3Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read3,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds4, count4Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read4,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds5, count5Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read5,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, inBounds6, count6Next,
    Aeneas.Std.lift, bind_tc_ok, reads.offsetRun, reads.read6,
    core.result.Result.Insts.CoreOpsTry.branch] at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp [
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body,
    V5MutableEnumerateSupport.next,
    core.slice.iter.IteratorIterMut.next, exhausted,
    Array.to_slice_mut, Array.to_slice, Array.from_slice] at run
  simp only [Slice.setAtNat, Array.repeat_val, sevenValues, Array.make,
    List.set] at run
  have reconstructedExact :
      (⟨[reads.value0, reads.value1, reads.value2, reads.value3,
          reads.value4, reads.value5, reads.value6], by simp⟩ :
        Array RawQM31 7#usize) =
      sevenValues reads.value0 reads.value1 reads.value2 reads.value3
        reads.value4 reads.value5 reads.value6 := by
    apply Subtype.ext
    rfl
  rw [reconstructedExact] at run
  generalize boundaryEquation :
      V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum
        (sevenValues reads.value0 reads.value1 reads.value2 reads.value3
          reads.value4 reads.value5 reads.value6) = boundaryResult at run
  cases boundaryResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok boundary =>
      simp only [bind_tc_ok] at run
      generalize neEquation :
          core.cmp.PartialEq.ne.trait_default
            V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
            boundary claim = neResult at run
      cases neResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok differs =>
          simp only [bind_tc_ok] at run
          cases differs with
          | true => simp at run
          | false =>
              simp only [Bool.false_eq_true, if_false] at run
              generalize evaluateEquation :
                  V5RelationFullGenerated.aspis_core.sumcheck.evaluate
                    (sevenValues reads.value0 reads.value1 reads.value2
                      reads.value3 reads.value4 reads.value5 reads.value6)
                    alpha = evaluateResult at run
              cases evaluateResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok evaluated =>
                  simp only [bind_tc_ok] at run
                  generalize foldEquation :
                      aspis_core.sumcheck.WeightAccumulator.fold weights alpha =
                        foldResult at run
                  cases foldResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok folded =>
                      simp only [bind_tc_ok] at run
                      generalize additiveEquation :
                          additiveInst.fold additive alpha = additiveResult at run
                      cases additiveResult with
                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                      | div => simp [Bind.bind, Aeneas.Std.bind] at run
                      | ok foldedAdditive =>
                          simp only [bind_tc_ok] at run
                          have boundaryExact : boundary = claim := by
                            rw [AspisV5RelationFullSourceProof.raw_qm31_ne_spec]
                              at neEquation
                            by_contra different
                            simp [different] at neEquation
                          subst boundary
                          injection run with outputEquation
                          have weightsExact : folded = nextWeights := by
                            simpa using congrArg (fun output => output.1)
                              outputEquation
                          have claimExact : evaluated = nextClaim := by
                            simpa using congrArg (fun output => output.2.1)
                              outputEquation
                          have additiveExact : foldedAdditive = nextAdditive := by
                            simpa using congrArg (fun output => output.2.2.1)
                              outputEquation
                          subst folded
                          subst evaluated
                          subst foldedAdditive
                          exact ⟨{
                            reads := reads
                            boundaryRun := boundaryEquation
                            evaluateRun := evaluateEquation
                            weightFoldRun := foldEquation
                            additiveFoldRun := additiveEquation }⟩

/-- Every coefficient reconstructed by an accepted polynomial loop is a
canonical field encoding, because every one came from the translated
production decoder's rejection-checked success branch. -/
theorem accepted_exact_polynomial_is_canonical
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize) (additive nextAdditive : A)
    (round : Std.Usize)
    (trace : AcceptedExactPolynomialExecution additiveInst weights
      nextWeights claim nextClaim alpha bytes additive nextAdditive round) :
    AspisV5RelationGeneratedKernelProjection.CanonicalArray
      (sevenValues trace.reads.value0 trace.reads.value1 trace.reads.value2
        trace.reads.value3 trace.reads.value4 trace.reads.value5
        trace.reads.value6) := by
  have canonical0 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      0#usize) trace.reads.value0 trace.reads.read0
  have canonical1 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      1#usize) trace.reads.value1 trace.reads.read1
  have canonical2 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      2#usize) trace.reads.value2 trace.reads.read2
  have canonical3 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      3#usize) trace.reads.value3 trace.reads.read3
  have canonical4 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      4#usize) trace.reads.value4 trace.reads.read4
  have canonical5 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      5#usize) trace.reads.value5 trace.reads.read5
  have canonical6 := accepted_decode_indexed_is_canonical bytes
    trace.reads.offset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
      6#usize) trace.reads.value6 trace.reads.read6
  intro index indexBound
  interval_cases index <;>
    simp [sevenValues, Array.make] <;>
    assumption

/-- A successful result of the generated polynomial loop cannot have arisen
from a decoder error or boundary mismatch.  It therefore exposes the exact
polynomial and all four successful calls at the loop's terminal state. -/
theorem accepted_polynomial_loop_exposes_execution
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (toSliceBack : Slice RawQM31 → Array RawQM31 7#usize)
    (iterBack : core.slice.iter.IterMut RawQM31 → Slice RawQM31)
    (enumerateBack : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut RawQM31) → core.slice.iter.IterMut RawQM31)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut RawQM31))
    (back : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.IterMut RawQM31) →
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.IterMut RawQM31))
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim alpha : RawQM31)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (round : Std.Usize)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
          additiveInst toSliceBack iterBack enumerateBack iter back weights claim
          bytes additive round alpha none =
        .ok (nextWeights, nextClaim, nextAdditive, none, 1#u32)) :
    Nonempty (AcceptedPolynomialExecution additiveInst weights nextWeights
      claim nextClaim alpha additive nextAdditive) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
    at run
  obtain ⟨⟨originIter, originBack⟩, bodyRun⟩ :=
    loop_ok_has_done_origin_eq
      (fun state =>
        V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body
          additiveInst toSliceBack iterBack enumerateBack weights claim bytes
          additive round alpha none state.1 state.2)
      (iter, back) (nextWeights, nextClaim, nextAdditive, none, 1#u32) run
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0.body
    at bodyRun
  generalize nextEquation : V5MutableEnumerateSupport.next originIter =
      nextResult at bodyRun
  cases nextResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok next =>
      rcases next with ⟨option, nextIter, nextBack⟩
      simp only [bind_tc_ok] at bodyRun
      cases option with
      | none =>
          let polynomial :=
            toSliceBack (iterBack (enumerateBack
              (originBack (nextBack nextIter none))))
          generalize boundaryEquation :
              V5RelationFullGenerated.aspis_core.sumcheck.boundary_sum
                polynomial = boundaryResult at bodyRun
          cases boundaryResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok boundary =>
              simp only [bind_tc_ok] at bodyRun
              generalize neEquation :
                  core.cmp.PartialEq.ne.trait_default
                    V5RelationFullGenerated.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                    boundary claim = neResult at bodyRun
              cases neResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | ok differs =>
                  simp only [bind_tc_ok] at bodyRun
                  cases differs with
                  | true => simp at bodyRun
                  | false =>
                      simp only [Bool.false_eq_true, if_false] at bodyRun
                      generalize evaluateEquation :
                          V5RelationFullGenerated.aspis_core.sumcheck.evaluate
                            polynomial alpha = evaluateResult at bodyRun
                      cases evaluateResult with
                      | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                      | div =>
                          simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                      | ok evaluated =>
                          simp only [bind_tc_ok] at bodyRun
                          generalize foldEquation :
                              aspis_core.sumcheck.WeightAccumulator.fold
                                weights alpha = foldResult at bodyRun
                          cases foldResult with
                          | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | div =>
                              simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                          | ok folded =>
                              simp only [bind_tc_ok] at bodyRun
                              generalize additiveEquation :
                                  additiveInst.fold additive alpha =
                                    additiveResult at bodyRun
                              cases additiveResult with
                              | fail error =>
                                  simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                              | div =>
                                  simp [Bind.bind, Aeneas.Std.bind] at bodyRun
                              | ok foldedAdditive =>
                                  simp only [bind_tc_ok] at bodyRun
                                  have boundaryExact : boundary = claim := by
                                    rw [AspisV5RelationFullSourceProof.raw_qm31_ne_spec]
                                      at neEquation
                                    by_contra different
                                    simp [different] at neEquation
                                  subst boundary
                                  injection bodyRun with tupleEquation
                                  injection tupleEquation with outputEquation
                                  have weightsExact : folded = nextWeights := by
                                    simpa using congrArg
                                      (fun output => output.1) outputEquation
                                  have claimExact : evaluated = nextClaim := by
                                    simpa using congrArg
                                      (fun output => output.2.1) outputEquation
                                  have additiveExact :
                                      foldedAdditive = nextAdditive := by
                                    simpa using congrArg
                                      (fun output => output.2.2.1) outputEquation
                                  subst nextWeights
                                  subst nextClaim
                                  subst nextAdditive
                                  exact ⟨{
                                    polynomial := polynomial
                                    boundaryRun := boundaryEquation
                                    evaluateRun := evaluateEquation
                                    weightFoldRun := foldEquation
                                    additiveFoldRun := additiveEquation }⟩
      | some item =>
          rcases item with ⟨coefficient, oldValue⟩
          simp only [Aeneas.Std.lift, bind_tc_ok] at bodyRun
          generalize offsetEquation :
              V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_SUMCHECK_OFFSET =
                offsetResult at bodyRun
          cases offsetResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok offset =>
              simp only [bind_tc_ok] at bodyRun
              generalize decodeEquation :
                  V5RelationFullGenerated.relation_stress.decode_indexed bytes
                    offset
                    (Std.Usize.wrapping_add
                      (Std.Usize.wrapping_mul round
                        V5RelationFullGenerated.aspis_core.sumcheck.SUMCHECK_COEFFICIENTS)
                      coefficient) = decodeResult at bodyRun
              cases decodeResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
              | ok decoded =>
                  cases decoded with
                  | Ok decodedValue =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch]
                        at bodyRun
                  | Err decodeError =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame, core.convert.FromSame.from]
                        at bodyRun

/-- Adding one tensor component never changes the accumulator domain size. -/
private theorem add_tensor_factors_success_preserves_log_length
    (weights output :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (scale : RawQM31)
    (factors : alloc.vec.Vec RawQM31)
    (run :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
        weights scale factors = .ok (.Ok (), output)) :
    output.log_len = weights.log_len := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_tensor_factors
    at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  split at run
  · simp at run
  · generalize pushRun :
        alloc.vec.Vec.push weights.components
          (V5RelationFullGenerated.aspis_core.sumcheck.WeightComponent.Tensor
            scale factors) = pushResult at run
    cases pushResult with
    | fail error => simp at run
    | div => simp at run
    | ok components =>
        simp only [bind_tc_ok, Result.ok.injEq] at run
        have outputExact :
            ({ weights with components := components } :
              V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator) =
              output := congrArg (fun pair => pair.2) run
        rw [← outputExact]

/-- The circle-tensor preparation path changes components but preserves the
domain size on every successful call. -/
private theorem add_circle_tensor_success_preserves_log_length
    (weights output :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (scale : RawQM31)
    (point : V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint)
    (run :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
        weights scale point = .ok (.Ok (), output)) :
    output.log_len = weights.log_len := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
    at run
  split at run
  · simp at run
  · simp only [Aeneas.Std.lift, bind_tc_ok] at run
    generalize firstPush :
        alloc.vec.Vec.push
          (alloc.vec.Vec.with_capacity RawQM31
            (UScalar.cast .Usize weights.log_len)) point.y = firstResult at run
    cases firstResult with
    | fail error => simp at run
    | div => simp at run
    | ok first =>
      simp only [bind_tc_ok] at run
      generalize secondPush : alloc.vec.Vec.push first point.x = secondResult at run
      cases secondResult with
      | fail error => simp at run
      | div => simp at run
      | ok second =>
        simp only [bind_tc_ok] at run
        generalize loopRun :
            V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor_loop
              { start := 2#u32, «end» := weights.log_len } second point.x =
                loopResult at run
        cases loopResult with
        | fail error => simp at run
        | div => simp at run
        | ok factors =>
          simp only [bind_tc_ok, Aeneas.Std.lift] at run
          exact add_tensor_factors_success_preserves_log_length weights output
            scale _ run

/-- The line-tensor preparation path changes components but preserves the
domain size on every successful call. -/
private theorem add_line_tensor_success_preserves_log_length
    (weights output :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (scale x : RawQM31)
    (run :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
        weights scale x = .ok (.Ok (), output)) :
    output.log_len = weights.log_len := by
  unfold
    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
    at run
  simp only [Aeneas.Std.lift, bind_tc_ok] at run
  generalize loopRun :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor_loop
        { start := 0#u32, «end» := weights.log_len } weights.log_len x
          (alloc.vec.Vec.with_capacity RawQM31
            (UScalar.cast .Usize weights.log_len)) = loopResult at run
  cases loopResult with
  | fail error => simp at run
  | div => simp at run
  | ok factors =>
      simp only [bind_tc_ok, Aeneas.Std.lift] at run
      exact add_tensor_factors_success_preserves_log_length weights output
        scale _ run

/-- Scalar calls made by one successful off-domain sample iteration.  The
two decoder equalities retain the exact word positions consumed from the
accepted 928-byte body. -/
structure AcceptedSampleExecution
    (bytes : Array Std.U8 928#usize)
    (round sample : Std.Usize)
    (incoming outgoing : RawQM31) : Type where
  oodOffset : Std.Usize
  mixOffset : Std.Usize
  value : RawQM31
  mix : RawQM31
  product : RawQM31
  oodOffsetRun :
    V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_OFFSET =
      .ok oodOffset
  mixOffsetRun :
    V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_MIX_OFFSET =
      .ok mixOffset
  valueDecodeRun :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes oodOffset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
        sample) = .ok (.Ok value)
  mixDecodeRun :
    V5RelationFullGenerated.relation_stress.decode_indexed bytes mixOffset
      (Std.Usize.wrapping_add
        (Std.Usize.wrapping_mul round
          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
        sample) = .ok (.Ok mix)
  productRun :
    V5RelationFullGenerated.aspis_core.field.QM31.mul mix value = .ok product
  claimRun :
    V5RelationFullGenerated.aspis_core.field.QM31.add incoming product =
      .ok outgoing

/-- The exact production weight update selected by one accepted sample.
For round zero this retains the circle point read from the accepted point
array and the successful `add_circle_tensor` call.  For later rounds it
retains the decoded line coordinate and the successful `add_line_tensor`
call.  The inactive alternative is discharged from the round test, so this
record contains no independently supplied tensor data. -/
structure AcceptedSampleWeightUpdate
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round sample : Std.Usize)
    (mix : RawQM31)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator) : Type where
  circle : round = 0#usize →
    ∃ point,
      Array.index_usize circlePoints sample = .ok point ∧
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
        weights mix point = .ok (.Ok (), nextWeights)
  line : round ≠ 0#usize →
    ∃ lineOffset lineValue,
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_LINE_OFFSET =
        .ok lineOffset ∧
      V5RelationFullGenerated.relation_stress.decode_indexed bytes lineOffset
        (Std.Usize.wrapping_add
          (Std.Usize.wrapping_mul
            (Std.Usize.wrapping_sub round 1#usize)
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
          sample) = .ok (.Ok lineValue) ∧
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
        weights mix lineValue = .ok (.Ok (), nextWeights)

structure AcceptedSampleBodyExecution
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round sample : Std.Usize)
    (incoming outgoing : RawQM31)
    (actualNextRange expectedNextRange : core.ops.range.Range Std.Usize)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator) :
    Type where
  scalar : AcceptedSampleExecution bytes round sample incoming outgoing
  rangeExact : actualNextRange = expectedNextRange
  weightLogExact : nextWeights.log_len = weights.log_len
  weightUpdate : AcceptedSampleWeightUpdate bytes circlePoints round sample
    scalar.mix weights nextWeights

private theorem accepted_sample_arithmetic_tail
    {Done : Type}
    (mix value incoming : RawQM31)
    (originRange nextRange : core.ops.range.Range Std.Usize)
    (originWeights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (outgoing : RawQM31)
    (run :
      (do
        let product ←
          V5RelationFullGenerated.aspis_core.field.QM31.mul mix value
        let updated ←
          V5RelationFullGenerated.aspis_core.field.QM31.add incoming product
        ok (cont (originRange, originWeights, updated))) =
      (ok (cont (nextRange, nextWeights, outgoing)) :
        Result (ControlFlow
          (core.ops.range.Range Std.Usize ×
            V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator ×
            RawQM31)
          Done))) :
    ∃ product,
      V5RelationFullGenerated.aspis_core.field.QM31.mul mix value = .ok product ∧
      V5RelationFullGenerated.aspis_core.field.QM31.add incoming product =
        .ok outgoing ∧
      originRange = nextRange ∧ originWeights = nextWeights := by
  generalize productEquation :
      V5RelationFullGenerated.aspis_core.field.QM31.mul mix value =
        productResult at run
  cases productResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok product =>
      simp only [bind_tc_ok] at run
      generalize claimEquation :
          V5RelationFullGenerated.aspis_core.field.QM31.add incoming product =
            claimResult at run
      cases claimResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok updated =>
          simp only [bind_tc_ok] at run
          injection run with flowEquation
          injection flowEquation with outputEquation
          have rangeExact : originRange = nextRange := by
            simpa using congrArg (fun output => output.1) outputEquation
          have weightsExact : originWeights = nextWeights := by
            simpa using congrArg (fun output => output.2.1) outputEquation
          have claimExact : updated = outgoing := by
            simpa using congrArg (fun output => output.2.2) outputEquation
          subst outgoing
          exact ⟨product, rfl, claimEquation, rangeExact,
            weightsExact⟩

/-- A successful generated sample-loop body exposes the two accepted decoded
field values and the exact multiply/add update.  Circle and later-line weight
updates are both inverted; neither is left as a control-flow assumption. -/
theorem accepted_sample_body_exposes_execution
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (additive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round sample : Std.Usize)
    (alpha : RawQM31)
    (range expectedNextRange actualNextRange : core.ops.range.Range Std.Usize)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim : RawQM31)
    (nextExact :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some sample, expectedNextRange))
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha none range
          weights claim = .ok (.cont (actualNextRange, nextWeights, nextClaim))) :
    Nonempty (AcceptedSampleBodyExecution bytes circlePoints round sample claim
      nextClaim actualNextRange expectedNextRange weights nextWeights) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
    at run
  rw [nextExact] at run
  simp only [bind_tc_ok, Aeneas.Std.lift] at run
  generalize oodOffsetEquation :
      V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_OFFSET =
        oodOffsetResult at run
  cases oodOffsetResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok oodOffset =>
      simp only [bind_tc_ok] at run
      generalize oodDecodeEquation :
          V5RelationFullGenerated.relation_stress.decode_indexed bytes
            oodOffset
            (Std.Usize.wrapping_add
              (Std.Usize.wrapping_mul round
                V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
              sample) = oodDecodeResult at run
      cases oodDecodeResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok oodDecoded =>
          cases oodDecoded with
          | Err oodError =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at run
          | Ok oodValue =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at run
              generalize mixOffsetEquation :
                  V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_MIX_OFFSET =
                    mixOffsetResult at run
              cases mixOffsetResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok mixOffset =>
                  simp only [bind_tc_ok] at run
                  generalize mixDecodeEquation :
                      V5RelationFullGenerated.relation_stress.decode_indexed bytes
                        mixOffset
                        (Std.Usize.wrapping_add
                          (Std.Usize.wrapping_mul round
                            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
                          sample) = mixDecodeResult at run
                  cases mixDecodeResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok mixDecoded =>
                      cases mixDecoded with
                      | Err mixError =>
                          simp [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from] at run
                      | Ok mixValue =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,
                            bind_tc_ok] at run
                          by_cases roundZero : round = 0#usize
                          · rw [roundZero] at run
                            simp only [if_true] at run
                            generalize pointEquation :
                                Array.index_usize circlePoints sample =
                                  pointResult at run
                            cases pointResult with
                            | fail error =>
                                simp [Bind.bind, Aeneas.Std.bind] at run
                            | div =>
                                simp [Bind.bind, Aeneas.Std.bind] at run
                            | ok point =>
                                simp only [bind_tc_ok] at run
                                generalize tensorEquation :
                                    V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_circle_tensor
                                      weights mixValue point = tensorResult at run
                                cases tensorResult with
                                | fail error =>
                                    simp [Bind.bind, Aeneas.Std.bind] at run
                                | div =>
                                    simp [Bind.bind, Aeneas.Std.bind] at run
                                | ok tensorOutput =>
                                    rcases tensorOutput with
                                      ⟨tensorStatus, tensorWeights⟩
                                    cases tensorStatus with
                                    | Err tensorError =>
                                        simp [core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          V5RelationFullGenerated.relation_stress.V5RelationStressError.Insts.CoreConvertFromTensorWeightError.from]
                                          at run
                                    | Ok unitValue =>
                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                          bind_tc_ok] at run
                                        obtain ⟨product, productRun, claimRun,
                                            rangeExact, weightsExact⟩ :=
                                          accepted_sample_arithmetic_tail
                                            mixValue oodValue claim
                                            expectedNextRange actualNextRange
                                            tensorWeights nextWeights
                                            nextClaim run
                                        exact ⟨{
                                          scalar := {
                                          oodOffset := oodOffset
                                          mixOffset := mixOffset
                                          value := oodValue
                                          mix := mixValue
                                          product := product
                                          oodOffsetRun := oodOffsetEquation
                                          mixOffsetRun := mixOffsetEquation
                                          valueDecodeRun := oodDecodeEquation
                                          mixDecodeRun := mixDecodeEquation
                                          productRun := productRun
                                          claimRun := claimRun }
                                          rangeExact := rangeExact.symm
                                          weightLogExact := by
                                            rw [← weightsExact]
                                            exact
                                              add_circle_tensor_success_preserves_log_length
                                                weights tensorWeights mixValue
                                                point (by simpa using tensorEquation)
                                          weightUpdate := {
                                            circle := fun _ =>
                                              ⟨point, pointEquation, by
                                                simpa [weightsExact] using
                                                  tensorEquation⟩
                                            line := fun nonzero =>
                                              (nonzero roundZero).elim } }⟩
                          · simp only [roundZero, if_false] at run
                            generalize lineOffsetEquation :
                                V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_LINE_OFFSET =
                                  lineOffsetResult at run
                            cases lineOffsetResult with
                            | fail error =>
                                simp [Bind.bind, Aeneas.Std.bind] at run
                            | div =>
                                simp [Bind.bind, Aeneas.Std.bind] at run
                            | ok lineOffset =>
                                simp only [bind_tc_ok] at run
                                generalize lineDecodeEquation :
                                    V5RelationFullGenerated.relation_stress.decode_indexed
                                      bytes lineOffset
                                      (Std.Usize.wrapping_add
                                        (Std.Usize.wrapping_mul
                                          (Std.Usize.wrapping_sub round 1#usize)
                                          V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
                                        sample) = lineDecodeResult at run
                                cases lineDecodeResult with
                                | fail error =>
                                    simp [Bind.bind, Aeneas.Std.bind] at run
                                | div =>
                                    simp [Bind.bind, Aeneas.Std.bind] at run
                                | ok lineDecoded =>
                                    cases lineDecoded with
                                    | Err lineError =>
                                        simp [core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          core.convert.FromSame.from] at run
                                    | Ok lineValue =>
                                        simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                          bind_tc_ok] at run
                                        generalize tensorEquation :
                                            V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator.add_line_tensor
                                              weights mixValue lineValue =
                                                tensorResult at run
                                        cases tensorResult with
                                        | fail error =>
                                            simp [Bind.bind, Aeneas.Std.bind] at run
                                        | div =>
                                            simp [Bind.bind, Aeneas.Std.bind] at run
                                        | ok tensorOutput =>
                                            rcases tensorOutput with
                                              ⟨tensorStatus, tensorWeights⟩
                                            cases tensorStatus with
                                            | Err tensorError =>
                                                simp [core.result.Result.Insts.CoreOpsTry.branch,
                                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                  V5RelationFullGenerated.relation_stress.V5RelationStressError.Insts.CoreConvertFromTensorWeightError.from]
                                                  at run
                                            | Ok unitValue =>
                                                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                                  bind_tc_ok] at run
                                                obtain ⟨product, productRun,
                                                    claimRun, rangeExact,
                                                    weightsExact⟩ :=
                                                  accepted_sample_arithmetic_tail
                                                    mixValue oodValue claim
                                                    expectedNextRange actualNextRange
                                                    tensorWeights nextWeights
                                                    nextClaim run
                                                exact ⟨{
                                                  scalar := {
                                                  oodOffset := oodOffset
                                                  mixOffset := mixOffset
                                                  value := oodValue
                                                  mix := mixValue
                                                  product := product
                                                  oodOffsetRun := oodOffsetEquation
                                                  mixOffsetRun := mixOffsetEquation
                                                  valueDecodeRun := oodDecodeEquation
                                                  mixDecodeRun := mixDecodeEquation
                                                  productRun := productRun
                                                  claimRun := claimRun }
                                                  rangeExact := rangeExact.symm
                                                  weightLogExact := by
                                                    rw [← weightsExact]
                                                    exact
                                                      add_line_tensor_success_preserves_log_length
                                                        weights tensorWeights
                                                        mixValue lineValue
                                                        (by simpa using tensorEquation)
                                                  weightUpdate := {
                                                    circle := fun zero =>
                                                      (roundZero zero).elim
                                                    line := fun _ =>
                                                      ⟨lineOffset, lineValue,
                                                        lineOffsetEquation,
                                                        lineDecodeEquation, by
                                                          simpa [weightsExact]
                                                            using tensorEquation⟩ } }⟩

/-- An active sample cannot terminate the round with the successful
`(pending = none, status = 1)` marker.  Every active success continues to the
next range state; every active termination carries an error and status zero. -/
private theorem bind_eq_ok_iff {A B : Type} (input : Result A)
    (next : A → Result B) (output : B) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

theorem active_sample_body_not_done_success
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round sample : Std.Usize)
    (alpha : RawQM31)
    (range nextRange : core.ops.range.Range Std.Usize)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim : RawQM31)
    (nextExact :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range =
        .ok (some sample, nextRange))
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha none range
          weights claim =
        .ok (.done (nextWeights, nextClaim, nextAdditive, none, 1#u32))) :
    False := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
    at run
  rw [nextExact] at run
  simp only [bind_tc_ok, Aeneas.Std.lift] at run
  rw [bind_eq_ok_iff] at run
  rcases run with ⟨oodOffset, _oodOffsetRun, run⟩
  rw [bind_eq_ok_iff] at run
  rcases run with ⟨oodDecoded, _oodDecodeRun, run⟩
  cases oodDecoded with
  | Err oodError =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run
  | Ok oodValue =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨mixOffset, _mixOffsetRun, run⟩
      rw [bind_eq_ok_iff] at run
      rcases run with ⟨mixDecoded, _mixDecodeRun, run⟩
      cases mixDecoded with
      | Err mixError =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
      | Ok mixValue =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          by_cases roundZero : round = 0#usize
          · rw [roundZero] at run
            simp only [if_true] at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨point, _pointRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨tensorOutput, _tensorRun, run⟩
            rcases tensorOutput with ⟨tensorStatus, tensorWeights⟩
            cases tensorStatus with
            | Err tensorError =>
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  V5RelationFullGenerated.relation_stress.V5RelationStressError.Insts.CoreConvertFromTensorWeightError.from]
                  at run
            | Ok unitValue =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  bind_tc_ok] at run
                rw [bind_eq_ok_iff] at run
                rcases run with ⟨product, _productRun, run⟩
                rw [bind_eq_ok_iff] at run
                rcases run with ⟨updated, _claimRun, run⟩
                simp at run
          · simp only [roundZero, if_false] at run
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨lineOffset, _lineOffsetRun, run⟩
            rw [bind_eq_ok_iff] at run
            rcases run with ⟨lineDecoded, _lineDecodeRun, run⟩
            cases lineDecoded with
            | Err lineError =>
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from] at run
            | Ok lineValue =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  bind_tc_ok] at run
                rw [bind_eq_ok_iff] at run
                rcases run with ⟨tensorOutput, _tensorRun, run⟩
                rcases tensorOutput with ⟨tensorStatus, tensorWeights⟩
                cases tensorStatus with
                | Err tensorError =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      V5RelationFullGenerated.relation_stress.V5RelationStressError.Insts.CoreConvertFromTensorWeightError.from]
                      at run
                | Ok unitValue =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      bind_tc_ok] at run
                    rw [bind_eq_ok_iff] at run
                    rcases run with ⟨product, _productRun, run⟩
                    rw [bind_eq_ok_iff] at run
                    rcases run with ⟨updated, _claimRun, run⟩
                    simp at run

/-- When the fixed two-sample range is exhausted, a successful body result
comes from the generated seven-coefficient loop, with the same weight,
claim, and additive outputs. -/
theorem accepted_sample_exhaustion_exposes_polynomial
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize)
    (alpha : RawQM31)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim : RawQM31)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha none
          (range2At 2#usize) weights claim =
        .ok (.done (nextWeights, nextClaim, nextAdditive, none, 1#u32))) :
    Nonempty (AcceptedConcretePolynomialExecution additiveInst weights
      nextWeights claim nextClaim alpha bytes additive nextAdditive round) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
    at run
  rw [range2_next_none] at run
  simp only [bind_tc_ok, Aeneas.Std.lift, core.slice.Slice.iter_mut,
    V5MutableEnumerateSupport.enumerate] at run
  let polynomialIterator : V5MutableEnumerateSupport.MutEnumerate RawQM31 :=
    { iter := { slice := (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1 }
      count := 0#usize }
  generalize polynomialEquation :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
        additiveInst
        (Array.repeat 7#usize
          V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2
        (fun iterator => iterator.slice)
        (fun enumerated => enumerated.iter)
        polynomialIterator (fun e => e) weights claim bytes additive round
        alpha none = polynomialResult at run
  cases polynomialResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok polynomialOutput =>
      rcases polynomialOutput with
        ⟨polynomialWeights, polynomialClaim, polynomialAdditive,
          polynomialPending, polynomialStatus⟩
      simp only [bind_tc_ok] at run
      by_cases successfulStatus : polynomialStatus = 1#u32
      · subst polynomialStatus
        injection run with tupleEquation
        injection tupleEquation with outputEquation
        have weightsExact : polynomialWeights = nextWeights := by
          simpa using congrArg (fun output => output.1) outputEquation
        have claimExact : polynomialClaim = nextClaim := by
          simpa using congrArg (fun output => output.2.1) outputEquation
        have additiveExact : polynomialAdditive = nextAdditive := by
          simpa using congrArg (fun output => output.2.2.1) outputEquation
        have pendingExact : polynomialPending = none := by
          simpa using congrArg (fun output => output.2.2.2.1) outputEquation
        subst polynomialWeights
        subst polynomialClaim
        subst polynomialAdditive
        subst polynomialPending
        obtain ⟨scalar⟩ := accepted_polynomial_loop_exposes_execution
          additiveInst
          (Array.repeat 7#usize
            V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2
          (fun iterator => iterator.slice)
          (fun enumerated => enumerated.iter)
          polynomialIterator (fun e => e) weights nextWeights claim nextClaim
          alpha bytes additive nextAdditive round polynomialEquation
        exact ⟨{
          scalar := scalar
          concreteRun := by
            simpa [concretePolynomialLoopCall, initialPolynomialIterator,
              polynomialIterator] using polynomialEquation }⟩
      · split at run
        case h_1 =>
          rcases run with ⟨weightsExact, claimExact, additiveExact,
            pendingExact⟩
          obtain ⟨scalar⟩ := accepted_polynomial_loop_exposes_execution
            additiveInst
            (Array.repeat 7#usize
              V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2
            (fun iterator => iterator.slice)
            (fun enumerated => enumerated.iter)
            polynomialIterator (fun e => e) weights nextWeights claim nextClaim
            alpha bytes additive nextAdditive round polynomialEquation
          exact ⟨{
            scalar := scalar
            concreteRun := by
              have statusLiteralExact :
                  (1#32#uscalar : Std.U32) = 1#u32 := by
                apply UScalar.eq_of_val_eq
                rfl
              rw [statusLiteralExact] at polynomialEquation
              simpa [concretePolynomialLoopCall, initialPolynomialIterator,
                polynomialIterator] using polynomialEquation }⟩
        case h_2 =>
          split at run <;> simp_all

theorem exhausted_sample_body_not_cont
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (additive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize)
    (alpha : RawQM31)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim : RawQM31)
    (nextRange : core.ops.range.Range Std.Usize)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
          additiveInst bytes additive circlePoints round alpha none
          (range2At 2#usize) weights claim =
        .ok (.cont (nextRange, nextWeights, nextClaim))) : False := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
    at run
  rw [range2_next_none] at run
  simp only [bind_tc_ok, Aeneas.Std.lift, core.slice.Slice.iter_mut,
    V5MutableEnumerateSupport.enumerate] at run
  let polynomialIterator : V5MutableEnumerateSupport.MutEnumerate RawQM31 :=
    { iter := { slice := (Array.repeat 7#usize
        V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.1 }
      count := 0#usize }
  generalize polynomialEquation :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0_loop0
        additiveInst
        (Array.repeat 7#usize
          V5RelationFullGenerated.aspis_core.field.QM31.ZERO).to_slice_mut.2
        (fun iterator => iterator.slice)
        (fun enumerated => enumerated.iter)
        polynomialIterator (fun e => e) weights claim bytes additive round
        alpha none = polynomialResult at run
  cases polynomialResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok polynomialOutput =>
      rcases polynomialOutput with
        ⟨polynomialWeights, polynomialClaim, polynomialAdditive,
          polynomialPending, polynomialStatus⟩
      simp only [bind_tc_ok] at run
      split at run
      · simp at run
      · split at run <;> simp at run

/-- Exact scalar evidence recovered from the released two-sample round. -/
structure AcceptedTwoSampleRoundExecution {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (additive nextAdditive : A)
    (round : Std.Usize)
    (alpha : RawQM31)
    (weights0 nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 nextClaim : RawQM31) : Type where
  weights1 : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
  claim1 : RawQM31
  weights2 : V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator
  claim2 : RawQM31
  sample0 : AcceptedSampleExecution bytes round 0#usize claim0 claim1
  sample1 : AcceptedSampleExecution bytes round 1#usize claim1 claim2
  sample0WeightLog : weights1.log_len = weights0.log_len
  sample1WeightLog : weights2.log_len = weights1.log_len
  sample0WeightUpdate : AcceptedSampleWeightUpdate bytes circlePoints round
    0#usize sample0.mix weights0 weights1
  sample1WeightUpdate : AcceptedSampleWeightUpdate bytes circlePoints round
    1#usize sample1.mix weights1 weights2
  polynomial : AcceptedConcretePolynomialExecution additiveInst weights2
    nextWeights claim2 nextClaim alpha bytes additive nextAdditive round

/-- The maintained arithmetic record together with the exact input, alpha,
and output identities of the accepted translated round that produced it. -/
structure AcceptedRawRoundProjection
    (incoming alpha outgoing : RawQM31) : Type where
  raw : AspisV5AcceptedRelationRoundProjection.AcceptedRawRoundArithmetic
  incomingExact : raw.incoming = incoming
  alphaExact : raw.alpha = alpha
  outgoingExact : raw.outgoing = outgoing

/-- One accepted translated round yields exactly the arithmetic record used
by the maintained round theorem. -/
theorem accepted_round_exposes_raw_arithmetic
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (additive nextAdditive : A)
    (round : Std.Usize)
    (alpha : RawQM31)
    (weights0 nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 nextClaim : RawQM31)
    (incomingCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 claim0)
    (alphaCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 alpha)
    (trace : AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim) :
    Nonempty (AcceptedRawRoundProjection claim0 alpha nextClaim) := by
  obtain ⟨polynomial⟩ :=
    accepted_concrete_polynomial_exposes_exact_execution additiveInst
      trace.weights2 nextWeights trace.claim2 nextClaim alpha bytes additive
      nextAdditive round trace.polynomial
  have firstValueCanonical := accepted_decode_indexed_is_canonical bytes
    trace.sample0.oodOffset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
      0#usize) trace.sample0.value trace.sample0.valueDecodeRun
  have firstMixCanonical := accepted_decode_indexed_is_canonical bytes
    trace.sample0.mixOffset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
      0#usize) trace.sample0.mix trace.sample0.mixDecodeRun
  have secondValueCanonical := accepted_decode_indexed_is_canonical bytes
    trace.sample1.oodOffset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
      1#usize) trace.sample1.value trace.sample1.valueDecodeRun
  have secondMixCanonical := accepted_decode_indexed_is_canonical bytes
    trace.sample1.mixOffset
    (Std.Usize.wrapping_add
      (Std.Usize.wrapping_mul round
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES)
      1#usize) trace.sample1.mix trace.sample1.mixDecodeRun
  let raw :
      AspisV5AcceptedRelationRoundProjection.AcceptedRawRoundArithmetic := {
    incoming := claim0
    firstValue := trace.sample0.value
    secondValue := trace.sample1.value
    firstMix := trace.sample0.mix
    secondMix := trace.sample1.mix
    firstProduct := trace.sample0.product
    claimAfterFirst := trace.claim1
    secondProduct := trace.sample1.product
    claimAfterSecond := trace.claim2
    polynomial := sevenValues polynomial.reads.value0 polynomial.reads.value1
      polynomial.reads.value2 polynomial.reads.value3 polynomial.reads.value4
      polynomial.reads.value5 polynomial.reads.value6
    alpha := alpha
    outgoing := nextClaim
    incomingCanonical := incomingCanonical
    firstValueCanonical := firstValueCanonical
    secondValueCanonical := secondValueCanonical
    firstMixCanonical := firstMixCanonical
    secondMixCanonical := secondMixCanonical
    polynomialCanonical := accepted_exact_polynomial_is_canonical
      additiveInst trace.weights2 nextWeights trace.claim2 nextClaim alpha bytes
      additive nextAdditive round polynomial
    alphaCanonical := alphaCanonical
    firstProductRun := trace.sample0.productRun
    firstClaimRun := trace.sample0.claimRun
    secondProductRun := trace.sample1.productRun
    secondClaimRun := trace.sample1.claimRun
    boundaryRun := polynomial.boundaryRun
    evaluateRun := polynomial.evaluateRun }
  exact ⟨{
    raw := raw
    incomingExact := rfl
    alphaExact := rfl
    outgoingExact := rfl }⟩

/-- Invert the generated fixed two-sample loop in execution order.  The two
active bodies must continue through ranges `0→1→2`; only the exhausted
body can return the successful round marker. -/
theorem accepted_two_sample_loop_exposes_execution
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (additive nextAdditive : A)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (round : Std.Usize)
    (alpha : RawQM31)
    (weights0 nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim0 nextClaim : RawQM31)
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
          additiveInst (range2At 0#usize) weights0 claim0 bytes additive
          circlePoints round alpha none =
        .ok (nextWeights, nextClaim, nextAdditive, none, 1#u32)) :
    Nonempty (AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights0 nextWeights claim0 nextClaim) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
    at run
  rw [Aeneas.Std.loop.eq_def] at run
  simp only at run
  generalize body0Equation :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
        additiveInst bytes additive circlePoints round alpha none
        (range2At 0#usize) weights0 claim0 = body0 at run
  cases body0 with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok flow0 =>
      cases flow0 with
      | done output0 =>
          rcases output0 with ⟨doneWeights, doneClaim, doneAdditive,
            donePending, doneStatus⟩
          simp only [bind_tc_ok] at run
          injection run with outputEquation
          have weightsExact : doneWeights = nextWeights := by
            simpa using congrArg (fun output => output.1) outputEquation
          have claimExact : doneClaim = nextClaim := by
            simpa using congrArg (fun output => output.2.1) outputEquation
          have additiveExact : doneAdditive = nextAdditive := by
            simpa using congrArg (fun output => output.2.2.1) outputEquation
          have pendingExact : donePending = none := by
            simpa using congrArg (fun output => output.2.2.2.1) outputEquation
          have statusExact : doneStatus = 1#u32 := by
            simpa using congrArg (fun output => output.2.2.2.2) outputEquation
          subst doneWeights
          subst doneClaim
          subst doneAdditive
          subst donePending
          subst doneStatus
          exact (active_sample_body_not_done_success additiveInst bytes
            additive nextAdditive circlePoints round 0#usize alpha
            (range2At 0#usize) (range2At 1#usize) weights0 nextWeights
            claim0 nextClaim range2_next_zero body0Equation).elim
      | cont state0 =>
          rcases state0 with ⟨actualRange1, weights1, claim1⟩
          simp only [bind_tc_ok] at run
          obtain ⟨sample0Body⟩ := accepted_sample_body_exposes_execution
            additiveInst bytes additive circlePoints round 0#usize alpha
            (range2At 0#usize) (range2At 1#usize) actualRange1 weights0
            weights1 claim0 claim1 range2_next_zero body0Equation
          rw [sample0Body.rangeExact] at run
          rw [Aeneas.Std.loop.eq_def] at run
          simp only at run
          generalize body1Equation :
              V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
                additiveInst bytes additive circlePoints round alpha none
                (range2At 1#usize) weights1 claim1 = body1 at run
          cases body1 with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok flow1 =>
              cases flow1 with
              | done output1 =>
                  rcases output1 with ⟨doneWeights, doneClaim, doneAdditive,
                    donePending, doneStatus⟩
                  simp only [bind_tc_ok] at run
                  injection run with outputEquation
                  have weightsExact : doneWeights = nextWeights := by
                    simpa using congrArg (fun output => output.1) outputEquation
                  have claimExact : doneClaim = nextClaim := by
                    simpa using congrArg (fun output => output.2.1) outputEquation
                  have additiveExact : doneAdditive = nextAdditive := by
                    simpa using congrArg (fun output => output.2.2.1) outputEquation
                  have pendingExact : donePending = none := by
                    simpa using congrArg (fun output => output.2.2.2.1) outputEquation
                  have statusExact : doneStatus = 1#u32 := by
                    simpa using congrArg (fun output => output.2.2.2.2) outputEquation
                  subst doneWeights
                  subst doneClaim
                  subst doneAdditive
                  subst donePending
                  subst doneStatus
                  exact (active_sample_body_not_done_success additiveInst
                    bytes additive nextAdditive circlePoints round 1#usize
                    alpha (range2At 1#usize) (range2At 2#usize) weights1
                    nextWeights claim1 nextClaim range2_next_one
                    body1Equation).elim
              | cont state1 =>
                  rcases state1 with ⟨actualRange2, weights2, claim2⟩
                  simp only [bind_tc_ok] at run
                  obtain ⟨sample1Body⟩ :=
                    accepted_sample_body_exposes_execution additiveInst bytes
                      additive circlePoints round 1#usize alpha
                      (range2At 1#usize) (range2At 2#usize) actualRange2
                      weights1 weights2 claim1 claim2 range2_next_one
                      body1Equation
                  rw [sample1Body.rangeExact] at run
                  rw [Aeneas.Std.loop.eq_def] at run
                  simp only at run
                  generalize exhaustionEquation :
                      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0.body
                        additiveInst bytes additive circlePoints round alpha none
                        (range2At 2#usize) weights2 claim2 = exhaustedBody at run
                  cases exhaustedBody with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok exhaustedFlow =>
                      cases exhaustedFlow with
                      | cont exhaustedState =>
                          rcases exhaustedState with
                            ⟨exhaustedRange, exhaustedWeights,
                              exhaustedClaim⟩
                          exact (exhausted_sample_body_not_cont additiveInst
                            bytes additive circlePoints round alpha weights2
                            exhaustedWeights claim2 exhaustedClaim
                            exhaustedRange exhaustionEquation).elim
                      | done exhaustedOutput =>
                          rcases exhaustedOutput with
                            ⟨polynomialWeights, polynomialClaim,
                              polynomialAdditive, polynomialPending,
                              polynomialStatus⟩
                          simp only [bind_tc_ok] at run
                          injection run with outputEquation
                          have weightsExact : polynomialWeights = nextWeights := by
                            simpa using congrArg (fun output => output.1)
                              outputEquation
                          have claimExact : polynomialClaim = nextClaim := by
                            simpa using congrArg (fun output => output.2.1)
                              outputEquation
                          have additiveExact : polynomialAdditive =
                              nextAdditive := by
                            simpa using congrArg (fun output => output.2.2.1)
                              outputEquation
                          have pendingExact : polynomialPending = none := by
                            simpa using congrArg (fun output => output.2.2.2.1)
                              outputEquation
                          have statusExact : polynomialStatus = 1#u32 := by
                            simpa using congrArg (fun output => output.2.2.2.2)
                              outputEquation
                          subst polynomialWeights
                          subst polynomialClaim
                          subst polynomialAdditive
                          subst polynomialPending
                          subst polynomialStatus
                          obtain ⟨polynomial⟩ :=
                            accepted_sample_exhaustion_exposes_polynomial
                              additiveInst bytes additive nextAdditive
                              circlePoints round alpha weights2 nextWeights
                              claim2 nextClaim exhaustionEquation
                          exact ⟨{
                            weights1 := weights1
                            claim1 := claim1
                            weights2 := weights2
                            claim2 := claim2
                            sample0 := sample0Body.scalar
                            sample1 := sample1Body.scalar
                            sample0WeightLog := sample0Body.weightLogExact
                            sample1WeightLog := sample1Body.weightLogExact
                            sample0WeightUpdate := sample0Body.weightUpdate
                            sample1WeightUpdate := sample1Body.weightUpdate
                            polynomial := polynomial }⟩

/-- A successful active outer-round body exposes the exact generated inner
two-sample execution for the `(round, alpha)` returned by its iterator. -/
theorem accepted_outer_round_body_exposes_execution
    {A : Type}
    (additiveInst :
      V5RelationFullGenerated.relation_stress.V5RelationStressAdditive A)
    (bytes : Array Std.U8 928#usize)
    (circlePoints : Array
      V5RelationFullGenerated.aspis_core.circle.SecureCirclePoint 2#usize)
    (iter nextIter : core.iter.adapters.enumerate.Enumerate
      (core.array.iter.IntoIter RawQM31 4#usize))
    (round : Std.Usize)
    (alpha : RawQM31)
    (weights nextWeights :
      V5RelationFullGenerated.aspis_core.sumcheck.WeightAccumulator)
    (claim nextClaim : RawQM31)
    (additive nextAdditive : A)
    (nextExact :
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize) iter =
        .ok (some (round, alpha), nextIter))
    (run :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
          additiveInst bytes circlePoints iter weights claim additive none =
        .ok (.cont
          (nextIter, nextWeights, nextClaim, nextAdditive, none))) :
    Nonempty (AcceptedTwoSampleRoundExecution additiveInst bytes circlePoints
      additive nextAdditive round alpha weights nextWeights claim nextClaim) := by
  unfold
    V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0.body
    at run
  rw [nextExact] at run
  simp only [bind_tc_ok] at run
  let initialRange : core.ops.range.Range Std.Usize :=
    { start := 0#usize
      «end» :=
        V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES }
  generalize innerEquation :
      V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
        additiveInst initialRange weights claim bytes additive circlePoints
        round alpha none = innerResult at run
  cases innerResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok innerOutput =>
      rcases innerOutput with
        ⟨innerWeights, innerClaim, innerAdditive, innerPending,
          innerStatus⟩
      simp only [bind_tc_ok] at run
      split at run
      · rcases run with ⟨iteratorExact, weightsExact, claimExact,
          additiveExact, pendingExact⟩
        have statusLiteralExact :
            (1#32#uscalar : Std.U32) = 1#u32 := by
          apply UScalar.eq_of_val_eq
          rfl
        rw [statusLiteralExact] at innerEquation
        have normalizedInner :
            V5RelationFullGenerated.relation_stress.verify_v5_relation_stress_with_additive_loop0_loop0_loop0
              additiveInst (range2At 0#usize) weights claim bytes additive
              circlePoints round alpha none =
            .ok (nextWeights, nextClaim, nextAdditive, none, 1#u32) := by
          simpa [initialRange, range2At,
            V5RelationFullGenerated.relation_stress.V5_RELATION_STRESS_OOD_SAMPLES]
            using innerEquation
        exact accepted_two_sample_loop_exposes_execution additiveInst bytes
          additive nextAdditive circlePoints round alpha weights nextWeights
          claim nextClaim normalizedInner
      · split at run <;> simp_all

def acceptedAlphaAt (alphas : Array RawQM31 4#usize) (slot : Fin 4) :
    RawQM31 :=
  alphas.val[slot.val]

private theorem usizeAddExactForRounds (x y z : Std.Usize)
    (hbound : x.val + y.val ≤ Std.Usize.max)
    (hval : z.val = x.val + y.val) :
    x + y = ok z := by
  have specification := Std.Usize.add_spec (x := x) (y := y) hbound
  obtain ⟨value, valueEquation, valueVal⟩ := WP.spec_imp_exists specification
  have valueExact : value = z := by
    apply UScalar.eq_of_val_eq
    omega
  rw [valueEquation, valueExact]

theorem alpha_iterator_next_round0 (alphas : Array RawQM31 4#usize) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize)
        (alphaIteratorAt alphas 0 0#usize) =
      .ok (some (0#usize, acceptedAlphaAt alphas 0),
        alphaIteratorAt alphas 1 1#usize) := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  have countExact : 0#usize + 1#usize = ok 1#usize := by
    apply usizeAddExactForRounds <;> scalar_tac
  simpa [acceptedAlphaAt] using alpha_iterator_next_some_exact
    alphas 0 0#usize 1#usize (acceptedAlphaAt alphas 0) (by omega) rfl
    countExact

theorem alpha_iterator_next_round1 (alphas : Array RawQM31 4#usize) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize)
        (alphaIteratorAt alphas 1 1#usize) =
      .ok (some (1#usize, acceptedAlphaAt alphas 1),
        alphaIteratorAt alphas 2 2#usize) := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  have countExact : 1#usize + 1#usize = ok 2#usize := by
    apply usizeAddExactForRounds <;> scalar_tac
  simpa [acceptedAlphaAt] using alpha_iterator_next_some_exact
    alphas 1 1#usize 2#usize (acceptedAlphaAt alphas 1) (by omega) rfl
    countExact

theorem alpha_iterator_next_round2 (alphas : Array RawQM31 4#usize) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize)
        (alphaIteratorAt alphas 2 2#usize) =
      .ok (some (2#usize, acceptedAlphaAt alphas 2),
        alphaIteratorAt alphas 3 3#usize) := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  have countExact : 2#usize + 1#usize = ok 3#usize := by
    apply usizeAddExactForRounds <;> scalar_tac
  simpa [acceptedAlphaAt] using alpha_iterator_next_some_exact
    alphas 2 2#usize 3#usize (acceptedAlphaAt alphas 2) (by omega) rfl
    countExact

theorem alpha_iterator_next_round3 (alphas : Array RawQM31 4#usize) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (V5RelationFullGenerated.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          RawQM31 4#usize)
        (alphaIteratorAt alphas 3 3#usize) =
      .ok (some (3#usize, acceptedAlphaAt alphas 3),
        alphaIteratorAt alphas 4 4#usize) := by
  have alphaLength : alphas.val.length = 4 := by
    simpa using alphas.property
  have countExact : 3#usize + 1#usize = ok 4#usize := by
    apply usizeAddExactForRounds <;> scalar_tac
  simpa [acceptedAlphaAt] using alpha_iterator_next_some_exact
    alphas 3 3#usize 4#usize (acceptedAlphaAt alphas 3) (by omega) rfl
    countExact

abbrev ProductionCompact :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights

def productionAdditiveInst :
    V5RelationFullGenerated.relation_stress.V5RelationStressAdditive
      ProductionCompact :=
  V5RelationCallerGenerated.v5_cu_probe.CompactBTerminalWeights.Insts.V5_relation_production_harnessV5_relation_stressV5RelationStressAdditive

/-- All four active rounds recovered from the same accepted relation caller. -/
structure AcceptedFourRoundExecution
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    Type where
  round0 : AcceptedTwoSampleRoundExecution productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.calls.compact
    trace.additive1 0#usize
    (acceptedAlphaAt alphas 0) trace.calls.relation.weights trace.weights1
    trace.calls.relation.relation_value trace.claim1
  round1 : AcceptedTwoSampleRoundExecution productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.additive1 trace.additive2
    1#usize
    (acceptedAlphaAt alphas 1) trace.weights1 trace.weights2 trace.claim1
    trace.claim2
  round2 : AcceptedTwoSampleRoundExecution productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.additive2 trace.additive3
    2#usize
    (acceptedAlphaAt alphas 2) trace.weights2 trace.weights3 trace.claim2
    trace.claim3
  round3 : AcceptedTwoSampleRoundExecution productionAdditiveInst
    parsed.v5_relation_stress trace.circlePoints trace.additive3 trace.additive4
    3#usize
    (acceptedAlphaAt alphas 3) trace.weights3 trace.weights4 trace.claim3
    trace.claim4

theorem accepted_full_trace_exposes_four_round_executions
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    Nonempty (AcceptedFourRoundExecution trace) := by
  obtain ⟨round0⟩ := accepted_outer_round_body_exposes_execution
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    (alphaIteratorAt alphas 0 0#usize)
    (alphaIteratorAt alphas 1 1#usize) 0#usize
    (acceptedAlphaAt alphas 0) trace.calls.relation.weights trace.weights1
    trace.calls.relation.relation_value trace.claim1 trace.calls.compact
    trace.additive1 (alpha_iterator_next_round0 alphas) trace.round0Success
  obtain ⟨round1⟩ := accepted_outer_round_body_exposes_execution
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    (alphaIteratorAt alphas 1 1#usize)
    (alphaIteratorAt alphas 2 2#usize) 1#usize
    (acceptedAlphaAt alphas 1) trace.weights1 trace.weights2 trace.claim1
    trace.claim2 trace.additive1 trace.additive2
    (alpha_iterator_next_round1 alphas) trace.round1Success
  obtain ⟨round2⟩ := accepted_outer_round_body_exposes_execution
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    (alphaIteratorAt alphas 2 2#usize)
    (alphaIteratorAt alphas 3 3#usize) 2#usize
    (acceptedAlphaAt alphas 2) trace.weights2 trace.weights3 trace.claim2
    trace.claim3 trace.additive2 trace.additive3
    (alpha_iterator_next_round2 alphas) trace.round2Success
  obtain ⟨round3⟩ := accepted_outer_round_body_exposes_execution
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    (alphaIteratorAt alphas 3 3#usize)
    (alphaIteratorAt alphas 4 4#usize) 3#usize
    (acceptedAlphaAt alphas 3) trace.weights3 trace.weights4 trace.claim3
    trace.claim4 trace.additive3 trace.additive4
    (alpha_iterator_next_round3 alphas) trace.round3Success
  exact ⟨{
    round0 := round0
    round1 := round1
    round2 := round2
    round3 := round3 }⟩

/-- All four exact maintained round records, chained by the actual outgoing
claim of each accepted translated round. -/
structure AcceptedFourRawRoundProjections
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim) :
    Type where
  round0 : AcceptedRawRoundProjection trace.calls.relation.relation_value
    (acceptedAlphaAt alphas 0) trace.claim1
  round1 : AcceptedRawRoundProjection trace.claim1
    (acceptedAlphaAt alphas 1) trace.claim2
  round2 : AcceptedRawRoundProjection trace.claim2
    (acceptedAlphaAt alphas 2) trace.claim3
  round3 : AcceptedRawRoundProjection trace.claim3
    (acceptedAlphaAt alphas 3) trace.claim4

/-- The accepted caller's four rounds project in order with no independently
chosen round trace.  Canonicality is needed only for the prepared initial
claim and the four decoded alphas; each next claim is then proved canonical
from the preceding accepted evaluator call. -/
theorem accepted_full_trace_exposes_four_raw_round_projections
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (initialCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        trace.calls.relation.relation_value)
    (alphaCanonical : ∀ slot : Fin 4,
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        (acceptedAlphaAt alphas slot)) :
    Nonempty (AcceptedFourRawRoundProjections trace) := by
  obtain ⟨rounds⟩ := accepted_full_trace_exposes_four_round_executions trace
  obtain ⟨round0⟩ := accepted_round_exposes_raw_arithmetic
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.calls.compact trace.additive1 0#usize (acceptedAlphaAt alphas 0)
    trace.calls.relation.weights trace.weights1
    trace.calls.relation.relation_value trace.claim1 initialCanonical
    (alphaCanonical 0) rounds.round0
  have claim1Canonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 trace.claim1 := by
    rw [← round0.outgoingExact]
    exact
      AspisV5AcceptedRelationRoundProjection.accepted_raw_round_outgoing_canonical
        round0.raw
  obtain ⟨round1⟩ := accepted_round_exposes_raw_arithmetic
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.additive1 trace.additive2 1#usize (acceptedAlphaAt alphas 1) trace.weights1
    trace.weights2 trace.claim1 trace.claim2 claim1Canonical
    (alphaCanonical 1) rounds.round1
  have claim2Canonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 trace.claim2 := by
    rw [← round1.outgoingExact]
    exact
      AspisV5AcceptedRelationRoundProjection.accepted_raw_round_outgoing_canonical
        round1.raw
  obtain ⟨round2⟩ := accepted_round_exposes_raw_arithmetic
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.additive2 trace.additive3 2#usize (acceptedAlphaAt alphas 2) trace.weights2
    trace.weights3 trace.claim2 trace.claim3 claim2Canonical
    (alphaCanonical 2) rounds.round2
  have claim3Canonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 trace.claim3 := by
    rw [← round2.outgoingExact]
    exact
      AspisV5AcceptedRelationRoundProjection.accepted_raw_round_outgoing_canonical
        round2.raw
  obtain ⟨round3⟩ := accepted_round_exposes_raw_arithmetic
    productionAdditiveInst parsed.v5_relation_stress trace.circlePoints
    trace.additive3 trace.additive4 3#usize (acceptedAlphaAt alphas 3) trace.weights3
    trace.weights4 trace.claim3 trace.claim4 claim3Canonical
    (alphaCanonical 3) rounds.round3
  exact ⟨{
    round0 := round0
    round1 := round1
    round2 := round2
    round3 := round3 }⟩

/-- The four projected records are four successful maintained source-model
rounds, with their exact accepted claims. -/
theorem accepted_four_raw_round_projections_run_source
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (rounds : AcceptedFourRawRoundProjections trace) :
    AspisV5RelationStressSourceBridge.runSourceRelationRound
        (AspisV5AcceptedRelationRoundProjection.toField
          trace.calls.relation.relation_value)
        (AspisV5AcceptedRelationRoundProjection.projectedRound
          rounds.round0.raw) =
          some (AspisV5AcceptedRelationRoundProjection.toField trace.claim1) ∧
      AspisV5RelationStressSourceBridge.runSourceRelationRound
        (AspisV5AcceptedRelationRoundProjection.toField trace.claim1)
        (AspisV5AcceptedRelationRoundProjection.projectedRound
          rounds.round1.raw) =
          some (AspisV5AcceptedRelationRoundProjection.toField trace.claim2) ∧
      AspisV5RelationStressSourceBridge.runSourceRelationRound
        (AspisV5AcceptedRelationRoundProjection.toField trace.claim2)
        (AspisV5AcceptedRelationRoundProjection.projectedRound
          rounds.round2.raw) =
          some (AspisV5AcceptedRelationRoundProjection.toField trace.claim3) ∧
      AspisV5RelationStressSourceBridge.runSourceRelationRound
        (AspisV5AcceptedRelationRoundProjection.toField trace.claim3)
        (AspisV5AcceptedRelationRoundProjection.projectedRound
          rounds.round3.raw) =
          some (AspisV5AcceptedRelationRoundProjection.toField trace.claim4) := by
  have run0 :=
    AspisV5AcceptedRelationRoundProjection.accepted_raw_round_runs_source_round
      rounds.round0.raw
  have run1 :=
    AspisV5AcceptedRelationRoundProjection.accepted_raw_round_runs_source_round
      rounds.round1.raw
  have run2 :=
    AspisV5AcceptedRelationRoundProjection.accepted_raw_round_runs_source_round
      rounds.round2.raw
  have run3 :=
    AspisV5AcceptedRelationRoundProjection.accepted_raw_round_runs_source_round
      rounds.round3.raw
  simpa [rounds.round0.incomingExact, rounds.round0.outgoingExact,
    rounds.round1.incomingExact, rounds.round1.outgoingExact,
    rounds.round2.incomingExact, rounds.round2.outgoingExact,
    rounds.round3.incomingExact, rounds.round3.outgoingExact] using
      And.intro run0 (And.intro run1 (And.intro run2 run3))

/-- The exact maintained relation input read from one accepted translated
execution.  No round messages, claims, final values, or terminal-dot outputs
are chosen independently of that execution. -/
def acceptedSourceRelationInput
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (rounds : AcceptedFourRawRoundProjections trace) :
    AspisV5RelationStressSourceBridge.SourceRelationInput
      AspisV5AcceptedRelationRoundProjection.ExactQM31 where
  initialClaim :=
    AspisV5AcceptedRelationRoundProjection.toField
      trace.calls.relation.relation_value
  round0 :=
    AspisV5AcceptedRelationRoundProjection.projectedRound rounds.round0.raw
  round1 :=
    AspisV5AcceptedRelationRoundProjection.projectedRound rounds.round1.raw
  round2 :=
    AspisV5AcceptedRelationRoundProjection.projectedRound rounds.round2.raw
  round3 :=
    AspisV5AcceptedRelationRoundProjection.projectedRound rounds.round3.raw
  finalCoefficients := fun index =>
    AspisV5AcceptedRelationRoundProjection.toField
      trace.finalCoefficients.val[index.val]!
  mainFinalDot :=
    AspisV5AcceptedRelationRoundProjection.toField trace.mainDot
  additiveFinalDot :=
    AspisV5AcceptedRelationRoundProjection.toField trace.additiveDot

/-- The accepted terminal addition is exact field addition as soon as its two
dot outputs are known to be canonical representatives. -/
theorem accepted_terminal_add_is_exact
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    (trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim)
    (mainCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 trace.mainDot)
    (additiveCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        trace.additiveDot) :
    AspisV5AcceptedRelationRoundProjection.toField trace.mainDot +
        AspisV5AcceptedRelationRoundProjection.toField trace.additiveDot =
      AspisV5AcceptedRelationRoundProjection.toField trace.claim4 := by
  exact
    (AspisV5RelationGeneratedFieldProjection.generated_qm31_add_run_corresponds
      trace.mainDot trace.additiveDot trace.claim4 mainCanonical
      additiveCanonical trace.terminalAddSuccess).2.symm

/-- Once the accepted terminal addition is interpreted in the exact field,
the same accepted execution runs the complete maintained relation verifier.
The only premise left here is that one scalar terminal interpretation; all
four rounds and all values in the source input are derived above. -/
theorem accepted_trace_runs_source_relation_verifier
    {parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData}
    {finalPolynomial : Array RawQM31 4#usize}
    {alphas : Array RawQM31 4#usize}
    {kappa inactiveClaim : RawQM31}
    {roundChallenges : Array RawQM31 10#usize}
    {preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims}
    {terminalClaim : RawQM31}
    {trace : AcceptedMode9FullRelationTrace parsed finalPolynomial alphas
      kappa inactiveClaim roundChallenges preparedClaims terminalClaim}
    (rounds : AcceptedFourRawRoundProjections trace)
    (terminalExact :
      AspisV5AcceptedRelationRoundProjection.toField trace.mainDot +
          AspisV5AcceptedRelationRoundProjection.toField trace.additiveDot =
        AspisV5AcceptedRelationRoundProjection.toField trace.claim4) :
    AspisV5RelationStressSourceBridge.runSourceRelationVerifier
        (acceptedSourceRelationInput rounds) =
      some {
        finalCoefficients := fun index =>
          AspisV5AcceptedRelationRoundProjection.toField
            trace.finalCoefficients.val[index.val]!
        terminalClaim :=
          AspisV5AcceptedRelationRoundProjection.toField trace.claim4 } := by
  obtain ⟨run0, run1, run2, run3⟩ :=
    accepted_four_raw_round_projections_run_source rounds
  have fourCall :
      AspisV5RelationStressSourceBridge.runSourceRelationVerifierFourCalls
          (acceptedSourceRelationInput rounds) =
        some {
          finalCoefficients := fun index =>
            AspisV5AcceptedRelationRoundProjection.toField
              trace.finalCoefficients.val[index.val]!
          terminalClaim :=
            AspisV5AcceptedRelationRoundProjection.toField trace.claim4 } := by
    simp [AspisV5RelationStressSourceBridge.runSourceRelationVerifierFourCalls,
      AspisV5RelationStressSourceBridge.runSourceRelationVerifierWithRound,
      acceptedSourceRelationInput, run0, run1, run2, run3, terminalExact]
  rw [AspisV5RelationStressSourceBridge.runSourceRelationVerifierFourCalls_eq_source]
    at fourCall
  exact fourCall

#print axioms accepted_polynomial_loop_exposes_execution
#print axioms accepted_sample_body_exposes_execution
#print axioms active_sample_body_not_done_success
#print axioms accepted_sample_exhaustion_exposes_polynomial
#print axioms exhausted_sample_body_not_cont
#print axioms accepted_two_sample_loop_exposes_execution
#print axioms accepted_outer_round_body_exposes_execution
#print axioms alpha_iterator_next_round0
#print axioms alpha_iterator_next_round1
#print axioms alpha_iterator_next_round2
#print axioms alpha_iterator_next_round3
#print axioms accepted_full_trace_exposes_four_round_executions
#print axioms accepted_full_trace_exposes_four_raw_round_projections
#print axioms accepted_four_raw_round_projections_run_source
#print axioms accepted_terminal_add_is_exact
#print axioms accepted_trace_runs_source_relation_verifier

end AspisV5AcceptedRelationRoundInversion
