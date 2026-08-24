import V5RelationPrepareLogLenProof
import V5RelationGeneratedFieldProjection
import V5RelationPrepareFieldProjection

/-!
# Canonical initial relation value from the translated preparation driver

The relation verifier starts from the inactive claim plus four prepared PCS
claims scaled by successive powers of kappa.  This file proves that the
translated preparation driver returns that initial value in canonical field
representation whenever its inactive claim and four prepared claims are
canonical.
-/

namespace AspisV5RelationPrepareCanonicalProof

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev PrepareQM31 := V5RelationPrepareGenerated.aspis_core.field.QM31
abbrev CallerQM31 := V5RelationCallerGenerated.aspis_core.field.QM31

def PrepareCanonicalQM31 (value : PrepareQM31) : Prop :=
  AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c0.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c0.b.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c1.a.val ∧
    AspisAeneasCM31Multiplicative.CanonicalRawM31 value.c1.b.val

theorem prepareCanonical_iff_fieldProjection
    (value : PrepareQM31) :
    PrepareCanonicalQM31 value ↔
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 value := by
  simp [PrepareCanonicalQM31,
    AspisV5RelationPrepareFieldProjection.CanonicalQM31,
    AspisV5RelationPrepareFieldProjection.CanonicalCM31]

def PrepareClaimsCanonical
    (claims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    Prop :=
  claims.inner.claims.val.length = 4 ∧
    ∀ (index : Nat) (bound : index < claims.inner.claims.val.length),
      PrepareCanonicalQM31 claims.inner.claims.val[index]

def prepareToCallerQM31 (value : PrepareQM31) : CallerQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerToPrepareQM31 (value : CallerQM31) : PrepareQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def callerToPrepareVec (values : alloc.vec.Vec CallerQM31) :
    alloc.vec.Vec PrepareQM31 :=
  ⟨values.val.map callerToPrepareQM31, by simpa using values.property⟩

def callerToPrepareMultiplier
    (value : V5RelationCallerGenerated.aspis_core.field.PreparedQm31Multiplier) :
    V5RelationPrepareGenerated.aspis_core.field.PreparedQm31Multiplier :=
  { components := value.components }

def callerToPrepareClaims
    (claims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims :=
  { inner :=
      { claims := callerToPrepareVec claims.inner.claims
        powers := callerToPrepareVec claims.inner.powers }
    c1_weight_limbs := claims.c1_weight_limbs
    c2_multipliers :=
      ⟨claims.c2_multipliers.val.map callerToPrepareMultiplier,
        by simpa using claims.c2_multipliers.property⟩ }

def CallerClaimsCanonical
    (claims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    Prop :=
  claims.inner.claims.val.length = 4 ∧
    ∀ (index : Nat) (bound : index < claims.inner.claims.val.length),
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        claims.inner.claims.val[index]

@[simp] theorem prepareToCaller_canonical_iff (value : PrepareQM31) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
        (prepareToCallerQM31 value) ↔
      PrepareCanonicalQM31 value := by
  simp [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    PrepareCanonicalQM31, prepareToCallerQM31]

@[simp] theorem callerToPrepare_canonical_iff (value : CallerQM31) :
    PrepareCanonicalQM31 (callerToPrepareQM31 value) ↔
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 value := by
  simp [AspisV5RelationGeneratedFieldProjection.CanonicalQM31,
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    PrepareCanonicalQM31, callerToPrepareQM31]

theorem callerClaims_to_prepare_canonical
    (claims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (canonical : CallerClaimsCanonical claims) :
    PrepareClaimsCanonical (callerToPrepareClaims claims) := by
  constructor
  · simpa [callerToPrepareClaims, callerToPrepareVec] using canonical.1
  · intro index bound
    have sourceBound : index < claims.inner.claims.val.length := by
      simpa [callerToPrepareClaims, callerToPrepareVec] using bound
    have entryCanonical := canonical.2 index sourceBound
    simpa [callerToPrepareClaims, callerToPrepareVec,
      callerToPrepare_canonical_iff, sourceBound] using entryCanonical

abbrev PrepareCM31 := V5RelationPrepareGenerated.aspis_core.field.CM31
abbrev CallerCM31 := V5RelationFullGenerated.aspis_core.field.CM31
abbrev RawM31 := Std.U32

def prepareToCallerCM31 (value : PrepareCM31) : CallerCM31 :=
  { a := value.a, b := value.b }

@[simp] theorem prepareToCallerQM31_c0 (value : PrepareQM31) :
    (prepareToCallerQM31 value).c0 = prepareToCallerCM31 value.c0 := by
  rfl

@[simp] theorem prepareToCallerQM31_c1 (value : PrepareQM31) :
    (prepareToCallerQM31 value).c1 = prepareToCallerCM31 value.c1 := by
  rfl

private theorem full_P_eq_prepare :
    V5RelationFullGenerated.aspis_core.field.P =
      V5RelationPrepareGenerated.aspis_core.field.P := by
  apply UScalar.eq_of_val_eq
  unfold V5RelationFullGenerated.aspis_core.field.P
    V5RelationPrepareGenerated.aspis_core.field.P
  rfl

private theorem full_reduce_u64_eq_prepare (value : Std.U64) :
    V5RelationFullGenerated.aspis_core.field.reduce_u64 value =
      V5RelationPrepareGenerated.aspis_core.field.reduce_u64 value := by
  unfold V5RelationFullGenerated.aspis_core.field.reduce_u64
    V5RelationPrepareGenerated.aspis_core.field.reduce_u64
  rw [full_P_eq_prepare]

private theorem full_m31_add_eq_prepare (left right : RawM31) :
    V5RelationFullGenerated.aspis_core.field.M31.add left right =
      V5RelationPrepareGenerated.aspis_core.field.M31.add left right := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.add
    V5RelationPrepareGenerated.aspis_core.field.M31.add
  rw [full_P_eq_prepare]

private theorem full_m31_sub_eq_prepare (left right : RawM31) :
    V5RelationFullGenerated.aspis_core.field.M31.sub left right =
      V5RelationPrepareGenerated.aspis_core.field.M31.sub left right := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.sub
    V5RelationPrepareGenerated.aspis_core.field.M31.sub
  rw [full_P_eq_prepare]

private theorem full_m31_mul_eq_prepare (left right : RawM31) :
    V5RelationFullGenerated.aspis_core.field.M31.mul left right =
      V5RelationPrepareGenerated.aspis_core.field.M31.mul left right := by
  unfold V5RelationFullGenerated.aspis_core.field.M31.mul
    V5RelationPrepareGenerated.aspis_core.field.M31.mul
  simp only [Aeneas.Std.lift, bind_tc_ok]
  rw [full_reduce_u64_eq_prepare]

private theorem full_cm31_add_transport (left right : PrepareCM31) :
    V5RelationFullGenerated.aspis_core.field.CM31.add
        (prepareToCallerCM31 left) (prepareToCallerCM31 right) =
      (do
        let output ← V5RelationPrepareGenerated.aspis_core.field.CM31.add
          left right
        ok (prepareToCallerCM31 output)) := by
  simp [V5RelationFullGenerated.aspis_core.field.CM31.add,
    V5RelationPrepareGenerated.aspis_core.field.CM31.add,
    full_m31_add_eq_prepare, prepareToCallerCM31]

private theorem full_cm31_sub_transport (left right : PrepareCM31) :
    V5RelationFullGenerated.aspis_core.field.CM31.sub
        (prepareToCallerCM31 left) (prepareToCallerCM31 right) =
      (do
        let output ← V5RelationPrepareGenerated.aspis_core.field.CM31.sub
          left right
        ok (prepareToCallerCM31 output)) := by
  simp [V5RelationFullGenerated.aspis_core.field.CM31.sub,
    V5RelationPrepareGenerated.aspis_core.field.CM31.sub,
    full_m31_sub_eq_prepare, prepareToCallerCM31]

private theorem full_cm31_mul_transport (left right : PrepareCM31) :
    V5RelationFullGenerated.aspis_core.field.CM31.mul
        (prepareToCallerCM31 left) (prepareToCallerCM31 right) =
      (do
        let output ← V5RelationPrepareGenerated.aspis_core.field.CM31.mul
          left right
        ok (prepareToCallerCM31 output)) := by
  simp [V5RelationFullGenerated.aspis_core.field.CM31.mul,
    V5RelationPrepareGenerated.aspis_core.field.CM31.mul,
    full_m31_add_eq_prepare, full_m31_sub_eq_prepare,
    full_m31_mul_eq_prepare, prepareToCallerCM31]

private theorem full_cm31_square_transport (input : PrepareCM31) :
    V5RelationFullGenerated.aspis_core.field.CM31.square
        (prepareToCallerCM31 input) =
      (do
        let output ← V5RelationPrepareGenerated.aspis_core.field.CM31.square input
        ok (prepareToCallerCM31 output)) := by
  simp [V5RelationFullGenerated.aspis_core.field.CM31.square,
    V5RelationPrepareGenerated.aspis_core.field.CM31.square,
    V5RelationFullGenerated.aspis_core.field.M31.double,
    V5RelationPrepareGenerated.aspis_core.field.M31.double,
    full_m31_add_eq_prepare, full_m31_sub_eq_prepare,
    full_m31_mul_eq_prepare, prepareToCallerCM31]

private theorem full_cm31_double_transport (input : PrepareCM31) :
    V5RelationFullGenerated.aspis_core.field.CM31.double
        (prepareToCallerCM31 input) =
      (do
        let output ← V5RelationPrepareGenerated.aspis_core.field.CM31.double input
        ok (prepareToCallerCM31 output)) := by
  unfold V5RelationFullGenerated.aspis_core.field.CM31.double
    V5RelationPrepareGenerated.aspis_core.field.CM31.double
  exact full_cm31_add_transport input input

private theorem full_mul_by_r_transport (input : PrepareCM31) :
    V5RelationFullGenerated.aspis_core.field.mul_by_r
        (prepareToCallerCM31 input) =
      (do
        let output ← V5RelationPrepareGenerated.aspis_core.field.mul_by_r input
        ok (prepareToCallerCM31 output)) := by
  simp [V5RelationFullGenerated.aspis_core.field.mul_by_r,
    V5RelationPrepareGenerated.aspis_core.field.mul_by_r,
    V5RelationFullGenerated.aspis_core.field.M31.double,
    V5RelationPrepareGenerated.aspis_core.field.M31.double,
    full_m31_add_eq_prepare, full_m31_sub_eq_prepare,
    prepareToCallerCM31]

theorem prepare_qm31_mul_success_canonical
    (left right output : PrepareQM31)
    (leftCanonical : PrepareCanonicalQM31 left)
    (rightCanonical : PrepareCanonicalQM31 right)
    (success :
      V5RelationPrepareGenerated.aspis_core.field.QM31.mul left right =
        .ok output) :
    PrepareCanonicalQM31 output := by
  apply (prepareCanonical_iff_fieldProjection output).2
  exact
    (AspisV5RelationPrepareFieldProjection.generated_qm31_mul_run_corresponds
      left right output
      ((prepareCanonical_iff_fieldProjection left).1 leftCanonical)
      ((prepareCanonical_iff_fieldProjection right).1 rightCanonical)
      success).1

theorem prepare_qm31_square_success_canonical
    (input output : PrepareQM31)
    (inputCanonical : PrepareCanonicalQM31 input)
    (success :
      V5RelationPrepareGenerated.aspis_core.field.QM31.square input =
        .ok output) :
    PrepareCanonicalQM31 output := by
  apply (prepareCanonical_iff_fieldProjection output).2
  exact
    (AspisV5RelationPrepareFieldProjection.generated_qm31_square_run_corresponds
      input output
      ((prepareCanonical_iff_fieldProjection input).1 inputCanonical)
      success).1

theorem prepare_qm31_add_success_canonical
    (left right output : PrepareQM31)
    (leftCanonical : PrepareCanonicalQM31 left)
    (rightCanonical : PrepareCanonicalQM31 right)
    (success :
      V5RelationPrepareGenerated.aspis_core.field.QM31.add left right =
        .ok output) :
    PrepareCanonicalQM31 output := by
  apply (prepareCanonical_iff_fieldProjection output).2
  exact
    (AspisV5RelationPrepareFieldProjection.generated_qm31_add_run_corresponds
      left right output
      ((prepareCanonical_iff_fieldProjection left).1 leftCanonical)
      ((prepareCanonical_iff_fieldProjection right).1 rightCanonical)
      success).1

private theorem prepare_vec_index_run
    (values : alloc.vec.Vec PrepareQM31) (index : Std.Usize)
    (bound : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice PrepareQM31) values index =
      .ok values.val[index.val] := by
  rw [alloc.vec.Vec.index_slice_index]
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index bound)
  simpa [valueEq] using run

theorem point_claim_at_success_canonical
    (claims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (index : Std.Usize) (output : PrepareQM31)
    (indexBound : index.val < 4)
    (claimsCanonical : PrepareClaimsCanonical claims)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
          claims index = .ok output) :
    PrepareCanonicalQM31 output := by
  have vectorBound : index.val < claims.inner.claims.val.length := by
    rw [claimsCanonical.1]
    exact indexBound
  have indexRun := prepare_vec_index_run claims.inner.claims index vectorBound
  unfold
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
    at success
  rw [indexRun] at success
  have outputEquality : claims.inner.claims.val[index.val] = output :=
    Result.ok.inj success
  subst output
  exact claimsCanonical.2 index.val vectorBound

/-- Successful translated relation preparation preserves canonical field
representation through the exact kappa-power and four-claim arithmetic trace. -/
theorem prepare_success_relation_value_canonical
    (parsed : V5RelationPrepareGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : PrepareQM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (point : Array PrepareQM31 10#usize)
    (denseScale : PrepareQM31)
    (kappaCanonical : PrepareCanonicalQM31 kappa)
    (inactiveCanonical : PrepareCanonicalQM31 inactiveClaim)
    (claimsCanonical : PrepareClaimsCanonical preparedClaims)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
          parsed kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    PrepareCanonicalQM31 relation.relation_value := by
  obtain ⟨_, ⟨trace, _⟩⟩ :=
    AspisV5RelationPrepareLogLenProof.Prepare.prepare_for_extraction_success_exposes_arithmetic
      parsed kappa inactiveClaim preparedClaims relation point denseScale success
  have kappa2Canonical := prepare_qm31_square_success_canonical
    kappa trace.kappa2 kappaCanonical trace.kappa2Run
  have kappa3Canonical := prepare_qm31_mul_success_canonical
    trace.kappa2 kappa trace.kappa3 kappa2Canonical kappaCanonical
    trace.kappa3Run
  have claim0Canonical := point_claim_at_success_canonical preparedClaims
    0#usize trace.claim0 (by norm_num) claimsCanonical trace.claim0Run
  have relationValue0Canonical := prepare_qm31_add_success_canonical
    inactiveClaim trace.claim0 trace.relationValue0 inactiveCanonical
    claim0Canonical trace.relationValue0Run
  have claim1Canonical := point_claim_at_success_canonical preparedClaims
    1#usize trace.claim1 (by norm_num) claimsCanonical trace.claim1Run
  have scaled1Canonical := prepare_qm31_mul_success_canonical
    kappa trace.claim1 trace.scaled1 kappaCanonical claim1Canonical
    trace.scaled1Run
  have relationValue1Canonical := prepare_qm31_add_success_canonical
    trace.relationValue0 trace.scaled1 trace.relationValue1
    relationValue0Canonical scaled1Canonical trace.relationValue1Run
  have claim2Canonical := point_claim_at_success_canonical preparedClaims
    2#usize trace.claim2 (by norm_num) claimsCanonical trace.claim2Run
  have scaled2Canonical := prepare_qm31_mul_success_canonical
    trace.kappa2 trace.claim2 trace.scaled2 kappa2Canonical claim2Canonical
    trace.scaled2Run
  have relationValue2Canonical := prepare_qm31_add_success_canonical
    trace.relationValue1 trace.scaled2 trace.relationValue2
    relationValue1Canonical scaled2Canonical trace.relationValue2Run
  have claim3Canonical := point_claim_at_success_canonical preparedClaims
    3#usize trace.claim3 (by norm_num) claimsCanonical trace.claim3Run
  have scaled3Canonical := prepare_qm31_mul_success_canonical
    trace.kappa3 trace.claim3 trace.scaled3 kappa3Canonical claim3Canonical
    trace.scaled3Run
  have relationValue3Canonical := prepare_qm31_add_success_canonical
    trace.relationValue2 trace.scaled3 trace.relationValue3
    relationValue2Canonical scaled3Canonical trace.relationValue3Run
  rw [trace.returnedRelationValue]
  exact relationValue3Canonical

/-- The third value returned by successful relation preparation is exactly
the generated `kappa² * kappa` result, hence is canonical whenever the
accepted kappa input is canonical. -/
theorem prepare_success_dense_scale_canonical
    (parsed : V5RelationPrepareGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : PrepareQM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (point : Array PrepareQM31 10#usize)
    (denseScale : PrepareQM31)
    (kappaCanonical : PrepareCanonicalQM31 kappa)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
          parsed kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    PrepareCanonicalQM31 denseScale := by
  obtain ⟨_, ⟨trace, returnedDenseScale⟩⟩ :=
    AspisV5RelationPrepareLogLenProof.Prepare.prepare_for_extraction_success_exposes_arithmetic
      parsed kappa inactiveClaim preparedClaims relation point denseScale success
  have kappa2Canonical := prepare_qm31_square_success_canonical
    kappa trace.kappa2 kappaCanonical trace.kappa2Run
  have kappa3Canonical := prepare_qm31_mul_success_canonical
    trace.kappa2 kappa trace.kappa3 kappa2Canonical kappaCanonical
    trace.kappa3Run
  rw [returnedDenseScale]
  exact kappa3Canonical

/-- The public relation-preparation wrapper preserves the same canonical
initial relation value proved for its translated extraction helper. -/
theorem caller_prepare_success_relation_value_canonical
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : CallerQM31)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationCallerGenerated.v5_cu_probe.PreparedRelation)
    (point : Array CallerQM31 10#usize)
    (denseScale : CallerQM31)
    (kappaCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 kappa)
    (inactiveCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 inactiveClaim)
    (claimsCanonical : CallerClaimsCanonical preparedClaims)
    (success :
      V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
          parsed
          V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
          kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
      relation.relation_value := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
    at success
  generalize sourceRunEquation :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
        _ _ _ _ = sourceResult at success
  cases sourceResult with
  | fail error => simp [sourceRunEquation] at success
  | div => simp [sourceRunEquation] at success
  | ok sourceResult =>
    simp only [sourceRunEquation, bind_tc_ok] at success
    cases sourceResult with
    | Err error => simp at success
    | Ok sourceTriple =>
      rcases sourceTriple with ⟨sourceRelation, sourcePoint, sourceScale⟩
      have sourceKappaCanonical :
          PrepareCanonicalQM31 (callerToPrepareQM31 kappa) :=
        (callerToPrepare_canonical_iff kappa).2 kappaCanonical
      have sourceInactiveCanonical :
          PrepareCanonicalQM31 (callerToPrepareQM31 inactiveClaim) :=
        (callerToPrepare_canonical_iff inactiveClaim).2 inactiveCanonical
      have sourceClaimsCanonical :
          PrepareClaimsCanonical (callerToPrepareClaims preparedClaims) :=
        callerClaims_to_prepare_canonical preparedClaims claimsCanonical
      change
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
            _ (callerToPrepareQM31 kappa)
            (callerToPrepareQM31 inactiveClaim)
            (callerToPrepareClaims preparedClaims) =
          .ok (.Ok (sourceRelation, sourcePoint, sourceScale))
        at sourceRunEquation
      have sourceRelationCanonical :=
        prepare_success_relation_value_canonical _
          (callerToPrepareQM31 kappa) (callerToPrepareQM31 inactiveClaim)
          (callerToPrepareClaims preparedClaims) sourceRelation sourcePoint
          sourceScale sourceKappaCanonical sourceInactiveCanonical
          sourceClaimsCanonical sourceRunEquation
      simp only at success
      have tripleEquality := core.result.Result.Ok.inj (Result.ok.inj success)
      have relationValueEquality := congrArg
        (fun triple => triple.1.relation_value) tripleEquality
      change prepareToCallerQM31 sourceRelation.relation_value =
        relation.relation_value at relationValueEquality
      rw [← relationValueEquality]
      exact (prepareToCaller_canonical_iff sourceRelation.relation_value).2
        sourceRelationCanonical

/-- The public caller wrapper returns the same canonical dense scale as its
translated extraction helper. -/
theorem caller_prepare_success_dense_scale_canonical
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : CallerQM31)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationCallerGenerated.v5_cu_probe.PreparedRelation)
    (point : Array CallerQM31 10#usize)
    (denseScale : CallerQM31)
    (kappaCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 kappa)
    (success :
      V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
          parsed
          V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
          kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31 denseScale := by
  unfold
    V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
    at success
  generalize sourceRunEquation :
      V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
        _ _ _ _ = sourceResult at success
  cases sourceResult with
  | fail error => simp [sourceRunEquation] at success
  | div => simp [sourceRunEquation] at success
  | ok sourceResult =>
    simp only [sourceRunEquation, bind_tc_ok] at success
    cases sourceResult with
    | Err error => simp at success
    | Ok sourceTriple =>
      rcases sourceTriple with ⟨sourceRelation, sourcePoint, sourceScale⟩
      have sourceKappaCanonical :
          PrepareCanonicalQM31 (callerToPrepareQM31 kappa) :=
        (callerToPrepare_canonical_iff kappa).2 kappaCanonical
      change
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
            _ (callerToPrepareQM31 kappa)
            (callerToPrepareQM31 inactiveClaim)
            (callerToPrepareClaims preparedClaims) =
          .ok (.Ok (sourceRelation, sourcePoint, sourceScale))
        at sourceRunEquation
      have sourceScaleCanonical :=
        prepare_success_dense_scale_canonical _
          (callerToPrepareQM31 kappa) (callerToPrepareQM31 inactiveClaim)
          (callerToPrepareClaims preparedClaims) sourceRelation sourcePoint
          sourceScale sourceKappaCanonical sourceRunEquation
      simp only at success
      have tripleEquality := core.result.Result.Ok.inj (Result.ok.inj success)
      have scaleEquality := congrArg (fun triple => triple.2.2) tripleEquality
      change prepareToCallerQM31 sourceScale = denseScale at scaleEquality
      rw [← scaleEquality]
      exact (prepareToCaller_canonical_iff sourceScale).2 sourceScaleCanonical

#print axioms prepare_qm31_mul_success_canonical
#print axioms prepare_qm31_square_success_canonical
#print axioms prepare_qm31_add_success_canonical
#print axioms prepare_success_relation_value_canonical
#print axioms prepare_success_dense_scale_canonical
#print axioms caller_prepare_success_relation_value_canonical
#print axioms caller_prepare_success_dense_scale_canonical

end AspisV5RelationPrepareCanonicalProof
