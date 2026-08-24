import V5AcceptedSameRunRelationFriSnapshot
import V5AcceptedPreparedClaimsCanonical
import V5AcceptedPrefixCanonical
import V5RelationPrepareCanonicalProof

/-!
# Exact accepted point-claim table

This file connects the 1,216 relation-claim bytes used by one accepted
production execution to the four prepared point claims consumed by the
relation verifier.  The table below is computed by the accepted production
QM31 decoder.  Failed fields are totalized to zero only to make the definition
total; a successful `prepare_v5_pcs_claims` run proves that none of the 76
accepted fields takes that branch.
-/

namespace AspisV5AcceptedClaimTableExact

open Aeneas Aeneas.Std Result
open AspisV5AcceptedEntrySourceBridge
open AspisV5AcceptedFriModelInputBinding
open AspisV5AcceptedPreparedClaimsCanonical
open AspisV5AcceptedSameRunRelationFriSnapshot
open AspisV5ComponentCPreProjectionDeployed
open AspisV5PreparedPointClaimsSourceBridge
open AspisV5PreparedPointClaimsSourceProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

abbrev K := AspisV5FriAcceptedForestChecks.K
abbrev AcceptedQM31 := AspisV5AcceptedEntrySourceBridge.EntryQM31
abbrev PreparedKernelQM31 :=
  AspisV5PreparedPointClaimsSourceProof.KernelQM31
abbrev PrepareQM31 :=
  V5RelationPrepareGenerated.aspis_core.field.QM31
abbrev CallerQM31 :=
  V5RelationCallerGenerated.aspis_core.field.QM31

private theorem kernelExact_mul_eq_maintained
    (left right : AspisV5PreparedPointClaimsSourceProof.KernelQM31Exact) :
    (left * right : AspisV5PreparedPointClaimsSourceProof.KernelQM31Exact) =
      ((show K from left) * (show K from right) : K) := by
  rfl

private theorem kernelExact_pow_eq_maintained
    (value : AspisV5PreparedPointClaimsSourceProof.KernelQM31Exact)
    (exponent : Nat) :
    (value ^ exponent :
        AspisV5PreparedPointClaimsSourceProof.KernelQM31Exact) =
      ((show K from value) ^ exponent : K) := by
  rfl

private theorem prepareExact_add_eq_maintained
    (left right : PrepareQM31) :
    AspisV5RelationPrepareFieldProjection.toExact left +
        AspisV5RelationPrepareFieldProjection.toExact right =
      AspisV5RelationPrepareFieldProjection.toMaintainedExact left +
        AspisV5RelationPrepareFieldProjection.toMaintainedExact right := by
  rfl

private theorem prepareExact_mul_eq_maintained
    (left right : PrepareQM31) :
    AspisV5RelationPrepareFieldProjection.toExact left *
        AspisV5RelationPrepareFieldProjection.toExact right =
      AspisV5RelationPrepareFieldProjection.toMaintainedExact left *
        AspisV5RelationPrepareFieldProjection.toMaintainedExact right := by
  rfl

private theorem prepareExact_pow_eq_maintained
    (value : PrepareQM31) (exponent : Nat) :
    AspisV5RelationPrepareFieldProjection.toExact value ^ exponent =
      AspisV5RelationPrepareFieldProjection.toMaintainedExact value ^
        exponent := by
  rfl

private theorem prepare_add_run_exact
    (left right output : PrepareQM31)
    (leftCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 left)
    (rightCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 right)
    (run : V5RelationPrepareGenerated.aspis_core.field.QM31.add left right =
      .ok output) :
    AspisV5RelationPrepareFieldProjection.CanonicalQM31 output ∧
      AspisV5RelationPrepareFieldProjection.toMaintainedExact output =
        AspisV5RelationPrepareFieldProjection.toMaintainedExact left +
          AspisV5RelationPrepareFieldProjection.toMaintainedExact right := by
  have result :=
    AspisV5RelationPrepareFieldProjection.generated_qm31_add_run_corresponds
      left right output leftCanonical rightCanonical run
  refine ⟨result.1, ?_⟩
  rw [show AspisV5RelationPrepareFieldProjection.toMaintainedExact output =
      AspisV5RelationPrepareFieldProjection.toExact output by rfl]
  exact result.2.trans (prepareExact_add_eq_maintained left right)

private theorem prepare_mul_run_exact
    (left right output : PrepareQM31)
    (leftCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 left)
    (rightCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 right)
    (run : V5RelationPrepareGenerated.aspis_core.field.QM31.mul left right =
      .ok output) :
    AspisV5RelationPrepareFieldProjection.CanonicalQM31 output ∧
      AspisV5RelationPrepareFieldProjection.toMaintainedExact output =
        AspisV5RelationPrepareFieldProjection.toMaintainedExact left *
          AspisV5RelationPrepareFieldProjection.toMaintainedExact right := by
  have result :=
    AspisV5RelationPrepareFieldProjection.generated_qm31_mul_run_corresponds
      left right output leftCanonical rightCanonical run
  refine ⟨result.1, ?_⟩
  rw [show AspisV5RelationPrepareFieldProjection.toMaintainedExact output =
      AspisV5RelationPrepareFieldProjection.toExact output by rfl]
  exact result.2.trans (prepareExact_mul_eq_maintained left right)

private theorem prepare_square_run_exact
    (value output : PrepareQM31)
    (valueCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 value)
    (run : V5RelationPrepareGenerated.aspis_core.field.QM31.square value =
      .ok output) :
    AspisV5RelationPrepareFieldProjection.CanonicalQM31 output ∧
      AspisV5RelationPrepareFieldProjection.toMaintainedExact output =
        AspisV5RelationPrepareFieldProjection.toMaintainedExact value ^ 2 := by
  have result :=
    AspisV5RelationPrepareFieldProjection.generated_qm31_square_run_corresponds
      value output valueCanonical run
  refine ⟨result.1, ?_⟩
  calc
    AspisV5RelationPrepareFieldProjection.toMaintainedExact output =
        AspisV5RelationPrepareFieldProjection.toExact output := by rfl
    _ = AspisV5RelationPrepareFieldProjection.toExact value ^ 2 := result.2
    _ = AspisV5RelationPrepareFieldProjection.toMaintainedExact value ^ 2 :=
      prepareExact_pow_eq_maintained value 2

@[simp] private theorem callerToPrepare_toMaintainedExact
    (value : CallerQM31) :
    AspisV5RelationPrepareFieldProjection.toMaintainedExact
        (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 value) =
      AspisV5RelationLinkedFieldProjection.toMaintainedExact value := by
  rfl

@[simp] private theorem prepareToCaller_toMaintainedExact
    (value : PrepareQM31) :
    AspisV5RelationLinkedFieldProjection.toMaintainedExact
        (AspisV5RelationPrepareCanonicalProof.prepareToCallerQM31 value) =
      AspisV5RelationPrepareFieldProjection.toMaintainedExact value := by
  rfl

private theorem prepare_point_claim_at_success_eq
    (claims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (index : Std.Usize) (output : PrepareQM31)
    (indexBound : index.val < 4)
    (claimsLength : claims.inner.claims.val.length = 4)
    (success :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
          claims index = .ok output) :
    output = claims.inner.claims.val[index.val] := by
  have vectorBound : index.val < claims.inner.claims.val.length := by
    rw [claimsLength]
    exact indexBound
  obtain ⟨value, valueRun, valueEquality⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec claims.inner.claims index vectorBound)
  unfold
    V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims.point_claim_at_for_extraction
    at success
  rw [alloc.vec.Vec.index_slice_index, valueRun] at success
  have outputEquality : value = output := Result.ok.inj success
  exact outputEquality.symm.trans valueEquality

private theorem preparedPointClaim_eq_relationStress
    (gamma : K) (claimTable : Fin 76 → K) (row : PointClaimRow) :
    sourcePreparedPointClaim gamma claimTable row =
      AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
        gamma claimTable row := by
  rfl

private theorem prepare_trace_from_exact_claims
    (kappa inactiveClaim : PrepareQM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (trace :
      AspisV5RelationPrepareLogLenProof.Prepare.PrepareRelationArithmeticTrace
        kappa inactiveClaim preparedClaims relation)
    (claim0 claim1 claim2 claim3 : K)
    (kappaCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 kappa)
    (inactiveCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 inactiveClaim)
    (claim0Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim0)
    (claim1Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim1)
    (claim2Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim2)
    (claim3Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim3)
    (claim0Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim0 =
        claim0)
    (claim1Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim1 =
        claim1)
    (claim2Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim2 =
        claim2)
    (claim3Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim3 =
        claim3) :
    AspisV5RelationPrepareFieldProjection.toMaintainedExact
        relation.relation_value =
      AspisV5RelationPrepareFieldProjection.toMaintainedExact inactiveClaim +
        claim0 +
        AspisV5RelationPrepareFieldProjection.toMaintainedExact kappa * claim1 +
        AspisV5RelationPrepareFieldProjection.toMaintainedExact kappa ^ 2 *
          claim2 +
        AspisV5RelationPrepareFieldProjection.toMaintainedExact kappa ^ 3 *
          claim3 := by
  have kappa2Result := prepare_square_run_exact kappa trace.kappa2
    kappaCanonical trace.kappa2Run
  have kappa3Result := prepare_mul_run_exact trace.kappa2 kappa trace.kappa3
    kappa2Result.1 kappaCanonical trace.kappa3Run
  have relationValue0Result := prepare_add_run_exact inactiveClaim trace.claim0
    trace.relationValue0 inactiveCanonical claim0Canonical
    trace.relationValue0Run
  have scaled1Result := prepare_mul_run_exact kappa trace.claim1 trace.scaled1
    kappaCanonical claim1Canonical trace.scaled1Run
  have relationValue1Result := prepare_add_run_exact trace.relationValue0
    trace.scaled1 trace.relationValue1 relationValue0Result.1 scaled1Result.1
    trace.relationValue1Run
  have scaled2Result := prepare_mul_run_exact trace.kappa2 trace.claim2
    trace.scaled2 kappa2Result.1 claim2Canonical trace.scaled2Run
  have relationValue2Result := prepare_add_run_exact trace.relationValue1
    trace.scaled2 trace.relationValue2 relationValue1Result.1 scaled2Result.1
    trace.relationValue2Run
  have scaled3Result := prepare_mul_run_exact trace.kappa3 trace.claim3
    trace.scaled3 kappa3Result.1 claim3Canonical trace.scaled3Run
  have relationValue3Result := prepare_add_run_exact trace.relationValue2
    trace.scaled3 trace.relationValue3 relationValue2Result.1 scaled3Result.1
    trace.relationValue3Run
  let exactKappa :=
    AspisV5RelationPrepareFieldProjection.toMaintainedExact kappa
  let exactInactive :=
    AspisV5RelationPrepareFieldProjection.toMaintainedExact inactiveClaim
  have kappa2Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.kappa2 =
        exactKappa ^ 2 := by
    simpa [exactKappa] using kappa2Result.2
  have kappa3Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.kappa3 =
        exactKappa ^ 3 := by
    rw [kappa3Result.2, kappa2Exact]
    change exactKappa ^ 2 * exactKappa = exactKappa ^ 3
    exact (pow_succ exactKappa 2).symm
  have scaled1Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.scaled1 =
        exactKappa * claim1 := by
    rw [scaled1Result.2, claim1Exact]
  have scaled2Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.scaled2 =
        exactKappa ^ 2 * claim2 := by
    rw [scaled2Result.2, kappa2Exact, claim2Exact]
  have scaled3Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.scaled3 =
        exactKappa ^ 3 * claim3 := by
    rw [scaled3Result.2, kappa3Exact, claim3Exact]
  have relationValue0Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact
          trace.relationValue0 = exactInactive + claim0 := by
    rw [relationValue0Result.2, claim0Exact]
  have relationValue1Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact
          trace.relationValue1 =
        exactInactive + claim0 + exactKappa * claim1 := by
    rw [relationValue1Result.2, relationValue0Exact, scaled1Exact]
  have relationValue2Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact
          trace.relationValue2 =
        exactInactive + claim0 + exactKappa * claim1 +
          exactKappa ^ 2 * claim2 := by
    rw [relationValue2Result.2, relationValue1Exact, scaled2Exact]
  have relationValue3Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact
          trace.relationValue3 =
        exactInactive + claim0 + exactKappa * claim1 +
          exactKappa ^ 2 * claim2 + exactKappa ^ 3 * claim3 := by
    rw [relationValue3Result.2, relationValue2Exact, scaled3Exact]
  rw [trace.returnedRelationValue, relationValue3Exact]

set_option maxHeartbeats 200000 in
/-- Exact arithmetic meaning of the source-extracted relation preparation
trace.  This theorem is independent of the outer caller adapter: it proves
the two kappa powers, four vector reads, three multiplications, and four
additions in the order executed by production. -/
theorem prepare_relation_arithmetic_trace_exact
    (kappa inactiveClaim : PrepareQM31)
    (preparedClaims :
      V5RelationPrepareGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationPrepareGenerated.v5_cu_probe.PreparedRelation)
    (gamma : K) (claimTable : Fin 76 → K)
    (trace :
      AspisV5RelationPrepareLogLenProof.Prepare.PrepareRelationArithmeticTrace
        kappa inactiveClaim preparedClaims relation)
    (kappaCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 kappa)
    (inactiveCanonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 inactiveClaim)
    (claimsCanonical :
      AspisV5RelationPrepareCanonicalProof.PrepareClaimsCanonical
        preparedClaims)
    (claimsExact : ∀ row : PointClaimRow,
      AspisV5RelationPrepareFieldProjection.toMaintainedExact
          (preparedClaims.inner.claims.val[row.val]'(by
            rw [claimsCanonical.1]
            simpa [pointClaimRows] using row.isLt)) =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
          gamma claimTable row) :
    AspisV5RelationPrepareFieldProjection.toMaintainedExact
        relation.relation_value =
      AspisV5RelationStressSourceBridge.sourceCallerInitialClaim
        (AspisV5RelationPrepareFieldProjection.toMaintainedExact inactiveClaim)
        (AspisV5RelationPrepareFieldProjection.toMaintainedExact kappa)
        gamma claimTable := by
  have claim0CanonicalPrepare :=
    AspisV5RelationPrepareCanonicalProof.point_claim_at_success_canonical
      preparedClaims 0#usize trace.claim0 (by norm_num) claimsCanonical
      trace.claim0Run
  have claim0Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim0 :=
    (AspisV5RelationPrepareCanonicalProof.prepareCanonical_iff_fieldProjection
      trace.claim0).1 claim0CanonicalPrepare
  have claim0Value := prepare_point_claim_at_success_eq preparedClaims
    0#usize trace.claim0 (by norm_num) claimsCanonical.1 trace.claim0Run
  have claim0Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim0 =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
          claimTable AspisV5RelationStressSourceBridge.sourcePoint0 := by
    rw [claim0Value]
    simpa [AspisV5RelationStressSourceBridge.sourcePoint0] using
      claimsExact AspisV5RelationStressSourceBridge.sourcePoint0
  have claim1CanonicalPrepare :=
    AspisV5RelationPrepareCanonicalProof.point_claim_at_success_canonical
      preparedClaims 1#usize trace.claim1 (by norm_num) claimsCanonical
      trace.claim1Run
  have claim1Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim1 :=
    (AspisV5RelationPrepareCanonicalProof.prepareCanonical_iff_fieldProjection
      trace.claim1).1 claim1CanonicalPrepare
  have claim1Value := prepare_point_claim_at_success_eq preparedClaims
    1#usize trace.claim1 (by norm_num) claimsCanonical.1 trace.claim1Run
  have claim1Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim1 =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
          claimTable AspisV5RelationStressSourceBridge.sourcePoint1 := by
    rw [claim1Value]
    simpa [AspisV5RelationStressSourceBridge.sourcePoint1] using
      claimsExact AspisV5RelationStressSourceBridge.sourcePoint1
  have claim2CanonicalPrepare :=
    AspisV5RelationPrepareCanonicalProof.point_claim_at_success_canonical
      preparedClaims 2#usize trace.claim2 (by norm_num) claimsCanonical
      trace.claim2Run
  have claim2Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim2 :=
    (AspisV5RelationPrepareCanonicalProof.prepareCanonical_iff_fieldProjection
      trace.claim2).1 claim2CanonicalPrepare
  have claim2Value := prepare_point_claim_at_success_eq preparedClaims
    2#usize trace.claim2 (by norm_num) claimsCanonical.1 trace.claim2Run
  have claim2Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim2 =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
          claimTable AspisV5RelationStressSourceBridge.sourcePoint2 := by
    rw [claim2Value]
    simpa [AspisV5RelationStressSourceBridge.sourcePoint2] using
      claimsExact AspisV5RelationStressSourceBridge.sourcePoint2
  have claim3CanonicalPrepare :=
    AspisV5RelationPrepareCanonicalProof.point_claim_at_success_canonical
      preparedClaims 3#usize trace.claim3 (by norm_num) claimsCanonical
      trace.claim3Run
  have claim3Canonical :
      AspisV5RelationPrepareFieldProjection.CanonicalQM31 trace.claim3 :=
    (AspisV5RelationPrepareCanonicalProof.prepareCanonical_iff_fieldProjection
      trace.claim3).1 claim3CanonicalPrepare
  have claim3Value := prepare_point_claim_at_success_eq preparedClaims
    3#usize trace.claim3 (by norm_num) claimsCanonical.1 trace.claim3Run
  have claim3Exact :
      AspisV5RelationPrepareFieldProjection.toMaintainedExact trace.claim3 =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
          claimTable AspisV5RelationStressSourceBridge.sourcePoint3 := by
    rw [claim3Value]
    simpa [AspisV5RelationStressSourceBridge.sourcePoint3] using
      claimsExact AspisV5RelationStressSourceBridge.sourcePoint3
  have arithmetic := prepare_trace_from_exact_claims kappa inactiveClaim
    preparedClaims relation trace
    (AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
      claimTable AspisV5RelationStressSourceBridge.sourcePoint0)
    (AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
      claimTable AspisV5RelationStressSourceBridge.sourcePoint1)
    (AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
      claimTable AspisV5RelationStressSourceBridge.sourcePoint2)
    (AspisV5RelationStressSourceBridge.sourcePreparedPointClaim gamma
      claimTable AspisV5RelationStressSourceBridge.sourcePoint3)
    kappaCanonical inactiveCanonical claim0Canonical claim1Canonical
    claim2Canonical claim3Canonical claim0Exact claim1Exact claim2Exact
    claim3Exact
  simpa [AspisV5RelationStressSourceBridge.sourceCallerInitialClaim] using
    arithmetic

/-- The public four-claim caller preserves the exact source initial claim
proved for its translated extraction helper. -/
theorem caller_prepare_success_relation_value_exact
    (parsed : V5RelationCallerGenerated.v5_cu_probe.ParsedProbeData)
    (kappa inactiveClaim : CallerQM31)
    (preparedClaims :
      V5RelationCallerGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (relation : V5RelationCallerGenerated.v5_cu_probe.PreparedRelation)
    (point : Array CallerQM31 10#usize)
    (denseScale : CallerQM31)
    (gamma : K) (claimTable : Fin 76 → K)
    (kappaCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 kappa)
    (inactiveCanonical :
      AspisV5RelationGeneratedFieldProjection.CanonicalQM31 inactiveClaim)
    (claimsCanonical :
      AspisV5RelationPrepareCanonicalProof.CallerClaimsCanonical
        preparedClaims)
    (claimsExact : ∀ row : PointClaimRow,
      AspisV5RelationLinkedFieldProjection.toMaintainedExact
          (preparedClaims.inner.claims.val[row.val]'(by
            rw [claimsCanonical.1]
            simpa [pointClaimRows] using row.isLt)) =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
          gamma claimTable row)
    (success :
      V5RelationCallerGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared
          parsed
          V5RelationCallerGenerated.v5_cu_probe.RelationVariant.FourClaimsCompact
          kappa inactiveClaim preparedClaims =
        .ok (.Ok (relation, point, denseScale))) :
    AspisV5RelationLinkedFieldProjection.toMaintainedExact
        relation.relation_value =
      AspisV5RelationStressSourceBridge.sourceCallerInitialClaim
        (AspisV5RelationLinkedFieldProjection.toMaintainedExact inactiveClaim)
        (AspisV5RelationLinkedFieldProjection.toMaintainedExact kappa)
        gamma claimTable := by
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
      have sourceKappaCanonicalPrepare :
          AspisV5RelationPrepareCanonicalProof.PrepareCanonicalQM31
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa) :=
        (AspisV5RelationPrepareCanonicalProof.callerToPrepare_canonical_iff
          kappa).2 kappaCanonical
      have sourceInactiveCanonicalPrepare :
          AspisV5RelationPrepareCanonicalProof.PrepareCanonicalQM31
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31
              inactiveClaim) :=
        (AspisV5RelationPrepareCanonicalProof.callerToPrepare_canonical_iff
          inactiveClaim).2 inactiveCanonical
      have sourceKappaCanonical :
          AspisV5RelationPrepareFieldProjection.CanonicalQM31
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa) :=
        (AspisV5RelationPrepareCanonicalProof.prepareCanonical_iff_fieldProjection
          _).1 sourceKappaCanonicalPrepare
      have sourceInactiveCanonical :
          AspisV5RelationPrepareFieldProjection.CanonicalQM31
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31
              inactiveClaim) :=
        (AspisV5RelationPrepareCanonicalProof.prepareCanonical_iff_fieldProjection
          _).1 sourceInactiveCanonicalPrepare
      have sourceClaimsCanonical :
          AspisV5RelationPrepareCanonicalProof.PrepareClaimsCanonical
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims
              preparedClaims) :=
        AspisV5RelationPrepareCanonicalProof.callerClaims_to_prepare_canonical
          preparedClaims claimsCanonical
      change
        V5RelationPrepareGenerated.v5_cu_probe.prepare_relation_base_with_kappa_prepared_for_extraction
            _
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa)
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31
              inactiveClaim)
            (AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims
              preparedClaims) =
          .ok (.Ok (sourceRelation, sourcePoint, sourceScale))
        at sourceRunEquation
      obtain ⟨_, ⟨trace, _⟩⟩ :=
        AspisV5RelationPrepareLogLenProof.Prepare.prepare_for_extraction_success_exposes_arithmetic
          _
          (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa)
          (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31
            inactiveClaim)
          (AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims
            preparedClaims)
          sourceRelation sourcePoint sourceScale sourceRunEquation
      have sourceClaimsExact : ∀ row : PointClaimRow,
          AspisV5RelationPrepareFieldProjection.toMaintainedExact
              ((AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims
                preparedClaims).inner.claims.val[row.val]'(by
                  rw [sourceClaimsCanonical.1]
                  simpa [pointClaimRows] using row.isLt)) =
            AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
              gamma claimTable row := by
        intro row
        simpa [AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims,
          AspisV5RelationPrepareCanonicalProof.callerToPrepareVec,
          row.isLt, claimsCanonical.1] using claimsExact row
      have sourceArithmetic := prepare_relation_arithmetic_trace_exact
        (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 kappa)
        (AspisV5RelationPrepareCanonicalProof.callerToPrepareQM31 inactiveClaim)
        (AspisV5RelationPrepareCanonicalProof.callerToPrepareClaims
          preparedClaims)
        sourceRelation gamma claimTable trace sourceKappaCanonical
        sourceInactiveCanonical sourceClaimsCanonical sourceClaimsExact
      simp only at success
      have tripleEquality := core.result.Result.Ok.inj (Result.ok.inj success)
      have relationValueEquality := congrArg
        (fun triple => triple.1.relation_value) tripleEquality
      change
        AspisV5RelationPrepareCanonicalProof.prepareToCallerQM31
            sourceRelation.relation_value = relation.relation_value
        at relationValueEquality
      rw [← relationValueEquality,
        prepareToCaller_toMaintainedExact]
      simpa only [callerToPrepare_toMaintainedExact] using sourceArithmetic

/-- The exact field value of an accepted-entry QM31 value. -/
def entryClaimToK (value : AcceptedQM31) : K :=
  entryToK value

/-- The exact sixteen-byte slice supplied to the production decoder for one
table position. -/
def acceptedPointClaimFieldSlice (bytes : Slice Std.U8) (field : Fin 76) :
    Slice Std.U8 :=
  ⟨bytes.val.slice (16 * field.val) (16 * field.val + 16), by
    rw [List.slice_length]
    have : 16 ≤ Std.Usize.max := by scalar_tac
    omega⟩

/-- Partial production decode of one accepted table field. -/
def acceptedPointClaimField (bytes : Slice Std.U8) (field : Fin 76) :
    Option K :=
  match V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes
      (acceptedPointClaimFieldSlice bytes field) with
  | .ok (some value) => some (entryClaimToK value)
  | _ => none

/-- Deterministic 76-entry mathematical table derived from the accepted
production decoder.  The zero branch is unreachable in every accepted
preparation run. -/
def acceptedPointClaimTable (bytes : Slice Std.U8) : Fin 76 → K :=
  fun field => (acceptedPointClaimField bytes field).getD 0

@[simp] theorem entryClaimToK_eq_kernelExact (value : AcceptedQM31) :
    entryClaimToK value =
      kernelQM31ToExact
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
          value) := by
  rfl

@[simp] theorem entryClaimToK_fromPreparedKernel
    (value : PreparedKernelQM31) :
    entryClaimToK
        (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          value) =
      kernelQM31ToExact value := by
  rfl

def entryArrayToPreparedKernel (values : Array AcceptedQM31 19#usize) :
    Array PreparedKernelQM31 19#usize :=
  V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
    values

@[simp] theorem entryArrayToPreparedKernel_entry
    (values : Array AcceptedQM31 19#usize) (index : Fin 19) :
    AspisV5PreparedPointClaimsSourceProof.kernelArrayEntry
        (entryArrayToPreparedKernel values) index =
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
        values.val[index.val]! := by
  simp [entryArrayToPreparedKernel,
    AspisV5PreparedPointClaimsSourceProof.kernelArrayEntry,
    V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray, index.isLt]

/-- The accepted wrapper around the extracted gamma-power kernel preserves
every exact field value. -/
theorem preparedKernelGammaPowers_success_exact
    (gamma : AcceptedQM31) (powers : Array AcceptedQM31 19#usize)
    (gammaCanonical : EntryCanonicalQM31 gamma)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers
          gamma = .ok powers) :
    ∀ lane : TotalLane,
      entryClaimToK powers.val[lane.val]! = entryClaimToK gamma ^ lane.val := by
  let kernelGamma :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 gamma
  have kernelGammaCanonical : KernelCanonicalQM31 kernelGamma :=
    (toPreparedKernel_canonical_iff gamma).2 gammaCanonical
  obtain ⟨kernelPowers, kernelRun, kernelPost⟩ :=
    extracted_gamma_powers_eq_source_weights kernelGamma kernelGammaCanonical
  have wrapperRun :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers
          gamma =
        .ok (V5AcceptedEntryGenerated.aspis_core.field.mapLinkedArray
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          kernelPowers) := by
    simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers,
      V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult, kernelGamma,
      kernelRun]
  rw [wrapperRun] at success
  cases success
  intro lane
  have exactPower := (kernelPost lane).2
  rw [mapped_fromKernel_entry]
  change kernelQM31ToExact kernelPowers.val[lane.val]! =
    kernelQM31ToExact kernelGamma ^ lane.val
  simpa [AspisV5PreparedPointClaimsSourceProof.kernelArrayEntry,
    sourceGammaWeight] using exactPower

/-- Exact value returned by one successful accepted-entry field addition. -/
theorem entry_qm31_add_success_exact
    (left right output : AcceptedQM31)
    (leftCanonical : EntryCanonicalQM31 left)
    (rightCanonical : EntryCanonicalQM31 right)
    (success :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.add left right =
        .ok output) :
    entryClaimToK output = entryClaimToK left + entryClaimToK right := by
  let kernelLeft :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 left
  let kernelRight :=
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31 right
  have kernelLeftCanonical : KernelCanonicalQM31 kernelLeft :=
    (toPreparedKernel_canonical_iff left).2 leftCanonical
  have kernelRightCanonical : KernelCanonicalQM31 kernelRight :=
    (toPreparedKernel_canonical_iff right).2 rightCanonical
  obtain ⟨kernelOutput, kernelRun, _kernelOutputCanonical, kernelExact⟩ :=
    extracted_kernel_qm31_add_corresponds kernelLeft kernelRight
      kernelLeftCanonical kernelRightCanonical
  have kernelAddRun :
      V5RelationPreparedClaimsGenerated.aspis_core.field.QM31.add
          kernelLeft kernelRight = .ok kernelOutput := by
    simpa [V5RelationPreparedClaimsGenerated.extracted_qm31_add] using
      kernelRun
  rw [entry_qm31_add_eq_preparedKernel, kernelAddRun] at success
  simp only [V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult,
    Result.ok.injEq] at success
  subst output
  change kernelQM31ToExact kernelOutput =
    kernelQM31ToExact kernelLeft + kernelQM31ToExact kernelRight
  exact kernelExact

/-- Exact block dot product returned by the accepted wrapper. -/
theorem preparedKernelClaimDotBlock_success_exact
    (powers values : Array AcceptedQM31 19#usize)
    (start count : Std.Usize) (output : AcceptedQM31)
    (countBound : count.val ≤ 4)
    (spanBound : start.val + count.val ≤ 19)
    (powersCanonical : EntryCanonicalArray powers)
    (valuesCanonical : EntryCanonicalArray values)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock
          powers values start count = .ok output) :
    entryClaimToK output =
      kernelExactBlockDot (entryArrayToPreparedKernel powers)
        (entryArrayToPreparedKernel values) start.val count.val := by
  let kernelPowers := entryArrayToPreparedKernel powers
  let kernelValues := entryArrayToPreparedKernel values
  have kernelPowersCanonical : KernelCanonicalQM31Array19 kernelPowers :=
    entryCanonicalArray_toKernel powers powersCanonical
  have kernelValuesCanonical : KernelCanonicalQM31Array19 kernelValues :=
    entryCanonicalArray_toKernel values valuesCanonical
  obtain ⟨kernelOutput, kernelRun, _kernelOutputCanonical, kernelExact⟩ :=
    extracted_claim_dot_block_corresponds kernelPowers kernelValues start count
      countBound spanBound kernelPowersCanonical kernelValuesCanonical
  change
    V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block
        (entryArrayToPreparedKernel powers) (entryArrayToPreparedKernel values)
        start count = .ok kernelOutput at kernelRun
  have wrapperRun :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock
          powers values start count =
        .ok (V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          kernelOutput) := by
    unfold
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelClaimDotBlock
    change
      V5AcceptedEntryGenerated.aspis_core.field.mapLinkedResult
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.fromPreparedKernelQM31
          (V5RelationPreparedClaimsGenerated.fri_checks.v5_claim_dot_block
            (entryArrayToPreparedKernel powers)
            (entryArrayToPreparedKernel values) start count) = _
    rw [kernelRun]
    rfl
  rw [wrapperRun] at success
  cases success
  change kernelQM31ToExact kernelOutput = _
  exact kernelExact

/-! ## Exact accepted claim decoder loop -/

def DecodedPointPrefix (bytes : Slice Std.U8) (point : PointClaimRow)
    (column : Nat) (values : Array AcceptedQM31 19#usize) : Prop :=
  ∀ lane : TotalLane, lane.val < column →
    entryClaimToK values.val[lane.val]! =
      acceptedPointClaimTable bytes (pointMajorClaimLayout (point, lane))

theorem acceptedPointClaimTable_of_decoder_success
    (bytes : Slice Std.U8) (field : Fin 76) (value : AcceptedQM31)
    (success :
      V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes
          (acceptedPointClaimFieldSlice bytes field) = .ok (some value)) :
    acceptedPointClaimTable bytes field = entryClaimToK value := by
  simp [acceptedPointClaimTable, acceptedPointClaimField, success]

private theorem decodedPointPrefix_set_next
    (bytes : Slice Std.U8) (point : PointClaimRow)
    (column : Std.Usize) (values : Array AcceptedQM31 19#usize)
    (value : AcceptedQM31)
    (columnBound : column.val < 19)
    (decodedPrefix : DecodedPointPrefix bytes point column.val values)
    (valueExact : entryClaimToK value =
      acceptedPointClaimTable bytes
        (pointMajorClaimLayout
          (point, ⟨column.val, columnBound⟩))) :
    DecodedPointPrefix bytes point (column.val + 1)
      (values.set column value) := by
  intro lane laneBound
  by_cases same : lane.val = column.val
  · have laneEq : lane = ⟨column.val, columnBound⟩ := Fin.ext same
    subst lane
    unfold entryClaimToK
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using columnBound, rfl⟩)]
    exact valueExact
  · have before : lane.val < column.val := by omega
    unfold entryClaimToK
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne values.val column.val lane.val value
      (Or.inl (by omega))]
    exact decodedPrefix lane before

/-- A successful translated 19-field decoder loop returns the exact
point-major row of the deterministic production-decoded table. -/
theorem decodeClaimValuesAux_success_exact
    (remaining : Nat) :
    ∀ (point : PointClaimRow) (runtimePoint column : Std.Usize)
      (bytes : Slice Std.U8)
      (values output : Array AcceptedQM31 19#usize),
      runtimePoint.val = point.val →
      column.val + remaining = 19 →
      bytes.val.length = 1216 →
      DecodedPointPrefix bytes point column.val values →
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux
          remaining runtimePoint column bytes values = .ok (.Ok output) →
      ∀ lane : TotalLane,
        entryClaimToK output.val[lane.val]! =
          acceptedPointClaimTable bytes
            (pointMajorClaimLayout (point, lane)) := by
  induction remaining with
  | zero =>
      intro point runtimePoint column bytes values output _ span _
        decodedPrefix success
      simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux]
        at success
      subst output
      intro lane
      have laneBound : lane.val < 19 := by
        simpa [totalLaneCount] using lane.isLt
      exact decodedPrefix lane (by omega)
  | succ remaining inductionHypothesis =>
      intro point runtimePoint column bytes values output pointValue span
        bytesLength decodedPrefix success
      have columnBound : column.val < 19 := by omega
      unfold
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux
        at success
      generalize pointBaseEquation : runtimePoint * 19#usize = pointBaseResult
        at success
      cases pointBaseResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
      | div => simp [Bind.bind, Aeneas.Std.bind] at success
      | ok pointBase =>
        simp only [bind_tc_ok] at success
        generalize indexEquation : pointBase + column = indexResult at success
        cases indexResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
        | div => simp [Bind.bind, Aeneas.Std.bind] at success
        | ok index =>
          simp only [bind_tc_ok] at success
          generalize offsetEquation : index * 16#usize = offsetResult at success
          cases offsetResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
          | div => simp [Bind.bind, Aeneas.Std.bind] at success
          | ok offset =>
            simp only [bind_tc_ok] at success
            generalize stopEquation : offset + 16#usize = stopResult at success
            cases stopResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
            | div => simp [Bind.bind, Aeneas.Std.bind] at success
            | ok stop =>
              simp only [bind_tc_ok] at success
              generalize encodedEquation :
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                  bytes { start := offset, «end» := stop } = encodedResult
                at success
              cases encodedResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
              | div => simp [Bind.bind, Aeneas.Std.bind] at success
              | ok encoded =>
                simp only [bind_tc_ok] at success
                generalize decodedEquation :
                  V5AcceptedEntryGenerated.aspis_core.field.QM31.from_le_bytes
                    encoded = decodedResult at success
                cases decodedResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
                | div => simp [Bind.bind, Aeneas.Std.bind] at success
                | ok decoded =>
                  cases decoded with
                  | none => simp [Bind.bind, Aeneas.Std.bind] at success
                  | some value =>
                    simp only [bind_tc_ok] at success
                    generalize updateEquation :
                      Array.update values column value = updateResult at success
                    cases updateResult with
                    | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
                    | div => simp [Bind.bind, Aeneas.Std.bind] at success
                    | ok updated =>
                      simp only [bind_tc_ok] at success
                      generalize nextEquation : column + 1#usize = nextResult
                        at success
                      cases nextResult with
                      | fail error =>
                        simp [Bind.bind, Aeneas.Std.bind] at success
                      | div => simp [Bind.bind, Aeneas.Std.bind] at success
                      | ok next =>
                        simp only [bind_tc_ok] at success
                        change UScalar.mul runtimePoint 19#usize = .ok pointBase
                          at pointBaseEquation
                        change UScalar.mul index 16#usize = .ok offset
                          at offsetEquation
                        have pointBaseFacts :=
                          @UScalar.mul_equiv UScalarTy.Usize runtimePoint
                            19#usize
                        rw [pointBaseEquation] at pointBaseFacts
                        have indexFacts :=
                          @UScalar.add_equiv UScalarTy.Usize pointBase column
                        rw [indexEquation] at indexFacts
                        have offsetFacts :=
                          @UScalar.mul_equiv UScalarTy.Usize index 16#usize
                        rw [offsetEquation] at offsetFacts
                        have stopFacts :=
                          @UScalar.add_equiv UScalarTy.Usize offset 16#usize
                        rw [stopEquation] at stopFacts
                        have nextFacts :=
                          @UScalar.add_equiv UScalarTy.Usize column 1#usize
                        rw [nextEquation] at nextFacts
                        have pointBaseValue :
                            pointBase.val = runtimePoint.val * 19 := by
                          exact pointBaseFacts.2.1
                        have indexValue :
                            index.val = pointBase.val + column.val := by
                          exact indexFacts.2.1
                        have offsetValue : offset.val = index.val * 16 := by
                          exact offsetFacts.2.1
                        have stopValue : stop.val = offset.val + 16 := by
                          exact stopFacts.2.1
                        have nextValue : next.val = column.val + 1 := by
                          exact nextFacts.2.1
                        let lane : TotalLane := ⟨column.val, columnBound⟩
                        let field : Fin 76 :=
                          pointMajorClaimLayout (point, lane)
                        have encodedFacts :=
                          AspisV5FriProductionDecoderCanonical.slice_range_success_facts
                            bytes encoded offset stop encodedEquation
                        have encodedExact :
                            encoded = acceptedPointClaimFieldSlice bytes field := by
                          apply Subtype.ext
                          rw [encodedFacts.2.2]
                          simp only [acceptedPointClaimFieldSlice]
                          congr 1 <;>
                            simp [field, lane, pointMajorClaimLayout_val,
                              pointValue, pointBaseValue, indexValue,
                              offsetValue, stopValue] <;> omega
                        have decoderExact :
                            acceptedPointClaimTable bytes field =
                              entryClaimToK value := by
                          apply acceptedPointClaimTable_of_decoder_success
                          rw [← encodedExact]
                          exact decodedEquation
                        have valueExact : entryClaimToK value =
                            acceptedPointClaimTable bytes
                              (pointMajorClaimLayout
                                (point, ⟨column.val, columnBound⟩)) := by
                          exact decoderExact.symm
                        have updatedEquality :
                            updated = values.set column value :=
                          array_update_success_eq values column value updated
                            columnBound updateEquation
                        have updatedPrefix :
                            DecodedPointPrefix bytes point (column.val + 1)
                              updated := by
                          rw [updatedEquality]
                          exact decodedPointPrefix_set_next bytes point column
                            values value columnBound decodedPrefix valueExact
                        apply inductionHypothesis point runtimePoint next bytes
                          updated output pointValue
                        · omega
                        · exact bytesLength
                        · simpa [nextValue] using updatedPrefix
                        · exact success

/-! ## Exact five-block claim sum -/

private theorem entry_exact_block_dot_eq_source_contiguous
    (gamma : AcceptedQM31)
    (powers values : Array AcceptedQM31 19#usize)
    (claims : Fin 76 → K) (point : PointClaimRow)
    (start count : Nat) (spanBound : start + count ≤ 19)
    (powersExact : ∀ lane : TotalLane,
      entryClaimToK powers.val[lane.val]! = entryClaimToK gamma ^ lane.val)
    (valuesExact : ∀ lane : TotalLane,
      entryClaimToK values.val[lane.val]! =
        claims (pointMajorClaimLayout (point, lane))) :
    kernelExactBlockDot (entryArrayToPreparedKernel powers)
        (entryArrayToPreparedKernel values) start count =
      sourceContiguousPointClaimBlock (entryClaimToK gamma)
        claims point start count := by
  classical
  unfold kernelExactBlockDot sourceContiguousPointClaimBlock
  apply Finset.sum_congr rfl
  intro offset offsetMembership
  simp only [Finset.mem_range] at offsetMembership
  have indexBound : start + offset < 19 := by omega
  let lane : TotalLane := ⟨start + offset, by
    simpa [totalLaneCount] using indexBound⟩
  have powerExact := powersExact lane
  have valueExact := valuesExact lane
  have mappedPower :
      (entryArrayToPreparedKernel powers).val[start + offset]! =
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
          powers.val[start + offset]! := by
    simpa [AspisV5PreparedPointClaimsSourceProof.kernelArrayEntry, lane] using
      entryArrayToPreparedKernel_entry powers lane
  have mappedValue :
      (entryArrayToPreparedKernel values).val[start + offset]! =
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.toPreparedKernelQM31
          values.val[start + offset]! := by
    simpa [AspisV5PreparedPointClaimsSourceProof.kernelArrayEntry, lane] using
      entryArrayToPreparedKernel_entry values lane
  rw [mappedPower, mappedValue]
  rw [kernelExact_mul_eq_maintained]
  change entryClaimToK powers.val[lane.val]! *
      entryClaimToK values.val[lane.val]! = _
  rw [powerExact, valueExact]
  simp [sourcePointClaimTerm, sourceGammaWeight, totalLaneCount, indexBound,
    lane]

/-- The accepted five-block helper returns exactly the maintained prepared
claim for this point, provided its production-decoded row and gamma powers
have already been identified. -/
theorem sumPreparedClaimBlocks_success_exact_source
    (gamma : AcceptedQM31) (claims : Fin 76 → K)
    (point : PointClaimRow)
    (powers values : Array AcceptedQM31 19#usize)
    (output : AcceptedQM31)
    (powersCanonical : EntryCanonicalArray powers)
    (valuesCanonical : EntryCanonicalArray values)
    (powersExact : ∀ lane : TotalLane,
      entryClaimToK powers.val[lane.val]! = entryClaimToK gamma ^ lane.val)
    (valuesExact : ∀ lane : TotalLane,
      entryClaimToK values.val[lane.val]! =
        claims (pointMajorClaimLayout (point, lane)))
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks
          powers values = .ok output) :
    entryClaimToK output =
      sourcePreparedPointClaim (entryClaimToK gamma) claims point := by
  obtain ⟨block0, block0Run, block0Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      0#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block1, block1Run, block1Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      4#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block2, block2Run, block2Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      8#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block3, block3Run, block3Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      12#usize 4#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨block4, block4Run, block4Canonical⟩ :=
    preparedKernelClaimDotBlock_exists_canonical powers values
      16#usize 3#usize (by norm_num) (by norm_num)
      powersCanonical valuesCanonical
  obtain ⟨sum01, sum01Run, sum01Canonical⟩ :=
    entry_qm31_add_exists_canonical block0 block1 block0Canonical
      block1Canonical
  obtain ⟨sum012, sum012Run, sum012Canonical⟩ :=
    entry_qm31_add_exists_canonical sum01 block2 sum01Canonical
      block2Canonical
  obtain ⟨sum0123, sum0123Run, sum0123Canonical⟩ :=
    entry_qm31_add_exists_canonical sum012 block3 sum012Canonical
      block3Canonical
  obtain ⟨expected, expectedRun, _expectedCanonical⟩ :=
    entry_qm31_add_exists_canonical sum0123 block4 sum0123Canonical
      block4Canonical
  have wholeRun :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks
          powers values = .ok expected := by
    simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks,
      block0Run, block1Run, block2Run, block3Run, block4Run,
      sum01Run, sum012Run, sum0123Run, expectedRun]
  rw [wholeRun] at success
  cases success
  have block0Exact := preparedKernelClaimDotBlock_success_exact powers values
    0#usize 4#usize block0 (by norm_num) (by norm_num)
    powersCanonical valuesCanonical block0Run
  have block1Exact := preparedKernelClaimDotBlock_success_exact powers values
    4#usize 4#usize block1 (by norm_num) (by norm_num)
    powersCanonical valuesCanonical block1Run
  have block2Exact := preparedKernelClaimDotBlock_success_exact powers values
    8#usize 4#usize block2 (by norm_num) (by norm_num)
    powersCanonical valuesCanonical block2Run
  have block3Exact := preparedKernelClaimDotBlock_success_exact powers values
    12#usize 4#usize block3 (by norm_num) (by norm_num)
    powersCanonical valuesCanonical block3Run
  have block4Exact := preparedKernelClaimDotBlock_success_exact powers values
    16#usize 3#usize block4 (by norm_num) (by norm_num)
    powersCanonical valuesCanonical block4Run
  have sum01Exact := entry_qm31_add_success_exact block0 block1 sum01
    block0Canonical block1Canonical sum01Run
  have sum012Exact := entry_qm31_add_success_exact sum01 block2 sum012
    sum01Canonical block2Canonical sum012Run
  have sum0123Exact := entry_qm31_add_success_exact sum012 block3 sum0123
    sum012Canonical block3Canonical sum0123Run
  have expectedExact := entry_qm31_add_success_exact sum0123 block4 output
    sum0123Canonical block4Canonical expectedRun
  rw [expectedExact, sum0123Exact, sum012Exact, sum01Exact,
    block0Exact, block1Exact, block2Exact, block3Exact, block4Exact]
  change
    kernelExactBlockDot (entryArrayToPreparedKernel powers)
          (entryArrayToPreparedKernel values) 0 4 +
        kernelExactBlockDot (entryArrayToPreparedKernel powers)
            (entryArrayToPreparedKernel values) 4 4 +
      kernelExactBlockDot (entryArrayToPreparedKernel powers)
          (entryArrayToPreparedKernel values) 8 4 +
    kernelExactBlockDot (entryArrayToPreparedKernel powers)
        (entryArrayToPreparedKernel values) 12 4 +
    kernelExactBlockDot (entryArrayToPreparedKernel powers)
        (entryArrayToPreparedKernel values) 16 3 = _
  rw [entry_exact_block_dot_eq_source_contiguous gamma powers values claims
      point 0 4 (by norm_num) powersExact valuesExact,
    entry_exact_block_dot_eq_source_contiguous gamma powers values claims
      point 4 4 (by norm_num) powersExact valuesExact,
    entry_exact_block_dot_eq_source_contiguous gamma powers values claims
      point 8 4 (by norm_num) powersExact valuesExact,
    entry_exact_block_dot_eq_source_contiguous gamma powers values claims
      point 12 4 (by norm_num) powersExact valuesExact,
    entry_exact_block_dot_eq_source_contiguous gamma powers values claims
      point 16 3 (by norm_num) powersExact valuesExact]
  change sourceFiveBlockPointClaim (entryClaimToK gamma) claims point =
    sourcePreparedPointClaim (entryClaimToK gamma) claims point
  rw [sourceFiveBlockPointClaim_eq_sourcePointClaim,
    sourcePreparedPointClaim_eq_sourcePointClaim]

/-! ## Exact four-point preparation loop -/

def PreparedPointPrefix (gamma : AcceptedQM31) (bytes : Slice Std.U8)
    (point : Nat) (claims : Array AcceptedQM31 4#usize) : Prop :=
  ∀ row : PointClaimRow, row.val < point →
    entryClaimToK claims.val[row.val]! =
      sourcePreparedPointClaim (entryClaimToK gamma)
        (acceptedPointClaimTable bytes) row

private theorem preparedPointPrefix_set_next
    (gamma : AcceptedQM31) (bytes : Slice Std.U8)
    (point : Std.Usize) (claims : Array AcceptedQM31 4#usize)
    (claim : AcceptedQM31)
    (pointBound : point.val < 4)
    (preparedPrefix : PreparedPointPrefix gamma bytes point.val claims)
    (claimExact : entryClaimToK claim =
      sourcePreparedPointClaim (entryClaimToK gamma)
        (acceptedPointClaimTable bytes)
        ⟨point.val, by simpa [pointClaimRows] using pointBound⟩) :
    PreparedPointPrefix gamma bytes (point.val + 1)
      (claims.set point claim) := by
  intro row rowBound
  by_cases same : row.val = point.val
  · have rowEquality :
        row = ⟨point.val, by simpa [pointClaimRows] using pointBound⟩ :=
      Fin.ext same
    subst row
    unfold entryClaimToK
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_eq _ _ _ _ (by
      exact ⟨by simpa [Array.length_eq] using pointBound, rfl⟩)]
    exact claimExact
  · have before : row.val < point.val := by omega
    unfold entryClaimToK
    simp only [Array.set_val_eq]
    rw [List.set_getElem!_ne claims.val point.val row.val claim
      (Or.inl (by omega))]
    exact preparedPrefix row before

/-- A successful translated four-point loop returns exactly the four
maintained prepared claims computed from the production-decoded byte table. -/
theorem preparePointClaimsAux_success_exact
    (remaining : Nat) :
    ∀ (gamma : AcceptedQM31) (point : Std.Usize)
      (bytes : Slice Std.U8)
      (powers : Array AcceptedQM31 19#usize)
      (claims output : Array AcceptedQM31 4#usize),
      point.val + remaining = 4 →
      bytes.val.length = 1216 →
      EntryCanonicalArray powers →
      (∀ lane : TotalLane,
        entryClaimToK powers.val[lane.val]! =
          entryClaimToK gamma ^ lane.val) →
      EntryCanonicalArray claims →
      PreparedPointPrefix gamma bytes point.val claims →
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux
          remaining point bytes powers claims = .ok (.Ok output) →
      ∀ row : PointClaimRow,
        entryClaimToK output.val[row.val]! =
          sourcePreparedPointClaim (entryClaimToK gamma)
            (acceptedPointClaimTable bytes) row := by
  induction remaining with
  | zero =>
      intro gamma point bytes powers claims output span _ _ _ _
        preparedPrefix success
      simp [V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux]
        at success
      subst output
      intro row
      exact preparedPrefix row (by
        have rowBound : row.val < 4 := by
          simpa [pointClaimRows] using row.isLt
        omega)
  | succ remaining inductionHypothesis =>
      intro gamma point bytes powers claims output span bytesLength
        powersCanonical powersExact claimsCanonical preparedPrefix success
      have pointBound : point.val < 4 := by omega
      let pointRow : PointClaimRow :=
        ⟨point.val, by simpa [pointClaimRows] using pointBound⟩
      unfold
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux
        at success
      generalize zeroEquation :
        V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = zeroResult
        at success
      cases zeroResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
      | div => simp [Bind.bind, Aeneas.Std.bind] at success
      | ok zero =>
        simp only [bind_tc_ok] at success
        let initialValues : Array AcceptedQM31 19#usize :=
          Array.repeat 19#usize zero
        have zeroCanonical : EntryCanonicalQM31 zero :=
          entry_qm31_zero_success_canonical zero zeroEquation
        have initialValuesCanonical : EntryCanonicalArray initialValues :=
          entryCanonicalArray_repeat 19#usize zero zeroCanonical
        generalize decodeEquation :
          V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.decodeClaimValuesAux
            19 point 0#usize bytes initialValues = decodeResult at success
        cases decodeResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
        | div => simp [Bind.bind, Aeneas.Std.bind] at success
        | ok decoded =>
          cases decoded with
          | Err error => simp [Bind.bind, Aeneas.Std.bind] at success
          | Ok values =>
            simp only [bind_tc_ok] at success
            have valuesCanonical : EntryCanonicalArray values :=
              decodeClaimValuesAux_success_canonical 19 point 0#usize bytes
                initialValues values (by norm_num) initialValuesCanonical
                decodeEquation
            have initialValuesPrefix :
                DecodedPointPrefix bytes pointRow 0 initialValues := by
              intro lane impossible
              omega
            have valuesExact : ∀ lane : TotalLane,
                entryClaimToK values.val[lane.val]! =
                  acceptedPointClaimTable bytes
                    (pointMajorClaimLayout (pointRow, lane)) :=
              decodeClaimValuesAux_success_exact 19 pointRow point 0#usize
                bytes initialValues values (by rfl) (by norm_num)
                bytesLength initialValuesPrefix decodeEquation
            generalize claimEquation :
              V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.sumPreparedClaimBlocks
                powers values = claimResult at success
            cases claimResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
            | div => simp [Bind.bind, Aeneas.Std.bind] at success
            | ok claim =>
              simp only [bind_tc_ok] at success
              have claimCanonical : EntryCanonicalQM31 claim :=
                sumPreparedClaimBlocks_success_canonical powers values claim
                  powersCanonical valuesCanonical claimEquation
              have claimExact : entryClaimToK claim =
                  sourcePreparedPointClaim (entryClaimToK gamma)
                    (acceptedPointClaimTable bytes) pointRow :=
                sumPreparedClaimBlocks_success_exact_source gamma
                  (acceptedPointClaimTable bytes) pointRow powers values claim
                  powersCanonical valuesCanonical powersExact valuesExact
                  claimEquation
              generalize updateEquation :
                Array.update claims point claim = updateResult at success
              cases updateResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
              | div => simp [Bind.bind, Aeneas.Std.bind] at success
              | ok updatedClaims =>
                simp only [bind_tc_ok] at success
                have updatedClaimsCanonical :
                    EntryCanonicalArray updatedClaims :=
                  array_update_preserves_entryCanonical claims updatedClaims
                    point claim pointBound claimsCanonical claimCanonical
                    updateEquation
                have updatedEquality :
                    updatedClaims = claims.set point claim :=
                  array_update_success_eq claims point claim updatedClaims
                    pointBound updateEquation
                have updatedPrefix : PreparedPointPrefix gamma bytes
                    (point.val + 1) updatedClaims := by
                  rw [updatedEquality]
                  exact preparedPointPrefix_set_next gamma bytes point claims
                    claim pointBound preparedPrefix claimExact
                generalize nextEquation : point + 1#usize = nextResult
                  at success
                cases nextResult with
                | fail error =>
                  simp [Bind.bind, Aeneas.Std.bind] at success
                | div => simp [Bind.bind, Aeneas.Std.bind] at success
                | ok next =>
                  simp only [bind_tc_ok] at success
                  have addFacts :=
                    @UScalar.add_equiv UScalarTy.Usize point 1#usize
                  rw [nextEquation] at addFacts
                  have nextValue : next.val = point.val + 1 := by
                    calc
                      next.val = point.val + (1#usize : Std.Usize).val :=
                        addFacts.2.1
                      _ = point.val + 1 := by rfl
                  apply inductionHypothesis gamma next bytes powers
                    updatedClaims output
                  · omega
                  · exact bytesLength
                  · exact powersCanonical
                  · exact powersExact
                  · exact updatedClaimsCanonical
                  · simpa [nextValue] using updatedPrefix
                  · exact success

/-- Exact mathematical meaning of the four claims stored in a production
`V5PreparedPcsClaims` value. -/
def PreparedClaimsExact (gamma : AcceptedQM31) (bytes : Slice Std.U8)
    (prepared :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    Prop :=
  ∀ row : PointClaimRow,
    entryClaimToK prepared.inner.claims.val[row.val]! =
      sourcePreparedPointClaim (entryClaimToK gamma)
        (acceptedPointClaimTable bytes) row

/-- Exact end-to-end specification of the accepted production claim
preparation call.  It covers the real length check, gamma-power builder,
76-field decoder, five-block sums, and four stored output claims. -/
theorem prepare_v5_pcs_claims_success_exact
    (gamma : AcceptedQM31) (bytes : Slice Std.U8)
    (prepared :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.V5PreparedPcsClaims)
    (gammaCanonical : EntryCanonicalQM31 gamma)
    (success :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepare_v5_pcs_claims
          gamma bytes = .ok (.Ok prepared)) :
    PreparedClaimsExact gamma bytes prepared := by
  unfold
    V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepare_v5_pcs_claims
    at success
  dsimp only at success
  split at success
  · simp at success
  · rename_i lengthCheck
    have runtimeLength : Slice.len bytes = 1216#usize := by
      simpa only [bne_iff_ne, ne_eq, not_not] using lengthCheck
    have bytesLength : bytes.val.length = 1216 := by
      have valueEquality := congrArg UScalar.val runtimeLength
      simpa [Slice.len] using valueEquality
    generalize powersEquation :
      V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparedKernelGammaPowers
        gamma = powersResult at success
    cases powersResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
    | div => simp [Bind.bind, Aeneas.Std.bind] at success
    | ok powers =>
      simp only [bind_tc_ok] at success
      have powersCanonical : EntryCanonicalArray powers :=
        preparedKernelGammaPowers_success_canonical gamma powers
          gammaCanonical powersEquation
      have powersExact : ∀ lane : TotalLane,
          entryClaimToK powers.val[lane.val]! =
            entryClaimToK gamma ^ lane.val :=
        preparedKernelGammaPowers_success_exact gamma powers gammaCanonical
          powersEquation
      let emptyLimbs := Array.repeat 4#usize 0#u32
      generalize c1Equation :
        V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepareC1WeightsAux
          16 0#usize powers (Array.repeat 16#usize emptyLimbs) = c1Result
        at success
      cases c1Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
      | div => simp [Bind.bind, Aeneas.Std.bind] at success
      | ok c1WeightLimbs =>
        simp only [bind_tc_ok] at success
        generalize zeroEquation :
          V5AcceptedEntryGenerated.aspis_core.field.QM31.ZERO = zeroResult
          at success
        cases zeroResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
        | div => simp [Bind.bind, Aeneas.Std.bind] at success
        | ok zero =>
          simp only [bind_tc_ok] at success
          have zeroCanonical : EntryCanonicalQM31 zero :=
            entry_qm31_zero_success_canonical zero zeroEquation
          generalize multiplierEquation :
            V5AcceptedEntryGenerated.aspis_core.field.PreparedQm31Multiplier.new
              zero = multiplierResult at success
          cases multiplierResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
          | div => simp [Bind.bind, Aeneas.Std.bind] at success
          | ok emptyMultiplier =>
            simp only [bind_tc_ok] at success
            generalize c2Equation :
              V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.prepareC2MultipliersAux
                3 0#usize powers
                  (Array.repeat 3#usize emptyMultiplier) = c2Result
              at success
            cases c2Result with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
            | div => simp [Bind.bind, Aeneas.Std.bind] at success
            | ok c2Multipliers =>
              simp only [bind_tc_ok] at success
              let initialClaims : Array AcceptedQM31 4#usize :=
                Array.repeat 4#usize zero
              have initialClaimsCanonical : EntryCanonicalArray initialClaims :=
                entryCanonicalArray_repeat 4#usize zero zeroCanonical
              have initialClaimsPrefix :
                  PreparedPointPrefix gamma bytes 0 initialClaims := by
                intro row impossible
                omega
              generalize claimsEquation :
                V5AcceptedEntryGenerated.v5_cu_probe.fri_checks.preparePointClaimsAux
                  4 0#usize bytes powers initialClaims = claimsResult
                at success
              cases claimsResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at success
              | div => simp [Bind.bind, Aeneas.Std.bind] at success
              | ok claimsResult =>
                cases claimsResult with
                | Err error =>
                  simp [Bind.bind, Aeneas.Std.bind] at success
                | Ok claims =>
                  have claimsExact : ∀ row : PointClaimRow,
                      entryClaimToK claims.val[row.val]! =
                        sourcePreparedPointClaim (entryClaimToK gamma)
                          (acceptedPointClaimTable bytes) row :=
                    preparePointClaimsAux_success_exact 4 gamma 0#usize bytes
                      powers initialClaims claims (by norm_num) bytesLength
                      powersCanonical powersExact initialClaimsCanonical
                      initialClaimsPrefix claimsEquation
                  have preparedEquality :
                      prepared = {
                        inner := {
                          claims := ⟨claims.val, by scalar_tac⟩
                          powers := ⟨powers.val, by scalar_tac⟩ }
                        c1_weight_limbs := c1WeightLimbs
                        c2_multipliers := c2Multipliers } := by
                    exact (core.result.Result.Ok.inj
                      (Result.ok.inj success)).symm
                  subst prepared
                  intro row
                  exact claimsExact row

/-! ## Accepted same-run snapshot -/

/-- The four prepared claims carried by one accepted same-run snapshot are
exactly the four claims deterministically decoded from that snapshot's
1,216-byte relation-claim field. -/
theorem accepted_snapshot_prepared_claims_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    PreparedClaimsExact snapshot.verifiedPrefix.gamma parsed.relation_claims
      snapshot.preparedClaims := by
  have prefixCanonical :=
    AspisV5AcceptedPrefixCanonical.accepted_prefix_gamma_and_inactive_canonical
      parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
      snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  exact prepare_v5_pcs_claims_success_exact snapshot.verifiedPrefix.gamma
    parsed.relation_claims snapshot.preparedClaims prefixCanonical.1
    snapshot.evidence.exactFriCalls.prepareClaimsSuccess

private theorem entry_canonical_to_relation_caller
    (value : SnapshotEntryQM31)
    (canonical : EntryCanonicalQM31 value) :
    AspisV5RelationGeneratedFieldProjection.CanonicalQM31
      (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller value) := by
  rcases AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller_components value
    with ⟨c0a, c0b, c1a, c1b⟩
  unfold AspisV5RelationGeneratedFieldProjection.CanonicalQM31
    AspisV5RelationGeneratedFieldProjection.CanonicalCM31
  rw [c0a, c0b, c1a, c1b]
  exact ⟨⟨canonical.1, canonical.2.1⟩,
    ⟨canonical.2.2.1, canonical.2.2.2⟩⟩

private theorem entry_prepared_claims_to_caller_canonical
    (claims : SnapshotEntryPreparedClaims)
    (canonical : PreparedClaimsCanonical claims) :
    AspisV5RelationPrepareCanonicalProof.CallerClaimsCanonical
      (AspisV5AcceptedRelationPreparedAdapter.preparedClaimsToCaller
        claims) := by
  unfold AspisV5RelationPrepareCanonicalProof.CallerClaimsCanonical
  change
    (claims.inner.claims.val.map
      AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller).length = 4 ∧
      ∀ (index : Nat)
        (bound : index < (claims.inner.claims.val.map
          AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller).length),
        AspisV5RelationGeneratedFieldProjection.CanonicalQM31
          (claims.inner.claims.val.map
            AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller)[index]
  constructor
  · simpa using canonical.1
  · intro index bound
    have sourceBound : index < claims.inner.claims.val.length := by
      simpa using bound
    have finBound : index < 4 := by
      rw [canonical.1] at sourceBound
      exact sourceBound
    have sourceCanonical := canonical.2 ⟨index, finBound⟩
    have bangEquality : claims.inner.claims.val[index]! =
        claims.inner.claims.val[index] := by
      apply List.getElem!_of_getElem?
      simp [sourceBound]
    rw [bangEquality] at sourceCanonical
    simpa [sourceBound] using entry_canonical_to_relation_caller
      claims.inner.claims.val[index] sourceCanonical

/-- The initial relation value consumed by one accepted same-run execution is
exactly the source initial claim formed from that execution's public prefix
and its deterministically decoded 76-entry claim table. -/
theorem accepted_snapshot_initial_relation_exact
    {accountData : Slice Std.U8}
    {parsed : SnapshotEntryParsed}
    {liveStatement : SnapshotEntryStatement}
    {statementDigest : Array Std.U8 32#usize}
    {acceptedValue : SnapshotEntryQM31}
    (snapshot : AcceptedSameRunRelationFriSnapshot accountData parsed
      liveStatement statementDigest acceptedValue) :
    AspisV5RelationLinkedFieldProjection.toMaintainedExact
        snapshot.relationTrace.calls.relation.relation_value =
      AspisV5RelationStressSourceBridge.sourceCallerInitialClaim
        (entryClaimToK snapshot.verifiedPrefix.inactive_claim)
        (entryClaimToK snapshot.verifiedPrefix.kappa)
        (entryClaimToK snapshot.verifiedPrefix.gamma)
        (acceptedPointClaimTable parsed.relation_claims) := by
  have prefixCanonical :=
    AspisV5AcceptedPrefixCanonical.accepted_prefix_gamma_and_inactive_canonical
      parsed liveStatement statementDigest
      V5AcceptedEntryGenerated.verify.sbf_hashv snapshot.verifiedPrefix
      snapshot.prefixTranscript snapshot.evidence.compositeCalls.prefixSuccess
  have preparedCanonical :=
    prepare_v5_pcs_claims_success_canonical snapshot.verifiedPrefix.gamma
      parsed.relation_claims snapshot.preparedClaims prefixCanonical.1
      snapshot.evidence.exactFriCalls.prepareClaimsSuccess
  have preparedExact := accepted_snapshot_prepared_claims_exact snapshot
  have callerClaimsCanonical :=
    entry_prepared_claims_to_caller_canonical snapshot.preparedClaims
      preparedCanonical
  have callerClaimsExact : ∀ row : PointClaimRow,
      AspisV5RelationLinkedFieldProjection.toMaintainedExact
          ((AspisV5AcceptedRelationPreparedAdapter.preparedClaimsToCaller
            snapshot.preparedClaims).inner.claims.val[row.val]'(by
              rw [callerClaimsCanonical.1]
              simpa [pointClaimRows] using row.isLt)) =
        AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
          (entryClaimToK snapshot.verifiedPrefix.gamma)
          (acceptedPointClaimTable parsed.relation_claims) row := by
    intro row
    have exactEntry := preparedExact row
    have sourceBound : row.val <
        snapshot.preparedClaims.inner.claims.val.length := by
      rw [preparedCanonical.1]
      simpa [pointClaimRows] using row.isLt
    have mappedEntry :
        ((AspisV5AcceptedRelationPreparedAdapter.preparedClaimsToCaller
          snapshot.preparedClaims).inner.claims.val[row.val]'(by
            rw [callerClaimsCanonical.1]
            simpa [pointClaimRows] using row.isLt)) =
          AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller
            snapshot.preparedClaims.inner.claims.val[row.val] := by
      change
        (snapshot.preparedClaims.inner.claims.val.map
          AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller)[row.val]'(by
            simpa using sourceBound) = _
      simp
    have bangEquality :
        snapshot.preparedClaims.inner.claims.val[row.val]! =
          snapshot.preparedClaims.inner.claims.val[row.val] := by
      apply List.getElem!_of_getElem?
      simp [sourceBound]
    calc
      AspisV5RelationLinkedFieldProjection.toMaintainedExact
          ((AspisV5AcceptedRelationPreparedAdapter.preparedClaimsToCaller
            snapshot.preparedClaims).inner.claims.val[row.val]'(by
              rw [callerClaimsCanonical.1]
              simpa [pointClaimRows] using row.isLt)) =
        entryClaimToK snapshot.preparedClaims.inner.claims.val[row.val]! := by
          rw [mappedEntry, bangEquality]
          exact
            (AspisV5AcceptedSameRunRelationFriSnapshot.entryToK_eq_relationCallerValue
              snapshot.preparedClaims.inner.claims.val[row.val]).symm
      _ = sourcePreparedPointClaim
          (entryClaimToK snapshot.verifiedPrefix.gamma)
          (acceptedPointClaimTable parsed.relation_claims) row := exactEntry
      _ = AspisV5RelationStressSourceBridge.sourcePreparedPointClaim
          (entryClaimToK snapshot.verifiedPrefix.gamma)
          (acceptedPointClaimTable parsed.relation_claims) row :=
        preparedPointClaim_eq_relationStress _ _ _
  have callerExact := caller_prepare_success_relation_value_exact
    (AspisV5AcceptedRelationPreparedAdapter.parsedToCaller parsed)
    (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller
      snapshot.verifiedPrefix.kappa)
    (AspisV5AcceptedRelationPreparedAdapter.qm31ToCaller
      snapshot.verifiedPrefix.inactive_claim)
    (AspisV5AcceptedRelationPreparedAdapter.preparedClaimsToCaller
      snapshot.preparedClaims)
    snapshot.relationTrace.calls.relation
    snapshot.relationTrace.calls.ignoredAlphas
    snapshot.relationTrace.calls.denseScale
    (entryClaimToK snapshot.verifiedPrefix.gamma)
    (acceptedPointClaimTable parsed.relation_claims)
    (entry_canonical_to_relation_caller snapshot.verifiedPrefix.kappa
      prefixCanonical.2.2)
    (entry_canonical_to_relation_caller snapshot.verifiedPrefix.inactive_claim
      prefixCanonical.2.1)
    callerClaimsCanonical callerClaimsExact
    snapshot.relationTrace.calls.prepareSuccess
  simpa [entryClaimToK,
    AspisV5AcceptedSameRunRelationFriSnapshot.entryToK_eq_relationCallerValue]
    using callerExact


end AspisV5AcceptedClaimTableExact
