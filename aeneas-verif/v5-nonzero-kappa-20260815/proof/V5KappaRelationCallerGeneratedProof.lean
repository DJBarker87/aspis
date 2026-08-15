import V5KappaRelationCaller.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V5KappaRelationCallerGenerated

namespace V5KappaRelationCallerGeneratedProof

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

theorem unpack_pack_kappa (kappa : aspis_core.field.QM31) :
    unpackKappa (packKappa kappa) = kappa := by
  cases kappa with
  | mk c0 c1 => cases c0; cases c1; rfl

theorem qm31_ne_self (value : aspis_core.field.QM31) :
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne value value =
      .ok false := by
  cases value with
  | mk c0 c1 =>
      cases c0
      cases c1
      simp [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
        core.cmp.PartialEq.ne.default]

private theorem qm31_ne_default_self (value : aspis_core.field.QM31) :
    core.cmp.PartialEq.ne.default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq value value =
      .ok false := by
  simpa [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31] using
    qm31_ne_self value

private theorem allM_zip_qm31_self
    (values : List aspis_core.field.QM31) :
    List.allM
        (fun (pair : aspis_core.field.QM31 × aspis_core.field.QM31) => do
          let different ←
            aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne
              pair.1 pair.2
          ok (!different))
        (List.zip values values) = pure true := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [qm31_ne_default_self, ih]

theorem qm31_array_ne_self {length : Std.Usize}
    (values : Array aspis_core.field.QM31 length) :
    core.array.equality.PartialEqArray.ne
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 values values =
      .ok false := by
  rcases values with ⟨values, hlength⟩
  simp [core.array.equality.PartialEqArray.ne,
    core.array.equality.PartialEqArray.eq, allM_zip_qm31_self]

/-- Under an observation semantics for the two opaque downstream helpers, the
exact Aeneas-translated production caller returns every limb of the `kappa`
argument it was given. The adapter also rejects any relation variant other
than `FourClaimsCompact`, so this checks both the variant and unchanged scalar
forwarding at the source call site. -/
theorem generated_relation_phase_forwards_exact_kappa
    (parsed : v5_cu_probe.ParsedProbeData)
    (alphas : Array aspis_core.field.QM31 4#usize)
    (kappa inactiveClaim : aspis_core.field.QM31)
    (roundChallenges : Array aspis_core.field.QM31 10#usize)
    (preparedClaims : v5_cu_probe.fri_checks.V5PreparedPcsClaims) :
    v5_cu_probe.verify_mode9_relation_phase parsed alphas alphas kappa
        inactiveClaim roundChallenges preparedClaims =
      .ok (.Ok kappa) := by
  simp [v5_cu_probe.verify_mode9_relation_phase,
    v5_cu_probe.prepare_relation_base_with_kappa_prepared,
    v5_cu_probe.CompactBTerminalWeights.new,
    v5_relation_stress.verify_v5_relation_stress_with_additive,
    core.result.Result.map_err,
    qm31_array_ne_self, unpack_pack_kappa]

#print axioms unpack_pack_kappa
#print axioms qm31_ne_self
#print axioms qm31_array_ne_self
#print axioms generated_relation_phase_forwards_exact_kappa

end V5KappaRelationCallerGeneratedProof
