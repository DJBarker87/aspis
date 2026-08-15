import V5KappaCompositeCaller.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
open V5KappaCompositeCallerGenerated

namespace V5KappaCompositeCallerGeneratedProof

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

theorem add_zero_left (value : aspis_core.field.QM31) :
    aspis_core.field.QM31.add zeroQm31 value = .ok value := by
  rfl

theorem add_zero_right (value : aspis_core.field.QM31) :
    aspis_core.field.QM31.add value zeroQm31 = .ok value := by
  rcases value with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  by_cases ha : a = 0#u32 <;>
  by_cases hb : b = 0#u32 <;>
  by_cases hc : c = 0#u32 <;>
  by_cases hd : d = 0#u32 <;>
    simp [aspis_core.field.QM31.add, qm31IsZero, zeroQm31,
      ha, hb, hc, hd]

/-- For every possible scalar returned by the prefix verifier, the Aeneas
translation of the composite caller supplies that same scalar to relation
verification. The replay derives this caller from the blob-pinned production
source using a checked patch that only names its existing fixed-hash prefix
call. The opaque relation observation returns its `kappa` argument, while all
unrelated phase observations return zero.

This proves only which Rust value is passed to the next check. It assumes no
distribution for `kappa` and no security property of SHA-256 or Poseidon2. -/
theorem generated_composite_forwards_prefix_kappa
    (accountData : Slice Std.U8)
    (parsed : v5_cu_probe.ParsedProbeData)
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
    (digest : Array Std.U8 32#usize) :
    v5_cu_probe.verify_mode9_composite_with_live_statement
        accountData parsed statement digest =
      .ok (.Ok parsed.gamma) := by
  simp [v5_cu_probe.verify_mode9_composite_with_live_statement,
    v5_cu_probe.verify_v5_wire_prefix_sbf,
    v5_cu_probe.verify_mode9_atomic_terminal_with_prefix,
    v5_cu_probe.replay_real_v5_relation_rounds,
    v5_cu_probe.derive_v5_selected_good_queries_from_transcript,
    v5_cu_probe.decode_v5_fri_alphas,
    v5_cu_probe.verify_mode9_fri_phase,
    v5_cu_probe.verify_mode9_relation_phase,
    core.hint.black_box, add_zero_left, add_zero_right]

#print axioms add_zero_left
#print axioms add_zero_right
#print axioms generated_composite_forwards_prefix_kappa

end V5KappaCompositeCallerGeneratedProof
