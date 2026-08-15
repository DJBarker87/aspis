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

/-! ## Complete outer call and data flow

The definition below writes out the successful composite-verifier path using
the same generated declarations as the Aeneas translation.  The declarations
for the individual phases remain opaque at this layer.  Keeping them named is
useful: the arguments at each call show exactly which result from an earlier
phase is used by the next one.

In particular:

* relation replay receives the transcript returned by prefix verification;
* query derivation receives the transcript returned by relation replay and the
  prefix verifier's ten round challenges;
* FRI receives the query array and final polynomial returned together by query
  derivation, the decoded four fold challenges, and the prefix `gamma`;
* relation verification receives that same final polynomial and fold-challenge
  array, the prefix `kappa`, inactive claim, and round challenges, and the
  prepared claims returned by FRI.

This is a deterministic statement about call order and values.  It does not
assume that a hash behaves randomly and does not assign a probability to any
challenge. -/

def expectedCompositeCallDataflow
    (accountData : Slice Std.U8)
    (parsed : v5_cu_probe.ParsedProbeData)
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
    (digest : Array Std.U8 32#usize) :
    Result (core.result.Result aspis_core.field.QM31
      solana_program_error.ProgramError) := do
  let prefixResult ←
    v5_cu_probe.verify_v5_wire_prefix_sbf parsed statement digest
  let prefixBranch ← core.result.Result.Insts.CoreOpsTry.branch prefixResult
  match prefixBranch with
  | core.ops.control_flow.ControlFlow.Continue prefixValue =>
    let (verifiedPrefix, prefixTranscript) := prefixValue
    let terminalResult ←
      v5_cu_probe.verify_mode9_atomic_terminal_with_prefix parsed statement
        verifiedPrefix
    let terminalBranch ←
      core.result.Result.Insts.CoreOpsTry.branch terminalResult
    match terminalBranch with
    | core.ops.control_flow.ControlFlow.Continue terminal =>
      let replayResult ←
        v5_cu_probe.replay_real_v5_relation_rounds prefixTranscript parsed
      let replayBranch ← core.result.Result.Insts.CoreOpsTry.branch replayResult
      match replayBranch with
      | core.ops.control_flow.ControlFlow.Continue relationTranscript =>
        let queryResult ←
          v5_cu_probe.derive_v5_selected_good_queries_from_transcript
            relationTranscript parsed verifiedPrefix.round_challenges
        let queryBranch ← core.result.Result.Insts.CoreOpsTry.branch queryResult
        match queryBranch with
        | core.ops.control_flow.ControlFlow.Continue queryOutput =>
          let (finalPolynomial, queries) := queryOutput
          let alphaResult ← v5_cu_probe.decode_v5_fri_alphas parsed
          let alphaBranch ←
            core.result.Result.Insts.CoreOpsTry.branch alphaResult
          match alphaBranch with
          | core.ops.control_flow.ControlFlow.Continue alphas =>
            let friResult ←
              v5_cu_probe.verify_mode9_fri_phase parsed queries finalPolynomial
                alphas verifiedPrefix.gamma
            let friBranch ← core.result.Result.Insts.CoreOpsTry.branch friResult
            match friBranch with
            | core.ops.control_flow.ControlFlow.Continue friOutput =>
              let (friSum, preparedClaims) := friOutput
              let relationResult ←
                v5_cu_probe.verify_mode9_relation_phase parsed finalPolynomial
                  alphas verifiedPrefix.kappa verifiedPrefix.inactive_claim
                  verifiedPrefix.round_challenges preparedClaims
              let relationBranch ←
                core.result.Result.Insts.CoreOpsTry.branch relationResult
              match relationBranch with
              | core.ops.control_flow.ControlFlow.Continue relationClaim =>
                let accountLength := Slice.len accountData
                let _ ← core.hint.black_box accountLength
                let partialSum ← aspis_core.field.QM31.add friSum relationClaim
                let output ← aspis_core.field.QM31.add partialSum terminal.masked
                ok (core.result.Result.Ok output)
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  aspis_core.field.QM31 (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                aspis_core.field.QM31 (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              aspis_core.field.QM31 (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            aspis_core.field.QM31 (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.QM31 (core.convert.FromSame
          solana_program_error.ProgramError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        aspis_core.field.QM31 (core.convert.FromSame
        solana_program_error.ProgramError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      aspis_core.field.QM31 (core.convert.FromSame
      solana_program_error.ProgramError) residual

/-- The Aeneas-generated composite verifier has exactly the call order and
argument flow written above.  This equality is independent of the observation
implementations supplied for the opaque phase declarations. -/
theorem generated_composite_has_exact_call_dataflow
    (accountData : Slice Std.U8)
    (parsed : v5_cu_probe.ParsedProbeData)
    (statement : aspis_statement.atomic_statement.AtomicPaymentStatementV4)
    (digest : Array Std.U8 32#usize) :
    v5_cu_probe.verify_mode9_composite_with_live_statement
        accountData parsed statement digest =
      expectedCompositeCallDataflow accountData parsed statement digest := by
  rfl

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
#print axioms generated_composite_has_exact_call_dataflow
#print axioms generated_composite_forwards_prefix_kappa

end V5KappaCompositeCallerGeneratedProof
