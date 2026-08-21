import V5FriCaller.Types

/-!
# Exact data flow through the production Merkle/FRI caller

Charon and Aeneas translate the two production caller functions in this
artifact.  Aeneas deliberately leaves the three large callees opaque.  This
module makes those callees explicit parameters and proves the accepted-path
data flow without assigning them arbitrary implementations.

The important fact is that the value returned by the Merkle call is passed
unchanged to the FRI call.  The roots, query array, proof slice, challenge,
fold challenges, and final polynomial are also the exact fields and arguments
read by the production caller.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriCallerParametric

open V5FriCaller

abbrev Parsed := v5_cu_probe.ParsedProbeData
abbrev Roots := v5_cu_probe.private_openings.V5PrivateOpeningRoots
abbrev Opening := v5_cu_probe.private_openings.VerifiedV5PrivateOpenings
abbrev OpeningError := v5_cu_probe.private_openings.V5PrivateOpeningError
abbrev Prepared := v5_cu_probe.fri_checks.V5PreparedPcsClaims
abbrev FriSink := v5_cu_probe.fri_checks.V5FriCheckSink
abbrev FriError := v5_cu_probe.fri_checks.V5FriCheckError
abbrev ProgramError := solana_program_error.ProgramError
abbrev QM31 := aspis_core.field.QM31

abbrev OpeningCall :=
  Roots -> Slice Std.U32 -> Slice Std.U8 ->
    Result (core.result.Result Opening OpeningError)

abbrev PrepareCall :=
  QM31 -> Slice Std.U8 -> Result (core.result.Result Prepared FriError)

abbrev FriCall :=
  Opening -> Prepared -> Array QM31 4#usize -> Array QM31 4#usize ->
    Result (core.result.Result FriSink FriError)

/-- Source-shaped form of `verify_v5_private_suffix`, with its one opaque
callee supplied explicitly. -/
def verifyPrivateSuffixWith (openingsCall : OpeningCall)
    (parsed : Parsed) (queries : Array Std.U32 18#usize) :
    Result (core.result.Result Opening ProgramError) := do
  let querySlice <- lift (Array.to_slice queries)
  let openingResult <- openingsCall parsed.v5_private_roots querySlice
    parsed.v5_private_proof
  match openingResult with
  | .Err _ => ok (.Err
      V5FriCaller.solana_program_error.ProgramError.InvalidAccountData)
  | .Ok opening =>
      if opening.c1.records = parsed.candidate_c1 then
        if opening.c2.records = parsed.c2 then
          ok (.Ok opening)
        else
          ok (.Err
            V5FriCaller.solana_program_error.ProgramError.InvalidAccountData)
      else
        ok (.Err
          V5FriCaller.solana_program_error.ProgramError.InvalidAccountData)

/-- Source-shaped form of `verify_mode9_fri_phase`, with its three callees
supplied explicitly. -/
def verifyFriPhaseWith (openingsCall : OpeningCall)
    (prepareCall : PrepareCall) (friCall : FriCall)
    (parsed : Parsed) (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array QM31 4#usize)
    (alphas : Array QM31 4#usize) (gamma : QM31) :
    Result (core.result.Result (QM31 × Prepared) ProgramError) := do
  let privateResult <- verifyPrivateSuffixWith openingsCall parsed queries
  match privateResult with
  | .Err error => ok (.Err error)
  | .Ok opening =>
      let preparedResult <- prepareCall gamma parsed.relation_claims
      match preparedResult with
      | .Err _ => ok (.Err
          V5FriCaller.solana_program_error.ProgramError.InvalidAccountData)
      | .Ok prepared =>
          let friResult <- friCall opening prepared alphas finalPolynomial
          match friResult with
          | .Err _ => ok (.Err
              V5FriCaller.solana_program_error.ProgramError.InvalidAccountData)
          | .Ok sink => ok (.Ok (sink.folded_layer0_sum, prepared))

/-- Everything observed on the successful production path.  In particular,
`fri_run` mentions exactly the same `opening` produced by `opening_run`; no
second parse or reconstructed opening is permitted by this proposition. -/
structure AcceptedCallerTrace (openingsCall : OpeningCall)
    (prepareCall : PrepareCall) (friCall : FriCall)
    (parsed : Parsed) (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array QM31 4#usize)
    (alphas : Array QM31 4#usize) (gamma : QM31)
    (output : QM31 × Prepared) : Type where
  opening : Opening
  prepared : Prepared
  sink : FriSink
  opening_run : openingsCall parsed.v5_private_roots (Array.to_slice queries)
    parsed.v5_private_proof = .ok (.Ok opening)
  c1_records_equal : opening.c1.records = parsed.candidate_c1
  c2_records_equal : opening.c2.records = parsed.c2
  prepare_run : prepareCall gamma parsed.relation_claims =
    .ok (.Ok prepared)
  fri_run : friCall opening prepared alphas finalPolynomial =
    .ok (.Ok sink)
  output_equal : output = (sink.folded_layer0_sum, prepared)

/-- Successful execution of the exact source-shaped caller yields the full
call trace, including identity of the Merkle return value consumed by FRI. -/
theorem accepted_fri_phase_yields_exact_call_trace
    (openingsCall : OpeningCall) (prepareCall : PrepareCall)
    (friCall : FriCall) (parsed : Parsed)
    (queries : Array Std.U32 18#usize)
    (finalPolynomial : Array QM31 4#usize)
    (alphas : Array QM31 4#usize) (gamma : QM31)
    (output : QM31 × Prepared)
    (run : verifyFriPhaseWith openingsCall prepareCall friCall parsed queries
      finalPolynomial alphas gamma = .ok (.Ok output)) :
    Nonempty (AcceptedCallerTrace openingsCall prepareCall friCall parsed
      queries finalPolynomial alphas gamma output) := by
  unfold verifyFriPhaseWith verifyPrivateSuffixWith at run
  simp only [Std.lift, bind_tc_ok] at run
  cases hopen : openingsCall parsed.v5_private_roots (Array.to_slice queries)
        parsed.v5_private_proof with
  | fail error => simp [hopen] at run
  | div => simp [hopen] at run
  | ok openingResult =>
    simp only [hopen, bind_tc_ok] at run
    cases openingResult with
    | Err openingError => simp at run
    | Ok opening =>
      by_cases hc1 : opening.c1.records = parsed.candidate_c1
      · simp only [hc1, if_true, bind_tc_ok] at run
        by_cases hc2 : opening.c2.records = parsed.c2
        · simp only [hc2, if_true, bind_tc_ok] at run
          cases hprepare : prepareCall gamma parsed.relation_claims with
          | fail error => simp [hprepare] at run
          | div => simp [hprepare] at run
          | ok preparedResult =>
            simp only [hprepare, bind_tc_ok] at run
            cases preparedResult with
            | Err prepareError => simp at run
            | Ok prepared =>
              cases hfri : friCall opening prepared alphas
                  finalPolynomial with
              | fail error => simp [hfri] at run
              | div => simp [hfri] at run
              | ok friResult =>
                simp only [hfri, bind_tc_ok] at run
                cases friResult with
                | Err friError => simp at run
                | Ok sink =>
                  have outputEq :
                      output = (sink.folded_layer0_sum, prepared) := by
                    simpa using (Result.ok.inj run).symm
                  exact ⟨{
                    opening := opening
                    prepared := prepared
                    sink := sink
                    opening_run := hopen
                    c1_records_equal := hc1
                    c2_records_equal := hc2
                    prepare_run := hprepare
                    fri_run := hfri
                    output_equal := outputEq
                  }⟩
        · simp [hc2] at run
      · simp [hc1] at run

#print axioms accepted_fri_phase_yields_exact_call_trace

end AspisV5FriCallerParametric
