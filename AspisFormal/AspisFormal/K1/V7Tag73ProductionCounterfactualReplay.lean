import AspisFormal.K1.V7Tag73PausedReplayAtInputSet
import AspisFormal.K1.V7Tag73VariablePrefixGammaSampler

/-!
# Executable pre-gamma production replay

This file gives the strongest machine-level counterfactual driver available
from the current pause semantics.  In the occurrence branch it executes the
literal output/advance duplex queries one at a time with `queryOracle`, stops
as soon as the deployed variable-prefix decoder returns a nonzero gamma, and
then resumes the frozen residual program under its original controller.

The possible twelve output/advance answers are data, not oracle programming:
cached answers are observed and checked, while fresh answers are installed by
ordinary queries and therefore retain `.fresh` origin.  No unused suffix query
is executed.  The no-target branch is the fixed, gamma-independent rerun
already constructed by the exhaustive operational scan.

There is deliberately no theorem here equating an arbitrary supplied duplex
tape with the production controller's future answers.  Constructing that tape
from one pre-gamma master-tape coordinate, and proving that ordinary queries
under the production controller return exactly those answers, is the remaining
source/controller coupling boundary.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ProductionCounterfactualReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73PausedReplayAtInputSet
open AspisK1.V7Tag73PausedRecursiveReplay
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Transcript data fixed immediately before the first possible gamma-output
query.  Later digests are the ordinary advance answers in the duplex tape. -/
structure GammaSamplerNuisance where
  initialDigest : Digest256

inductive GammaDuplexQueryKind where
  | output
  | advance
  deriving DecidableEq

/-- Every failure of the total driver is explicit.  In particular, a cached
answer which differs from the counterfactual tape is not silently replaced. -/
inductive CounterfactualReplayFailure where
  | expectedQuery (kind : GammaDuplexQueryKind)
  | queryInputMismatch (kind : GammaDuplexQueryKind)
  | samplerOutOfFuel (kind : GammaDuplexQueryKind)
  | oracleAbort (kind : GammaDuplexQueryKind) (reason : OracleAbort)
  | oracleAnswerMismatch (kind : GammaDuplexQueryKind)
  | samplerTapeExhausted
  | decodedValueInvalid
  | gammaMismatch
  | continuationOracleAbort (reason : OracleAbort)
  | continuationOutOfFuel
  deriving DecidableEq

/-- A normally returned counterfactual continuation.  `returnedGamma = none`
is exactly the exhaustive no-target branch. -/
structure CounterfactualResponse (Result : Type*) where
  value : Result
  run : MachineRun Result
  consumedBlocks : Nat
  returnedGamma : Option QM31Exact

/-- A controller used for one ordinary fresh query.  Cached queries do not
consult it, which is why their returned answer is checked separately. -/
def answerController (answer : ShaOutput) : AdaptiveController :=
  fun _ _ => .answer answer

def outputInput (digest : Digest256) : ShaInput :=
  bytes digest ++ [domSqueeze]

def advanceInput (digest : Digest256) : ShaInput :=
  bytes digest ++ [domAdvance]

/-- Execute one expected query of the paused residual program.  This uses the
ordinary lazy-oracle query interface and never programs the oracle table. -/
def executeExpectedQuery {Result : Type*}
    (kind : GammaDuplexQueryKind)
    (limits : OracleLimits) (actor : QueryActor)
    (expectedInput : ShaInput) (expectedAnswer : ShaOutput) :
    Nat -> OracleState -> OracleMachine Result ->
      Except CounterfactualReplayFailure
        (Nat × OracleState × OracleMachine Result)
  | 0, _, _ => .error (.samplerOutOfFuel kind)
  | fuel + 1, oracle, program =>
      match program with
      | .query actualInput next =>
          if actualInput = expectedInput then
            match queryOracle (answerController expectedAnswer) limits actor
                oracle actualInput with
            | .error reason => .error (.oracleAbort kind reason)
            | .ok (actualAnswer, nextOracle) =>
                if actualAnswer = expectedAnswer then
                  .ok (fuel, nextOracle, next actualAnswer)
                else
                  .error (.oracleAnswerMismatch kind)
          else
            .error (.queryInputMismatch kind)
      | .pure _ => .error (.expectedQuery kind)
      | .abort _ => .error (.expectedQuery kind)

/-- Convert a machine run into the total replay result. -/
def finishContinuation {Result : Type*}
    (consumedBlocks : Nat) (returnedGamma : Option QM31Exact)
    (run : MachineRun Result) :
    Except CounterfactualReplayFailure (CounterfactualResponse Result) :=
  match run.halt with
  | .returned value => .ok
      { value := value
        run := run
        consumedBlocks := consumedBlocks
        returnedGamma := returnedGamma }
  | .oracleAbort reason => .error (.continuationOracleAbort reason)
  | .outOfFuel => .error .continuationOutOfFuel

/-- Chronological output/advance pairs in the fixed possible tape. -/
def gammaDuplexPairs (tape : TotalGammaDuplexTape) :
    List (Digest256 × Digest256) :=
  (List.ofFn tape.1).zip (List.ofFn tape.2)

/-- Internal variable-prefix sampler loop.  `outputs` contains exactly the
output answers already queried.  The recursion stops at the first prefix for
which the deployed nonzero decoder succeeds. -/
def runGammaDuplexPrefix {Result : Type*}
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (gamma : NonzeroQM31Exact) :
    List (Digest256 × Digest256) -> Nat -> Nat -> Digest256 ->
      List Digest256 -> OracleState -> OracleMachine Result ->
      Except CounterfactualReplayFailure (CounterfactualResponse Result)
  | [], _, _, _, _, _, _ => .error .samplerTapeExhausted
  | (output, advanced) :: rest, consumed, fuel, digest, outputs, oracle,
      program =>
      match executeExpectedQuery .output limits actor (outputInput digest)
          output fuel oracle program with
      | .error failure => .error failure
      | .ok (afterOutputFuel, afterOutputOracle, afterOutputProgram) =>
          match executeExpectedQuery .advance limits actor
              (advanceInput digest) advanced afterOutputFuel afterOutputOracle
              afterOutputProgram with
          | .error failure => .error failure
          | .ok (afterAdvanceFuel, afterAdvanceOracle, afterAdvanceProgram) =>
              let nextOutputs := outputs ++ [output]
              match decodeNonzeroPrefix 3 nextOutputs with
              | none =>
                  runGammaDuplexPrefix controller limits actor gamma rest
                    (consumed + 1) afterAdvanceFuel advanced nextOutputs
                    afterAdvanceOracle afterAdvanceProgram
              | some decoded =>
                  match decodeTagQM31ExactLE decoded.value with
                  | none => .error .decodedValueInvalid
                  | some actualGamma =>
                      if actualGamma = gamma.1 then
                        finishContinuation (consumed + 1) none
                          (runMachine controller limits actor afterAdvanceFuel
                            afterAdvanceOracle afterAdvanceProgram)
                      else
                        .error .gammaMismatch

/-- Occurrence replay from a genuine frozen pre-query pause.  The initial
digest is nuisance fixed before gamma; all possible output/advance answers are
supplied as a total tape, but the execution reads only its stopping prefix. -/
def replayOccurrenceAtGamma {Result : Type*}
    (frozen : FrozenTargetPause Result)
    (nuisance : GammaSamplerNuisance)
    (tape : TotalGammaDuplexTape)
    (gamma : NonzeroQM31Exact) :
    Except CounterfactualReplayFailure (CounterfactualResponse Result) :=
  (runGammaDuplexPrefix frozen.controller frozen.limits frozen.actor gamma
    (gammaDuplexPairs tape) 0 frozen.remainingFuel nuisance.initialDigest []
    frozen.prefixOracle frozen.residualProgram).map fun response =>
      { response with returnedGamma := some gamma.1 }

/-- The exhaustive no-target replay is a constant counterfactual family.  It
does not inspect the sampler nuisance, tape, or supplied gamma. -/
def replayNoTargetAtGamma {Result : Type*}
    (frozen : FrozenNoTarget Result) :
    Except CounterfactualReplayFailure (CounterfactualResponse Result) :=
  finishContinuation 0 none (runFrozenNoTarget frozen)

/-- Total executable counterfactual driver for both occurrence and no-target
branches. -/
def replayAtGamma {Result : Type*}
    (frozen : FrozenPreGammaState Result)
    (nuisance : GammaSamplerNuisance)
    (tape : TotalGammaDuplexTape)
    (gamma : NonzeroQM31Exact) :
    Except CounterfactualReplayFailure (CounterfactualResponse Result) :=
  match frozen with
  | .occurrence state => replayOccurrenceAtGamma state nuisance tape gamma
  | .noTarget state => replayNoTargetAtGamma state

theorem replay_occurrence_returned_gamma_exact {Result : Type*}
    (frozen : FrozenTargetPause Result)
    (nuisance : GammaSamplerNuisance)
    (tape : TotalGammaDuplexTape)
    (gamma : NonzeroQM31Exact)
    (response : CounterfactualResponse Result)
    (run : replayOccurrenceAtGamma frozen nuisance tape gamma = .ok response) :
    response.returnedGamma = some gamma.1 := by
  unfold replayOccurrenceAtGamma at run
  cases replayRun : runGammaDuplexPrefix frozen.controller frozen.limits
      frozen.actor gamma (gammaDuplexPairs tape) 0 frozen.remainingFuel
      nuisance.initialDigest [] frozen.prefixOracle frozen.residualProgram with
  | error failure =>
      rw [replayRun] at run
      cases run
  | ok baseResponse =>
      rw [replayRun] at run
      cases run
      rfl

/-- The no-target branch is observationally independent of gamma and every
sampler coordinate. -/
theorem replay_at_gamma_no_target_constant {Result : Type*}
    (frozen : FrozenNoTarget Result)
    (leftNuisance rightNuisance : GammaSamplerNuisance)
    (leftTape rightTape : TotalGammaDuplexTape)
    (leftGamma rightGamma : NonzeroQM31Exact) :
    replayAtGamma (.noTarget frozen) leftNuisance leftTape leftGamma =
      replayAtGamma (.noTarget frozen) rightNuisance rightTape rightGamma := by
  rfl

/-- Freezing the actual absent segment and running the no-target branch
returns its literal production value. -/
theorem replay_no_target_segment_returns_actual {Result : Type*}
    {start : OracleMachine Result}
    (segment : OperationalReturnedSegment start)
    (nuisance : GammaSamplerNuisance)
    (tape : TotalGammaDuplexTape)
    (gamma : NonzeroQM31Exact) :
    ∃ response,
      replayAtGamma (.noTarget (freezeNoTargetSegment segment)) nuisance tape
          gamma = .ok response ∧
        response.value = segment.returnedValue ∧
        response.returnedGamma = none := by
  have returned := run_frozen_no_target_returns_actual segment
  refine ⟨
    { value := segment.returnedValue
      run := runFrozenNoTarget (freezeNoTargetSegment segment)
      consumedBlocks := 0
      returnedGamma := none }, ?_, rfl, rfl⟩
  simp only [replayAtGamma, replayNoTargetAtGamma, finishContinuation]
  rw [returned]

#print axioms replay_occurrence_returned_gamma_exact
#print axioms replay_at_gamma_no_target_constant
#print axioms replay_no_target_segment_returns_actual

end

end AspisK1.V7Tag73ProductionCounterfactualReplay
