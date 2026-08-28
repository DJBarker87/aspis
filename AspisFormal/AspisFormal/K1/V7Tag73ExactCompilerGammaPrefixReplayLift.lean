import AspisFormal.K1.V7Tag73ExactCompilerGammaCachedCoordinate
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal

/-!
# Lift exact coordinate steps through the gamma-prefix driver

This file isolates the induction needed after a one-coordinate exact compiler
step is available.  The induction assumes only that each final-table lookup
can be consumed while preserving `ExactCompilerRootGammaCursorAligned`; it
does not assume a replay/run conclusion.  Alignment itself reconstructs the
literal production run by the existing native-prefix factorization.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73SemanticRoundReplay
open AspisV5ComponentCQM31TowerExact

noncomputable section

universe u

/-! ## Any aligned cursor reconstructs the production root run -/

/-- The answer prefix encoded by an aligned cursor and its retained suffix is
the literal exact compiler master tape. -/
theorem exact_compiler_root_gamma_alignment_answers_factor
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state) :
    freshAnswerTapeToList sample.2 =
      aligned.consumed.map Prod.snd ++ state.remainingAnswers := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  calc
    freshAnswerTapeToList sample.2 =
        prefixes.adversary.freshQueries.map Prod.snd ++
          prefixes.adversary.remaining := prefixes.adversary.availableExact
    _ = prefixes.adversary.freshQueries.map Prod.snd ++
        (prefixes.verifier.freshQueries.map Prod.snd ++
          prefixes.verifier.remaining) := congrArg
            (List.append (prefixes.adversary.freshQueries.map Prod.snd))
            prefixes.verifier.availableExact
    _ = (prefixes.adversary.freshQueries ++
        prefixes.verifier.freshQueries).map Prod.snd ++
          prefixes.verifier.remaining := by
      rw [List.map_append, List.append_assoc]
    _ = (aligned.consumed ++ aligned.future).map Prod.snd ++
          prefixes.verifier.remaining := by rw [aligned.rootSplit]
    _ = aligned.consumed.map Prod.snd ++
        (aligned.future.map Prod.snd ++ prefixes.verifier.remaining) := by
      rw [List.map_append, List.append_assoc]
    _ = aligned.consumed.map Prod.snd ++ state.remainingAnswers := by
      rw [aligned.answersExact]

/-- Appending the run from any aligned live gamma cursor to its retained trace
prefix gives exactly the production scheduler run from the compiler root. -/
theorem exact_compiler_root_gamma_alignment_reconstructs_run
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state) :
    let tail := runSchedulerNativeListRun transitionFuel state.cursor
      state.remainingAnswers
    ({ terminal := tail.terminal
       trace := state.tracePrefix ++ tail.trace } :
      SchedulerNativeRun
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)) =
      runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) := by
  obtain ⟨records, finalCursor, traversal⟩ :=
    scheduler_native_prefix_traversal_exists transitionFuel
      (exactPlainRomCursor configuration sample.1)
      (aligned.consumed.map Prod.snd)
  have recordsExact :=
    scheduler_native_prefix_traversal_records_exact traversal
  have cursorExact :=
    scheduler_native_prefix_traversal_cursor_exact traversal
  have answersExact :=
    exact_compiler_root_gamma_alignment_answers_factor input state aligned
  have traceFactor :=
    scheduler_native_prefix_traversal_trace_factorization traversal
      state.remainingAnswers
  have terminalFactor :=
    scheduler_native_prefix_traversal_terminal_factorization traversal
      state.remainingAnswers
  rw [← aligned.cursorExact] at cursorExact
  rw [← aligned.traceExact] at recordsExact
  subst finalCursor
  subst records
  rw [← answersExact] at traceFactor terminalFactor
  change
    ({ terminal :=
        (runSchedulerNativeListRun transitionFuel state.cursor
          state.remainingAnswers).terminal
       trace := state.tracePrefix ++
        (runSchedulerNativeListRun transitionFuel state.cursor
          state.remainingAnswers).trace } :
      SchedulerNativeRun
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)) =
    { terminal :=
        (runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2)).terminal
      trace :=
        (runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2)).trace }
  rw [SchedulerNativeRun.mk.injEq]
  exact ⟨terminalFactor.symm, traceFactor.symm⟩

/-! ## Minimal coordinate-step interface and prefix induction -/

/-- The exact local fact needed by the recursive driver.  It is deliberately
one-coordinate and final-table sourced; it contains no replay equality. -/
def ExactCompilerGammaCoordinateStep
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Prop :=
  ∀ (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state),
    tableLookup (exactOperationalTable input) expectedInput =
        some expectedAnswer →
      ∃ nextState,
        consumeSchedulerNativeGammaCoordinate transitionFuel kind expectedInput
            expectedAnswer state = .ok nextState ∧
        Nonempty (ExactCompilerRootGammaCursorAligned input nextState)

/-- The exact coordinate chain is sufficient to lift a local coordinate step
through every recursive output/advance pair.  Whenever the deployed decoder
returns, the response run is the literal production root run. -/
theorem run_scheduler_native_gamma_prefix_actual_chain_reconstructs
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∀ {digest : Digest256} {outputs advances : List Digest256},
      GammaTableCoordinateChain (exactOperationalTable input) digest outputs
        advances →
      ∀ (consumedBlocks : Nat) (priorOutputs : List Digest256)
        (state : SchedulerNativeGammaCursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result))
        (aligned : ExactCompilerRootGammaCursorAligned input state)
        (decoded : DecodedSchedulerNativeGammaResponse
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)),
        runSchedulerNativeGammaPrefix transitionFuel (outputs.zip advances)
            consumedBlocks digest priorOutputs state = .ok decoded →
          decoded.response.run =
            runSchedulerNativeListRun transitionFuel
              (exactPlainRomCursor configuration sample.1)
              (freshAnswerTapeToList sample.2) := by
  intro digest outputs advances chain
  induction chain with
  | done digest =>
      intro consumedBlocks priorOutputs state aligned decoded run
      simp [runSchedulerNativeGammaPrefix] at run
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      intro consumedBlocks priorOutputs state aligned decoded run
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (gammaOutputInput digest) output state aligned
          outputLookup
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (gammaAdvanceInput digest) advanced afterOutput
          outputAligned advanceLookup
      simp only [List.zip_cons_cons, runSchedulerNativeGammaPrefix] at run
      rw [outputRun] at run
      simp only at run
      rw [advanceRun] at run
      simp only at run
      split at run
      next stopped decodedRun =>
        split at run
        next value valueRun =>
          cases run
        next valueRun =>
          cases run
          exact exact_compiler_root_gamma_alignment_reconstructs_run input
            afterAdvance advanceAligned
      next decodedRun =>
        exact ih (consumedBlocks + 1)
          (priorOutputs ++ [output]) afterAdvance advanceAligned decoded run

/-- If the ordinary decoder is known to stop within the exact coordinate
chain, the coordinate-step invariant constructs a successful executable
prefix run.  The only decoder premise is the literal offline prefix equation;
no scheduler replay equation is accepted. -/
theorem run_scheduler_native_gamma_prefix_actual_chain_succeeds
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∀ {digest : Digest256} {outputs advances : List Digest256},
      GammaTableCoordinateChain (exactOperationalTable input) digest outputs
          advances →
      ∀ (consumedBlocks : Nat) (priorOutputs : List Digest256)
        (state : SchedulerNativeGammaCursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result))
        (aligned : ExactCompilerRootGammaCursorAligned input state)
        (finalDecoded : OrdinaryPrefixDecode) (value : QM31Exact),
        decodeNonzeroPrefix 3 priorOutputs = none →
        decodeNonzeroPrefix 3 (priorOutputs ++ outputs) = some finalDecoded →
        decodeTagQM31ExactLE finalDecoded.value = some value →
        ∃ decoded : DecodedSchedulerNativeGammaResponse
            (SchedulerNativePlainRomResult TapeIdentity Statement
              Tag73K12ParsedProof Payload Result),
          runSchedulerNativeGammaPrefix transitionFuel (outputs.zip advances)
              consumedBlocks digest priorOutputs state = .ok decoded ∧
          decoded.response.run =
            runSchedulerNativeListRun transitionFuel
              (exactPlainRomCursor configuration sample.1)
              (freshAnswerTapeToList sample.2) ∧
          decoded.value = value := by
  intro digest outputs advances chain
  induction chain with
  | done digest =>
      intro consumedBlocks priorOutputs state aligned finalDecoded value
        priorNone fullRun valueRun
      simp only [List.append_nil] at fullRun
      rw [priorNone] at fullRun
      contradiction
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      intro consumedBlocks priorOutputs state aligned finalDecoded value
        priorNone fullRun valueRun
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (gammaOutputInput digest) output state aligned
          outputLookup
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (gammaAdvanceInput digest) advanced afterOutput
          outputAligned advanceLookup
      let nextOutputs := priorOutputs ++ [output]
      cases currentRun : decodeNonzeroPrefix 3 nextOutputs with
      | none =>
          simp only [nextOutputs] at currentRun
          have fullRun' : decodeNonzeroPrefix 3 (nextOutputs ++ outputs) =
              some finalDecoded := by
            simpa [nextOutputs, List.append_assoc] using fullRun
          obtain ⟨decoded, tailRun, reconstructed, decodedValue⟩ :=
            ih (consumedBlocks + 1) nextOutputs afterAdvance advanceAligned
              finalDecoded value currentRun fullRun' valueRun
          refine ⟨decoded, ?_, reconstructed, decodedValue⟩
          simp only [List.zip_cons_cons, runSchedulerNativeGammaPrefix]
          rw [outputRun]
          simp only
          rw [advanceRun]
          simp only
          rw [currentRun]
          exact tailRun
      | some currentDecoded =>
          simp only [nextOutputs] at currentRun
          have extended := decodeNonzeroPrefix_append_of_some 3 nextOutputs
            outputs currentDecoded currentRun
          have decodedExact :
              appendOrdinaryRemaining currentDecoded outputs = finalDecoded := by
            apply Option.some.inj
            exact extended.symm.trans (by
              simpa [nextOutputs, List.append_assoc] using fullRun)
          have currentValueExact :
              decodeTagQM31ExactLE currentDecoded.value = some value := by
            rw [show currentDecoded.value = finalDecoded.value by
              rw [← decodedExact]
              rfl]
            exact valueRun
          simp only [List.zip_cons_cons, runSchedulerNativeGammaPrefix]
          rw [outputRun]
          simp only
          rw [advanceRun]
          simp only
          rw [currentRun]
          simp only
          split
          next invalidRun =>
            rw [currentValueExact] at invalidRun
            contradiction
          next validRun =>
            refine ⟨_, rfl, ?_, ?_⟩
            · exact exact_compiler_root_gamma_alignment_reconstructs_run input
                afterAdvance advanceAligned
            · exact Option.some.inj (validRun.symm.trans currentValueExact)

/-- The same local coordinate-step invariant lifts through the production
entry point whose first output request has already been exposed by the exact
root scanner.  The scanner equality, rather than a replay equality, identifies
the directly installed first-output state with the ordinary coordinate step. -/
theorem run_scheduler_native_gamma_from_first_pause_actual_chain_reconstructs
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    {initialDigest output advanced : Digest256}
    {outputs advances : List Digest256}
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      initialDigest (output :: outputs) (advanced :: advances))
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) (gammaOutputInput initialDigest))
    (paused : exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
      .paused firstPause)
    (decoded : DecodedSchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (run : runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
      ((output, advanced) :: outputs.zip advances) = .ok decoded) :
    decoded.response.run =
      runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) := by
  cases chain with
  | next outputLookup advanceLookup tail =>
      let initial := exactCompilerInitialGammaCursor input
      let directAfterOutput : SchedulerNativeGammaCursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result) :=
        { cursor := firstPause.resumeCursorWith output
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input output
          tracePrefix := initial.tracePrefix ++ firstPause.consumedTrace ++
            [machineFreshRecord firstPause output] }
      have scanned : scanSchedulerNativeToInput transitionFuel
          (gammaOutputInput initialDigest) initial.cursor
          initial.remainingAnswers = .paused firstPause := by
        exact paused
      have missing : lookupEntry initial.oracle
          (gammaOutputInput initialDigest) = none := by
        rfl
      have directOutputRun :
          consumeSchedulerNativeGammaCoordinate transitionFuel .output
              (gammaOutputInput initialDigest) output initial =
            .ok directAfterOutput := by
        simpa [directAfterOutput, initial, List.append_assoc] using
          consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
            transitionFuel .output (gammaOutputInput initialDigest) output
              initial missing firstPause scanned
      obtain ⟨afterOutput, outputRun, ⟨afterOutputAligned⟩⟩ :=
        coordinateStep .output (gammaOutputInput initialDigest) output initial
          (exactCompilerInitialGammaCursorAlignment input) outputLookup
      have afterOutputExact : afterOutput = directAfterOutput := by
        rw [directOutputRun] at outputRun
        exact Except.ok.inj outputRun.symm
      subst afterOutput
      obtain ⟨afterAdvance, advanceRun, ⟨afterAdvanceAligned⟩⟩ :=
        coordinateStep .advance (gammaAdvanceInput initialDigest) advanced
          directAfterOutput afterOutputAligned advanceLookup
      have advanceRunDirect :
          consumeSchedulerNativeGammaCoordinate transitionFuel .advance
              (gammaAdvanceInput initialDigest) advanced
              { cursor := firstPause.resumeCursorWith output
                remainingAnswers := firstPause.remainingAnswers
                oracle := freshQueryState firstPause.actor
                  firstPause.requestState firstPause.input output
                tracePrefix := firstPause.consumedTrace ++
                  [machineFreshRecord firstPause output] } =
            .ok afterAdvance := by
        simpa [directAfterOutput, initial, exactCompilerInitialGammaCursor,
          List.append_assoc] using advanceRun
      simp only [runSchedulerNativeGammaFromFirstPause] at run
      rw [advanceRunDirect] at run
      simp only at run
      split at run
      next stopped decodedRun =>
        split at run
        next valueRun =>
          cases run
        next valueRun =>
          cases run
          exact exact_compiler_root_gamma_alignment_reconstructs_run input
            afterAdvance afterAdvanceAligned
      next decodedRun =>
        exact run_scheduler_native_gamma_prefix_actual_chain_reconstructs input
          coordinateStep tail 1 [output] afterAdvance afterAdvanceAligned decoded
            run

/-- A literal successful decoder equation on the consumed coordinates builds
the successful production first-pause replay itself.  In particular, replay
success is a conclusion rather than a caller-supplied equality. -/
theorem run_scheduler_native_gamma_from_first_pause_actual_chain_succeeds
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    {initialDigest output advanced : Digest256}
    {outputs advances : List Digest256}
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      initialDigest (output :: outputs) (advanced :: advances))
    (finalDecoded : OrdinaryPrefixDecode) (value : QM31Exact)
    (prefixRun : decodeNonzeroPrefix 3 (output :: outputs) =
      some finalDecoded)
    (valueRun : decodeTagQM31ExactLE finalDecoded.value = some value)
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) (gammaOutputInput initialDigest))
    (paused : exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
      .paused firstPause) :
    ∃ decoded : DecodedSchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result),
      runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
          ((output, advanced) :: outputs.zip advances) = .ok decoded ∧
      decoded.response.run =
        runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) ∧
      decoded.value = value := by
  let initial := exactCompilerInitialGammaCursor input
  let directAfterOutput : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) :=
    { cursor := firstPause.resumeCursorWith output
      remainingAnswers := firstPause.remainingAnswers
      oracle := freshQueryState firstPause.actor firstPause.requestState
        firstPause.input output
      tracePrefix := initial.tracePrefix ++ firstPause.consumedTrace ++
        [machineFreshRecord firstPause output] }
  have scanned : scanSchedulerNativeToInput transitionFuel
      (gammaOutputInput initialDigest) initial.cursor initial.remainingAnswers =
        .paused firstPause := by
    exact paused
  have missing : lookupEntry initial.oracle (gammaOutputInput initialDigest) =
      none := by
    rfl
  have directOutputRun :
      consumeSchedulerNativeGammaCoordinate transitionFuel .output
          (gammaOutputInput initialDigest) output initial =
        .ok directAfterOutput := by
    simpa [directAfterOutput, initial, List.append_assoc] using
      consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
        transitionFuel .output (gammaOutputInput initialDigest) output initial
          missing firstPause scanned
  have emptyPrefixNone : decodeNonzeroPrefix 3 [] = none := by
    cases emptyRun : decodeNonzeroPrefix 3 [] with
    | none => rfl
    | some decoded =>
        obtain ⟨discarded, suffix, split, ordinary⟩ :=
          decodeNonzeroPrefix_ordinary_suffix 3 [] decoded emptyRun
        have suffixEmpty : suffix = [] :=
          (List.append_eq_nil_iff.mp split.symm).2
        exact False.elim
          ((decodeOrdinaryPrefix_blocks_nonempty suffix decoded ordinary)
            suffixEmpty)
  obtain ⟨decoded, prefixDriverRun, reconstructed, decodedValue⟩ :=
    run_scheduler_native_gamma_prefix_actual_chain_succeeds input coordinateStep
      chain 0 [] initial (exactCompilerInitialGammaCursorAlignment input)
        finalDecoded value emptyPrefixNone (by simpa using prefixRun)
          valueRun
  refine ⟨decoded, ?_, reconstructed, decodedValue⟩
  have driversExact :
      runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
          ((output, advanced) :: outputs.zip advances) =
        runSchedulerNativeGammaPrefix transitionFuel
          ((output, advanced) :: outputs.zip advances) 0 initialDigest []
            initial := by
    simp only [runSchedulerNativeGammaFromFirstPause,
      runSchedulerNativeGammaPrefix]
    rw [directOutputRun]
    rfl
  rw [driversExact]
  exact prefixDriverRun

/-! ## Unread duplex suffixes are inert for the online scheduler driver -/

/-- Once the recursive scheduler-native gamma driver has returned, appending
unread duplex pairs cannot affect its result. -/
theorem run_scheduler_native_gamma_prefix_append_of_ok
    {globalOracleCalls : Nat} {ReplayResult : Type u}
    (transitionFuel : Nat) (pairs suffix : List (Digest256 × Digest256))
    (consumedBlocks : Nat) (digest : Digest256)
    (outputs : List Digest256)
    (state : SchedulerNativeGammaCursor globalOracleCalls ReplayResult)
    (decoded : DecodedSchedulerNativeGammaResponse ReplayResult)
    (run : runSchedulerNativeGammaPrefix transitionFuel pairs consumedBlocks
      digest outputs state = .ok decoded) :
    runSchedulerNativeGammaPrefix transitionFuel (pairs ++ suffix)
      consumedBlocks digest outputs state = .ok decoded := by
  induction pairs generalizing consumedBlocks digest outputs state with
  | nil => simp [runSchedulerNativeGammaPrefix] at run
  | cons pair rest ih =>
      obtain ⟨output, advanced⟩ := pair
      change runSchedulerNativeGammaPrefix transitionFuel
        ((output, advanced) :: (rest ++ suffix)) consumedBlocks digest outputs
          state = .ok decoded
      simp only [runSchedulerNativeGammaPrefix] at run ⊢
      cases outputRun : consumeSchedulerNativeGammaCoordinate transitionFuel
          .output (gammaOutputInput digest) output state with
      | error failure => simp [outputRun] at run
      | ok afterOutput =>
          simp only [outputRun] at run
          simp only at ⊢
          cases advanceRun : consumeSchedulerNativeGammaCoordinate transitionFuel
              .advance (gammaAdvanceInput digest) advanced afterOutput with
          | error failure => simp [advanceRun] at run
          | ok afterAdvance =>
              simp only [advanceRun] at run
              simp only at ⊢
              split at *
              next stopped decodedRun =>
                split at *
                next valueRun => cases run
                next valueRun => exact run
              next decodedRun =>
                exact ih (consumedBlocks + 1) advanced
                  (outputs ++ [output]) afterAdvance run

/-- The production first-pause entry point inherits the same unread-suffix
irrelevance from its recursive tail. -/
theorem run_scheduler_native_gamma_from_first_pause_append_of_ok
    {globalOracleCalls : Nat} {ReplayResult : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls ReplayResult
      (gammaOutputInput initialDigest))
    (pairs suffix : List (Digest256 × Digest256))
    (decoded : DecodedSchedulerNativeGammaResponse ReplayResult)
    (run : runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
      pairs = .ok decoded) :
    runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
      (pairs ++ suffix) = .ok decoded := by
  cases pairs with
  | nil => simp [runSchedulerNativeGammaFromFirstPause] at run
  | cons pair rest =>
      obtain ⟨output, advanced⟩ := pair
      change runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
        ((output, advanced) :: (rest ++ suffix)) = .ok decoded
      simp only [runSchedulerNativeGammaFromFirstPause] at run ⊢
      cases advanceRun : consumeSchedulerNativeGammaCoordinate transitionFuel
          .advance (gammaAdvanceInput initialDigest) advanced
          { cursor := firstPause.resumeCursorWith output
            remainingAnswers := firstPause.remainingAnswers
            oracle := freshQueryState firstPause.actor firstPause.requestState
              firstPause.input output
            tracePrefix := firstPause.consumedTrace ++
              [machineFreshRecord firstPause output] } with
      | error failure => simp [advanceRun] at run
      | ok afterAdvance =>
          simp only [advanceRun] at run
          simp only at ⊢
          split at *
          next stopped decodedRun =>
            split at *
            next valueRun => cases run
            next valueRun => exact run
          next decodedRun =>
            exact run_scheduler_native_gamma_prefix_append_of_ok
              transitionFuel rest suffix 1 advanced [output] afterAdvance
                decoded run

/-- Taking a prefix commutes with zipping two lists. -/
theorem take_zip_eq_zip_take {Left Right : Type}
    (count : Nat) (left : List Left) (right : List Right) :
    (left.zip right).take count = (left.take count).zip (right.take count) := by
  induction count generalizing left right with
  | zero => simp
  | succ count ih =>
      cases left <;> cases right <;> simp [ih]

/-- The output/advance prefix equations exported by the compiler construction
combine to the literal consumed duplex-pair prefix. -/
theorem gamma_duplex_pairs_consumed_prefix
    (tape : TotalGammaDuplexTape) (outputs advances : List Digest256)
    (lengthExact : advances.length = outputs.length)
    (outputPrefix : (gammaOutputBlocks tape).take outputs.length = outputs)
    (advancePrefix : (List.ofFn tape.2).take advances.length = advances) :
    (gammaDuplexPairs tape).take outputs.length = outputs.zip advances := by
  change (List.ofFn tape.1).take outputs.length = outputs at outputPrefix
  rw [gammaDuplexPairs, take_zip_eq_zip_take, outputPrefix]
  have advancePrefix' : (List.ofFn tape.2).take outputs.length = advances := by
    rw [← lengthExact]
    exact advancePrefix
  rw [advancePrefix']

/-! ## Actual compiler padded-tape replay closure -/

/-- The strict compiler construction, a source-derived first pause, and the
local exact coordinate step jointly construct a successful scheduler replay
on the full padded `SuccessfulGammaPrefixTape`.  Only the consumed prefix is
executed; the remaining duplex pairs are eliminated by the unread-suffix
theorem above. -/
theorem exact_compiler_actual_gamma_replay_closure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (firstPause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result) (gammaOutputInput initialDigest))
      (decoded : DecodedSchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
          .paused firstPause ∧
      runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
          (gammaDuplexPairs flat.1) = .ok decoded ∧
      decoded.response.run =
          runSchedulerNativeListRun transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (freshAnswerTapeToList sample.2) ∧
      decoded.value = exactOperationalChallenge input .gamma := by
  obtain ⟨beforeGamma, afterBlocks, allOutputs, allAdvances, flat,
      paddedDecoded, consumedDecoded, consumedValue, outputsLength,
      advancesLength, coordinates, callsExact, outputPrefix, advancePrefix,
      consumedPrefixRun, consumedValueRun, consumedDecodedValue, flatRun,
      paddedDecodedValue, routedValue⟩ :=
    exact_compiler_constructs_successful_gamma_prefix_coordinates input
  have outputsPositive : 0 < allOutputs.length := by
    rw [outputsLength]
    exact ((exactOperationalTape input).messages.challengeUse
      .gamma).consumesBlock
  have consumedValueOperational :
      consumedValue = exactOperationalChallenge input .gamma := by
    simp [exactOperationalChallenge, exactChallengeValue,
      ← consumedDecodedValue, consumedValueRun]
  cases allOutputs with
  | nil => simp at outputsPositive
  | cons output outputs =>
      cases coordinates with
      | @next initialDigest output advanced outputs advances outputLookup
          advanceLookup tail =>
          obtain ⟨firstPause, paused⟩ :=
            exact_compiler_final_lookup_has_full_target_pause input
              (gammaOutputInput beforeGamma.digest) output outputLookup
          obtain ⟨decoded, consumedDriverRun, reconstructed,
              decodedValue⟩ :=
            run_scheduler_native_gamma_from_first_pause_actual_chain_succeeds
              input coordinateStep (.next outputLookup advanceLookup tail)
                consumedDecoded consumedValue consumedPrefixRun consumedValueRun
                  firstPause paused
          have pairPrefix := gamma_duplex_pairs_consumed_prefix flat.1
            (output :: outputs) (advanced :: advances) advancesLength
              outputPrefix advancePrefix
          let unreadPairs := (gammaDuplexPairs flat.1).drop
            (output :: outputs).length
          have pairSplit : gammaDuplexPairs flat.1 =
              ((output, advanced) :: outputs.zip advances) ++ unreadPairs := by
            calc
              gammaDuplexPairs flat.1 =
                  (gammaDuplexPairs flat.1).take (output :: outputs).length ++
                    unreadPairs :=
                (List.take_append_drop (output :: outputs).length
                  (gammaDuplexPairs flat.1)).symm
              _ = ((output, advanced) :: outputs.zip advances) ++
                    unreadPairs := by
                rw [pairPrefix]
                rfl
          have paddedDriverRun :
              runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
                  (gammaDuplexPairs flat.1) = .ok decoded := by
            rw [pairSplit]
            exact run_scheduler_native_gamma_from_first_pause_append_of_ok
              transitionFuel firstPause
                ((output, advanced) :: outputs.zip advances) unreadPairs decoded
                  consumedDriverRun
          exact ⟨beforeGamma.digest, flat, firstPause, decoded, routedValue,
            paused, paddedDriverRun, reconstructed,
            decodedValue.trans consumedValueOperational⟩

/-- Routed wrapper form of the actual compiler replay closure.  The response
is constructed by the wrapper's literal gamma-label update, while its run is
the exact production run. -/
theorem exact_compiler_actual_gamma_routed_replay_closure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (response : SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample := by
  obtain ⟨initialDigest, flat, firstPause, decoded, gammaExact, paused,
      driverRun, reconstructed, decodedValue⟩ :=
    exact_compiler_actual_gamma_replay_closure input coordinateStep
  let routed := successfulGammaPrefixFlatRoutingEquiv flat
  let response : SchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) :=
    { decoded.response with
      returnedGamma := some (routedSuccessfulGammaValue routed).1 }
  have decodedRouted : decoded.value = (routedSuccessfulGammaValue routed).1 :=
    decodedValue.trans gammaExact
  have routedRun : exactCompilerRoutedGammaReplay input initialDigest routed =
      .ok response := by
    unfold exactCompilerRoutedGammaReplay schedulerNativeRoutedReplay
      replaySchedulerNativeAtGamma
    rw [paused]
    unfold replaySchedulerNativeOccurrenceAtGamma
    simp only [routed, routedSuccessfulGammaToFlat_flatRoutingEquiv]
    rw [driverRun]
    simp [decodedRouted, response, routed]
  refine ⟨initialDigest, flat, response, gammaExact, routedRun, ?_⟩
  change decoded.response.run = runExactPlainRom transitionFuel configuration
    sample
  simpa [runExactPlainRom, run_scheduler_native_eq_list_run] using reconstructed

/-- The source-derived consumed gamma coordinates are nonempty and therefore
support the production first-pause lift above.  This packages the minimal
induction result at the actual compiler coordinates without claiming that an
arbitrary padded suffix was consumed. -/
theorem exact_compiler_actual_gamma_consumed_run_reconstructs
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∃ (initialDigest output : Digest256) (outputs : List Digest256)
      (advanced : Digest256) (advances : List Digest256)
      (firstPause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result) (gammaOutputInput initialDigest)),
      GammaTableCoordinateChain (exactOperationalTable input) initialDigest
          (output :: outputs) (advanced :: advances) ∧
      (output :: outputs).length =
        ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed ∧
      exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
        .paused firstPause ∧
      ∀ (decoded : DecodedSchedulerNativeGammaResponse
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)),
        runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
            ((output, advanced) :: outputs.zip advances) = .ok decoded →
          decoded.response.run =
            runSchedulerNativeListRun transitionFuel
              (exactPlainRomCursor configuration sample.1)
              (freshAnswerTapeToList sample.2) := by
  obtain ⟨initialDigest, allOutputs, allAdvances, chain, outputsLength,
      _occurs⟩ := exact_compiler_consumed_gamma_coordinates_ordered_root input
  have outputsPositive : 0 < allOutputs.length := by
    rw [outputsLength]
    exact ((exactOperationalTape input).messages.challengeUse
      .gamma).consumesBlock
  cases allOutputs with
  | nil => simp at outputsPositive
  | cons output outputs =>
      cases chain with
      | @next digest output advanced outputs advances outputLookup
          advanceLookup tail =>
          obtain ⟨firstPause, paused⟩ :=
            exact_compiler_final_lookup_has_full_target_pause input
              (gammaOutputInput initialDigest) output outputLookup
          refine ⟨initialDigest, output, outputs, advanced, advances,
            firstPause, ?_, outputsLength, paused, ?_⟩
          · exact .next outputLookup advanceLookup tail
          · intro decoded run
            exact
              run_scheduler_native_gamma_from_first_pause_actual_chain_reconstructs
                input coordinateStep (.next outputLookup advanceLookup tail)
                  firstPause paused decoded run

#print axioms exact_compiler_root_gamma_alignment_answers_factor
#print axioms exact_compiler_root_gamma_alignment_reconstructs_run
#print axioms run_scheduler_native_gamma_prefix_actual_chain_reconstructs
#print axioms run_scheduler_native_gamma_prefix_actual_chain_succeeds
#print axioms run_scheduler_native_gamma_from_first_pause_actual_chain_reconstructs
#print axioms run_scheduler_native_gamma_from_first_pause_actual_chain_succeeds
#print axioms run_scheduler_native_gamma_prefix_append_of_ok
#print axioms run_scheduler_native_gamma_from_first_pause_append_of_ok
#print axioms gamma_duplex_pairs_consumed_prefix
#print axioms exact_compiler_actual_gamma_replay_closure
#print axioms exact_compiler_actual_gamma_routed_replay_closure
#print axioms exact_compiler_actual_gamma_consumed_run_reconstructs

end

end AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
