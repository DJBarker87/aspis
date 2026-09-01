import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence
import AspisFormal.K1.V7Tag73SchedulerNativePreGammaFamily
import AspisFormal.K1.V7Tag73VariablePrefixGammaCoordinates

/-!
# Exact compiler coordinates of the consumed gamma prefix

The checked work-erased evaluator retains the whole successful gamma sample,
not only its first squeeze lookup.  This file extracts every actually consumed
output/advance coordinate, constructs a twelve-coordinate chronological tape
by padding only the unread suffix, and proves that its routed value is the
literal operational gamma.

The coordinate theorem is deliberately phrased in terms of final-table
lookups and actual compiler trace occurrences.  It does not assert that the
fresh occurrences have the same order as the later cached verifier calls;
that stronger scheduler-replay statement requires a separate causal source
bridge.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaCoordinates
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Recursive literal table coordinates -/

/-- The chronological output/advance lookups made by a consumed gamma prefix.
The next digest is the advance answer of the current block. -/
inductive GammaTableCoordinateChain (table : FixedOracleTable) :
    Digest256 -> List Digest256 -> List Digest256 -> Prop where
  | done (digest : Digest256) :
      GammaTableCoordinateChain table digest [] []
  | next {digest output advanced : Digest256}
      {outputs advances : List Digest256}
      (outputLookup : tableLookup table (gammaOutputInput digest) = some output)
      (advanceLookup : tableLookup table (gammaAdvanceInput digest) =
        some advanced)
      (tail : GammaTableCoordinateChain table advanced outputs advances) :
      GammaTableCoordinateChain table digest (output :: outputs)
        (advanced :: advances)

/-- Flatten a consumed coordinate chain to its literal input/answer pairs. -/
def gammaConsumedCoordinates :
    Digest256 -> List Digest256 -> List Digest256 ->
      List (ShaInput × Digest256)
  | _, [], [] => []
  | digest, output :: outputs, advanced :: advances =>
      (gammaOutputInput digest, output) ::
        (gammaAdvanceInput digest, advanced) ::
          gammaConsumedCoordinates advanced outputs advances
  | _, _, _ => []

/-- Literal evaluator call records for a consumed duplex prefix. -/
def gammaConsumedRawCallsFrom (owner : SqueezeOwner) :
    Nat -> Digest256 -> List Digest256 -> List Digest256 -> List RawCall
  | _, _, [], [] => []
  | first, digest, output :: outputs, advanced :: advances =>
      [RawCall.mk (.squeezeOutput owner first) digest output,
       RawCall.mk (.squeezeAdvance owner first) digest advanced] ++
        gammaConsumedRawCallsFrom owner (first + 1) advanced outputs advances
  | _, _, _, _ => []

@[simp] theorem gamma_consumed_coordinates_length
    (table : FixedOracleTable) (digest : Digest256)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain table digest outputs advances) :
    (gammaConsumedCoordinates digest outputs advances).length =
      2 * outputs.length := by
  induction chain with
  | done => rfl
  | next outputLookup advanceLookup tail ih =>
      simp [gammaConsumedCoordinates, ih]
      omega

theorem gamma_table_coordinate_chain_lengths
    (table : FixedOracleTable) (digest : Digest256)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain table digest outputs advances) :
    advances.length = outputs.length := by
  induction chain with
  | done => rfl
  | next outputLookup advanceLookup tail ih => simp [ih]

/-- Every flattened coordinate is a literal lookup in the same fixed table. -/
theorem gamma_consumed_coordinate_lookup
    (table : FixedOracleTable) (digest : Digest256)
    (outputs advances : List Digest256)
    (chain : GammaTableCoordinateChain table digest outputs advances)
    (target : ShaInput) (answer : Digest256)
    (member : (target, answer) ∈
      gammaConsumedCoordinates digest outputs advances) :
    tableLookup table target = some answer := by
  induction chain with
  | done => simp [gammaConsumedCoordinates] at member
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      simp only [gammaConsumedCoordinates, List.mem_cons] at member
      rcases member with head | head | later
      · rcases head with ⟨rfl, rfl⟩
        exact outputLookup
      · rcases head with ⟨rfl, rfl⟩
        exact advanceLookup
      · exact ih later

/-- The evaluator squeeze recursion exposes both answers, including the
advance digest that is not stored in `SampleRecord.blocks`.  The coordinate
chain is owner-independent; logical ownership is retained only in the raw
call evidence. -/
theorem evaluator_squeeze_chain_coordinates
    (table : FixedOracleTable) (first : Nat)
    (owner : SqueezeOwner)
    (state finalState : EvalState) (outputs : List Digest256)
    (chain : EvaluatorSqueezeChain table owner first state outputs finalState) :
    ∃ advances,
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table state.digest outputs advances ∧
      finalState.calls = state.calls ++
        gammaConsumedRawCallsFrom owner first state.digest outputs advances := by
  induction chain with
  | done first state => exact ⟨[], rfl, .done state.digest, by simp
      [gammaConsumedRawCallsFrom]⟩
  | @next first state middle final output outputs head tail ih =>
      obtain ⟨advances, lengthExact, tailCoordinates, tailCalls⟩ := ih
      obtain ⟨outputLookup, advanceLookup, headCalls⟩ :=
        squeeze_step_emits_two_distinct_queries table state middle
          owner first output head
      refine ⟨middle.digest :: advances, by simp [lengthExact], ?_, ?_⟩
      · exact .next
          (by simpa [gammaOutputInput, domSqueeze] using outputLookup)
          (by simpa [gammaAdvanceInput, domAdvance] using advanceLookup)
          tailCoordinates
      · rw [tailCalls, headCalls]
        simp [gammaConsumedRawCallsFrom, List.append_assoc]

/-- Gamma-specialized compatibility wrapper. -/
theorem evaluator_gamma_squeeze_chain_coordinates
    (table : FixedOracleTable) (first : Nat)
    (state finalState : EvalState) (outputs : List Digest256)
    (chain : EvaluatorSqueezeChain table (.challenge .gamma) first state
      outputs finalState) :
    ∃ advances,
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table state.digest outputs advances ∧
      finalState.calls = state.calls ++
        gammaConsumedRawCallsFrom (.challenge .gamma) first state.digest
          outputs advances :=
  evaluator_squeeze_chain_coordinates table first (.challenge .gamma) state
    finalState outputs chain

/-- Owner-generic coordinate extraction for one successful deployed sampler.
Logical ownership is retained in the raw-call suffix, while the fixed-table
coordinates themselves remain the literal two-query duplex inputs. -/
theorem squeeze_many_coordinates
    (table : FixedOracleTable) (owner : SqueezeOwner) (count : Nat)
    (state finalState : EvalState) (outputs : List Digest256)
    (run : squeezeMany table owner count state = some (outputs, finalState)) :
    ∃ advances,
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table state.digest outputs advances ∧
      finalState.calls = state.calls ++
        gammaConsumedRawCallsFrom owner 0 state.digest outputs advances := by
  have chain := evaluator_squeeze_chain_of_run table owner 0 count state
    finalState outputs (by simpa [squeezeMany] using run)
  exact evaluator_squeeze_chain_coordinates table 0 owner state finalState
    outputs chain

theorem squeeze_many_gamma_coordinates
    (table : FixedOracleTable) (count : Nat)
    (state finalState : EvalState) (outputs : List Digest256)
    (run : squeezeMany table (.challenge .gamma) count state =
      some (outputs, finalState)) :
    ∃ advances,
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table state.digest outputs advances ∧
      finalState.calls = state.calls ++
        gammaConsumedRawCallsFrom (.challenge .gamma) 0 state.digest outputs
          advances := by
  exact squeeze_many_coordinates table (.challenge .gamma) count state
    finalState outputs run

/-! ## Padding only the unread suffix -/

/-- Extend a consumed list to twelve coordinates.  Only indices beyond the
list length read the arbitrary default. -/
def padGammaCoordinates (values : List Digest256) (default : Digest256) :
    Fin 12 -> Digest256 :=
  fun index => values.getD index.val default

def totalGammaTapeOfConsumed
    (outputs advances : List Digest256)
    (outputDefault advanceDefault : Digest256) : TotalGammaDuplexTape :=
  (padGammaCoordinates outputs outputDefault,
    padGammaCoordinates advances advanceDefault)

theorem ofFn_pad_gamma_coordinates_take
    (values : List Digest256) (default : Digest256)
    (within : values.length ≤ 12) :
    (List.ofFn (padGammaCoordinates values default)).take values.length =
      values := by
  apply List.ext_getElem
  · simp [within]
  · intro index leftBound rightBound
    simp only [List.length_take, List.length_ofFn] at leftBound
    have indexWithin : index < 12 := by omega
    simp only [List.getElem_take, List.getElem_ofFn, padGammaCoordinates]
    rw [List.getD_eq_getElem values default rightBound]

theorem total_gamma_tape_output_prefix
    (outputs advances : List Digest256)
    (outputDefault advanceDefault : Digest256)
    (within : outputs.length ≤ 12) :
    (gammaOutputBlocks
      (totalGammaTapeOfConsumed outputs advances outputDefault
        advanceDefault)).take outputs.length = outputs := by
  exact ofFn_pad_gamma_coordinates_take outputs outputDefault within

theorem total_gamma_tape_advance_prefix
    (outputs advances : List Digest256)
    (outputDefault advanceDefault : Digest256)
    (within : advances.length ≤ 12) :
    (List.ofFn
      (totalGammaTapeOfConsumed outputs advances outputDefault
        advanceDefault).2).take advances.length = advances := by
  exact ofFn_pad_gamma_coordinates_take advances advanceDefault within

/-! ## The source-derived successful prefix tape -/

/-- The strict exact-compiler input constructs one successful chronological
gamma tape.  Its consumed output and advance coordinates are exactly the
literal fixed-table answers; the unused suffix is merely zero-padded and is
never required to decode.  Routing this tape returns the operational gamma. -/
theorem exact_compiler_constructs_successful_gamma_prefix_coordinates
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (beforeGamma afterBlocks : EvalState)
      (outputs advances : List Digest256)
      (flat : SuccessfulGammaPrefixTape) (decoded consumedDecoded : OrdinaryPrefixDecode)
      (consumedValue : QM31Exact),
      outputs.length =
          ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed ∧
      advances.length = outputs.length ∧
      GammaTableCoordinateChain (exactOperationalTable input)
        beforeGamma.digest
        outputs advances ∧
      afterBlocks.calls = beforeGamma.calls ++
        gammaConsumedRawCallsFrom (.challenge .gamma) 0 beforeGamma.digest
          outputs advances ∧
      (gammaOutputBlocks flat.1).take outputs.length = outputs ∧
      (List.ofFn flat.1.2).take advances.length = advances ∧
      decodeNonzeroPrefix 3 outputs = some consumedDecoded ∧
      decodeTagQM31ExactLE consumedDecoded.value = some consumedValue ∧
      consumedDecoded.value =
        (exactOperationalTape input).messages.challengeValue .gamma ∧
      runGammaPrefix flat.1 = some decoded ∧
      decoded.value =
        (exactOperationalTape input).messages.challengeValue .gamma ∧
      exactOperationalChallenge input .gamma =
        (routedSuccessfulGammaValue
          (successfulGammaPrefixFlatRoutingEquiv flat)).1 := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  have splitRun := segments.afterSemanticRun
  rw [after_semantic_tail_events_gamma_split] at splitRun
  obtain ⟨beforeGamma, _prefixRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input)
      (beforeGammaTailEvents (exactOperationalTape input).messages)
      (challengeEvent (exactOperationalTape input).messages .gamma ::
        ([.absorb (.inactiveClaim
            (exactOperationalTape input).messages.inactiveClaim),
          challengeEvent (exactOperationalTape input).messages .kappa] ++
          oodEvents (exactOperationalTape input).messages ++
          [.absorb (.relationRound 0
            ((exactOperationalTape input).messages.relationSent 0)),
           .grind .fold (exactOperationalTape input).messages.foldGrinding,
           .check .foldWork,
           .absorb (.foldNonce
            (exactOperationalTape input).messages.foldGrinding.selected),
           challengeEvent (exactOperationalTape input).messages (.alpha 0),
           .absorb (.final256
            (exactOperationalTape input).messages.finalValues),
           .grind .final (exactOperationalTape input).messages.finalGrinding,
           .check .finalWork,
           .absorb (.finalNonce
            (exactOperationalTape input).messages.finalGrinding.selected)]))
      segments.afterSemantic evaluator.prefixState).mp splitRun
  simp only [runMachineEventsWorkErased] at restRun
  obtain ⟨afterGamma, gammaRun, tailRun⟩ :=
    Option.bind_eq_some_iff.mp restRun
  have gammaRun' : runMachineEventWorkErased (exactOperationalTable input)
      beforeGamma (.challenge .gamma
        ((exactOperationalTape input).messages.challengeUse .gamma)) =
        some afterGamma := by
    simpa [challengeEvent] using gammaRun
  obtain ⟨outputs, afterBlocks, squeezeRun, afterGammaExact, outputsLength,
      recordMember⟩ := challenge_event_work_erased_exposes_record
    (exactOperationalTable input) beforeGamma afterGamma .gamma
      ((exactOperationalTape input).messages.challengeUse .gamma) gammaRun'
  obtain ⟨advances, advancesLength, coordinates, callsExact⟩ :=
    squeeze_many_gamma_coordinates (exactOperationalTable input)
      ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed
      beforeGamma afterBlocks outputs squeezeRun
  let remainingEvents : List MachineEvent :=
    [.absorb (.inactiveClaim
        (exactOperationalTape input).messages.inactiveClaim),
      challengeEvent (exactOperationalTape input).messages .kappa] ++
      oodEvents (exactOperationalTape input).messages ++
      [.absorb (.relationRound 0
        ((exactOperationalTape input).messages.relationSent 0)),
       .grind .fold (exactOperationalTape input).messages.foldGrinding,
       .check .foldWork,
       .absorb (.foldNonce
        (exactOperationalTape input).messages.foldGrinding.selected),
       challengeEvent (exactOperationalTape input).messages (.alpha 0),
       .absorb (.final256
        (exactOperationalTape input).messages.finalValues),
       .grind .final (exactOperationalTape input).messages.finalGrinding,
       .check .finalWork,
       .absorb (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected)]
  have tailIncluded : SamplesIncluded afterGamma evaluator.prefixState :=
    machine_events_work_erased_samples_included (exactOperationalTable input)
      remainingEvents afterGamma evaluator.prefixState (by
        simpa [remainingEvents] using tailRun)
  have throughQ16 : SamplesIncluded evaluator.prefixState evaluator.afterQ16 :=
    run_q16_preserves_prior_samples (exactOperationalTable input)
      evaluator.prefixState evaluator.afterQ16
      (q16TapeOfSearch (exactOperationalTape input).search) evaluator.q16Run
  have afterQ16 : SamplesIncluded evaluator.afterQ16 evaluator.finalState :=
    machine_events_work_erased_samples_included (exactOperationalTable input)
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState evaluator.afterQ16Run
  have recordFinal :
      ({ id := .gamma, blocks := outputs } : SampleRecord) ∈
        evaluator.finalState.samples :=
    afterQ16 _ (throughQ16 _ (tailIncluded _ recordMember))
  have acceptedParameter :
      decodeNonzeroExact outputs =
        some ((exactOperationalTape input).messages.challengeValue .gamma) := by
    have decodedAtFinal := finalDecoded
      ({ id := .gamma, blocks := outputs } : SampleRecord) recordFinal
    simpa [decodeChallengeParameter, samplerMode] using decodedAtFinal
  obtain ⟨decoded, prefixRun, noRemaining, decodedValue⟩ :=
    decodeNonzeroExact_witness outputs
      ((exactOperationalTape input).messages.challengeValue .gamma)
      acceptedParameter
  have outputsWithin : outputs.length ≤ 12 := by
    rw [outputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        .gamma).withinDeployedCap
  have advancesWithin : advances.length ≤ 12 := by
    rw [advancesLength]
    exact outputsWithin
  let tape := totalGammaTapeOfConsumed outputs advances (zeroBytes 32)
    (zeroBytes 32)
  have outputPrefix : (gammaOutputBlocks tape).take outputs.length = outputs :=
    total_gamma_tape_output_prefix outputs advances (zeroBytes 32)
      (zeroBytes 32) outputsWithin
  let unreadOutputs := (gammaOutputBlocks tape).drop outputs.length
  have outputSplit : gammaOutputBlocks tape = outputs ++ unreadOutputs := by
    calc
      gammaOutputBlocks tape =
          (gammaOutputBlocks tape).take outputs.length ++
            (gammaOutputBlocks tape).drop outputs.length :=
        (List.take_append_drop outputs.length (gammaOutputBlocks tape)).symm
      _ = outputs ++ unreadOutputs := by rw [outputPrefix]
  have fullPrefixRun : runGammaPrefix tape =
      some (appendOrdinaryRemaining decoded unreadOutputs) := by
    unfold runGammaPrefix
    rw [outputSplit]
    exact decodeNonzeroPrefix_append_of_some 3 outputs unreadOutputs decoded
      prefixRun
  let flat : SuccessfulGammaPrefixTape :=
    ⟨tape, by unfold GammaPrefixSucceeds; rw [fullPrefixRun]; rfl⟩
  have flatRun : runGammaPrefix flat.1 =
      some (appendOrdinaryRemaining decoded unreadOutputs) := fullPrefixRun
  have routedDecode := flatRoutingEquiv_returned_exact_value flat
    (appendOrdinaryRemaining decoded unreadOutputs) flatRun
  obtain ⟨exactValue, exactDecode⟩ :=
    decodeChallengeParameter_has_exact_tower_value
      exactSecureCircleParameterMap .gamma outputs
      ((exactOperationalTape input).messages.challengeValue .gamma)
      (by simpa [decodeChallengeParameter, samplerMode] using acceptedParameter)
  have operationalValue : exactOperationalChallenge input .gamma =
      exactValue := by
    simp [exactOperationalChallenge, exactChallengeValue, exactDecode]
  have routedValue :
      (routedSuccessfulGammaValue
        (successfulGammaPrefixFlatRoutingEquiv flat)).1 = exactValue := by
    apply Option.some.inj
    rw [← routedDecode]
    simpa [appendOrdinaryRemaining, decodedValue] using exactDecode
  refine ⟨beforeGamma, afterBlocks, outputs, advances, flat,
    appendOrdinaryRemaining decoded unreadOutputs, decoded, exactValue,
    outputsLength, advancesLength, coordinates, callsExact, outputPrefix, ?_,
    prefixRun, ?_, decodedValue, flatRun, ?_, ?_⟩
  · exact total_gamma_tape_advance_prefix outputs advances (zeroBytes 32)
      (zeroBytes 32) advancesWithin
  · simpa [decodedValue] using exactDecode
  · simpa [appendOrdinaryRemaining] using decodedValue
  · exact operationalValue.trans routedValue.symm

/-! ## Every consumed coordinate occurs in the actual compiler trace -/

/-- Each consumed output or advance answer was created at a literal fresh
coordinate of the actual result-carrying compiler trace.  This says nothing
about the relative order of those first creations. -/
theorem exact_compiler_consumed_gamma_coordinates_occur
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ initialDigest outputs advances,
      GammaTableCoordinateChain (exactOperationalTable input) initialDigest
          outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse .gamma).blocksUsed ∧
      ∀ target answer,
        (target, answer) ∈
            gammaConsumedCoordinates initialDigest outputs advances ->
          ∃ actor,
            (.machineFresh actor target answer : UnifiedExposureRecord) ∈
              (runExactPlainRom transitionFuel configuration sample).trace := by
  obtain ⟨beforeGamma, afterBlocks, outputs, advances, flat, decoded,
      consumedDecoded, consumedValue,
      outputsLength,
      advancesLength, coordinates, callsExact, outputPrefix, advancePrefix,
      consumedRun, consumedValueRun, consumedDecodedValue, flatRun,
      decodedValue, routedValue⟩ :=
    exact_compiler_constructs_successful_gamma_prefix_coordinates input
  refine ⟨beforeGamma.digest, outputs, advances, coordinates, outputsLength,
    ?_⟩
  intro target answer member
  have lookup := gamma_consumed_coordinate_lookup
    (exactOperationalTable input) beforeGamma.digest outputs advances
      coordinates target answer member
  obtain ⟨actor, rootMember⟩ := exact_final_table_lookup_has_root_record input
    target answer lookup
  refine ⟨actor, ?_⟩
  rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
    configuration projection fixedInstance sample input.package]
  exact List.mem_append_left _ rootMember

/-- The same source construction binds its own pre-gamma digest and routed
successful tape to an executable first-coordinate pause.  Thus the first scan
and the sampler witness are not chosen by unrelated existential proofs. -/
theorem exact_compiler_constructs_routed_gamma_with_first_pause
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (pause : SchedulerNativeFreshPause
        (globalFull256OracleCallCap parameters)
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)
        (gammaOutputInput initialDigest)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
        .paused pause := by
  obtain ⟨beforeGamma, afterBlocks, outputs, advances, flat, decoded,
      consumedDecoded, consumedValue,
      outputsLength,
      advancesLength, coordinates, callsExact, outputPrefix, advancePrefix,
      consumedRun, consumedValueRun, consumedDecodedValue, flatRun,
      decodedValue, routedValue⟩ :=
    exact_compiler_constructs_successful_gamma_prefix_coordinates input
  have outputsPositive : 0 < outputs.length := by
    rw [outputsLength]
    exact ((exactOperationalTape input).messages.challengeUse
      .gamma).consumesBlock
  cases coordinates with
  | done digest => simp at outputsPositive
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail =>
      obtain ⟨actor, rootMember⟩ := exact_final_table_lookup_has_root_record
        input (gammaOutputInput beforeGamma.digest) output outputLookup
      have fullMember :
          (.machineFresh actor (gammaOutputInput beforeGamma.digest) output :
            UnifiedExposureRecord) ∈
            (runExactPlainRom transitionFuel configuration sample).trace := by
        rw [exact_fixed_operational_state_map_trace_is_full_trace
          transitionFuel configuration projection fixedInstance sample
          input.package]
        exact List.mem_append_left _ rootMember
      obtain ⟨pause, paused⟩ :=
        exact_compiler_full_target_scan_paused_of_trace_mem input
          (gammaOutputInput beforeGamma.digest) actor output fullMember
      exact ⟨beforeGamma.digest, flat, pause, routedValue, paused⟩

#print axioms gamma_consumed_coordinates_length
#print axioms gamma_consumed_coordinate_lookup
#print axioms evaluator_squeeze_chain_coordinates
#print axioms evaluator_gamma_squeeze_chain_coordinates
#print axioms squeeze_many_coordinates
#print axioms squeeze_many_gamma_coordinates
#print axioms ofFn_pad_gamma_coordinates_take
#print axioms exact_compiler_constructs_successful_gamma_prefix_coordinates
#print axioms exact_compiler_consumed_gamma_coordinates_occur
#print axioms exact_compiler_constructs_routed_gamma_with_first_pause

end

end AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
