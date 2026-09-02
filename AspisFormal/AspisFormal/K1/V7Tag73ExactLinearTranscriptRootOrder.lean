import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant
import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder
import AspisFormal.K1.V7Tag73ExactFinal256DigestRootOrigin

/-!
# Root order through the accepted linear Tag-73 transcript

This module propagates the first-creation order of a transcript-state producer
through arbitrary successful linear machine events.  It is the reusable causal
bridge needed to show that the C1 and C2 root absorptions were fixed before the
selected final-work/q16 anchor, including adversary-first cache population.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactLinearTranscriptRootOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFinal256DigestRootOrigin
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootFreshInputUniqueness
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

private theorem run_machine_events_append_iff
    (table : FixedOracleTable) (first second : List MachineEvent)
    (state final : EvalState) :
    runMachineEvents table (first ++ second) state = some final ↔
      ∃ middle,
        runMachineEvents table first state = some middle ∧
        runMachineEvents table second middle = some final := by
  induction first generalizing state with
  | nil => simp [runMachineEvents]
  | cons event rest ih =>
      simp only [List.cons_append, runMachineEvents]
      constructor
      · intro run
        obtain ⟨next, eventRun, tailRun⟩ := Option.bind_eq_some_iff.mp run
        obtain ⟨middle, restRun, secondRun⟩ := (ih next).mp tailRun
        exact ⟨middle, Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, restRun⟩, secondRun⟩
      · rintro ⟨middle, firstRun, secondRun⟩
        obtain ⟨next, eventRun, restRun⟩ :=
          Option.bind_eq_some_iff.mp firstRun
        exact Option.bind_eq_some_iff.mpr
          ⟨next, eventRun, (ih next).mpr ⟨middle, restRun, secondRun⟩⟩

/-- Strict chronological order of two concrete input/answer pairs in the
actual adversary-then-verifier first-creation root. -/
def ExactRootPairBefore
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
    (first second : ShaInput × Digest256) : Prop :=
  ∃ before middle after,
    exactRootFreshQueries input =
      before ++ first :: middle ++ second :: after

/-- Distinct root inputs imply that the concrete first-creation pairs are
duplicate-free as well. -/
private theorem pairs_nodup_of_inputs_nodup
    (queries : List (ShaInput × Digest256))
    (inputsNodup : (queries.map Prod.fst).Nodup) :
    queries.Nodup := by
  induction queries with
  | nil => exact .nil
  | cons head tail ih =>
      rw [List.map_cons] at inputsNodup
      obtain ⟨headMissing, tailNodup⟩ := List.nodup_cons.mp inputsNodup
      apply List.nodup_cons.mpr
      refine ⟨?_, ih tailNodup⟩
      intro headMember
      exact headMissing (List.mem_map.mpr ⟨head, headMember, rfl⟩)

theorem exact_root_fresh_queries_nodup
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
    (exactRootFreshQueries input).Nodup := by
  exact pairs_nodup_of_inputs_nodup (exactRootFreshQueries input)
    (exact_root_fresh_query_inputs_nodup input)

/-- Strict first-creation order is transitive. -/
theorem exact_root_pair_before_trans
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {first middle last : ShaInput × Digest256}
    (firstBeforeMiddle : ExactRootPairBefore input first middle)
    (middleBeforeLast : ExactRootPairBefore input middle last) :
    ExactRootPairBefore input first last := by
  obtain ⟨firstPrior, firstMiddle, middleLater, firstExact⟩ :=
    firstBeforeMiddle
  obtain ⟨middlePrior, middleLast, lastLater, middleExact⟩ :=
    middleBeforeLast
  have firstMember : first ∈ middlePrior :=
    mem_canonical_prefix_of_strictly_before_pivot
      (exactRootFreshQueries input) middlePrior
      (middleLast ++ last :: lastLater) firstPrior firstMiddle middleLater first
      middle (exact_root_fresh_queries_nodup input)
      (by simpa only [List.cons_append, List.append_assoc] using middleExact)
      firstExact
  obtain ⟨before, after, priorExact⟩ :=
    (List.mem_iff_append).mp firstMember
  refine ⟨before, after ++ middle :: middleLast, lastLater, ?_⟩
  rw [middleExact, priorExact]
  simp only [List.cons_append, List.append_assoc]

/-- Reflexive closure used while a check or grinding probe leaves the
continuing transcript digest unchanged. -/
def ExactRootPairBeforeOrEq
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
    (first second : ShaInput × Digest256) : Prop :=
  first = second ∨ ExactRootPairBefore input first second

theorem exact_root_pair_before_or_eq_trans_before
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {first middle last : ShaInput × Digest256}
    (firstBeforeOrEq : ExactRootPairBeforeOrEq input first middle)
    (middleBeforeLast : ExactRootPairBefore input middle last) :
    ExactRootPairBefore input first last := by
  rcases firstBeforeOrEq with rfl | strict
  · exact middleBeforeLast
  · exact exact_root_pair_before_trans strict middleBeforeLast

/-- A nonempty ordered duplex chain places its initial state producer
strictly before the advance query producing its terminal digest. -/
theorem exact_root_ordered_chain_initial_before_terminal
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {producerInput : ShaInput} {digest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances)
    (nonempty : 0 < outputs.length) :
    ∃ terminalInput,
      tableLookup (exactOperationalTable input) terminalInput =
          some (gammaTerminalDigest digest advances) ∧
      ExactRootPairBefore input (producerInput, digest)
        (terminalInput, gammaTerminalDigest digest advances) := by
  induction chain with
  | done => simp at nonempty
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      by_cases outputsEmpty : outputs = []
      · subst outputs
        have advancesEmpty : advances = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using exact_root_ordered_q16_chain_lengths tail
        subst advances
        refine ⟨gammaAdvanceInput digest, ?_, ?_⟩
        · simpa [gammaTerminalDigest] using advanceFound
        · simpa [ExactRootPairBefore, gammaTerminalDigest] using
            producerBeforeAdvance
      · have tailNonempty : 0 < outputs.length := by
          exact Nat.pos_of_ne_zero fun lengthZero =>
            outputsEmpty (List.length_eq_zero_iff.mp lengthZero)
        obtain ⟨terminalInput, terminalLookup, terminalOrder⟩ :=
          ih tailNonempty
        have firstOrder : ExactRootPairBefore input (producerInput, digest)
            (gammaAdvanceInput digest, advanced) := by
          simpa [ExactRootPairBefore] using producerBeforeAdvance
        refine ⟨terminalInput, ?_, ?_⟩
        · simpa [gammaTerminalDigest] using terminalLookup
        · simpa [gammaTerminalDigest] using
            (exact_root_pair_before_trans firstOrder terminalOrder)

/-- One successful linear event preserves an origin producer in the reflexive
root order while returning a concrete producer for the continuing digest. -/
theorem exact_root_order_through_machine_event
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (origin : ShaInput × Digest256) (producerInput : ShaInput)
    (state next : EvalState) (event : MachineEvent)
    (producerLookup : tableLookup (exactOperationalTable input) producerInput =
      some state.digest)
    (originBeforeOrEq : ExactRootPairBeforeOrEq input origin
      (producerInput, state.digest))
    (run : runMachineEvent (exactOperationalTable input) state event =
      some next) :
    ∃ nextProducerInput,
      tableLookup (exactOperationalTable input) nextProducerInput =
          some next.digest ∧
      ExactRootPairBeforeOrEq input origin (nextProducerInput, next.digest) := by
  cases event with
  | absorb payload =>
      let absorbInput :=
        bytes state.digest ++ [domAbsorb, payload.label] ++ payload.data
      have absorbLookup : tableLookup (exactOperationalTable input)
          absorbInput = some next.digest := by
        simpa [absorbInput] using absorb_step_exposes_literal_lookup
          (exactOperationalTable input) state next payload run
      have dependency : HasLiteralStatePrefix state.digest absorbInput := by
        unfold HasLiteralStatePrefix absorbInput
        simp
      have producerBeforeAbsorb : ExactRootPairBefore input
          (producerInput, state.digest) (absorbInput, next.digest) := by
        simpa [ExactRootPairBefore] using
          exact_compiler_literal_dependency_has_strict_root_order
            transitionRoom input producerInput absorbInput state.digest
              next.digest producerLookup absorbLookup dependency
      exact ⟨absorbInput, absorbLookup, Or.inr
        (exact_root_pair_before_or_eq_trans_before originBeforeOrEq
          producerBeforeAbsorb)⟩
  | challenge id use =>
      rw [runMachineEvent] at run
      obtain ⟨samplePair, squeezeRun, result⟩ :=
        Option.bind_eq_some_iff.mp run
      rcases samplePair with ⟨outputs, sampled⟩
      have nextExact :
          { sampled with
              samples := sampled.samples ++ [{ id := id, blocks := outputs }] } =
            next := by
        simpa only [pure, Option.some.injEq] using result
      subst next
      obtain ⟨advances, advancesLength, coordinates, terminalExact,
          _callsExact⟩ :=
        squeeze_many_coordinates_with_terminal (exactOperationalTable input)
          (.challenge id) use.blocksUsed state sampled outputs squeezeRun
      have outputsLength : outputs.length = use.blocksUsed :=
        (squeeze_many_exact_sizes (exactOperationalTable input)
          (.challenge id) use.blocksUsed state sampled outputs squeezeRun).1
      have outputsPositive : 0 < outputs.length := by
        rw [outputsLength]
        exact use.consumesBlock
      have ordered := gamma_table_coordinate_chain_has_exact_root_order
        transitionRoom input producerInput state.digest producerLookup coordinates
      obtain ⟨terminalInput, terminalLookup, producerBeforeTerminal⟩ :=
        exact_root_ordered_chain_initial_before_terminal ordered outputsPositive
      refine ⟨terminalInput, ?_, Or.inr ?_⟩
      · simpa [terminalExact] using terminalLookup
      · have originBeforeTerminal :=
          exact_root_pair_before_or_eq_trans_before originBeforeOrEq
            producerBeforeTerminal
        simpa [terminalExact] using originBeforeTerminal
  | grind stage choice =>
      have digestExact := grinding_choice_does_not_advance
        (exactOperationalTable input) state next stage choice run
      refine ⟨producerInput, ?_, ?_⟩
      · simpa [digestExact] using producerLookup
      · simpa [digestExact] using originBeforeOrEq
  | check check =>
      have nextExact : next = state := by
        simpa [runMachineEvent] using (Option.some.inj run).symm
      subst next
      exact ⟨producerInput, producerLookup, originBeforeOrEq⟩

/-- Iteration of the one-event result over a successful literal event list. -/
theorem exact_root_order_through_machine_events
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (origin : ShaInput × Digest256) (producerInput : ShaInput)
    (events : List MachineEvent) (state final : EvalState)
    (producerLookup : tableLookup (exactOperationalTable input) producerInput =
      some state.digest)
    (originBeforeOrEq : ExactRootPairBeforeOrEq input origin
      (producerInput, state.digest))
    (run : runMachineEvents (exactOperationalTable input) events state =
      some final) :
    ∃ finalProducerInput,
      tableLookup (exactOperationalTable input) finalProducerInput =
          some final.digest ∧
      ExactRootPairBeforeOrEq input origin
        (finalProducerInput, final.digest) := by
  induction events generalizing state producerInput with
  | nil =>
      have finalExact : final = state := by
        simpa [runMachineEvents] using (Option.some.inj run).symm
      subst final
      exact ⟨producerInput, producerLookup, originBeforeOrEq⟩
  | cons event rest ih =>
      rw [runMachineEvents] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨nextProducer, nextLookup, nextOrder⟩ :=
        exact_root_order_through_machine_event transitionRoom input origin
          producerInput state next event producerLookup originBeforeOrEq eventRun
      exact ih (producerInput := nextProducer) (state := next) nextLookup
        nextOrder restRun

/-- Any later lookup whose input begins with the final continuing state lies
strictly after the original producer, irrespective of cached ownership. -/
theorem exact_root_origin_before_post_events_lookup
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (originInput dependentInput : ShaInput) (originAnswer dependentAnswer : Digest256)
    (events : List MachineEvent) (state final : EvalState)
    (originLookup : tableLookup (exactOperationalTable input) originInput =
      some originAnswer)
    (originState : originAnswer = state.digest)
    (run : runMachineEvents (exactOperationalTable input) events state =
      some final)
    (dependentLookup : tableLookup (exactOperationalTable input) dependentInput =
      some dependentAnswer)
    (dependentPrefix : HasLiteralStatePrefix final.digest dependentInput) :
    ExactRootPairBefore input (originInput, originAnswer)
      (dependentInput, dependentAnswer) := by
  subst originAnswer
  obtain ⟨finalProducer, finalLookup, originBeforeOrEq⟩ :=
    exact_root_order_through_machine_events transitionRoom input
      (originInput, state.digest) originInput events state final originLookup
      (Or.inl rfl) run
  have finalBeforeDependent : ExactRootPairBefore input
      (finalProducer, final.digest) (dependentInput, dependentAnswer) := by
    simpa [ExactRootPairBefore] using
      exact_compiler_literal_dependency_has_strict_root_order transitionRoom
        input finalProducer dependentInput final.digest dependentAnswer
          finalLookup dependentLookup dependentPrefix
  exact exact_root_pair_before_or_eq_trans_before originBeforeOrEq
    finalBeforeDependent

/-- In every accepted production execution, both root absorptions are
strictly earlier than the final256 absorption in the actual first-creation
root.  This is the concrete pre-q16 commitment fact; adversary-first cache
population is covered by the root-order lemmas rather than excluded. -/
theorem exact_operational_root_absorbs_before_final256
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (c1Before c2Before c1Salt c2Salt c1Answer c2Answer : Digest256)
        (beforeFinal256 : EvalState)
        (prefinalDigest workAnswer q16Base : Digest256),
      let c1Input :=
        bytes c1Before ++ [domAbsorb, c1RootLabel] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
            (exactOperationalTape input).messages.c1Root c1Salt).data
      let c2Input :=
        bytes c2Before ++ [domAbsorb, c2RootLabel] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
            (exactOperationalTape input).messages.c2.root c2Salt).data
      let final256Input :=
        bytes beforeFinal256.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
              (exactOperationalTape input).messages.finalValues).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
            (exactOperationalTape input).messages.finalValues).data
      let workInput :=
        bytes prefinalDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected
      let nonceInput :=
        bytes prefinalDigest ++ [domAbsorb, finalWorkNonceLabel] ++
          bytes (exactOperationalTape input).messages.finalGrinding.selected
      tableLookup (exactOperationalTable input) c1Input = some c1Answer ∧
      tableLookup (exactOperationalTable input) c2Input = some c2Answer ∧
      tableLookup (exactOperationalTable input) final256Input =
        some prefinalDigest ∧
      tableLookup (exactOperationalTable input) workInput = some workAnswer ∧
      FinalWork34Accepted workAnswer ∧
      tableLookup (exactOperationalTable input) nonceInput = some q16Base ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      ExactRootPairBefore input (c1Input, c1Answer)
        (final256Input, prefinalDigest) ∧
      ExactRootPairBefore input (c2Input, c2Answer)
        (final256Input, prefinalDigest) ∧
      ExactRootPairBefore input (c1Input, c1Answer)
        (workInput, workAnswer) ∧
      ExactRootPairBefore input (c2Input, c2Answer)
        (workInput, workAnswer) ∧
      ExactRootPairBefore input (c1Input, c1Answer)
        (nonceInput, q16Base) ∧
      ExactRootPairBefore input (c2Input, c2Answer)
        (nonceInput, q16Base) := by
  have strict := input.package.root.fixedRoot.base.strictRefinement
  have refined := (checked_refinement_is_well_formed
    (exactOperationalTable input) exactDeterministicDecoders
    (exactOperationalTape input) (exactOperationalRawTrace input) strict).1
  rw [refine] at refined
  obtain ⟨prefixState, prefixRun, refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  obtain ⟨_afterQ16, _q16Run, refined⟩ :=
    Option.bind_eq_some_iff.mp refined
  obtain ⟨_finalState, _finalRun, rawRun⟩ :=
    Option.bind_eq_some_iff.mp refined
  have q16BaseExact : prefixState.digest =
      (exactOperationalRawTrace input).q16BaseDigest := by
    simpa using congrArg InteractiveRawTrace.q16BaseDigest
      (Option.some.inj rawRun)
  rw [runPrefix] at prefixRun
  obtain ⟨beforeC1, _beforeC1Run, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c1Pair, c1SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c1Pair with ⟨c1Salt, withC1SaltQuery⟩
  obtain ⟨afterC1, c1AbsorbRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨afterPhaseChallenges, phaseRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  obtain ⟨c2Pair, c2SaltRun, prefixRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rcases c2Pair with ⟨c2Salt, withC2SaltQuery⟩
  obtain ⟨afterC2, c2AbsorbRun, remainingRun⟩ :=
    Option.bind_eq_some_iff.mp prefixRun
  rw [prefix_after_c2_final_work_split] at remainingRun
  obtain ⟨beforeFinalWork, beforeFinalRun, suffixRun⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFinalWork (exactOperationalTape input).messages)
      [.grind .final (exactOperationalTape input).messages.finalGrinding,
       .check .finalWork,
       .absorb (.finalNonce
        (exactOperationalTape input).messages.finalGrinding.selected)]
      afterC2 prefixState).mp remainingRun
  rw [prefix_before_final_work_final256_split] at beforeFinalRun
  obtain ⟨beforeFinal256, beforeFinal256Run, final256Run⟩ :=
    (run_machine_events_append_iff
      (exactOperationalTable input)
      (prefixAfterC2BeforeFinal256 (exactOperationalTape input).messages)
      [.absorb (.final256 (exactOperationalTape input).messages.finalValues)]
      afterC2 beforeFinalWork).mp beforeFinalRun
  simp only [runMachineEvents] at final256Run
  obtain ⟨afterFinal256, final256AbsorbRun, final256Done⟩ :=
    Option.bind_eq_some_iff.mp final256Run
  have afterFinal256Exact : afterFinal256 = beforeFinalWork := by
    simpa [runMachineEvents] using Option.some.inj final256Done
  subst afterFinal256
  simp only [runMachineEvents] at suffixRun
  obtain ⟨afterGrind, grindRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨afterCheck, checkRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterCheckExact : afterCheck = afterGrind := by
    simpa [runMachineEvent] using (Option.some.inj checkRun).symm
  subst afterCheck
  obtain ⟨afterNonce, nonceAbsorbRun, suffixDone⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterNonceExact : afterNonce = prefixState := by
    simpa [runMachineEvents] using Option.some.inj suffixDone
  subst afterNonce
  let c1Input := bytes withC1SaltQuery.digest ++
    [domAbsorb, c1RootLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c1Root
        (exactOperationalTape input).messages.c1Root c1Salt).data
  let c2Input := bytes withC2SaltQuery.digest ++
    [domAbsorb, c2RootLabel] ++
      (AspisK1.V7Tag73TranscriptSchedule.Payload.c2Root
        (exactOperationalTape input).messages.c2.root c2Salt).data
  let final256Input := bytes beforeFinal256.digest ++
    [domAbsorb,
      (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
        (exactOperationalTape input).messages.finalValues).label] ++
    (AspisK1.V7Tag73TranscriptSchedule.Payload.final256
      (exactOperationalTape input).messages.finalValues).data
  let workInput := bytes beforeFinalWork.digest ++ [domGrind] ++
    bytes (exactOperationalTape input).messages.finalGrinding.selected
  let nonceInput := bytes beforeFinalWork.digest ++
    [domAbsorb, finalWorkNonceLabel] ++
    bytes (exactOperationalTape input).messages.finalGrinding.selected
  have c1Lookup : tableLookup (exactOperationalTable input) c1Input =
      some afterC1.digest := by
    simpa [c1Input, AspisK1.V7Tag73TranscriptSchedule.Payload.label] using
      absorb_step_exposes_literal_lookup (exactOperationalTable input)
        withC1SaltQuery afterC1
        (.c1Root (exactOperationalTape input).messages.c1Root c1Salt)
        c1AbsorbRun
  have c2Lookup : tableLookup (exactOperationalTable input) c2Input =
      some afterC2.digest := by
    simpa [c2Input, AspisK1.V7Tag73TranscriptSchedule.Payload.label] using
      absorb_step_exposes_literal_lookup (exactOperationalTable input)
        withC2SaltQuery afterC2
        (.c2Root (exactOperationalTape input).messages.c2.root c2Salt)
        c2AbsorbRun
  have final256Lookup : tableLookup (exactOperationalTable input)
      final256Input = some beforeFinalWork.digest := by
    simpa [final256Input] using absorb_step_exposes_literal_lookup
      (exactOperationalTable input) beforeFinal256 beforeFinalWork
      (.final256 (exactOperationalTape input).messages.finalValues)
      final256AbsorbRun
  obtain ⟨workAnswer, rawWorkLookup, workAccepted⟩ :=
    run_grinding_choice_exposes_selected_lookup
      (exactOperationalTable input) beforeFinalWork afterGrind .final
      (exactOperationalTape input).messages.finalGrinding grindRun
  have grindDigestExact : afterGrind.digest = beforeFinalWork.digest :=
    grinding_choice_does_not_advance (exactOperationalTable input)
      beforeFinalWork afterGrind .final
      (exactOperationalTape input).messages.finalGrinding grindRun
  have workLookup : tableLookup (exactOperationalTable input) workInput =
      some workAnswer := by
    simpa [workInput] using rawWorkLookup
  have rawNonceLookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) afterGrind prefixState
    (.finalNonce
      (exactOperationalTape input).messages.finalGrinding.selected)
    nonceAbsorbRun
  have nonceLookup : tableLookup (exactOperationalTable input) nonceInput =
      some prefixState.digest := by
    rw [grindDigestExact] at rawNonceLookup
    simpa [nonceInput, AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using rawNonceLookup
  have c2SaltStep := query_step_appends_one (exactOperationalTable input)
    afterPhaseChallenges withC2SaltQuery
    (.publicRootSalt (exactOperationalTape input).messages.context c2TreeTag)
    c2Salt (by simpa [rootSaltStep] using c2SaltRun)
  have c2BeforeExact : withC2SaltQuery.digest =
      afterPhaseChallenges.digest := by
    simpa [RawQueryRole.nextDigest] using c2SaltStep.2.2
  have c2Prefix : HasLiteralStatePrefix afterPhaseChallenges.digest c2Input := by
    unfold HasLiteralStatePrefix c2Input
    rw [c2BeforeExact]
    simp
  have c1BeforeC2 := exact_root_origin_before_post_events_lookup
    transitionRoom input c1Input c2Input afterC1.digest afterC2.digest
    [challengeEvent (exactOperationalTape input).messages .lambda,
     challengeEvent (exactOperationalTape input).messages .chi]
    afterC1 afterPhaseChallenges c1Lookup rfl phaseRun c2Lookup c2Prefix
  have final256Prefix : HasLiteralStatePrefix beforeFinal256.digest
      final256Input := by
    unfold HasLiteralStatePrefix final256Input
    simp
  have c2BeforeFinal256 := exact_root_origin_before_post_events_lookup
    transitionRoom input c2Input final256Input afterC2.digest
      beforeFinalWork.digest
    (prefixAfterC2BeforeFinal256 (exactOperationalTape input).messages)
    afterC2 beforeFinal256 c2Lookup rfl beforeFinal256Run final256Lookup
      final256Prefix
  have c1BeforeFinal256 := exact_root_pair_before_trans c1BeforeC2
    c2BeforeFinal256
  have final256BeforeWork : ExactRootPairBefore input
      (final256Input, beforeFinalWork.digest) (workInput, workAnswer) := by
    have dependency : HasLiteralStatePrefix beforeFinalWork.digest workInput := by
      unfold HasLiteralStatePrefix workInput
      simp
    simpa [ExactRootPairBefore] using
      exact_compiler_literal_dependency_has_strict_root_order transitionRoom
        input final256Input workInput beforeFinalWork.digest workAnswer
          final256Lookup workLookup dependency
  have final256BeforeNonce : ExactRootPairBefore input
      (final256Input, beforeFinalWork.digest)
      (nonceInput, prefixState.digest) := by
    have dependency : HasLiteralStatePrefix beforeFinalWork.digest nonceInput := by
      unfold HasLiteralStatePrefix nonceInput
      simp
    simpa [ExactRootPairBefore] using
      exact_compiler_literal_dependency_has_strict_root_order transitionRoom
        input final256Input nonceInput beforeFinalWork.digest prefixState.digest
          final256Lookup nonceLookup dependency
  have c1BeforeWork := exact_root_pair_before_trans c1BeforeFinal256
    final256BeforeWork
  have c2BeforeWork := exact_root_pair_before_trans c2BeforeFinal256
    final256BeforeWork
  have c1BeforeNonce := exact_root_pair_before_trans c1BeforeFinal256
    final256BeforeNonce
  have c2BeforeNonce := exact_root_pair_before_trans c2BeforeFinal256
    final256BeforeNonce
  exact ⟨withC1SaltQuery.digest, withC2SaltQuery.digest, c1Salt, c2Salt,
    afterC1.digest, afterC2.digest, beforeFinal256, beforeFinalWork.digest,
    workAnswer, prefixState.digest, c1Lookup, c2Lookup, final256Lookup,
    workLookup, workAccepted, nonceLookup, q16BaseExact, c1BeforeFinal256,
    c2BeforeFinal256, c1BeforeWork, c2BeforeWork, c1BeforeNonce,
    c2BeforeNonce⟩

#print axioms exact_root_fresh_queries_nodup
#print axioms exact_root_pair_before_trans
#print axioms exact_root_pair_before_or_eq_trans_before
#print axioms exact_root_ordered_chain_initial_before_terminal
#print axioms exact_root_order_through_machine_event
#print axioms exact_root_order_through_machine_events
#print axioms exact_root_origin_before_post_events_lookup
#print axioms exact_operational_root_absorbs_before_final256

end

end AspisK1.V7Tag73ExactLinearTranscriptRootOrder
