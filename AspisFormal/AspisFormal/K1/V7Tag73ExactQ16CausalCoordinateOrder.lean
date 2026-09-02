import AspisFormal.K1.V7Tag73ExactRootLookupCausalOrder
import AspisFormal.K1.V7Tag73ExactCompilerQ16BranchCoordinates
import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence

/-!
# Exact causal order of every used q16 coordinate

The strict source evaluator supplies the literal candidate absorb and duplex
table lookups.  This module proves that the absorb answer precedes both block
zero siblings, and every advance answer precedes both siblings of the next
block, in the actual adversary-then-verifier root chronology.  Sibling order
itself remains arbitrary, matching the order-robust controller.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactQ16CausalCoordinateOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ActualQ16InitialDigest
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerQ16BranchCoordinates
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Every candidate retained at the exact evaluator's post-q16 state uses the
single q16 base recorded by the returned strict trace. -/
theorem exact_operational_q16_after_state_uses_shared_base
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
    ∀ record ∈ (exactOperationalQ16Evaluator input).afterQ16.candidates,
      record.baseDigest = (exactOperationalRawTrace input).q16BaseDigest := by
  let evaluator := exactOperationalQ16Evaluator input
  have wellFormed : TraceWellFormed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input) :=
    (checked_refinement_is_well_formed (exactOperationalTable input)
      exactDeterministicDecoders (exactOperationalTape input)
      (exactOperationalRawTrace input)
      input.package.root.fixedRoot.base.strictRefinement).2
  have included : CandidatesIncluded evaluator.afterQ16 evaluator.finalState :=
    machine_events_work_erased_candidates_included (exactOperationalTable input)
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState evaluator.afterQ16Run
  have candidatesExact : evaluator.finalState.candidates =
      (exactOperationalRawTrace input).candidates := by
    simpa [evaluator] using congrArg InteractiveRawTrace.candidates
      evaluator.rawTraceEq
  intro record member
  apply wellFormed.clonedCandidateBase record
  rw [← candidatesExact]
  exact included record member

/-- The literal candidate-counter absorb lookup starts from the shared q16
base and returns the canonical initial digest selected for that branch. -/
theorem exact_operational_q16_candidate_absorb_lookup
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
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    tableLookup (exactOperationalTable input)
        (bytes (exactOperationalRawTrace input).q16BaseDigest ++
          [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val]) =
      some (exactOperationalQ16InitialDigest input counter) := by
  let evaluator := exactOperationalQ16Evaluator input
  let witness := Classical.choice
    (accepted_q16_run_exposes_initial_digest (exactOperationalTable input)
      evaluator.prefixState evaluator.afterQ16
      (exactOperationalTape input).search evaluator.q16Run counter
      beforeSelected)
  obtain ⟨afterCounter, outputs, afterBlocks, absorbRun, squeezeRun,
      _afterExact, _outputsLength, recordMember⟩ :=
    run_candidate_exposes_exact_record (exactOperationalTable input)
      witness.before witness.after
      { counter := counter,
        outcome := (exactOperationalTape input).search.outcome counter }
      witness.candidateRun
  have afterCounterExact : afterCounter = witness.afterCounter := by
    apply Option.some.inj
    exact absorbRun.symm.trans witness.absorbRun
  let record : CandidateRecord :=
    { counter := counter
      outcome := (exactOperationalTape input).search.outcome counter
      baseDigest := witness.before.digest
      endDigest := afterBlocks.digest
      blocks := outputs }
  have recordInAfter : record ∈ witness.after.candidates := by
    simpa [record] using recordMember
  have recordInAfterQ16 : record ∈ evaluator.afterQ16.candidates :=
    witness.afterIncluded record recordInAfter
  have baseExact : witness.before.digest =
      (exactOperationalRawTrace input).q16BaseDigest := by
    simpa [record, evaluator] using
      exact_operational_q16_after_state_uses_shared_base input record
        recordInAfterQ16
  have initialExact : witness.afterCounter.digest =
      exactOperationalQ16InitialDigest input counter := by
    simp [exactOperationalQ16InitialDigest, acceptedQ16InitialDigest,
      beforeSelected, evaluator, witness]
  have lookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) witness.before witness.afterCounter
      (.queryCandidate counter) witness.absorbRun
  rw [baseExact, initialExact] at lookup
  simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
    AspisK1.V7Tag73TranscriptSchedule.Payload.data,
    List.append_assoc] using lookup

/-- A recursive certificate that names the query producing the current digest
and retains strict root order to both sibling queries of every used block. -/
inductive ExactRootOrderedQ16Chain
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
    ShaInput → Digest256 → List Digest256 → List Digest256 → Prop where
  | done (producerInput : ShaInput) (digest : Digest256)
      (producerFound : tableLookup (exactOperationalTable input) producerInput =
        some digest) :
      ExactRootOrderedQ16Chain input producerInput digest [] []
  | next {producerInput : ShaInput} {digest output advanced : Digest256}
      {outputs advances : List Digest256}
      (producerFound : tableLookup (exactOperationalTable input) producerInput =
        some digest)
      (outputFound : tableLookup (exactOperationalTable input)
        (gammaOutputInput digest) = some output)
      (advanceFound : tableLookup (exactOperationalTable input)
        (gammaAdvanceInput digest) = some advanced)
      (producerBeforeOutput : ∃ before middle after,
        exactRootFreshQueries input =
          before ++ (producerInput, digest) :: middle ++
            (gammaOutputInput digest, output) :: after)
      (producerBeforeAdvance : ∃ before middle after,
        exactRootFreshQueries input =
          before ++ (producerInput, digest) :: middle ++
            (gammaAdvanceInput digest, advanced) :: after)
      (tail : ExactRootOrderedQ16Chain input
        (gammaAdvanceInput digest) advanced outputs advances) :
      ExactRootOrderedQ16Chain input producerInput digest
        (output :: outputs) (advanced :: advances)

/-- Every ordered chain retains the lookup that produced its initial state. -/
theorem exact_root_ordered_q16_chain_producer_lookup
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
      advances) :
    tableLookup (exactOperationalTable input) producerInput = some digest := by
  cases chain <;> assumption

/-- Root ordering preserves the one-output/one-advance shape of every
consumed duplex block. -/
theorem exact_root_ordered_q16_chain_lengths
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
      advances) :
    advances.length = outputs.length := by
  induction chain with
  | done => rfl
  | next _ _ _ _ _ tail ih => simp [ih]

/-- A nonempty ordered chain exposes the last consumed output/advance pair in
the literal root chronology.  The advance answer is exactly the terminal
digest.  This is the reverse-induction handle used to transport a sampler
chain from its already-fixed successor state. -/
theorem exact_root_ordered_q16_chain_terminal_pair_mem
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
    ∃ blockDigest blockOutput,
      tableLookup (exactOperationalTable input)
          (gammaOutputInput blockDigest) = some blockOutput ∧
      tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) =
        some (gammaTerminalDigest digest advances) ∧
      (gammaOutputInput blockDigest, blockOutput) ∈
          exactRootFreshQueries input ∧
      (gammaAdvanceInput blockDigest,
          gammaTerminalDigest digest advances) ∈
        exactRootFreshQueries input := by
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
        refine ⟨digest, output, outputFound, ?_, ?_, ?_⟩
        · simpa [gammaTerminalDigest] using advanceFound
        · obtain ⟨before, middle, after, rootExact⟩ := producerBeforeOutput
          rw [rootExact]
          simp
        · obtain ⟨before, middle, after, rootExact⟩ := producerBeforeAdvance
          rw [rootExact]
          simp [gammaTerminalDigest]
      · have tailLengthNe : outputs.length ≠ 0 := by
          intro lengthZero
          exact outputsEmpty (List.length_eq_zero_iff.mp lengthZero)
        have tailNonempty : 0 < outputs.length := by omega
        obtain ⟨blockDigest, blockOutput, outputLookup, advanceLookup,
          outputMember, advanceMember⟩ := ih tailNonempty
        exact ⟨blockDigest, blockOutput, outputLookup, by
          simpa [gammaTerminalDigest] using advanceLookup, outputMember, by
          simpa [gammaTerminalDigest] using advanceMember⟩

/-- A nonempty ordered duplex chain can be peeled at its final block while
retaining an exact ordered certificate for the preceding blocks.  This is the
proof-relevant `unsnoc` operation needed for backwards transcript transport:
the predecessor digest and both final table lookups are exposed without
assuming that SHA-256 itself is injective. -/
theorem exact_root_ordered_q16_chain_unsnoc
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
    ∃ prefixOutputs prefixAdvances blockDigest blockOutput blockAdvance,
      outputs = prefixOutputs ++ [blockOutput] ∧
      advances = prefixAdvances ++ [blockAdvance] ∧
      ExactRootOrderedQ16Chain input producerInput digest prefixOutputs
        prefixAdvances ∧
      tableLookup (exactOperationalTable input)
        (gammaOutputInput blockDigest) = some blockOutput ∧
      tableLookup (exactOperationalTable input)
        (gammaAdvanceInput blockDigest) = some blockAdvance ∧
      gammaTerminalDigest digest prefixAdvances = blockDigest ∧
      gammaTerminalDigest digest advances = blockAdvance := by
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
        exact ⟨[], [], digest, output, advanced, rfl, rfl,
          .done producerInput digest producerFound, outputFound, advanceFound,
          rfl, rfl⟩
      · have tailNonempty : 0 < outputs.length := by
          exact Nat.pos_of_ne_zero (fun lengthZero =>
            outputsEmpty (List.length_eq_zero_iff.mp lengthZero))
        obtain ⟨prefixOutputs, prefixAdvances, blockDigest, blockOutput,
            blockAdvance, outputsExact, advancesExact, prefixChain,
            outputLookup, advanceLookup, predecessorExact, terminalExact⟩ :=
          ih tailNonempty
        refine ⟨output :: prefixOutputs, advanced :: prefixAdvances,
          blockDigest, blockOutput, blockAdvance, ?_, ?_, ?_, outputLookup,
          advanceLookup, ?_, ?_⟩
        · simp only [List.cons_append]
          rw [outputsExact]
        · simp only [List.cons_append]
          rw [advancesExact]
        · exact .next producerFound outputFound advanceFound
            producerBeforeOutput producerBeforeAdvance prefixChain
        · simpa [gammaTerminalDigest] using predecessorExact
        · rw [advancesExact]
          exact gamma_terminal_digest_append_singleton digest blockAdvance
            (advanced :: prefixAdvances)

/-- Ordered form of `exact_root_ordered_q16_chain_unsnoc`.  In addition to
the shortened chain it retains the literal query producing the final block
state and its strict root order before the final advance query.  That order is
what lets a backwards cross-fibre proof move pre-anchor membership from the
successor answer to its predecessor without assuming SHA-256 injectivity. -/
theorem exact_root_ordered_q16_chain_unsnoc_with_order
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
    ∃ prefixOutputs prefixAdvances blockProducerInput blockDigest blockOutput
        blockAdvance,
      outputs = prefixOutputs ++ [blockOutput] ∧
      advances = prefixAdvances ++ [blockAdvance] ∧
      ExactRootOrderedQ16Chain input producerInput digest prefixOutputs
        prefixAdvances ∧
      tableLookup (exactOperationalTable input) blockProducerInput =
        some blockDigest ∧
      tableLookup (exactOperationalTable input)
        (gammaOutputInput blockDigest) = some blockOutput ∧
      tableLookup (exactOperationalTable input)
        (gammaAdvanceInput blockDigest) = some blockAdvance ∧
      (∃ before middle after,
        exactRootFreshQueries input =
          before ++ (blockProducerInput, blockDigest) :: middle ++
            (gammaAdvanceInput blockDigest, blockAdvance) :: after) ∧
      gammaTerminalDigest digest prefixAdvances = blockDigest ∧
      gammaTerminalDigest digest advances = blockAdvance := by
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
        exact ⟨[], [], producerInput, digest, output, advanced, rfl, rfl,
          .done producerInput digest producerFound, producerFound, outputFound,
          advanceFound, producerBeforeAdvance, rfl, rfl⟩
      · have tailNonempty : 0 < outputs.length := by
          exact Nat.pos_of_ne_zero (fun lengthZero =>
            outputsEmpty (List.length_eq_zero_iff.mp lengthZero))
        obtain ⟨prefixOutputs, prefixAdvances, blockProducerInput,
            blockDigest, blockOutput, blockAdvance, outputsExact,
            advancesExact, prefixChain, producerLookup, outputLookup,
            advanceLookup, producerOrder, predecessorExact, terminalExact⟩ :=
          ih tailNonempty
        refine ⟨output :: prefixOutputs, advanced :: prefixAdvances,
          blockProducerInput, blockDigest, blockOutput, blockAdvance, ?_, ?_,
          ?_, producerLookup, outputLookup, advanceLookup, producerOrder, ?_,
          ?_⟩
        · simp only [List.cons_append]
          rw [outputsExact]
        · simp only [List.cons_append]
          rw [advancesExact]
        · exact .next producerFound outputFound advanceFound
            producerBeforeOutput producerBeforeAdvance prefixChain
        · simpa [gammaTerminalDigest] using predecessorExact
        · rw [advancesExact]
          exact gamma_terminal_digest_append_singleton digest blockAdvance
            (advanced :: prefixAdvances)

/-- Every literal evaluator duplex chain has the exact strict root ordering
required by the causal controller. -/
theorem gamma_table_coordinate_chain_has_exact_root_order
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
    (producerInput : ShaInput) (digest : Digest256)
    (producerFound : tableLookup (exactOperationalTable input) producerInput =
      some digest) {outputs advances : List Digest256}
    (chain : GammaTableCoordinateChain (exactOperationalTable input) digest
      outputs advances) :
    ExactRootOrderedQ16Chain input producerInput digest outputs advances := by
  induction chain generalizing producerInput with
  | done digest =>
      exact .done producerInput digest producerFound
  | @next digest output advanced outputs advances outputFound advanceFound
      tail ih =>
      have outputDependency :
          HasLiteralStatePrefix digest (gammaOutputInput digest) := by
        simp [HasLiteralStatePrefix, gammaOutputInput]
      have advanceDependency :
          HasLiteralStatePrefix digest (gammaAdvanceInput digest) := by
        simp [HasLiteralStatePrefix, gammaAdvanceInput]
      have outputOrder :=
        exact_compiler_literal_dependency_has_strict_root_order transitionRoom
          input producerInput (gammaOutputInput digest) digest output
          producerFound outputFound outputDependency
      have advanceOrder :=
        exact_compiler_literal_dependency_has_strict_root_order transitionRoom
          input producerInput (gammaAdvanceInput digest) digest advanced
          producerFound advanceFound advanceDependency
      exact .next producerFound outputFound advanceFound outputOrder
        advanceOrder (ih (gammaAdvanceInput digest) advanceFound)

/-- Production specialization for every branch through the selected q16
counter.  The first producer is the shared-base candidate absorb. -/
theorem exact_operational_q16_branch_has_exact_root_order
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
    (counter : Fin 64)
    (beforeSelected : counter.val ≤
      (exactOperationalTape input).search.selectedCounter.val) :
    ExactRootOrderedQ16Chain input
      (bytes (exactOperationalRawTrace input).q16BaseDigest ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])
      (exactOperationalQ16InitialDigest input counter)
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).outputs
      (exactOperationalQ16BranchCoordinates input counter
        beforeSelected).advances := by
  exact gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
    (bytes (exactOperationalRawTrace input).q16BaseDigest ++
      [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val])
    (exactOperationalQ16InitialDigest input counter)
    (exact_operational_q16_candidate_absorb_lookup input counter
      beforeSelected)
    (exactOperationalQ16BranchCoordinates input counter
      beforeSelected).tableChain

#print axioms exact_operational_q16_after_state_uses_shared_base
#print axioms exact_operational_q16_candidate_absorb_lookup
#print axioms exact_root_ordered_q16_chain_lengths
#print axioms exact_root_ordered_q16_chain_producer_lookup
#print axioms exact_root_ordered_q16_chain_terminal_pair_mem
#print axioms exact_root_ordered_q16_chain_unsnoc
#print axioms exact_root_ordered_q16_chain_unsnoc_with_order
#print axioms gamma_table_coordinate_chain_has_exact_root_order
#print axioms exact_operational_q16_branch_has_exact_root_order

end

end AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
