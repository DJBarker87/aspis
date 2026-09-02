import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant

/-!
# Cross-fibre alpha advance-chain closure

Starting from a common retained terminal answer, walk two accepted ordered
duplex chains backwards.  Root-answer uniqueness identifies predecessor
states; absorption-boundary/advance grammar separation rules out unequal
chain lengths.  No SHA-256 injectivity is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactPairAlphaAdvanceChainClosure

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedQ16VerifierAnchorInvariant
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPairTrialProbabilityClosure
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The deployed alpha-zero boundary absorption cannot be confused with a
duplex advance input.  Keeping this as a small nondependent lemma avoids
eliminating the producer witness inside the full accepted-run package. -/
theorem alpha_zero_boundary_ne_gamma_advance
    (messages : Messages) (producerInput : ShaInput)
    (boundary : ∃ (producerDigest : Digest256),
      producerInput = bytes producerDigest ++
        [domAbsorb, (alphaZeroBoundaryPayload messages).label] ++
        (alphaZeroBoundaryPayload messages).data) :
    ∀ state, producerInput ≠ gammaAdvanceInput state := by
  obtain ⟨producerDigest, producerExact⟩ := boundary
  intro state equal
  rw [producerExact] at equal
  have lengths := congrArg List.length equal
  simp [alphaZeroBoundaryPayload,
    AspisK1.V7Tag73TranscriptSchedule.Payload.data,
    gammaAdvanceInput] at lengths

/-- Erasing only the leading-zero check does not change the transcript digest
during a grinding search. -/
theorem grinding_choice_work_erased_does_not_advance
    (table : FixedOracleTable) (state next : EvalState)
    (stage : WorkStage) (choice : GrindingChoice stage)
    (run : runGrindingChoiceWorkErased table state stage choice = some next) :
    next.digest = state.digest := by
  rw [runGrindingChoiceWorkErased] at run
  obtain ⟨queried, probesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨selectedPair, selectedRun, result⟩ :=
    Option.bind_eq_some_iff.mp run
  rcases selectedPair with ⟨output, afterSelected⟩
  have nextExact : afterSelected = next := Option.some.inj result
  subst next
  exact (grind_probe_does_not_advance table queried afterSelected stage
    choice.selected output selectedRun).trans
      (grinding_probes_do_not_advance table stage choice.probesBeforeSelected
        state queried probesRun)

/-- The work-erased semantic prefix and the retained fold package identify
the same state before the selected fold-nonce absorption.  This is a source
schedule fact; it compares two lookups at one literal relation-round input. -/
theorem before_alpha_zero_producer_run_fixes_fold_digest
    (table : FixedOracleTable) (messages : Messages)
    (start beforeAlphaProducer beforeRelation : EvalState)
    (foldDigest : Digest256)
    (run : runMachineEventsWorkErased table
        (beforeAlphaZeroProducerTailEvents messages) start =
      some beforeAlphaProducer)
    (relationLookup : tableLookup table
        (bytes beforeRelation.digest ++
          [domAbsorb,
            (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
              (messages.relationSent 0)).label] ++
          (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
            (messages.relationSent 0)).data) = some foldDigest)
    (prefixRun : runMachineEventsWorkErased table
        (beforeGammaTailEvents messages ++
          [challengeEvent messages .gamma,
           .absorb (.inactiveClaim messages.inactiveClaim),
           challengeEvent messages .kappa] ++
          oodEvents messages) start = some beforeRelation) :
    beforeAlphaProducer.digest = foldDigest := by
  let prefixEvents := beforeGammaTailEvents messages ++
    [challengeEvent messages .gamma,
     .absorb (.inactiveClaim messages.inactiveClaim),
     challengeEvent messages .kappa] ++ oodEvents messages
  have eventsExact : beforeAlphaZeroProducerTailEvents messages =
      prefixEvents ++
        [.absorb (.relationRound 0 (messages.relationSent 0)),
         .grind .fold messages.foldGrinding,
         .check .foldWork] := by
    simp [beforeAlphaZeroProducerTailEvents, prefixEvents, List.append_assoc]
  rw [eventsExact] at run
  obtain ⟨middle, prefixRun', suffixRun⟩ :=
    (run_machine_events_work_erased_append_iff table prefixEvents _ start
      beforeAlphaProducer).mp run
  have middleExact : middle = beforeRelation := by
    have same : some middle = some beforeRelation := prefixRun'.symm.trans (by
      simpa [prefixEvents] using prefixRun)
    exact Option.some.inj same
  subst middle
  simp only [runMachineEventsWorkErased] at suffixRun
  obtain ⟨afterRelation, absorbRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨afterGrind, grindRun, suffixRun⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  obtain ⟨afterCheck, checkRun, done⟩ :=
    Option.bind_eq_some_iff.mp suffixRun
  have afterCheckExact : afterCheck = beforeAlphaProducer := by
    simpa [runMachineEventsWorkErased] using Option.some.inj done
  have checkExact : afterGrind = afterCheck := by
    simpa [runMachineEventWorkErased] using Option.some.inj checkRun
  have grindDigest : afterGrind.digest = afterRelation.digest :=
    grinding_choice_work_erased_does_not_advance table afterRelation
      afterGrind .fold messages.foldGrinding (by
        simpa [runMachineEventWorkErased] using grindRun)
  have literalLookup := absorb_step_exposes_literal_lookup table beforeRelation
    afterRelation (.relationRound 0 (messages.relationSent 0)) absorbRun
  have literalLookup' : tableLookup table
      (bytes beforeRelation.digest ++
        [domAbsorb,
          (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
            (messages.relationSent 0)).label] ++
        (AspisK1.V7Tag73TranscriptSchedule.Payload.relationRound 0
          (messages.relationSent 0)).data) = some afterRelation.digest := by
    simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using literalLookup
  have digestExact : afterRelation.digest = foldDigest := by
    apply Option.some.inj
    exact literalLookup'.symm.trans relationLookup
  rw [← afterCheckExact, ← checkExact, grindDigest, digestExact]

/-- Every consumed duplex output is looked up at the state in the matching
position of the initial/advance chain.  This is the pointwise bridge needed
by the pair proof: advance-state equality fixes the literal SHA input for
each output without making any claim about SHA-256 injectivity. -/
theorem exact_root_ordered_q16_chain_output_lookup_at_state
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
    ∀ index (inOutputs : index < outputs.length),
      let inStates : index < (digest :: advances).length := by
        have lengths := exact_root_ordered_q16_chain_lengths chain
        simp only [List.length_cons]
        omega
      tableLookup (exactOperationalTable input)
          (gammaOutputInput ((digest :: advances)[index]'inStates)) =
        some outputs[index] := by
  induction chain with
  | done producerInput digest producerFound =>
      intro index inOutputs
      simp at inOutputs
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail
      ih =>
      intro index inOutputs
      cases index with
      | zero =>
          simpa using outputFound
      | succ index =>
          have inTail : index < outputs.length := by
            simpa using inOutputs
          simpa using ih index inTail

/-- Equal initial/advance chains place the two literal output lookups at one
common SHA input, block by block.  The answers are deliberately not equated
here: that final step comes from the causal residual/named-coordinate replay,
not from treating SHA-256 as injective or as a function shared by fiat. -/
theorem exact_pair_ordered_chains_output_lookups_at_common_states
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    {leftInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance leftSample}
    {rightInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance rightSample}
    {leftProducerInput rightProducerInput : ShaInput}
    {leftInitial rightInitial : Digest256}
    {leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256}
    (leftChain : ExactRootOrderedQ16Chain leftInput leftProducerInput
      leftInitial leftOutputs leftAdvances)
    (rightChain : ExactRootOrderedQ16Chain rightInput rightProducerInput
      rightInitial rightOutputs rightAdvances)
    (initialExact : leftInitial = rightInitial)
    (advancesExact : leftAdvances = rightAdvances)
    (lengthsExact : leftOutputs.length = rightOutputs.length) :
    ∀ index (leftBound : index < leftOutputs.length),
      let rightBound : index < rightOutputs.length := by omega
      ∃ state,
        tableLookup (exactOperationalTable leftInput)
            (gammaOutputInput state) = some leftOutputs[index] ∧
          tableLookup (exactOperationalTable rightInput)
            (gammaOutputInput state) = some rightOutputs[index] := by
  subst rightInitial
  subst rightAdvances
  intro index leftBound
  have rightBound : index < rightOutputs.length := by omega
  have stateBound : index < (leftInitial :: leftAdvances).length := by
    have leftLengths := exact_root_ordered_q16_chain_lengths leftChain
    simp only [List.length_cons]
    omega
  let state := (leftInitial :: leftAdvances)[index]'stateBound
  refine ⟨state, ?_, ?_⟩
  · simpa [state] using
      exact_root_ordered_q16_chain_output_lookup_at_state leftChain index
        leftBound
  · simpa [state] using
      exact_root_ordered_q16_chain_output_lookup_at_state rightChain index
        rightBound

/-- Two ordered chains whose terminal producer records lie in equal canonical
root prefixes have identical advance-state chains.  Each initial producer is
required to be an absorption boundary, expressed by its disjointness from
every advance input. -/
theorem exact_equal_root_priors_ordered_chain_advance_states_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (leftInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance leftSample)
    (rightInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance rightSample)
    (leftPrior rightPrior leftLater rightLater : List UnifiedExposureRecord)
    (leftAnchor rightAnchor : UnifiedExposureRecord)
    (leftRootExact : exactFixedRootRecords leftInput.package.root =
      leftPrior ++ leftAnchor :: leftLater)
    (rightRootExact : exactFixedRootRecords rightInput.package.root =
      rightPrior ++ rightAnchor :: rightLater)
    (priorExact : leftPrior = rightPrior)
    (leftProducerInput rightProducerInput : ShaInput)
    (leftInitial rightInitial : Digest256)
    (leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256)
    (leftChain : ExactRootOrderedQ16Chain leftInput leftProducerInput
      leftInitial leftOutputs leftAdvances)
    (rightChain : ExactRootOrderedQ16Chain rightInput rightProducerInput
      rightInitial rightOutputs rightAdvances)
    (leftBoundary : ∀ state, leftProducerInput ≠ gammaAdvanceInput state)
    (rightBoundary : ∀ state, rightProducerInput ≠ gammaAdvanceInput state)
    (leftTerminalInput rightTerminalInput : ShaInput)
    (terminalAnswer : Digest256)
    (leftTerminalExact :
      gammaTerminalDigest leftInitial leftAdvances = terminalAnswer)
    (rightTerminalExact :
      gammaTerminalDigest rightInitial rightAdvances = terminalAnswer)
    (leftTerminalLookup : tableLookup (exactOperationalTable leftInput)
      leftTerminalInput = some terminalAnswer)
    (rightTerminalLookup : tableLookup (exactOperationalTable rightInput)
      rightTerminalInput = some terminalAnswer)
    (leftTerminalActor rightTerminalActor : QueryActor)
    (leftTerminalMember :
      (.machineFresh leftTerminalActor leftTerminalInput terminalAnswer :
        UnifiedExposureRecord) ∈ leftPrior)
    (rightTerminalMember :
      (.machineFresh rightTerminalActor rightTerminalInput terminalAnswer :
        UnifiedExposureRecord) ∈ rightPrior)
    (blockCap : Nat)
    (leftBound : leftOutputs.length ≤ blockCap)
    (rightBound : rightOutputs.length ≤ blockCap) :
    leftInitial = rightInitial ∧
      leftAdvances = rightAdvances ∧
      leftOutputs.length = rightOutputs.length := by
  induction blockCap generalizing leftProducerInput rightProducerInput
      leftInitial rightInitial leftOutputs leftAdvances rightOutputs
      rightAdvances leftTerminalInput rightTerminalInput terminalAnswer
      leftTerminalActor rightTerminalActor with
  | zero =>
      have leftOutputsEmpty : leftOutputs = [] :=
        List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero leftBound)
      have rightOutputsEmpty : rightOutputs = [] :=
        List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero rightBound)
      have leftAdvancesEmpty : leftAdvances = [] := by
        apply List.length_eq_zero_iff.mp
        rw [exact_root_ordered_q16_chain_lengths leftChain, leftOutputsEmpty]
        rfl
      have rightAdvancesEmpty : rightAdvances = [] := by
        apply List.length_eq_zero_iff.mp
        rw [exact_root_ordered_q16_chain_lengths rightChain, rightOutputsEmpty]
        rfl
      have leftInitialExact : leftInitial = terminalAnswer := by
        simpa [leftAdvancesEmpty, gammaTerminalDigest] using leftTerminalExact
      have rightInitialExact : rightInitial = terminalAnswer := by
        simpa [rightAdvancesEmpty, gammaTerminalDigest] using rightTerminalExact
      refine ⟨leftInitialExact.trans rightInitialExact.symm,
        by simp [leftAdvancesEmpty, rightAdvancesEmpty], by
        simp [leftOutputsEmpty, rightOutputsEmpty]⟩
  | succ cap ih =>
      by_cases leftEmpty : leftOutputs = []
      · by_cases rightEmpty : rightOutputs = []
        · have leftAdvancesEmpty : leftAdvances = [] := by
            apply List.length_eq_zero_iff.mp
            rw [exact_root_ordered_q16_chain_lengths leftChain, leftEmpty]
            rfl
          have rightAdvancesEmpty : rightAdvances = [] := by
            apply List.length_eq_zero_iff.mp
            rw [exact_root_ordered_q16_chain_lengths rightChain, rightEmpty]
            rfl
          have leftInitialExact : leftInitial = terminalAnswer := by
            simpa [leftAdvancesEmpty, gammaTerminalDigest] using leftTerminalExact
          have rightInitialExact : rightInitial = terminalAnswer := by
            simpa [rightAdvancesEmpty, gammaTerminalDigest] using rightTerminalExact
          refine ⟨leftInitialExact.trans rightInitialExact.symm,
            by simp [leftAdvancesEmpty, rightAdvancesEmpty], by
            simp [leftEmpty, rightEmpty]⟩
        · have rightPositive : 0 < rightOutputs.length :=
            Nat.pos_of_ne_zero (fun lengthZero =>
              rightEmpty (List.length_eq_zero_iff.mp lengthZero))
          obtain ⟨_rightPrefixOutputs, _rightPrefixAdvances,
              _rightBlockProducerInput, rightBlock, _rightBlockOutput,
              rightBlockAdvance, _rightProducerActor, rightAdvanceActor,
              _rightOutputsExact, _rightAdvancesExact, _rightPrefixChain,
              _rightProducerLookup, _rightOutputLookup, _rightAdvanceLookup,
              _rightPredecessorExact, rightAdvanceExact,
              _rightProducerMember, rightAdvanceMember⟩ :=
            exact_ordered_chain_predecessor_mem_of_terminal_record rightInput
              rightPrior rightLater rightAnchor rightRootExact
              rightProducerInput rightInitial rightOutputs rightAdvances
              rightChain rightPositive rightTerminalInput terminalAnswer
              rightTerminalExact rightTerminalLookup rightTerminalActor
              rightTerminalMember
          have rightAdvanceMember' :
              (.machineFresh rightAdvanceActor (gammaAdvanceInput rightBlock)
                  terminalAnswer : UnifiedExposureRecord) ∈ rightPrior := by
            simpa only [rightAdvanceExact] using rightAdvanceMember
          have terminalInputExact :
              leftTerminalInput = gammaAdvanceInput rightBlock :=
            exact_equal_root_priors_same_answer_input_eq leftInput leftPrior
              rightPrior leftTerminalActor rightAdvanceActor leftTerminalInput
              (gammaAdvanceInput rightBlock) terminalAnswer priorExact
              leftTerminalMember rightAdvanceMember' (by
                intro record member
                rw [leftRootExact]
                exact List.mem_append_left _ member)
          have leftTerminalProducer :=
            exact_empty_ordered_chain_terminal_input_eq_producer leftInput
              leftProducerInput leftInitial leftOutputs leftAdvances leftChain
              leftEmpty leftTerminalInput terminalAnswer leftTerminalExact
              leftTerminalLookup
          exact (leftBoundary rightBlock
            (leftTerminalProducer.symm.trans terminalInputExact)).elim
      · by_cases rightEmpty : rightOutputs = []
        · have leftPositive : 0 < leftOutputs.length :=
            Nat.pos_of_ne_zero (fun lengthZero =>
              leftEmpty (List.length_eq_zero_iff.mp lengthZero))
          obtain ⟨_leftPrefixOutputs, _leftPrefixAdvances,
              _leftBlockProducerInput, leftBlock, _leftBlockOutput,
              leftBlockAdvance, _leftProducerActor, leftAdvanceActor,
              _leftOutputsExact, _leftAdvancesExact, _leftPrefixChain,
              _leftProducerLookup, _leftOutputLookup, _leftAdvanceLookup,
              _leftPredecessorExact, leftAdvanceExact, _leftProducerMember,
              leftAdvanceMember⟩ :=
            exact_ordered_chain_predecessor_mem_of_terminal_record leftInput
              leftPrior leftLater leftAnchor leftRootExact leftProducerInput
              leftInitial leftOutputs leftAdvances leftChain leftPositive
              leftTerminalInput terminalAnswer leftTerminalExact
              leftTerminalLookup leftTerminalActor leftTerminalMember
          have leftAdvanceMember' :
              (.machineFresh leftAdvanceActor (gammaAdvanceInput leftBlock)
                  terminalAnswer : UnifiedExposureRecord) ∈ leftPrior := by
            simpa only [leftAdvanceExact] using leftAdvanceMember
          have terminalInputExact :
              gammaAdvanceInput leftBlock = rightTerminalInput :=
            exact_equal_root_priors_same_answer_input_eq leftInput leftPrior
              rightPrior leftAdvanceActor rightTerminalActor
              (gammaAdvanceInput leftBlock) rightTerminalInput terminalAnswer
              priorExact leftAdvanceMember' rightTerminalMember (by
                intro record member
                rw [leftRootExact]
                exact List.mem_append_left _ member)
          have rightTerminalProducer :=
            exact_empty_ordered_chain_terminal_input_eq_producer rightInput
              rightProducerInput rightInitial rightOutputs rightAdvances
              rightChain rightEmpty rightTerminalInput terminalAnswer
              rightTerminalExact rightTerminalLookup
          exact (rightBoundary leftBlock
            (rightTerminalProducer.symm.trans terminalInputExact.symm)).elim
        · have leftPositive : 0 < leftOutputs.length :=
            Nat.pos_of_ne_zero (fun lengthZero =>
              leftEmpty (List.length_eq_zero_iff.mp lengthZero))
          have rightPositive : 0 < rightOutputs.length :=
            Nat.pos_of_ne_zero (fun lengthZero =>
              rightEmpty (List.length_eq_zero_iff.mp lengthZero))
          obtain ⟨leftPrefixOutputs, leftPrefixAdvances,
              leftBlockProducerInput, leftBlock, leftBlockOutput,
              leftBlockAdvance, leftProducerActor, leftAdvanceActor,
              leftOutputsExact, leftAdvancesExact, leftPrefixChain,
              leftProducerLookup, _leftOutputLookup, _leftAdvanceLookup,
              leftPredecessorExact, leftAdvanceExact, leftProducerMember,
              leftAdvanceMember⟩ :=
            exact_ordered_chain_predecessor_mem_of_terminal_record leftInput
              leftPrior leftLater leftAnchor leftRootExact leftProducerInput
              leftInitial leftOutputs leftAdvances leftChain leftPositive
              leftTerminalInput terminalAnswer leftTerminalExact
              leftTerminalLookup leftTerminalActor leftTerminalMember
          obtain ⟨rightPrefixOutputs, rightPrefixAdvances,
              rightBlockProducerInput, rightBlock, rightBlockOutput,
              rightBlockAdvance, rightProducerActor, rightAdvanceActor,
              rightOutputsExact, rightAdvancesExact, rightPrefixChain,
              rightProducerLookup, _rightOutputLookup, _rightAdvanceLookup,
              rightPredecessorExact, rightAdvanceExact, rightProducerMember,
              rightAdvanceMember⟩ :=
            exact_ordered_chain_predecessor_mem_of_terminal_record rightInput
              rightPrior rightLater rightAnchor rightRootExact
              rightProducerInput rightInitial rightOutputs rightAdvances
              rightChain rightPositive rightTerminalInput terminalAnswer
              rightTerminalExact rightTerminalLookup rightTerminalActor
              rightTerminalMember
          have leftAdvanceMember' :
              (.machineFresh leftAdvanceActor (gammaAdvanceInput leftBlock)
                  terminalAnswer : UnifiedExposureRecord) ∈ leftPrior := by
            simpa only [leftAdvanceExact] using leftAdvanceMember
          have rightAdvanceMember' :
              (.machineFresh rightAdvanceActor (gammaAdvanceInput rightBlock)
                  terminalAnswer : UnifiedExposureRecord) ∈ rightPrior := by
            simpa only [rightAdvanceExact] using rightAdvanceMember
          have advanceInputExact : gammaAdvanceInput leftBlock =
              gammaAdvanceInput rightBlock :=
            exact_equal_root_priors_same_answer_input_eq leftInput leftPrior
              rightPrior leftAdvanceActor rightAdvanceActor
              (gammaAdvanceInput leftBlock) (gammaAdvanceInput rightBlock)
              terminalAnswer priorExact leftAdvanceMember' rightAdvanceMember'
              (by
                intro record member
                rw [leftRootExact]
                exact List.mem_append_left _ member)
          have blockExact : leftBlock = rightBlock :=
            advance_input_eq_implies_state_eq leftBlock rightBlock
              advanceInputExact
          have leftPrefixBound : leftPrefixOutputs.length ≤ cap := by
            rw [leftOutputsExact] at leftBound
            simp only [List.length_append, List.length_singleton] at leftBound
            omega
          have rightPrefixBound : rightPrefixOutputs.length ≤ cap := by
            rw [rightOutputsExact] at rightBound
            simp only [List.length_append, List.length_singleton] at rightBound
            omega
          have rightPredecessorExact' :
              gammaTerminalDigest rightInitial rightPrefixAdvances =
                leftBlock := rightPredecessorExact.trans blockExact.symm
          have rightProducerLookup' :
              tableLookup (exactOperationalTable rightInput)
                rightBlockProducerInput = some leftBlock := by
            simpa only [blockExact] using rightProducerLookup
          have rightProducerMember' :
              (.machineFresh rightProducerActor rightBlockProducerInput
                  leftBlock : UnifiedExposureRecord) ∈ rightPrior := by
            simpa only [blockExact] using rightProducerMember
          obtain ⟨initialExact, prefixAdvancesExact, prefixLengthsExact⟩ :=
            ih leftProducerInput rightProducerInput leftInitial rightInitial
              leftPrefixOutputs leftPrefixAdvances rightPrefixOutputs
              rightPrefixAdvances leftPrefixChain rightPrefixChain leftBoundary
              rightBoundary leftBlockProducerInput rightBlockProducerInput
              leftBlock leftPredecessorExact rightPredecessorExact'
              leftProducerLookup rightProducerLookup' leftProducerActor
              rightProducerActor leftProducerMember rightProducerMember'
              leftPrefixBound rightPrefixBound
          refine ⟨initialExact, ?_, ?_⟩
          · rw [leftAdvancesExact, rightAdvancesExact, prefixAdvancesExact,
              leftAdvanceExact, rightAdvanceExact]
          · rw [leftOutputsExact, rightOutputsExact]
            simp only [List.length_append, List.length_singleton]
            omega

/-- Deployed pair-specific corollary: equal non-q16 conditioning coordinates
fix the entire alpha-zero advance-state chain and consumed block count on the
adversary-anchor branch. -/
theorem exact_fixed_clean_pair_k13_alpha_advance_states_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactFixedCleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (anchor : ExactFixedK13AdversaryAnchor leftWitness.joint.input finalTrial)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).2.1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).2.1) :
    ∃ (leftInitial rightInitial : Digest256)
        (leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256),
      leftInitial = rightInitial ∧
      leftAdvances = rightAdvances ∧
      leftOutputs.length = rightOutputs.length ∧
      (∀ index (leftBound : index < leftOutputs.length),
        ∀ rightBound : index < rightOutputs.length,
        ∃ state,
          tableLookup (exactOperationalTable leftWitness.joint.input)
              (gammaOutputInput state) = some leftOutputs[index] ∧
            tableLookup (exactOperationalTable rightWitness.joint.input)
              (gammaOutputInput state) = some rightOutputs[index]) := by
  obtain ⟨leftProducer, rightProducer, leftFinal256Input, rightFinal256Input,
      leftBeforeAlpha, rightBeforeAlpha, leftAfterAlpha, rightAfterAlpha,
      _leftAfterBlocks, _rightAfterBlocks, _leftAfterFinal256,
      _rightAfterFinal256, leftOutputs, leftAdvances, rightOutputs,
      rightAdvances, _leftValue, _rightValue, prefinalDigest, leftPrior,
      rightPrior, leftLater, rightLater, leftAnchorRecord, rightAnchorRecord,
      leftChain, rightChain, leftBoundaryShape, rightBoundaryShape,
      leftPositive, rightPositive, _leftLengths, _rightLengths, leftTerminal,
      rightTerminal, leftAfterExact, rightAfterExact, alphaTerminalExact,
      _leftPrefinal, _rightPrefinal, _prefinalExact, leftFinal256Prefix,
      rightFinal256Prefix, leftFinal256Lookup, rightFinal256Lookup, priorExact,
      leftRootExact, rightRootExact, leftFinalMember, rightFinalMember,
      _leftDecode, _rightDecode, _leftOperational, _rightOperational⟩ :=
    exact_fixed_clean_pair_k13_adversary_anchor_alpha_terminal_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
      rightWitness anchor programmedCover contextExact foldExact
  have leftGammaTerminal :
      gammaTerminalDigest leftBeforeAlpha.digest leftAdvances =
        leftAfterAlpha.digest := leftTerminal.symm.trans leftAfterExact.symm
  have rightGammaTerminal :
      gammaTerminalDigest rightBeforeAlpha.digest rightAdvances =
        rightAfterAlpha.digest := rightTerminal.symm.trans rightAfterExact.symm
  have leftPrefix : HasLiteralStatePrefix
      (gammaTerminalDigest leftBeforeAlpha.digest leftAdvances)
        leftFinal256Input := by
    simpa only [leftGammaTerminal] using leftFinal256Prefix
  have rightPrefix : HasLiteralStatePrefix
      (gammaTerminalDigest rightBeforeAlpha.digest rightAdvances)
        rightFinal256Input := by
    simpa only [rightGammaTerminal] using rightFinal256Prefix
  obtain ⟨leftBlock, _leftOutput, leftAdvanceActor, _leftOutputLookup,
      leftAdvanceLookup, leftAdvanceMember⟩ :=
    exact_alpha_terminal_advance_mem_anchor_prior transitionRoom
      leftWitness.joint.input leftPrior leftLater leftAnchorRecord leftRootExact
      leftProducer leftBeforeAlpha.digest leftOutputs leftAdvances leftChain
      leftPositive leftFinal256Input prefinalDigest leftPrefix
      leftFinal256Lookup .adversary leftFinalMember
  obtain ⟨rightBlock, _rightOutput, rightAdvanceActor, _rightOutputLookup,
      rightAdvanceLookup, rightAdvanceMember⟩ :=
    exact_alpha_terminal_advance_mem_anchor_prior transitionRoom
      rightWitness.joint.input rightPrior rightLater rightAnchorRecord
      rightRootExact rightProducer rightBeforeAlpha.digest rightOutputs
      rightAdvances rightChain rightPositive rightFinal256Input prefinalDigest
      rightPrefix rightFinal256Lookup .adversary rightFinalMember
  have leftAdvanceLookup' :
      tableLookup (exactOperationalTable leftWitness.joint.input)
          (gammaAdvanceInput leftBlock) = some leftAfterAlpha.digest := by
    simpa only [leftGammaTerminal] using leftAdvanceLookup
  have leftAdvanceMember' :
      (.machineFresh leftAdvanceActor (gammaAdvanceInput leftBlock)
          leftAfterAlpha.digest : UnifiedExposureRecord) ∈ leftPrior := by
    simpa only [leftGammaTerminal] using leftAdvanceMember
  have rightTerminalExact' :
      gammaTerminalDigest rightBeforeAlpha.digest rightAdvances =
        leftAfterAlpha.digest := rightGammaTerminal.trans alphaTerminalExact.symm
  have rightAdvanceLookup' :
      tableLookup (exactOperationalTable rightWitness.joint.input)
          (gammaAdvanceInput rightBlock) = some leftAfterAlpha.digest := by
    simpa only [rightGammaTerminal, alphaTerminalExact] using rightAdvanceLookup
  have rightAdvanceMember' :
      (.machineFresh rightAdvanceActor (gammaAdvanceInput rightBlock)
          leftAfterAlpha.digest : UnifiedExposureRecord) ∈ rightPrior := by
    simpa only [rightGammaTerminal, alphaTerminalExact] using rightAdvanceMember
  have leftBoundary : ∀ state,
      leftProducer ≠ gammaAdvanceInput state :=
    alpha_zero_boundary_ne_gamma_advance
      (exactOperationalTape leftWitness.joint.input).messages leftProducer
      leftBoundaryShape
  have rightBoundary : ∀ state,
      rightProducer ≠ gammaAdvanceInput state :=
    alpha_zero_boundary_ne_gamma_advance
      (exactOperationalTape rightWitness.joint.input).messages rightProducer
      rightBoundaryShape
  obtain ⟨initialExact, advancesExact, lengthsExact⟩ :=
    exact_equal_root_priors_ordered_chain_advance_states_eq
      leftWitness.joint.input rightWitness.joint.input leftPrior rightPrior
      leftLater rightLater leftAnchorRecord rightAnchorRecord leftRootExact
      rightRootExact priorExact leftProducer rightProducer
      leftBeforeAlpha.digest rightBeforeAlpha.digest leftOutputs leftAdvances
      rightOutputs rightAdvances leftChain rightChain leftBoundary rightBoundary
      (gammaAdvanceInput leftBlock) (gammaAdvanceInput rightBlock)
      leftAfterAlpha.digest leftGammaTerminal rightTerminalExact'
      leftAdvanceLookup' rightAdvanceLookup' leftAdvanceActor rightAdvanceActor
      leftAdvanceMember' rightAdvanceMember'
      (leftOutputs.length + rightOutputs.length) (by omega) (by omega)
  have pointwise :=
    exact_pair_ordered_chains_output_lookups_at_common_states leftChain
      rightChain initialExact advancesExact lengthsExact
  have pointwise' : ∀ index (leftBound : index < leftOutputs.length),
      ∀ rightBound : index < rightOutputs.length,
        ∃ state,
          tableLookup (exactOperationalTable leftWitness.joint.input)
              (gammaOutputInput state) = some leftOutputs[index] ∧
            tableLookup (exactOperationalTable rightWitness.joint.input)
              (gammaOutputInput state) = some rightOutputs[index] := by
    intro index leftBound rightBound
    exact pointwise index leftBound
  exact ⟨leftBeforeAlpha.digest, rightBeforeAlpha.digest, leftOutputs,
    leftAdvances, rightOutputs, rightAdvances, initialExact, advancesExact,
    lengthsExact, pointwise'⟩

#print axioms grinding_choice_work_erased_does_not_advance
#print axioms before_alpha_zero_producer_run_fixes_fold_digest
#print axioms exact_root_ordered_q16_chain_output_lookup_at_state
#print axioms exact_pair_ordered_chains_output_lookups_at_common_states
#print axioms exact_equal_root_priors_ordered_chain_advance_states_eq
#print axioms exact_fixed_clean_pair_k13_alpha_advance_states_eq

end

end AspisK1.V7Tag73ExactPairAlphaAdvanceChainClosure
