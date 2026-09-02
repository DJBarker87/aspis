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
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

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

#print axioms exact_equal_root_priors_ordered_chain_advance_states_eq

end

end AspisK1.V7Tag73ExactPairAlphaAdvanceChainClosure
