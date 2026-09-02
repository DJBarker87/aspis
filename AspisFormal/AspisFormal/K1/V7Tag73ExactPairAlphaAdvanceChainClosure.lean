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
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
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
      leftOutputs.length = rightOutputs.length := by
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
  exact ⟨leftBeforeAlpha.digest, rightBeforeAlpha.digest, leftOutputs,
    leftAdvances, rightOutputs, rightAdvances, initialExact, advancesExact,
    lengthsExact⟩

#print axioms exact_equal_root_priors_ordered_chain_advance_states_eq
#print axioms exact_fixed_clean_pair_k13_alpha_advance_states_eq

end

end AspisK1.V7Tag73ExactPairAlphaAdvanceChainClosure
