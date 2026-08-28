import AspisFormal.K1.V7Tag73K15SemanticSequentialRouter
import AspisFormal.K1.V7Tag73RelationTailSourceComposition
import AspisFormal.K1.V7Tag73CompleteCausalOrdinaryProbability
import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization
import AspisFormal.Pool.V7RelationCandidateBinding

/-!
# Four scheduler-native pre-alpha routers

Each deployed relation alpha is preceded by a unique verifier absorb marker:
alpha zero follows the accepted fold nonce, while alphas one through three
follow their corresponding relation-round payload.  This file recognizes
those literal markers from completed verifier history, tracks the bounded
ordinary duplex sampler through output/advance pairs, and instantiates four
independent causal coordinate routers on the actual plain-ROM cursor.

The collision target is also factored through a pre-alpha data view containing
only the claimed and honest coefficient families already constructed before
the challenge.  In particular, the target does not inspect the current alpha.

No probability statement and no source-equality provider is introduced here.
The remaining compiler/source boundary is whether a literal accepted verifier
call is a new `.machineFresh` exposure or a cached table lookup; the router
labels exactly the former, as required by `CausalSlotRouter`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.V7RelationCandidateBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
open AspisV5RelationSumcheckSoundness

noncomputable section

/-! ## Literal pre-alpha markers -/

/-- Decode a literal relation-round absorb and reject round zero.  The round
zero relation payload occurs before fold grinding; alpha zero is not sampled
until the later fold-nonce marker. -/
def laterRelationRoundOfInput? (input : ShaInput) : Option (Fin 4) :=
  if semanticAbsorbLabelOfInput? input = some relationRoundLabel then
    match input[34]? with
    | some round =>
        if 0 < round.toNat then
          if bounded : round.toNat < 4 then some ⟨round.toNat, bounded⟩
          else none
        else none
    | none => none
  else none

/-- The round whose ordinary alpha sampler starts after this completed input. -/
def relationAlphaMarkerOfInput? (input : ShaInput) : Option (Fin 4) :=
  if semanticAbsorbLabelOfInput? input = some foldWorkNonceLabel then
    some 0
  else
    laterRelationRoundOfInput? input

@[simp] theorem later_relation_round_of_literal_input
    (digest : Digest256) (round : Fin 4) (positive : 0 < round.val)
    (sent : Fin 6 → Qm31Bytes) :
    laterRelationRoundOfInput?
        (bytes digest ++ domAbsorb :: relationRoundLabel ::
          UInt8.ofNat round.val :: encodeBlocks sent) = some round := by
  have roundLt256 : round.val < 256 := lt_trans round.isLt (by omega)
  have roundMod : round.val % 256 = round.val := Nat.mod_eq_of_lt roundLt256
  have label : semanticAbsorbLabelOfInput?
      (bytes digest ++ domAbsorb :: relationRoundLabel ::
        UInt8.ofNat round.val :: encodeBlocks sent) =
      some relationRoundLabel := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      literal_semantic_absorb_label digest relationRoundLabel
        (UInt8.ofNat round.val :: encodeBlocks sent)
  unfold laterRelationRoundOfInput?
  rw [label]
  simp [roundMod, positive, round.isLt]

@[simp] theorem alpha_marker_of_literal_fold_nonce
    (digest : Digest256) (nonce : NonceBytes) :
    relationAlphaMarkerOfInput?
        (bytes digest ++ domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce) =
      some 0 := by
  have label : semanticAbsorbLabelOfInput?
      (bytes digest ++ domAbsorb :: foldWorkNonceLabel :: 0 :: bytes nonce) =
      some foldWorkNonceLabel := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      literal_semantic_absorb_label digest foldWorkNonceLabel (0 :: bytes nonce)
  simp [relationAlphaMarkerOfInput?, label]

@[simp] theorem alpha_marker_of_literal_later_relation
    (digest : Digest256) (round : Fin 4) (positive : 0 < round.val)
    (sent : Fin 6 → Qm31Bytes) :
    relationAlphaMarkerOfInput?
        (bytes digest ++ domAbsorb :: relationRoundLabel ::
          UInt8.ofNat round.val :: encodeBlocks sent) = some round := by
  have label : semanticAbsorbLabelOfInput?
      (bytes digest ++ domAbsorb :: relationRoundLabel ::
        UInt8.ofNat round.val :: encodeBlocks sent) =
      some relationRoundLabel := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      literal_semantic_absorb_label digest relationRoundLabel
        (UInt8.ofNat round.val :: encodeBlocks sent)
  unfold relationAlphaMarkerOfInput?
  rw [label]
  norm_num [foldWorkNonceLabel, relationRoundLabel]
  exact later_relation_round_of_literal_input digest round positive sent

/-! ## One round-local ordinary sampler phase -/

inductive RelationAlphaHistoryPhase where
  | inactive
  | output (priorOutputs : List Digest256)
  | advance (priorOutputs : List Digest256) (currentOutput : Digest256)
  deriving DecidableEq, Repr

/-- Reconstruct one selected round.  Markers for other rounds reset this local
phase, preventing any cross-round reuse of a realized challenge. -/
def RelationAlphaHistoryPhase.afterVerifierRecord
    (round : Fin 4) (phase : RelationAlphaHistoryPhase)
    (record : QueryRecord) : RelationAlphaHistoryPhase :=
  match relationAlphaMarkerOfInput? record.input with
  | some marked => if marked = round then .output [] else .inactive
  | none =>
      match phase with
      | .inactive => .inactive
      | .output priorOutputs =>
          if isSemanticSqueezeInput record.input then
            .advance priorOutputs record.output
          else .inactive
      | .advance priorOutputs currentOutput =>
          if isSemanticAdvanceInput record.input then
            let outputs := priorOutputs ++ [currentOutput]
            match decodeChallengeParameter exactSecureCircleParameterMap
                (.alpha round) outputs with
            | some _ => .inactive
            | none => .output outputs
          else .inactive

def relationAlphaHistoryPhase (round : Fin 4)
    (history : List QueryRecord) : RelationAlphaHistoryPhase :=
  history.foldl (fun phase record =>
    if record.actor = .verifier then
      phase.afterVerifierRecord round record
    else phase) .inactive

@[simp] theorem relation_alpha_history_phase_append_verifier
    (round : Fin 4) (history : List QueryRecord) (record : QueryRecord)
    (actor : record.actor = .verifier) :
    relationAlphaHistoryPhase round (history ++ [record]) =
      (relationAlphaHistoryPhase round history).afterVerifierRecord round
        record := by
  simp [relationAlphaHistoryPhase, actor]

@[simp] theorem relation_alpha_history_phase_append_nonverifier
    (round : Fin 4) (history : List QueryRecord) (record : QueryRecord)
    (actor : record.actor ≠ .verifier) :
    relationAlphaHistoryPhase round (history ++ [record]) =
      relationAlphaHistoryPhase round history := by
  simp [relationAlphaHistoryPhase, actor]

theorem RelationAlphaHistoryPhase.afterVerifierRecord_of_marker
    (round : Fin 4) (phase : RelationAlphaHistoryPhase)
    (record : QueryRecord)
    (marker : relationAlphaMarkerOfInput? record.input = some round) :
    phase.afterVerifierRecord round record = .output [] := by
  simp [RelationAlphaHistoryPhase.afterVerifierRecord, marker]

@[simp] theorem alpha_zero_phase_after_literal_fold_nonce
    (phase : RelationAlphaHistoryPhase) (digest output : Digest256)
    (nonce : NonceBytes) (origin : AnswerOrigin) :
    phase.afterVerifierRecord 0
        { input := bytes digest ++ [domAbsorb, foldWorkNonceLabel] ++
            ([0] ++ bytes nonce)
          output := output
          actor := .verifier
          origin := origin } = .output [] := by
  apply RelationAlphaHistoryPhase.afterVerifierRecord_of_marker
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    alpha_marker_of_literal_fold_nonce digest nonce

@[simp] theorem later_alpha_phase_after_literal_relation_round
    (phase : RelationAlphaHistoryPhase) (digest output : Digest256)
    (round : Fin 4) (positive : 0 < round.val)
    (sent : Fin 6 → Qm31Bytes) (origin : AnswerOrigin) :
    phase.afterVerifierRecord round
        { input := bytes digest ++ [domAbsorb, relationRoundLabel] ++
            ([UInt8.ofNat round.val] ++ encodeBlocks sent)
          output := output
          actor := .verifier
          origin := origin } = .output [] := by
  apply RelationAlphaHistoryPhase.afterVerifierRecord_of_marker
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    alpha_marker_of_literal_later_relation digest round positive sent

/-! ## Four exact compiler routers -/

/-- Four output halves and four advance halves for one alpha sampler. -/
abbrev RelationAlphaDuplexSlot := Fin 4 × Fin 2

theorem relation_alpha_duplex_slot_card :
    Fintype.card RelationAlphaDuplexSlot = 8 := by
  simp [RelationAlphaDuplexSlot]

/-- Split the eight routed answers into the four chronological decoder blocks
and four duplex-advance nuisance digests. -/
def relationAlphaDuplexTapeEquiv :
    (RelationAlphaDuplexSlot → Digest256) ≃
      FourGammaBlocks × Tag73OrdinaryAdvanceDigestGhosts where
  toFun tape :=
    (fun block => tape (block, 0), fun block => tape (block, 1))
  invFun tape slot :=
    if slot.2 = 0 then tape.1 slot.1 else tape.2 slot.1
  left_inv := by
    intro tape
    funext slot
    rcases slot with ⟨block, half⟩
    fin_cases half <;> simp
  right_inv := by
    intro tape
    apply Prod.ext
    · funext block
      simp
    · funext block
      simp

abbrev RelationAlphaTotalTape :=
  FourGammaBlocks × Tag73OrdinaryAdvanceDigestGhosts

def relationAlphaPreferredSlotFromHistory
    (round : Fin 4) (history : List QueryRecord) (input : ShaInput) :
    Option RelationAlphaDuplexSlot :=
  match relationAlphaHistoryPhase round history with
  | .output priorOutputs =>
      if isSemanticSqueezeInput input then
        if bounded : priorOutputs.length < 4 then
          some (⟨priorOutputs.length, bounded⟩, 0)
        else none
      else none
  | .advance priorOutputs _ =>
      if isSemanticAdvanceInput input then
        if bounded : priorOutputs.length < 4 then
          some (⟨priorOutputs.length, bounded⟩, 1)
        else none
      else none
  | .inactive => none

def schedulerRelationAlphaLabel
    {globalOracleCalls : Nat} (round : Fin 4) (transitionFuel : Nat) :
    UnifiedExposureCursor globalOracleCalls → Option RelationAlphaDuplexSlot :=
  fun cursor =>
    match seekUnifiedExposure transitionFuel cursor with
    | .machineFresh _limits _limitBound actor state input _nextProgram
        _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
        if actor = .verifier then
          relationAlphaPreferredSlotFromHistory round state.history input
        else none
    | .halted | .transitionLimit | .forkOutput .. | .forkAdvance .. => none

def relationAlphaSlotMachine
    {globalOracleCalls : Nat} (round : Fin 4) (transitionFuel : Nat) :
    PreAnswerSlotMachine Digest256 RelationAlphaDuplexSlot
      (UnifiedExposureCursor globalOracleCalls) where
  preferredSlot := schedulerRelationAlphaLabel round transitionFuel
  afterAnswer := unifiedCursorAfterAnswer transitionFuel

def relationAlphaRouterResidual
    (parameters : ExactCompilerResourceParameters) : Nat :=
  (exactCompilerTargetCaps parameters).length -
    Fintype.card RelationAlphaDuplexSlot

theorem relation_alpha_slots_fit_exact_compiler
    (parameters : ExactCompilerResourceParameters) :
    Fintype.card RelationAlphaDuplexSlot ≤
      (exactCompilerTargetCaps parameters).length := by
  rw [relation_alpha_duplex_slot_card, exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

theorem relation_alpha_slots_add_residual
    (parameters : ExactCompilerResourceParameters) :
    Fintype.card RelationAlphaDuplexSlot +
        relationAlphaRouterResidual parameters =
      (exactCompilerTargetCaps parameters).length := by
  unfold relationAlphaRouterResidual
  have fit := relation_alpha_slots_fit_exact_compiler parameters
  omega

/-- Parameterized constructor whose four literal specializations below are
the requested four pre-alpha routers. -/
def exactPlainRomRelationAlphaRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (round : Fin 4) (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  (relationAlphaSlotMachine round transitionFuel).fullRouter
    (relationAlphaRouterResidual parameters)
    (exactPlainRomExposureCursor configuration hidden)

def exactPlainRomRelationAlphaCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (round : Fin 4) (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      (RelationAlphaDuplexSlot → Digest256) ×
        FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters) :=
  (castFreshAnswerTape (relation_alpha_slots_add_residual parameters).symm).trans
    ((relationAlphaSlotMachine round transitionFuel).fullCoordinateEquiv
      (relationAlphaRouterResidual parameters)
      (exactPlainRomExposureCursor configuration hidden))

/-- Adapter-ready coordinate order: residual context first, followed by the
literal complete four-block ordinary attempt. -/
def exactPlainRomRelationAlphaSamplerCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (round : Fin 4) (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      FreshAnswerTape Digest256 (relationAlphaRouterResidual parameters) ×
        RelationAlphaTotalTape :=
  (exactPlainRomRelationAlphaCoordinates round transitionFuel configuration
      hidden).trans
    ((Equiv.prodCongr relationAlphaDuplexTapeEquiv (Equiv.refl _)).trans
      (Equiv.prodComm _ _))

def exactPlainRomAlphaZeroRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaRouter 0 transitionFuel configuration hidden

def exactPlainRomAlphaOneRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaRouter 1 transitionFuel configuration hidden

def exactPlainRomAlphaTwoRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaRouter 2 transitionFuel configuration hidden

def exactPlainRomAlphaThreeRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaRouter 3 transitionFuel configuration hidden

def exactPlainRomAlphaZeroSamplerCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaSamplerCoordinates 0 transitionFuel configuration
    hidden

def exactPlainRomAlphaOneSamplerCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaSamplerCoordinates 1 transitionFuel configuration
    hidden

def exactPlainRomAlphaTwoSamplerCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaSamplerCoordinates 2 transitionFuel configuration
    hidden

def exactPlainRomAlphaThreeSamplerCoordinates
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  exactPlainRomRelationAlphaSamplerCoordinates 3 transitionFuel configuration
    hidden

/-! ## Pre-alpha collision-target coherence -/

/-- All data read by the degree-six target before the current alpha. -/
structure RelationAlphaPreChallengeView (K : Type*) [Field K] where
  claimed : RelationCoefficients K
  honest : RelationCoefficients K

noncomputable def RelationAlphaPreChallengeView.collisionSet
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (view : RelationAlphaPreChallengeView K) : Finset K :=
  roundCollisionSet view.claimed view.honest

/-- Literal projection from a candidate execution; `execution.alpha round` is
not an argument to the projected target.  Previous alphas may legitimately
affect later-round claimed/honest state. -/
def relationAlphaPreChallengeView
    {K : Type*} [Field K] (execution : CandidateExecution K)
    (round : Fin 4) : RelationAlphaPreChallengeView K where
  claimed := execution.claimedAt round
  honest := execution.honestAt round

theorem relation_alpha_collision_set_is_prechallenge
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (execution : CandidateExecution K) (round : Fin 4) :
    (relationAlphaPreChallengeView execution round).collisionSet =
      execution.relationCollisionSet round := by
  rfl

/-- Source-side alpha coherence already follows from parser/projection data
for round zero and from translated continuation updates for rounds one to
three.  This theorem exposes that existing boundary next to the routers; it
does not add a provider premise. -/
theorem accepted_relation_source_alpha_coherence
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (source : ExactAcceptedTag73RelationSourceRun decoder input)
    (round : Fin 4) :
    source.execution.alpha round =
      exactOperationalChallenge input (.alpha round) :=
  source.alphaExact round

#print axioms laterRelationRoundOfInput?
#print axioms relationAlphaMarkerOfInput?
#print axioms RelationAlphaHistoryPhase.afterVerifierRecord
#print axioms relationAlphaHistoryPhase
#print axioms relationAlphaPreferredSlotFromHistory
#print axioms schedulerRelationAlphaLabel
#print axioms exactPlainRomRelationAlphaRouter
#print axioms exactPlainRomRelationAlphaCoordinates
#print axioms exactPlainRomRelationAlphaSamplerCoordinates
#print axioms exactPlainRomAlphaZeroRouter
#print axioms exactPlainRomAlphaOneRouter
#print axioms exactPlainRomAlphaTwoRouter
#print axioms exactPlainRomAlphaThreeRouter
#print axioms exactPlainRomAlphaZeroSamplerCoordinates
#print axioms exactPlainRomAlphaOneSamplerCoordinates
#print axioms exactPlainRomAlphaTwoSamplerCoordinates
#print axioms exactPlainRomAlphaThreeSamplerCoordinates
#print axioms relation_alpha_collision_set_is_prechallenge
#print axioms accepted_relation_source_alpha_coherence

end

end AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
