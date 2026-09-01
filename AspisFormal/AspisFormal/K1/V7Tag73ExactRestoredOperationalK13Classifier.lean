import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73CurrentSourceDecodeBridge
import AspisFormal.K1.V7Tag73RestoredDerivedK13View
import AspisFormal.K1.V7Tag73RestoredQ16LedgerInvariant

/-!
# Exact restoration-wide operational K1.3 classifier

The original fixed-run K1.3 classifier consumes the parser-owned root proof.
That is not the correct endpoint for the state-restoring K1.6 extractor: the
completed client contains the root and every successful same-tape restored
execution, and a future q16 coordinate may first have been queried by the
adversary.

This leaf makes the corrected endpoint proof relevant.  A source provider
supplies only the canonically decoded fixed fields for every stored accepting
node.  Gamma, alpha zero, and q16 are derived from the retained executable
verifier state rather than opaque parsed fields.

The total classifier returns either one actual stored-node K1.3 certificate or
an exact typed K1.3 error for every stored accepting node.  It contains no
probability bound, witness, acceptance oracle, or caller-selected query
schedule.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK13Classifier

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73CurrentSourceDecodeBridge
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredQ16LedgerInvariant
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73FixedFieldMessageBridge
open AspisK1.V7Tag73Q16LedgerCertificate
open AspisK1.V7Tag73Q16LedgerControlInvariant
open AspisK1.V7Tag73ChallengeRecordControlInvariant
open AspisK1.V7Tag73ChallengeRecordUniquenessInvariant
open AspisK1.V7Tag73SecureCircleMap
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Operational nonvacuity and verifier-owned q16 data -/

/-- The literal accepted root remains node zero in the completed append-only
store.  This is recovered from the completed full-run projection rather than
assumed by the K1.3 data provider. -/
theorem exact_restoration_accumulator_contains_root
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
    input.package.root.fixedRoot.base.runtime.node ∈
      (exactRestorationAccumulator input).nodes := by
  have lookup :=
    input.package.root.full.projection.nodeStoreInvariant.1
  change (exactRestorationAccumulator input).nodes[0]? =
    some input.package.root.fixedRoot.base.runtime.node at lookup
  rw [List.getElem?_eq_some_iff] at lookup
  rcases lookup with ⟨within, valueExact⟩
  have member := List.getElem_mem within
  rw [valueExact] at member
  exact member

/-- Strict checked-source acceptance and actual-run alignment force the
stored root to be schedule-exhausted.  Hence restoration-wide K1.3 failure
can never become vacuous merely because the client produced no children. -/
theorem exact_restoration_accumulator_root_is_done
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
    input.package.root.fixedRoot.base.runtime.node.verifierFinalState.current.control =
      .done := by
  have exhausted :=
    input.package.root.fixedRoot.base.actualPathAlignment.scheduleExhausted
  unfold FutureFreeScheduleExhausted at exhausted
  rw [input.package.root.fixedRoot.base.projected.finalStateExact] at exhausted
  change input.package.root.fixedRoot.base.runtime.verifierFinalState.current.control =
    .done
  exact exhausted

/-- Every accepting node in the actual returned store has its exact
first-cap-203 verifier ledger.  The q16 schedule is therefore no longer a
source/parser obligation. -/
noncomputable def exact_restored_done_node_selected_q16_ledger
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
    (node : RestoredK13Node Statement Payload)
    (member : node ∈ (exactRestorationAccumulator input).nodes)
    (done : node.verifierFinalState.current.control = .done) :
    SelectedQ16LedgerCertificate configuration.machine.environment
      node.verifierFinalState.current := by
  exact Classical.choice
    (done_state_has_selected_q16_ledger configuration.machine.environment
      node.verifierFinalState
      (input.stateMap.everyNodeQ16LedgerInvariant node member) done)

/-- The only per-node K1.3 data not already forced by the operational state
map is canonical fixed-field decoding.  Gamma, alpha zero, and q16 are all
verifier-owned consequences of the exact restored controller trace. -/
structure ExactRestoredOperationalK13SourceNodeData
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) where
  decoded : Fin 641 → QM31Exact
  fixedFields : CurrentSourceFixedFieldProjection
    node.adversaryValue.rawMessages decoded

/-- The checked raw-prover refinement supplies the sole source datum needed
by K1.3 for every literal restoration node.  No per-node acceptance or source
oracle is required: invalid packed field encodings are excluded by the same
canonical reader check that precedes deployed transcript verification. -/
noncomputable def exact_restored_operational_k13_source_node_data
    {Statement Payload : Type*}
    (node : RestoredK13Node Statement Payload) :
    ExactRestoredOperationalK13SourceNodeData node := by
  have decodeExists :=
    V7Tag73RawSameTapeSource.checked_raw_return_has_exact_fixed_field_decode
      node.adversaryValue
  let decoded := Classical.choose decodeExists
  have decodeExact := Classical.choose_spec decodeExists
  exact
    { decoded := decoded
      fixedFields :=
        fixed_field_decode_implies_current_source_projection decodeExact }

/-- Operational state supplies q16; the source node data supplies only the
canonical field/challenge bytes.  Their composition is the corrected K1.3
view consumed by the total classifier. -/
noncomputable def exact_restored_operational_k13_data_of_source_node
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
    (node : RestoredK13Node Statement Payload)
    (member : node ∈ (exactRestorationAccumulator input).nodes)
    (done : node.verifierFinalState.current.control = .done)
    (source : ExactRestoredOperationalK13SourceNodeData node) :
    RestoredOperationalK13Data configuration.machine.environment node := by
  have challengeInvariant :=
    input.stateMap.everyNodeK13ChallengeInvariant node member
  obtain ⟨gammaExact, alphaZeroExact⟩ :=
    done_state_has_exact_gamma_alpha_zero node.verifierFinalState
      challengeInvariant done
  let gammaBytes := Classical.choose gammaExact
  have gammaValueExists := Classical.choose_spec gammaExact
  let gamma := Classical.choose gammaValueExists
  have gammaFacts := Classical.choose_spec gammaValueExists
  let alphaZeroBytes := Classical.choose alphaZeroExact
  have alphaZeroValueExists := Classical.choose_spec alphaZeroExact
  let alphaZero := Classical.choose alphaZeroValueExists
  have alphaZeroFacts := Classical.choose_spec alphaZeroValueExists
  exact restored_operational_k13_data_of_selected_ledger source.decoded
    (current_source_fixed_field_projection_implies_decode source.fixedFields)
    gamma gammaBytes gammaFacts.1 gammaFacts.2 alphaZero
    alphaZeroBytes alphaZeroFacts.1 alphaZeroFacts.2
    (exact_restored_done_node_selected_q16_ledger input node member done)

/-- Source-facing material for the corrected restoration-wide classifier.

`data` is indexed by literal node membership and terminal control.  In
particular, it cannot select a different accumulator, a different node, or a
parser-owned q16 schedule.  `hasDone` prevents an empty accumulator from
turning the universal failure branch into a vacuous result. -/
structure ExactRestoredOperationalK13DataProvider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  hasDone : Nonempty
    { node : RestoredK13Node Statement Payload //
      node ∈ (exactRestorationAccumulator input).nodes ∧
        node.verifierFinalState.current.control = .done }
  data : (node : RestoredK13Node Statement Payload) →
    node ∈ (exactRestorationAccumulator input).nodes →
    node.verifierFinalState.current.control = .done →
      RestoredOperationalK13Data configuration.machine.environment node

/-- Construct the complete provider from the exact remaining per-node source
facts.  Nonvacuity comes from the stored accepted root, and q16 data comes
from the verifier-owned ledger invariant. -/
noncomputable def exact_restored_operational_k13_provider_of_source
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
    (source : (node : RestoredK13Node Statement Payload) →
      node ∈ (exactRestorationAccumulator input).nodes →
      node.verifierFinalState.current.control = .done →
        ExactRestoredOperationalK13SourceNodeData node) :
    ExactRestoredOperationalK13DataProvider input where
  hasDone := ⟨
    ⟨input.package.root.fixedRoot.base.runtime.node,
      exact_restoration_accumulator_contains_root input,
      exact_restoration_accumulator_root_is_done input⟩⟩
  data := fun node member done =>
    exact_restored_operational_k13_data_of_source_node input node member done
      (source node member done)

/-- The complete restoration-wide K1.3 provider now follows from the exact
operational input alone.  Canonical fixed-field decoding is part of the
checked deployed-parser return type, while gamma, alpha zero and q16 remain
verifier-owned consequences of the restored controller state. -/
noncomputable def exact_restored_operational_k13_provider
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
    ExactRestoredOperationalK13DataProvider input :=
  exact_restored_operational_k13_provider_of_source input
    (fun node _member _done =>
      exact_restored_operational_k13_source_node_data node)

/-- Any two admissible data providers induce the same mathematical K1.3 view
for one literal done node.  This removes the remaining classical-choice
dependence from gamma, alpha zero, fixed-field decoding, and q16 selection. -/
theorem exact_restored_operational_k13_view_is_intrinsic
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
    (node : RestoredK13Node Statement Payload)
    (member : node ∈ (exactRestorationAccumulator input).nodes)
    (_done : node.verifierFinalState.current.control = .done)
    (left right : RestoredOperationalK13Data
      configuration.machine.environment node) :
    restoredOperationalK13View left = restoredOperationalK13View right := by
  exact restored_operational_k13_view_unique
    (input.stateMap.everyNodeChallengeRecordUniqueness node member).1
    left right

/-- On the literal accepted root, every admissible restored K1.3 provider is
forced to use the gamma and alpha-zero bytes—and therefore the exact field
values—decoded by the deployed checked transcript.  No provider-selected
challenge equality remains at the root interface. -/
theorem exact_restored_root_operational_data_challenges_are_source_exact
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
    (data : RestoredOperationalK13Data configuration.machine.environment
      input.package.root.fixedRoot.base.runtime.node) :
    data.gammaBytes =
        (exactOperationalTape input).messages.challengeValue .gamma ∧
      data.gamma = exactChallengeValue
        (exactOperationalTape input).messages.challengeValue .gamma ∧
      data.alphaZeroBytes =
        (exactOperationalTape input).messages.challengeValue
          (ChallengeId.alpha 0) ∧
      data.alphaZero = exactChallengeValue
        (exactOperationalTape input).messages.challengeValue
          (ChallengeId.alpha 0) := by
  have gammaBytes := exact_operational_root_gamma_record_unique input
    data.gammaBytes data.gammaRecorded
  have alphaZeroBytes := exact_operational_root_alpha_zero_record_unique input
    data.alphaZeroBytes data.alphaZeroRecorded
  have gammaDecoded :
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue .gamma) =
        some data.gamma := by
    simpa [gammaBytes] using data.gammaDecoded
  have alphaZeroDecoded :
      decodeTagQM31ExactLE
          ((exactOperationalTape input).messages.challengeValue
            (ChallengeId.alpha 0)) = some data.alphaZero := by
    simpa [alphaZeroBytes] using data.alphaZeroDecoded
  have gammaValue : data.gamma = exactChallengeValue
      (exactOperationalTape input).messages.challengeValue .gamma := by
    simp [exactChallengeValue, gammaDecoded]
  have alphaZeroValue : data.alphaZero = exactChallengeValue
      (exactOperationalTape input).messages.challengeValue
        (ChallengeId.alpha 0) := by
    simp [exactChallengeValue, alphaZeroDecoded]
  exact ⟨gammaBytes, gammaValue, alphaZeroBytes, alphaZeroValue⟩

/-- Successful restoration-wide K1.3 classification chooses one literal
accepting node from the returned accumulator and retains its exact corrected
operational data and certificate. -/
structure ExactRestoredOperationalK13Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  node : RestoredK13Node Statement Payload
  member : node ∈ (exactRestorationAccumulator input).nodes
  done : node.verifierFinalState.current.control = .done
  data : RestoredOperationalK13Data configuration.machine.environment node
  classified : RestoredOperationalK13Certificate decoder node data

/-- Failure means that every accepting node retained by the actual client has
its exact total-classifier error.  The provider's `hasDone` field makes this
statement nonvacuous. -/
structure ExactRestoredOperationalK13Error
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (provider : ExactRestoredOperationalK13DataProvider input) : Type where
  everyDoneResult : ∀ (node : RestoredK13Node Statement Payload)
      (member : node ∈ (exactRestorationAccumulator input).nodes)
      (done : node.verifierFinalState.current.control = .done),
    { error : RestoredOperationalK13Error decoder node
        (provider.data node member done) //
      classifyRestoredOperationalK13 decoder node
          (provider.data node member done) = .inr error }

/-- The exact error returned by the total node classifier.  This projection
retains the classifier equation in `everyDoneResult`; unlike the earlier
bare error field, it cannot carry an arbitrary existential K1.3 word vector. -/
def ExactRestoredOperationalK13Error.everyDoneFailed
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
    {provider : ExactRestoredOperationalK13DataProvider input}
    (failure : ExactRestoredOperationalK13Error decoder input provider)
    (node : RestoredK13Node Statement Payload)
    (member : node ∈ (exactRestorationAccumulator input).nodes)
    (done : node.verifierFinalState.current.control = .done) :
    RestoredOperationalK13Error decoder node
      (provider.data node member done) :=
  (failure.everyDoneResult node member done).1

/-- A K1.3 error returned by the total node classifier carries the unique
K1.2 certificate that produced its word vector.  This is the source pinning
needed by the restored probability argument; arbitrary existential words do
not satisfy this theorem. -/
theorem classify_restored_operational_k13_k13_error_has_k12_certificate
    {Statement Payload : Type*}
    {environment : FutureFreeEnvironment}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {node : RestoredK13Node Statement Payload}
    {data : RestoredOperationalK13Data environment node}
    {words : ExtractedWords}
    {error : ParsedK13Error decoder words (restoredOperationalK13View data)}
    (classified : classifyRestoredOperationalK13 decoder node data =
      .inr (.k13 words error)) :
    ∃ k12 : RestoredNodeK12Certificate node,
      classifyRestoredNodeK12 node = .inl k12 ∧ k12.words = words := by
  unfold classifyRestoredOperationalK13 at classified
  cases k12Result : classifyRestoredNodeK12 node with
  | inl k12 =>
      cases k13Result : classifyParsedK13 decoder k12.words
          (restoredOperationalK13View data) with
      | inl certificate => simp [k12Result, k13Result] at classified
      | inr returnedError =>
          have errorExact :
              RestoredOperationalK13Error.k13 k12.words returnedError =
                RestoredOperationalK13Error.k13 words error := by
            simpa [k12Result, k13Result] using classified
          have wordsExact : k12.words = words := by
            injection errorExact
          exact ⟨k12, rfl, wordsExact⟩
  | inr k12Error => simp [k12Result] at classified

/-- Total restoration-wide classifier.  The choice is over the finite literal
node store and the already fixed provider data; no transcript value or query
schedule is synthesized by the classifier. -/
noncomputable def classifyExactRestoredOperationalK13
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (provider : ExactRestoredOperationalK13DataProvider input) :
    ExactRestoredOperationalK13Certificate decoder input ⊕
      ExactRestoredOperationalK13Error decoder input provider := by
  classical
  by_cases succeeds : Nonempty
      (ExactRestoredOperationalK13Certificate decoder input)
  · exact Sum.inl (Classical.choice succeeds)
  · apply Sum.inr
    refine { everyDoneResult := ?_ }
    intro node member done
    cases classified : classifyRestoredOperationalK13 decoder node
        (provider.data node member done) with
    | inl certificate =>
        exact (succeeds ⟨
          { node := node
            member := member
            done := done
            data := provider.data node member done
            classified := certificate }⟩).elim
    | inr error => exact ⟨error, rfl⟩

/-- Source-closed restoration-wide classifier used by the concrete stage
assembly.  The provider is the intrinsic checked-parser provider above, so
this entrypoint has no caller-supplied field decoder or per-node source map. -/
noncomputable def classifyExactRestoredOperationalK13Checked
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactRestoredOperationalK13Certificate decoder input ⊕
      ExactRestoredOperationalK13Error decoder input
        (exact_restored_operational_k13_provider input) :=
  classifyExactRestoredOperationalK13 decoder input
    (exact_restored_operational_k13_provider input)

/-- The failure branch exposes an actual accepting stored node and its typed
corrected K1.3 error.  This is the nonvacuous event witness consumed by the
subsequent probability decomposition. -/
theorem exact_restored_operational_k13_error_exposes_done_failure
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
    {provider : ExactRestoredOperationalK13DataProvider input}
    (failure : ExactRestoredOperationalK13Error decoder input provider) :
    ∃ (node : RestoredK13Node Statement Payload)
        (member : node ∈ (exactRestorationAccumulator input).nodes)
        (done : node.verifierFinalState.current.control = .done),
      Nonempty (RestoredOperationalK13Error decoder node
        (provider.data node member done)) := by
  rcases provider.hasDone with ⟨⟨node, member, done⟩⟩
  exact ⟨node, member, done, ⟨failure.everyDoneFailed node member done⟩⟩

/-- Each stored error is definitionally the result of the total classifier,
not merely an inhabitant of the same error type.  This equation preserves the
canonical K1.2 word source through the restoration-wide failure package. -/
theorem exact_restored_operational_k13_error_done_classified
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
    {provider : ExactRestoredOperationalK13DataProvider input}
    (failure : ExactRestoredOperationalK13Error decoder input provider)
    (node : RestoredK13Node Statement Payload)
    (member : node ∈ (exactRestorationAccumulator input).nodes)
    (done : node.verifierFinalState.current.control = .done) :
    classifyRestoredOperationalK13 decoder node
        (provider.data node member done) =
      .inr (failure.everyDoneFailed node member done) :=
  (failure.everyDoneResult node member done).2

/-- Exact sample event for failure of the source-closed restoration-wide
K1.3 classifier.  Its witness is the operational input constructed from that
same sample; no caller-selected event or alternate accumulator appears. -/
def exactTag73RestoredOperationalK13FailureEvent
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ input : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance sample,
    Nonempty (ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input))}

/-- Membership in the exact source-closed failure event exposes one literal
done node and one of the explicit K1.2/K1.3 mathematical failure families. -/
theorem exact_restored_operational_k13_failure_event_exposes_node_failure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    (member : sample ∈ exactTag73RestoredOperationalK13FailureEvent
      transitionFuel configuration projection fixedInstance decoder) :
    ∃ (input : ExactK12OperationalInput transitionFuel configuration projection
          fixedInstance sample)
        (node : RestoredK13Node Statement Payload)
        (nodeMember : node ∈ (exactRestorationAccumulator input).nodes)
        (done : node.verifierFinalState.current.control = .done),
      RestoredOperationalK13FailureEvent decoder node
        ((exact_restored_operational_k13_provider input).data node nodeMember
          done) := by
  rcases member with ⟨input, ⟨failure⟩⟩
  obtain ⟨node, nodeMember, done, ⟨nodeFailure⟩⟩ :=
    exact_restored_operational_k13_error_exposes_done_failure failure
  exact ⟨input, node, nodeMember, done,
    restored_operational_k13_error_implies_failure_event nodeFailure⟩

/-- Conversely, a success is tied definitionally to one node in the literal
returned accumulator and never to the opaque root-only parser view. -/
theorem exact_restored_operational_k13_certificate_has_literal_node
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
    (certificate : ExactRestoredOperationalK13Certificate decoder input) :
    certificate.node ∈ (exactRestorationAccumulator input).nodes ∧
      certificate.node.verifierFinalState.current.control = .done := by
  exact ⟨certificate.member, certificate.done⟩

#print axioms classifyExactRestoredOperationalK13
#print axioms classifyExactRestoredOperationalK13Checked
#print axioms exact_restoration_accumulator_contains_root
#print axioms exact_restoration_accumulator_root_is_done
#print axioms exact_restored_done_node_selected_q16_ledger
#print axioms exact_restored_operational_k13_source_node_data
#print axioms exact_restored_operational_k13_data_of_source_node
#print axioms exact_restored_operational_k13_provider_of_source
#print axioms exact_restored_operational_k13_provider
#print axioms exact_restored_operational_k13_view_is_intrinsic
#print axioms
  exact_restored_root_operational_data_challenges_are_source_exact
#print axioms exact_restored_operational_k13_error_exposes_done_failure
#print axioms
  classify_restored_operational_k13_k13_error_has_k12_certificate
#print axioms exact_restored_operational_k13_error_done_classified
#print axioms
  exact_restored_operational_k13_failure_event_exposes_node_failure
#print axioms exact_restored_operational_k13_certificate_has_literal_node

end

end AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
