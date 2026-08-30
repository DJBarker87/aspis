import AspisFormal.K1.V7Tag73ExactRestoredOperationalStages
import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction

/-!
# Exact restoration-wide K1.3 event ledger

The corrected K1.3 classifier may select any completed node retained by the
literal state-restoration client.  This file decomposes its source-closed
failure event into the six mathematical families that can actually be
returned on such a node.  All predicates use the node's authenticated Merkle
data and the verifier-derived gamma, alpha-zero and q16 schedule.

There is no probability premise, source oracle, caller-selected transcript or
root-only fallback in this ledger.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK13Events

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredOperationalStages
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Lift a dependent predicate on one completed stored node into the exact
compiler sample space.  The data argument is always constructed by the
intrinsic checked-source provider for that same input and node. -/
def exactTag73RestoredOperationalK13NodeEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (predicate : (node : RestoredK13Node Statement Payload) →
      RestoredOperationalK13Data configuration.machine.environment node → Prop) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (node : RestoredK13Node Statement Payload)
      (member : node ∈ (exactRestorationAccumulator input).nodes)
      (done : node.verifierFinalState.current.control = .done),
    predicate node
      ((exact_restored_operational_k13_provider input).data node member done)}

def exactTag73RestoredOperationalK12AuthenticationEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13NodeEvent transitionFuel configuration
    projection fixedInstance fun node _data =>
      ¬ accepted_two_tree_openings (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node)

def exactTag73RestoredOperationalK12ExtractionEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13NodeEvent transitionFuel configuration
    projection fixedInstance fun node _data =>
      V7MerkleExtractionFailure (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node)
        (restoredNodeK12OrderedQueries node)

def exactTag73RestoredOperationalK13IdealRejectedEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13NodeEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        ¬ IdealAccepts (restoredOperationalK13View data).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))
          (restoredOperationalK13View data).queries

def exactTag73RestoredOperationalK13QueryEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13NodeEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        QueryPhaseFailure (restoredOperationalK13View data).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))
          (restoredOperationalK13View data).queries

def exactTag73RestoredOperationalK13OneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13NodeEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        OneFoldReductionFailure (restoredOperationalK13View data).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))

def exactTag73RestoredOperationalK13ListCapEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13NodeEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        InitialListCapFailure (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))

/-- The restored list-cap event is empty for the exact production initial
encoder.  This is the same proved overlap argument as the fixed-root case and
does not consume a probability term. -/
theorem exact_restored_operational_k13_list_cap_event_eq_empty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder) :
    exactTag73RestoredOperationalK13ListCapEvent transitionFuel configuration
        projection fixedInstance decoder = ∅ := by
  ext sample
  constructor
  · rintro ⟨input, node, member, done, words, failure⟩
    have overlap : InitialEncoderOverlapCap (decoderCodeEncoders decoder) := by
      simpa [exactK13Encoders] using
        exact_k13_initial_encoder_overlap_cap decoder initialEncoderExact
    exact False.elim
      ((initial_list_cap_failure_impossible_of_overlap
        (decoderCodeEncoders decoder)
        (parsedK13Transcript words
          (restoredOperationalK13View
            ((exact_restored_operational_k13_provider input).data node member
              done))) overlap) failure)
  · simp

/-- Complete literal K1.2/K1.3 failure ledger for a restored node. -/
def exactTag73RestoredOperationalK13CompleteEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  (((exactTag73RestoredOperationalK12AuthenticationEvent transitionFuel
          configuration projection fixedInstance ∪
        exactTag73RestoredOperationalK12ExtractionEvent transitionFuel
          configuration projection fixedInstance) ∪
      exactTag73RestoredOperationalK13IdealRejectedEvent transitionFuel
        configuration projection fixedInstance decoder) ∪
    exactTag73RestoredOperationalK13QueryEvent transitionFuel configuration
      projection fixedInstance decoder) ∪
  (exactTag73RestoredOperationalK13OneFoldEvent transitionFuel configuration
      projection fixedInstance decoder ∪
    exactTag73RestoredOperationalK13ListCapEvent transitionFuel configuration
      projection fixedInstance decoder)

/-- Every error returned by the corrected restoration-wide classifier lands
in exactly one of the six explicit families above. -/
theorem exact_restored_operational_k13_failure_subset_complete
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact} :
    exactTag73RestoredOperationalK13FailureEvent transitionFuel configuration
        projection fixedInstance decoder ⊆
      exactTag73RestoredOperationalK13CompleteEvent transitionFuel configuration
        projection fixedInstance decoder := by
  intro sample member
  obtain ⟨input, node, nodeMember, done, failure⟩ :=
    exact_restored_operational_k13_failure_event_exposes_node_failure member
  change sample ∈ (((_ ∪ _) ∪ _) ∪ _) ∪ (_ ∪ _)
  rcases failure with authentication | extraction | residual
  · exact Or.inl (Or.inl (Or.inl (Or.inl
      ⟨input, node, nodeMember, done, authentication⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr
      ⟨input, node, nodeMember, done, extraction⟩)))
  · rcases residual with ⟨words, ideal | query | oneFold | listCap⟩
    · exact Or.inl (Or.inl (Or.inr
        ⟨input, node, nodeMember, done, words, ideal⟩))
    · exact Or.inl (Or.inr
        ⟨input, node, nodeMember, done, words, query⟩)
    · exact Or.inr (Or.inl
        ⟨input, node, nodeMember, done, words, oneFold⟩)
    · exact Or.inr (Or.inr
        ⟨input, node, nodeMember, done, words, listCap⟩)

/-- Generic K1.6-stage form of the same complete event cover. -/
theorem exact_restored_stages_k13_error_subset_complete
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {relation : PublicInstance Statement → Witness → Prop}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : AspisPool.V7C1SubfieldRecovery.InitialProjectionBinding decoder}
    (k15 : ExactRestoredOperationalK15Classifier transitionFuel configuration
      projection fixedInstance relation decoder binding) :
    AspisK1.V7Tag73ProofRelevantUpstreamInterface.k13CircleListDecodeErrorEvent
        (exactTag73RestoredOperationalStages transitionFuel configuration
          projection fixedInstance relation decoder binding k15) ⊆
      exactTag73RestoredOperationalK13CompleteEvent transitionFuel configuration
        projection fixedInstance decoder := by
  rw [exact_restored_stages_k13_error_event_eq k15]
  exact exact_restored_operational_k13_failure_subset_complete

/-! ## Root reduction for restoration-wide failure

The restoration-wide classifier succeeds when *any* completed stored node
succeeds.  Consequently its failure branch contains an error for every
completed node, in particular the literal accepted root.  This gives a useful
deterministic diagnostic cover and lets root-specific source equalities be
reused where applicable.

It does **not** by itself prove the tight K1.3 probability bound: the root
proof may depend adaptively on root random-oracle answers.  The final bound
must still use the restoration/fork coupling when independence is required.
No extraction power or distribution on the successful-node choice is assumed
here. -/

/-- Lift a predicate on the literal accepted root and its intrinsic restored
K1.3 view into the exact compiler sample space. -/
def exactTag73RestoredOperationalK13RootEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (predicate : (node : RestoredK13Node Statement Payload) →
      RestoredOperationalK13Data configuration.machine.environment node → Prop) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ input : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance sample,
    predicate input.package.root.fixedRoot.base.runtime.node
      ((exact_restored_operational_k13_provider input).data
        input.package.root.fixedRoot.base.runtime.node
        (exact_restoration_accumulator_contains_root input)
        (exact_restoration_accumulator_root_is_done input))}

def exactTag73RestoredOperationalRootK12AuthenticationEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13RootEvent transitionFuel configuration
    projection fixedInstance fun node _data =>
      ¬ accepted_two_tree_openings (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node)

def exactTag73RestoredOperationalRootK12ExtractionEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13RootEvent transitionFuel configuration
    projection fixedInstance fun node _data =>
      V7MerkleExtractionFailure (restoredNodeK12Truncate node)
        (restoredNodeK12Roots node) (restoredNodeK12Openings node)
        (restoredNodeK12OrderedQueries node)

def exactTag73RestoredOperationalRootK13IdealRejectedEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13RootEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        ¬ IdealAccepts (restoredOperationalK13View data).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))
          (restoredOperationalK13View data).queries

def exactTag73RestoredOperationalRootK13QueryEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13RootEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        QueryPhaseFailure (restoredOperationalK13View data).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))
          (restoredOperationalK13View data).queries

def exactTag73RestoredOperationalRootK13OneFoldEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13RootEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        OneFoldReductionFailure (restoredOperationalK13View data).schedule
          (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))

def exactTag73RestoredOperationalRootK13ListCapEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactTag73RestoredOperationalK13RootEvent transitionFuel configuration
    projection fixedInstance fun _node data =>
      ∃ words : ExtractedWords,
        InitialListCapFailure (decoderCodeEncoders decoder)
          (parsedK13Transcript words (restoredOperationalK13View data))

def exactTag73RestoredOperationalRootK13CompleteEvent
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  (((exactTag73RestoredOperationalRootK12AuthenticationEvent transitionFuel
          configuration projection fixedInstance ∪
        exactTag73RestoredOperationalRootK12ExtractionEvent transitionFuel
          configuration projection fixedInstance) ∪
      exactTag73RestoredOperationalRootK13IdealRejectedEvent transitionFuel
        configuration projection fixedInstance decoder) ∪
    exactTag73RestoredOperationalRootK13QueryEvent transitionFuel configuration
      projection fixedInstance decoder) ∪
  (exactTag73RestoredOperationalRootK13OneFoldEvent transitionFuel configuration
      projection fixedInstance decoder ∪
    exactTag73RestoredOperationalRootK13ListCapEvent transitionFuel configuration
      projection fixedInstance decoder)

/-- Restoration-wide K1.3 failure is deterministically covered by the six
exact mathematical failure families on the literal root.  This theorem makes
no independence or probability claim. -/
theorem exact_restored_operational_k13_failure_subset_root_complete
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact} :
    exactTag73RestoredOperationalK13FailureEvent transitionFuel configuration
        projection fixedInstance decoder ⊆
      exactTag73RestoredOperationalRootK13CompleteEvent transitionFuel
        configuration projection fixedInstance decoder := by
  intro sample member
  rcases member with ⟨input, ⟨failure⟩⟩
  let root := input.package.root.fixedRoot.base.runtime.node
  let rootMember : root ∈ (exactRestorationAccumulator input).nodes :=
    exact_restoration_accumulator_contains_root input
  let rootDone : root.verifierFinalState.current.control = .done :=
    exact_restoration_accumulator_root_is_done input
  have rootFailure := failure.everyDoneFailed root rootMember rootDone
  have failureEvent :=
    restored_operational_k13_error_implies_failure_event rootFailure
  change sample ∈ (((_ ∪ _) ∪ _) ∪ _) ∪ (_ ∪ _)
  rcases failureEvent with authentication | extraction | residual
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨input, authentication⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨input, extraction⟩)))
  · rcases residual with ⟨words, ideal | query | oneFold | listCap⟩
    · exact Or.inl (Or.inl (Or.inr ⟨input, words, ideal⟩))
    · exact Or.inl (Or.inr ⟨input, words, query⟩)
    · exact Or.inr (Or.inl ⟨input, words, oneFold⟩)
    · exact Or.inr (Or.inr ⟨input, words, listCap⟩)

/-- The root list-cap branch is empty for the production encoder, just as the
restoration-wide branch is. -/
theorem exact_restored_operational_root_k13_list_cap_event_eq_empty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder =
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder) :
    exactTag73RestoredOperationalRootK13ListCapEvent transitionFuel configuration
        projection fixedInstance decoder = ∅ := by
  ext sample
  constructor
  · rintro ⟨input, words, failure⟩
    have overlap : InitialEncoderOverlapCap (decoderCodeEncoders decoder) := by
      simpa [exactK13Encoders] using
        exact_k13_initial_encoder_overlap_cap decoder initialEncoderExact
    exact False.elim
      ((initial_list_cap_failure_impossible_of_overlap
        (decoderCodeEncoders decoder)
        (parsedK13Transcript words
          (restoredOperationalK13View
            ((exact_restored_operational_k13_provider input).data
              input.package.root.fixedRoot.base.runtime.node
              (exact_restoration_accumulator_contains_root input)
              (exact_restoration_accumulator_root_is_done input)))) overlap)
        failure)
  · simp

#print axioms exactTag73RestoredOperationalK13NodeEvent
#print axioms exact_restored_operational_k13_list_cap_event_eq_empty
#print axioms exact_restored_operational_k13_failure_subset_complete
#print axioms exact_restored_stages_k13_error_subset_complete
#print axioms exactTag73RestoredOperationalK13RootEvent
#print axioms exact_restored_operational_k13_failure_subset_root_complete
#print axioms
  exact_restored_operational_root_k13_list_cap_event_eq_empty

end

end AspisK1.V7Tag73ExactRestoredOperationalK13Events
