import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import AspisFormal.K1.V7FsAokExperiment

/-!
# Legacy conditional probability ledger for V7 Tag 73

This file proves probability bookkeeping around a deliberately conditional
Fiat--Shamir step.  It does **not** instantiate the deployed Tag-73 compiler,
and it does not postulate the desired bound as a field of a compiler object.
The core protocol-specific statement that is not yet proved is exposed as
`Tag73FreshAcceptanceTraceCover`: outside the enumerated compiler events, a
fresh accepting deployed execution must induce a legal restricted
state-restoration execution of the interactive Tag-73 IOP.

The event vocabulary below predates the exact applicability audit and is an
over-inclusive observed-proof ledger.  In particular its BCS, C2, grinding,
sampler, simulator, and WUR entries are **not** established plain-ROM Tag-73
losses.  Names containing `exact` mean only that the supplied allowances are
expanded and summed without hidden normalization.  The honest plain failure
partition is defined separately in `V7Tag73PlainRawError`.

Observed-proof instantiation also needs the separately enumerated canonical
simulation, programming, and weak-unique-response event bounds; this file does
not treat them as external axioms.

`UpstreamK12ToK15KnowledgeBound` is deliberately about that interactive set,
not the Fiat--Shamir accepting set.  It is the typed insertion point for the
K1.2 two-tree query-graph extractor, K1.3 circle/list decoder, K1.4 coherent
chain selector, and K1.5 spend-witness recovery theorem.
-/

set_option autoImplicit false

namespace AspisK1.V7FsAokCompiler

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-! ## Legacy conditional allowance vocabulary -/

/-- Historical candidate events for an observed-proof adapter.  This type is
not a claim that every constructor contributes loss to the plain theorem. -/
inductive CompilerFailureKind where
  | bcsFull256HashChain
  | challengeDependentC2
  | batchGrinding35
  | foldGrinding31
  | finalGrinding34
  | ordinaryQm31Sampler
  | nonzeroQm31Sampler
  | secureCircleSampler
  | firstCap203Q16
  | duplexStateCoupling
  | adversaryQ1Separation
  | canonicalSimulator
  | programmingCollision
  | weakUniqueResponse
  | attemptAndStatementBinding
  | resourceBudget
  deriving DecidableEq, Fintype, Repr

/-- K1.2--K1.5 errors remain separate, named upstream quantities. -/
inductive UpstreamFailureKind where
  | k12TwoTreeMerkle208
  | k13CircleListDecoding
  | k14CoherentChainSelection
  | k15SpendWitnessRecovery
  deriving DecidableEq, Fintype, Repr

structure CompilerFailureEvents (Sample : Type*) where
  event : CompilerFailureKind → Set Sample

structure CompilerErrorTerms where
  challengeDependentC2 : ENNReal
  batchGrinding35 : ENNReal
  foldGrinding31 : ENNReal
  finalGrinding34 : ENNReal
  ordinaryQm31Sampler : ENNReal
  nonzeroQm31Sampler : ENNReal
  secureCircleSampler : ENNReal
  firstCap203Q16 : ENNReal
  duplexStateCoupling : ENNReal
  adversaryQ1Separation : ENNReal
  canonicalSimulator : ENNReal
  programmingCollision : ENNReal
  /-- State-restoration weak-unique-response advantage.  The FS-WUR lifting
  and the number of simulated proofs are applied below. -/
  stateRestorationWur : ENNReal
  attemptAndStatementBinding : ENNReal
  resourceBudget : ENNReal

structure UpstreamErrorTerms where
  k12TwoTreeMerkle208 : ENNReal
  k13CircleListDecoding : ENNReal
  k14CoherentChainSelection : ENNReal
  k15SpendWitnessRecovery : ENNReal

/-- The literal full-output BCS 2016 Theorem 7.1 benchmark at 256 bits.
`V7BcsApplicabilityGate` proves that the deployed Tag-73 transcript is not the
literal Section-6 compiler, so this definition is not an instantiated Tag-73
loss.  It is retained only for the legacy conditional ledger. -/
def bcsFull256HashChainLoss (adversaryOracleQueries : Nat) : ENNReal :=
  3 * (((adversaryOracleQueries : ENNReal) ^ 2) + 1) /
    ((2 : ENNReal) ^ 256)

/-- Ganesh et al. 2024, Lemma 3.1, kept symbolic because its perfect-HVZK,
canonical-simulator and common challenge-domain hypotheses are not yet proved
for Tag 73. -/
def fsWurRawUpper (stateRestorationWur : ENNReal)
    (randomOracleQueries minimumChallengeCardinality : Nat) : ENNReal :=
  stateRestorationWur +
    ((randomOracleQueries + 1 : Nat) : ENNReal) /
      (minimumChallengeCardinality : ENNReal)

/-- Ganesh et al. 2024, Lemma 3.2 contributes one FS-WUR advantage for each
previous simulated proof. -/
def observedWurLoss (stateRestorationWur : ENNReal)
    (randomOracleQueries minimumChallengeCardinality simulatedProofs : Nat) :
    ENNReal :=
  (simulatedProofs : ENNReal) *
    fsWurRawUpper stateRestorationWur randomOracleQueries
      minimumChallengeCardinality

def compilerFailureAllowance (budget : ResourceBudget)
    (minimumChallengeCardinality : Nat) (terms : CompilerErrorTerms) :
    CompilerFailureKind → ENNReal
  | .bcsFull256HashChain =>
      bcsFull256HashChainLoss budget.adversaryOracleCalls
  | .challengeDependentC2 => terms.challengeDependentC2
  | .batchGrinding35 => terms.batchGrinding35
  | .foldGrinding31 => terms.foldGrinding31
  | .finalGrinding34 => terms.finalGrinding34
  | .ordinaryQm31Sampler => terms.ordinaryQm31Sampler
  | .nonzeroQm31Sampler => terms.nonzeroQm31Sampler
  | .secureCircleSampler => terms.secureCircleSampler
  | .firstCap203Q16 => terms.firstCap203Q16
  | .duplexStateCoupling => terms.duplexStateCoupling
  | .adversaryQ1Separation => terms.adversaryQ1Separation
  | .canonicalSimulator => terms.canonicalSimulator
  | .programmingCollision => terms.programmingCollision
  | .weakUniqueResponse =>
      observedWurLoss terms.stateRestorationWur
        budget.adversaryOracleCalls minimumChallengeCardinality
        budget.simulatedProofs
  | .attemptAndStatementBinding => terms.attemptAndStatementBinding
  | .resourceBudget => terms.resourceBudget

def upstreamFailureAllowance (terms : UpstreamErrorTerms) :
    UpstreamFailureKind → ENNReal
  | .k12TwoTreeMerkle208 => terms.k12TwoTreeMerkle208
  | .k13CircleListDecoding => terms.k13CircleListDecoding
  | .k14CoherentChainSelection => terms.k14CoherentChainSelection
  | .k15SpendWitnessRecovery => terms.k15SpendWitnessRecovery

/-- Sum of the legacy supplied allowances, not a proved Tag-73 compiler loss.
It is at least honest about using a raw union sum rather than work
normalization. -/
def exactCompilerRawError (budget : ResourceBudget)
    (minimumChallengeCardinality : Nat) (terms : CompilerErrorTerms) : ENNReal :=
  ∑ kind : CompilerFailureKind,
    compilerFailureAllowance budget minimumChallengeCardinality terms kind

def exactUpstreamRawError (terms : UpstreamErrorTerms) : ENNReal :=
  ∑ kind : UpstreamFailureKind, upstreamFailureAllowance terms kind

def exactTag73RawExtractionError (budget : ResourceBudget)
    (minimumChallengeCardinality : Nat) (upstream : UpstreamErrorTerms)
    (compiler : CompilerErrorTerms) : ENNReal :=
  exactUpstreamRawError upstream +
    exactCompilerRawError budget minimumChallengeCardinality compiler

/-! Despite its historical name, `exactTag73RawExtractionError` is exact only
as an algebraic expansion of caller-supplied allowances.  It must not be used
as the final plain-ROM error expression without proving the corresponding
events and the trace cover. -/

/-! The following two equations make every summand kernel-visible. -/

theorem exact_upstream_raw_error_expanded (terms : UpstreamErrorTerms) :
    exactUpstreamRawError terms =
      terms.k12TwoTreeMerkle208 +
      terms.k13CircleListDecoding +
      terms.k14CoherentChainSelection +
      terms.k15SpendWitnessRecovery := by
  unfold exactUpstreamRawError
  rw [show (Finset.univ : Finset UpstreamFailureKind) =
    {.k12TwoTreeMerkle208, .k13CircleListDecoding,
      .k14CoherentChainSelection, .k15SpendWitnessRecovery} by decide]
  simp [upstreamFailureAllowance]
  ac_rfl

theorem exact_compiler_raw_error_expanded (budget : ResourceBudget)
    (minimumChallengeCardinality : Nat) (terms : CompilerErrorTerms) :
    exactCompilerRawError budget minimumChallengeCardinality terms =
      bcsFull256HashChainLoss budget.adversaryOracleCalls +
      terms.challengeDependentC2 +
      terms.batchGrinding35 +
      terms.foldGrinding31 +
      terms.finalGrinding34 +
      terms.ordinaryQm31Sampler +
      terms.nonzeroQm31Sampler +
      terms.secureCircleSampler +
      terms.firstCap203Q16 +
      terms.duplexStateCoupling +
      terms.adversaryQ1Separation +
      terms.canonicalSimulator +
      terms.programmingCollision +
      observedWurLoss terms.stateRestorationWur
        budget.adversaryOracleCalls minimumChallengeCardinality
        budget.simulatedProofs +
      terms.attemptAndStatementBinding +
      terms.resourceBudget := by
  unfold exactCompilerRawError
  rw [show (Finset.univ : Finset CompilerFailureKind) =
    {.bcsFull256HashChain, .challengeDependentC2, .batchGrinding35,
      .foldGrinding31, .finalGrinding34, .ordinaryQm31Sampler,
      .nonzeroQm31Sampler, .secureCircleSampler, .firstCap203Q16,
      .duplexStateCoupling, .adversaryQ1Separation, .canonicalSimulator,
      .programmingCollision, .weakUniqueResponse,
      .attemptAndStatementBinding, .resourceBudget} by decide]
  simp [compilerFailureAllowance]
  ac_rfl

/-! ## Probability experiments and the missing behavioral bridge -/

def eventProbability
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (event : Set Sample) : ENNReal :=
  experiment.law.toOuterMeasure event

def freshAcceptanceProbability
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    ENNReal :=
  eventProbability experiment (FreshAcceptanceEvent experiment)

def validExtractionProbability
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    ENNReal :=
  eventProbability experiment (ValidExtractionEvent experiment)

def compilerFailureUnion {Sample : Type*}
    (events : CompilerFailureEvents Sample) : Set Sample :=
  ⋃ kind : CompilerFailureKind, events.event kind

/-! ## Legacy candidate interactive target -/

structure RestrictedReplay (RandomTape : Type*) where
  tapeIdentity : RandomTape
  /-- Legacy event-prefix metadata. Positivity does not by itself prove that
  this prefix denotes a complete previously seen verifier state. -/
  prefixLength : Nat
  /-- Only queries newly made by this replay, not the inherited first-run
  prefix. -/
  newQueries : List QueryRecord

/-- Legacy candidate adapter data. A caller can construct this record without
running `checkedRefine` or the start-only coupling, so the record is not itself
evidence of deployed refinement or legal state restoration. It contains no
witness and no assertion that extraction succeeded. -/
structure InteractiveTag73Run
    (RandomTape Statement Proof : Type*) where
  transcriptOracle : HashOracle
  sharedOracle : OracleState
  messages : Messages
  frontierNodes : QuerySchedule → Nat
  querySearch : FirstCap203Search frontierNodes
  forgery : PublicProof Statement Proof
  fixedTapeIdentity : RandomTape
  firstRunQ1 : List QueryRecord
  replays : List (RestrictedReplay RandomTape)
  resources : ResourceUse
  verifierAccepted : Bool

abbrev InteractiveTag73World
    (Sample RandomTape Statement Proof : Type*) :=
  Sample → Option (InteractiveTag73Run RandomTape Statement Proof)

def sharedAnswerDefined (state : OracleState) (input : ShaInput)
    (output : ShaOutput) : Prop :=
  ∃ entry ∈ state.table,
    entry.input = input ∧ entry.output = output

def sharedQueryObserved (state : OracleState) (input : ShaInput)
    (output : ShaOutput) : Prop :=
  ∃ record ∈ state.history,
    record.input = input ∧ record.output = output

def sharedOracleAgrees
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ entry ∈ run.sharedOracle.table,
    entry.output = run.transcriptOracle.answer entry.input

def sharedHistoryAgreesWithTable
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ record ∈ run.sharedOracle.history,
    sharedAnswerDefined run.sharedOracle record.input record.output

def sharedProgrammingAgreesWithTable
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ record ∈ run.sharedOracle.programmingHistory,
    ∃ entry ∈ run.sharedOracle.table,
      entry.input = record.input ∧ entry.output = record.output ∧
      entry.source = .programmed

def acceptedTranscriptQueriesDefined
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ query ∈ (acceptedTranscriptState run.transcriptOracle run.messages
      run.querySearch).oracleHistory,
    sharedQueryObserved run.sharedOracle query.input query.output

def rootSaltQueriesDefined
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  sharedQueryObserved run.sharedOracle
      (rootSaltInput run.messages.context c1TreeTag)
      (run.transcriptOracle.answer
        (rootSaltInput run.messages.context c1TreeTag)) ∧
  sharedQueryObserved run.sharedOracle
      (rootSaltInput run.messages.context c2TreeTag)
      (run.transcriptOracle.answer
        (rootSaltInput run.messages.context c2TreeTag))

def scannedCandidateQueries
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof)
    (counter : Fin 64) : List OracleQuery :=
  let base := postFinalNonceState run.transcriptOracle run.messages
  let branch := runCandidateBranch run.transcriptOracle base counter
    (run.querySearch.outcome counter)
  branch.oracleHistory.drop base.oracleHistory.length

def scannedCandidateQueriesDefined
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ counter : Fin 64,
    counter.val ≤ run.querySearch.selectedCounter.val →
    ∀ query ∈ scannedCandidateQueries run counter,
      sharedQueryObserved run.sharedOracle query.input query.output

def q1OnlyContainsAdversaryQueries
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ query ∈ run.firstRunQ1, query.actor = .adversary

/-- Legacy token/prefix checks. Equality of a public tape token and a positive
event index prove neither common hidden-tape origin nor a complete verifier
checkpoint; `V7FsStateRestorationCoupling` supplies the stronger start-only
operational construction and leaves the complete-state map explicit. -/
def replaysUseSameTapeAndNonemptyCheckpoints
    {RandomTape Statement Proof : Type*}
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  ∀ replay ∈ run.replays,
    replay.tapeIdentity = run.fixedTapeIdentity ∧
    0 < replay.prefixLength ∧
    replay.prefixLength ≤
      (beforeQueryScan run.transcriptOracle run.messages).length + 1 +
        (afterAcceptedQueryScan run.messages).length ∧
    ∀ query ∈ replay.newQueries, query.actor = .extractorReplay

/-- Legacy candidate legality predicate. The dependent schedule fields encode
C2 ordering, stage-indexed nonce annotations, and first-cap-203 selection, but
this predicate does not link raw blocks to decoders, derive terminal acceptance,
or prove that replay prefixes are legal verifier states. -/
def IsLegalInteractiveTag73
    {RandomTape Statement Proof : Type*} (budget : ResourceBudget)
    (run : InteractiveTag73Run RandomTape Statement Proof) : Prop :=
  run.verifierAccepted = true ∧
  run.messages.context = run.forgery.publicInstance.context ∧
  q1OnlyContainsAdversaryQueries run ∧
  run.firstRunQ1 = actorHistory .adversary run.sharedOracle ∧
  replaysUseSameTapeAndNonemptyCheckpoints run ∧
  sharedOracleAgrees run ∧
  sharedHistoryAgreesWithTable run ∧
  sharedProgrammingAgreesWithTable run ∧
  rootSaltQueriesDefined run ∧
  scannedCandidateQueriesDefined run ∧
  acceptedTranscriptQueriesDefined run ∧
  run.resources.batchGrindingQueries =
    run.messages.batchGrinding.probesBeforeSelected.length + 1 ∧
  run.resources.foldGrindingQueries =
    run.messages.foldGrinding.probesBeforeSelected.length + 1 ∧
  run.resources.finalGrindingQueries =
    run.messages.finalGrinding.probesBeforeSelected.length + 1 ∧
  run.resources.queryCandidateBranches =
    run.querySearch.selectedCounter.val + 1 ∧
  run.resources.adversaryOracleCalls =
    (actorHistory .adversary run.sharedOracle).length ∧
  run.resources.simulatorOracleCalls =
    (actorHistory .simulator run.sharedOracle).length ∧
  run.resources.verifierOracleCalls =
    (actorHistory .verifier run.sharedOracle).length ∧
  run.resources.extractorOracleCalls =
    (actorHistory .extractorReplay run.sharedOracle).length ∧
  run.resources.programmedPoints =
    run.sharedOracle.programmingHistory.length ∧
  run.resources.freshOracleAnswers = run.sharedOracle.freshCalls ∧
  run.sharedOracle.totalCalls = run.sharedOracle.history.length ∧
  WithinBudget run.resources budget

/-- Legacy set selected through a caller-supplied `world`. The type alone does
not show that `world` was produced by the deterministic adapter, so no theorem
should treat this set as an instantiated interactive execution. -/
def legalInteractiveTag73Set
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (world : InteractiveTag73World Sample RandomTape Statement Proof) : Set Sample :=
  {sample | ∃ forgery run,
    (experiment.outcome sample).firstRun.forgery = some forgery ∧
    world sample = some run ∧
    run.forgery = forgery ∧
    run.fixedTapeIdentity =
      (experiment.outcome sample).firstRun.tapeIdentity ∧
    run.firstRunQ1 = (experiment.outcome sample).firstRun.q1 ∧
    run.resources = (experiment.outcome sample).use ∧
    (experiment.outcome sample).extraction.use = run.resources ∧
    (experiment.outcome sample).programmingAbort = none ∧
    (experiment.outcome sample).weakUniqueResponseBad = false ∧
    (experiment.outcome sample).transcriptCouplingAbort = false ∧
    run.resources.adversaryOracleCalls = run.firstRunQ1.length ∧
    run.resources.simulatedProofs =
      (experiment.outcome sample).simulations.length ∧
    IsLegalInteractiveTag73 experiment.budget run}

/-- Legacy conditional cover. It packages essentially the missing compiler
bridge and is therefore not accepted as a proof of K1.6. It mentions no
witness and no extraction probability, but a caller still has to prove the
acceptance-to-interactive inclusion. -/
def Tag73FreshAcceptanceTraceCover
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (world : InteractiveTag73World Sample RandomTape Statement Proof)
    (events : CompilerFailureEvents Sample) : Prop :=
  FreshAcceptanceEvent experiment \ legalInteractiveTag73Set experiment world ⊆
    compilerFailureUnion events

/-- Conditional K1.2--K1.5 insertion point for the legacy candidate set. Its
left side is not the Fiat--Shamir accepting event, but it becomes an honest
state-restoration premise only after the candidate set is constructively
linked to the exact interactive experiment. -/
def UpstreamK12ToK15KnowledgeBound
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (world : InteractiveTag73World Sample RandomTape Statement Proof)
    (polynomialLoss : ENNReal)
    (terms : UpstreamErrorTerms) : Prop :=
  eventProbability experiment (legalInteractiveTag73Set experiment world) ≤
    polynomialLoss * validExtractionProbability experiment +
      exactUpstreamRawError terms

/-- Caller-supplied bounds for every legacy event. This structure performs no
Tag-73 probability analysis and can double-count overlapping events. -/
structure CompilerFailureBounds
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (events : CompilerFailureEvents Sample)
    (minimumChallengeCardinality : Nat) (terms : CompilerErrorTerms) : Prop where
  bound : ∀ kind,
    eventProbability experiment (events.event kind) ≤
      compilerFailureAllowance experiment.budget minimumChallengeCardinality
        terms kind

theorem compiler_failure_union_probability_le
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (events : CompilerFailureEvents Sample)
    (minimumChallengeCardinality : Nat) (terms : CompilerErrorTerms)
    (bounds : CompilerFailureBounds experiment events
      minimumChallengeCardinality terms) :
    eventProbability experiment (compilerFailureUnion events) ≤
      exactCompilerRawError experiment.budget minimumChallengeCardinality terms := by
  calc
    eventProbability experiment (compilerFailureUnion events) ≤
        ∑ kind : CompilerFailureKind,
          eventProbability experiment (events.event kind) := by
      simpa [eventProbability, compilerFailureUnion, tsum_fintype] using
        (measure_iUnion_le (μ := experiment.law.toOuterMeasure)
          (fun kind : CompilerFailureKind => events.event kind))
    _ ≤ ∑ kind : CompilerFailureKind,
          compilerFailureAllowance experiment.budget minimumChallengeCardinality
            terms kind := by
      exact Finset.sum_le_sum fun kind _ => bounds.bound kind
    _ = exactCompilerRawError experiment.budget minimumChallengeCardinality
          terms := rfl

/-! ## Legacy conditional K1.6 bookkeeping theorems -/

/-- Conditional observed-proof AoK arithmetic.  The theorem proves the
arithmetic from (1) the protocol-specific trace cover, (2) the interactive
K1.2--K1.5 knowledge theorem, and (3) individually bounded raw events.  It does
not divide soundness by adversary work and it does not assert pointwise
extraction from every accepting proof.  It is not a proof of the trace cover
or of literal BCS applicability. -/
theorem v7_tag73_fs_aok_raw_from_trace_cover
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (world : InteractiveTag73World Sample RandomTape Statement Proof)
    (events : CompilerFailureEvents Sample)
    (minimumChallengeCardinality : Nat)
    (upstreamTerms : UpstreamErrorTerms) (compilerTerms : CompilerErrorTerms)
    (polynomialLoss : ENNReal)
    (traceCover : Tag73FreshAcceptanceTraceCover experiment world events)
    (upstreamKnowledge : UpstreamK12ToK15KnowledgeBound experiment
      world polynomialLoss upstreamTerms)
    (eventBounds : CompilerFailureBounds experiment events
      minimumChallengeCardinality compilerTerms) :
    freshAcceptanceProbability experiment ≤
      polynomialLoss * validExtractionProbability experiment +
        exactTag73RawExtractionError experiment.budget minimumChallengeCardinality
          upstreamTerms compilerTerms := by
  have acceptingSubset :
      FreshAcceptanceEvent experiment ⊆
        legalInteractiveTag73Set experiment world ∪
          compilerFailureUnion events := by
    intro sample accepted
    by_cases legal : sample ∈ legalInteractiveTag73Set experiment world
    · exact Or.inl legal
    · exact Or.inr (traceCover ⟨accepted, legal⟩)
  calc
    freshAcceptanceProbability experiment ≤
        eventProbability experiment
          (legalInteractiveTag73Set experiment world ∪
            compilerFailureUnion events) :=
      measure_mono acceptingSubset
    _ ≤ eventProbability experiment
          (legalInteractiveTag73Set experiment world) +
          eventProbability experiment (compilerFailureUnion events) :=
      measure_union_le _ _
    _ ≤ eventProbability experiment
          (legalInteractiveTag73Set experiment world) +
      exactCompilerRawError experiment.budget minimumChallengeCardinality
            compilerTerms :=
      add_le_add_right
        (compiler_failure_union_probability_le experiment events
          minimumChallengeCardinality compilerTerms eventBounds) _
    _ ≤ (polynomialLoss * validExtractionProbability experiment +
          exactUpstreamRawError upstreamTerms) +
          exactCompilerRawError experiment.budget minimumChallengeCardinality
            compilerTerms :=
      add_le_add_left upstreamKnowledge _
    _ = polynomialLoss * validExtractionProbability experiment +
          exactTag73RawExtractionError experiment.budget minimumChallengeCardinality
            upstreamTerms compilerTerms := by
      simp only [exactTag73RawExtractionError, add_assoc]

/-- Equivalent normalized extraction statement when the polynomial loss is
finite and nonzero: `(acceptance - rawError) / loss ≤ extraction`. -/
theorem v7_tag73_fs_aok_normalized_from_trace_cover
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment : ObservedProofExperiment Sample RandomTape Statement Proof Witness)
    (world : InteractiveTag73World Sample RandomTape Statement Proof)
    (events : CompilerFailureEvents Sample)
    (minimumChallengeCardinality : Nat)
    (upstreamTerms : UpstreamErrorTerms) (compilerTerms : CompilerErrorTerms)
    (polynomialLoss : ENNReal)
    (lossNonzero : polynomialLoss ≠ 0) (lossFinite : polynomialLoss ≠ ⊤)
    (traceCover : Tag73FreshAcceptanceTraceCover experiment world events)
    (upstreamKnowledge : UpstreamK12ToK15KnowledgeBound experiment
      world polynomialLoss upstreamTerms)
    (eventBounds : CompilerFailureBounds experiment events
      minimumChallengeCardinality compilerTerms) :
    (freshAcceptanceProbability experiment -
        exactTag73RawExtractionError experiment.budget minimumChallengeCardinality
          upstreamTerms compilerTerms) / polynomialLoss ≤
      validExtractionProbability experiment := by
  rw [ENNReal.div_le_iff' lossNonzero lossFinite, tsub_le_iff_right]
  exact v7_tag73_fs_aok_raw_from_trace_cover experiment world events
    minimumChallengeCardinality upstreamTerms compilerTerms
    polynomialLoss traceCover upstreamKnowledge eventBounds

/-! This formal countermodel records why K1.2--K1.5 alone cannot close K1.6:
an interactive theorem can be vacuous on an empty legal-interactive set while
the noninteractive accepting event has probability one. -/
theorem upstream_knowledge_alone_does_not_imply_fs_bound :
    ∃ (law : PMF Unit) (accepting legalInteractive extraction : Set Unit),
      law.toOuterMeasure legalInteractive ≤
          (1 : ENNReal) * law.toOuterMeasure extraction ∧
      ¬ law.toOuterMeasure accepting ≤
          (1 : ENNReal) * law.toOuterMeasure extraction := by
  refine ⟨PMF.pure (), Set.univ, ∅, ∅, ?_, ?_⟩
  · simp
  · simp

#print axioms exact_upstream_raw_error_expanded
#print axioms exact_compiler_raw_error_expanded
#print axioms compiler_failure_union_probability_le
#print axioms v7_tag73_fs_aok_raw_from_trace_cover
#print axioms v7_tag73_fs_aok_normalized_from_trace_cover
#print axioms upstream_knowledge_alone_does_not_imply_fs_bound

end

end AspisK1.V7FsAokCompiler
