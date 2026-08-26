import AspisFormal.K1.V7Tag73ResourceLazyOracle
import AspisFormal.K1.V7Tag73SchedulerNativePlainRomExperiment

/-!
# Observable Tag-73 work-query accounting

The three work searches use the same 41-byte SHA grammar, but they occur at
three different transcript checkpoints.  A raw prover result deliberately
does not carry its exploratory nonce list.  The operational run nevertheless
retains enough information to count the searches without trusting such a
list:

* the prover oracle history retains every actual SHA query; and
* the future-free verifier transition that submits the selected nonce retains
  the exact pre-submission transcript digest and its `WorkStage`.

This leaf therefore classifies a query at stage `s` exactly when its input has
the deployed `digest || 0x03 || 8-byte nonce` grammar for a checkpoint digest
actually recorded at stage `s`.  A state collision can make one query match
more than one stage; the counts intentionally remain separate and may then
overlap.  Later target-cleanness can exclude that collision, while the basic
`Q` upper bound below needs no disjointness assumption.

The fields account for the first accepted Fiat--Shamir adversary history, as
the legacy `ResourceUse` grinding fields do.  SHA calls made by restoration
starts, including failed starts, are separately and completely charged to
`extractorOracleCalls`; they are not silently duplicated into these three
first-run fields.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ActualGrindingQueryAccounting

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73AdaptiveLazyOracle

noncomputable section

universe u

/-! ## Exact observable grammar -/

/-- A 41-byte input is a deployed grinding query at `digest` precisely when
its first 32 bytes are `digest` and byte 32 is the grinding domain `0x03`.
The remaining eight bytes are the adversary-selected nonce. -/
def hasGrindingInputGrammarAt
    (digest : Digest256) (input : ShaInput) : Bool :=
  decide (input.length = 41) &&
    decide (input.take 32 = bytes digest) &&
      decide (input[32]? = some domGrind)

@[simp] theorem literal_grinding_input_has_exact_grammar
    (state : MachineState) (nonce : NonceBytes) :
    hasGrindingInputGrammarAt state.digest (grindInput state nonce) = true := by
  simp [hasGrindingInputGrammarAt, grindInput, bytes_length]

/-- The stage tag and checkpoint digest retained by a work-nonce submission.
Exploratory probes are made at `transition.before.core.digest`, before the
selected nonce is submitted and absorbed. -/
def submittedWorkCheckpoint?
    (transition : FutureFreeTransition) : Option (WorkStage × Digest256) :=
  match transition.event with
  | .proverWorkNonce stage _nonce =>
      some (stage, transition.before.core.digest)
  | _ => none

/-- All actual checkpoint digests at which the verifier received the selected
nonce for one stage.  The literal deployed path has one; retaining a list
makes the definition total for rejected or malformed operational paths. -/
def submittedWorkCheckpointDigests
    (state : FutureFreeVerifierState) (stage : WorkStage) : List Digest256 :=
  state.transitions.filterMap fun transition =>
    match submittedWorkCheckpoint? transition with
    | some (foundStage, digest) =>
        if foundStage = stage then some digest else none
    | none => none

/-- An actual query record matches stage `stage` when it has the grinding
grammar at one of that stage's recorded checkpoint digests. -/
def queryMatchesSubmittedWorkStage
    (state : FutureFreeVerifierState) (stage : WorkStage)
    (record : QueryRecord) : Bool :=
  (submittedWorkCheckpointDigests state stage).any fun digest =>
    hasGrindingInputGrammarAt digest record.input

/-- Exact observable stage count in one actual prover history. -/
def stageGrindingQueryCount
    (history : List QueryRecord) (state : FutureFreeVerifierState)
    (stage : WorkStage) : Nat :=
  (history.filter (queryMatchesSubmittedWorkStage state stage)).length

theorem stage_grinding_query_count_le_history_length
    (history : List QueryRecord) (state : FutureFreeVerifierState)
    (stage : WorkStage) :
    stageGrindingQueryCount history state stage ≤ history.length := by
  unfold stageGrindingQueryCount
  exact List.length_filter_le _ _

/-! ## Actual initial-run projection -/

/-- The three separately classified counts of the actual initial adversary
history. -/
def actualRootStageGrindingQueryUse
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) : StageGrindingQueryUse where
  batch := stageGrindingQueryCount runtime.node.proverHistory
    runtime.verifierFinalState .batch
  fold := stageGrindingQueryCount runtime.node.proverHistory
    runtime.verifierFinalState .fold
  final := stageGrindingQueryCount runtime.node.proverHistory
    runtime.verifierFinalState .final

theorem actual_root_stage_grinding_counts_le_prover_history
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) :
    (actualRootStageGrindingQueryUse runtime).batch ≤
        runtime.node.proverHistory.length ∧
      (actualRootStageGrindingQueryUse runtime).fold ≤
        runtime.node.proverHistory.length ∧
      (actualRootStageGrindingQueryUse runtime).final ≤
        runtime.node.proverHistory.length := by
  exact ⟨stage_grinding_query_count_le_history_length _ _ .batch,
    stage_grinding_query_count_le_history_length _ _ .fold,
    stage_grinding_query_count_le_history_length _ _ .final⟩

/-- A single all-SHA `Q` bound is a conservative bound for each of the three
separately defined work-search counts.  It does not identify the counts. -/
theorem actual_root_stage_grinding_counts_le_Q
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) (Q : Nat)
    (rootBound : runtime.node.proverHistory.length ≤ Q) :
    (actualRootStageGrindingQueryUse runtime).batch ≤ Q ∧
      (actualRootStageGrindingQueryUse runtime).fold ≤ Q ∧
      (actualRootStageGrindingQueryUse runtime).final ≤ Q := by
  rcases actual_root_stage_grinding_counts_le_prover_history runtime with
    ⟨batch, fold, final⟩
  exact ⟨batch.trans rootBound, fold.trans rootBound,
    final.trans rootBound⟩

/-- Exact, sample-local work-cap predicate.  This exposes the actual three
classified counts rather than accepting a caller-provided count record. -/
def ActualRootStageGrindingWithin
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (batchCap foldCap finalCap : Nat) : Prop :=
  (actualRootStageGrindingQueryUse runtime).batch ≤ batchCap ∧
    (actualRootStageGrindingQueryUse runtime).fold ≤ foldCap ∧
    (actualRootStageGrindingQueryUse runtime).final ≤ finalCap

theorem actual_root_stage_grinding_within_of_Q_caps
    {TapeIdentity Statement Proof Payload : Type u}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload) (Q batchCap foldCap finalCap : Nat)
    (rootBound : runtime.node.proverHistory.length ≤ Q)
    (batchReserve : Q ≤ batchCap)
    (foldReserve : Q ≤ foldCap)
    (finalReserve : Q ≤ finalCap) :
    ActualRootStageGrindingWithin runtime batchCap foldCap finalCap := by
  rcases actual_root_stage_grinding_counts_le_Q runtime Q rootBound with
    ⟨batch, fold, final⟩
  exact ⟨batch.trans batchReserve, fold.trans foldReserve,
    final.trans finalReserve⟩

#print axioms stage_grinding_query_count_le_history_length
#print axioms literal_grinding_input_has_exact_grammar
#print axioms actual_root_stage_grinding_counts_le_prover_history
#print axioms actual_root_stage_grinding_counts_le_Q
#print axioms actual_root_stage_grinding_within_of_Q_caps

end

end AspisK1.V7Tag73ActualGrindingQueryAccounting
