import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73UnqueriedChallengeFiberProbability
import AspisFormal.K1.V7Tag73Q16TargetAudit
import AspisFormal.K1.V7Tag73UnqueriedOutputObliviousReplay
import AspisFormal.K1.V7Tag73ExactCompilerTargetClean
import AspisFormal.K1.V7Tag73OracleTableProvenance
import AspisFormal.K1.V7Tag73ExactSourceAcceptanceModel
import AspisFormal.K1.V7Tag73SharedShaGrammar
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent

/-!
# Coverage audit for the exact Tag-73 plain-ROM target event

`exactPlainRomTargetEvent` is the causal collision/literal-prefix event of the
corrected dummy-seeded scheduler.  Its implemented coefficient is exactly

`F + F.choose 2 + F * G`.

It does not contain the accepted-completion fibers of an unqueried deployed
challenge-output half.  The concrete restoration scheduler does not need
such a term: it scans for the first occurrence of either member of the paired
squeeze.  If neither input occurs, the no-pair theorem proves that programming
arbitrary values at both fresh points preserves the identical same-start
prover path.  If only the advance input occurs, output-oblivious replay proves
that arbitrary programming of the absent output half preserves the actual
path through the advance.  A fresh verifier coin may therefore be ignored by
the prover; it is not a guessed decoded challenge.

`V7Tag73UnqueriedChallengeFiberProbability` remains a sound bound for an
alternative *query-only* fork theorem that insists every output half be
represented by a pre-answer decoded-value prediction.  It uses a separate
36-coordinate tape, whereas the concrete compiler has one `F`-coordinate
master tape with `F >= 1511`; it is deliberately not added to the plain
concrete compiler error below.

This leaf kernel-checks the alternative query-only arithmetic reserve, the
mismatch between the two finite-tape types, and the fact that q16 contributes
no probabilistic forest-failure term after successful strict refinement.

The prior unseeded target event started its accumulated output set at `∅`
and therefore did not protect the dummy initial verifier digest
`zeroDigest256`.  A later sampled coordinate could equal zero without a hit,
after which a positive child checkpoint could inherit the root-programmed
`0 || 0x01`, `0 || 0x02` pair.  The corrected target tree seeds the initial
digest, adding one target at every coordinate.  Its coefficient is

`F.choose 2 + F * (G + 1)`,

an additional `F / 2^256`, not a challenge-decoder fiber.  Even with that
repair, the remaining positive compiler lemma is deterministic: chronological
lineage must map any inherited programmed pair at a positive child checkpoint
to an earlier protected master coordinate.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactProbabilityCoverageAudit

set_option maxRecDepth 8192

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73UnqueriedChallengeFiberProbability
open AspisK1.V7Tag73Q16TargetAudit
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73UnqueriedOutputObliviousReplay
open AspisK1.V7Tag73ExactCompilerTargetClean
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73GlobalForwardReferenceBound
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73SeededTargetArithmetic
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73OracleTableProvenance
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73CoupledReplayAlignment
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73SharedShaGrammar
open AspisK1.V7Tag73ExactFixedInstanceEvent

noncomputable section

universe u

/-! ## What the corrected exact target charges -/

/-- The coefficient before retaining the public initial digest.  This is kept
only to state the proved no-go and the exact delta to the corrected tree. -/
def legacyUnseededTargetCoefficient
    (parameters : ExactCompilerResourceParameters) : Nat :=
  (unifiedFull256ExposureCap parameters).choose 2 +
    unifiedFull256ExposureCap parameters *
      globalFull256OracleCallCap parameters

def legacyUnseededTargetRawError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  (legacyUnseededTargetCoefficient parameters : ENNReal) /
    ((2 : ENNReal) ^ 256)

theorem exact_scheduler_target_coefficient_is_seed_plus_collision_plus_literal_prefix
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerTargetCoefficient parameters =
      unifiedFull256ExposureCap parameters +
        (unifiedFull256ExposureCap parameters).choose 2 +
        unifiedFull256ExposureCap parameters *
          globalFull256OracleCallCap parameters := by
  unfold exactCompilerTargetCoefficient seededTargetCoefficient
  ring

/-- The concrete scheduler charges exactly the seeded causal target.  The
absence of a challenge-fiber summand is justified operationally below by the
same-start no-pair and output-oblivious replay theorems; it is not represented
by defining an extra coefficient to be zero. -/
theorem concrete_plain_rom_coefficient_is_seeded_causal_target
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerTargetCoefficient parameters =
      unifiedFull256ExposureCap parameters +
        (unifiedFull256ExposureCap parameters).choose 2 +
        unifiedFull256ExposureCap parameters *
          globalFull256OracleCallCap parameters := by
  exact
    exact_scheduler_target_coefficient_is_seed_plus_collision_plus_literal_prefix
      parameters

/-! ## Exact initial-digest seed delta -/

/-- Retaining the dummy initial verifier digest contributes one target at
every one of the `F` sampled coordinates. -/
def initialVerifierDigestSeedCoefficient
    (parameters : ExactCompilerResourceParameters) : Nat :=
  unifiedFull256ExposureCap parameters

theorem initial_digest_seeded_target_coefficient_expanded
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerTargetCoefficient parameters =
      (unifiedFull256ExposureCap parameters).choose 2 +
        unifiedFull256ExposureCap parameters *
          (globalFull256OracleCallCap parameters + 1) := by
  rw [exact_scheduler_target_coefficient_is_seed_plus_collision_plus_literal_prefix]
  ring

theorem exact_target_raw_error_is_legacy_plus_initial_digest_seed
    (parameters : ExactCompilerResourceParameters) :
    exactCompilerPositiveExposureError parameters =
      legacyUnseededTargetRawError parameters +
        (unifiedFull256ExposureCap parameters : ENNReal) /
          ((2 : ENNReal) ^ 256) := by
  unfold exactCompilerPositiveExposureError legacyUnseededTargetRawError
    legacyUnseededTargetCoefficient
  rw [exact_scheduler_target_coefficient_is_seed_plus_collision_plus_literal_prefix]
  push_cast
  simp only [ENNReal.add_div]
  ac_rfl

/-! ## Alternative query-only challenge-fiber reserve -/

/-- One query-only deployed verifier has 36 challenge-output completion sites.
This is the exact sum of their proved finite decoder-fiber caps.  It is not a
term in the concrete scheduler theorem. -/
def queryOnlyOneVerifierChallengeFiberCoefficient : Nat :=
  deployedChallengePredictionFiberCoefficient

/-- Conservative arithmetic reserve for an alternative query-only root and
at most `R` replay verifiers.  It is retained only to make the distinction
between the two proof strategies exact. -/
def queryOnlyRootAndReplayChallengeFiberCoefficient
    (parameters : ExactCompilerResourceParameters) : Nat :=
  (parameters.forkRequestCap + 1) *
    queryOnlyOneVerifierChallengeFiberCoefficient

def queryOnlyRootAndReplayChallengeFiberRawError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  (queryOnlyRootAndReplayChallengeFiberCoefficient parameters : ENNReal) /
    ((2 : ENNReal) ^ 256)

/-- Alternative query-only combined coefficient.  This definition is
arithmetic only and is not the plain concrete compiler coefficient. -/
def queryOnlyCollisionPrefixAndFiberCoefficient
    (parameters : ExactCompilerResourceParameters) : Nat :=
  exactCompilerTargetCoefficient parameters +
    queryOnlyRootAndReplayChallengeFiberCoefficient parameters

def queryOnlyCollisionPrefixAndFiberRawError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  (queryOnlyCollisionPrefixAndFiberCoefficient parameters : ENNReal) /
    ((2 : ENNReal) ^ 256)

def queryOnlyCollisionPrefixAndFiberExactCountError
    (parameters : ExactCompilerResourceParameters) : ENNReal :=
  ((queryOnlyCollisionPrefixAndFiberCoefficient parameters *
      (2 ^ 256) ^ (unifiedFull256ExposureCap parameters - 1) : Nat) :
      ENNReal) /
    (((2 : ENNReal) ^ 256) ^ unifiedFull256ExposureCap parameters)

theorem one_verifier_challenge_fiber_coefficient_has_36_terms :
    (deployedChallengeIds.map challengeCompletionFiberCap).length = 36 := by
  exact deployed_challenge_prediction_coefficient_has_36_terms

theorem root_and_replay_challenge_fiber_coefficient_expanded
    (parameters : ExactCompilerResourceParameters) :
    queryOnlyRootAndReplayChallengeFiberCoefficient parameters =
      (parameters.forkRequestCap + 1) *
        deployedChallengePredictionFiberCoefficient := by
  rfl

theorem exact_compiler_collision_prefix_and_fiber_coefficient_expanded
    (parameters : ExactCompilerResourceParameters) :
    queryOnlyCollisionPrefixAndFiberCoefficient parameters =
      unifiedFull256ExposureCap parameters +
        (unifiedFull256ExposureCap parameters).choose 2 +
        unifiedFull256ExposureCap parameters *
          globalFull256OracleCallCap parameters +
        (parameters.forkRequestCap + 1) *
          deployedChallengePredictionFiberCoefficient := by
  unfold queryOnlyCollisionPrefixAndFiberCoefficient
    queryOnlyRootAndReplayChallengeFiberCoefficient
    queryOnlyOneVerifierChallengeFiberCoefficient
  rw [exact_scheduler_target_coefficient_is_seed_plus_collision_plus_literal_prefix]

theorem root_and_replay_challenge_fiber_coefficient_le_fallback
    (parameters : ExactCompilerResourceParameters) :
    queryOnlyRootAndReplayChallengeFiberCoefficient parameters <=
      (parameters.forkRequestCap + 1) * (36 * 2 ^ 228) := by
  unfold queryOnlyRootAndReplayChallengeFiberCoefficient
    queryOnlyOneVerifierChallengeFiberCoefficient
  exact Nat.mul_le_mul_left (parameters.forkRequestCap + 1)
    deployed_challenge_prediction_coefficient_le_36_mul_two_pow_228

theorem exact_compiler_collision_prefix_and_fiber_coefficient_le_fallback
    (parameters : ExactCompilerResourceParameters) :
    queryOnlyCollisionPrefixAndFiberCoefficient parameters <=
      exactCompilerTargetCoefficient parameters +
        (parameters.forkRequestCap + 1) * (36 * 2 ^ 228) := by
  unfold queryOnlyCollisionPrefixAndFiberCoefficient
  exact Nat.add_le_add_left
    (root_and_replay_challenge_fiber_coefficient_le_fallback parameters) _

theorem exact_compiler_collision_prefix_and_fiber_raw_error_is_sum
    (parameters : ExactCompilerResourceParameters) :
    queryOnlyCollisionPrefixAndFiberRawError parameters =
      exactCompilerPositiveExposureError parameters +
        queryOnlyRootAndReplayChallengeFiberRawError parameters := by
  unfold queryOnlyCollisionPrefixAndFiberRawError
    queryOnlyCollisionPrefixAndFiberCoefficient
    exactCompilerPositiveExposureError
    queryOnlyRootAndReplayChallengeFiberRawError
  push_cast
  rw [ENNReal.add_div]

/-! ## Why the query-only theorem cannot be silently composed anyway -/

theorem exact_compiler_master_tape_length_at_least_1511
    (parameters : ExactCompilerResourceParameters) :
    1511 <= (exactCompilerTargetCaps parameters).length := by
  rw [exact_compiler_target_caps_length]
  unfold unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
    deployedFull256VerifierCallCap
  omega

/-- This type-level mismatch is why the already proved 36-coordinate fiber
probability cannot be added directly to `exactPlainRomTargetEvent`. -/
theorem exact_compiler_tape_length_ne_challenge_completion_tape_length
    (parameters : ExactCompilerResourceParameters) :
    (exactCompilerTargetCaps parameters).length ≠
      (deployedChallengeIds.map challengeCompletionFiberCap).length := by
  rw [deployed_challenge_prediction_coefficient_has_36_terms]
  have lower := exact_compiler_master_tape_length_at_least_1511 parameters
  omega

/-! ## Deterministic zero-loss classes -/

/-- Strict checked refinement already supplies the work-erased refinement
used by the exact q16-forest theorem.  Hence q16 branching itself needs no
random-oracle failure coefficient on this operational success domain. -/
theorem successful_strict_checked_refinement_has_exact_q16_forest
    (table : FixedOracleTable) (tape : DeployedFixedTape)
    (raw : InteractiveRawTrace)
    (success : checkedRefine table exactDeterministicDecoders tape = some raw) :
    ExactQ16OperationalForestExists table tape := by
  obtain ⟨strictRun, _wellFormed⟩ :=
    checked_refinement_is_well_formed table exactDeterministicDecoders tape raw
      success
  have erasedRun :=
    refinement_success_survives_work_erasure table tape raw strictRun
  exact successful_work_erased_refinement_has_exact_q16_forest table tape raw
    erasedRun

/-!
Public-instance binding is likewise deterministic on
`exactSourceRefinementEvent`: the checked raw return fixes program, release,
statement, attempt, and proof-account identifiers before any restoration.
Therefore it contributes no random-oracle coefficient.  The imported theorem
`exact_source_refinement_event_preserves_public_bindings` is the exact
operational statement.

Membership in `exactSourceRefinementEvent` already contains the actual strict
`checkedRefine` result over the root scheduler's final first-hit table.  It is
the deterministic source-refinement domain, not another probabilistic bad
event.  Relating pinned Rust/SBF terminal acceptance to that event remains the
named source/tool correspondence boundary.  The two typed 208-bit Merkle
authentication trees and their extraction/list-decoding errors remain in the
explicit K1.2--K1.5 premises; they are not full-256 coordinates and are not
hidden in the plain-ROM coefficient.

Resource failure is different.  It is empty only after a concrete
`WithinBudget` proof; timeout is empty only after a hard runtime cap strictly
below `timeoutCutoff`.  Without the latter, the honest additional term is
`expectedNatCost / timeoutCutoff`, as proved by
`exact_compiler_timeout_probability_le_expected_div`.  Neither resource
failure nor timeout is absorbed into the
`F + F.choose 2 + F * G` coefficient.

The 35-, 31-, and 34-bit work stages add no separate probabilistic event on
`exactSourceRefinementEvent`.  Successful strict `checkedRefine` already
contains the three selected nonce checks at their distinct transcript states;
the work-erasure theorem removes only those rejection predicates for the
interactive ancestor.  Their actual SHA calls remain counted in `F` and `G`.
There is no division by grinding work and no merger of the three stages.
-/

/-! ## The exact deterministic freshness residual -/

/-- The minimal structural request rule that avoids reforking the inherited
parent squeeze from a mutated child base.  Root requests may be repeated:
they are always recomputed from the immutable root base.  A non-root child
must select a transition after its inherited transition zero.

This predicate does not assert lookup freshness.  For positive child
transition indices, freshness still requires the chronological
digest-to-master-coordinate theorem described below. -/
def AvoidsInheritedChildTransition
    (request : ConcreteRestorationRequest) : Prop :=
  request.nodeId = 0 ∨ request.verifierTransitionIndex ≠ 0

theorem root_request_avoids_inherited_child_transition
    (request : ConcreteRestorationRequest) (root : request.nodeId = 0) :
    AvoidsInheritedChildTransition request := by
  exact Or.inl root

theorem positive_child_transition_avoids_inherited_child_transition
    (request : ConcreteRestorationRequest)
    (positive : 0 < request.verifierTransitionIndex) :
    AvoidsInheritedChildTransition request := by
  exact Or.inr (Nat.ne_of_gt positive)

/-- A pre-existing output lookup failure is independent of both new uniform
fork coordinates.  It therefore cannot be repaired or probability-bounded by
a decoder fiber for those coordinates. -/
theorem inherited_output_conflict_survives_every_new_fork_coin
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (distinct : outputInput ≠ advanceInput)
    (found : lookupEntry state outputInput = some entry) :
    ∀ forkOutput forkAdvance : Digest256,
      programConcretePair limits order state outputInput advanceInput
        forkOutput forkAdvance =
          .failed .outputInputAlreadyDefined 0 := by
  intro forkOutput forkAdvance
  exact existing_output_lookup_conflict_is_coordinate_independent limits order
    state outputInput advanceInput entry distinct found forkOutput forkAdvance

/-- The analogous advance-input conflict is equally independent of the new
coordinates once the output input is known absent. -/
theorem inherited_advance_conflict_survives_every_new_fork_coin
    (limits : OracleLimits) (order : PairProgrammingOrder)
    (state : OracleState) (outputInput advanceInput : ShaInput)
    (entry : AspisK1.V7FsAokExperiment.TableEntry)
    (distinct : outputInput ≠ advanceInput)
    (outputMissing : lookupEntry state outputInput = none)
    (found : lookupEntry state advanceInput = some entry) :
    ∀ forkOutput forkAdvance : Digest256,
      programConcretePair limits order state outputInput advanceInput
        forkOutput forkAdvance =
          .failed .advanceInputAlreadyDefined 0 := by
  intro forkOutput forkAdvance
  exact existing_advance_lookup_conflict_is_coordinate_independent limits order
    state outputInput advanceInput entry distinct outputMissing found forkOutput
      forkAdvance

/-! ## Whole-scheduler projection of direct fork cleanliness -/

/-- The `operationalCapsFrom` index has exactly one cell per scheduler
coordinate.  This recursive reindexing is definitionally head/tail preserving,
which lets the trace interpreter and its causal target tree run in lockstep
without an opaque cast. -/
def operationalIndexedTape
    (globalOracleCalls step : Nat) :
    (remaining : Nat) → FreshAnswerTape Digest256 remaining →
      FreshAnswerTape Digest256
        (operationalCapsFrom step remaining globalOracleCalls).length
  | 0, tape => tape
  | remaining + 1, tape =>
      (tape.1,
        operationalIndexedTape globalOracleCalls (step + 1) remaining tape.2)

/-- Read the same indexed tape back as the literal coordinate tape consumed
by `runUnifiedExposureTrace`. -/
def operationalTapeCoordinates
    (globalOracleCalls step : Nat) :
    (remaining : Nat) → FreshAnswerTape Digest256
        (operationalCapsFrom step remaining globalOracleCalls).length →
      FreshAnswerTape Digest256 remaining
  | 0, tape => tape
  | remaining + 1, tape =>
      (tape.1,
        operationalTapeCoordinates globalOracleCalls (step + 1) remaining
          tape.2)

theorem operational_indexed_tape_coordinates_roundtrip
    (globalOracleCalls step remaining : Nat)
    (tape : FreshAnswerTape Digest256
      (operationalCapsFrom step remaining globalOracleCalls).length) :
    operationalIndexedTape globalOracleCalls step remaining
        (operationalTapeCoordinates globalOracleCalls step remaining tape) =
      tape := by
  induction remaining generalizing step with
  | zero =>
      cases tape
      rfl
  | succ remaining ih =>
      change Digest256 × FreshAnswerTape Digest256
        (operationalCapsFrom (step + 1) remaining globalOracleCalls).length
          at tape
      rcases tape with ⟨answer, tail⟩
      simp only [operationalTapeCoordinates, operationalIndexedTape]
      rw [ih (step + 1) tail]

theorem operational_indexed_tape_preserves_coordinate_list
    (globalOracleCalls step remaining : Nat)
    (tape : FreshAnswerTape Digest256 remaining) :
    freshAnswerTapeToList
        (operationalIndexedTape globalOracleCalls step remaining tape) =
      freshAnswerTapeToList tape := by
  induction remaining generalizing step with
  | zero =>
      cases tape
      rfl
  | succ remaining ih =>
      change Digest256 × FreshAnswerTape Digest256 remaining at tape
      rcases tape with ⟨answer, tail⟩
      simp only [operationalIndexedTape, freshAnswerTapeToList]
      exact congrArg (List.cons answer) (ih (step + 1) tail)

/-- Reindexing by the causal cap list does not change the executable exposure
trace.  This is stronger than equality of answer lists: actors, inputs,
frozen histories, fork templates, and pair association are preserved
record-for-record. -/
theorem run_unified_exposure_trace_operational_indexed_tape
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining) :
    runUnifiedExposureTrace transitionFuel
        (operationalCapsFrom step remaining globalOracleCalls).length cursor
        (operationalIndexedTape globalOracleCalls step remaining tape) =
      runUnifiedExposureTrace transitionFuel remaining cursor tape := by
  induction remaining generalizing step cursor with
  | zero =>
      cases tape
      rfl
  | succ remaining ih =>
      cases request : seekUnifiedExposure transitionFuel cursor with
      | halted =>
          simp only [operationalCapsFrom, List.length_cons,
            operationalIndexedTape, runUnifiedExposureTrace, request]
          exact congrArg (List.cons (.padding tape.1))
            (ih (step + 1)
              (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2)
      | transitionLimit =>
          simp only [operationalCapsFrom, List.length_cons,
            operationalIndexedTape, runUnifiedExposureTrace, request]
          exact congrArg (List.cons (.padding tape.1))
            (ih (step + 1)
              (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2)
      | machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          simp only [operationalCapsFrom, List.length_cons,
            operationalIndexedTape, runUnifiedExposureTrace, request]
          exact congrArg (List.cons (.machineFresh actor input tape.1))
            (ih (step + 1)
              (.machine limits limitBound actor
                (freshQueryState actor state input tape.1)
                (nextProgram tape.1) remainingFuel
                (fresh_query_state_preserves_history_total_coherent actor state
                  input tape.1 coherent) onReturned) tape.2)
      | forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          simp only [operationalCapsFrom, List.length_cons,
            operationalIndexedTape, runUnifiedExposureTrace, request]
          exact congrArg
            (List.cons (.forkOutput frozenHistory outputInput advanceInput
              template tape.1))
            (ih (step + 1)
              (.forkAdvance frozenHistory pairRoom outputInput advanceInput
                template tape.1 next) tape.2)
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          simp only [operationalCapsFrom, List.length_cons,
            operationalIndexedTape, runUnifiedExposureTrace, request]
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := tape.1 }
          exact congrArg (List.cons (.forkAdvance scheduled))
            (ih (step + 1) (next scheduled.configuration) tape.2)

/-- Exact association between the output record and its immediately following
scheduled advance record.  All these fields are definitionally shared by the
actual trace interpreter; keeping them explicit prevents an arbitrary adjacent
pair of record constructors from being mistaken for one scheduler fork. -/
structure AdjacentForkRecordsExact
    (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (forkOutput : Digest256) (scheduled : ScheduledForkCoins) : Prop where
  frozenHistoryEq : scheduled.frozenHistory = frozenHistory
  outputInputEq : scheduled.outputInput = outputInput
  advanceInputEq : scheduled.advanceInput = advanceInput
  templateEq : scheduled.template = template
  forkOutputEq : scheduled.forkOutput = forkOutput

/-- Extend the accumulated set exactly as the causal tree does.  Padding is
not an exposure and therefore does not enter `seen`; all other records are
actual sampled coordinates. -/
def extendUnifiedExposureSeen
    (seen : Finset Digest256) : UnifiedExposureRecord → Finset Digest256
  | .padding _answer => seen
  | record => insert record.answer seen

/-- Every complete adjacent fork pair in a trace is clean at the exact
pre-output accumulated `seen` set.  A final dangling output coordinate is not
asserted to be a pair, because a capped tape may end between the two fork
coordinates. -/
def EveryAdjacentDirectForkPairClean :
    Finset Digest256 → List UnifiedExposureRecord → Prop
  | _seen, [] => True
  | seen,
      .forkOutput frozenHistory outputInput advanceInput template forkOutput ::
        .forkAdvance scheduled :: rest =>
      AdjacentForkRecordsExact frozenHistory outputInput advanceInput template
          forkOutput scheduled ∧
        DirectForkCoordinatesClean seen frozenHistory outputInput advanceInput
          forkOutput scheduled.forkAdvance ∧
        EveryAdjacentDirectForkPairClean
          (insert scheduled.forkAdvance (insert forkOutput seen)) rest
  | seen, record :: rest =>
      EveryAdjacentDirectForkPairClean
        (extendUnifiedExposureSeen seen record) rest

theorem every_adjacent_direct_fork_pair_clean_head
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration)
    (forkOutput : Digest256) (scheduled : ScheduledForkCoins)
    (rest : List UnifiedExposureRecord)
    (clean : EveryAdjacentDirectForkPairClean seen
      (.forkOutput frozenHistory outputInput advanceInput template forkOutput ::
        .forkAdvance scheduled :: rest)) :
    AdjacentForkRecordsExact frozenHistory outputInput advanceInput template
        forkOutput scheduled ∧
      DirectForkCoordinatesClean seen frozenHistory outputInput advanceInput
        forkOutput scheduled.forkAdvance := by
  exact ⟨clean.1, clean.2.1⟩

/-- Chronological consequences for one record at its exact pre-coordinate
`seen` set. -/
def ExposureCoordinateChronologicallyClean
    (seen : Finset Digest256) : UnifiedExposureRecord → Prop
  | .padding _answer => True
  | .machineFresh _actor input answer =>
      answer ∉ seen ∧ ¬ HasLiteralStatePrefix answer input
  | .forkOutput _history outputInput advanceInput _template answer =>
      answer ∉ seen ∧
        ¬ HasLiteralStatePrefix answer outputInput ∧
        ¬ HasLiteralStatePrefix answer advanceInput
  | .forkAdvance scheduled =>
      scheduled.forkAdvance ∉ seen ∧
        ¬ HasLiteralStatePrefix scheduled.forkAdvance scheduled.outputInput ∧
        ¬ HasLiteralStatePrefix scheduled.forkAdvance scheduled.advanceInput

/-- Chronological consequences retained for every non-padding coordinate.
Each sampled output is new relative to all earlier sampled outputs and avoids
the literal state prefix of the input(s) known at its coordinate. -/
def EveryNonpaddingExposureChronologicallyClean :
    Finset Digest256 → List UnifiedExposureRecord → Prop
  | _seen, [] => True
  | seen, record :: rest =>
      ExposureCoordinateChronologicallyClean seen record ∧
        EveryNonpaddingExposureChronologicallyClean
          (extendUnifiedExposureSeen seen record) rest

def nonpaddingExposureAnswers :
    List UnifiedExposureRecord → List Digest256
  | [] => []
  | .padding _answer :: rest => nonpaddingExposureAnswers rest
  | record :: rest => record.answer :: nonpaddingExposureAnswers rest

/-- List-level characterization matching the proof-only
`ActiveExposureAnswer` predicate used by downstream node provenance, without
importing that downstream certificate module here. -/
theorem mem_nonpaddingExposureAnswers_iff
    (records : List UnifiedExposureRecord) (answer : Digest256) :
    answer ∈ nonpaddingExposureAnswers records ↔
      ∃ record ∈ records,
        (match record with
          | .padding _answer => False
          | _ => record.answer = answer) := by
  induction records with
  | nil =>
      simp [nonpaddingExposureAnswers]
  | cons record records ih =>
      cases record <;>
        simp [nonpaddingExposureAnswers, ih, UnifiedExposureRecord.answer,
          eq_comm]

def accumulatedExposureSeen
    (initialSeen : Finset Digest256)
    (priorRecords : List UnifiedExposureRecord) : Finset Digest256 :=
  priorRecords.foldl extendUnifiedExposureSeen initialSeen

theorem exposure_seen_subset_extend
    (seen : Finset Digest256) (record : UnifiedExposureRecord) :
    seen ⊆ extendUnifiedExposureSeen seen record := by
  cases record <;> simp [extendUnifiedExposureSeen]

theorem initial_seen_subset_accumulated_exposure_seen
    (initialSeen : Finset Digest256)
    (records : List UnifiedExposureRecord) :
    initialSeen ⊆ accumulatedExposureSeen initialSeen records := by
  induction records generalizing initialSeen with
  | nil =>
      exact fun _ member => member
  | cons record records ih =>
      exact (exposure_seen_subset_extend initialSeen record).trans
        (ih (extendUnifiedExposureSeen initialSeen record))

theorem nonpadding_answer_mem_accumulated_exposure_seen
    (initialSeen : Finset Digest256)
    (records : List UnifiedExposureRecord)
    (answer : Digest256)
    (member : answer ∈ nonpaddingExposureAnswers records) :
    answer ∈ accumulatedExposureSeen initialSeen records := by
  induction records generalizing initialSeen with
  | nil =>
      simp [nonpaddingExposureAnswers] at member
  | cons record records ih =>
      cases record with
      | padding paddingAnswer =>
          exact ih initialSeen member
      | machineFresh actor input headAnswer =>
          simp only [nonpaddingExposureAnswers, List.mem_cons] at member
          rcases member with rfl | member
          · exact initial_seen_subset_accumulated_exposure_seen
              (insert answer initialSeen) records
              (Finset.mem_insert_self answer initialSeen)
          · exact ih (insert headAnswer initialSeen) member
      | forkOutput frozenHistory outputInput advanceInput template headAnswer =>
          simp only [nonpaddingExposureAnswers, List.mem_cons] at member
          rcases member with rfl | member
          · exact initial_seen_subset_accumulated_exposure_seen
              (insert answer initialSeen) records
              (Finset.mem_insert_self answer initialSeen)
          · exact ih (insert headAnswer initialSeen) member
      | forkAdvance scheduled =>
          simp only [nonpaddingExposureAnswers, List.mem_cons] at member
          rcases member with rfl | member
          · exact initial_seen_subset_accumulated_exposure_seen
              (insert scheduled.forkAdvance initialSeen) records
              (Finset.mem_insert_self scheduled.forkAdvance initialSeen)
          · exact ih (insert scheduled.forkAdvance initialSeen) member

theorem chronologically_clean_coordinate_of_append
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ record :: laterRecords)) :
    ExposureCoordinateChronologicallyClean
      (accumulatedExposureSeen initialSeen priorRecords) record := by
  induction priorRecords generalizing initialSeen with
  | nil =>
      exact clean.1
  | cons head priorRecords ih =>
      apply ih (extendUnifiedExposureSeen initialSeen head)
      exact clean.2

theorem chronologically_clean_machine_coordinate_of_append
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ .machineFresh actor input answer :: laterRecords)) :
    answer ∉ accumulatedExposureSeen initialSeen priorRecords ∧
      ¬ HasLiteralStatePrefix answer input := by
  exact chronologically_clean_coordinate_of_append initialSeen priorRecords
    laterRecords (.machineFresh actor input answer) clean

theorem chronologically_clean_fork_output_coordinate_of_append
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration) (answer : Digest256)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ .forkOutput frozenHistory outputInput advanceInput
        template answer :: laterRecords)) :
    answer ∉ accumulatedExposureSeen initialSeen priorRecords ∧
      ¬ HasLiteralStatePrefix answer outputInput ∧
      ¬ HasLiteralStatePrefix answer advanceInput := by
  exact chronologically_clean_coordinate_of_append initialSeen priorRecords
    laterRecords
      (.forkOutput frozenHistory outputInput advanceInput template answer) clean

theorem chronologically_clean_fork_advance_coordinate_of_append
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (scheduled : ScheduledForkCoins)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ .forkAdvance scheduled :: laterRecords)) :
    scheduled.forkAdvance ∉
        accumulatedExposureSeen initialSeen priorRecords ∧
      ¬ HasLiteralStatePrefix scheduled.forkAdvance scheduled.outputInput ∧
      ¬ HasLiteralStatePrefix scheduled.forkAdvance scheduled.advanceInput := by
  exact chronologically_clean_coordinate_of_append initialSeen priorRecords
    laterRecords (.forkAdvance scheduled) clean

theorem chronologically_clean_machine_answer_ne_prior_nonpadding
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (actor : QueryActor) (input : ShaInput) (answer earlier : Digest256)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ .machineFresh actor input answer :: laterRecords))
    (earlierMember : earlier ∈ nonpaddingExposureAnswers priorRecords) :
    answer ≠ earlier := by
  intro equal
  have current := chronologically_clean_machine_coordinate_of_append
    initialSeen priorRecords laterRecords actor input answer clean
  apply current.1
  rw [equal]
  exact nonpadding_answer_mem_accumulated_exposure_seen initialSeen
    priorRecords earlier earlierMember

theorem chronologically_clean_fork_output_ne_prior_nonpadding
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (template : AtomicPairReplayConfiguration) (answer earlier : Digest256)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ .forkOutput frozenHistory outputInput advanceInput
        template answer :: laterRecords))
    (earlierMember : earlier ∈ nonpaddingExposureAnswers priorRecords) :
    answer ≠ earlier := by
  intro equal
  have current := chronologically_clean_fork_output_coordinate_of_append
    initialSeen priorRecords laterRecords frozenHistory outputInput advanceInput
      template answer clean
  apply current.1
  rw [equal]
  exact nonpadding_answer_mem_accumulated_exposure_seen initialSeen
    priorRecords earlier earlierMember

theorem chronologically_clean_fork_advance_ne_prior_nonpadding
    (initialSeen : Finset Digest256)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (scheduled : ScheduledForkCoins) (earlier : Digest256)
    (clean : EveryNonpaddingExposureChronologicallyClean initialSeen
      (priorRecords ++ .forkAdvance scheduled :: laterRecords))
    (earlierMember : earlier ∈ nonpaddingExposureAnswers priorRecords) :
    scheduled.forkAdvance ≠ earlier := by
  intro equal
  have current := chronologically_clean_fork_advance_coordinate_of_append
    initialSeen priorRecords laterRecords scheduled clean
  apply current.1
  rw [equal]
  exact nonpadding_answer_mem_accumulated_exposure_seen initialSeen
    priorRecords earlier earlierMember

theorem seen_member_is_fork_target
    (seen : Finset Digest256) (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput) (answer : Digest256)
    (member : answer ∈ seen) :
    answer ∈ operationalForkTargets seen frozenHistory outputInput
      advanceInput := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact (operational_target_hit_iff_mem seen frozenHistory answer).mp
    (.priorFullOutput member)

/-- Definitional one-coordinate eliminator for a causal target step.  Naming
this reduction avoids relying on simplifier transparency through the
proof-indexed `unifiedExposureTargetTreeFrom` recursion. -/
@[simp] theorem causal_target_tree_step_everHits_iff
    {Output : Type} [DecidableEq Output] {cap : Nat} {caps : List Nat}
    (targets : Finset Output) (targetCardLe : targets.card ≤ cap)
    (next : Output → CausalTargetTree Output caps)
    (tape : FreshAnswerTape Output (cap :: caps).length) :
    (CausalTargetTree.step targets targetCardLe next).everHits tape ↔
      tape.1 ∈ targets ∨ (next tape.1).everHits tape.2 := by
  rfl

/-! ## Dependent operational target-clean execution certificate -/

/-- A proof-relevant mirror of the actual `seekUnifiedExposure` execution.
Unlike the public list trace, the machine constructor retains the complete
pre-query `OracleState`, hence its cumulative history, and stores avoidance of
the full operational target set.  Fork constructors analogously retain the
actual frozen history and both pair inputs.

There is no restoration function, accepted result, or caller-selected outcome
in this certificate: every successor cursor and tape tail is fixed by the
actual request and current coordinate. -/
inductive UnifiedOperationalTargetCleanCertificate
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    (step remaining : Nat) →
      (seen : Finset Digest256) → seen.card ≤ step →
      UnifiedExposureCursor.{u} globalOracleCalls →
      FreshAnswerTape Digest256 remaining → Prop where
  | done
      (step : Nat) (seen : Finset Digest256) (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls) :
      UnifiedOperationalTargetCleanCertificate transitionFuel step 0 seen
        seenBound cursor PUnit.unit
  | halted
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (request : seekUnifiedExposure transitionFuel cursor = .halted)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining seen
        (seenBound.trans (Nat.le_add_right step 1))
        (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2) :
      UnifiedOperationalTargetCleanCertificate transitionFuel step
        (remaining + 1) seen seenBound cursor tape

  | transitionLimit
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (request : seekUnifiedExposure transitionFuel cursor = .transitionLimit)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining seen
        (seenBound.trans (Nat.le_add_right step 1))
        (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2) :
      UnifiedOperationalTargetCleanCertificate transitionFuel step
        (remaining + 1) seen seenBound cursor tape
  | machineFresh
      {MachineResult : Type u}
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (limits : OracleLimits) (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor) (state : OracleState) (input : ShaInput)
      (nextProgram : ShaOutput → OracleMachine MachineResult)
      (remainingFuel : Nat) (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)
      (onReturned : MachineResult → OracleState →
        UnifiedExposureCursor.{u} globalOracleCalls)
      (request : seekUnifiedExposure transitionFuel cursor =
        .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned)
      (answerAvoidsTargets :
        tape.1 ∉ operationalRequestTargets seen state.history input)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (.machine limits limitBound actor
          (freshQueryState actor state input tape.1) (nextProgram tape.1)
          remainingFuel
          (fresh_query_state_preserves_history_total_coherent actor state input
            tape.1 coherent) onReturned) tape.2) :
      UnifiedOperationalTargetCleanCertificate transitionFuel step
        (remaining + 1) seen seenBound cursor tape
  | forkOutput
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor.{u} globalOracleCalls)
      (request : seekUnifiedExposure transitionFuel cursor =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next)
      (answerAvoidsTargets :
        tape.1 ∉ operationalForkTargets seen frozenHistory outputInput
          advanceInput)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          tape.1 next) tape.2) :
      UnifiedOperationalTargetCleanCertificate transitionFuel step
        (remaining + 1) seen seenBound cursor tape
  | forkAdvance
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration) (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor.{u} globalOracleCalls)
      (request : seekUnifiedExposure transitionFuel cursor =
        .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next)
      (answerAvoidsTargets :
        tape.1 ∉ operationalForkTargets seen frozenHistory outputInput
          advanceInput)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (next (scheduledForkConfiguration template forkOutput tape.1)) tape.2) :
      UnifiedOperationalTargetCleanCertificate transitionFuel step
        (remaining + 1) seen seenBound cursor tape

/-- Proof-rich exposure at one concrete scheduler coordinate.  The machine
case retains the exact pre-query oracle state and its target-avoidance proof;
fork cases retain the exact frozen history. -/
inductive CertifiedOperationalExposure where
  | padding (answer : Digest256)
  | machineFresh (seen : Finset Digest256) (actor : QueryActor)
      (state : OracleState) (input : ShaInput) (answer : Digest256)
      (answerAvoidsTargets :
        answer ∉ operationalRequestTargets seen state.history input)
  | forkOutput (seen : Finset Digest256)
      (frozenHistory : List QueryRecord) (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration) (answer : Digest256)
      (answerAvoidsTargets :
        answer ∉ operationalForkTargets seen frozenHistory outputInput
          advanceInput)
  | forkAdvance (seen : Finset Digest256) (scheduled : ScheduledForkCoins)
      (answerAvoidsTargets :
        scheduled.forkAdvance ∉ operationalForkTargets seen
          scheduled.frozenHistory scheduled.outputInput scheduled.advanceInput)

def CertifiedOperationalExposure.erase :
    CertifiedOperationalExposure → UnifiedExposureRecord
  | .padding answer => .padding answer
  | .machineFresh _seen actor _state input answer _avoids =>
      .machineFresh actor input answer
  | .forkOutput _seen frozenHistory outputInput advanceInput template answer
      _avoids =>
      .forkOutput frozenHistory outputInput advanceInput template answer
  | .forkAdvance _seen scheduled _avoids => .forkAdvance scheduled

/-- Exact dependent shape of a machine-fresh request.  Pattern matching this
predicate exposes the limits, continuation and every proof field of the
literal `UnifiedExposureRequest.machineFresh`; it does not reconstruct a
request from the erased actor/input/answer record. -/
inductive IsExactMachineFreshRequest
    {globalOracleCalls : Nat} (actor : QueryActor) (state : OracleState)
    (input : ShaInput) : UnifiedExposureRequest.{u} globalOracleCalls → Prop where
  | witness
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (nextProgram : ShaOutput → OracleMachine MachineResult)
      (remainingFuel : Nat) (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)
      (onReturned : MachineResult → OracleState →
        UnifiedExposureCursor.{u} globalOracleCalls) :
      IsExactMachineFreshRequest actor state input
        (.machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned)

/-- Proof relation between a dependent cleanliness certificate and its unique
proof-rich coordinate trace.  It lives in `Prop`, so it does not illegally
eliminate the certificate proof into runtime data. -/
inductive CertifiedOperationalExposureTrace
    {globalOracleCalls : Nat} {transitionFuel : Nat} :
    {step remaining : Nat} → {seen : Finset Digest256} →
      {seenBound : seen.card ≤ step} →
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls} →
      {tape : FreshAnswerTape Digest256 remaining} →
      UnifiedOperationalTargetCleanCertificate transitionFuel step remaining
        seen seenBound cursor tape →
      List CertifiedOperationalExposure → Prop where
  | done
      (step : Nat) (seen : Finset Digest256) (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls) :
      CertifiedOperationalExposureTrace
        (.done step seen seenBound cursor) []
  | halted
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (request : seekUnifiedExposure transitionFuel cursor = .halted)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining seen
        (seenBound.trans (Nat.le_add_right step 1))
        (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2)
      (tailSnapshots : List CertifiedOperationalExposure)
      (tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots) :
      CertifiedOperationalExposureTrace (.halted step remaining seen seenBound
        cursor tape request tail) (.padding tape.1 :: tailSnapshots)
  | transitionLimit
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (request : seekUnifiedExposure transitionFuel cursor = .transitionLimit)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining seen
        (seenBound.trans (Nat.le_add_right step 1))
        (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2)
      (tailSnapshots : List CertifiedOperationalExposure)
      (tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots) :
      CertifiedOperationalExposureTrace
        (.transitionLimit step remaining seen seenBound cursor tape request tail)
        (.padding tape.1 :: tailSnapshots)
  | machineFresh
      {MachineResult : Type u}
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor) (state : OracleState) (input : ShaInput)
      (nextProgram : ShaOutput → OracleMachine MachineResult)
      (remainingFuel : Nat) (coherent : HistoryTotalCoherent state)
      (totalRoom : state.totalCalls < limits.totalCalls)
      (freshRoom : state.freshCalls < limits.freshCalls)
      (missing : lookupEntry state input = none)
      (onReturned : MachineResult → OracleState →
        UnifiedExposureCursor.{u} globalOracleCalls)
      (request : seekUnifiedExposure transitionFuel cursor =
        .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned)
      (avoids : tape.1 ∉
        operationalRequestTargets seen state.history input)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (.machine limits limitBound actor
          (freshQueryState actor state input tape.1) (nextProgram tape.1)
          remainingFuel
          (fresh_query_state_preserves_history_total_coherent actor state input
            tape.1 coherent) onReturned) tape.2)
      (tailSnapshots : List CertifiedOperationalExposure)
      (tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots) :
      CertifiedOperationalExposureTrace
        (.machineFresh step remaining seen seenBound cursor tape limits
          limitBound actor state input nextProgram remainingFuel coherent
          totalRoom freshRoom missing onReturned request avoids tail)
        (.machineFresh seen actor state input tape.1 avoids :: tailSnapshots)
  | forkOutput
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor.{u} globalOracleCalls)
      (request : seekUnifiedExposure transitionFuel cursor =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next)
      (avoids : tape.1 ∉ operationalForkTargets seen frozenHistory outputInput
        advanceInput)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          tape.1 next) tape.2)
      (tailSnapshots : List CertifiedOperationalExposure)
      (tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots) :
      CertifiedOperationalExposureTrace
        (.forkOutput step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template next request avoids tail)
        (.forkOutput seen frozenHistory outputInput advanceInput template tape.1
          avoids :: tailSnapshots)
  | forkAdvance
      (step remaining : Nat) (seen : Finset Digest256)
      (seenBound : seen.card ≤ step)
      (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
      (tape : FreshAnswerTape Digest256 (remaining + 1))
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AtomicPairReplayConfiguration) (forkOutput : Digest256)
      (next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor.{u} globalOracleCalls)
      (request : seekUnifiedExposure transitionFuel cursor =
        .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next)
      (avoids : tape.1 ∉ operationalForkTargets seen frozenHistory outputInput
        advanceInput)
      (tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (next (scheduledForkConfiguration template forkOutput tape.1)) tape.2)
      (tailSnapshots : List CertifiedOperationalExposure)
      (tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots) :
      CertifiedOperationalExposureTrace
        (.forkAdvance step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template forkOutput next request
          avoids tail)
        (.forkAdvance seen
          { frozenHistory := frozenHistory
            outputInput := outputInput
            advanceInput := advanceInput
            template := template
            forkOutput := forkOutput
            forkAdvance := tape.1 }
          avoids :: tailSnapshots)

theorem certified_operational_exposure_trace_exists
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    (certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape) :
    ∃ snapshots, CertifiedOperationalExposureTrace certificate snapshots := by
  induction certificate with
  | done step seen seenBound cursor =>
      exact ⟨[], .done step seen seenBound cursor⟩
  | halted step remaining seen seenBound cursor tape request tail ih =>
      obtain ⟨tailSnapshots, tailTrace⟩ := ih
      exact ⟨.padding tape.1 :: tailSnapshots,
        .halted step remaining seen seenBound cursor tape request tail
          tailSnapshots tailTrace⟩
  | transitionLimit step remaining seen seenBound cursor tape request tail ih =>
      obtain ⟨tailSnapshots, tailTrace⟩ := ih
      exact ⟨.padding tape.1 :: tailSnapshots,
        .transitionLimit step remaining seen seenBound cursor tape request tail
          tailSnapshots tailTrace⟩
  | machineFresh step remaining seen seenBound cursor tape limits limitBound
      actor state input nextProgram remainingFuel coherent totalRoom freshRoom
      missing onReturned request avoids tail ih =>
      obtain ⟨tailSnapshots, tailTrace⟩ := ih
      exact ⟨.machineFresh seen actor state input tape.1 avoids :: tailSnapshots,
        .machineFresh step remaining seen seenBound cursor tape limits
          limitBound actor state input nextProgram remainingFuel coherent
          totalRoom freshRoom missing onReturned request avoids tail
          tailSnapshots tailTrace⟩
  | forkOutput step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template next request avoids tail ih =>
      obtain ⟨tailSnapshots, tailTrace⟩ := ih
      exact ⟨.forkOutput seen frozenHistory outputInput advanceInput template
          tape.1 avoids :: tailSnapshots,
        .forkOutput step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template next request avoids tail
          tailSnapshots tailTrace⟩
  | forkAdvance step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template forkOutput next request avoids tail ih =>
      obtain ⟨tailSnapshots, tailTrace⟩ := ih
      exact ⟨.forkAdvance seen
          { frozenHistory := frozenHistory
            outputInput := outputInput
            advanceInput := advanceInput
            template := template
            forkOutput := forkOutput
            forkAdvance := tape.1 }
          avoids :: tailSnapshots,
        .forkAdvance step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template forkOutput next request
          avoids tail tailSnapshots tailTrace⟩

/-- Erasing the proof-rich traversal is exactly the scheduler's literal flat
trace. -/
theorem certified_operational_exposure_trace_erases_to_trace
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {snapshots : List CertifiedOperationalExposure}
    (trace : CertifiedOperationalExposureTrace certificate snapshots) :
    snapshots.map CertifiedOperationalExposure.erase =
      runUnifiedExposureTrace transitionFuel remaining cursor tape := by
  induction trace with
  | done => rfl
  | halted step remaining seen seenBound cursor tape request tail
      tailSnapshots tailTrace ih =>
      simp [CertifiedOperationalExposure.erase, runUnifiedExposureTrace,
        request, ih]

  | transitionLimit step remaining seen seenBound cursor tape request tail
      tailSnapshots tailTrace ih =>
      simp [CertifiedOperationalExposure.erase, runUnifiedExposureTrace,
        request, ih]
  | machineFresh step remaining seen seenBound cursor tape limits limitBound
      actor state input nextProgram remainingFuel coherent totalRoom freshRoom
      missing onReturned request avoids tail tailSnapshots tailTrace ih =>
      simp [CertifiedOperationalExposure.erase, runUnifiedExposureTrace,
        request, ih]
  | forkOutput step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template next request avoids tail tailSnapshots
      tailTrace ih =>
      simp [CertifiedOperationalExposure.erase, runUnifiedExposureTrace,
        request, ih]
  | forkAdvance step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template forkOutput next request avoids tail
      tailSnapshots tailTrace ih =>
    simp [CertifiedOperationalExposure.erase, runUnifiedExposureTrace,
        request, ih, scheduledForkConfiguration,
        ScheduledForkCoins.configuration]

/-- A machine snapshot in the proof-rich traversal retains the literal cursor
whose `seekUnifiedExposure` request produced that snapshot. -/
theorem certified_operational_exposure_trace_machine_member_has_exact_request
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {snapshots : List CertifiedOperationalExposure}
    (trace : CertifiedOperationalExposureTrace certificate snapshots)
    {snapshotSeen : Finset Digest256} {actor : QueryActor}
    {state : OracleState} {input : ShaInput} {answer : Digest256}
    {avoids : answer ∉
      operationalRequestTargets snapshotSeen state.history input}
    (member : CertifiedOperationalExposure.machineFresh snapshotSeen actor
      state input answer avoids ∈ snapshots) :
    ∃ requestCursor : UnifiedExposureCursor.{u} globalOracleCalls,
      IsExactMachineFreshRequest actor state input
        (seekUnifiedExposure transitionFuel requestCursor) := by
  induction trace with
  | done =>
      simp at member
  | halted step remaining seen seenBound cursor tape request tail
      tailSnapshots tailTrace ih =>
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · cases headExact
      · exact ih tailMember
  | transitionLimit step remaining seen seenBound cursor tape request tail
      tailSnapshots tailTrace ih =>
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · cases headExact
      · exact ih tailMember
  | machineFresh step remaining seen seenBound cursor tape limits limitBound
      actorAt stateAt inputAt nextProgram remainingFuel coherent totalRoom
      freshRoom missing onReturned request avoidsAt tail tailSnapshots tailTrace
      ih =>
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · cases headExact
        refine ⟨cursor, ?_⟩
        rw [request]
        exact .witness limits limitBound nextProgram remainingFuel coherent
          totalRoom freshRoom missing onReturned
      · exact ih tailMember
  | forkOutput step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template next request avoidsAt tail tailSnapshots
      tailTrace ih =>
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · cases headExact
      · exact ih tailMember
  | forkAdvance step remaining seen seenBound cursor tape frozenHistory pairRoom
      outputInput advanceInput template forkOutput next request avoidsAt tail
      tailSnapshots tailTrace ih =>
      simp only [List.mem_cons] at member
      rcases member with headExact | tailMember
      · cases headExact
      · exact ih tailMember

/-- The literal dependent traversal from the root certificate to a cursor
after consuming exactly the supplied proof-rich prefix.  Unlike flat trace
membership, this relation retains every intervening `seekUnifiedExposure`
equation and the exact successor cursor chosen by that request. -/
inductive CertifiedOperationalTracePrefixCursor
    {globalOracleCalls transitionFuel : Nat} :
    {step remaining : Nat} → {seen : Finset Digest256} →
      {seenBound : seen.card ≤ step} →
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls} →
      {tape : FreshAnswerTape Digest256 remaining} →
      {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
        step remaining seen seenBound cursor tape} →
      {snapshots : List CertifiedOperationalExposure} →
      CertifiedOperationalExposureTrace certificate snapshots →
      List CertifiedOperationalExposure →
      UnifiedExposureCursor.{u} globalOracleCalls → Prop where
  | here
      {step remaining : Nat} {seen : Finset Digest256}
      {seenBound : seen.card ≤ step}
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tape : FreshAnswerTape Digest256 remaining}
      {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
        step remaining seen seenBound cursor tape}
      {snapshots : List CertifiedOperationalExposure}
      (trace : CertifiedOperationalExposureTrace certificate snapshots) :
      CertifiedOperationalTracePrefixCursor trace [] cursor
  | halted
      {step remaining : Nat} {seen : Finset Digest256}
      {seenBound : seen.card ≤ step}
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tape : FreshAnswerTape Digest256 (remaining + 1)}
      {request : seekUnifiedExposure transitionFuel cursor = .halted}
      {tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining seen
        (seenBound.trans (Nat.le_add_right step 1))
        (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2}
      {tailSnapshots priorSnapshots : List CertifiedOperationalExposure}
      {requestCursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots}
      (reached : CertifiedOperationalTracePrefixCursor tailTrace priorSnapshots
        requestCursor) :
      CertifiedOperationalTracePrefixCursor
        (.halted step remaining seen seenBound cursor tape request tail
          tailSnapshots tailTrace)
        (.padding tape.1 :: priorSnapshots) requestCursor
  | transitionLimit
      {step remaining : Nat} {seen : Finset Digest256}
      {seenBound : seen.card ≤ step}
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tape : FreshAnswerTape Digest256 (remaining + 1)}
      {request : seekUnifiedExposure transitionFuel cursor = .transitionLimit}
      {tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining seen
        (seenBound.trans (Nat.le_add_right step 1))
        (.halted : UnifiedExposureCursor.{u} globalOracleCalls) tape.2}
      {tailSnapshots priorSnapshots : List CertifiedOperationalExposure}
      {requestCursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots}
      (reached : CertifiedOperationalTracePrefixCursor tailTrace priorSnapshots
        requestCursor) :
      CertifiedOperationalTracePrefixCursor
        (.transitionLimit step remaining seen seenBound cursor tape request tail
          tailSnapshots tailTrace)
        (.padding tape.1 :: priorSnapshots) requestCursor
  | machineFresh
      {MachineResult : Type u}
      {step remaining : Nat} {seen : Finset Digest256}
      {seenBound : seen.card ≤ step}
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tape : FreshAnswerTape Digest256 (remaining + 1)}
      {limits : OracleLimits}
      {limitBound : limits.totalCalls ≤ globalOracleCalls}
      {actor : QueryActor} {state : OracleState} {input : ShaInput}
      {nextProgram : ShaOutput → OracleMachine MachineResult}
      {remainingFuel : Nat} {coherent : HistoryTotalCoherent state}
      {totalRoom : state.totalCalls < limits.totalCalls}
      {freshRoom : state.freshCalls < limits.freshCalls}
      {missing : lookupEntry state input = none}
      {onReturned : MachineResult → OracleState →
        UnifiedExposureCursor.{u} globalOracleCalls}
      {request : seekUnifiedExposure transitionFuel cursor =
        .machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned}
      {avoids : tape.1 ∉ operationalRequestTargets seen state.history input}
      {tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (.machine limits limitBound actor
          (freshQueryState actor state input tape.1) (nextProgram tape.1)
          remainingFuel
          (fresh_query_state_preserves_history_total_coherent actor state input
            tape.1 coherent) onReturned) tape.2}
      {tailSnapshots priorSnapshots : List CertifiedOperationalExposure}
      {requestCursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots}
      (reached : CertifiedOperationalTracePrefixCursor tailTrace priorSnapshots
        requestCursor) :
      CertifiedOperationalTracePrefixCursor
        (.machineFresh step remaining seen seenBound cursor tape limits
          limitBound actor state input nextProgram remainingFuel coherent
          totalRoom freshRoom missing onReturned request avoids tail
          tailSnapshots tailTrace)
        (.machineFresh seen actor state input tape.1 avoids :: priorSnapshots)
        requestCursor
  | forkOutput
      {step remaining : Nat} {seen : Finset Digest256}
      {seenBound : seen.card ≤ step}
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tape : FreshAnswerTape Digest256 (remaining + 1)}
      {frozenHistory : List QueryRecord}
      {pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls}
      {outputInput advanceInput : ShaInput}
      {template : AtomicPairReplayConfiguration}
      {next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor.{u} globalOracleCalls}
      {request : seekUnifiedExposure transitionFuel cursor =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next}
      {avoids : tape.1 ∉ operationalForkTargets seen frozenHistory
        outputInput advanceInput}
      {tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          tape.1 next) tape.2}
      {tailSnapshots priorSnapshots : List CertifiedOperationalExposure}
      {requestCursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots}
      (reached : CertifiedOperationalTracePrefixCursor tailTrace priorSnapshots
        requestCursor) :
      CertifiedOperationalTracePrefixCursor
        (.forkOutput step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template next request avoids tail
          tailSnapshots tailTrace)
        (.forkOutput seen frozenHistory outputInput advanceInput template tape.1
          avoids :: priorSnapshots) requestCursor
  | forkAdvance
      {step remaining : Nat} {seen : Finset Digest256}
      {seenBound : seen.card ≤ step}
      {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tape : FreshAnswerTape Digest256 (remaining + 1)}
      {frozenHistory : List QueryRecord}
      {pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls}
      {outputInput advanceInput : ShaInput}
      {template : AtomicPairReplayConfiguration} {forkOutput : Digest256}
      {next : AtomicPairReplayConfiguration →
        UnifiedExposureCursor.{u} globalOracleCalls}
      {request : seekUnifiedExposure transitionFuel cursor =
        .forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next}
      {avoids : tape.1 ∉ operationalForkTargets seen frozenHistory
        outputInput advanceInput}
      {tail : UnifiedOperationalTargetCleanCertificate transitionFuel
        (step + 1) remaining (insert tape.1 seen)
        ((Finset.card_insert_le tape.1 seen).trans
          (Nat.add_le_add_right seenBound 1))
        (next (scheduledForkConfiguration template forkOutput tape.1)) tape.2}
      {tailSnapshots priorSnapshots : List CertifiedOperationalExposure}
      {requestCursor : UnifiedExposureCursor.{u} globalOracleCalls}
      {tailTrace : CertifiedOperationalExposureTrace tail tailSnapshots}
      (reached : CertifiedOperationalTracePrefixCursor tailTrace priorSnapshots
        requestCursor) :
      CertifiedOperationalTracePrefixCursor
        (.forkAdvance step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template forkOutput next request
          avoids tail tailSnapshots tailTrace)
        (.forkAdvance seen
          { frozenHistory := frozenHistory
            outputInput := outputInput
            advanceInput := advanceInput
            template := template
            forkOutput := forkOutput
            forkAdvance := tape.1 }
          avoids :: priorSnapshots) requestCursor

/-- A machine constructor selected after an exact proof-rich prefix exposes
both the cursor reached by the dependent traversal and the literal request at
that cursor.  This is the prefix-sensitive form required to align a native
projected-machine constructor; it cannot be recovered from flat record
membership alone. -/
theorem certified_operational_trace_machine_after_prefix_has_exact_cursor
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    (priorSnapshots laterSnapshots : List CertifiedOperationalExposure)
    (snapshotSeen : Finset Digest256) (actor : QueryActor)
    (state : OracleState) (input : ShaInput) (answer : Digest256)
    (avoids : answer ∉
      operationalRequestTargets snapshotSeen state.history input)
    (trace : CertifiedOperationalExposureTrace certificate
      (priorSnapshots ++
        .machineFresh snapshotSeen actor state input answer avoids ::
          laterSnapshots)) :
    ∃ requestCursor : UnifiedExposureCursor.{u} globalOracleCalls,
      CertifiedOperationalTracePrefixCursor trace priorSnapshots
          requestCursor ∧
        IsExactMachineFreshRequest actor state input
          (seekUnifiedExposure transitionFuel requestCursor) := by
  induction priorSnapshots generalizing step remaining seen seenBound cursor
      tape certificate with
  | nil =>
      cases trace with
      | machineFresh step remaining seen seenBound cursor tape limits limitBound
          actor state input nextProgram remainingFuel coherent totalRoom
          freshRoom missing onReturned request avoids tail tailSnapshots
          tailTrace =>
        refine ⟨cursor, .here _, ?_⟩
        rw [request]
        exact .witness limits limitBound nextProgram remainingFuel coherent
          totalRoom freshRoom missing onReturned
  | cons priorHead priorSnapshots ih =>
      cases trace with
      | halted step remaining seen seenBound cursor tape request tail
          tailSnapshots tailTrace =>
        obtain ⟨requestCursor, reached, exactRequest⟩ := ih tailTrace
        exact ⟨requestCursor, .halted (request := request) reached,
          exactRequest⟩
      | transitionLimit step remaining seen seenBound cursor tape request tail
          tailSnapshots tailTrace =>
        obtain ⟨requestCursor, reached, exactRequest⟩ := ih tailTrace
        exact ⟨requestCursor,
          .transitionLimit (request := request) reached, exactRequest⟩
      | machineFresh step remaining seen seenBound cursor tape limits limitBound
          actorAt stateAt inputAt nextProgram remainingFuel coherent totalRoom
          freshRoom missing onReturned request avoidsAt tail tailSnapshots
          tailTrace =>
        obtain ⟨requestCursor, reached, exactRequest⟩ := ih tailTrace
        exact ⟨requestCursor, .machineFresh (request := request) reached,
          exactRequest⟩
      | forkOutput step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template next request avoidsAt tail
          tailSnapshots tailTrace =>
        obtain ⟨requestCursor, reached, exactRequest⟩ := ih tailTrace
        exact ⟨requestCursor, .forkOutput (request := request) reached,
          exactRequest⟩
      | forkAdvance step remaining seen seenBound cursor tape frozenHistory
          pairRoom outputInput advanceInput template forkOutput next request
          avoidsAt tail tailSnapshots tailTrace =>
        obtain ⟨requestCursor, reached, exactRequest⟩ := ih tailTrace
        exact ⟨requestCursor, .forkAdvance (request := request) reached,
          exactRequest⟩

private theorem list_map_eq_append_cons_elim
    {α β : Type*} (f : α → β) :
    ∀ (items : List α) (priorItems laterItems : List β) (item : β),
      items.map f = priorItems ++ item :: laterItems →
        ∃ priorSources source laterSources,
          items = priorSources ++ source :: laterSources ∧
          priorSources.map f = priorItems ∧
          f source = item ∧
          laterSources.map f = laterItems := by
  intro items priorItems
  induction priorItems generalizing items with
  | nil =>
      intro laterItems item equal
      cases items with
      | nil =>
          simp at equal
      | cons source laterSources =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at equal
          exact ⟨[], source, laterSources, rfl, rfl, equal.1, equal.2⟩
  | cons priorHead priorItems ih =>
      intro laterItems item equal
      cases items with
      | nil =>
          simp at equal
      | cons source sources =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at equal
          obtain ⟨priorSources, selected, laterSources, sourcesExact,
              priorExact, selectedExact, laterExact⟩ :=
            ih sources laterItems item equal.2
          refine ⟨source :: priorSources, selected, laterSources, ?_, ?_,
            selectedExact, laterExact⟩
          · simp only [List.cons_append, sourcesExact]
          · simp only [List.map_cons, priorExact, equal.1]

/-- Exact position of a machine exposure inside a dependent certificate.  In
particular `state` is the scheduler's actual pre-query state at the supplied
flat-trace prefix, not a state reconstructed from the erased record. -/
def CertifiedMachineExposureAtPrefix
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    (certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (actor : QueryActor) (state : OracleState) (input : ShaInput)
    (answer : Digest256) : Prop :=
  ∃ (snapshotSeen : Finset Digest256)
      (avoids : answer ∉
        operationalRequestTargets snapshotSeen state.history input)
      (priorSnapshots laterSnapshots : List CertifiedOperationalExposure)
      (snapshotTrace : CertifiedOperationalExposureTrace certificate
        (priorSnapshots ++
          .machineFresh snapshotSeen actor state input answer avoids ::
            laterSnapshots))
      (requestCursor : UnifiedExposureCursor.{u} globalOracleCalls),
    CertifiedOperationalTracePrefixCursor snapshotTrace priorSnapshots
        requestCursor ∧
      IsExactMachineFreshRequest actor state input
        (seekUnifiedExposure transitionFuel requestCursor) ∧
      priorSnapshots.map CertifiedOperationalExposure.erase = priorRecords ∧
      laterSnapshots.map CertifiedOperationalExposure.erase = laterRecords

/-- Prefix-keyed eliminator requested by the concrete replay provenance lane.
Any actual flat-trace machine record has an exact pre-query state in the
dependent certificate, together with the target-avoidance proof stored at
that same coordinate. -/
theorem certified_operational_machine_at_prefix_of_trace_decomposition
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    (certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape)
    (priorRecords laterRecords : List UnifiedExposureRecord)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (traceExact :
      runUnifiedExposureTrace transitionFuel remaining cursor tape =
        priorRecords ++ .machineFresh actor input answer :: laterRecords) :
    ∃ state, CertifiedMachineExposureAtPrefix certificate priorRecords
      laterRecords actor state input answer := by
  obtain ⟨snapshots, snapshotTrace⟩ :=
    certified_operational_exposure_trace_exists certificate
  have erasedExact :
      snapshots.map CertifiedOperationalExposure.erase =
        priorRecords ++ .machineFresh actor input answer :: laterRecords :=
    (certified_operational_exposure_trace_erases_to_trace snapshotTrace).trans
      traceExact
  obtain ⟨priorSnapshots, selected, laterSnapshots, snapshotsExact,
      priorExact, selectedExact, laterExact⟩ :=
    list_map_eq_append_cons_elim CertifiedOperationalExposure.erase snapshots
      priorRecords laterRecords (.machineFresh actor input answer) erasedExact
  cases selected with
  | padding paddingAnswer =>
      simp [CertifiedOperationalExposure.erase] at selectedExact
  | machineFresh snapshotSeen selectedActor state selectedInput selectedAnswer
      avoids =>
      simp only [CertifiedOperationalExposure.erase,
        UnifiedExposureRecord.machineFresh.injEq] at selectedExact
      rcases selectedExact with ⟨actorExact, inputExact, answerExact⟩
      subst selectedActor
      subst selectedInput
      subst selectedAnswer
      have selectedTrace : CertifiedOperationalExposureTrace certificate
          (priorSnapshots ++
            .machineFresh snapshotSeen actor state input answer avoids ::
              laterSnapshots) := by
        rw [← snapshotsExact]
        exact snapshotTrace
      obtain ⟨requestCursor, reached, exactRequest⟩ :=
        certified_operational_trace_machine_after_prefix_has_exact_cursor
          priorSnapshots laterSnapshots snapshotSeen actor state input answer
            avoids selectedTrace
      exact ⟨state, snapshotSeen, avoids, priorSnapshots, laterSnapshots,
        selectedTrace, requestCursor, reached, exactRequest, priorExact,
          laterExact⟩
  | forkOutput snapshotSeen frozenHistory outputInput advanceInput template
      forkAnswer avoids =>
      simp [CertifiedOperationalExposure.erase] at selectedExact
  | forkAdvance snapshotSeen scheduled avoids =>
      simp [CertifiedOperationalExposure.erase] at selectedExact

/-- Accessor for the exact request equation retained by the clean constructor
at this prefix.  The witness cursor is the actual cursor in the dependent
traversal, enabling native/erased scheduler alignment to identify its
pre-query state with a projected `ProjectedFreshReturnedTrace.requestState`. -/
theorem certified_machine_exposure_at_prefix_has_exact_request
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {priorRecords laterRecords : List UnifiedExposureRecord}
    {actor : QueryActor} {state : OracleState} {input : ShaInput}
    {answer : Digest256}
    (atPrefix : CertifiedMachineExposureAtPrefix certificate priorRecords
      laterRecords actor state input answer) :
    ∃ requestCursor : UnifiedExposureCursor.{u} globalOracleCalls,
      IsExactMachineFreshRequest actor state input
        (seekUnifiedExposure transitionFuel requestCursor) := by
  rcases atPrefix with ⟨snapshotSeen, avoids, priorSnapshots, laterSnapshots,
    snapshotTrace, requestCursor, _reached, exactRequest, _priorExact,
      _laterExact⟩
  exact ⟨requestCursor, exactRequest⟩

/-- Strong accessor retaining the exact proof-rich prefix traversal, not only
the terminal request equation.  A synchronized native/erased scheduler proof
can induct on `reached` to identify this request cursor with the cursor reached
after the native projected prefix. -/
theorem certified_machine_exposure_at_prefix_has_exact_traversal
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {priorRecords laterRecords : List UnifiedExposureRecord}
    {actor : QueryActor} {state : OracleState} {input : ShaInput}
    {answer : Digest256}
    (atPrefix : CertifiedMachineExposureAtPrefix certificate priorRecords
      laterRecords actor state input answer) :
    ∃ (snapshotSeen : Finset Digest256)
        (avoids : answer ∉
          operationalRequestTargets snapshotSeen state.history input)
        (priorSnapshots laterSnapshots : List CertifiedOperationalExposure)
        (snapshotTrace : CertifiedOperationalExposureTrace certificate
          (priorSnapshots ++
            .machineFresh snapshotSeen actor state input answer avoids ::
              laterSnapshots))
        (requestCursor : UnifiedExposureCursor.{u} globalOracleCalls),
      CertifiedOperationalTracePrefixCursor snapshotTrace priorSnapshots
          requestCursor ∧
        IsExactMachineFreshRequest actor state input
          (seekUnifiedExposure transitionFuel requestCursor) ∧
        priorSnapshots.map CertifiedOperationalExposure.erase = priorRecords ∧
        laterSnapshots.map CertifiedOperationalExposure.erase = laterRecords := by
  exact atPrefix

/-- Full-history consequence needed by programming provenance: a clean fresh
machine answer cannot be the literal state prefix of any query already in the
actual cumulative pre-query history. -/
theorem machine_answer_avoids_every_history_literal_prefix
    (seen : Finset Digest256) (state : OracleState) (input : ShaInput)
    (answer : Digest256)
    (avoids : answer ∉ operationalRequestTargets seen state.history input)
    (record : QueryRecord) (member : record ∈ state.history) :
    ¬ HasLiteralStatePrefix answer record.input := by
  intro prefixProof
  exact avoids ((operational_request_target_hit_iff_mem seen state.history
    input answer).mp (.priorLiteralPrefix record member prefixProof))

theorem certified_machine_exposure_at_prefix_avoids_history_literal_prefix
    {globalOracleCalls transitionFuel step remaining : Nat}
    {seen : Finset Digest256} {seenBound : seen.card ≤ step}
    {cursor : UnifiedExposureCursor.{u} globalOracleCalls}
    {tape : FreshAnswerTape Digest256 remaining}
    {certificate : UnifiedOperationalTargetCleanCertificate transitionFuel
      step remaining seen seenBound cursor tape}
    {priorRecords laterRecords : List UnifiedExposureRecord}
    {actor : QueryActor} {state : OracleState} {input : ShaInput}
    {answer : Digest256}
    (atPrefix : CertifiedMachineExposureAtPrefix certificate priorRecords
      laterRecords actor state input answer)
    (record : QueryRecord) (member : record ∈ state.history) :
    ¬ HasLiteralStatePrefix answer record.input := by
  rcases atPrefix with ⟨snapshotSeen, avoids, _priorSnapshots, _laterSnapshots,
    _snapshotTrace, _requestCursor, _reached, _exactRequest, _priorExact,
      _laterExact⟩
  exact machine_answer_avoids_every_history_literal_prefix snapshotSeen state
    input answer avoids record member

theorem unified_target_clean_constructs_operational_certificate
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256) (seenBound : seen.card ≤ step)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel step
        remaining seen seenBound cursor).everHits
          (operationalIndexedTape globalOracleCalls step remaining tape)) :
    UnifiedOperationalTargetCleanCertificate transitionFuel step remaining
      seen seenBound cursor tape := by
  induction remaining generalizing step seen cursor with
  | zero =>
      cases tape
      exact .done step seen seenBound cursor
  | succ remaining ih =>
      change Digest256 × FreshAnswerTape Digest256 remaining at tape
      cases request : seekUnifiedExposure transitionFuel cursor with
      | halted =>
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : UnifiedExposureCursor globalOracleCalls)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          exact .halted step remaining seen seenBound cursor tape request
            (ih (step + 1) seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
              tailClean)
      | transitionLimit =>
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : UnifiedExposureCursor globalOracleCalls)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          exact .transitionLimit step remaining seen seenBound cursor tape
            request
            (ih (step + 1) seen
              (seenBound.trans (Nat.le_add_right step 1))
              (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
              tailClean)
      | machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          have answerAvoidsTargets :
              tape.1 ∉ operationalRequestTargets seen state.history input := by
            intro member
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl member
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          let nextCursor : UnifiedExposureCursor globalOracleCalls :=
            .machine limits limitBound actor
              (freshQueryState actor state input tape.1)
              (nextProgram tape.1) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input tape.1 coherent) onReturned
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                nextCursor).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          exact .machineFresh step remaining seen seenBound cursor tape limits
            limitBound actor state input nextProgram remainingFuel coherent
            totalRoom freshRoom missing onReturned request answerAvoidsTargets
            (ih (step + 1) (insert tape.1 seen) insertedBound nextCursor tape.2
              tailClean)
      | forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          have answerAvoidsTargets :
              tape.1 ∉ operationalForkTargets seen frozenHistory outputInput
                advanceInput := by
            intro member
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl member
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          let nextCursor : UnifiedExposureCursor globalOracleCalls :=
            .forkAdvance frozenHistory pairRoom outputInput advanceInput
              template tape.1 next
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                nextCursor).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          exact .forkOutput step remaining seen seenBound cursor tape
            frozenHistory pairRoom outputInput advanceInput template next
            request answerAvoidsTargets
            (ih (step + 1) (insert tape.1 seen) insertedBound nextCursor tape.2
              tailClean)
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          have answerAvoidsTargets :
              tape.1 ∉ operationalForkTargets seen frozenHistory outputInput
                advanceInput := by
            intro member
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl member
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                (next (scheduledForkConfiguration template forkOutput
                  tape.1))).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          exact .forkAdvance step remaining seen seenBound cursor tape
            frozenHistory pairRoom outputInput advanceInput template forkOutput
            next request answerAvoidsTargets
            (ih (step + 1) (insert tape.1 seen) insertedBound
              (next (scheduledForkConfiguration template forkOutput tape.1))
              tape.2 tailClean)

theorem chronologically_clean_nonpadding_answers_avoid_initial_seen :
    ∀ (seen : Finset Digest256) (records : List UnifiedExposureRecord),
      EveryNonpaddingExposureChronologicallyClean seen records →
        ∀ answer ∈ nonpaddingExposureAnswers records, answer ∉ seen := by
  intro seen records clean
  induction records generalizing seen with
  | nil =>
      simp [nonpaddingExposureAnswers]
  | cons record rest ih =>
      cases record with
      | padding paddingAnswer =>
          exact ih seen clean.2
      | machineFresh actor input headAnswer =>
          intro answer member answerSeen
          simp only [nonpaddingExposureAnswers, List.mem_cons] at member
          rcases member with rfl | member
          · exact clean.1.1 answerSeen
          · have avoidsInserted := ih (insert headAnswer seen) clean.2
                answer member
            exact avoidsInserted (Finset.mem_insert_of_mem answerSeen)
      | forkOutput frozenHistory outputInput advanceInput template headAnswer =>
          intro answer member answerSeen
          simp only [nonpaddingExposureAnswers, List.mem_cons] at member
          rcases member with rfl | member
          · exact clean.1.1 answerSeen
          · have avoidsInserted := ih (insert headAnswer seen) clean.2
                answer member
            exact avoidsInserted (Finset.mem_insert_of_mem answerSeen)
      | forkAdvance scheduled =>
          intro answer member answerSeen
          simp only [nonpaddingExposureAnswers, List.mem_cons] at member
          rcases member with rfl | member
          · exact clean.1.1 answerSeen
          · have avoidsInserted := ih
                (insert scheduled.forkAdvance seen) clean.2 answer member
            exact avoidsInserted (Finset.mem_insert_of_mem answerSeen)

/-- Global pairwise distinctness of all actual sampled coordinates.  Padding
is excluded because it is deliberately not an exposure. -/
theorem chronologically_clean_nonpadding_answers_nodup :
    ∀ (seen : Finset Digest256) (records : List UnifiedExposureRecord),
      EveryNonpaddingExposureChronologicallyClean seen records →
        (nonpaddingExposureAnswers records).Nodup := by
  intro seen records clean
  induction records generalizing seen with
  | nil =>
      exact List.nodup_nil
  | cons record rest ih =>
      cases record with
      | padding paddingAnswer =>
          exact ih seen clean.2
      | machineFresh actor input headAnswer =>
          apply List.nodup_cons.mpr
          constructor
          · intro member
            have avoidsInserted :=
              chronologically_clean_nonpadding_answers_avoid_initial_seen
                (insert headAnswer seen) rest clean.2 headAnswer member
            exact avoidsInserted (Finset.mem_insert_self headAnswer seen)
          · exact ih (insert headAnswer seen) clean.2
      | forkOutput frozenHistory outputInput advanceInput template headAnswer =>
          apply List.nodup_cons.mpr
          constructor
          · intro member
            have avoidsInserted :=
              chronologically_clean_nonpadding_answers_avoid_initial_seen
                (insert headAnswer seen) rest clean.2 headAnswer member
            exact avoidsInserted (Finset.mem_insert_self headAnswer seen)
          · exact ih (insert headAnswer seen) clean.2
      | forkAdvance scheduled =>
          apply List.nodup_cons.mpr
          constructor
          · intro member
            have avoidsInserted :=
              chronologically_clean_nonpadding_answers_avoid_initial_seen
                (insert scheduled.forkAdvance seen) rest clean.2
                scheduled.forkAdvance member
            exact avoidsInserted
              (Finset.mem_insert_self scheduled.forkAdvance seen)
          · exact ih (insert scheduled.forkAdvance seen) clean.2

/-- The actual trace interpreter and target tree consume the same adaptive
requests and the same coordinates.  Consequently global tree cleanliness
gives local `DirectForkCoordinatesClean` for every complete adjacent pair in
the emitted trace, at the exact accumulated `seen` set.

This is a deterministic whole-trace decomposition theorem.  It is stronger
than applying `unified_tree_clean_direct_fork_pair` to a caller-chosen local
tree, because every recursive tail here is forced by the actual scheduler. -/
theorem unified_target_clean_implies_every_emitted_direct_fork_pair_clean
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256) (seenBound : seen.card ≤ step)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel step
        remaining seen seenBound cursor).everHits
          (operationalIndexedTape globalOracleCalls step remaining tape)) :
    EveryAdjacentDirectForkPairClean seen
      (runUnifiedExposureTrace transitionFuel remaining cursor tape) := by
  induction remaining generalizing step seen cursor with
  | zero =>
      cases tape
      simp [runUnifiedExposureTrace, EveryAdjacentDirectForkPairClean]
  | succ remaining ih =>
      change Digest256 × FreshAnswerTape Digest256 remaining at tape
      cases request : seekUnifiedExposure transitionFuel cursor with
      | halted =>
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : UnifiedExposureCursor globalOracleCalls)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) seen
            (seenBound.trans (Nat.le_add_right step 1))
            (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
            tailClean
          simpa [runUnifiedExposureTrace, request,
            EveryAdjacentDirectForkPairClean, extendUnifiedExposureSeen]
            using tail
      | transitionLimit =>
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : UnifiedExposureCursor globalOracleCalls)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) seen
            (seenBound.trans (Nat.le_add_right step 1))
            (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
            tailClean
          simpa [runUnifiedExposureTrace, request,
            EveryAdjacentDirectForkPairClean, extendUnifiedExposureSeen]
            using tail
      | machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          let nextCursor : UnifiedExposureCursor globalOracleCalls :=
            .machine limits limitBound actor
              (freshQueryState actor state input tape.1)
              (nextProgram tape.1) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input tape.1 coherent) onReturned
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                nextCursor).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) (insert tape.1 seen) insertedBound
            nextCursor tape.2 tailClean
          simpa [runUnifiedExposureTrace, request, nextCursor,
            EveryAdjacentDirectForkPairClean, extendUnifiedExposureSeen,
            UnifiedExposureRecord.answer] using tail
      | forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          cases remaining with
          | zero =>
              simp [runUnifiedExposureTrace, request,
                EveryAdjacentDirectForkPairClean]
          | succ tailRemaining =>
              cases transitionFuel with
              | zero =>
                  simp [seekUnifiedExposure] at request
              | succ transitionFuel =>
                  let scheduled : ScheduledForkCoins :=
                    { frozenHistory := frozenHistory
                      outputInput := outputInput
                      advanceInput := advanceInput
                      template := template
                      forkOutput := tape.1
                      forkAdvance := tape.2.1 }
                  have directClean : DirectForkCoordinatesClean seen
                      frozenHistory outputInput advanceInput tape.1 tape.2.1 := by
                    constructor
                    · intro member
                      apply clean
                      simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
                      rw [causal_target_tree_step_everHits_iff]
                      exact Or.inl member
                    · intro member
                      apply clean
                      simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
                      rw [causal_target_tree_step_everHits_iff]
                      exact Or.inr (Or.inl member)
                  have outputSeenBound : (insert tape.1 seen).card ≤ step + 1 :=
                    (Finset.card_insert_le tape.1 seen).trans
                      (Nat.add_le_add_right seenBound 1)
                  let advanceCursor : UnifiedExposureCursor globalOracleCalls :=
                    .forkAdvance frozenHistory pairRoom outputInput advanceInput
                      template tape.1 next
                  have tailClean : ¬
                      (unifiedExposureTargetTreeFrom globalOracleCalls
                        (transitionFuel + 1) (step + 1)
                        (tailRemaining + 1) (insert tape.1 seen) outputSeenBound
                        advanceCursor).everHits
                          (operationalIndexedTape globalOracleCalls (step + 1)
                            (tailRemaining + 1) tape.2) := by
                    intro hit
                    apply clean
                    simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
                    rw [causal_target_tree_step_everHits_iff]
                    exact Or.inr hit
                  have tailPairs := ih (step + 1) (insert tape.1 seen)
                    outputSeenBound advanceCursor tape.2 tailClean
                  simp only [runUnifiedExposureTrace, request,
                    seek_unified_exposure_fork_advance]
                  change
                    AdjacentForkRecordsExact frozenHistory outputInput
                        advanceInput template tape.1 scheduled ∧
                      DirectForkCoordinatesClean seen frozenHistory outputInput
                        advanceInput tape.1 scheduled.forkAdvance ∧
                      EveryAdjacentDirectForkPairClean
                        (insert scheduled.forkAdvance (insert tape.1 seen))
                        (runUnifiedExposureTrace (transitionFuel + 1)
                          tailRemaining
                          (next scheduled.configuration) tape.2.2)
                  refine ⟨?_, ?_, ?_⟩
                  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
                  · exact directClean
                  · simpa [advanceCursor, scheduled,
                      EveryAdjacentDirectForkPairClean,
                      extendUnifiedExposureSeen,
                      runUnifiedExposureTrace,
                      UnifiedExposureRecord.answer] using tailPairs
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := tape.1 }
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                (next scheduled.configuration)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) (insert tape.1 seen) insertedBound
            (next scheduled.configuration) tape.2 tailClean
          simpa [runUnifiedExposureTrace, request, scheduled,
            EveryAdjacentDirectForkPairClean, extendUnifiedExposureSeen,
            UnifiedExposureRecord.answer] using tail

/-- Whole-trace chronological projection.  In addition to the atomic pair
association above, target cleanliness forces every non-padding coordinate to
be new relative to all prior coordinates and to avoid the literal state
prefix of the input(s) visible before it was sampled. -/
theorem unified_target_clean_implies_every_nonpadding_exposure_clean
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256) (seenBound : seen.card ≤ step)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256 remaining)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel step
        remaining seen seenBound cursor).everHits
          (operationalIndexedTape globalOracleCalls step remaining tape)) :
    EveryNonpaddingExposureChronologicallyClean seen
      (runUnifiedExposureTrace transitionFuel remaining cursor tape) := by
  induction remaining generalizing step seen cursor with
  | zero =>
      cases tape
      simp [runUnifiedExposureTrace,
        EveryNonpaddingExposureChronologicallyClean]
  | succ remaining ih =>
      change Digest256 × FreshAnswerTape Digest256 remaining at tape
      cases request : seekUnifiedExposure transitionFuel cursor with
      | halted =>
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : UnifiedExposureCursor globalOracleCalls)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) seen
            (seenBound.trans (Nat.le_add_right step 1))
            (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
            tailClean
          simpa [runUnifiedExposureTrace, request,
            EveryNonpaddingExposureChronologicallyClean,
            ExposureCoordinateChronologicallyClean,
            extendUnifiedExposureSeen] using tail
      | transitionLimit =>
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining seen
                (seenBound.trans (Nat.le_add_right step 1))
                (.halted : UnifiedExposureCursor globalOracleCalls)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) seen
            (seenBound.trans (Nat.le_add_right step 1))
            (.halted : UnifiedExposureCursor globalOracleCalls) tape.2
            tailClean
          simpa [runUnifiedExposureTrace, request,
            EveryNonpaddingExposureChronologicallyClean,
            ExposureCoordinateChronologicallyClean,
            extendUnifiedExposureSeen] using tail
      | machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          have answerAvoidsSeen : tape.1 ∉ seen := by
            intro member
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                ((operational_request_target_hit_iff_mem seen state.history
                  input tape.1).mp (.priorFullOutput member))
          have answerAvoidsInput : ¬ HasLiteralStatePrefix tape.1 input := by
            intro prefixProof
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                ((operational_request_target_hit_iff_mem seen state.history
                  input tape.1).mp (.currentLiteralPrefix prefixProof))
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          let nextCursor : UnifiedExposureCursor globalOracleCalls :=
            .machine limits limitBound actor
              (freshQueryState actor state input tape.1)
              (nextProgram tape.1) remainingFuel
              (fresh_query_state_preserves_history_total_coherent actor state
                input tape.1 coherent) onReturned
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                nextCursor).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) (insert tape.1 seen) insertedBound
            nextCursor tape.2 tailClean
          simpa [runUnifiedExposureTrace, request, nextCursor,
            EveryNonpaddingExposureChronologicallyClean,
            ExposureCoordinateChronologicallyClean,
            extendUnifiedExposureSeen, UnifiedExposureRecord.answer] using
              ⟨⟨answerAvoidsSeen, answerAvoidsInput⟩, tail⟩
      | forkOutput frozenHistory pairRoom outputInput advanceInput template
          next =>
          have answerAvoidsSeen : tape.1 ∉ seen := by
            intro member
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                (seen_member_is_fork_target seen frozenHistory outputInput
                  advanceInput tape.1 member)
          have answerAvoidsOutput :
              ¬ HasLiteralStatePrefix tape.1 outputInput := by
            intro prefixProof
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                (output_input_literal_prefix_is_fork_target seen frozenHistory
                  outputInput advanceInput tape.1 prefixProof)
          have answerAvoidsAdvance :
              ¬ HasLiteralStatePrefix tape.1 advanceInput := by
            intro prefixProof
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                (advance_input_literal_prefix_is_fork_target seen frozenHistory
                  outputInput advanceInput tape.1 prefixProof)
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          let nextCursor : UnifiedExposureCursor globalOracleCalls :=
            .forkAdvance frozenHistory pairRoom outputInput advanceInput
              template tape.1 next
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                nextCursor).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) (insert tape.1 seen) insertedBound
            nextCursor tape.2 tailClean
          simpa [runUnifiedExposureTrace, request, nextCursor,
            EveryNonpaddingExposureChronologicallyClean,
            ExposureCoordinateChronologicallyClean,
            extendUnifiedExposureSeen, UnifiedExposureRecord.answer] using
              ⟨⟨answerAvoidsSeen, answerAvoidsOutput,
                answerAvoidsAdvance⟩, tail⟩
      | forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next =>
          let scheduled : ScheduledForkCoins :=
            { frozenHistory := frozenHistory
              outputInput := outputInput
              advanceInput := advanceInput
              template := template
              forkOutput := forkOutput
              forkAdvance := tape.1 }
          have answerAvoidsSeen : tape.1 ∉ seen := by
            intro member
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                (seen_member_is_fork_target seen frozenHistory outputInput
                  advanceInput tape.1 member)
          have answerAvoidsOutput :
              ¬ HasLiteralStatePrefix tape.1 outputInput := by
            intro prefixProof
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                (output_input_literal_prefix_is_fork_target seen frozenHistory
                  outputInput advanceInput tape.1 prefixProof)
          have answerAvoidsAdvance :
              ¬ HasLiteralStatePrefix tape.1 advanceInput := by
            intro prefixProof
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inl
                (advance_input_literal_prefix_is_fork_target seen frozenHistory
                  outputInput advanceInput tape.1 prefixProof)
          have insertedBound : (insert tape.1 seen).card ≤ step + 1 :=
            (Finset.card_insert_le tape.1 seen).trans
              (Nat.add_le_add_right seenBound 1)
          have tailClean : ¬
              (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel
                (step + 1) remaining (insert tape.1 seen) insertedBound
                (next scheduled.configuration)).everHits
                  (operationalIndexedTape globalOracleCalls (step + 1)
                    remaining tape.2) := by
            intro hit
            apply clean
            simp only [operationalCapsFrom, unifiedExposureTargetTreeFrom, request,
              operationalIndexedTape]
            rw [causal_target_tree_step_everHits_iff]
            exact Or.inr hit
          have tail := ih (step + 1) (insert tape.1 seen) insertedBound
            (next scheduled.configuration) tape.2 tailClean
          simpa [runUnifiedExposureTrace, request, scheduled,
            EveryNonpaddingExposureChronologicallyClean,
            ExposureCoordinateChronologicallyClean,
            extendUnifiedExposureSeen, UnifiedExposureRecord.answer] using
              ⟨⟨answerAvoidsSeen, answerAvoidsOutput,
                answerAvoidsAdvance⟩, tail⟩

/-- Indexed-tape form of the whole-trace theorem.  This is the form consumed
directly by the exact compiler target tree; the trace tape is not supplied by
the caller but is the definitional coordinate projection of the same indexed
tape. -/
theorem unified_indexed_target_clean_implies_every_emitted_direct_fork_pair_clean
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256) (seenBound : seen.card ≤ step)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256
      (operationalCapsFrom step remaining globalOracleCalls).length)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel step
        remaining seen seenBound cursor).everHits tape) :
    EveryAdjacentDirectForkPairClean seen
      (runUnifiedExposureTrace transitionFuel remaining cursor
        (operationalTapeCoordinates globalOracleCalls step remaining tape)) := by
  apply unified_target_clean_implies_every_emitted_direct_fork_pair_clean
    transitionFuel step remaining seen seenBound cursor
  simpa [operational_indexed_tape_coordinates_roundtrip] using clean

theorem unified_indexed_target_clean_implies_every_nonpadding_exposure_clean
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256) (seenBound : seen.card ≤ step)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256
      (operationalCapsFrom step remaining globalOracleCalls).length)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel step
        remaining seen seenBound cursor).everHits tape) :
    EveryNonpaddingExposureChronologicallyClean seen
      (runUnifiedExposureTrace transitionFuel remaining cursor
        (operationalTapeCoordinates globalOracleCalls step remaining tape)) := by
  apply unified_target_clean_implies_every_nonpadding_exposure_clean
    transitionFuel step remaining seen seenBound cursor
  simpa [operational_indexed_tape_coordinates_roundtrip] using clean

theorem unified_indexed_target_clean_constructs_operational_certificate
    {globalOracleCalls : Nat}
    (transitionFuel step remaining : Nat)
    (seen : Finset Digest256) (seenBound : seen.card ≤ step)
    (cursor : UnifiedExposureCursor.{u} globalOracleCalls)
    (tape : FreshAnswerTape Digest256
      (operationalCapsFrom step remaining globalOracleCalls).length)
    (clean : ¬
      (unifiedExposureTargetTreeFrom globalOracleCalls transitionFuel step
        remaining seen seenBound cursor).everHits tape) :
    UnifiedOperationalTargetCleanCertificate transitionFuel step remaining
      seen seenBound cursor
        (operationalTapeCoordinates globalOracleCalls step remaining tape) := by
  apply unified_target_clean_constructs_operational_certificate
    transitionFuel step remaining seen seenBound cursor
  simpa [operational_indexed_tape_coordinates_roundtrip] using clean

/-- Reindex the exact compiler master tape by the definitionally equal
`operationalCapsFrom 0 F G` list used inside its target tree. -/
noncomputable def exactCompilerOperationalIndexedTape
    (parameters : ExactCompilerResourceParameters)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      (operationalCapsFrom 1 (unifiedFull256ExposureCap parameters)
        (globalFull256OracleCallCap parameters)).length := by
  exact masterTape

/-- The literal fixed-length trace generated from the exact compiler's own
master tape. -/
noncomputable def exactCompilerUnifiedExposureTrace
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    List UnifiedExposureRecord :=
  runUnifiedExposureTrace transitionFuel
    (unifiedFull256ExposureCap parameters) cursor.erase
    (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters masterTape))

noncomputable def exactCompilerMasterCoordinates
    (parameters : ExactCompilerResourceParameters)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) : List Digest256 :=
  freshAnswerTapeToList
    (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters masterTape))

/-- The reindexed target-analysis trace is the literal record trace of the
actual result-carrying plain-ROM scheduler run.  This closes the root
dispatcher/native trace-alignment step; no equality of answer lists is used
as a substitute for record-level execution equality. -/
theorem exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    exactCompilerUnifiedExposureTrace parameters transitionFuel
        (exactPlainRomCursor configuration sample.1) sample.2 =
      (runExactPlainRom transitionFuel configuration sample).trace := by
  calc
    exactCompilerUnifiedExposureTrace parameters transitionFuel
        (exactPlainRomCursor configuration sample.1) sample.2 =
      runUnifiedExposureTrace transitionFuel
        (unifiedFull256ExposureCap parameters)
        (exactPlainRomCursor configuration sample.1).erase
        (operationalTapeCoordinates
          (globalFull256OracleCallCap parameters) 1
          (unifiedFull256ExposureCap parameters)
          (exactCompilerOperationalIndexedTape parameters sample.2)) := rfl
    _ = runUnifiedExposureTrace transitionFuel
        (operationalCapsFrom 1 (unifiedFull256ExposureCap parameters)
          (globalFull256OracleCallCap parameters)).length
        (exactPlainRomCursor configuration sample.1).erase
        (exactCompilerOperationalIndexedTape parameters sample.2) := by
      have indexed :=
        (run_unified_exposure_trace_operational_indexed_tape
          transitionFuel 1 (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2))).symm
      simpa only [operational_indexed_tape_coordinates_roundtrip] using indexed
    _ = runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exactPlainRomCursor configuration sample.1).erase sample.2 := by
      rfl
    _ = (runExactPlainRom transitionFuel configuration sample).trace := by
      exact (exact_plain_rom_trace_is_erased_exposure_trace
        transitionFuel configuration sample).symm

theorem exact_compiler_master_coordinates_are_literal_master_tape
    (parameters : ExactCompilerResourceParameters)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    exactCompilerMasterCoordinates parameters masterTape =
      freshAnswerTapeToList masterTape := by
  unfold exactCompilerMasterCoordinates
  calc
    freshAnswerTapeToList
        (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
          (unifiedFull256ExposureCap parameters)
          (exactCompilerOperationalIndexedTape parameters masterTape)) =
      freshAnswerTapeToList
        (operationalIndexedTape (globalFull256OracleCallCap parameters) 1
          (unifiedFull256ExposureCap parameters)
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters masterTape))) := by
      exact (operational_indexed_tape_preserves_coordinate_list
        (globalFull256OracleCallCap parameters) 1
        (unifiedFull256ExposureCap parameters)
        (operationalTapeCoordinates
          (globalFull256OracleCallCap parameters) 1
          (unifiedFull256ExposureCap parameters)
          (exactCompilerOperationalIndexedTape parameters masterTape))).symm
    _ = freshAnswerTapeToList
        (exactCompilerOperationalIndexedTape parameters masterTape) := by
      rw [operational_indexed_tape_coordinates_roundtrip]
    _ = freshAnswerTapeToList masterTape := by
      rfl

theorem exact_compiler_unified_exposure_trace_answers_are_master_coordinates
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape).map UnifiedExposureRecord.answer =
      exactCompilerMasterCoordinates parameters masterTape := by
  exact run_unified_exposure_trace_answers_are_exact_tape transitionFuel
    (unifiedFull256ExposureCap parameters) cursor.erase
    (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters masterTape))

/-- Root corollary: literal global `ExactCompilerTargetClean` implies direct
fork-coordinate cleanliness for every adjacent pair emitted by that same
exact master tape. -/
theorem exact_compiler_target_clean_implies_every_emitted_direct_fork_pair_clean
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    EveryAdjacentDirectForkPairClean {zeroDigest256}
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) := by
  apply
    unified_indexed_target_clean_implies_every_emitted_direct_fork_pair_clean
      transitionFuel 1 (unifiedFull256ExposureCap parameters)
      {zeroDigest256} (by simp)
      cursor.erase (exactCompilerOperationalIndexedTape parameters masterTape)
  change ExactCompilerTargetClean parameters transitionFuel cursor masterTape
  exact clean

theorem exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    EveryNonpaddingExposureChronologicallyClean {zeroDigest256}
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape) := by
  apply unified_indexed_target_clean_implies_every_nonpadding_exposure_clean
    transitionFuel 1 (unifiedFull256ExposureCap parameters)
      {zeroDigest256} (by simp)
      cursor.erase (exactCompilerOperationalIndexedTape parameters masterTape)
  change ExactCompilerTargetClean parameters transitionFuel cursor masterTape
  exact clean

theorem exact_compiler_target_clean_constructs_operational_certificate
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    UnifiedOperationalTargetCleanCertificate transitionFuel 1
      (unifiedFull256ExposureCap parameters) {zeroDigest256} (by simp)
      cursor.erase
      (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
        (unifiedFull256ExposureCap parameters)
        (exactCompilerOperationalIndexedTape parameters masterTape)) := by
  apply unified_indexed_target_clean_constructs_operational_certificate
    transitionFuel 1 (unifiedFull256ExposureCap parameters)
      {zeroDigest256} (by simp) cursor.erase
      (exactCompilerOperationalIndexedTape parameters masterTape)
  change ExactCompilerTargetClean parameters transitionFuel cursor masterTape
  exact clean

/-- Literal event-complement form of target cleanliness for the actual hidden
tape selected cursor. -/
theorem exact_plain_rom_outside_target_is_exact_compiler_clean
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (outside : sample ∉
      exactPlainRomTargetEvent transitionFuel configuration) :
    ExactCompilerTargetClean parameters transitionFuel
      (exactPlainRomCursor configuration sample.1) sample.2 := by
  simpa [ExactCompilerTargetClean, exactPlainRomTargetEvent,
    exactCompilerTargetEvent, hiddenDependentCausalHitEvent,
    exactPlainRomExposureCursor] using outside

/-- Direct experiment-facing form: being outside the literal
`exactPlainRomTargetEvent` constructs the dependent operational certificate
for the very scheduler cursor selected by that sample's hidden tape.  No
separate clean cursor or trace-alignment premise is supplied. -/
theorem exact_plain_rom_outside_target_constructs_operational_certificate
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (outside : sample ∉
      exactPlainRomTargetEvent transitionFuel configuration) :
    UnifiedOperationalTargetCleanCertificate transitionFuel 1
      (unifiedFull256ExposureCap parameters) {zeroDigest256} (by simp)
      (exactPlainRomCursor configuration sample.1).erase
      (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
        (unifiedFull256ExposureCap parameters)
        (exactCompilerOperationalIndexedTape parameters sample.2)) := by
  apply exact_compiler_target_clean_constructs_operational_certificate
    parameters transitionFuel (exactPlainRomCursor configuration sample.1)
      sample.2
  exact exact_plain_rom_outside_target_is_exact_compiler_clean transitionFuel
    configuration sample outside

/-- The actual scheduler trace, not merely its reindexed analysis copy, is
chronologically clean outside the exact target event. -/
theorem exact_plain_rom_outside_target_actual_trace_chronologically_clean
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (outside : sample ∉
      exactPlainRomTargetEvent transitionFuel configuration) :
    EveryNonpaddingExposureChronologicallyClean {zeroDigest256}
      (runExactPlainRom transitionFuel configuration sample).trace := by
  rw [← exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
    transitionFuel configuration sample]
  exact exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
    parameters transitionFuel (exactPlainRomCursor configuration sample.1)
      sample.2
      (exact_plain_rom_outside_target_is_exact_compiler_clean transitionFuel
        configuration sample outside)

/-- Every adjacent output/advance fork pair in the literal actual scheduler
trace has the exact shared frozen state and avoids its pre-pair target set. -/
theorem exact_plain_rom_outside_target_actual_trace_direct_fork_pairs_clean
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (outside : sample ∉
      exactPlainRomTargetEvent transitionFuel configuration) :
    EveryAdjacentDirectForkPairClean {zeroDigest256}
      (runExactPlainRom transitionFuel configuration sample).trace := by
  rw [← exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
    transitionFuel configuration sample]
  exact
    exact_compiler_target_clean_implies_every_emitted_direct_fork_pair_clean
      parameters transitionFuel (exactPlainRomCursor configuration sample.1)
        sample.2
        (exact_plain_rom_outside_target_is_exact_compiler_clean transitionFuel
          configuration sample outside)

theorem exact_compiler_target_clean_nonpadding_answers_nodup
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    (nonpaddingExposureAnswers
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape)).Nodup := by
  exact chronologically_clean_nonpadding_answers_nodup {zeroDigest256} _
    (exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
      parameters transitionFuel cursor masterTape clean)

theorem exact_compiler_target_clean_nonpadding_answers_avoid_dummy_digest
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    ∀ answer ∈ nonpaddingExposureAnswers
        (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
          masterTape),
      answer ≠ zeroDigest256 := by
  intro answer member equal
  have avoidsSeed :=
    chronologically_clean_nonpadding_answers_avoid_initial_seen
      {zeroDigest256}
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape)
      (exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
        parameters transitionFuel cursor masterTape clean)
      answer member
  apply avoidsSeed
  simp [equal]

/-- One reusable deterministic package for downstream programming-freshness
composition.  It contains only consequences of the literal seeded target-tree
cleanliness of the exact root tape; no acceptance, restoration, or extraction
claim is stored in the structure. -/
structure ExactCompilerWholeTraceCleanFacts
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) : Prop where
  operationalCertificate :
    UnifiedOperationalTargetCleanCertificate transitionFuel 1
      (unifiedFull256ExposureCap parameters) {zeroDigest256} (by simp)
      cursor.erase
      (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
        (unifiedFull256ExposureCap parameters)
        (exactCompilerOperationalIndexedTape parameters masterTape))
  answersAreExactMasterCoordinates :
    (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape).map UnifiedExposureRecord.answer =
      exactCompilerMasterCoordinates parameters masterTape
  answersAreLiteralMasterTape :
    (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape).map UnifiedExposureRecord.answer =
      freshAnswerTapeToList masterTape
  everyDirectForkPair :
    EveryAdjacentDirectForkPairClean {zeroDigest256}
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape)
  everyCoordinate :
    EveryNonpaddingExposureChronologicallyClean {zeroDigest256}
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape)
  nonpaddingAnswersNodup :
    (nonpaddingExposureAnswers
      (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
        masterTape)).Nodup
  nonpaddingAnswersAvoidDummy :
    ∀ answer ∈ nonpaddingExposureAnswers
        (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
          masterTape),
      answer ≠ zeroDigest256

theorem exact_compiler_target_clean_has_whole_trace_facts
    {Result : Type*}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters) Result)
    (masterTape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (clean : ExactCompilerTargetClean parameters transitionFuel cursor
      masterTape) :
    ExactCompilerWholeTraceCleanFacts parameters transitionFuel cursor
      masterTape := by
  exact
    { operationalCertificate :=
        exact_compiler_target_clean_constructs_operational_certificate
          parameters transitionFuel cursor masterTape clean
      answersAreExactMasterCoordinates :=
        exact_compiler_unified_exposure_trace_answers_are_master_coordinates
          parameters transitionFuel cursor masterTape
      everyDirectForkPair :=
        exact_compiler_target_clean_implies_every_emitted_direct_fork_pair_clean
          parameters transitionFuel cursor masterTape clean
      answersAreLiteralMasterTape := by
        calc
          (exactCompilerUnifiedExposureTrace parameters transitionFuel cursor
              masterTape).map UnifiedExposureRecord.answer =
              exactCompilerMasterCoordinates parameters masterTape :=
            exact_compiler_unified_exposure_trace_answers_are_master_coordinates
              parameters transitionFuel cursor masterTape
          _ = freshAnswerTapeToList masterTape :=
            exact_compiler_master_coordinates_are_literal_master_tape
              parameters masterTape
      everyCoordinate :=
        exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
          parameters transitionFuel cursor masterTape clean
      nonpaddingAnswersNodup :=
        exact_compiler_target_clean_nonpadding_answers_nodup parameters
          transitionFuel cursor masterTape clean
      nonpaddingAnswersAvoidDummy :=
        exact_compiler_target_clean_nonpadding_answers_avoid_dummy_digest
          parameters transitionFuel cursor masterTape clean }

/-!
The next positive lemma must be proved from the actual completed scheduler
lineage, rather than added as an interface premise.  Its exact conclusion is

```
lookupEntry prepared.programmingBase prepared.outputInput = none ∧
lookupEntry prepared.programmingBase prepared.advanceInput = none
```

for every actual `.ready prepared` selected by a request satisfying
`AvoidsInheritedChildTransition`, outside `exactPlainRomTargetEvent`.
`PreparedSelectionIsExact` already ties `prepared` to the stored node and
transition; `no_pair_segment_lookup_conflict_is_in_entry_table` reduces a
node-local conflict to the immutable entry table.  What remains is a
chronological projection showing that, for a positive child transition, its
checkpoint digest is a later master-tape output while every inherited query
or programming input predates it.  The literal `S || 0x01`/`S || 0x02`
conflict then hits the existing causal target at the coordinate producing
`S`.  Transition zero is excluded because it gives a real deterministic
counterexample: `S` was restored from the parent and its pair is already
programmed at child entry.
-/

/-! ## Named final bad-event classes -/

open AspisK1.V7Tag73PausedRecursiveReplay
open AspisK1.V7Tag73NoPairReplay

/-- Exact same-start replay witness when neither half of a squeeze pair occurs
in the frozen first-run Q1.  The prover program is definitionally the original
same-hidden-tape capability; only two fresh table points are programmed. -/
def OperationalNoPairSameStartReplay
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (result : Result) (outputInput advanceInput : ShaInput)
    (outputValue advanceValue : ShaOutput) : Prop :=
  ∃ pairs : List (ShaInput × ShaOutput),
    let post := source.origin.firstRun.stateAtAdversaryHalt
    let outputProgramming : Programming :=
      { input := outputInput, output := outputValue }
    let advanceProgramming : Programming :=
      { input := advanceInput, output := advanceValue }
    let firstProgrammed := appendProgrammedPoint .extractorReplay post
      outputProgramming
    let bothProgrammed := appendProgrammedPoint .extractorReplay
      firstProgrammed advanceProgramming
    let limits := noPairReplayLimits post pairs.length
    let replayController := recordedPrefixController
      bothProgrammed.history.length (freezeAdversaryQ1 post)
    let replay := runMachine replayController limits .extractorReplay
      pairs.length bothProgrammed
      (source.origin.capability.start source.observation)
    MachineQueryPath (source.origin.capability.start source.observation)
        pairs result ∧
      programOracle limits .extractorReplay post outputProgramming =
        .ok firstProgrammed ∧
      programOracle limits .extractorReplay firstProgrammed
          advanceProgramming = .ok bothProgrammed ∧
      replay.halt = .returned result ∧
      queryAnswerTrace (historySince bothProgrammed replay.oracle) = pairs ∧
      (∀ record ∈ historySince bothProgrammed replay.oracle,
        record.actor = .extractorReplay ∧
          record.input ≠ outputInput ∧ record.input ≠ advanceInput) ∧
      replay.oracle.table = bothProgrammed.table ∧
      replay.oracle.programmingHistory.length =
        post.programmingHistory.length + 2 ∧
      replay.oracle.totalCalls = post.totalCalls + pairs.length ∧
      replay.oracle.freshCalls = post.freshCalls ∧
      replay.steps = pairs.length ∧
      source.origin.capability.tapeIdentity = source.tapeIdentity ∧
      source.origin.capability.start source.observation =
        source.blackBox.start source.hiddenTape source.observation ∧
      source.origin.firstRun.forgery = source.forgeryOf result

/-- A both-halves-unqueried prediction failure is an actual violation of the
same-start replay theorem under its operational freshness hypotheses. -/
def OperationalNoPairSameStartFailure
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (result : Result) (outputInput advanceInput : ShaInput)
    (outputValue advanceValue : ShaOutput) : Prop :=
  source.origin.firstExecution.halt = .returned result ∧
    outputInput ≠ advanceInput ∧
    lookupEntry source.initialOracle outputInput = none ∧
    lookupEntry source.initialOracle advanceInput = none ∧
    firstEitherInputOccurrence outputInput advanceInput
      (freezeAdversaryQ1 source.origin.firstRun.stateAtAdversaryHalt) = none ∧
    ¬ OperationalNoPairSameStartReplay source result outputInput advanceInput
      outputValue advanceValue

theorem operational_no_pair_same_start_failure_impossible
    {HiddenTape TapeIdentity Observation Statement Proof Result : Type*}
    (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
      Statement Proof Result)
    (result : Result) (outputInput advanceInput : ShaInput)
    (outputValue advanceValue : ShaOutput) :
    ¬ OperationalNoPairSameStartFailure source result outputInput advanceInput
      outputValue advanceValue := by
  rintro ⟨returned, distinct, outputMissing, advanceMissing, noPair, failed⟩
  apply failed
  exact AspisK1.V7Tag73NoPairReplay.same_tape_source_no_pair_replay source
    result returned outputInput advanceInput outputValue advanceValue distinct
      outputMissing advanceMissing noPair

/-- Sample-level name for the both-halves-absent case.  Membership requires a
real same-start counterexample, so emptiness follows from the operational
replay construction rather than from a zero coefficient declaration. -/
def exactNoPairSameStartPredictionFailureEvent
    {Sample : Type} : Set Sample :=
  {_sample | ∃
      (HiddenTape TapeIdentity Observation Statement Proof Result : Type)
      (source : SameTapeOriginSource HiddenTape TapeIdentity Observation
        Statement Proof Result)
      (result : Result) (outputInput advanceInput : ShaInput)
      (outputValue advanceValue : ShaOutput),
    OperationalNoPairSameStartFailure source result outputInput advanceInput
      outputValue advanceValue}

theorem exact_no_pair_same_start_prediction_failure_event_empty
    {Sample : Type} :
    exactNoPairSameStartPredictionFailureEvent (Sample := Sample) = ∅ := by
  ext sample
  simp only [exactNoPairSameStartPredictionFailureEvent, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨HiddenTape, TapeIdentity, Observation, Statement, Proof, Result,
    source, result, outputInput, advanceInput, outputValue, advanceValue,
    failed⟩
  exact operational_no_pair_same_start_failure_impossible source result
    outputInput advanceInput outputValue advanceValue failed

/-- Exact value-oblivious continuation property for a transcript-driving
output half absent from the prover path while the paired advance half is
observed.  The witness is an actual same-entry-program query path and replay,
not a decoded-value prediction. -/
def OperationalUnqueriedOutputIsOblivious
    {MachineResult : Type} {start : OracleMachine MachineResult}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput) : Prop :=
  ∃ pairs : List (ShaInput × ShaOutput),
    MachineQueryPath segment.entryProgram pairs segment.returnedValue ∧
      queryAnswerTrace segment.records = pairs ∧
      PathAvoidsInput pairs outputInput ∧
      PathQueriesInput pairs advanceInput ∧
      ∀ assignedOutput : ShaOutput,
        let programming : Programming :=
          { input := outputInput, output := assignedOutput }
        let programmed := appendProgrammedPoint .extractorReplay
          segment.run.oracle programming
        let limits := outputObliviousReplayLimits segment.run.oracle
          pairs.length
        programOracle limits .extractorReplay segment.run.oracle programming =
            .ok programmed ∧
          let replay := runMachine
            (recordedPrefixController segment.run.oracle.history.length
              segment.records)
            limits .extractorReplay pairs.length programmed
              segment.entryProgram
          replay.halt = .returned segment.returnedValue

/-- A coupling-relevant unqueried-output failure is defined by the actual
scan, observed advance, and missing-table facts together with failure of the
operational value-oblivious replay above. -/
def OperationalUnqueriedOutputPredictionFailure
    {MachineResult : Type} {start : OracleMachine MachineResult}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput) : Prop :=
  firstEitherInputOccurrence outputInput outputInput segment.records = none ∧
    (∃ record ∈ segment.records, record.input = advanceInput) ∧
    lookupEntry segment.run.oracle outputInput = none ∧
    ¬ OperationalUnqueriedOutputIsOblivious segment outputInput advanceInput

theorem operational_unqueried_output_prediction_failure_impossible
    {MachineResult : Type} {start : OracleMachine MachineResult}
    (segment : OperationalReturnedSegment start)
    (outputInput advanceInput : ShaInput) :
    ¬ OperationalUnqueriedOutputPredictionFailure segment outputInput
      advanceInput := by
  rintro ⟨outputScan, advanceQueried, fresh, failed⟩
  obtain ⟨pairs, path, trace, avoids, queries, everyAssigned⟩ :=
    operational_segment_scanned_unqueried_output_is_oblivious_through_advance
      segment outputInput advanceInput outputScan advanceQueried fresh
  apply failed
  refine ⟨pairs, path, trace, avoids, queries, ?_⟩
  intro assignedOutput
  have replay := everyAssigned assignedOutput
  exact ⟨replay.1, replay.2.1⟩

/-- Sample-level name for the unqueried transcript-output class.  Membership
requires a concrete operational counterexample; the preceding theorem proves
that no such counterexample exists for any sample.  Thus its absence is a
proved same-start noninterference fact, not a zero coefficient by definition. -/
def exactUnqueriedTranscriptOutputPredictionFailureEvent
    {Sample : Type} : Set Sample :=
  {_sample | ∃ (machineResult : Type) (start : OracleMachine machineResult)
      (segment : OperationalReturnedSegment start)
      (outputInput advanceInput : ShaInput),
    OperationalUnqueriedOutputPredictionFailure segment outputInput
      advanceInput}

theorem exact_unqueried_transcript_output_prediction_failure_event_empty
    {Sample : Type} :
    exactUnqueriedTranscriptOutputPredictionFailureEvent (Sample := Sample) =
      ∅ := by
  ext sample
  simp only [exactUnqueriedTranscriptOutputPredictionFailureEvent,
    Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨machineResult, start, segment, outputInput, advanceInput, failed⟩
  exact operational_unqueried_output_prediction_failure_impossible segment
    outputInput advanceInput failed

/-- The two inputs of one deployed 256-bit squeeze pair cannot alias: they
share the same state prefix but end in distinct domain bytes `0x01` and
`0x02`. -/
def exactPairedSqueezeInputCollisionEvent {Sample : Type} : Set Sample :=
  {_sample | ∃ state : Digest256,
    bytes state ++ [domSqueeze] = bytes state ++ [domAdvance]}

theorem exact_paired_squeeze_input_collision_event_empty {Sample : Type} :
    exactPairedSqueezeInputCollisionEvent (Sample := Sample) = ∅ := by
  ext sample
  simp only [exactPairedSqueezeInputCollisionEvent, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨state, collision⟩
  exact squeeze_output_and_advance_inputs_are_distinct state collision

/-- Cross-grammar input collision between any exact Tag-73 transcript SHA
query and any deployed typed-Merkle preimage.  The grammars use the same SHA
primitive, so this disjointness must be proved before splitting their logical
oracle roles. -/
def exactTranscriptTypedMerkleInputCollisionEvent
    {Sample : Type} : Set Sample :=
  {_sample | ∃ (before : Digest256) (role : RawQueryRole)
      (merkle : TypedMerklePreimage),
    role.input before = merkle.input}

theorem exact_transcript_typed_merkle_input_collision_event_empty
    {Sample : Type} :
    exactTranscriptTypedMerkleInputCollisionEvent (Sample := Sample) = ∅ := by
  ext sample
  simp only [exactTranscriptTypedMerkleInputCollisionEvent, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨before, role, merkle, collision⟩
  exact transcript_input_ne_typed_merkle_input before role merkle collision

/-- Full-256 output/state collision class on the actual scheduler trace.  It
includes equality with the public dummy digest and equality between two
nonpadding exposure answers. -/
def exactOutputOrStateCollisionEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample |
    let answers := nonpaddingExposureAnswers
      (exactCompilerUnifiedExposureTrace parameters transitionFuel
        (exactPlainRomCursor configuration sample.1) sample.2)
    ¬ answers.Nodup ∨ zeroDigest256 ∈ answers}

theorem exact_output_or_state_collision_event_subset_target
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    exactOutputOrStateCollisionEvent transitionFuel configuration ⊆
      exactPlainRomTargetEvent transitionFuel configuration := by
  intro sample collision
  by_contra outside
  have clean := exact_plain_rom_outside_target_is_exact_compiler_clean
    transitionFuel configuration sample outside
  rcases collision with duplicate | dummy
  · exact duplicate
      (exact_compiler_target_clean_nonpadding_answers_nodup parameters
        transitionFuel (exactPlainRomCursor configuration sample.1) sample.2
          clean)
  · exact
      (exact_compiler_target_clean_nonpadding_answers_avoid_dummy_digest
        parameters transitionFuel (exactPlainRomCursor configuration sample.1)
          sample.2 clean zeroDigest256 dummy rfl)

/-- Forward-reference/programming-conflict class: failure of the dependent
operational certificate that checks each actual machine or fork answer against
the full pre-coordinate history and current input grammar. -/
def exactForwardReferenceOrProgrammingConflictEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ¬ UnifiedOperationalTargetCleanCertificate transitionFuel 1
    (unifiedFull256ExposureCap parameters) {zeroDigest256} (by simp)
    (exactPlainRomCursor configuration sample.1).erase
    (operationalTapeCoordinates (globalFull256OracleCallCap parameters) 1
      (unifiedFull256ExposureCap parameters)
      (exactCompilerOperationalIndexedTape parameters sample.2))}

theorem exact_forward_reference_or_programming_conflict_event_subset_target
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters) :
    exactForwardReferenceOrProgrammingConflictEvent transitionFuel
        configuration ⊆
      exactPlainRomTargetEvent transitionFuel configuration := by
  intro sample failed
  by_contra outside
  exact failed
    (exact_plain_rom_outside_target_constructs_operational_certificate
      transitionFuel configuration sample outside)

/-- A strict source-refinement result whose exact q16 cloned forest would be
missing.  Successful `checkedRefine` makes this event impossible. -/
def exactAdaptiveQ16ForestFailureEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ runtime clientRun tape raw,
    (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun) ∧
      projection runtime.adversaryValue = some tape ∧
      checkedRefine (fixedTableOfOracleState runtime.verifierFinalOracle)
          exactDeterministicDecoders tape = some raw ∧
      ¬ ExactQ16OperationalForestExists
        (fixedTableOfOracleState runtime.verifierFinalOracle) tape}

theorem exact_adaptive_q16_forest_failure_event_empty
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload) :
    exactAdaptiveQ16ForestFailureEvent transitionFuel configuration projection =
      ∅ := by
  ext sample
  simp only [exactAdaptiveQ16ForestFailureEvent, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨runtime, clientRun, tape, raw, _completed, _projected, refined,
    failed⟩
  exact failed (successful_strict_checked_refinement_has_exact_q16_forest
    (fixedTableOfOracleState runtime.verifierFinalOracle) tape raw refined)

/-- The fixed clean root carries the exact q16 cloned-forest witness directly
from its successful strict refinement.  This is a deterministic deployed
schedule fact, not a random-oracle loss term. -/
theorem fixed_clean_root_has_exact_q16_operational_forest
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (fixed : ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample) :
    ExactQ16OperationalForestExists
      (fixedTableOfOracleState fixed.base.runtime.verifierFinalOracle)
      fixed.base.tape := by
  exact successful_strict_checked_refinement_has_exact_q16_forest
    (fixedTableOfOracleState fixed.base.runtime.verifierFinalOracle)
      fixed.base.tape fixed.base.raw fixed.base.strictRefinement

/-- Fixed clean roots preserve all literal program/release/statement/attempt
bindings and the opaque statement, while q16 has its exact first-cap-203
forest.  This packages only already-constructed operational data. -/
structure FixedCleanDeterministicClassifications
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (fixed : ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample) : Prop where
  q16 : ExactQ16OperationalForestExists
    (fixedTableOfOracleState fixed.base.runtime.verifierFinalOracle)
      fixed.base.tape
  completeInstance :
    fixed.base.runtime.adversaryValue.rawMessages.context =
        fixedInstance.context ∧
      fixed.base.runtime.adversaryValue.1.publicProof.publicInstance.statement =
        fixedInstance.statement
  bindingFields :
    let bindings := FixedBindings.ofContext
      fixed.base.runtime.adversaryValue.rawMessages.context
    bindings.programId = fixedInstance.context.programId ∧
      bindings.releaseBinding = fixedInstance.context.releaseBinding ∧
      bindings.statementDigest = fixedInstance.context.statementDigest ∧
      bindings.attemptId = fixedInstance.context.attemptId ∧
      bindings.proofAccountId = fixedInstance.context.attemptId

theorem fixed_clean_root_has_deterministic_classifications
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Proof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (fixed : ExactFixedCleanSourceRootProjection transitionFuel configuration
      projection fixedInstance sample) :
    FixedCleanDeterministicClassifications fixed :=
  { q16 := fixed_clean_root_has_exact_q16_operational_forest fixed
    completeInstance := fixed_clean_root_preserves_complete_instance fixed
    bindingFields := fixed_clean_root_binding_fields_exact fixed }

/-- Literal program/release/statement/attempt/proof-account bindings and
opaque statement equality relative to a public instance fixed before
sampling. -/
def ReturnedRootMatchesFixedInstance
    {TapeIdentity Statement Proof Payload : Type}
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (fixedInstance : PublicInstance Statement) : Prop :=
  let bindings := FixedBindings.ofContext
    runtime.adversaryValue.rawMessages.context
  bindings.programId = fixedInstance.context.programId ∧
    bindings.releaseBinding = fixedInstance.context.releaseBinding ∧
    bindings.statementDigest = fixedInstance.context.statementDigest ∧
    bindings.attemptId = fixedInstance.context.attemptId ∧
    bindings.proofAccountId = fixedInstance.context.attemptId ∧
    runtime.adversaryValue.1.publicProof.publicInstance.statement =
      fixedInstance.statement

/-- Binding failure relative to a public instance fixed before sampling.  The
returned checked parsed proof fixes all five deployed binding projections and
the opaque statement, so this event is empty. -/
def exactFixedBindingFailureEvent
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ runtime clientRun,
    (runExactPlainRomRoot transitionFuel configuration sample).terminal =
        .returned (.completed runtime clientRun) ∧
      runtime.adversaryValue.1.publicProof.publicInstance = fixedInstance ∧
      ¬ ReturnedRootMatchesFixedInstance runtime fixedInstance}

theorem exact_fixed_binding_failure_event_empty
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (fixedInstance : PublicInstance Statement) :
    exactFixedBindingFailureEvent transitionFuel configuration fixedInstance =
      ∅ := by
  ext sample
  simp only [exactFixedBindingFailureEvent, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨runtime, clientRun, _completed, publicExact, failed⟩
  subst fixedInstance
  have bindings := checked_raw_return_preserves_public_bindings
    runtime.adversaryValue
  exact failed ⟨bindings.1, bindings.2.1, bindings.2.2.1,
    bindings.2.2.2.1, bindings.2.2.2.2, rfl⟩

/-- Strict resource/runtime failure remains an explicit class.  Unlike q16
and bindings it is empty only after the actual compiler use and runtime have
been proved within their concrete caps. -/
def exactStrictResourceRuntimeFailureEvent
    {Sample : Type} (parameters : ExactCompilerResourceParameters)
    (use : Sample → ResourceUse) (runtime : Sample → Nat) : Set Sample :=
  resourceFailureEvent use (exactCompilerResourceBudget parameters) ∪
    exactCompilerTimeoutEvent parameters runtime

theorem exact_strict_resource_runtime_failure_event_empty
    {Sample : Type} (parameters : ExactCompilerResourceParameters)
    (use : Sample → ResourceUse) (runtime : Sample → Nat)
    (within : ∀ sample,
      WithinBudget (use sample) (exactCompilerResourceBudget parameters))
    (runtimeBound : ∀ sample,
      runtime sample ≤ totalCompilerRuntimeCap parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff) :
    exactStrictResourceRuntimeFailureEvent parameters use runtime = ∅ := by
  rw [exactStrictResourceRuntimeFailureEvent,
    resource_failure_event_empty use (exactCompilerResourceBudget parameters)
      within,
    exact_compiler_timeout_event_empty_of_hard_runtime_cap parameters runtime
      runtimeBound cutoffBeyondCap]
  simp

/-- Exact named union used by the final fixed-instance compiler theorem.  The
causal target appears once; the collision and forward-reference subclasses
are included explicitly for auditability and are proved subsets of it. -/
def exactNamedCompilerBadEventUnion
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (use : ExactCompilerSample HiddenTape parameters → ResourceUse)
    (runtime : ExactCompilerSample HiddenTape parameters → Nat) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  exactPlainRomTargetEvent transitionFuel configuration ∪
    exactPairedSqueezeInputCollisionEvent ∪
    exactTranscriptTypedMerkleInputCollisionEvent ∪
    exactOutputOrStateCollisionEvent transitionFuel configuration ∪
    exactForwardReferenceOrProgrammingConflictEvent transitionFuel
      configuration ∪
    exactUnqueriedTranscriptOutputPredictionFailureEvent ∪
    exactNoPairSameStartPredictionFailureEvent ∪
    exactAdaptiveQ16ForestFailureEvent transitionFuel configuration projection ∪
    exactFixedBindingFailureEvent transitionFuel configuration fixedInstance ∪
    exactStrictResourceRuntimeFailureEvent parameters use runtime

theorem exact_named_compiler_bad_event_union_eq_target
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (use : ExactCompilerSample HiddenTape parameters → ResourceUse)
    (runtime : ExactCompilerSample HiddenTape parameters → Nat)
    (within : ∀ sample,
      WithinBudget (use sample) (exactCompilerResourceBudget parameters))
    (runtimeBound : ∀ sample,
      runtime sample ≤ totalCompilerRuntimeCap parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff) :
    exactNamedCompilerBadEventUnion transitionFuel configuration projection
        fixedInstance use runtime =
      exactPlainRomTargetEvent transitionFuel configuration := by
  unfold exactNamedCompilerBadEventUnion
  rw [exact_unqueried_transcript_output_prediction_failure_event_empty,
    exact_no_pair_same_start_prediction_failure_event_empty,
    exact_paired_squeeze_input_collision_event_empty,
    exact_transcript_typed_merkle_input_collision_event_empty,
    exact_adaptive_q16_forest_failure_event_empty transitionFuel configuration
      projection,
    exact_fixed_binding_failure_event_empty transitionFuel configuration
      fixedInstance,
    exact_strict_resource_runtime_failure_event_empty parameters use runtime
      within runtimeBound cutoffBeyondCap]
  simp only [Set.union_empty]
  ext sample
  simp only [Set.mem_union]
  have collisionImp :
      sample ∈ exactOutputOrStateCollisionEvent transitionFuel configuration →
        sample ∈ exactPlainRomTargetEvent transitionFuel configuration :=
    fun member =>
      exact_output_or_state_collision_event_subset_target transitionFuel
        configuration member
  have forwardImp : sample ∈
      exactForwardReferenceOrProgrammingConflictEvent transitionFuel
          configuration →
        sample ∈ exactPlainRomTargetEvent transitionFuel configuration :=
    fun member =>
      exact_forward_reference_or_programming_conflict_event_subset_target
        transitionFuel configuration member
  tauto

/-!
The following imported kernel theorems are the operational reason no separate
challenge-fiber summand is present:

* `same_tape_source_no_pair_replay` handles absence of both squeeze inputs;
* `operational_segment_scanned_unqueried_output_is_oblivious_through_advance`
  handles an absent output half with an observed advance half.

The exact residual is instead exposed by
`no_pair_lookup_conflict_is_prior_programming`: after complete query-history
absence, a defined pair input is necessarily inherited programming.  The
coordinate-independent conflict theorems in `V7Tag73ExactCompilerTargetClean`
show that newly sampled fork coins cannot probabilistically repair it.
-/

#print axioms exact_scheduler_target_coefficient_is_seed_plus_collision_plus_literal_prefix
#print axioms concrete_plain_rom_coefficient_is_seeded_causal_target
#print axioms initial_digest_seeded_target_coefficient_expanded
#print axioms exact_target_raw_error_is_legacy_plus_initial_digest_seed
#print axioms one_verifier_challenge_fiber_coefficient_has_36_terms
#print axioms exact_compiler_collision_prefix_and_fiber_coefficient_expanded
#print axioms root_and_replay_challenge_fiber_coefficient_le_fallback
#print axioms exact_compiler_collision_prefix_and_fiber_raw_error_is_sum
#print axioms exact_compiler_master_tape_length_at_least_1511
#print axioms exact_compiler_tape_length_ne_challenge_completion_tape_length
#print axioms successful_strict_checked_refinement_has_exact_q16_forest
#print axioms exact_source_refinement_event_preserves_public_bindings
#print axioms AspisK1.V7Tag73ResourceLazyOracle.resource_failure_event_empty
#print axioms exact_compiler_timeout_event_empty_of_hard_runtime_cap
#print axioms exact_compiler_timeout_probability_le_expected_div
#print axioms root_request_avoids_inherited_child_transition
#print axioms positive_child_transition_avoids_inherited_child_transition
#print axioms inherited_output_conflict_survives_every_new_fork_coin
#print axioms inherited_advance_conflict_survives_every_new_fork_coin
#print axioms operational_indexed_tape_coordinates_roundtrip
#print axioms run_unified_exposure_trace_operational_indexed_tape
#print axioms chronologically_clean_machine_coordinate_of_append
#print axioms chronologically_clean_fork_output_coordinate_of_append
#print axioms chronologically_clean_fork_advance_coordinate_of_append
#print axioms mem_nonpaddingExposureAnswers_iff
#print axioms exposure_seen_subset_extend
#print axioms initial_seen_subset_accumulated_exposure_seen
#print axioms nonpadding_answer_mem_accumulated_exposure_seen
#print axioms chronologically_clean_machine_answer_ne_prior_nonpadding
#print axioms chronologically_clean_fork_output_ne_prior_nonpadding
#print axioms chronologically_clean_fork_advance_ne_prior_nonpadding
#print axioms chronologically_clean_nonpadding_answers_nodup
#print axioms certified_operational_exposure_trace_exists
#print axioms certified_operational_exposure_trace_erases_to_trace
#print axioms certified_operational_exposure_trace_machine_member_has_exact_request
#print axioms certified_operational_trace_machine_after_prefix_has_exact_cursor
#print axioms certified_operational_machine_at_prefix_of_trace_decomposition
#print axioms certified_machine_exposure_at_prefix_has_exact_request
#print axioms certified_machine_exposure_at_prefix_has_exact_traversal
#print axioms machine_answer_avoids_every_history_literal_prefix
#print axioms certified_machine_exposure_at_prefix_avoids_history_literal_prefix
#print axioms unified_target_clean_constructs_operational_certificate
#print axioms unified_target_clean_implies_every_emitted_direct_fork_pair_clean
#print axioms unified_target_clean_implies_every_nonpadding_exposure_clean
#print axioms exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
#print axioms exact_compiler_unified_exposure_trace_answers_are_master_coordinates
#print axioms exact_compiler_target_clean_implies_every_emitted_direct_fork_pair_clean
#print axioms exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
#print axioms exact_compiler_target_clean_constructs_operational_certificate
#print axioms exact_plain_rom_outside_target_is_exact_compiler_clean
#print axioms exact_plain_rom_outside_target_constructs_operational_certificate
#print axioms exact_plain_rom_outside_target_actual_trace_chronologically_clean
#print axioms exact_plain_rom_outside_target_actual_trace_direct_fork_pairs_clean
#print axioms exact_compiler_target_clean_nonpadding_answers_nodup
#print axioms exact_compiler_target_clean_nonpadding_answers_avoid_dummy_digest
#print axioms exact_compiler_target_clean_has_whole_trace_facts
#print axioms AspisK1.V7Tag73NoPairReplay.same_tape_source_no_pair_replay
#print axioms operational_segment_scanned_unqueried_output_is_oblivious_through_advance
#print axioms no_pair_lookup_conflict_is_prior_programming
#print axioms existing_output_lookup_conflict_is_coordinate_independent
#print axioms existing_advance_lookup_conflict_is_coordinate_independent
#print axioms operational_unqueried_output_prediction_failure_impossible
#print axioms exact_unqueried_transcript_output_prediction_failure_event_empty
#print axioms operational_no_pair_same_start_failure_impossible
#print axioms exact_no_pair_same_start_prediction_failure_event_empty
#print axioms exact_paired_squeeze_input_collision_event_empty
#print axioms exact_transcript_typed_merkle_input_collision_event_empty
#print axioms exact_output_or_state_collision_event_subset_target
#print axioms exact_forward_reference_or_programming_conflict_event_subset_target
#print axioms exact_adaptive_q16_forest_failure_event_empty
#print axioms fixed_clean_root_has_exact_q16_operational_forest
#print axioms fixed_clean_root_has_deterministic_classifications
#print axioms exact_fixed_binding_failure_event_empty
#print axioms exact_strict_resource_runtime_failure_event_empty
#print axioms exact_named_compiler_bad_event_union_eq_target

end

end AspisK1.V7Tag73ExactProbabilityCoverageAudit
