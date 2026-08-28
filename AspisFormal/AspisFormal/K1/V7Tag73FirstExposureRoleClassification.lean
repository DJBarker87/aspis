import AspisFormal.K1.V7Tag73VerifierActionPreAnswerRoles
import AspisFormal.K1.V7Tag73PersistentRoleSelectionObstruction
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity
import AspisFormal.K1.V7Tag73CausalProgrammingFreshness

/-!
# Classification boundary for adversary-first Tag-73 coordinates

The deployed squeeze input retains the complete pre-answer digest and its
output/advance domain byte, but erases the logical owner and block number.
Consequently neither raw bytes nor an otherwise unrestricted oracle history
can classify all future verifier roles.  This file gives the exact
constructor-level obstruction and an executable adversary-first/cache-hit
witness.

There is one important causal case that *is* already covered by the exact
compiler target.  If an adversary queried `S || domain` before the fresh
answer `S` existed, then `S` is a literal prefix of prior history at the point
where it is sampled.  Such an execution hits `operationalRequestTargets` and
is excluded by the existing target-clean certificate.  The remaining case is
a query made after `S` is already known but before a canonical Tag-73 path has
reserved a unique logical role for it.

No probability statement, protocol byte, or source assumption is introduced
here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73FirstExposureRoleClassification

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73VerifierActionPreAnswerRoles
open AspisK1.V7Tag73PersistentRoleSelectionObstruction
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73CausalProgrammingFreshness
open AspisK1.V7Tag73SqueezeInputStateInjectivity

/-! ## Exactly what the raw coordinate retains -/

theorem squeeze_output_coordinate_forgets_owner_and_block
    (before : Digest256) (firstOwner secondOwner : SqueezeOwner)
    (firstBlock secondBlock : Nat) :
    (RawQueryRole.squeezeOutput firstOwner firstBlock).input before =
      (RawQueryRole.squeezeOutput secondOwner secondBlock).input before := by
  rfl

theorem squeeze_advance_coordinate_forgets_owner_and_block
    (before : Digest256) (firstOwner secondOwner : SqueezeOwner)
    (firstBlock secondBlock : Nat) :
    (RawQueryRole.squeezeAdvance firstOwner firstBlock).input before =
      (RawQueryRole.squeezeAdvance secondOwner secondBlock).input before := by
  rfl

theorem squeeze_output_coordinate_determines_before_digest
    (first second : Digest256) (firstOwner secondOwner : SqueezeOwner)
    (firstBlock secondBlock : Nat)
    (equal :
      (RawQueryRole.squeezeOutput firstOwner firstBlock).input first =
        (RawQueryRole.squeezeOutput secondOwner secondBlock).input second) :
    first = second := by
  exact output_input_eq_implies_state_eq first second equal

theorem squeeze_advance_coordinate_determines_before_digest
    (first second : Digest256) (firstOwner secondOwner : SqueezeOwner)
    (firstBlock secondBlock : Nat)
    (equal :
      (RawQueryRole.squeezeAdvance firstOwner firstBlock).input first =
        (RawQueryRole.squeezeAdvance secondOwner secondBlock).input second) :
    first = second := by
  exact advance_input_eq_implies_state_eq first second equal

theorem squeeze_output_and_advance_coordinates_are_disjoint
    (outputState advanceState : Digest256)
    (outputOwner advanceOwner : SqueezeOwner)
    (outputBlock advanceBlock : Nat) :
    (RawQueryRole.squeezeOutput outputOwner outputBlock).input outputState ≠
      (RawQueryRole.squeezeAdvance advanceOwner advanceBlock).input
        advanceState := by
  exact output_input_ne_advance_input outputState advanceState

/-! ## No raw-coordinate or unrestricted history/input classifier -/

abbrev RawCoordinateRoleClassifier := ShaInput → Option RawQueryRole

abbrev HistoryInputVerifierRoleClassifier :=
  List QueryRecord → ShaInput → Option RawQueryRole

def ClassifiesRawRole (classifier : RawCoordinateRoleClassifier)
    (before : Digest256) (role : RawQueryRole) : Prop :=
  classifier (role.input before) = some role

def ClassifiesHistoryRole (classifier : HistoryInputVerifierRoleClassifier)
    (history : List QueryRecord) (before : Digest256)
    (role : RawQueryRole) : Prop :=
  classifier history (role.input before) = some role

theorem lambda_output_role_ne_gamma_output_role :
    RawQueryRole.squeezeOutput (.challenge .lambda) 0 ≠
      RawQueryRole.squeezeOutput (.challenge .gamma) 0 := by
  intro equal
  injection equal with ownerEqual
  injection ownerEqual with idEqual
  exact ChallengeId.noConfusion idEqual

theorem gamma_output_role_ne_q16_output_role :
    RawQueryRole.squeezeOutput (.challenge .gamma) 0 ≠
      RawQueryRole.squeezeOutput (.queryCandidate 0) 0 := by
  intro equal
  injection equal with ownerEqual
  cases ownerEqual

theorem same_owner_distinct_blocks_are_distinct_roles
    (owner : SqueezeOwner) :
    RawQueryRole.squeezeOutput owner 0 ≠
      RawQueryRole.squeezeOutput owner 1 := by
  intro equal
  injection equal with _ blockEqual
  omega

theorem no_raw_coordinate_classifier_classifies_lambda_and_gamma
    (classifier : RawCoordinateRoleClassifier) (before : Digest256) :
    ¬ (ClassifiesRawRole classifier before
          (.squeezeOutput (.challenge .lambda) 0) ∧
       ClassifiesRawRole classifier before
          (.squeezeOutput (.challenge .gamma) 0)) := by
  rintro ⟨lambdaExact, gammaExact⟩
  have sameInput :
      (RawQueryRole.squeezeOutput (.challenge .lambda) 0).input before =
        (RawQueryRole.squeezeOutput (.challenge .gamma) 0).input before := by
    rfl
  have equalSome :
      some (RawQueryRole.squeezeOutput (.challenge .lambda) 0) =
        some (RawQueryRole.squeezeOutput (.challenge .gamma) 0) := by
    exact lambdaExact.symm.trans ((congrArg classifier sameInput).trans gammaExact)
  exact lambda_output_role_ne_gamma_output_role (Option.some.inj equalSome)

theorem no_history_input_classifier_classifies_lambda_and_gamma
    (classifier : HistoryInputVerifierRoleClassifier)
    (history : List QueryRecord) (before : Digest256) :
    ¬ (ClassifiesHistoryRole classifier history before
          (.squeezeOutput (.challenge .lambda) 0) ∧
       ClassifiesHistoryRole classifier history before
          (.squeezeOutput (.challenge .gamma) 0)) := by
  rintro ⟨lambdaExact, gammaExact⟩
  have sameInput :
      (RawQueryRole.squeezeOutput (.challenge .lambda) 0).input before =
        (RawQueryRole.squeezeOutput (.challenge .gamma) 0).input before := by
    rfl
  have equalSome :
      some (RawQueryRole.squeezeOutput (.challenge .lambda) 0) =
        some (RawQueryRole.squeezeOutput (.challenge .gamma) 0) := by
    exact lambdaExact.symm.trans
      ((congrArg (classifier history) sameInput).trans gammaExact)
  exact lambda_output_role_ne_gamma_output_role (Option.some.inj equalSome)

/-! The exact verifier-action abstraction has the same boundary.  At a fixed
runtime core, changing only the logical owner changes the role plan but not
the issued SHA inputs. -/

theorem lambda_and_gamma_actions_have_identical_inputs_at_same_core
    (bindings : FixedBindings) (core : RuntimeCore) :
    verifierIssuedInputs bindings core
        (.squeezePair (.challenge .lambda) 0) =
      verifierIssuedInputs bindings core
        (.squeezePair (.challenge .gamma) 0) := by
  rfl

theorem gamma_and_q16_actions_have_identical_inputs_at_same_core
    (bindings : FixedBindings) (core : RuntimeCore) :
    verifierIssuedInputs bindings core
        (.squeezePair (.challenge .gamma) 0) =
      verifierIssuedInputs bindings core
        (.squeezePair (.queryCandidate 0) 0) := by
  rfl

/-! ## Executable adversary-first/cache-hit witness -/

def twoCallOneFreshLimits : OracleLimits where
  totalCalls := 2
  freshCalls := 1
  programmedPoints := 0

def adversaryFirstSqueezeState (before answer : Digest256) : OracleState where
  table :=
    [{ input := bytes before ++ [domSqueeze]
       output := answer
       source := .fresh }]
  history :=
    [{ input := bytes before ++ [domSqueeze]
       output := answer
       actor := .adversary
       origin := .fresh }]
  programmingHistory := []
  totalCalls := 1
  freshCalls := 1

def verifierCachedSqueezeState (before answer : Digest256) : OracleState where
  table := (adversaryFirstSqueezeState before answer).table
  history := (adversaryFirstSqueezeState before answer).history ++
    [{ input := bytes before ++ [domSqueeze]
       output := answer
       actor := .verifier
       origin := .cached }]
  programmingHistory := []
  totalCalls := 2
  freshCalls := 1

theorem adversary_first_squeeze_query_is_fresh
    (before answer : Digest256) :
    queryOracle (constantAnswerController answer) twoCallOneFreshLimits
        .adversary emptyOracle (bytes before ++ [domSqueeze]) =
      .ok (answer, adversaryFirstSqueezeState before answer) := by
  simp [queryOracle, constantAnswerController, twoCallOneFreshLimits,
    emptyOracle, lookupEntry, adversaryFirstSqueezeState]

theorem later_verifier_squeeze_query_is_cached
    (before answer : Digest256) :
    queryOracle (constantAnswerController answer) twoCallOneFreshLimits
        .verifier (adversaryFirstSqueezeState before answer)
          (bytes before ++ [domSqueeze]) =
      .ok (answer, verifierCachedSqueezeState before answer) := by
  simp [queryOracle, twoCallOneFreshLimits,
    adversaryFirstSqueezeState, verifierCachedSqueezeState, lookupEntry,
    cachedOrigin]

/-- The exact arbitrary-oracle/action abstraction admits two future logical
uses of one identical adversary-created cache coordinate.  The operational
oracle executions are real `queryOracle` executions; the two `VerifierAction`
plans differ only in metadata erased by their common SHA input.  This does not
claim that both alternatives are complete accepted production transcripts. -/
theorem same_preanswer_coordinate_can_have_distinct_future_roles
    (bindings : FixedBindings) (core : RuntimeCore) (answer : Digest256) :
    queryOracle (constantAnswerController answer) twoCallOneFreshLimits
        .adversary emptyOracle (bytes core.digest ++ [domSqueeze]) =
          .ok (answer, adversaryFirstSqueezeState core.digest answer) ∧
    queryOracle (constantAnswerController answer) twoCallOneFreshLimits
        .verifier (adversaryFirstSqueezeState core.digest answer)
          ((RawQueryRole.squeezeOutput (.challenge .lambda) 0).input
            core.digest) =
          .ok (answer, verifierCachedSqueezeState core.digest answer) ∧
    queryOracle (constantAnswerController answer) twoCallOneFreshLimits
        .verifier (adversaryFirstSqueezeState core.digest answer)
          ((RawQueryRole.squeezeOutput (.challenge .gamma) 0).input
            core.digest) =
          .ok (answer, verifierCachedSqueezeState core.digest answer) ∧
    verifierIssuedInputs bindings core
        (.squeezePair (.challenge .lambda) 0) =
      verifierIssuedInputs bindings core
        (.squeezePair (.challenge .gamma) 0) ∧
    RawQueryRole.squeezeOutput (.challenge .lambda) 0 ≠
      RawQueryRole.squeezeOutput (.challenge .gamma) 0 := by
  exact ⟨adversary_first_squeeze_query_is_fresh core.digest answer,
    later_verifier_squeeze_query_is_cached core.digest answer,
    later_verifier_squeeze_query_is_cached core.digest answer,
    lambda_and_gamma_actions_have_identical_inputs_at_same_core bindings core,
    lambda_output_role_ne_gamma_output_role⟩

/-! ## The already-covered forward-reference subcase -/

theorem prior_output_coordinate_for_later_fresh_state_hits_target
    (seen : Finset Digest256) (state : OracleState)
    (currentInput : ShaInput) (answer : Digest256)
    (record : QueryRecord) (member : record ∈ state.history)
    (owner : SqueezeOwner) (block : Nat)
    (recordExact :
      record.input = (RawQueryRole.squeezeOutput owner block).input answer) :
    answer ∈ operationalRequestTargets seen state.history currentInput := by
  apply (operational_request_target_hit_iff_mem seen state.history
    currentInput answer).mp
  apply OperationalRequestTargetHit.priorLiteralPrefix record member
  rw [recordExact]
  exact literal_squeeze_input_has_state_prefix answer domSqueeze

theorem prior_advance_coordinate_for_later_fresh_state_hits_target
    (seen : Finset Digest256) (state : OracleState)
    (currentInput : ShaInput) (answer : Digest256)
    (record : QueryRecord) (member : record ∈ state.history)
    (owner : SqueezeOwner) (block : Nat)
    (recordExact :
      record.input = (RawQueryRole.squeezeAdvance owner block).input answer) :
    answer ∈ operationalRequestTargets seen state.history currentInput := by
  apply (operational_request_target_hit_iff_mem seen state.history
    currentInput answer).mp
  apply OperationalRequestTargetHit.priorLiteralPrefix record member
  rw [recordExact]
  exact literal_squeeze_input_has_state_prefix answer domAdvance

theorem target_clean_fresh_state_was_not_prequeried_as_output_coordinate
    (seen : Finset Digest256) (state : OracleState)
    (currentInput : ShaInput) (answer : Digest256)
    (avoids : answer ∉
      operationalRequestTargets seen state.history currentInput)
    (record : QueryRecord) (member : record ∈ state.history)
    (owner : SqueezeOwner) (block : Nat) :
    record.input ≠
      (RawQueryRole.squeezeOutput owner block).input answer := by
  intro exactInput
  exact avoids (prior_output_coordinate_for_later_fresh_state_hits_target
    seen state currentInput answer record member owner block exactInput)

theorem target_clean_fresh_state_was_not_prequeried_as_advance_coordinate
    (seen : Finset Digest256) (state : OracleState)
    (currentInput : ShaInput) (answer : Digest256)
    (avoids : answer ∉
      operationalRequestTargets seen state.history currentInput)
    (record : QueryRecord) (member : record ∈ state.history)
    (owner : SqueezeOwner) (block : Nat) :
    record.input ≠
      (RawQueryRole.squeezeAdvance owner block).input answer := by
  intro exactInput
  exact avoids (prior_advance_coordinate_for_later_fresh_state_hits_target
    seen state currentInput answer record member owner block exactInput)

#print axioms squeeze_output_coordinate_forgets_owner_and_block
#print axioms squeeze_advance_coordinate_forgets_owner_and_block
#print axioms squeeze_output_coordinate_determines_before_digest
#print axioms squeeze_advance_coordinate_determines_before_digest
#print axioms squeeze_output_and_advance_coordinates_are_disjoint
#print axioms no_raw_coordinate_classifier_classifies_lambda_and_gamma
#print axioms no_history_input_classifier_classifies_lambda_and_gamma
#print axioms lambda_and_gamma_actions_have_identical_inputs_at_same_core
#print axioms gamma_and_q16_actions_have_identical_inputs_at_same_core
#print axioms adversary_first_squeeze_query_is_fresh
#print axioms later_verifier_squeeze_query_is_cached
#print axioms same_preanswer_coordinate_can_have_distinct_future_roles
#print axioms prior_output_coordinate_for_later_fresh_state_hits_target
#print axioms prior_advance_coordinate_for_later_fresh_state_hits_target
#print axioms target_clean_fresh_state_was_not_prequeried_as_output_coordinate
#print axioms target_clean_fresh_state_was_not_prequeried_as_advance_coordinate

end AspisK1.V7Tag73FirstExposureRoleClassification
