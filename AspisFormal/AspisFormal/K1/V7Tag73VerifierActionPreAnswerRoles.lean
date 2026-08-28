import AspisFormal.K1.V7Tag73PersistentTranscriptRoles
import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner

/-!
# Pre-answer roles carried by the executable Tag-73 verifier action

`VerifierAction` is the source-control program point immediately before the
operational verifier issues its SHA calls.  This file projects each action to
the exact `RawQueryRole` list which it will issue.  The projection does not
inspect a reply.  Its input erasure is exactly `verifierIssuedInputs`, including
the fact that historical grinding probes issue no verifier call.

The small list-control policy then feeds those already-fixed roles to the
persistent role machine one call at a time.  It deliberately cannot install a
role at a pre-existing cache entry; adversary-origin cache hits therefore
remain the separate first-exposure problem rather than being relabelled here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73VerifierActionPreAnswerRoles

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73PersistentTranscriptRoles

/-! ## Exact role plan at the action boundary -/

/-- The exact roles known from the verifier action and pre-answer runtime
core.  Neither `VerifierReply` nor any SHA output is an argument. -/
def verifierActionPreAnswerRoles (bindings : FixedBindings)
    (core : RuntimeCore) : VerifierAction → List RawQueryRole
  | .absorb payload => [.absorb payload]
  | .requestRootSalt tree => [.publicRootSalt bindings.context tree.tag]
  | .absorbC1 root =>
      match core.c1Salt with
      | none => []
      | some salt => [.absorb (Payload.c1Root root.value salt)]
  | .absorbC2 _lambda _chi commitment =>
      match core.c2Salt with
      | none => []
      | some salt => [.absorb (Payload.c2Root commitment.root salt)]
  | .squeezePair owner block =>
      [.squeezeOutput owner block, .squeezeAdvance owner block]
  | .workProbe _stage _nonce .adversaryHistory => []
  | .workProbe stage nonce .verifierSelected => [.grind stage nonce]
  | .checkpoint _ => []
  | .markQ16Base => []
  | .q16CandidateAbsorb counter _outcome _selected =>
      [.absorb (.queryCandidate counter)]
  | .q16Restore _ => []
  | .q16Selected _ => []
  | .q16SamplerAbortReject _ => []
  | .q16AllNoncompactReject => []
  | .terminal => []

/-- The action role plan erases to the literal list queried by the deployed
verifier runner. -/
theorem verifier_action_preanswer_roles_inputs_exact
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) :
    (verifierActionPreAnswerRoles bindings core action).map
        (RawQueryRole.input core.digest) =
      verifierIssuedInputs bindings core action := by
  cases action with
  | absorb payload =>
      simp [verifierActionPreAnswerRoles, verifierIssuedInputs, actionInputs,
        RawQueryRole.input]
  | requestRootSalt tree =>
      rfl
  | absorbC1 root =>
      cases salt : core.c1Salt <;>
        simp [verifierActionPreAnswerRoles, verifierIssuedInputs, actionInputs,
          RawQueryRole.input, Payload.label, salt]
  | absorbC2 lambda chi commitment =>
      cases salt : core.c2Salt <;>
        simp [verifierActionPreAnswerRoles, verifierIssuedInputs, actionInputs,
          RawQueryRole.input, Payload.label, salt]
  | squeezePair owner block =>
      rfl
  | workProbe stage nonce kind =>
      cases kind <;> rfl
  | checkpoint checkpoint =>
      rfl
  | markQ16Base =>
      rfl
  | q16CandidateAbsorb counter outcome selected =>
      rfl
  | q16Restore counter =>
      rfl
  | q16Selected counter =>
      rfl
  | q16SamplerAbortReject counter =>
      rfl
  | q16AllNoncompactReject =>
      rfl
  | terminal =>
      rfl

/-- Consequently the existing oracle program is definitionally a query over
the inputs of the pre-answer role plan. -/
theorem verifier_action_program_uses_preanswer_role_inputs
    (evidence : OracleState) (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) :
    verifierActionProgram evidence bindings core action =
      queryInputsFor
        ((verifierActionPreAnswerRoles bindings core action).map
          (RawQueryRole.input core.digest))
        (replyFromVerifierOutputs evidence bindings core action) := by
  rw [verifierActionProgram,
    verifier_action_preanswer_roles_inputs_exact]

/-! ## Executable one-action persistent policy -/

/-- Exact role/input pairs computed before an action starts. -/
def verifierActionPreAnswerBindings (bindings : FixedBindings)
    (core : RuntimeCore) (action : VerifierAction) :
    List (PersistentTranscriptRole RawQueryRole) :=
  (verifierActionPreAnswerRoles bindings core action).map fun role =>
    { role := role, input := role.input core.digest }

/-- Control for one action is only the unconsumed suffix of its fixed role
plan. -/
abbrev VerifierActionRoleControl :=
  List (PersistentTranscriptRole RawQueryRole)

/-- Consume one already-fixed action role per matching operational query.
Classification happens before the output argument supplied to `afterQuery`.
An unexpected input receives no role and does not advance the plan. -/
def verifierActionRolePolicy :
    ExecutablePreAnswerRolePolicy VerifierActionRoleControl RawQueryRole where
  classify control _actor _oracle input :=
    match control with
    | [] => none
    | binding :: _ =>
        if binding.input = input then some binding.role else none
  afterQuery control _actor _before input _output _after :=
    match control with
    | [] => []
    | binding :: rest =>
        if binding.input = input then rest else control
  afterProgramming control _actor _before _programming _after := control

@[simp] theorem verifier_action_bindings_inputs
    (bindings : FixedBindings) (core : RuntimeCore)
    (action : VerifierAction) :
    (verifierActionPreAnswerBindings bindings core action).map
        PersistentTranscriptRole.input =
      verifierIssuedInputs bindings core action := by
  rw [verifierActionPreAnswerBindings, List.map_map]
  change
    (verifierActionPreAnswerRoles bindings core action).map
        (RawQueryRole.input core.digest) =
      verifierIssuedInputs bindings core action
  exact verifier_action_preanswer_roles_inputs_exact bindings core action

theorem verifier_action_policy_classifies_head_before_answer
    (binding : PersistentTranscriptRole RawQueryRole)
    (rest : VerifierActionRoleControl) (actor : QueryActor)
    (oracle : OracleState) :
    verifierActionRolePolicy.classify (binding :: rest) actor oracle
        binding.input =
      some binding.role := by
  simp [verifierActionRolePolicy]

theorem verifier_action_policy_consumes_head_after_matching_query
    (binding : PersistentTranscriptRole RawQueryRole)
    (rest : VerifierActionRoleControl) (actor : QueryActor)
    (before after : OracleState) (output : ShaOutput) :
    verifierActionRolePolicy.afterQuery (binding :: rest) actor before
        binding.input output after = rest := by
  simp [verifierActionRolePolicy]

/-! ## Shared K1.3--K1.5 specializations

These are specializations of the same action projection, not separate causal
routers.  `ChallengeId` distinguishes the width-29/semantic, gamma, and
relation-alpha families; `queryCandidate` distinguishes every q16
counter/block coordinate before its answer is decoded. -/

@[simp] theorem challenge_sampler_pair_roles_are_preanswer
    (bindings : FixedBindings) (core : RuntimeCore)
    (id : ChallengeId) (block : Nat) :
    verifierActionPreAnswerRoles bindings core
        (.squeezePair (.challenge id) block) =
      [.squeezeOutput (.challenge id) block,
       .squeezeAdvance (.challenge id) block] := by
  rfl

@[simp] theorem q16_sampler_pair_roles_are_preanswer
    (bindings : FixedBindings) (core : RuntimeCore)
    (counter : Fin 64) (block : Nat) :
    verifierActionPreAnswerRoles bindings core
        (.squeezePair (.queryCandidate counter) block) =
      [.squeezeOutput (.queryCandidate counter) block,
       .squeezeAdvance (.queryCandidate counter) block] := by
  rfl

@[simp] theorem q16_candidate_absorb_role_is_preanswer
    (bindings : FixedBindings) (core : RuntimeCore)
    (counter : Fin 64) (outcome : CandidateOutcome) (selected : Bool) :
    verifierActionPreAnswerRoles bindings core
        (.q16CandidateAbsorb counter outcome selected) =
      [.absorb (.queryCandidate counter)] := by
  rfl

#print axioms verifier_action_preanswer_roles_inputs_exact
#print axioms verifier_action_program_uses_preanswer_role_inputs
#print axioms verifier_action_bindings_inputs
#print axioms verifier_action_policy_classifies_head_before_answer
#print axioms verifier_action_policy_consumes_head_after_matching_query
#print axioms challenge_sampler_pair_roles_are_preanswer
#print axioms q16_sampler_pair_roles_are_preanswer
#print axioms q16_candidate_absorb_role_is_preanswer

end AspisK1.V7Tag73VerifierActionPreAnswerRoles
