import AspisFormal.K1.V7Tag73ExactFixedK12PrefixClassifier
import AspisFormal.K1.V7Tag73SharedShaGrammar
import AspisFormal.Pool.V7MerkleCompletePrefixStability

/-!
# The post-prover Tag-73 verifier log is not Merkle grammar

This file identifies the exact suffix added after the prover's shared-oracle
history and proves that every input in it is a transcript-machine input, hence
cannot parse as a 437-, 220-, or 53-byte Tag-73 Merkle preimage.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactK12UntypedVerifierSuffix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73RawFutureFreeDriver
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73SharedShaGrammar
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar

noncomputable section

theorem parseTypedPreimage_none_of_length_avoids
    (input : RawHashInput)
    (avoids : input.length ≠ 437 ∧ input.length ≠ 220 ∧
      input.length ≠ 53) :
    parseTypedPreimage input = none := by
  simp [parseTypedPreimage, avoids.1, avoids.2.1, avoids.2.2]

theorem raw_query_role_input_is_untyped
    (before : Digest256) (role : RawQueryRole) :
    parseTypedPreimage
      (runtimeInputToRawHashInput (role.input before)) = none := by
  apply parseTypedPreimage_none_of_length_avoids
  simpa [runtimeInputToRawHashInput] using
    (raw_query_input_length_avoids_typed_merkle before role)

theorem future_free_reply_program_path_inputs_exact
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath (futureFreeReplyProgram state action) pairs reply) :
    pairs.map Prod.fst =
      actionInputs state.current.bindings state.current.core action := by
  cases action with
  | absorb payload =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | requestRootSalt tree =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | absorbC1 root =>
      cases saltExact : state.current.core.c1Salt with
      | none =>
          simp [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path
          cases path
      | some salt =>
          simp only [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path ⊢
          cases path with
          | query _ _ output _ _ tail => cases tail; rfl
  | absorbC2 lambda chi commitment =>
      cases saltExact : state.current.core.c2Salt with
      | none =>
          simp [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path
          cases path
      | some salt =>
          simp only [futureFreeReplyProgram, structuralFutureFreeReply,
            actionInputs, saltExact] at path ⊢
          cases path with
          | query _ _ output _ _ tail => cases tail; rfl
  | squeezePair owner block =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail =>
          cases tail with
          | query _ _ advance _ _ final => cases final; rfl
  | workProbe stage nonce kind =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | checkpoint checkpoint => cases path; rfl
  | markQ16Base => cases path; rfl
  | q16CandidateAbsorb counter outcome selected =>
      simp only [futureFreeReplyProgram, structuralFutureFreeReply,
        actionInputs] at path ⊢
      cases path with
      | query _ _ output _ _ tail => cases tail; rfl
  | q16Restore counter => cases path; rfl
  | q16Selected counter => cases path; rfl
  | q16SamplerAbortReject counter => cases path; rfl
  | q16AllNoncompactReject => cases path; rfl
  | terminal => cases path; rfl

def futureFreeActionRoles (bindings : FixedBindings) (core : RuntimeCore) :
    VerifierAction → List RawQueryRole
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
  | .workProbe stage nonce _kind => [.grind stage nonce]
  | .checkpoint _ | .markQ16Base | .q16Restore _ | .q16Selected _ |
      .q16SamplerAbortReject _ | .q16AllNoncompactReject | .terminal => []
  | .q16CandidateAbsorb counter _outcome _selected =>
      [.absorb (.queryCandidate counter)]

theorem future_free_action_roles_inputs_exact
    (bindings : FixedBindings) (core : RuntimeCore) (action : VerifierAction) :
    (futureFreeActionRoles bindings core action).map
        (RawQueryRole.input core.digest) =
      actionInputs bindings core action := by
  cases action with
  | absorb payload => rfl
  | requestRootSalt tree => rfl
  | absorbC1 root =>
      cases saltExact : core.c1Salt <;>
        simp [futureFreeActionRoles, actionInputs, RawQueryRole.input,
          Payload.label, saltExact]
  | absorbC2 lambda chi commitment =>
      cases saltExact : core.c2Salt <;>
        simp [futureFreeActionRoles, actionInputs, RawQueryRole.input,
          Payload.label, saltExact]
  | squeezePair owner block => rfl
  | workProbe stage nonce kind => rfl
  | checkpoint checkpoint => rfl
  | markQ16Base => rfl
  | q16CandidateAbsorb counter outcome selected => rfl
  | q16Restore counter => rfl
  | q16Selected counter => rfl
  | q16SamplerAbortReject counter => rfl
  | q16AllNoncompactReject => rfl
  | terminal => rfl

theorem future_free_action_input_is_untyped
    (bindings : FixedBindings) (core : RuntimeCore) (action : VerifierAction)
    (input : ShaInput) (member : input ∈ actionInputs bindings core action) :
    parseTypedPreimage (runtimeInputToRawHashInput input) = none := by
  rw [← future_free_action_roles_inputs_exact bindings core action] at member
  obtain ⟨role, _roleMember, rfl⟩ := List.mem_map.mp member
  exact raw_query_role_input_is_untyped core.digest role

theorem future_free_reply_program_path_inputs_untyped
    (state : FutureFreeVerifierState) (action : VerifierAction)
    (pairs : List (ShaInput × ShaOutput)) (reply : VerifierReply)
    (path : MachineQueryPath (futureFreeReplyProgram state action) pairs reply) :
    ∀ pair ∈ pairs,
      parseTypedPreimage (runtimeInputToRawHashInput pair.1) = none := by
  have inputsExact := future_free_reply_program_path_inputs_exact state action
    pairs reply path
  intro pair member
  have inputMember : pair.1 ∈ pairs.map Prod.fst := List.mem_map_of_mem member
  rw [inputsExact] at inputMember
  exact future_free_action_input_is_untyped state.current.bindings
    state.current.core action pair.1 inputMember

theorem future_free_operational_trace_inputs_untyped
    (environment : FutureFreeEnvironment) (raw : RawTag73ProverMessages) :
    ∀ (initial final : FutureFreeVerifierState)
      (pairs : List (ShaInput × ShaOutput)),
      FutureFreeOperationalTrace environment raw initial pairs final →
      ∀ pair ∈ pairs,
        parseTypedPreimage (runtimeInputToRawHashInput pair.1) = none := by
  intro initial final pairs trace
  induction trace with
  | stop state => simp
  | next step rest ih =>
      intro pair member
      rw [List.mem_append] at member
      rcases member with headMember | tailMember
      · cases step with
        | prover submitted event snapshot appendExact => simp at headMember
        | verifier forced replyPath advanced =>
            exact future_free_reply_program_path_inputs_untyped _ _ _ _
              replyPath pair headMember
        | stutter noSubmission noAction => simp at headMember
      · exact ih pair tailMember

#print axioms raw_query_role_input_is_untyped

end

end AspisK1.V7Tag73ExactK12UntypedVerifierSuffix
