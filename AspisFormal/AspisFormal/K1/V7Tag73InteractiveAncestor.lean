import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# An explicit ROM-free interactive ancestor for deployed Tag 73

This module turns the exact deployed schedule into a finite, tape-indexed
interactive-verifier plan.  It does not expose a random-oracle function and it
does not postulate a restore operation.  Instead, hash replies are explicit
messages to an operational state machine.  A later coupling proof must show
that replies obtained from a Fiat--Shamir query history induce these steps.

The plan has three features needed by that coupling.

* Its initial state is already a complete dummy round and is stored in the
  nonempty `seen` history.
* One duplex squeeze is one complete action containing both replies to
  `S || 0x01` and `S || 0x02`; there is no restorable half-squeeze state.
* Every discarded q16 branch ends in a literal `q16Restore` action, while the
  selected branch does not.  Thus all branches start from the one digest saved
  by `markQ16Base`, without granting a generic restore capability.

The ordinary verifier and the work-erased verifier have the same actions,
replies, transcript states, nonces, absorbs, and histories.  The latter erases
only the leading-zero predicate on each selected work nonce.  No acceptance,
knowledge extraction, probability bound, or state-restoration conclusion is a
field of any definition below.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73InteractiveAncestor

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement

/-! ## Fixed bindings and typed authenticated roots -/

/-- The two deployed Merkle roots have the same 208-bit wire width but remain
different types in the interactive ancestor. -/
inductive AuthenticatedTree where
  | initialC1
  | foldedC2
  deriving DecidableEq, Repr

def AuthenticatedTree.tag : AuthenticatedTree → UInt8
  | .initialC1 => c1TreeTag
  | .foldedC2 => c2TreeTag

structure TypedMerkleRoot (tree : AuthenticatedTree) where
  value : Digest208

def c1TypedRoot (messages : Messages) : TypedMerkleRoot .initialC1 :=
  ⟨messages.c1Root⟩

def c2TypedRoot (messages : Messages) : TypedMerkleRoot .foldedC2 :=
  ⟨messages.c2.root⟩

theorem authenticated_tree_tags_are_distinct :
    AuthenticatedTree.initialC1.tag ≠ AuthenticatedTree.foldedC2.tag := by
  decide

theorem typed_merkle_root_is_208_bits
    {tree : AuthenticatedTree} (root : TypedMerkleRoot tree) :
    (bytes root.value).length = 26 := by
  simp

theorem transcript_state_is_256_bits (state : Digest256) :
    (bytes state).length = 32 := by
  simp

/-- This record makes explicit that the deployed attempt identifier and the
proof-account binding are one and the same 32-byte context field. -/
structure FixedBindings where
  programId : Bytes 32
  releaseBinding : Bytes 32
  statementDigest : Bytes 32
  attemptId : Bytes 32
  proofAccountId : Bytes 32

def FixedBindings.ofContext (context : Context) : FixedBindings where
  programId := context.programId
  releaseBinding := context.releaseBinding
  statementDigest := context.statementDigest
  attemptId := context.attemptId
  proofAccountId := context.attemptId

def FixedBindings.context (bindings : FixedBindings) : Context where
  programId := bindings.programId
  releaseBinding := bindings.releaseBinding
  statementDigest := bindings.statementDigest
  attemptId := bindings.attemptId

@[simp] theorem fixed_bindings_attempt_is_proof_account (context : Context) :
    (FixedBindings.ofContext context).attemptId =
      (FixedBindings.ofContext context).proofAccountId := by
  rfl

@[simp] theorem fixed_bindings_recover_context (context : Context) :
    (FixedBindings.ofContext context).context = context := by
  cases context
  rfl

/-! ## Complete atomic verifier actions -/

/-- A selected work probe is distinguished from adversarial probes made before
it.  This marker does not impose a first-success policy. -/
inductive WorkProbeKind where
  | adversaryHistory
  | verifierSelected
  deriving DecidableEq, Repr

/-- Every action ends at a complete verifier state.  In particular,
`squeezePair` is not split into two actions. -/
inductive VerifierAction where
  | absorb (payload : Payload)
  | requestRootSalt (tree : AuthenticatedTree)
  | absorbC1 (root : TypedMerkleRoot .initialC1)
  | absorbC2 (lambda chi : Qm31Bytes)
      (commitment : C2Commitment lambda chi)
  | squeezePair (owner : SqueezeOwner) (block : Nat)
  | workProbe (stage : WorkStage) (nonce : NonceBytes)
      (kind : WorkProbeKind)
  | checkpoint (checkpoint : Checkpoint)
  | markQ16Base
  | q16CandidateAbsorb (counter : Fin 64) (outcome : CandidateOutcome)
      (selected : Bool)
  | q16Restore (counter : Fin 64)
  | q16Selected (counter : Fin 64)
  | q16SamplerAbortReject (counter : Fin 64)
  | q16AllNoncompactReject
  | terminal

/-- Explicit replies replace oracle access.  `squeeze` associates an output
and an advance reply with one complete public-coin action. -/
inductive VerifierReply where
  | none
  | single (output : Digest256)
  | squeeze (output advance : Digest256)

/-- A public-coin bundle retains both answers for every deployed duplex
block.  The decoder consumes `outputBlocks`; `advance` values determine the
subsequent complete transcript states. -/
structure PairedCoinBlock where
  output : Digest256
  advance : Digest256

structure ChallengeCoinBundle where
  blocks : List PairedCoinBlock

def ChallengeCoinBundle.outputBlocks (bundle : ChallengeCoinBundle) :
    List Digest256 :=
  bundle.blocks.map PairedCoinBlock.output

/-- Executable decoder obligations for a fixed challenge.  This predicate is
checked data, not a field of the verifier or a compiler assumption. -/
def ChallengeCoinBundleValid (decoders : DeterministicDecoders)
    (tape : DeployedFixedTape) (id : ChallengeId)
    (bundle : ChallengeCoinBundle) : Prop :=
  bundle.blocks.length = (tape.messages.challengeUse id).blocksUsed ∧
  decoders.qm31Parameter id bundle.outputBlocks =
    some (tape.messages.challengeValue id) ∧
  match id with
  | .circlePoint sample =>
      decoders.secureCirclePoint (tape.messages.challengeValue id) =
        some (tape.circlePoints sample)
  | _ => True

structure CandidateCoinBundle where
  counter : Fin 64
  blocks : List PairedCoinBlock

def CandidateCoinBundle.outputBlocks (bundle : CandidateCoinBundle) :
    List Digest256 :=
  bundle.blocks.map PairedCoinBlock.output

def CandidateCoinBundleValid (decoders : DeterministicDecoders)
    (spec : CandidateSpec) (bundle : CandidateCoinBundle) : Prop :=
  bundle.counter = spec.counter ∧
  bundle.blocks.length = spec.outcome.blocksUsed ∧
  decoders.candidate bundle.counter bundle.outputBlocks = some spec.outcome

theorem valid_challenge_bundle_respects_exact_sampler_cap
    (decoders : DeterministicDecoders) (tape : DeployedFixedTape)
    (id : ChallengeId) (bundle : ChallengeCoinBundle)
    (valid : ChallengeCoinBundleValid decoders tape id bundle) :
    bundle.blocks.length ≤ samplerBlockCap (samplerMode id) := by
  rw [valid.1]
  exact (tape.messages.challengeUse id).withinDeployedCap

theorem valid_candidate_bundle_respects_sixty_four_draw_cap
    (decoders : DeterministicDecoders) (spec : CandidateSpec)
    (bundle : CandidateCoinBundle)
    (valid : CandidateCoinBundleValid decoders spec bundle) :
    bundle.blocks.length ≤ 8 := by
  rw [valid.2.1]
  cases spec.outcome with
  | samplerAbort => simp [CandidateOutcome.blocksUsed]
  | schedule schedule => exact schedule.withinSixtyFourDraws

inductive VerifierPhase where
  | dummyNonempty
  | after (action : VerifierAction)

/-- The typed early rounds make challenge-dependent C2 visible before the
actions are flattened.  Constructing the last round requires a commitment at
the exact newly decoded `lambda` and `chi` indices. -/
inductive AdaptiveRound where
  | c1 (root : TypedMerkleRoot .initialC1)
  | publicChallenge (id : ChallengeId) (use : SamplerUse id)
  | c2 (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi)

def adaptiveRounds (messages : Messages) : List AdaptiveRound :=
  [.c1 (c1TypedRoot messages),
   .publicChallenge .lambda (messages.challengeUse .lambda),
   .publicChallenge .chi (messages.challengeUse .chi),
   .c2 (messages.challengeValue .lambda) (messages.challengeValue .chi)
      messages.c2]

theorem adaptive_round_order_is_c1_lambda_chi_c2 (messages : Messages) :
    adaptiveRounds messages =
      [.c1 (c1TypedRoot messages),
       .publicChallenge .lambda (messages.challengeUse .lambda),
       .publicChallenge .chi (messages.challengeUse .chi),
       .c2 (messages.challengeValue .lambda) (messages.challengeValue .chi)
          messages.c2] := by
  rfl

/-- Rewinding either early challenge constructs a new dependent C2 round;
there is no operation in this type that freezes an old commitment at new
challenge indices. -/
def adaptiveC2Round (lambda chi : Qm31Bytes)
    (commitment : C2Commitment lambda chi) : AdaptiveRound :=
  .c2 lambda chi commitment

theorem adaptive_c2_round_retains_new_indices
    (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi) :
    adaptiveC2Round lambda chi commitment = .c2 lambda chi commitment := by
  rfl

/-! ## Exact finite action plan -/

def challengeActions (id : ChallengeId) (use : SamplerUse id) :
    List VerifierAction :=
  (List.range use.blocksUsed).map fun block =>
    .squeezePair (.challenge id) block

def grindingActions (stage : WorkStage) (choice : GrindingChoice stage) :
    List VerifierAction :=
  choice.probesBeforeSelected.map
      (fun nonce => .workProbe stage nonce .adversaryHistory) ++
    [.workProbe stage choice.selected .verifierSelected]

def eventActions : MachineEvent → List VerifierAction
  | .absorb payload => [.absorb payload]
  | .challenge id use => challengeActions id use
  | .grind stage choice => grindingActions stage choice
  | .check checkpoint => [.checkpoint checkpoint]

def eventsToActions (events : List MachineEvent) : List VerifierAction :=
  events.flatMap eventActions

def expandAdaptiveRound : AdaptiveRound → List VerifierAction
  | .c1 root => [.requestRootSalt .initialC1, .absorbC1 root]
  | .publicChallenge id use => challengeActions id use
  | .c2 lambda chi commitment =>
      [.requestRootSalt .foldedC2, .absorbC2 lambda chi commitment]

def adaptivePrefixPlan (tape : DeployedFixedTape) : List VerifierAction :=
  eventsToActions (prefixBeforeC1 tape.messages) ++
    (adaptiveRounds tape.messages).flatMap expandAdaptiveRound ++
    eventsToActions (prefixAfterC2 tape.messages)

def candidateActions (spec : CandidateSpec) (selected : Bool) :
    List VerifierAction :=
  [.q16CandidateAbsorb spec.counter spec.outcome selected] ++
  (List.range spec.outcome.blocksUsed).map fun block =>
    .squeezePair (.queryCandidate spec.counter) block

def discardedCandidateActions (spec : CandidateSpec) : List VerifierAction :=
  candidateActions spec false ++ [.q16Restore spec.counter]

/-! ### Total q16 scan, including both rejecting outcomes -/

inductive TotalQ16ScanResult where
  | selected (counter : Fin 64) (schedule : QuerySchedule)
  | samplerAbort (counter : Fin 64)
  | allSixtyFourNoncompact

/-- Total first-hit scan over an explicit ordered counter list.  A sampler
abort rejects immediately; a sampled noncompact schedule is discarded; and
only the first compact schedule is selected. -/
def scanQ16Candidates (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome) :
    List (Fin 64) → TotalQ16ScanResult
  | [] => .allSixtyFourNoncompact
  | counter :: rest =>
      match outcome counter with
      | .samplerAbort => .samplerAbort counter
      | .schedule schedule =>
          if frontierNodes schedule ≤ 203 then
            .selected counter schedule
          else
            scanQ16Candidates frontierNodes outcome rest

def allQ16Counters : List (Fin 64) := List.finRange 64

def totalQ16Scan (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome) : TotalQ16ScanResult :=
  scanQ16Candidates frontierNodes outcome allQ16Counters

/-- The operational action forest associated with the same total scan.  It
contains a restore after every sampled noncompact branch, stops at sampler
abort, and has no restore after the selected branch. -/
def totalQ16ActionsFrom (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome) :
    List (Fin 64) → List VerifierAction
  | [] => [.q16AllNoncompactReject]
  | counter :: rest =>
      match h : outcome counter with
      | .samplerAbort =>
          candidateActions { counter, outcome := .samplerAbort } false ++
            [.q16SamplerAbortReject counter]
      | .schedule schedule =>
          let spec : CandidateSpec := { counter, outcome := .schedule schedule }
          if frontierNodes schedule ≤ 203 then
            candidateActions spec true ++ [.q16Selected counter]
          else
            discardedCandidateActions spec ++
              totalQ16ActionsFrom frontierNodes outcome rest

def totalQ16Plan (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome) : List VerifierAction :=
  [.markQ16Base] ++
    totalQ16ActionsFrom frontierNodes outcome allQ16Counters

/-- A structural certificate generated by the total scanner itself.  The only
recursive constructor first appends a complete discarded branch, whose final
action is `q16Restore`, and then continues with the next counter. -/
inductive Q16ForestLayout : List VerifierAction → Prop where
  | selected (spec : CandidateSpec) :
      Q16ForestLayout
        (candidateActions spec true ++ [.q16Selected spec.counter])
  | samplerAbort (counter : Fin 64) :
      Q16ForestLayout
        (candidateActions { counter, outcome := .samplerAbort } false ++
          [.q16SamplerAbortReject counter])
  | allNoncompact :
      Q16ForestLayout [.q16AllNoncompactReject]
  | discard (spec : CandidateSpec) (rest : List VerifierAction)
      (restLayout : Q16ForestLayout rest) :
      Q16ForestLayout (discardedCandidateActions spec ++ rest)

theorem total_q16_actions_have_explicit_shared_base_layout
    (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome)
    (counters : List (Fin 64)) :
    Q16ForestLayout
      (totalQ16ActionsFrom frontierNodes outcome counters) := by
  induction counters with
  | nil => exact .allNoncompact
  | cons counter rest ih =>
      rw [totalQ16ActionsFrom]
      split
      · exact .samplerAbort counter
      · rename_i schedule h
        split
        · exact .selected
            { counter := counter, outcome := .schedule schedule }
        · exact .discard
            { counter := counter, outcome := .schedule schedule }
            (totalQ16ActionsFrom frontierNodes outcome rest) ih

/-- An accepting search is definitionally in the selected case; unlike
`totalQ16Scan`, this constructor consumes the already proved first-hit search
certificate used by the deployed accepting tape. -/
def acceptingQ16Result {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) : TotalQ16ScanResult :=
  .selected search.selectedCounter search.selectedSchedule

theorem accepting_search_result_is_selected
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    acceptingQ16Result search =
      .selected search.selectedCounter search.selectedSchedule := by
  rfl

def IsFirstCompactSelection (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome) (counter : Fin 64)
    (schedule : QuerySchedule) : Prop :=
  outcome counter = .schedule schedule ∧
  frontierNodes schedule ≤ 203 ∧
  ∀ earlier : Fin 64, earlier.val < counter.val →
    ∃ earlierSchedule,
      outcome earlier = .schedule earlierSchedule ∧
      203 < frontierNodes earlierSchedule

/-- This is the substantive first-success fact supplied by an accepting
deployed search, independent of the definitional result tag above. -/
theorem accepting_search_is_first_compact_selection
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    IsFirstCompactSelection frontierNodes search.outcome
      search.selectedCounter search.selectedSchedule := by
  exact ⟨search.selectedOutcome, search.selectedCompact,
    search.everyEarlierSampledAndNoncompact⟩

theorem scan_selected_result_is_compact
    (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome)
    (counters : List (Fin 64)) (counter : Fin 64)
    (schedule : QuerySchedule)
    (run : scanQ16Candidates frontierNodes outcome counters =
      .selected counter schedule) :
    frontierNodes schedule ≤ 203 := by
  induction counters with
  | nil => simp [scanQ16Candidates] at run
  | cons head rest ih =>
      rw [scanQ16Candidates] at run
      cases hresult : outcome head with
      | samplerAbort => simp [hresult] at run
      | schedule current =>
          rw [hresult] at run
          by_cases compact : frontierNodes current ≤ 203
          · simp [compact] at run
            rcases run with ⟨rfl, rfl⟩
            exact compact
          · simp [compact] at run
            exact ih run

theorem scan_sampler_abort_result_was_observed
    (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome)
    (counters : List (Fin 64)) (counter : Fin 64)
    (run : scanQ16Candidates frontierNodes outcome counters =
      .samplerAbort counter) :
    outcome counter = .samplerAbort := by
  induction counters with
  | nil => simp [scanQ16Candidates] at run
  | cons head rest ih =>
      rw [scanQ16Candidates] at run
      cases hresult : outcome head with
      | samplerAbort =>
          simp [hresult] at run
          cases run
          exact hresult
      | schedule current =>
          rw [hresult] at run
          by_cases compact : frontierNodes current ≤ 203
          · simp [compact] at run
          · simp [compact] at run
            exact ih run

theorem scan_all_noncompact_result_checked_every_counter
    (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome)
    (counters : List (Fin 64))
    (run : scanQ16Candidates frontierNodes outcome counters =
      .allSixtyFourNoncompact) :
    ∀ counter ∈ counters,
      ∃ schedule,
        outcome counter = .schedule schedule ∧
        203 < frontierNodes schedule := by
  induction counters with
  | nil => simp
  | cons head rest ih =>
      rw [scanQ16Candidates] at run
      cases hresult : outcome head with
      | samplerAbort => simp [hresult] at run
      | schedule schedule =>
          rw [hresult] at run
          by_cases compact : frontierNodes schedule ≤ 203
          · simp [compact] at run
          · simp [compact] at run
            intro counter member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨schedule, hresult, by omega⟩
            · exact ih run counter member

theorem accepting_search_excludes_sampler_abort_at_selected
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    search.outcome search.selectedCounter ≠ .samplerAbort := by
  intro abort
  have selected := search.selectedOutcome
  rw [abort] at selected
  cases selected

theorem discarded_candidate_plan_ends_in_explicit_restore
    (spec : CandidateSpec) :
    ∃ prefixActions,
      discardedCandidateActions spec =
        prefixActions ++ [.q16Restore spec.counter] := by
  exact ⟨candidateActions spec false, rfl⟩

def q16Plan (tape : DeployedFixedTape) : List VerifierAction :=
  let q16 := q16TapeOfSearch tape.search
  [.markQ16Base] ++
    q16.earlier.flatMap discardedCandidateActions ++
    candidateActions q16.selected true ++
    [.q16Selected q16.selected.counter]

/-- The exact complete action plan.  It is indexed by the fixed deployed tape,
so a transition cannot choose a convenient next action. -/
def fullPlan (tape : DeployedFixedTape) : List VerifierAction :=
  adaptivePrefixPlan tape ++ q16Plan tape ++
    eventsToActions (afterAcceptedQueryScan tape.messages) ++ [.terminal]

@[simp] theorem challenge_actions_length (id : ChallengeId)
    (use : SamplerUse id) :
    (challengeActions id use).length = use.blocksUsed := by
  simp [challengeActions]

theorem challenge_actions_nonempty (id : ChallengeId)
    (use : SamplerUse id) :
    (challengeActions id use).length > 0 := by
  simpa using use.consumesBlock

theorem challenge_actions_respect_deployed_cap (id : ChallengeId)
    (use : SamplerUse id) :
    (challengeActions id use).length ≤ samplerBlockCap (samplerMode id) := by
  simpa using use.withinDeployedCap

theorem candidate_outcome_blocks_le_eight (outcome : CandidateOutcome) :
    outcome.blocksUsed ≤ 8 := by
  cases outcome with
  | samplerAbort => simp [CandidateOutcome.blocksUsed]
  | schedule schedule => exact schedule.withinSixtyFourDraws

theorem q16_search_selected_is_compact (tape : DeployedFixedTape) :
    tape.frontierNodes tape.search.selectedSchedule ≤ 203 :=
  tape.search.selectedCompact

theorem q16_search_every_earlier_is_sampled_and_noncompact
    (tape : DeployedFixedTape) (counter : Fin 64)
    (earlier : counter.val < tape.search.selectedCounter.val) :
    ∃ schedule,
      tape.search.outcome counter = .schedule schedule ∧
      203 < tape.frontierNodes schedule :=
  tape.search.everyEarlierSampledAndNoncompact counter earlier

def AllCandidatesAbort (outcome : Fin 64 → CandidateOutcome) : Prop :=
  ∀ counter, outcome counter = .samplerAbort

theorem all_candidates_abort_excludes_accepting_search
    (frontierNodes : QuerySchedule → Nat)
    (outcome : Fin 64 → CandidateOutcome)
    (allAbort : AllCandidatesAbort outcome) :
    ¬ ∃ search : FirstCap203Search frontierNodes,
        search.outcome = outcome := by
  rintro ⟨search, houtcome⟩
  have habort : search.outcome search.selectedCounter = .samplerAbort := by
    rw [houtcome]
    exact allAbort search.selectedCounter
  have selected := search.selectedOutcome
  rw [habort] at selected
  cases selected

/-! ## Operational complete states -/

structure RuntimeCore where
  digest : Digest256
  c1Salt : Option Digest256
  c2Salt : Option Digest256
  q16Base : Option Digest256

def initialCore : RuntimeCore where
  digest := zeroBytes 32
  c1Salt := none
  c2Salt := none
  q16Base := none

/-- Exact query inputs associated with one complete action.  Structural actions
have no query; a squeeze has exactly the two distinct 33-byte inputs. -/
def actionInputs (bindings : FixedBindings) (core : RuntimeCore) :
    VerifierAction → List ByteString
  | .absorb payload =>
      [bytes core.digest ++ [domAbsorb, payload.label] ++ payload.data]
  | .requestRootSalt tree =>
      [rootSaltInput bindings.context tree.tag]
  | .absorbC1 root =>
      match core.c1Salt with
      | none => []
      | some salt =>
          [bytes core.digest ++ [domAbsorb, c1RootLabel] ++
            (Payload.c1Root root.value salt).data]
  | .absorbC2 _ _ commitment =>
      match core.c2Salt with
      | none => []
      | some salt =>
          [bytes core.digest ++ [domAbsorb, c2RootLabel] ++
            (Payload.c2Root commitment.root salt).data]
  | .squeezePair _ _ =>
      [bytes core.digest ++ [domSqueeze],
       bytes core.digest ++ [domAdvance]]
  | .workProbe _ nonce _ =>
      [bytes core.digest ++ [domGrind] ++ bytes nonce]
  | .checkpoint _ => []
  | .markQ16Base => []
  | .q16CandidateAbsorb counter _ _ =>
      [bytes core.digest ++ [domAbsorb, queryCandidateLabel,
        UInt8.ofNat counter.val]]
  | .q16Restore _ => []
  | .q16Selected _ => []
  | .q16SamplerAbortReject _ => []
  | .q16AllNoncompactReject => []
  | .terminal => []

theorem squeeze_action_has_exact_paired_inputs
    (bindings : FixedBindings) (core : RuntimeCore)
    (owner : SqueezeOwner) (block : Nat) :
    actionInputs bindings core (.squeezePair owner block) =
      [bytes core.digest ++ [1], bytes core.digest ++ [2]] ∧
    bytes core.digest ++ [1] ≠ bytes core.digest ++ [2] := by
  exact ⟨rfl, squeeze_output_and_advance_inputs_are_distinct core.digest⟩

theorem c1_root_action_uses_208_bit_root
    (bindings : FixedBindings) (core : RuntimeCore)
    (root : TypedMerkleRoot .initialC1) (salt : Digest256)
    (hasSalt : core.c1Salt = some salt) :
    actionInputs bindings core (.absorbC1 root) =
      [bytes core.digest ++ [0, 12] ++
        (Payload.c1Root root.value salt).data] := by
  simp [actionInputs, hasSalt, domAbsorb, c1RootLabel]

theorem c2_root_action_uses_208_bit_root
    (bindings : FixedBindings) (core : RuntimeCore)
    (lambda chi : Qm31Bytes) (commitment : C2Commitment lambda chi)
    (salt : Digest256) (hasSalt : core.c2Salt = some salt) :
    actionInputs bindings core (.absorbC2 lambda chi commitment) =
      [bytes core.digest ++ [0, 13] ++
        (Payload.c2Root commitment.root salt).data] := by
  simp [actionInputs, hasSalt, domAbsorb, c2RootLabel]

/-- Work-erased execution still performs every work query and retains every
nonce.  It only omits the selected nonce's rejection predicate. -/
def applyActionWorkErased (core : RuntimeCore) (action : VerifierAction)
    (reply : VerifierReply) : Option RuntimeCore :=
  match action, reply with
  | .absorb _, .single output => some { core with digest := output }
  | .requestRootSalt .initialC1, .single output =>
      some { core with c1Salt := some output }
  | .requestRootSalt .foldedC2, .single output =>
      some { core with c2Salt := some output }
  | .absorbC1 _, .single output =>
      match core.c1Salt with
      | none => none
      | some _ => some { core with digest := output }
  | .absorbC2 _ _ _, .single output =>
      match core.c2Salt with
      | none => none
      | some _ => some { core with digest := output }
  | .squeezePair _ _, .squeeze _ advance =>
      some { core with digest := advance }
  | .workProbe _ _ _, .single _ => some core
  | .checkpoint _, .none => some core
  | .markQ16Base, .none => some { core with q16Base := some core.digest }
  | .q16CandidateAbsorb _ _ _, .single output =>
      match core.q16Base with
      | none => none
      | some _ => some { core with digest := output }
  | .q16Restore _, .none =>
      match core.q16Base with
      | none => none
      | some base => some { core with digest := base }
  | .q16Selected _, .none => some core
  | .q16SamplerAbortReject _, .none => some core
  | .q16AllNoncompactReject, .none => some core
  | .terminal, .none => some core
  | _, _ => none

def selectedWorkReplyAccepted (action : VerifierAction)
    (reply : VerifierReply) : Bool :=
  match action, reply with
  | .workProbe stage _ .verifierSelected, .single output =>
      workDigestAccepted stage output
  | .workProbe _ _ .verifierSelected, _ => false
  | _, _ => true

def applyActionStrict (core : RuntimeCore) (action : VerifierAction)
    (reply : VerifierReply) : Option RuntimeCore :=
  if selectedWorkReplyAccepted action reply then
    applyActionWorkErased core action reply
  else
    none

theorem strict_action_success_survives_work_erasure
    (core next : RuntimeCore) (action : VerifierAction)
    (reply : VerifierReply)
    (run : applyActionStrict core action reply = some next) :
    applyActionWorkErased core action reply = some next := by
  unfold applyActionStrict at run
  split at run
  · exact run
  · simp at run

theorem work_probe_never_advances_in_erased_ancestor
    (core next : RuntimeCore) (stage : WorkStage) (nonce : NonceBytes)
    (kind : WorkProbeKind) (output : Digest256)
    (run : applyActionWorkErased core (.workProbe stage nonce kind)
      (.single output) = some next) :
    next.digest = core.digest := by
  have mapped := congrArg (fun value => value.map RuntimeCore.digest) run
  simpa [applyActionWorkErased] using mapped.symm

theorem squeeze_pair_installs_only_advance_state
    (core next : RuntimeCore) (owner : SqueezeOwner) (block : Nat)
    (output advance : Digest256)
    (run : applyActionWorkErased core (.squeezePair owner block)
      (.squeeze output advance) = some next) :
    next.digest = advance := by
  have mapped := congrArg (fun value => value.map RuntimeCore.digest) run
  simpa [applyActionWorkErased] using mapped.symm

theorem mark_q16_base_saves_current_digest (core next : RuntimeCore)
    (run : applyActionWorkErased core .markQ16Base .none = some next) :
    next.q16Base = some core.digest ∧ next.digest = core.digest := by
  have mapped := congrArg
    (fun value => value.map (fun state => (state.q16Base, state.digest))) run
  simpa [applyActionWorkErased] using mapped.symm

theorem q16_restore_returns_to_saved_base
    (core next : RuntimeCore) (counter : Fin 64) (base : Digest256)
    (saved : core.q16Base = some base)
    (run : applyActionWorkErased core (.q16Restore counter) .none = some next) :
    next.digest = base ∧ next.q16Base = some base := by
  simp [applyActionWorkErased, saved] at run
  subst next
  exact ⟨rfl, rfl⟩

/-- These are precisely the actions generated after `markQ16Base` by either
the accepting or total q16 plan. -/
inductive IsQ16ContinuationAction : VerifierAction → Prop where
  | candidate (counter : Fin 64) (outcome : CandidateOutcome)
      (selected : Bool) :
      IsQ16ContinuationAction (.q16CandidateAbsorb counter outcome selected)
  | squeeze (counter : Fin 64) (block : Nat) :
      IsQ16ContinuationAction (.squeezePair (.queryCandidate counter) block)
  | restore (counter : Fin 64) :
      IsQ16ContinuationAction (.q16Restore counter)
  | selected (counter : Fin 64) :
      IsQ16ContinuationAction (.q16Selected counter)
  | samplerAbort (counter : Fin 64) :
      IsQ16ContinuationAction (.q16SamplerAbortReject counter)
  | allNoncompact :
      IsQ16ContinuationAction .q16AllNoncompactReject

/-- Once the one q16 base is saved, no generated branch action can replace
it.  Together with the explicit restore at the end of every discarded branch,
this is the operational shared-base invariant. -/
theorem q16_continuation_preserves_one_saved_base
    (core next : RuntimeCore) (action : VerifierAction)
    (reply : VerifierReply) (base : Digest256)
    (isQ16 : IsQ16ContinuationAction action)
    (saved : core.q16Base = some base)
    (run : applyActionWorkErased core action reply = some next) :
    next.q16Base = some base := by
  cases isQ16 <;> cases reply <;>
    simp [applyActionWorkErased, saved] at run
  all_goals
    subst next
    simpa [saved] using saved

/-- A candidate absorb cannot execute before `markQ16Base`; successful
execution exposes the already saved base rather than fabricating one. -/
theorem successful_q16_candidate_requires_saved_base
    (core next : RuntimeCore) (counter : Fin 64)
    (outcome : CandidateOutcome) (selected : Bool) (output : Digest256)
    (run : applyActionWorkErased core
      (.q16CandidateAbsorb counter outcome selected) (.single output) =
        some next) :
    ∃ base, core.q16Base = some base ∧ next.q16Base = some base := by
  cases saved : core.q16Base with
  | none => simp [applyActionWorkErased, saved] at run
  | some base =>
      simp [applyActionWorkErased, saved] at run
      subst next
      exact ⟨base, rfl, rfl⟩

/-! ## Tape-indexed snapshots and previously-seen history -/

/-- The cursor type enforces that a snapshot is at a boundary between complete
actions.  `0` is the dummy initial round and `fullPlan.length` is the final
boundary. -/
structure CompleteSnapshot (tape : DeployedFixedTape) where
  cursor : Fin (fullPlan tape).length.succ
  core : RuntimeCore

def phaseForCursor (tape : DeployedFixedTape)
    (cursor : Fin (fullPlan tape).length.succ) : VerifierPhase :=
  if atStart : cursor.val = 0 then
    .dummyNonempty
  else
    let previous : Fin (fullPlan tape).length :=
      ⟨cursor.val - 1, by omega⟩
    .after ((fullPlan tape).get previous)

def CompleteSnapshot.phase {tape : DeployedFixedTape}
    (snapshot : CompleteSnapshot tape) : VerifierPhase :=
  phaseForCursor tape snapshot.cursor

def CompleteSnapshot.bindings {tape : DeployedFixedTape}
    (_snapshot : CompleteSnapshot tape) : FixedBindings :=
  FixedBindings.ofContext tape.messages.context

def IsComplete {tape : DeployedFixedTape}
    (snapshot : CompleteSnapshot tape) : Prop :=
  snapshot.cursor.val ≤ (fullPlan tape).length

theorem every_typed_snapshot_is_complete {tape : DeployedFixedTape}
    (snapshot : CompleteSnapshot tape) : IsComplete snapshot := by
  exact Nat.le_of_lt_succ snapshot.cursor.isLt

theorem phase_is_unique_at_one_cursor {tape : DeployedFixedTape}
    (first second : CompleteSnapshot tape)
    (sameCursor : first.cursor = second.cursor) :
    first.phase = second.phase := by
  unfold CompleteSnapshot.phase
  rw [sameCursor]

theorem every_snapshot_preserves_fixed_bindings {tape : DeployedFixedTape}
    (snapshot : CompleteSnapshot tape) :
    snapshot.bindings = FixedBindings.ofContext tape.messages.context := by
  rfl

structure TransitionRecord (tape : DeployedFixedTape) where
  before : CompleteSnapshot tape
  action : VerifierAction
  reply : VerifierReply
  inputs : List ByteString
  after : CompleteSnapshot tape

structure InteractiveVerifierState (tape : DeployedFixedTape) where
  current : CompleteSnapshot tape
  seen : List (CompleteSnapshot tape)
  transitions : List (TransitionRecord tape)

def initialSnapshot (tape : DeployedFixedTape) : CompleteSnapshot tape where
  cursor := ⟨0, Nat.zero_lt_succ _⟩
  core := initialCore

def initialInteractiveState (tape : DeployedFixedTape) :
    InteractiveVerifierState tape where
  current := initialSnapshot tape
  seen := [initialSnapshot tape]
  transitions := []

def PreviouslySeen {tape : DeployedFixedTape}
    (snapshot : CompleteSnapshot tape)
    (state : InteractiveVerifierState tape) : Prop :=
  snapshot ∈ state.seen

def NonemptyVerifierHistory {tape : DeployedFixedTape}
    (state : InteractiveVerifierState tape) : Prop :=
  state.seen ≠ []

@[simp] theorem initial_phase_is_dummy_nonempty (tape : DeployedFixedTape) :
    (initialInteractiveState tape).current.phase = .dummyNonempty := by
  simp [initialInteractiveState, initialSnapshot, CompleteSnapshot.phase,
    phaseForCursor]

theorem initial_history_is_nonempty (tape : DeployedFixedTape) :
    NonemptyVerifierHistory (initialInteractiveState tape) := by
  simp [NonemptyVerifierHistory, initialInteractiveState]

theorem initial_snapshot_is_previously_seen (tape : DeployedFixedTape) :
    PreviouslySeen (initialSnapshot tape) (initialInteractiveState tape) := by
  simp [PreviouslySeen, initialInteractiveState]

/-- Commit one already-validated reply.  This helper is not a restore
operation: its next cursor is forced to be exactly the current cursor plus one.
-/
def commitAdvance {tape : DeployedFixedTape}
    (state : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (action : VerifierAction) (reply : VerifierReply)
    (nextCore : RuntimeCore) : InteractiveVerifierState tape :=
  let nextSnapshot : CompleteSnapshot tape :=
    { cursor := ⟨state.current.cursor.val + 1, by omega⟩
      core := nextCore }
  let record : TransitionRecord tape :=
    { before := state.current
      action := action
      reply := reply
      inputs := actionInputs state.current.bindings state.current.core action
      after := nextSnapshot }
  { current := nextSnapshot
    seen := state.seen ++ [nextSnapshot]
    transitions := state.transitions ++ [record] }

/-- Execute only the next action in the deployed plan.  The caller supplies no
action and therefore cannot choose a convenient phase. -/
def advanceWorkErased {tape : DeployedFixedTape}
    (state : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply) : Option (InteractiveVerifierState tape) := do
  let action := (fullPlan tape)[state.current.cursor.val]
  let nextCore ← applyActionWorkErased state.current.core action reply
  pure (commitAdvance state available action reply nextCore)

def advanceStrict {tape : DeployedFixedTape}
    (state : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply) : Option (InteractiveVerifierState tape) := do
  let action := (fullPlan tape)[state.current.cursor.val]
  let nextCore ← applyActionStrict state.current.core action reply
  pure (commitAdvance state available action reply nextCore)

theorem strict_advance_success_survives_work_erasure
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (run : advanceStrict state available reply = some next) :
    advanceWorkErased state available reply = some next := by
  rw [advanceStrict] at run
  obtain ⟨nextCore, hstrict, hnext⟩ := Option.bind_eq_some_iff.mp run
  have herased := strict_action_success_survives_work_erasure
    state.current.core nextCore
      ((fullPlan tape)[state.current.cursor.val]) reply hstrict
  rw [advanceWorkErased]
  exact Option.bind_eq_some_iff.mpr ⟨nextCore, herased, hnext⟩

theorem successful_advance_increments_exactly_one_phase
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (run : advanceWorkErased state available reply = some next) :
    next.current.cursor.val = state.current.cursor.val + 1 := by
  rw [advanceWorkErased] at run
  obtain ⟨nextCore, _, hnext⟩ := Option.bind_eq_some_iff.mp run
  have equals := Option.some.inj hnext
  rw [← equals]
  rfl

theorem successful_advance_records_next_as_previously_seen
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (run : advanceWorkErased state available reply = some next) :
    PreviouslySeen next.current next := by
  rw [advanceWorkErased] at run
  obtain ⟨nextCore, _, hnext⟩ := Option.bind_eq_some_iff.mp run
  have equals := Option.some.inj hnext
  rw [← equals]
  simp [PreviouslySeen, commitAdvance]

theorem successful_advance_preserves_every_previously_seen_state
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (run : advanceWorkErased state available reply = some next)
    (snapshot : CompleteSnapshot tape) (seen : PreviouslySeen snapshot state) :
    PreviouslySeen snapshot next := by
  rw [advanceWorkErased] at run
  obtain ⟨nextCore, _, hnext⟩ := Option.bind_eq_some_iff.mp run
  have equals := Option.some.inj hnext
  rw [← equals]
  simp only [PreviouslySeen, commitAdvance, List.mem_append]
  exact Or.inl seen

theorem successful_advance_history_never_becomes_empty
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (run : advanceWorkErased state available reply = some next) :
    NonemptyVerifierHistory next := by
  exact fun empty => by
    have seen := successful_advance_records_next_as_previously_seen
      state next available reply run
    rw [PreviouslySeen, empty] at seen
    simp at seen

theorem successful_advance_preserves_fixed_program_release_statement_attempt
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (run : advanceWorkErased state available reply = some next) :
    next.current.bindings = state.current.bindings ∧
    next.current.bindings.proofAccountId =
      next.current.bindings.attemptId := by
  constructor
  · rfl
  · rfl

theorem successful_advance_ends_at_complete_state
    {tape : DeployedFixedTape}
    (state next : InteractiveVerifierState tape)
    (available : state.current.cursor.val < (fullPlan tape).length)
    (reply : VerifierReply)
    (_run : advanceWorkErased state available reply = some next) :
    IsComplete next.current :=
  every_typed_snapshot_is_complete next.current

/-! ## Query-count facts exposed to the resource-accounting lane -/

def VerifierAction.queryCount : VerifierAction → Nat
  | .absorb _ => 1
  | .requestRootSalt _ => 1
  | .absorbC1 _ => 1
  | .absorbC2 _ _ _ => 1
  | .squeezePair _ _ => 2
  | .workProbe _ _ _ => 1
  | .checkpoint _ => 0
  | .markQ16Base => 0
  | .q16CandidateAbsorb _ _ _ => 1
  | .q16Restore _ => 0
  | .q16Selected _ => 0
  | .q16SamplerAbortReject _ => 0
  | .q16AllNoncompactReject => 0
  | .terminal => 0

def planQueryCount (plan : List VerifierAction) : Nat :=
  (plan.map VerifierAction.queryCount).sum

@[simp] theorem plan_query_count_append
    (first second : List VerifierAction) :
    planQueryCount (first ++ second) =
      planQueryCount first + planQueryCount second := by
  simp [planQueryCount]

@[simp] theorem squeeze_pair_query_count (owner : SqueezeOwner) (block : Nat) :
    (VerifierAction.squeezePair owner block).queryCount = 2 := by
  rfl

theorem one_candidate_query_count
    (spec : CandidateSpec) (selected : Bool) :
    planQueryCount (candidateActions spec selected) =
      1 + 2 * spec.outcome.blocksUsed := by
  simp [planQueryCount, candidateActions, VerifierAction.queryCount,
    Function.comp_def, List.sum_replicate, Nat.mul_comm]

theorem one_candidate_query_count_le_seventeen
    (spec : CandidateSpec) (selected : Bool) :
    planQueryCount (candidateActions spec selected) ≤ 17 := by
  rw [one_candidate_query_count]
  have cap := candidate_outcome_blocks_le_eight spec.outcome
  omega

theorem discarded_candidate_has_same_queries_as_selected
    (spec : CandidateSpec) :
    planQueryCount (discardedCandidateActions spec) =
      planQueryCount (candidateActions spec true) := by
  rw [discardedCandidateActions]
  rw [plan_query_count_append]
  rw [one_candidate_query_count spec false,
    one_candidate_query_count spec true]
  simp [planQueryCount, VerifierAction.queryCount]

#print axioms authenticated_tree_tags_are_distinct
#print axioms adaptive_round_order_is_c1_lambda_chi_c2
#print axioms challenge_actions_respect_deployed_cap
#print axioms all_candidates_abort_excludes_accepting_search
#print axioms accepting_search_is_first_compact_selection
#print axioms scan_selected_result_is_compact
#print axioms scan_sampler_abort_result_was_observed
#print axioms scan_all_noncompact_result_checked_every_counter
#print axioms total_q16_actions_have_explicit_shared_base_layout
#print axioms squeeze_action_has_exact_paired_inputs
#print axioms strict_action_success_survives_work_erasure
#print axioms q16_restore_returns_to_saved_base
#print axioms q16_continuation_preserves_one_saved_base
#print axioms successful_q16_candidate_requires_saved_base
#print axioms every_typed_snapshot_is_complete
#print axioms initial_phase_is_dummy_nonempty
#print axioms successful_advance_records_next_as_previously_seen
#print axioms successful_advance_history_never_becomes_empty
#print axioms successful_advance_preserves_fixed_program_release_statement_attempt
#print axioms one_candidate_query_count_le_seventeen

end AspisK1.V7Tag73InteractiveAncestor
