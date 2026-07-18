import AspisFormal.V5SumcheckCommitment
import AspisFormal.V5CompleteView

/-!
# Component-B transcript binding with a deterministic challenge derivation

In `V5SumcheckBinding`, the binding theorems take a
`committedBeforeChallenge` relation that their proofs do not use; the
conclusions there follow from `Function.Injective commit` alone.  Part 1 of
this file states those conclusions with exactly that hypothesis and no order
relation.  Part 2 builds the transcript model in which order has logical
content.

Part 1: for an injective commitment to one degree-27 message, or to the full
271-coordinate Component-B state, commitment equality forces coefficient
equality, and with it equality of every derived round message, terminal
covector and ten-round recurrence value, at every evaluation point.  These
are statements about injective functions.  They hold for evaluation points
chosen before the commitment as well as after it.

Part 2: the pre-`eta` transcript is the public prefix together with the
Component-B mask root.  A `FiatShamirSchedule` derives `eta` as a function of
that transcript, and derives the round-`i` challenge from the transcript
extended by `eta` and the masked messages of rounds `0` through `i`.  An
accepted run carries the verifier's recomputation equations
`eta = scheme.eta preEta` and `point = derivedPoint scheme preEta eta
messages`.  The theorems rewrite along those equations: equal committed
prefixes force equal `eta` for arbitrary later data, equal message prefixes
force equal round challenges, and an authenticated terminal value is
identified with the bound state's terminal covector at the transcript-derived
point.

What this file proves unconditionally: the statements listed above, in the
symbolic model where challenges are values of the schedule's functions.

What remains an explicit assumption: set-theoretic opening uniqueness at a
root (`OpeningUniquenessAt`), the residue of computational commitment/PCS
binding.  `ComponentBComputationalBinding` reuses
`AspisV5CompleteView.ComputationalPreEtaCommitmentBinding` with the
deterministic derivation as its challenge map; its computational-binding
conjunct is a game parameter, not a theorem.

What remains a named correspondence obligation:
`RustPreEtaAbsorbOrderCorrespondence` and
`RustRoundChallengeCorrespondence` — that the Rust transcript serialises and
absorbs exactly the modelled prefix in exactly the modelled order.  Nothing
here inspects the Rust code.

What remains a named external assumption:
`ChallengeDerivationHashAssumption` — hash or random-oracle properties of the
deployed challenge functions.  No hash security is proved.

Chronology itself is not proved.  The proved order content is: `eta` is a
deterministic function of the committed prefix, the round-`i` challenge is a
deterministic function of the data through round `i`, and every accepted
run's challenges are values of those functions.  Openings and claimed
terminal values are outside both functions' domains.
-/

namespace AspisV5SumcheckTranscriptBinding

open AspisSumcheckMasking AspisV5SumcheckCommitment AspisV5CompleteView

/-! ## Part 1 — commitment injectivity, stated with the hypotheses it uses -/

section PureAlgebra

variable {K Commitment : Type*} [Field K]

/-- Equality of injective commitments fixes the complete degree-27
coefficient vector.  The hypothesis is injectivity and nothing else: no
transcript-order relation appears, because none is used. -/
theorem degree27_coefficients_eq_of_injective_commitment
    (commit : Degree27RoundMessage K → Commitment)
    (hinjective : Function.Injective commit)
    (left right : Degree27RoundMessage K)
    (hcommit : commit left = commit right) :
    left = right :=
  hinjective hcommit

/-- An injective degree-27 commitment determines the round polynomial at
every evaluation point.  The quantifier is over all points: injectivity gives
this for points chosen before the commitment as well as after it, so the
statement carries no order content. -/
theorem degree27_coeffEval_eq_of_injective_commitment
    (commit : Degree27RoundMessage K → Commitment)
    (hinjective : Function.Injective commit)
    (left right : Degree27RoundMessage K)
    (hcommit : commit left = commit right) (x : K) :
    coeffEval left x = coeffEval right x := by
  rw [degree27_coefficients_eq_of_injective_commitment
    commit hinjective left right hcommit]

end PureAlgebra

/-- The full bound Component-B mask state: one initial claim and ten blocks
of 27 tail coefficients — all 271 coordinates, not endpoint values.
`SumcheckMasking.booleanEndpoints_do_not_determine_eval` is the reason the
bound object must be this state: Boolean endpoint data leave every
non-Boolean degree-27 evaluation free. -/
structure BoundComponentBState (K : Type*) where
  /-- The initial mask claim. -/
  initial : K
  /-- The 27 freely sampled tail coefficients of each of the ten rounds. -/
  tails : Fin roundCount → Fin tailCount → K

section FullState

variable {K Commitment : Type*} [Field K]

/-- The terminal Component-B functional of one bound state at one ten-round
point. -/
def boundTerminal (state : BoundComponentBState K)
    (point : Fin roundCount → K) : K :=
  terminalCovector point state.initial state.tails

/-- The terminal functional agrees with the literal ten-round recurrence, by
the kernel-checked covector identity. -/
theorem boundTerminal_eq_tenRoundTerminal (state : BoundComponentBState K)
    (point : Fin roundCount → K) :
    boundTerminal state point =
      tenRoundTerminal state.initial state.tails point :=
  (tenRoundTerminal_eq_terminalCovector state.initial state.tails point).symm

omit [Field K] in
/-- Equality of injective full-state commitments fixes all 271 coordinates.
Injectivity is the only hypothesis; no field structure is used. -/
theorem componentBState_eq_of_injective_commitment
    (commit : BoundComponentBState K → Commitment)
    (hinjective : Function.Injective commit)
    (left right : BoundComponentBState K)
    (hcommit : commit left = commit right) :
    left = right :=
  hinjective hcommit

/-- The incoming claim at a round: the recurrence applied to the already
evaluated earlier rounds.  Same recurrence as
`AspisV5SumcheckCommitment.chainContributions`. -/
def incomingClaimAt (state : BoundComponentBState K)
    (point : Fin roundCount → K) (round : Fin roundCount) : K :=
  chainContributions state.initial
    (List.ofFn (fun index : Fin (round : ℕ) =>
      tailEvaluation
        (state.tails ⟨index, lt_trans index.isLt round.isLt⟩)
        (point ⟨index, lt_trans index.isLt round.isLt⟩)))

/-- The complete degree-27 mask message of one round of the chained
construction, derived from the bound state. -/
def roundMessageAt (h2 : (2 : K) ≠ 0) (state : BoundComponentBState K)
    (point : Fin roundCount → K) (round : Fin roundCount) :
    Degree27RoundMessage K :=
  maskRoundCoeff (incomingClaimAt state point round)
    (zeroBoundaryFromTail h2 (state.tails round))

/-- An injective full-state commitment determines every derived round
message evaluation, including the recursively derived incoming claim, at
every point vector and every evaluation argument. -/
theorem componentB_roundMessageEval_eq_of_injective_commitment
    (h2 : (2 : K) ≠ 0)
    (commit : BoundComponentBState K → Commitment)
    (hinjective : Function.Injective commit)
    (left right : BoundComponentBState K)
    (hcommit : commit left = commit right)
    (point : Fin roundCount → K) (round : Fin roundCount) (x : K) :
    coeffEval (roundMessageAt h2 left point round) x =
      coeffEval (roundMessageAt h2 right point round) x := by
  rw [componentBState_eq_of_injective_commitment
    commit hinjective left right hcommit]

/-- An injective full-state commitment determines the public terminal
covector at every ten-coordinate point. -/
theorem componentB_terminalCovector_eq_of_injective_commitment
    (commit : BoundComponentBState K → Commitment)
    (hinjective : Function.Injective commit)
    (left right : BoundComponentBState K)
    (hcommit : commit left = commit right)
    (point : Fin roundCount → K) :
    terminalCovector point left.initial left.tails =
      terminalCovector point right.initial right.tails := by
  rw [componentBState_eq_of_injective_commitment
    commit hinjective left right hcommit]

/-- An injective full-state commitment determines the literal ten-round
recurrence value at every ten-coordinate point. -/
theorem componentB_tenRoundTerminal_eq_of_injective_commitment
    (commit : BoundComponentBState K → Commitment)
    (hinjective : Function.Injective commit)
    (left right : BoundComponentBState K)
    (hcommit : commit left = commit right)
    (point : Fin roundCount → K) :
    tenRoundTerminal left.initial left.tails point =
      tenRoundTerminal right.initial right.tails point := by
  rw [componentBState_eq_of_injective_commitment
    commit hinjective left right hcommit]

end FullState

/-! ## Part 2 — the transcript model in which order has logical content -/

/-- The committed pre-`eta` transcript: the public prefix (statement, prior
commitments, Component-A data) followed by the Component-B mask root.  The
root is inside the challenge function's argument; that inclusion is what a
commit-then-challenge order means in this model. -/
structure PreEtaTranscript (Public Root : Type*) where
  /-- Public transcript data absorbed before the Component-B root. -/
  publicPrefix : Public
  /-- The Component-B mask commitment root, absorbed after the prefix and
  before `eta`. -/
  maskRoot : Root

/-- Deterministic Fiat--Shamir challenge derivation for Component B.  `eta`
is a function of the pre-`eta` transcript alone.  `roundChallenge` is a
function of the pre-`eta` transcript, `eta` and a list of already sent
masked round messages.  Later messages, openings and claimed terminal values
are outside both domains. -/
structure FiatShamirSchedule (Public Root K : Type*) [Field K] where
  /-- The first challenge as a function of the committed pre-`eta`
  transcript. -/
  eta : PreEtaTranscript Public Root → K
  /-- A later challenge as a function of the transcript extended by `eta`
  and the masked messages sent so far. -/
  roundChallenge : PreEtaTranscript Public Root → K →
    List (Degree27RoundMessage K) → K

section TranscriptModel

variable {Public Root K : Type*} [Field K]

/-- The transcript-derived ten-round evaluation point.  The round-`i`
challenge is the schedule's challenge function applied to the pre-`eta`
transcript, the derived `eta`, and the masked messages of rounds `0`
through `i`. -/
def derivedPoint (scheme : FiatShamirSchedule Public Root K)
    (preEta : PreEtaTranscript Public Root) (eta : K)
    (messages : Fin roundCount → Degree27RoundMessage K) :
    Fin roundCount → K :=
  fun round => scheme.roundChallenge preEta eta
    (List.ofFn fun earlier : Fin ((round : ℕ) + 1) =>
      messages ⟨earlier.val,
        lt_of_le_of_lt (Nat.lt_succ_iff.mp earlier.isLt) round.isLt⟩)

/-- The round-`i` derived challenge depends only on the messages of rounds
`0` through `i`: replacing every later message leaves it unchanged. -/
theorem derivedPoint_congr_message_prefix
    (scheme : FiatShamirSchedule Public Root K)
    (preEta : PreEtaTranscript Public Root) (eta : K)
    (messages₁ messages₂ : Fin roundCount → Degree27RoundMessage K)
    (round : Fin roundCount)
    (hmessages : ∀ earlier : Fin roundCount, earlier ≤ round →
      messages₁ earlier = messages₂ earlier) :
    derivedPoint scheme preEta eta messages₁ round =
      derivedPoint scheme preEta eta messages₂ round :=
  congrArg (scheme.roundChallenge preEta eta)
    (congrArg List.ofFn (funext fun earlier =>
      hmessages
        ⟨earlier.val,
          lt_of_le_of_lt (Nat.lt_succ_iff.mp earlier.isLt) round.isLt⟩
        (Fin.le_def.mpr (Nat.lt_succ_iff.mp earlier.isLt))))

/-- One accepted Component-B transcript.  The two equation fields are the
verifier's recomputation checks: an accepted transcript's challenges are the
values of the schedule's functions on the corresponding committed data.
They are the load-bearing order facts of this model, and the theorems below
rewrite along them. -/
structure AcceptedRun {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K) where
  /-- The committed pre-`eta` transcript. -/
  preEta : PreEtaTranscript Public Root
  /-- The first challenge recorded in the transcript. -/
  eta : K
  /-- The ten masked degree-27 round messages sent after `eta`. -/
  messages : Fin roundCount → Degree27RoundMessage K
  /-- The ten recorded round challenges. -/
  point : Fin roundCount → K
  /-- Recomputation equation: `eta` is the schedule's function of the
  committed pre-`eta` transcript. -/
  eta_eq : eta = scheme.eta preEta
  /-- Recomputation equation: the evaluation point is derived from the
  transcript extended by `eta` and the sent messages. -/
  point_eq : point = derivedPoint scheme preEta eta messages

variable {scheme : FiatShamirSchedule Public Root K}

/-- Two accepted runs with the same committed pre-`eta` transcript have the
same `eta`, whatever their later messages, challenges, openings or claimed
values.  The proof rewrites both sides to `scheme.eta` of the common prefix:
`eta` is fixed by the committed prefix because it is literally
`scheme.eta preEta`. -/
theorem eta_fixed_by_committed_prefix
    (run₁ run₂ : AcceptedRun scheme)
    (hprefix : run₁.preEta = run₂.preEta) :
    run₁.eta = run₂.eta := by
  rw [run₁.eta_eq, run₂.eta_eq, hprefix]

/-- Two accepted runs with the same committed prefix and the same messages
through round `i` have the same round-`i` challenge, whatever their later
messages.  Both recomputation equations are rewritten to reach the common
derivation. -/
theorem roundChallenge_fixed_by_message_prefix
    (run₁ run₂ : AcceptedRun scheme)
    (hprefix : run₁.preEta = run₂.preEta) (round : Fin roundCount)
    (hmessages : ∀ earlier : Fin roundCount, earlier ≤ round →
      run₁.messages earlier = run₂.messages earlier) :
    run₁.point round = run₂.point round := by
  rw [run₁.point_eq, run₂.point_eq, run₁.eta_eq, run₂.eta_eq, hprefix]
  exact derivedPoint_congr_message_prefix scheme run₂.preEta
    (scheme.eta run₂.preEta) run₁.messages run₂.messages round hmessages

/-- Two accepted runs with the same committed prefix and the same ten
messages have the same complete evaluation point. -/
theorem point_fixed_by_committed_prefix_and_messages
    (run₁ run₂ : AcceptedRun scheme)
    (hprefix : run₁.preEta = run₂.preEta)
    (hmessages : run₁.messages = run₂.messages) :
    run₁.point = run₂.point := by
  rw [run₁.point_eq, run₂.point_eq, run₁.eta_eq, run₂.eta_eq, hprefix,
    hmessages]

end TranscriptModel

/-! ## The binding assumption, explicit and named -/

/-- Set-theoretic opening uniqueness at one root.  This is the residue of
computational commitment binding used by the theorems below: a computational
binding game supplies it only up to the adversary's advantage, so it enters
here as a named assumption, never as a conclusion. -/
def OpeningUniquenessAt {Root State : Type*}
    (Opens : Root → State → Prop) (root : Root) : Prop :=
  ∀ state₁ state₂, Opens root state₁ → Opens root state₂ → state₁ = state₂

/-- An ideal injective commitment satisfies opening uniqueness at every
root, for the opening relation `commit state = root`. -/
theorem openingUniquenessAt_of_injective_commit
    {Root State : Type*} (commit : State → Root)
    (hinjective : Function.Injective commit) (root : Root) :
    OpeningUniquenessAt (fun root state => commit state = root) root :=
  fun _ _ h₁ h₂ => hinjective (h₁.trans h₂.symm)

/-- The uniqueness conjunct of
`AspisV5CompleteView.IdealPreEtaOpeningUniqueness` supplies opening
uniqueness at every root. -/
theorem openingUniquenessAt_of_ideal
    {Root State Challenge : Type*}
    {Opens : Root → State → Prop}
    {DerivesChallenge : Root → Challenge → Prop}
    {challengeFromRoot : Root → Challenge}
    (hideal : IdealPreEtaOpeningUniqueness
      Opens DerivesChallenge challengeFromRoot)
    (root : Root) : OpeningUniquenessAt Opens root :=
  fun state₁ state₂ h₁ h₂ => hideal.1 root state₁ state₂ h₁ h₂

/-- An injective full-state commitment together with the deterministic
schedule instantiates `AspisV5CompleteView.IdealPreEtaOpeningUniqueness` at a
fixed public prefix: the challenge map is `root ↦ scheme.eta ⟨publicPrefix,
root⟩` and the derivation relation is its graph. -/
theorem idealPreEtaOpeningUniqueness_of_injective_commit
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K) (publicPrefix : Public)
    (commit : BoundComponentBState K → Root)
    (hinjective : Function.Injective commit) :
    IdealPreEtaOpeningUniqueness
      (fun root state => commit state = root)
      (fun root challenge => challenge = scheme.eta ⟨publicPrefix, root⟩)
      (fun root => scheme.eta ⟨publicPrefix, root⟩) :=
  ⟨fun _root _ _ h₁ h₂ => hinjective (h₁.trans h₂.symm),
    fun _ _ => Iff.rfl⟩

/-- Component-B instantiation of the computational interface from
`V5CompleteView`: the opening relation of the mask root, with the challenge
map given by the deterministic schedule at a fixed public prefix.
`ComputationallyBinding` stays an abstract game parameter. -/
def ComponentBComputationalBinding
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K) (publicPrefix : Public)
    (Opens : Root → BoundComponentBState K → Prop)
    (ComputationallyBinding :
      (Root → BoundComponentBState K → Prop) → Prop) : Prop :=
  ComputationalPreEtaCommitmentBinding Opens
    (fun root challenge => challenge = scheme.eta ⟨publicPrefix, root⟩)
    (fun root => scheme.eta ⟨publicPrefix, root⟩)
    ComputationallyBinding

/-- Under the deterministic schedule, the challenge-dependence conjunct of
`ComputationalPreEtaCommitmentBinding` holds definitionally, so the
interface reduces to exactly the abstract binding game.  The residue of the
computational assumption is the game and nothing else. -/
theorem componentBComputationalBinding_iff_game
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K) (publicPrefix : Public)
    (Opens : Root → BoundComponentBState K → Prop)
    (ComputationallyBinding :
      (Root → BoundComponentBState K → Prop) → Prop) :
    ComponentBComputationalBinding scheme publicPrefix Opens
        ComputationallyBinding ↔
      ComputationallyBinding Opens :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => Iff.rfl⟩⟩

/-! ## The terminal theorems -/

section Terminal

variable {Public Root K : Type*} [Field K]
variable {scheme : FiatShamirSchedule Public Root K}

/-- Terminal determination for one accepted run.

Given opening uniqueness at the run's mask root (the named binding residue)
and the terminal-authentication interface
`AspisV5CompleteView.AuthenticatedTerminalMaskEvaluation` for the bound
state's terminal functional:

* an accepted alternate opening of the same root is the same bound state;
* the authenticated terminal value is the bound state's terminal covector at
  the transcript-derived point
  `derivedPoint scheme run.preEta (scheme.eta run.preEta) run.messages`.

The conclusion's evaluation point is spelled with `scheme.eta run.preEta` in
place of `run.eta`: the proof rewrites along `run.point_eq` and `run.eta_eq`,
so the order equations identify the point at which the terminal value is
authenticated. -/
theorem acceptedRun_terminalValue_determined
    (Opens : Root → BoundComponentBState K → Prop)
    (AuthenticatedTerminal : Root → (Fin roundCount → K) → K → Prop)
    (run : AcceptedRun scheme)
    (hbinding : OpeningUniquenessAt Opens run.preEta.maskRoot)
    (hauthenticated : AuthenticatedTerminalMaskEvaluation
      Opens AuthenticatedTerminal boundTerminal)
    (state alternate : BoundComponentBState K)
    (hstate : Opens run.preEta.maskRoot state)
    (halternate : Opens run.preEta.maskRoot alternate)
    (value : K)
    (hvalue : AuthenticatedTerminal run.preEta.maskRoot run.point value) :
    alternate = state ∧
      value = boundTerminal state
        (derivedPoint scheme run.preEta (scheme.eta run.preEta)
          run.messages) := by
  refine ⟨hbinding alternate state halternate hstate, ?_⟩
  have hterminal : value = boundTerminal state run.point :=
    hauthenticated run.preEta.maskRoot state run.point value hstate hvalue
  rw [hterminal, run.point_eq, run.eta_eq]

/-- The recurrence form of the terminal determination: the authenticated
value is the literal ten-round recurrence of the bound state at the
transcript-derived point. -/
theorem acceptedRun_tenRoundTerminal_determined
    (Opens : Root → BoundComponentBState K → Prop)
    (AuthenticatedTerminal : Root → (Fin roundCount → K) → K → Prop)
    (run : AcceptedRun scheme)
    (hbinding : OpeningUniquenessAt Opens run.preEta.maskRoot)
    (hauthenticated : AuthenticatedTerminalMaskEvaluation
      Opens AuthenticatedTerminal boundTerminal)
    (state alternate : BoundComponentBState K)
    (hstate : Opens run.preEta.maskRoot state)
    (halternate : Opens run.preEta.maskRoot alternate)
    (value : K)
    (hvalue : AuthenticatedTerminal run.preEta.maskRoot run.point value) :
    alternate = state ∧
      value = tenRoundTerminal state.initial state.tails
        (derivedPoint scheme run.preEta (scheme.eta run.preEta)
          run.messages) := by
  obtain ⟨halt, hval⟩ := acceptedRun_terminalValue_determined
    Opens AuthenticatedTerminal run hbinding hauthenticated
    state alternate hstate halternate value hvalue
  exact ⟨halt, hval.trans (boundTerminal_eq_tenRoundTerminal state _)⟩

/-- Terminal uniqueness across runs: two accepted runs with the same
committed prefix (hence the same mask root) and the same ten messages
authenticate the same terminal value, under opening uniqueness at that root.
The evaluation points are identified through the recomputation equations and
the states through the binding residue. -/
theorem terminalValue_fixed_across_runs
    (Opens : Root → BoundComponentBState K → Prop)
    (AuthenticatedTerminal : Root → (Fin roundCount → K) → K → Prop)
    (run₁ run₂ : AcceptedRun scheme)
    (hprefix : run₁.preEta = run₂.preEta)
    (hmessages : run₁.messages = run₂.messages)
    (hbinding : OpeningUniquenessAt Opens run₁.preEta.maskRoot)
    (hauthenticated : AuthenticatedTerminalMaskEvaluation
      Opens AuthenticatedTerminal boundTerminal)
    (state₁ state₂ : BoundComponentBState K)
    (hstate₁ : Opens run₁.preEta.maskRoot state₁)
    (hstate₂ : Opens run₂.preEta.maskRoot state₂)
    (value₁ value₂ : K)
    (hvalue₁ : AuthenticatedTerminal run₁.preEta.maskRoot run₁.point value₁)
    (hvalue₂ : AuthenticatedTerminal run₂.preEta.maskRoot run₂.point
      value₂) :
    value₁ = value₂ := by
  have hroot : run₂.preEta.maskRoot = run₁.preEta.maskRoot :=
    congrArg PreEtaTranscript.maskRoot hprefix.symm
  rw [hroot] at hstate₂ hvalue₂
  have hstates : state₂ = state₁ := hbinding state₂ state₁ hstate₂ hstate₁
  have hpoint : run₁.point = run₂.point :=
    point_fixed_by_committed_prefix_and_messages run₁ run₂ hprefix hmessages
  have h₁ : value₁ = boundTerminal state₁ run₁.point :=
    hauthenticated run₁.preEta.maskRoot state₁ run₁.point value₁
      hstate₁ hvalue₁
  have h₂ : value₂ = boundTerminal state₂ run₂.point :=
    hauthenticated run₁.preEta.maskRoot state₂ run₂.point value₂
      hstate₂ hvalue₂
  rw [h₁, h₂, hstates, hpoint]

end Terminal

/-! ## Named obligations outside the symbolic model -/

/-- Correspondence obligation, not proved: the Rust transcript derives `eta`
by hashing the serialised public prefix followed by the serialised mask
root, in that order, and the result equals the modelled challenge function.
Discharging it requires inspecting the Rust absorb sequence. -/
def RustPreEtaAbsorbOrderCorrespondence
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K)
    (serialisePublic : Public → List UInt8)
    (serialiseRoot : Root → List UInt8)
    (rustEtaOfBytes : List UInt8 → K) : Prop :=
  ∀ preEta : PreEtaTranscript Public Root,
    rustEtaOfBytes
        (serialisePublic preEta.publicPrefix ++
          serialiseRoot preEta.maskRoot) =
      scheme.eta preEta

/-- Correspondence obligation, not proved: the Rust transcript derives each
round challenge from the bytes of the pre-`eta` transcript, `eta`, and the
messages sent so far, in that order, matching the modelled round-challenge
function. -/
def RustRoundChallengeCorrespondence
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K)
    (serialisePublic : Public → List UInt8)
    (serialiseRoot : Root → List UInt8)
    (serialiseEta : K → List UInt8)
    (serialiseMessages : List (Degree27RoundMessage K) → List UInt8)
    (rustChallengeOfBytes : List UInt8 → K) : Prop :=
  ∀ (preEta : PreEtaTranscript Public Root) (eta : K)
      (messages : List (Degree27RoundMessage K)),
    rustChallengeOfBytes
        (serialisePublic preEta.publicPrefix ++
          serialiseRoot preEta.maskRoot ++
          serialiseEta eta ++ serialiseMessages messages) =
      scheme.roundChallenge preEta eta messages

/-- External cryptographic assumption, not proved: the deployed challenge
functions satisfy a hash or random-oracle game supplied by a computational
model.  The game is a parameter; this file assigns it a name and nothing
more. -/
def ChallengeDerivationHashAssumption
    {Public Root K : Type*} [Field K]
    (scheme : FiatShamirSchedule Public Root K)
    (SatisfiesHashGame : (PreEtaTranscript Public Root → K) →
      (PreEtaTranscript Public Root → K →
        List (Degree27RoundMessage K) → K) → Prop) : Prop :=
  SatisfiesHashGame scheme.eta scheme.roundChallenge

/-!
## Ledger

Unconditional, in this file's symbolic model: Part 1's injectivity algebra;
`eta_fixed_by_committed_prefix`; `roundChallenge_fixed_by_message_prefix`;
`point_fixed_by_committed_prefix_and_messages`;
`acceptedRun_terminalValue_determined` and its recurrence and cross-run
forms, each conditional only on the hypotheses named in its statement.

Explicit assumption: `OpeningUniquenessAt` at the deployed mask root.  The
ideal discharges (`openingUniquenessAt_of_injective_commit`,
`idealPreEtaOpeningUniqueness_of_injective_commit`) cover the injective
model only; for a deployed PCS the assumption is computational and remains
the game parameter of `ComponentBComputationalBinding`.

Named correspondence obligations: `RustPreEtaAbsorbOrderCorrespondence`,
`RustRoundChallengeCorrespondence`.  Named external assumption:
`ChallengeDerivationHashAssumption`.  None is proved here, and no theorem in
this file depends on them; they mark where the symbolic model ends.
-/

end AspisV5SumcheckTranscriptBinding

#print axioms AspisV5SumcheckTranscriptBinding.degree27_coefficients_eq_of_injective_commitment
#print axioms AspisV5SumcheckTranscriptBinding.degree27_coeffEval_eq_of_injective_commitment
#print axioms AspisV5SumcheckTranscriptBinding.boundTerminal_eq_tenRoundTerminal
#print axioms AspisV5SumcheckTranscriptBinding.componentBState_eq_of_injective_commitment
#print axioms AspisV5SumcheckTranscriptBinding.componentB_roundMessageEval_eq_of_injective_commitment
#print axioms AspisV5SumcheckTranscriptBinding.componentB_terminalCovector_eq_of_injective_commitment
#print axioms AspisV5SumcheckTranscriptBinding.componentB_tenRoundTerminal_eq_of_injective_commitment
#print axioms AspisV5SumcheckTranscriptBinding.derivedPoint_congr_message_prefix
#print axioms AspisV5SumcheckTranscriptBinding.eta_fixed_by_committed_prefix
#print axioms AspisV5SumcheckTranscriptBinding.roundChallenge_fixed_by_message_prefix
#print axioms AspisV5SumcheckTranscriptBinding.point_fixed_by_committed_prefix_and_messages
#print axioms AspisV5SumcheckTranscriptBinding.openingUniquenessAt_of_injective_commit
#print axioms AspisV5SumcheckTranscriptBinding.openingUniquenessAt_of_ideal
#print axioms AspisV5SumcheckTranscriptBinding.idealPreEtaOpeningUniqueness_of_injective_commit
#print axioms AspisV5SumcheckTranscriptBinding.componentBComputationalBinding_iff_game
#print axioms AspisV5SumcheckTranscriptBinding.acceptedRun_terminalValue_determined
#print axioms AspisV5SumcheckTranscriptBinding.acceptedRun_tenRoundTerminal_determined
#print axioms AspisV5SumcheckTranscriptBinding.terminalValue_fixed_across_runs
#print axioms AspisV5SumcheckTranscriptBinding.OpeningUniquenessAt
#print axioms AspisV5SumcheckTranscriptBinding.ComponentBComputationalBinding
#print axioms AspisV5SumcheckTranscriptBinding.RustPreEtaAbsorbOrderCorrespondence
#print axioms AspisV5SumcheckTranscriptBinding.RustRoundChallengeCorrespondence
#print axioms AspisV5SumcheckTranscriptBinding.ChallengeDerivationHashAssumption
