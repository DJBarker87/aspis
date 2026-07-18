import AspisFormal.V5InactiveClaimDeployedCorrespondence
import AspisFormal.V5SumcheckTranscriptBinding

/-!
# Transcript ordering for the deployed Component-B joint pair

`V5InactiveClaimDeployedCorrespondence` names
`DeployedJointPairAbsorbedPreChallenge` — the terminal-triple span
`[5799, 5847)` and the carried inactive-claim span `[5847, 5863)` of the v5
wire prefix are absorbed into the Fiat-Shamir transcript before the
dependent second-phase challenges are drawn (`label::CLAIM` before `γ`,
`programs/aspis-verifier/src/v5_cu_probe.rs:880-886`;
`label::SECOND_PHASE_CLAIM` before `κ`, lines 888-894) — and delegates the
predicate's semantics to the transcript model.  This module is that
transcript model.  It mirrors the load-bearing ordering pattern of
`V5SumcheckTranscriptBinding`: an accepted second-phase run carries
recomputation equations (`gamma_eq`, `kappa_eq`) identifying the recorded
challenges with values of a deterministic schedule on the committed
transcript slots, and every ordering theorem rewrites along those equations
together with the slot equations extracted from
`DeployedJointPairAbsorbedPreChallenge`.  The ordering premise is consumed,
not decorated: without it the run's absorbed slots bear no relation to the
wire, and no challenge is recomputable from the wire spans.

Separation, maintained throughout:

* The **algebraic distribution theorem** is
  `AspisV5InactiveClaimDeployedCorrespondence.deployed_joint_hiding_of_binary_mask`
  — a PMF equality over the transcribed terminal covector whose statement
  and proof mention no schedule, no accepted run, no absorb predicate and
  no wire offset.  This module does not re-prove or alter it.
* The **computational Fiat-Shamir interface** is the named premise
  `DeployedJointPairAbsorbedPreChallenge`, read through
  `absorbedAtDesignatedSlot`, together with the recomputation equations of
  `AcceptedSecondPhaseRun`.  No distribution statement appears in it.
* The deployment wrapper `deployed_joint_hiding_with_transcript_ordering`
  composes the two: its hiding conjunct is proved by the algebraic theorem
  from the algebraic premises alone, and its ordering conjuncts are proved
  from the transcript premises alone.  Neither side's proof term touches
  the other side's hypotheses.

What this module does not do: it does not prove that the deployed Rust
absorbs the modelled spans in the modelled order — that identification is
exactly the hypothesis `DeployedJointPairAbsorbedPreChallenge`, plus the
named schedule correspondence `RustSecondPhaseChallengeCorrespondence`
below; it proves no hash or random-oracle property of the deployed
challenge derivation; and it leaves the Question 2 freshness premise
untouched.
-/

namespace AspisV5InactiveClaimDeployedTranscriptOrdering

open AspisV5SumcheckCommitment AspisV5CompactTerminal AspisV5CompleteView
  AspisV5InactiveClaimJointHiding AspisV5InactiveClaimDeployedCorrespondence
  AspisV5SumcheckTranscriptBinding

/-! ## 1. The second-phase transcript model

The deployed verifier draws two challenges after the sumcheck rounds: `γ`
after absorbing the terminal triple under `label::CLAIM`, and `κ` after
absorbing the carried inactive claim under `label::SECOND_PHASE_CLAIM`
(`v5_cu_probe.rs:880-894`).  The model mirrors
`AspisV5SumcheckTranscriptBinding.FiatShamirSchedule` and
`AspisV5SumcheckTranscriptBinding.AcceptedRun`: challenges are values of
deterministic functions of the committed data, and an accepted run carries
the verifier's recomputation equations as fields. -/

/-- Deterministic second-phase challenge derivation.  `gammaOf` maps the
prior transcript (everything absorbed before `label::CLAIM`: public prefix,
commitment roots, `η`, the ten masked round messages, the claims table) and
the `label::CLAIM` span to the layer-zero challenge `γ`; `kappaOf`
additionally consumes the `label::SECOND_PHASE_CLAIM` span and yields `κ`.
Data absorbed after a challenge is outside that challenge's domain: that
exclusion is the model's order content, exactly as in
`AspisV5SumcheckTranscriptBinding.FiatShamirSchedule`. -/
structure SecondPhaseSchedule (Prior Bytes K : Type*) where
  /-- `γ` as a function of the prior transcript and the `label::CLAIM`
  span. -/
  gammaOf : Prior → Bytes → K
  /-- `κ` as a function of the prior transcript, the `label::CLAIM` span
  and the `label::SECOND_PHASE_CLAIM` span. -/
  kappaOf : Prior → Bytes → Bytes → K

/-- One accepted second-phase transcript.  The two equation fields are the
verifier's recomputation checks — the mirror of `eta_eq` and `point_eq` in
`AspisV5SumcheckTranscriptBinding.AcceptedRun`: an accepted run's recorded
challenges are the schedule's values on the committed slots.  They are the
load-bearing order facts of this model; the theorems below rewrite along
them.  Nothing in this structure relates the slots to the wire prefix —
that relation is exactly the premise
`DeployedJointPairAbsorbedPreChallenge`, consumed as a hypothesis below,
never built in. -/
structure AcceptedSecondPhaseRun {Prior Bytes K : Type*}
    (scheme : SecondPhaseSchedule Prior Bytes K) where
  /-- Everything the run absorbed before `label::CLAIM`. -/
  prior : Prior
  /-- The bytes the run absorbed under `label::CLAIM`, before `γ`. -/
  claimLabelSlot : Bytes
  /-- The bytes the run absorbed under `label::SECOND_PHASE_CLAIM`, before
  `κ`. -/
  secondPhaseClaimLabelSlot : Bytes
  /-- The recorded layer-zero challenge. -/
  gamma : K
  /-- The recorded second-phase challenge. -/
  kappa : K
  /-- Recomputation equation: `γ` is the schedule's function of the
  committed prior and the `label::CLAIM` slot. -/
  gamma_eq : gamma = scheme.gammaOf prior claimLabelSlot
  /-- Recomputation equation: `κ` is the schedule's function of the
  committed prior and both absorbed slots. -/
  kappa_eq : kappa = scheme.kappaOf prior claimLabelSlot
    secondPhaseClaimLabelSlot

/-- The transcript model's semantics for the `absorbedBeforeChallenge`
parameter of `DeployedJointPairAbsorbedPreChallenge`, relative to one
accepted second-phase run and one wire slicer.  A byte string is absorbed
before its dependent challenge exactly when the run's committed slot that
the deployed label schedule designates for that string carries it: the wire
designates the terminal-triple span `[5799, 5847)` for the `label::CLAIM`
slot (absorbed before `γ`) and the inactive-claim span `[5847, 5863)` for
the `label::SECOND_PHASE_CLAIM` slot (absorbed before `κ`).  A byte string
matching neither designated span is constrained by neither conjunct; one
matching both (possible only when the slicer returns equal spans) must sit
in both slots.  The premise instance
`DeployedJointPairAbsorbedPreChallenge slice (absorbedAtDesignatedSlot run slice)`
therefore says exactly: this run absorbed the wire's two designated spans
at their designated pre-challenge slots.  Everywhere below that instance is
a hypothesis — the Rust absorb schedule is never discharged by
definition. -/
def absorbedAtDesignatedSlot {Prior Bytes K : Type*}
    {scheme : SecondPhaseSchedule Prior Bytes K}
    (run : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (bytes : Bytes) : Prop :=
  (bytes = slice v5TerminalTripleOffset v5InactiveClaimOffset →
      run.claimLabelSlot = bytes) ∧
    (bytes = slice v5InactiveClaimOffset v5ReservedOffset →
      run.secondPhaseClaimLabelSlot = bytes)

/-! ## 2. The slot equations extracted from the ordering premise

The two rewriting equations that make `DeployedJointPairAbsorbedPreChallenge`
load-bearing.  Each consumes the premise instance; neither is provable
without it. -/

/-- First slot equation of the ordering premise: the run's `label::CLAIM`
slot is the wire's terminal-triple span `[5799, 5847)`. -/
theorem claimLabelSlot_eq_of_absorbed {Prior Bytes K : Type*}
    {scheme : SecondPhaseSchedule Prior Bytes K}
    (run : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (habsorbed : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run slice)) :
    run.claimLabelSlot
      = slice v5TerminalTripleOffset v5InactiveClaimOffset :=
  habsorbed.1.1 rfl

/-- Second slot equation of the ordering premise: the run's
`label::SECOND_PHASE_CLAIM` slot is the wire's inactive-claim span
`[5847, 5863)`. -/
theorem secondPhaseClaimLabelSlot_eq_of_absorbed {Prior Bytes K : Type*}
    {scheme : SecondPhaseSchedule Prior Bytes K}
    (run : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (habsorbed : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run slice)) :
    run.secondPhaseClaimLabelSlot
      = slice v5InactiveClaimOffset v5ReservedOffset :=
  habsorbed.2.2 rfl

/-! ## 3. Single-run ordering theorems: the pair is fixed before the
challenge

The recomputation equations of the run and the slot equations of the
ordering premise are rewritten in sequence.  The conclusions place the wire
spans — and, through the serialization premise, the encoded carried claim —
inside the challenge functions' arguments: the challenge is drawn as a
deterministic function of data that already contains the joint pair, so the
pair cannot be chosen after the challenge. -/

/-- **`γ` is recomputable from the committed wire.**  For an accepted run
whose absorbed slots are the wire's designated spans, the recorded `γ` is
the schedule's value at the committed prior and the terminal-triple span
`[5799, 5847)` — the span containing the masked terminal at
`[5831, 5847)`.  The proof rewrites the recomputation equation `gamma_eq`
and then the first slot equation of the ordering premise. -/
theorem gamma_recomputed_from_committed_wire {Prior Bytes K : Type*}
    {scheme : SecondPhaseSchedule Prior Bytes K}
    (run : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (habsorbed : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run slice)) :
    run.gamma = scheme.gammaOf run.prior
      (slice v5TerminalTripleOffset v5InactiveClaimOffset) := by
  rw [run.gamma_eq, claimLabelSlot_eq_of_absorbed run slice habsorbed]

/-- **The deployment wrapper: `κ` is a deterministic function of the
committed prior, the absorbed terminal-triple span, and the encoded carried
claim.**  The joint (terminal, inactive) pair being absorbed pre-challenge
is what lets the second-phase challenge be recomputed from the committed
prefix: the proof rewrites the recomputation equation `kappa_eq`, then both
slot equations extracted from `DeployedJointPairAbsorbedPreChallenge`, then
the claim-position premise.  The encoded pair sits inside `κ`'s argument,
so the pair is fixed before the challenge is drawn. -/
theorem kappa_recomputed_from_committed_pair {Prior Bytes K : Type*}
    [Field K] {scheme : SecondPhaseSchedule Prior Bytes K}
    (run : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (encode : K → Bytes) (claim : K)
    (habsorbed : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run slice))
    (hpos_claim : DeployedInactiveClaimAtWireOffset slice encode claim) :
    run.kappa = scheme.kappaOf run.prior
      (slice v5TerminalTripleOffset v5InactiveClaimOffset)
      (encode claim) := by
  rw [DeployedInactiveClaimAtWireOffset] at hpos_claim
  rw [run.kappa_eq, claimLabelSlot_eq_of_absorbed run slice habsorbed,
    secondPhaseClaimLabelSlot_eq_of_absorbed run slice habsorbed,
    hpos_claim]

/-! ## 4. Cross-run ordering theorems -/

/-- **Replays agree.**  Two accepted runs with the same committed prior
over the same wire have the same `γ` and the same `κ`: both challenges are
values of the schedule on the committed data, identified through the
recomputation equations and both runs' ordering premises.  Mirror of
`AspisV5SumcheckTranscriptBinding.eta_fixed_by_committed_prefix`. -/
theorem secondPhase_challenges_fixed_by_committed_wire
    {Prior Bytes K : Type*} {scheme : SecondPhaseSchedule Prior Bytes K}
    (run₁ run₂ : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (hprior : run₁.prior = run₂.prior)
    (habsorbed₁ : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run₁ slice))
    (habsorbed₂ : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run₂ slice)) :
    run₁.gamma = run₂.gamma ∧ run₁.kappa = run₂.kappa := by
  refine ⟨?_, ?_⟩
  · rw [gamma_recomputed_from_committed_wire run₁ slice habsorbed₁,
      gamma_recomputed_from_committed_wire run₂ slice habsorbed₂, hprior]
  · rw [run₁.kappa_eq, run₂.kappa_eq,
      claimLabelSlot_eq_of_absorbed run₁ slice habsorbed₁,
      claimLabelSlot_eq_of_absorbed run₂ slice habsorbed₂,
      secondPhaseClaimLabelSlot_eq_of_absorbed run₁ slice habsorbed₁,
      secondPhaseClaimLabelSlot_eq_of_absorbed run₂ slice habsorbed₂,
      hprior]

/-- **The committed span fixes the masked terminal value.**  Two wires that
agree on the span `[5831, 5847)` carry the same masked terminal, because
the span is the injective encoding of the value.  Injectivity is derived
from the codec round trip, not assumed. -/
theorem maskedTerminal_fixed_by_committed_span {K Bytes : Type*} [Field K]
    (slice₁ slice₂ : ℕ → ℕ → Bytes) (encode : K → Bytes)
    (decode : Bytes → Option K)
    (hcodec : DeployedQM31CodecRoundTrip encode decode) (t₁ t₂ : K)
    (hpos₁ : DeployedMaskedTerminalAtWireOffset slice₁ encode t₁)
    (hpos₂ : DeployedMaskedTerminalAtWireOffset slice₂ encode t₂)
    (hspan : slice₁ v5MaskedTerminalOffset v5InactiveClaimOffset
      = slice₂ v5MaskedTerminalOffset v5InactiveClaimOffset) :
    t₁ = t₂ := by
  rw [DeployedMaskedTerminalAtWireOffset] at hpos₁ hpos₂
  exact encode_injective_of_codec_roundTrip hcodec
    (hpos₁.symm.trans (hspan.trans hpos₂))

/-- **The committed span fixes the carried inactive claim.**  Two wires
that agree on the span `[5847, 5863)` carry the same inactive claim.  With
`kappa_recomputed_from_committed_pair` this closes the loop: the committed
span determines the claim value, and the claim value's encoding is inside
`κ`'s argument. -/
theorem carriedClaim_fixed_by_committed_span {K Bytes : Type*} [Field K]
    (slice₁ slice₂ : ℕ → ℕ → Bytes) (encode : K → Bytes)
    (decode : Bytes → Option K)
    (hcodec : DeployedQM31CodecRoundTrip encode decode) (claim₁ claim₂ : K)
    (hpos₁ : DeployedInactiveClaimAtWireOffset slice₁ encode claim₁)
    (hpos₂ : DeployedInactiveClaimAtWireOffset slice₂ encode claim₂)
    (hspan : slice₁ v5InactiveClaimOffset v5ReservedOffset
      = slice₂ v5InactiveClaimOffset v5ReservedOffset) :
    claim₁ = claim₂ := by
  rw [DeployedInactiveClaimAtWireOffset] at hpos₁ hpos₂
  exact encode_injective_of_codec_roundTrip hcodec
    (hpos₁.symm.trans (hspan.trans hpos₂))

/-! ## 5. The composed deployment wrapper

The algebraic distribution theorem and the computational Fiat-Shamir
interface, composed without conflation.  The hiding conjunct is proved by
`deployed_joint_hiding_of_binary_mask` from the algebraic premises alone —
no schedule, run, slicer or absorb predicate enters its proof.  The
ordering conjuncts are proved from the transcript premises alone — no
distribution fact enters theirs. -/

/-- **Deployment wrapper for the Component-B joint pair.**  Under

* the algebraic premises — binary mask, residual freshness, restricted
  surjectivity, and two witnesses of the terminal value `t` — the joint
  released triple has a witness-independent law (conjunct 1, proved by the
  algebraic theorem `deployed_joint_hiding_of_binary_mask`); and
* the computational Fiat-Shamir premises — the ordering premise
  `DeployedJointPairAbsorbedPreChallenge`, the codec round trip and the two
  position premises — the recorded challenges of an accepted run are
  deterministic functions of the committed prefix with the encoded pair
  inside their arguments, and the committed spans decode to exactly the
  pair `(t, claim)` (conjuncts 2-5).

The two halves share only the field `K` and the pair values; neither
conjunct's proof consumes the other's hypotheses. -/
theorem deployed_joint_hiding_with_transcript_ordering
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Prior Bytes : Type*} {scheme : SecondPhaseSchedule Prior Bytes K}
    (point : Round → K) (scale : K)
    (inactive : (Row → K) →ₗ[K] K) (released : (Row → K) →ₗ[K] V)
    (hmask : DeployedInactiveCovectorIsUnitAtPivotRow inactive)
    (hfresh : DeployedResidualViewFreshAtPivotRow released)
    (hrel : Function.Surjective (released ∘ₗ
      (LinearMap.ker (terminalDotFunctional point scale)).subtype))
    (t : K) (m₁ m₂ : Row → K)
    (h₁ : terminalDotFunctional point scale m₁ = t)
    (h₂ : terminalDotFunctional point scale m₂ = t)
    (run : AcceptedSecondPhaseRun scheme) (slice : ℕ → ℕ → Bytes)
    (encode : K → Bytes) (decode : Bytes → Option K) (claim : K)
    (habsorbed : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot run slice))
    (hcodec : DeployedQM31CodecRoundTrip encode decode)
    (hpos_t : DeployedMaskedTerminalAtWireOffset slice encode t)
    (hpos_claim : DeployedInactiveClaimAtWireOffset slice encode claim) :
    ((PMF.uniformOfFintype
          (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (m₁ + (u : Row → K)),
            inactive (m₁ + (u : Row → K)),
            released (m₁ + (u : Row → K))))
      = (PMF.uniformOfFintype
          (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale (m₂ + (u : Row → K)),
            inactive (m₂ + (u : Row → K)),
            released (m₂ + (u : Row → K)))))
      ∧ run.gamma = scheme.gammaOf run.prior
          (slice v5TerminalTripleOffset v5InactiveClaimOffset)
      ∧ run.kappa = scheme.kappaOf run.prior
          (slice v5TerminalTripleOffset v5InactiveClaimOffset)
          (encode claim)
      ∧ decode (slice v5MaskedTerminalOffset v5InactiveClaimOffset)
          = some t
      ∧ decode (slice v5InactiveClaimOffset v5ReservedOffset)
          = some claim := by
  refine ⟨deployed_joint_hiding_of_binary_mask point scale inactive
      released hmask hfresh hrel t m₁ m₂ h₁ h₂,
    gamma_recomputed_from_committed_wire run slice habsorbed,
    kappa_recomputed_from_committed_pair run slice encode claim habsorbed
      hpos_claim, ?_, ?_⟩
  · rw [DeployedMaskedTerminalAtWireOffset] at hpos_t
    rw [hpos_t]
    exact hcodec t
  · rw [DeployedInactiveClaimAtWireOffset] at hpos_claim
    rw [hpos_claim]
    exact hcodec claim

/-! ## 6. Composition with the first-phase transcript model

The second phase sits after the `η`-and-rounds phase of
`V5SumcheckTranscriptBinding`.  The prior of a second-phase run is abstract
there; here two containment maps expose the first-phase committed data
inside it, and one committed-data equality fixes every challenge of the
full schedule at once. -/

/-- **Full-schedule determinism.**  If the second-phase priors contain the
first-phase committed transcripts and messages (via `preEtaOf` and
`messagesOf`), then one equality of committed second-phase priors — with
both runs' ordering premises over one wire — fixes `η` (through
`eta_fixed_by_committed_prefix`), the full ten-round evaluation point
(through `point_fixed_by_committed_prefix_and_messages`), and both
second-phase challenges. -/
theorem full_transcript_challenges_fixed_by_committed_data
    {Public Root K Prior Bytes : Type*} [Field K]
    {scheme₁ : FiatShamirSchedule Public Root K}
    {scheme₂ : SecondPhaseSchedule Prior Bytes K}
    (preEtaOf : Prior → PreEtaTranscript Public Root)
    (messagesOf : Prior → Fin roundCount → Degree27RoundMessage K)
    (first₁ first₂ : AcceptedRun scheme₁)
    (second₁ second₂ : AcceptedSecondPhaseRun scheme₂)
    (slice : ℕ → ℕ → Bytes)
    (hpre₁ : preEtaOf second₁.prior = first₁.preEta)
    (hpre₂ : preEtaOf second₂.prior = first₂.preEta)
    (hmsg₁ : messagesOf second₁.prior = first₁.messages)
    (hmsg₂ : messagesOf second₂.prior = first₂.messages)
    (habsorbed₁ : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot second₁ slice))
    (habsorbed₂ : DeployedJointPairAbsorbedPreChallenge slice
      (absorbedAtDesignatedSlot second₂ slice))
    (hprior : second₁.prior = second₂.prior) :
    first₁.eta = first₂.eta ∧ first₁.point = first₂.point ∧
      second₁.gamma = second₂.gamma ∧ second₁.kappa = second₂.kappa := by
  have hpreEta : first₁.preEta = first₂.preEta := by
    rw [← hpre₁, ← hpre₂, hprior]
  have hmessages : first₁.messages = first₂.messages := by
    rw [← hmsg₁, ← hmsg₂, hprior]
  obtain ⟨hgamma, hkappa⟩ := secondPhase_challenges_fixed_by_committed_wire
    second₁ second₂ slice hprior habsorbed₁ habsorbed₂
  exact ⟨eta_fixed_by_committed_prefix first₁ first₂ hpreEta,
    point_fixed_by_committed_prefix_and_messages first₁ first₂ hpreEta
      hmessages, hgamma, hkappa⟩

/-! ## 7. Named obligation outside the symbolic model -/

/-- Correspondence obligation, not proved: the deployed Rust derives `γ` by
hashing the serialised prior transcript followed by the `label::CLAIM` span
and `κ` from those bytes followed by the `label::SECOND_PHASE_CLAIM` span,
in that order, matching the modelled schedule functions
(`v5_cu_probe.rs:880-894`).  Discharging it requires inspecting the Rust
absorb sequence; nothing in this module depends on it.  It marks, together
with the hash assumptions of `V5SumcheckTranscriptBinding`, where the
symbolic model ends. -/
def RustSecondPhaseChallengeCorrespondence {Prior Bytes K : Type*}
    (scheme : SecondPhaseSchedule Prior Bytes K)
    (serialisePrior : Prior → List UInt8)
    (serialiseSpan : Bytes → List UInt8)
    (rustGammaOfBytes rustKappaOfBytes : List UInt8 → K) : Prop :=
  ∀ (prior : Prior) (tripleSpan claimSpan : Bytes),
    rustGammaOfBytes
        (serialisePrior prior ++ serialiseSpan tripleSpan) =
      scheme.gammaOf prior tripleSpan ∧
    rustKappaOfBytes
        (serialisePrior prior ++ serialiseSpan tripleSpan ++
          serialiseSpan claimSpan) =
      scheme.kappaOf prior tripleSpan claimSpan

/-! ## 8. Non-vacuity

The hypothesis bundles are instantiated at named concrete witnesses: the
wire `witnessSlice` (shared with the layout of
`serialization_interface_nonvacuous`) and the run `witnessRun` whose
committed slots are that wire's designated spans.  The ordering bundle
holds at them for every schedule and prior, the full wrapper bundle holds
jointly with the algebraic premises at the real transcribed terminal
covector, and the wrapper's conclusion holds at the two genuinely different
witnesses of `deployed_capstone_nonvacuous`. -/

/-- The concrete non-vacuity wire, the layout of
`serialization_interface_nonvacuous`: the encoded masked terminal at the
masked-terminal offset, the encoded claim at every other span. -/
def witnessSlice {K : Type*} (t claim : K) : ℕ → ℕ → Option K :=
  fun start _ =>
    if start = v5MaskedTerminalOffset then some t else some claim

/-- The concrete accepted run over the witness wire: its committed slots
are the wire's two designated spans and its challenges are the schedule's
values on them, so both recomputation equations hold by `rfl`. -/
def witnessRun {K Prior : Type*}
    (scheme : SecondPhaseSchedule Prior (Option K) K) (prior : Prior)
    (t claim : K) : AcceptedSecondPhaseRun scheme where
  prior := prior
  claimLabelSlot :=
    witnessSlice t claim v5TerminalTripleOffset v5InactiveClaimOffset
  secondPhaseClaimLabelSlot :=
    witnessSlice t claim v5InactiveClaimOffset v5ReservedOffset
  gamma := scheme.gammaOf prior
    (witnessSlice t claim v5TerminalTripleOffset v5InactiveClaimOffset)
  kappa := scheme.kappaOf prior
    (witnessSlice t claim v5TerminalTripleOffset v5InactiveClaimOffset)
    (witnessSlice t claim v5InactiveClaimOffset v5ReservedOffset)
  gamma_eq := rfl
  kappa_eq := rfl

/-- The ordering premise is satisfiable: the witness run absorbs the
witness wire's designated spans at their designated slots. -/
theorem witnessRun_absorbed {K Prior : Type*}
    (scheme : SecondPhaseSchedule Prior (Option K) K) (prior : Prior)
    (t claim : K) :
    DeployedJointPairAbsorbedPreChallenge (witnessSlice t claim)
      (absorbedAtDesignatedSlot (witnessRun scheme prior t claim)
        (witnessSlice t claim)) :=
  ⟨⟨fun _ => rfl, fun h => h.symm⟩, ⟨fun h => h.symm, fun _ => rfl⟩⟩

/-- The masked-terminal position premise holds on the witness wire. -/
theorem witnessSlice_maskedTerminal {K : Type*} [Field K] (t claim : K) :
    DeployedMaskedTerminalAtWireOffset (witnessSlice t claim) some t := by
  rw [DeployedMaskedTerminalAtWireOffset]
  exact if_pos rfl

/-- The inactive-claim position premise holds on the witness wire. -/
theorem witnessSlice_inactiveClaim {K : Type*} [Field K] (t claim : K) :
    DeployedInactiveClaimAtWireOffset (witnessSlice t claim) some
      claim := by
  rw [DeployedInactiveClaimAtWireOffset]
  exact if_neg (by decide)

/-- The ordering premise, the codec premise and both position premises hold
jointly at the witness run over the witness wire, for every schedule and
prior. -/
theorem transcript_ordering_bundle_instantiable {K Prior : Type*} [Field K]
    (scheme : SecondPhaseSchedule Prior (Option K) K) (prior : Prior)
    (t claim : K) :
    DeployedJointPairAbsorbedPreChallenge (witnessSlice t claim)
        (absorbedAtDesignatedSlot (witnessRun scheme prior t claim)
          (witnessSlice t claim)) ∧
      DeployedQM31CodecRoundTrip (some : K → Option K) id ∧
        DeployedMaskedTerminalAtWireOffset (witnessSlice t claim) some t ∧
          DeployedInactiveClaimAtWireOffset (witnessSlice t claim) some
            claim :=
  ⟨witnessRun_absorbed scheme prior t claim, fun _ => rfl,
    witnessSlice_maskedTerminal t claim,
    witnessSlice_inactiveClaim t claim⟩

/-- **The whole wrapper hypothesis bundle is satisfiable at the real
terminal covector**: the algebraic bundle of
`deployed_hypothesis_bundle_instantiable` (row-993 projection for the mask,
row-994 projection fresh and restrictedly surjective) and the ordering
bundle at the witness run over the witness wire — simultaneously, for
every schedule, prior, `point`, `scale`, `t` and `claim`. -/
theorem deployed_wrapper_bundle_instantiable {K Prior : Type*} [Field K]
    (scheme : SecondPhaseSchedule Prior (Option K) K) (prior : Prior)
    (point : Round → K) (scale t claim : K) :
    DeployedInactiveCovectorIsUnitAtPivotRow
        (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K)
      ∧ DeployedResidualViewFreshAtPivotRow
        (LinearMap.proj padRow : (Row → K) →ₗ[K] K)
      ∧ Function.Surjective
        ((LinearMap.proj padRow : (Row → K) →ₗ[K] K) ∘ₗ
          (LinearMap.ker (terminalDotFunctional point scale)).subtype)
      ∧ DeployedJointPairAbsorbedPreChallenge (witnessSlice t claim)
        (absorbedAtDesignatedSlot (witnessRun scheme prior t claim)
          (witnessSlice t claim))
      ∧ DeployedQM31CodecRoundTrip (some : K → Option K) id
      ∧ DeployedMaskedTerminalAtWireOffset (witnessSlice t claim) some t
      ∧ DeployedInactiveClaimAtWireOffset (witnessSlice t claim) some
          claim :=
  ⟨binary_mask_interface_nonvacuous,
    proj_fresh_at_pivot padRow (by decide),
    proj_padRow_restricted_surjective point scale,
    witnessRun_absorbed scheme prior t claim, fun _ => rfl,
    witnessSlice_maskedTerminal t claim,
    witnessSlice_inactiveClaim t claim⟩

/-- **The wrapper fires.**  At the witness run over the witness wire, with
the two genuinely different terminal-value-`0` witnesses of
`deployed_capstone_nonvacuous` — the zero message and the unit pivot vector
— the composed conclusion holds: the joint law is witness-independent, both
challenges are recomputed from the committed wire, and the committed spans
decode to the pair `(0, claim)`. -/
theorem deployed_wrapper_conclusion_nonvacuous {K Prior : Type*} [Field K]
    [Fintype K] [DecidableEq K]
    (scheme : SecondPhaseSchedule Prior (Option K) K) (prior : Prior)
    (point : Round → K) (scale claim : K) :
    ((PMF.uniformOfFintype
          (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale
              ((0 : Row → K) + (u : Row → K)),
            (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K)
              ((0 : Row → K) + (u : Row → K)),
            (LinearMap.proj padRow : (Row → K) →ₗ[K] K)
              ((0 : Row → K) + (u : Row → K))))
      = (PMF.uniformOfFintype
          (LinearMap.ker (terminalDotFunctional point scale))).map
        (fun u : LinearMap.ker (terminalDotFunctional point scale) =>
          (terminalDotFunctional point scale
              (basis pivotRow 1 + (u : Row → K)),
            (LinearMap.proj pivotRow : (Row → K) →ₗ[K] K)
              (basis pivotRow 1 + (u : Row → K)),
            (LinearMap.proj padRow : (Row → K) →ₗ[K] K)
              (basis pivotRow 1 + (u : Row → K)))))
      ∧ (witnessRun scheme prior 0 claim).gamma
          = scheme.gammaOf (witnessRun scheme prior 0 claim).prior
            (witnessSlice 0 claim v5TerminalTripleOffset
              v5InactiveClaimOffset)
      ∧ (witnessRun scheme prior 0 claim).kappa
          = scheme.kappaOf (witnessRun scheme prior 0 claim).prior
            (witnessSlice 0 claim v5TerminalTripleOffset
              v5InactiveClaimOffset) (some claim)
      ∧ id (witnessSlice 0 claim v5MaskedTerminalOffset
            v5InactiveClaimOffset) = some (0 : K)
      ∧ id (witnessSlice 0 claim v5InactiveClaimOffset v5ReservedOffset)
          = some claim :=
  deployed_joint_hiding_with_transcript_ordering point scale
    (LinearMap.proj pivotRow) (LinearMap.proj padRow)
    binary_mask_interface_nonvacuous
    (proj_fresh_at_pivot padRow (by decide))
    (proj_padRow_restricted_surjective point scale)
    0 (0 : Row → K) (basis pivotRow 1) (map_zero _)
    (terminalDotFunctional_pivot_scaled_eq_zero point scale 1)
    (witnessRun scheme prior 0 claim) (witnessSlice 0 claim) some id claim
    (witnessRun_absorbed scheme prior 0 claim) (fun _ => rfl)
    (witnessSlice_maskedTerminal 0 claim)
    (witnessSlice_inactiveClaim 0 claim)

/-! ## Status ledger

* `DeployedJointPairAbsorbedPreChallenge` — **given semantics and
  consumed**: `absorbedAtDesignatedSlot` is the model reading of its
  predicate parameter; `claimLabelSlot_eq_of_absorbed` and
  `secondPhaseClaimLabelSlot_eq_of_absorbed` extract the two slot
  equations from it, and `gamma_recomputed_from_committed_wire`,
  `kappa_recomputed_from_committed_pair`,
  `secondPhase_challenges_fixed_by_committed_wire` and the wrapper rewrite
  along them.  The instance is a hypothesis of every consuming theorem;
  it is never proved and never built into a definition.
* Algebraic/computational separation — the distribution conjunct of
  `deployed_joint_hiding_with_transcript_ordering` is proved by
  `AspisV5InactiveClaimDeployedCorrespondence.deployed_joint_hiding_of_binary_mask`,
  which predates this module and mentions no transcript object; the
  ordering conjuncts consume no distribution hypothesis.
* Remaining unproved edges feeding this model:
  `DeployedJointPairAbsorbedPreChallenge` itself (per accepted run),
  `DeployedQM31CodecRoundTrip`, `DeployedMaskedTerminalAtWireOffset`,
  `DeployedInactiveClaimAtWireOffset` (all named in
  `V5InactiveClaimDeployedCorrespondence`), the schedule correspondence
  `RustSecondPhaseChallengeCorrespondence` named here, and the hash-game
  assumptions already named in `V5SumcheckTranscriptBinding`.  The
  Question 2 freshness premise `DeployedResidualViewFreshAtPivotRow`
  remains open exactly as recorded there.
-/

end AspisV5InactiveClaimDeployedTranscriptOrdering

#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.SecondPhaseSchedule
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.AcceptedSecondPhaseRun
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.absorbedAtDesignatedSlot
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.claimLabelSlot_eq_of_absorbed
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.secondPhaseClaimLabelSlot_eq_of_absorbed
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.gamma_recomputed_from_committed_wire
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.kappa_recomputed_from_committed_pair
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.secondPhase_challenges_fixed_by_committed_wire
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.maskedTerminal_fixed_by_committed_span
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.carriedClaim_fixed_by_committed_span
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.deployed_joint_hiding_with_transcript_ordering
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.full_transcript_challenges_fixed_by_committed_data
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.RustSecondPhaseChallengeCorrespondence
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.witnessSlice
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.witnessRun
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.witnessRun_absorbed
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.witnessSlice_maskedTerminal
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.witnessSlice_inactiveClaim
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.transcript_ordering_bundle_instantiable
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.deployed_wrapper_bundle_instantiable
#print axioms AspisV5InactiveClaimDeployedTranscriptOrdering.deployed_wrapper_conclusion_nonvacuous
