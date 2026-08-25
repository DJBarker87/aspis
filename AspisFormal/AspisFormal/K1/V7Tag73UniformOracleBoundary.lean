import AspisFormal.K1.V7Tag73AdaptiveLazyOracle

/-!
# The uniform-oracle boundary for Tag 73

This file makes two boundaries explicit.

First, the arbitrary finite law stored in `ObservedProofExperiment` cannot by
itself imply any nontrivial random-oracle bound.  We construct a one-point
experiment whose transcript-coupling-abort event has probability one.  Thus a
uniform-ROM conclusion must come from a concrete construction of the
experiment law, not from the experiment record alone.

Second, for an explicit uniform tape of `Q` fresh 256-bit answers, we combine
the causal target families into one target cap at exposure `i`:

* one unqueried transcript-driving prediction target;
* `i` targets for equality with a previously exposed full 256-bit answer;
* `P` forward-reference or programming-conflict targets; and
* at most `1088` targets from the complete q16 cloned forest.

The resulting coefficient is proved, rather than postulated, to be

`Q + choose(Q, 2) + P * Q + 1088 * Q`.

This is not a K1.6 closure theorem.  The remaining protocol-specific task is
to inject every failure of the exact deployed Tag-73 trace coupling into the
corresponding causal target tree while preserving the uniform fresh-answer
law.  The transparent proposition spelling out that obligation appears at
the end of this file and is not assumed by any theorem here.  Fixed-instance
binding and strict-resource failures must be eliminated deterministically;
208-bit typed Merkle-node binding remains in K1.2 and is not charged to this
full-256-bit coefficient.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73UniformOracleBoundary

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73AdaptiveLazyOracle

noncomputable section

/-! ## An arbitrary observed-proof law gives no ROM bound -/

/-- The raw transcript-coupling-abort event already present in an observed
proof experiment. -/
def TranscriptCouplingAbortEvent
    {Sample RandomTape Statement Proof Witness : Type*}
    [Fintype Sample] [MeasurableSpace Sample]
    (experiment :
      ObservedProofExperiment Sample RandomTape Statement Proof Witness) :
    Set Sample :=
  {sample | (experiment.outcome sample).transcriptCouplingAbort = true}

private def unitTag73Context : Context where
  programId := zeroBytes 32
  releaseBinding := zeroBytes 32
  statementDigest := zeroBytes 32
  attemptId := zeroBytes 32

private def unitPublicProof : PublicProof PUnit PUnit where
  publicInstance :=
    { context := unitTag73Context
      statement := PUnit.unit }
  proof := PUnit.unit

private def zeroResourceUse : ResourceUse where
  adversaryOracleCalls := 0
  simulatorOracleCalls := 0
  verifierOracleCalls := 0
  extractorOracleCalls := 0
  freshOracleAnswers := 0
  programmedPoints := 0
  simulatedProofs := 0
  restartCount := 0
  runtimeSteps := 0
  batchGrindingQueries := 0
  foldGrindingQueries := 0
  finalGrindingQueries := 0
  queryCandidateBranches := 0

private def zeroResourceBudget : ResourceBudget where
  adversaryOracleCalls := 0
  simulatorOracleCalls := 0
  verifierOracleCalls := 0
  extractorOracleCalls := 0
  freshOracleAnswers := 0
  programmedPoints := 0
  simulatedProofs := 0
  restartCount := 0
  runtimeSteps := 0
  batchGrindingQueries := 0
  foldGrindingQueries := 0
  finalGrindingQueries := 0
  queryCandidateBranches := 0

private def alwaysCouplingBadOutcome :
    ExperimentOutcome PUnit PUnit PUnit PUnit where
  simulations := []
  programmingAbort := none
  firstRun :=
    { tapeIdentity := PUnit.unit
      forgery := some unitPublicProof
      stateAtAdversaryHalt := emptyOracle }
  verifierAccepted := true
  extraction :=
    { output := none
      abort := none
      use := zeroResourceUse }
  use := zeroResourceUse
  weakUniqueResponseBad := false
  transcriptCouplingAbort := true

/-- A concrete point-mass experiment witnessing the arbitrary-law no-go. -/
def pointMassAlwaysCouplingBadExperiment :
    ObservedProofExperiment PUnit PUnit PUnit PUnit PUnit where
  law := PMF.pure PUnit.unit
  outcome := fun _ => alwaysCouplingBadOutcome
  relation := fun _ _ => False
  budget := zeroResourceBudget

theorem point_mass_coupling_abort_event_eq_univ :
    TranscriptCouplingAbortEvent pointMassAlwaysCouplingBadExperiment =
      Set.univ := by
  ext sample
  cases sample
  simp [TranscriptCouplingAbortEvent, pointMassAlwaysCouplingBadExperiment,
    alwaysCouplingBadOutcome]

/-- The counterexample's bad event has probability exactly one. -/
theorem point_mass_coupling_abort_probability_one :
    pointMassAlwaysCouplingBadExperiment.law.toOuterMeasure
        (TranscriptCouplingAbortEvent pointMassAlwaysCouplingBadExperiment) =
      1 := by
  rw [point_mass_coupling_abort_event_eq_univ]
  change (PMF.pure PUnit.unit).toOuterMeasure (Set.univ : Set PUnit) = 1
  rw [PMF.toOuterMeasure_pure_apply]
  simp

/-- No constant strictly below one can universally bound transcript coupling
abort for all values of the arbitrary `ObservedProofExperiment.law` field. -/
theorem arbitrary_observed_law_has_no_nontrivial_coupling_bound
    (bound : ENNReal) (nontrivial : bound < 1) :
    ¬ (∀ experiment :
        ObservedProofExperiment PUnit PUnit PUnit PUnit PUnit,
      experiment.law.toOuterMeasure
          (TranscriptCouplingAbortEvent experiment) ≤ bound) := by
  intro universalBound
  have pointBound := universalBound pointMassAlwaysCouplingBadExperiment
  rw [point_mass_coupling_abort_probability_one] at pointBound
  exact (not_le_of_gt nontrivial) pointBound

/-! ## One exact target-slot family per fresh exposure -/

/-- Operational classes of full-256-bit targets at one causal exposure.
The sum type makes their cardinality disjoint by construction; it does not
claim that the deployed trace failures have already been injected into these
slots. -/
abbrev OperationalTargetSlot (prior programmedPoints : Nat) :=
  PUnit ⊕ (Fin prior ⊕ (Fin programmedPoints ⊕ Fin 1088))

theorem operational_target_slot_card_exact
    (prior programmedPoints : Nat) :
    Fintype.card (OperationalTargetSlot prior programmedPoints) =
      1 + prior + programmedPoints + 1088 := by
  simp [OperationalTargetSlot]
  omega

/-- At exposure `prior`, the causal target cap is
`1 + prior + programmedPoints + 1088`. -/
def tag73PerExposureTargetCaps
    (freshExposures programmedPoints : Nat) : List Nat :=
  (List.range' 0 freshExposures).map fun prior =>
    1 + prior + programmedPoints + 1088

theorem tag73_per_exposure_target_caps_length
    (freshExposures programmedPoints : Nat) :
    (tag73PerExposureTargetCaps freshExposures programmedPoints).length =
      freshExposures := by
  simp [tag73PerExposureTargetCaps]

private theorem sum_operational_target_caps
    (indices : List Nat) (programmedPoints : Nat) :
    (indices.map fun prior =>
        1 + prior + programmedPoints + 1088).sum =
      indices.sum + indices.length * (1 + programmedPoints + 1088) := by
  induction indices with
  | nil => simp
  | cons prior indices ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

/-- The exact coefficient obtained by summing all causal target caps. -/
def tag73UniformTargetCoefficient
    (freshExposures programmedPoints : Nat) : Nat :=
  freshExposures + freshExposures.choose 2 +
    programmedPoints * freshExposures + 1088 * freshExposures

/-- Literal target-cap arithmetic.  In particular, the q16 and programming
terms are rectangular target counts, while collisions contribute exactly one
target for each prior fresh answer. -/
theorem tag73_per_exposure_target_caps_sum_exact
    (freshExposures programmedPoints : Nat) :
    (tag73PerExposureTargetCaps freshExposures programmedPoints).sum =
      tag73UniformTargetCoefficient freshExposures programmedPoints := by
  unfold tag73PerExposureTargetCaps
  rw [sum_operational_target_caps]
  rw [collision_caps_sum_exact]
  simp only [List.length_range']
  unfold tag73UniformTargetCoefficient
  ring

/-! ## Uniform-tape corollaries -/

/-- Counting form of the combined adaptive target theorem.  The concrete tree
chooses each target set only from the answers exposed earlier on that path. -/
theorem tag73_uniform_target_tree_hit_count_le
    (freshExposures programmedPoints : Nat)
    (tree : CausalTargetTree Digest256
      (tag73PerExposureTargetCaps freshExposures programmedPoints)) :
    causalHitCount tree ≤
      tag73UniformTargetCoefficient freshExposures programmedPoints *
        (2 ^ 256) ^ (freshExposures - 1) := by
  have bound := causal_hit_count_le_target_caps tree
  rw [AspisK1.V7FsStateRestorationCoupling.deployed_digest_256_cardinality,
    tag73_per_exposure_target_caps_sum_exact,
    tag73_per_exposure_target_caps_length] at bound
  exact bound

/-- Exact-count probability form under the explicit uniform fresh-answer
tape.  For positive `freshExposures`, the right side cancels algebraically to
`tag73UniformTargetCoefficient freshExposures programmedPoints / 2^256`;
this form also states the zero-exposure case without a side condition. -/
theorem tag73_uniform_target_tree_probability_le_exact_count
    (freshExposures programmedPoints : Nat)
    (tree : CausalTargetTree Digest256
      (tag73PerExposureTargetCaps freshExposures programmedPoints)) :
    (uniformDigestFreshTape
        (tag73PerExposureTargetCaps freshExposures programmedPoints).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((tag73UniformTargetCoefficient freshExposures programmedPoints *
          (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ freshExposures) := by
  have bound := uniform_digest_causal_hit_probability_le_exact_count tree
  calc
    (uniformDigestFreshTape
        (tag73PerExposureTargetCaps freshExposures programmedPoints).length).toOuterMeasure
          (causalHitEvent tree) ≤
        ((((tag73PerExposureTargetCaps freshExposures programmedPoints).sum *
            (2 ^ 256) ^
              ((tag73PerExposureTargetCaps freshExposures programmedPoints).length - 1) :
              Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^
            (tag73PerExposureTargetCaps freshExposures programmedPoints).length)) := bound
    _ = ((tag73UniformTargetCoefficient freshExposures programmedPoints *
            (2 ^ 256) ^ (freshExposures - 1) : Nat) : ENNReal) /
          (((2 : ENNReal) ^ 256) ^ freshExposures) := by
      rw [tag73_per_exposure_target_caps_sum_exact,
        tag73_per_exposure_target_caps_length]

/-- Resource-envelope specialization.  The envelope supplies only the strict
numbers `Q` and `P`; it does not supply or assume the causal tree. -/
theorem strict_envelope_uniform_target_tree_hit_count_le
    (envelope : StrictTag73ResourceEnvelope)
    (tree : CausalTargetTree Digest256
      (tag73PerExposureTargetCaps envelope.full256FreshExposures
        envelope.programmedPoints)) :
    causalHitCount tree ≤
      tag73UniformTargetCoefficient envelope.full256FreshExposures
          envelope.programmedPoints *
        (2 ^ 256) ^ (envelope.full256FreshExposures - 1) :=
  tag73_uniform_target_tree_hit_count_le _ _ tree

theorem strict_envelope_uniform_target_tree_probability_le_exact_count
    (envelope : StrictTag73ResourceEnvelope)
    (tree : CausalTargetTree Digest256
      (tag73PerExposureTargetCaps envelope.full256FreshExposures
        envelope.programmedPoints)) :
    (uniformDigestFreshTape
        (tag73PerExposureTargetCaps envelope.full256FreshExposures
          envelope.programmedPoints).length).toOuterMeasure
        (causalHitEvent tree) ≤
      ((tag73UniformTargetCoefficient envelope.full256FreshExposures
            envelope.programmedPoints *
          (2 ^ 256) ^ (envelope.full256FreshExposures - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ envelope.full256FreshExposures) :=
  tag73_uniform_target_tree_probability_le_exact_count _ _ tree

/-! ## Exact remaining operational obligation -/

/-- Transparent statement of the remaining protocol-specific injection.  An
exact Tag-73 coupling-failure sample must be encoded as its `Q` fresh full
256-bit answers and must hit the causal tree constructed from the actual
machine history.  A future operational theorem must prove this subset; this
file neither assumes it in a structure nor uses it as a theorem premise.

The operational proof must classify a hit into the singleton prediction,
prior-answer collision, one of the `P` forward/programming points, or one of
the `1088` q16-forest slots.  Fixed context/attempt/proof-account binding and
strict timeout/resource failures are deterministic side conditions, not
random-oracle targets.  Typed 208-bit Merkle-node collisions are excluded. -/
def ProtocolFailureCoveredByCausalTargets
    {Sample : Type*} {freshExposures programmedPoints : Nat}
    (protocolFailure : Set Sample)
    (freshAnswerEncoding :
      Sample → FreshAnswerTape Digest256
        (tag73PerExposureTargetCaps freshExposures programmedPoints).length)
    (tree : CausalTargetTree Digest256
      (tag73PerExposureTargetCaps freshExposures programmedPoints)) : Prop :=
  protocolFailure ⊆ freshAnswerEncoding ⁻¹' causalHitEvent tree

#print axioms point_mass_coupling_abort_event_eq_univ
#print axioms point_mass_coupling_abort_probability_one
#print axioms arbitrary_observed_law_has_no_nontrivial_coupling_bound
#print axioms operational_target_slot_card_exact
#print axioms tag73_per_exposure_target_caps_length
#print axioms tag73_per_exposure_target_caps_sum_exact
#print axioms tag73_uniform_target_tree_hit_count_le
#print axioms tag73_uniform_target_tree_probability_le_exact_count
#print axioms strict_envelope_uniform_target_tree_hit_count_le
#print axioms strict_envelope_uniform_target_tree_probability_le_exact_count

end

end AspisK1.V7Tag73UniformOracleBoundary
