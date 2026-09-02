import AspisFormal.K1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization

/-!
# Cutoff-20 final-nonce publication bridge

The audit prover may withhold an otherwise work-valid Tag-73 proof unless its
ordinary first-cap-203 q16 scan selects a counter at most twenty and every
candidate through that selected counter uses the minimum sixteen raw draws.
The verifier is unchanged: a published proof is still accepted through the
ordinary sixty-four-candidate scan.

This file models that exact publication predicate and connects it to the
existing lazy-ROM/final-work trial accounting.  The decisive observation is
set-theoretic, not an additional independence claim.  The exact compiler
theorem already covers arbitrary adaptive selection among all genuine
work-qualified final-nonce/q16 trials.  Intersecting its bad event with any
off-chain publication predicate can only shrink the event.  Consequently the
cutoff and minimum-draw tests do not spend another soundness factor and do not
expand the verifier's accepted language.

No claim about proof-generation latency or the probability that an honest
nonce qualifies is made here.  Those are liveness/performance questions, not
soundness premises.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73Cutoff20FinalNoncePublicationBridge

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedCleanWorkDependentQ16Factorization
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Exact audit-prover publication predicate -/

/-- The production cutoff is inclusive: counters `0` through `20` qualify. -/
def finalNonceQ16CounterCutoff : Nat := 20

/-- The minimum-draw path used by the Rust audit selector.  The first sixteen
of the candidate's sixty-four available low-18-bit draws must be pairwise
distinct, so the without-replacement sampler stops after exactly sixteen raw
draws (two SHA-256 squeeze blocks). -/
def UsesMinimumQ16Draws (draws : Q16DrawTape) : Prop :=
  Function.Injective fun index : Fin 16 =>
    draws (Fin.castLE (by decide : 16 <= 64) index)

/-- One ordinary verifier-derived first-cap-203 sample satisfying the exact
off-chain cutoff-20 publication policy.  All candidates which the verifier
will scan, including the selected candidate, must use minimum draws. -/
def Cutoff20Publication
    (sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64) : Prop :=
  sample.2.1.1.val <= finalNonceQ16CounterCutoff /\
    forall counter : Fin 64,
      counter.val <= sample.2.1.1.val ->
        UsesMinimumQ16Draws (sample.2.1.2 counter)

/-- A published sample's selected counter is one of the first twenty-one
ordinary verifier candidates. -/
theorem cutoff20_publication_counter_lt_twenty_one
    (sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64)
    (published : Cutoff20Publication sample) :
    sample.2.1.1.val < 21 := by
  exact Nat.lt_succ_iff.mpr published.1

/-- Every candidate actually scanned by the verifier is on the minimum-draw
path. -/
theorem cutoff20_publication_scanned_candidate_uses_minimum_draws
    (sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64)
    (published : Cutoff20Publication sample)
    (counter : Fin 64)
    (scanned : counter.val <= sample.2.1.1.val) :
    UsesMinimumQ16Draws (sample.2.1.2 counter) := by
  exact published.2 counter scanned

/-- Erasing the publication policy yields byte-for-byte the ordinary
first-cap-203 trace already checked by the unchanged verifier model. -/
theorem cutoff20_publication_is_ordinary_first_cap203
    (sample : FirstAdmittedSample q16CandidateOutput
      SemanticCap203Admitted 64)
    (_published : Cutoff20Publication sample) :
    FirstAdmittedAt q16CandidateOutput SemanticCap203Admitted 64
      sample.1.1 sample.2.1 := by
  exact sample.2.2

/-! ## Arbitrary final-nonce selection remains inside the existing cover -/

/-- A source-level sample is publishable when its decoded ordinary q16 sample
satisfies the exact cutoff-20 predicate.  The decoder may depend on the whole
sample; the proof below does not assume independence between publication and
the lazy random oracle. -/
def Cutoff20PublicationEvent {Sample : Type}
    (decode : Sample -> Option
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64)) :
    Set Sample :=
  {sourceSample | exists q16Sample,
    decode sourceSample = some q16Sample /\ Cutoff20Publication q16Sample}

theorem cutoff20_filtered_event_subset
    {Sample : Type}
    (decode : Sample -> Option
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64))
    (event : Set Sample) :
    Cutoff20PublicationEvent decode ∩ event ⊆ event := by
  exact Set.inter_subset_right

/-- Direct final-nonce bridge: even an arbitrary, whole-transcript-dependent
cutoff-20 publisher cannot enlarge the finite union of genuine work-qualified
q16 failure trials.  The existing exact 34-bit final-work product pays for up
to `2^34` adaptive trials. -/
theorem cutoff20_published_failure_union_probability_le_one_forest
    {HiddenTape Trial : Type}
    [Fintype HiddenTape] [Fintype Trial]
    {hiddenLaw : PMF HiddenTape}
    {parameters : ExactCompilerResourceParameters}
    (trials : ExactCompilerCausalFinalWorkAnswerQ16Trials
      (HiddenTape := HiddenTape) (Trial := Trial) parameters)
    (decode : ExactCompilerSample HiddenTape parameters -> Option
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64))
    (trialCap : Fintype.card Trial <= 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (Cutoff20PublicationEvent decode ∩
          (⋃ trial, trials.event trial)) <= q16SemanticOneForestRawError := by
  calc
    _ <= (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (⋃ trial, trials.event trial) := by
      exact measure_mono Set.inter_subset_right
    _ <= q16SemanticOneForestRawError :=
      trials.failure_union_probability_le_one_forest trialCap

/-! ## Production-facing clean fixed-K1.3 endpoint -/

/-- The exact accepted-source K1.3 q16 event, after applying the audit
publication policy, retains the one-forest semantic bound.  This consumes the
existing operational source cover, causal final-work/q16 routing, exact
34-bit work probability and semantic cap-203 denominator.

The result is deliberately quantified over the publication decoder: no
freshness or independence premise about final-nonce retries is introduced. -/
theorem exact_fixed_clean_cutoff20_published_k13_query_probability_le_one_forest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (publicationDecode : ExactCompilerSample HiddenTape parameters -> Option
      (FirstAdmittedSample q16CandidateOutput SemanticCap203Admitted 64))
    (transitionRoom : 2 <= transitionFuel)
    (programmedCover : 513 <= 2 * parameters.forkRequestCap)
    (source : ExactFixedK13ParsedSourceProvider transitionFuel configuration
      projection fixedInstance)
    (frontierExact : forall
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (invariant : ExactFixedCleanK13ResidualWorkInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (exposureCap : unifiedFull256ExposureCap parameters <= 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (Cutoff20PublicationEvent publicationDecode ∩
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73K13QueryEvent transitionFuel configuration projection
              fixedInstance decoder)) <= q16SemanticOneForestRawError := by
  have semanticBound :=
    exact_fixed_clean_work_dependent_k13_query_probability_le_one_forest
      hiddenLaw transitionRoom programmedCover source frontierExact invariant
      reference traceExists exposureCap
  calc
    _ <= (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73K13QueryEvent transitionFuel configuration projection
            fixedInstance decoder) := by
      exact measure_mono Set.inter_subset_right
    _ <= q16SemanticOneForestRawError := semanticBound

#print axioms cutoff20_publication_counter_lt_twenty_one
#print axioms cutoff20_publication_scanned_candidate_uses_minimum_draws
#print axioms cutoff20_publication_is_ordinary_first_cap203
#print axioms cutoff20_filtered_event_subset
#print axioms cutoff20_published_failure_union_probability_le_one_forest
#print axioms
  exact_fixed_clean_cutoff20_published_k13_query_probability_le_one_forest

end

end AspisK1.V7Tag73Cutoff20FinalNoncePublicationBridge
