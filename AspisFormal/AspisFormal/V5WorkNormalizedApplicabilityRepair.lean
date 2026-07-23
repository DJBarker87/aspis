import AspisFormal.V5NonceWorkAuthentication

/-!
# v5 work-normalized applicability repairs

This module closes two premise-independent arithmetic/accounting defects without
claiming the published S-two/BCS arguments apply to the deployed verifier.

1. The deployed batching challenge is sampled from `F*`, not from all of `F`.
   Consequently the coefficient-18 arithmetic uses `|F| - 1` in the
   denominator.  The corrected expression still has at least 107 bits after
   the deployed 37-bit work factor.
2. Under S-two's convention the initial committed ensemble `m0` is excluded
   from the public-coin IOP round count.  The existing 31-boundary serialized
   ledger decomposes into the C1 root/salt `m0` followed by exactly 30 genuine
   candidate round boundaries, so the corrected numerical count satisfies
   `R <= 32`.

The following remain named premises, rather than conclusions of the arithmetic
in this file:

* the separate-output random-oracle reduction connecting the grinding digest
  to the later nonzero batching challenge;
* virtual combined-oracle and exact circle-code membership;
* Rust-to-Lean sampling, transcript, and ordered-boundary correspondence;
* authenticated public-coin round semantics and conditional round-error bounds;
* computational PCS/Merkle, SHA/random-oracle, and cited BCS/CMS/MCA
  applicability.

The hostile regression theorems record both original defects: replacing
`|F|-1` by `|F|` strictly understates the degree-18 root fraction, and the old
31-element serialization trace is not the S-two `m0`-excluded semantic trace.
-/

namespace AspisV5WorkNormalizedApplicabilityRepair

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint
open AspisV5NonceWorkAuthentication

/-! ## 1. Exact coefficient-18 arithmetic for a challenge uniform on `F*` -/

/-- The width-19 scalar-powers MCA arithmetic for the deployed nonzero batching
challenge.  The degree is `19 - 1 = 18`, and uniform sampling from `F*` gives
the exact denominator `|F| - 1`.  The `2^37` factor is only arithmetic here;
connecting it to the separately hashed grinding predicate remains an explicit
deployment premise below. -/
noncomputable def powersBatchArithmeticFStar (coefficient : ℝ) : ℝ :=
  coefficient * ((21 / 2) / Real.sqrt (1 / 512))
    * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1)
    * 524288 / (FIELD - 1) / 2 ^ 37

/-- Denominator-parametric arithmetic lemma used only to check the corrected
finite constants.  It proves no MCA theorem or deployed-event reduction. -/
private theorem sqrt_event_le_with_denominator
    (coefficient mh rr symbols lowerBound denominator target : ℝ) (work : ℕ)
    (hrr : 0 < rr) (hlower : 0 < lowerBound)
    (hlowerSq : lowerBound ^ 2 ≤ rr) (hdenominator : 0 < denominator)
    (htarget : 0 ≤ target)
    (hfinite :
      coefficient * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols
        ≤ target * (lowerBound * denominator * 2 ^ work)) :
    coefficient * (mh / Real.sqrt rr)
        * ((2 * (mh / Real.sqrt rr) ^ 4 / 3) * rr + 1) * symbols
        / denominator / 2 ^ work ≤ target := by
  set root := Real.sqrt rr with hroot
  have hrootSq : root ^ 2 = rr := Real.sq_sqrt hrr.le
  have hrootPos : 0 < root := Real.sqrt_pos.mpr hrr
  have hlowerRoot : lowerBound ≤ root := by
    nlinarith [sq_nonneg (root - lowerBound)]
  have hrootFourth : root ^ 4 = rr ^ 2 := by
    rw [show root ^ 4 = (root ^ 2) ^ 2 by ring, hrootSq]
  have hratioFourth : (mh / root) ^ 4 = mh ^ 4 / rr ^ 2 := by
    rw [div_pow, hrootFourth]
  have hnumerator :
      coefficient * (mh / root)
          * ((2 * (mh / root) ^ 4 / 3) * rr + 1) * symbols =
        (coefficient * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols) / root := by
    rw [hratioFourth]
    field_simp
  rw [hnumerator]
  set numerator :=
    coefficient * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols
  have hpositiveDenominator : 0 < root * denominator * 2 ^ work :=
    mul_pos (mul_pos hrootPos hdenominator) (by positivity)
  have hreassociate :
      numerator / root / denominator / 2 ^ work =
        numerator / (root * denominator * 2 ^ work) := by
    rw [div_div, div_div]
    ring_nf
  rw [hreassociate, div_le_iff₀ hpositiveDenominator]
  have hdenominatorMonotone :
      lowerBound * denominator * 2 ^ work ≤
        root * denominator * 2 ^ work :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlowerRoot hdenominator.le) (by positivity)
  have htargetMonotone :
      target * (lowerBound * denominator * 2 ^ work) ≤
        target * (root * denominator * 2 ^ work) :=
    mul_le_mul_of_nonneg_left hdenominatorMonotone htarget
  linarith [hfinite, htargetMonotone]

/-- Exact corrected finite arithmetic: coefficient 18, nonzero-field
denominator `|F|-1`, and 37 work bits still give error at most `2^-107`.
This is solely an inequality between the displayed real expressions. -/
theorem width19_fstar_powers_batch_arithmetic_bound :
    powersBatchArithmeticFStar 18 ≤ 1 / 2 ^ 107 := by
  unfold powersBatchArithmeticFStar
  exact sqrt_event_le_with_denominator
    18 (21 / 2) (1 / 512) 524288 (4419417 / 100000000)
    (FIELD - 1) (1 / 2 ^ 107) 37
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by unfold FIELD; norm_num)
    (by norm_num)
    (by unfold FIELD; norm_num)

/-- Regression tooth: using the full-field denominator strictly understates
the degree-18 root fraction for a challenge sampled uniformly from `F*`.
Thus the old `18 / |F|` fraction cannot be substituted definitionally or by a
monotone upper bound for the deployed `18 / (|F|-1)` fraction. -/
theorem full_field_degree18_fraction_strictly_understates_fstar :
    (18 : ℝ) / FIELD < 18 / (FIELD - 1) := by
  have hfield : (0 : ℝ) < FIELD := FIELD_pos
  have hfieldMinusOne : (0 : ℝ) < FIELD - 1 := by
    unfold FIELD
    norm_num
  rw [div_lt_div_iff₀ hfield hfieldMinusOne]
  have hfieldGap : (18 : ℝ) * (FIELD - 1) < 18 * FIELD := by
    nlinarith
  exact hfieldGap

/-- The corrected expression is genuinely different in the adverse direction:
at coefficient 18 the former full-field arithmetic is strictly smaller than
the nonzero-field arithmetic. -/
theorem full_field_width19_arithmetic_strictly_understates_fstar :
    powersBatchArithmetic 18 < powersBatchArithmeticFStar 18 := by
  have hfield : (0 : ℝ) < FIELD := FIELD_pos
  have hfieldMinusOne : (0 : ℝ) < FIELD - 1 := by
    unfold FIELD
    norm_num
  let numerator : ℝ :=
    18 * ((21 / 2) / Real.sqrt (1 / 512))
      * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1)
      * 524288
  have hnumerator : 0 < numerator := by
    dsimp [numerator]
    have hsqrt : (0 : ℝ) < Real.sqrt (1 / 512) :=
      Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hcore : numerator / FIELD < numerator / (FIELD - 1) := by
    rw [div_lt_div_iff₀ hfield hfieldMinusOne]
    nlinarith
  have hwork : (0 : ℝ) < 2 ^ 37 := by positivity
  unfold powersBatchArithmetic powersBatchArithmeticFStar
  change numerator / FIELD / 2 ^ 37 < numerator / (FIELD - 1) / 2 ^ 37
  exact div_lt_div_of_pos_right hcore hwork

/-! ### Named external premises for applying the repaired arithmetic -/

/-- Explicit deployment/published-theorem interface for the corrected `F*`
arithmetic.  Each predicate is supplied independently so no numerical theorem
can manufacture code membership, grinding independence, or executable
correspondence. -/
structure Width19FStarDeploymentPremises {Schedule : Type*}
    (acceptedSchedule : Schedule → Prop)
    (citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (separateGrindingOutputReduction : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualEventProbability : Schedule → ℝ) : Prop where
  acceptedHasCitedMCAHypotheses :
    ∀ schedule, acceptedSchedule schedule → citedMCAHypotheses schedule
  acceptedHasVirtualOracleAndCodeMembership :
    ∀ schedule, acceptedSchedule schedule →
      virtualOracleAndCodeMembership schedule
  acceptedHasSeparateGrindingOutputReduction :
    ∀ schedule, acceptedSchedule schedule →
      separateGrindingOutputReduction schedule
  acceptedHasRustSamplingAndTranscriptCorrespondence :
    ∀ schedule, acceptedSchedule schedule →
      rustSamplingAndTranscriptCorrespondence schedule
  citedCorrectedEventBound :
    ∀ schedule,
      citedMCAHypotheses schedule →
      virtualOracleAndCodeMembership schedule →
      separateGrindingOutputReduction schedule →
      rustSamplingAndTranscriptCorrespondence schedule →
      actualEventProbability schedule ≤ powersBatchArithmeticFStar 18

/-- Conditional application of the repaired number.  All published-theorem,
separate-output grinding, virtual-oracle/code, and Rust correspondence premises
are load-bearing inputs. -/
theorem width19_fstar_event_bound_of_all_named_premises
    {Schedule : Type*}
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (separateGrindingOutputReduction : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualEventProbability : Schedule → ℝ)
    (premises : Width19FStarDeploymentPremises acceptedSchedule
      citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualEventProbability)
    (schedule : Schedule) (accepted : acceptedSchedule schedule) :
    actualEventProbability schedule ≤ 1 / 2 ^ 107 := by
  apply (premises.citedCorrectedEventBound schedule
    (premises.acceptedHasCitedMCAHypotheses schedule accepted)
    (premises.acceptedHasVirtualOracleAndCodeMembership schedule accepted)
    (premises.acceptedHasSeparateGrindingOutputReduction schedule accepted)
    (premises.acceptedHasRustSamplingAndTranscriptCorrespondence schedule accepted)).trans
  exact width19_fstar_powers_batch_arithmetic_bound

/-- Regression tooth: corrected arithmetic alone still cannot produce the
separate grinding-output reduction required to apply its `2^37` factor. -/
theorem corrected_arithmetic_does_not_supply_grinding_output_reduction :
    ∃ (acceptedSchedule separateGrindingOutputReduction : Bool → Prop),
      acceptedSchedule true ∧
        ¬ (∀ schedule, acceptedSchedule schedule →
          separateGrindingOutputReduction schedule) := by
  refine ⟨fun _ => True, fun _ => False, trivial, ?_⟩
  intro supplied
  exact supplied true trivial

/-! ## 2. S-two `m0`-excluded 30-round trace -/

/-- The existing C1 root and public salt form the initial committed ensemble
`m0` in S-two's convention.  They precede the first verifier public coin and
are excluded from the public-coin IOP round count. -/
def stwoInitialEnsembleM0 : V5PublicMessageBoundary :=
  .c1RootAndPublicSalt

/-- Ordered candidate public-coin round boundaries after excluding `m0`.
The four OOD/relation/later-root groups remain interleaved exactly as in the
existing serialized ledger. -/
def intendedV5M0ExcludedRoundTrace : List V5PublicMessageBoundary :=
  [.c2RootAndPublicSalt,
    .maskedInitialClaim,
    .semanticSumcheckRound 0,
    .semanticSumcheckRound 1,
    .semanticSumcheckRound 2,
    .semanticSumcheckRound 3,
    .semanticSumcheckRound 4,
    .semanticSumcheckRound 5,
    .semanticSumcheckRound 6,
    .semanticSumcheckRound 7,
    .semanticSumcheckRound 8,
    .semanticSumcheckRound 9,
    .terminalAndBatchWork,
    .inactiveClaim,
    .oodValue 0 0,
    .oodValue 0 1,
    .relationSumcheckAndFoldWork 0,
    .laterRootAndPublicSalt 0,
    .oodValue 1 0,
    .oodValue 1 1,
    .relationSumcheckAndFoldWork 1,
    .laterRootAndPublicSalt 1,
    .oodValue 2 0,
    .oodValue 2 1,
    .relationSumcheckAndFoldWork 2,
    .laterRootAndPublicSalt 2,
    .oodValue 3 0,
    .oodValue 3 1,
    .relationSumcheckAndFoldWork 3,
    .finalPolynomialAndWork]

/-- The existing 31-boundary serialized ledger decomposes exactly into the
initial ensemble `m0` followed by the corrected public-coin round trace. -/
theorem old_serialized_trace_is_m0_cons_corrected_round_trace :
    intendedV5OrderedBoundaryTrace =
      stwoInitialEnsembleM0 :: intendedV5M0ExcludedRoundTrace := by
  rfl

/-- Exact S-two-convention public-coin IOP round count for the candidate trace. -/
theorem intended_v5_m0_excluded_round_trace_length_is_30 :
    intendedV5M0ExcludedRoundTrace.length = 30 := by
  decide

/-- Removing the initial ensemble from the old serialized trace recovers
exactly the corrected semantic-round trace. -/
theorem old_serialized_trace_tail_is_corrected_round_trace :
    intendedV5OrderedBoundaryTrace.tail = intendedV5M0ExcludedRoundTrace := by
  rfl

/-- Regression tooth: the old 31-boundary serialized trace is not the
S-two-convention `m0`-excluded semantic-round trace. -/
theorem old_31_trace_is_not_m0_excluded_semantic_trace :
    intendedV5OrderedBoundaryTrace ≠ intendedV5M0ExcludedRoundTrace := by
  intro equalTraces
  have equalLengths := congrArg List.length equalTraces
  rw [intended_v5_ordered_boundary_trace_length_is_31,
    intended_v5_m0_excluded_round_trace_length_is_30] at equalLengths
  omega

/-- The corrected concrete round count is below the endpoint's cap 32.  This
does not establish that any boundary has the required public-coin semantics. -/
theorem intended_v5_m0_excluded_round_count_le_32 :
    intendedV5M0ExcludedRoundTrace.length ≤ 32 := by
  rw [intended_v5_m0_excluded_round_trace_length_is_30]
  omega

/-- Exact executable-correspondence seam for the `m0`-excluded ordered trace. -/
def ExactRustV5M0ExcludedRoundTraceCorrespondence {RustBoundary : Type*}
    (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary) : Prop :=
  rustRoundTrace.map decode = intendedV5M0ExcludedRoundTrace

/-- Corrected numerical BCS accounting.  `R` is tied to the decoded list of
post-`m0` public-coin round boundaries, not to the full serialized ledger. -/
def ExactV5M0ExcludedBCSRoundAccounting {RustBoundary : Type*}
    (R : ℝ) (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary) : Prop :=
  ExactRustV5M0ExcludedRoundTraceCorrespondence rustRoundTrace decode ∧
    R = rustRoundTrace.length

/-- Exact corrected accounting pins `R` to 30 and hence proves `R <= R_BCS=32`.
The Rust trace equality remains an explicit correspondence premise. -/
theorem bcs_R_is_30_and_meets_32_of_m0_excluded_accounting
    {RustBoundary : Type*} (R : ℝ) (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (accounting :
      ExactV5M0ExcludedBCSRoundAccounting R rustRoundTrace decode) :
    R = 30 ∧ R ≤ R_BCS := by
  have decodedLength := congrArg List.length accounting.1
  simp only [List.length_map,
    intended_v5_m0_excluded_round_trace_length_is_30] at decodedLength
  have roundCount : R = 30 := by
    rw [accounting.2]
    exact_mod_cast decodedLength
  exact ⟨roundCount, by rw [roundCount]; norm_num [R_BCS]⟩

/-! ### Named external premises for applying the 30-round accounting -/

/-- Full corrected boundary interface.  Exact count and order do not imply
public-coin semantics, conditional round-error coverage, or any computational
assumption.  Those remain separate fields. -/
structure M0ExcludedBCSDeploymentPremises {RustBoundary : Type*}
    (R : ℝ) (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustRoundTrace)
    (rustInitialEnsembleM0Correspondence : Prop)
    (randomOracleAndFiatShamirApplicability : Prop)
    (pcsAndMerkleAuthenticationApplicability : Prop)
    (citedBCSAndCMSApplicability : Prop) : Prop where
  exactM0ExcludedAccounting :
    ExactV5M0ExcludedBCSRoundAccounting R rustRoundTrace decode
  hasRustInitialEnsembleM0Correspondence :
    rustInitialEnsembleM0Correspondence
  genuinePublicCoinRoundSemantics :
    STwoBCSIOPRoundSemanticApplicability R rustRoundTrace semantics
  hasRandomOracleAndFiatShamirApplicability :
    randomOracleAndFiatShamirApplicability
  hasPCSAndMerkleAuthenticationApplicability :
    pcsAndMerkleAuthenticationApplicability
  hasCitedBCSAndCMSApplicability : citedBCSAndCMSApplicability

/-- Conditional projection of the corrected count and every still-open
semantic/computational premise.  No field is discharged by list arithmetic. -/
theorem m0_excluded_boundary_application_preserves_all_named_premises
    {RustBoundary : Type*}
    (R : ℝ) (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustRoundTrace)
    (rustInitialEnsembleM0Correspondence : Prop)
    (randomOracleAndFiatShamirApplicability : Prop)
    (pcsAndMerkleAuthenticationApplicability : Prop)
    (citedBCSAndCMSApplicability : Prop)
    (premises : M0ExcludedBCSDeploymentPremises
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability) :
    R = 30 ∧ R ≤ R_BCS ∧
      STwoBCSIOPRoundSemanticApplicability R rustRoundTrace semantics ∧
      rustInitialEnsembleM0Correspondence ∧
      randomOracleAndFiatShamirApplicability ∧
      pcsAndMerkleAuthenticationApplicability ∧
      citedBCSAndCMSApplicability := by
  rcases bcs_R_is_30_and_meets_32_of_m0_excluded_accounting
    R rustRoundTrace decode premises.exactM0ExcludedAccounting with
    ⟨roundCount, roundBound⟩
  exact ⟨roundCount, roundBound, premises.genuinePublicCoinRoundSemantics,
    premises.hasRustInitialEnsembleM0Correspondence,
    premises.hasRandomOracleAndFiatShamirApplicability,
    premises.hasPCSAndMerkleAuthenticationApplicability,
    premises.hasCitedBCSAndCMSApplicability⟩

/-- Regression tooth: an exact corrected 30-element trace still does not imply
that its first position supplies authenticated public coin, an authenticated
response, or a covered conditional round error. -/
theorem corrected_30_trace_does_not_supply_round_semantics :
    ∃ semantics : STwoBCSIOPRoundSemantics intendedV5M0ExcludedRoundTrace,
      ¬ STwoBCSIOPRoundSemanticApplicability 30
        intendedV5M0ExcludedRoundTrace semantics := by
  let semantics : STwoBCSIOPRoundSemantics intendedV5M0ExcludedRoundTrace :=
    { verifierPublicCoinAfterAuthenticatedPrefix := fun _ => False
      authenticatedProverOracleOrMessageResponse := fun _ => True
      conditionalRoundErrorCovered := fun _ => True
      initialAndFinalTranscriptMaterialAccounted := True }
  refine ⟨semantics, ?_⟩
  intro applicable
  have firstRound := applicable.2.2.2
    (⟨0, by
      rw [intended_v5_m0_excluded_round_trace_length_is_30]
      omega⟩ : Fin intendedV5M0ExcludedRoundTrace.length)
  exact firstRound.1

/-! ## Axiom audit -/

#print axioms width19_fstar_powers_batch_arithmetic_bound
#print axioms full_field_degree18_fraction_strictly_understates_fstar
#print axioms full_field_width19_arithmetic_strictly_understates_fstar
#print axioms width19_fstar_event_bound_of_all_named_premises
#print axioms corrected_arithmetic_does_not_supply_grinding_output_reduction
#print axioms old_serialized_trace_is_m0_cons_corrected_round_trace
#print axioms intended_v5_m0_excluded_round_trace_length_is_30
#print axioms old_serialized_trace_tail_is_corrected_round_trace
#print axioms old_31_trace_is_not_m0_excluded_semantic_trace
#print axioms intended_v5_m0_excluded_round_count_le_32
#print axioms bcs_R_is_30_and_meets_32_of_m0_excluded_accounting
#print axioms m0_excluded_boundary_application_preserves_all_named_premises
#print axioms corrected_30_trace_does_not_supply_round_semantics

end AspisV5WorkNormalizedApplicabilityRepair
