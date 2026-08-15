import AspisFormal.V5ImplementedWorkNormalizedEndpoint

/-!
# Preserve enough numerical margin for a 100-bit work-normalized statement

The maintained endpoint rounds the work-normalized arithmetic directly to
`2^-100`.  That is enough for the interactive core, but leaves no formal room
to add separately stated hash or implementation failure probabilities.

This file keeps a conservative fraction of the actual margin.  It uses the
released width-nineteen coefficient and nonzero-field denominator, the exact
`R = 30` public-coin count, and every other existing ledger term unchanged.
The resulting work-normalized core is at most `0.7 * 2^-100`.  Therefore any
explicit external-event budget of at most `0.3 * 2^-100` can be added while
retaining a complete `2^-100` work-normalized bound.

This is not a `2^-100` bound on the conditional probability of failure after
an attacker has already completed the 37-bit grind.  Removing the work charge
restores a factor `2^37`; the raw completed-attempt calculation is kept
separate in `V5RefinedWidth19DeploymentBridge`.

This is arithmetic only.  The event inclusions, published theorem, random
oracle, and executable correspondence hypotheses remain separate.
-/

namespace AspisV5HundredBitSecurityMargin

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint
open AspisV5ImplementedWorkNormalizedEndpoint
open AspisV5NonceWorkAuthentication
open AspisV5SelectedGoodVerifierRelation
open AspisV5WorkNormalizedApplicabilityRepair
open AspisFormal.V5ExactRuntimeWireRepair

/-! ## Tighter corrected batching term -/

/-- Denominator-parametric version of the maintained square-root arithmetic
lemma, with an arbitrary rational target. -/
private theorem sqrt_event_le_with_denominator
    (coefficient mh rr symbols lowerBound denominator target : ℝ)
    (work : ℕ)
    (hrr : 0 < rr) (hlower : 0 < lowerBound)
    (hlowerSq : lowerBound ^ 2 ≤ rr) (hdenominator : 0 < denominator)
    (htarget : 0 ≤ target)
    (hfinite :
      coefficient * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols ≤
        target * (lowerBound * denominator * 2 ^ work)) :
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
        (coefficient * mh * (2 * mh ^ 4 / (3 * rr) + 1) * symbols) /
          root := by
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

/-- Released coefficient `18`, `K*` denominator, and 37-bit batch work give a
tight rational ceiling used below. -/
theorem corrected_batch_le_2120_div_two_pow_119 :
    powersBatchArithmeticFStar 18 ≤ (2120 : ℝ) / 2 ^ 119 := by
  unfold powersBatchArithmeticFStar
  exact sqrt_event_le_with_denominator
    18 (21 / 2) (1 / 512) 524288 (4419417 / 100000000)
    (FIELD - 1) ((2120 : ℝ) / 2 ^ 119) 37
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by unfold FIELD; norm_num)
    (by norm_num)
    (by unfold FIELD; norm_num)

/-- Removing the 37-bit work charge from the tighter batching ceiling gives
the corresponding raw completed-attempt ceiling. -/
theorem corrected_batch_without_work_le_2120_div_two_pow_82 :
    powersBatchArithmeticFStar 18 * 2 ^ 37 ≤
      (2120 : ℝ) / 2 ^ 82 := by
  have hworkNonnegative : (0 : ℝ) ≤ 2 ^ 37 := by positivity
  calc
    powersBatchArithmeticFStar 18 * 2 ^ 37 ≤
        ((2120 : ℝ) / 2 ^ 119) * 2 ^ 37 :=
      mul_le_mul_of_nonneg_right corrected_batch_le_2120_div_two_pow_119
        hworkNonnegative
    _ = (2120 : ℝ) / 2 ^ 82 := by norm_num

/-- Regression check: the maintained conservative raw width-19 ceiling is not
itself a 100-bit probability bound.  The 100-bit conclusion below is explicitly
work-normalized. -/
theorem raw_width19_reference_ceiling_is_above_two_pow_neg_100 :
    (1 : ℝ) / 2 ^ 100 < 31 / 2 ^ 75 := by
  norm_num

/-! ## Corrected tight union -/

/-- Same tight ledger as `unionBound`, replacing only its legacy width-29
batch ceiling with the deployed width-19 ceiling. -/
noncomputable def correctedTightUnionBound : ℝ :=
  2120 / 2 ^ 119 + 2837 / 2 ^ 121 + 3502 / 2 ^ 123 +
    2260 / 2 ^ 124 + 2288 / 2 ^ 125
    + 1 / 2 ^ 111 + 1 / 2 ^ 213
    + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119 + 1 / 2 ^ 119
    + 1 / 2 ^ 112 + 1 / 2 ^ 111 + 1 / 2 ^ 120 + 1 / 2 ^ 123 +
      1 / 2 ^ 123
    + 1 / 2 ^ 115 + 1 / 2 ^ 124 + 1 / 2 ^ 128

/-- The corrected implemented round ledger is below the tighter union. -/
theorem corrected_round_error_le_tight_union :
    correctedRoundError ≤ correctedTightUnionBound := by
  unfold correctedRoundError exactSixWorkTermTotal noWorkRoundError
    correctedTightUnionBound
  linarith [corrected_batch_le_2120_div_two_pow_119,
    fold0Term_le, fold1Term_le, fold2Term_le, fold3Term_le,
    (show rawTerm ≤ 1 / 2 ^ 111 by unfold rawTerm; exact raw_query_miss),
    (show oodTerm ≤ 1 / 2 ^ 213 by unfold oodTerm; exact ood_list_union),
    sz_relation_mixers, sz_theta, sz_three_point, sz_inactive, sz_tuple,
    sz_poles, sz_zerocheck_eq, sz_zero_sum, sz_nonzero_eta, sz_ten_rounds]

/-! ## Keep 30% of `2^-100` for explicit external assumptions -/

/-- With the exact `R ≤ 30` count, the three-case work-normalized core uses
at most seventy percent of the target `2^-100` budget. -/
theorem corrected_work_normalized_core_le_seven_tenths
    (epsRound R capErr T : ℝ)
    (hround0 : 0 ≤ epsRound)
    (hround : epsRound ≤ correctedTightUnionBound)
    (_hRnn : 0 ≤ R) (hR : R ≤ 30)
    (hcapnn : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    selectorInflation * bcsError epsRound T R capErr ≤
      (7 : ℝ) / (10 * 2 ^ 100) := by
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hRT : R / T ≤ 30 := by
    rw [div_le_iff₀ hTpos]
    nlinarith [hR, hT1]
  have h1T : 1 / T ≤ 1 := by
    rw [div_le_one hTpos]
    exact hT1
  have hcap' : capErr ≤ 1 / 2 ^ 256 := by
    unfold roCapErr at hcap
    exact hcap
  have hA : (1 + R / T) * epsRound ≤
      31 * correctedTightUnionBound := by
    have h1 : (1 + R / T) * epsRound ≤ 31 * epsRound :=
      mul_le_mul_of_nonneg_right (by linarith [hRT]) hround0
    have h2 : 31 * epsRound ≤ 31 * correctedTightUnionBound := by
      linarith [hround]
    linarith [h1, h2]
  have hB : 3 * (T + 1 / T) * capErr ≤
      3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    have hTsum : T + 1 / T ≤ 2 ^ 128 + 1 := by
      linarith [hTmax, h1T]
    have h1 : 3 * (T + 1 / T) * capErr ≤
        3 * (2 ^ 128 + 1) * capErr :=
      mul_le_mul_of_nonneg_right (by linarith [hTsum]) hcapnn
    have h2 : 3 * (2 ^ 128 + 1) * capErr ≤
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) :=
      mul_le_mul_of_nonneg_left hcap' (by positivity)
    linarith [h1, h2]
  have hbcs : bcsError epsRound T R capErr ≤
      31 * correctedTightUnionBound +
        3 * (2 ^ 128 + 1) * (1 / 2 ^ 256) := by
    unfold bcsError
    linarith [hA, hB]
  have hfinal : selectorInflation * bcsError epsRound T R capErr ≤
      selectorInflation *
        (31 * correctedTightUnionBound +
          3 * (2 ^ 128 + 1) * (1 / 2 ^ 256)) :=
    mul_le_mul_of_nonneg_left hbcs (by
      unfold selectorInflation
      norm_num)
  refine hfinal.trans ?_
  unfold selectorInflation correctedTightUnionBound
  norm_num

/-! ## Conditional release endpoint with the margin retained -/

/-- The existing selected-branch endpoint, but with the tighter width-19
arithmetic retained in the conclusion.  This is still conditional on the
published decoding result, the transcript correspondence, the separate
grinding reduction, the Merkle/PCS connection, and the cited Fiat--Shamir
theorem through the structures in the arguments. -/
theorem corrected_selected_release_core_le_seven_tenths
    {Schedule RustBoundary : Type*}
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (separateGrindingOutputReduction : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualBatchEventProbability : Schedule → ℝ)
    (widthDeployment : Width19FStarDeploymentPremises acceptedSchedule
      citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability)
    (schedule : Schedule) (haccepted : acceptedSchedule schedule)
    (epsRound : ℝ) (hepsRoundNonnegative : 0 ≤ epsRound)
    (hdecomposition : epsRound ≤
      actualBatchEventProbability schedule + correctedNonBatchRoundError)
    (R : ℝ) (rustRoundTrace : List RustBoundary)
    (decode : RustBoundary → V5PublicMessageBoundary)
    (semantics : STwoBCSIOPRoundSemantics rustRoundTrace)
    (rustInitialEnsembleM0Correspondence : Prop)
    (randomOracleAndFiatShamirApplicability : Prop)
    (pcsAndMerkleAuthenticationApplicability : Prop)
    (citedBCSAndCMSApplicability : Prop)
    (bcsDeployment : M0ExcludedBCSDeploymentPremises
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability)
    (unionError branch0 branch1 branch2 capErr T : ℝ)
    (hUnion : unionError ≤ branch0 + branch1 + branch2)
    (hbranch0 : branch0 ≤ bcsError epsRound T R capErr)
    (hbranch1 : branch1 ≤ bcsError epsRound T R capErr)
    (hbranch2 : branch2 ≤ bcsError epsRound T R capErr)
    (hcapNonnegative : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    unionError ≤ (7 : ℝ) / (10 * 2 ^ 100) := by
  have hroundCorrected : epsRound ≤ correctedRoundError :=
    actual_round_error_le_corrected_round_error
      acceptedSchedule citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability widthDeployment schedule haccepted epsRound
      hdecomposition
  have hroundTight : epsRound ≤ correctedTightUnionBound :=
    hroundCorrected.trans corrected_round_error_le_tight_union
  rcases m0_excluded_boundary_application_preserves_all_named_premises
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability bcsDeployment with
    ⟨hR30, _hRbound, _hsemantics, _hm0, _hrofs, _hpcs, _hcited⟩
  have hRNonnegative : 0 ≤ R := by
    rw [hR30]
    norm_num
  have hRle30 : R ≤ 30 := by
    rw [hR30]
  calc
    unionError ≤ selectorInflation * bcsError epsRound T R capErr :=
      three_selected_branches_union_bound unionError branch0 branch1 branch2
        (bcsError epsRound T R capErr) hUnion hbranch0 hbranch1 hbranch2
    _ ≤ (7 : ℝ) / (10 * 2 ^ 100) :=
      corrected_work_normalized_core_le_seven_tenths epsRound R capErr T
        hepsRoundNonnegative hroundTight hRNonnegative hRle30
        hcapNonnegative hcap hT1 hTmax

/-- Any separately justified external budget occupying the remaining thirty
percent preserves an overall 100-bit bound. -/
theorem core_plus_external_budget_le_two_pow_neg_100
    (core external : ℝ)
    (hcore : core ≤ (7 : ℝ) / (10 * 2 ^ 100))
    (hexternal : external ≤ (3 : ℝ) / (10 * 2 ^ 100)) :
    core + external ≤ (1 : ℝ) / 2 ^ 100 := by
  linarith

/-- The release target is exactly 100 bits.  The proof does not require every
external event to satisfy a separate 128-bit target: it requires only that the
sum of the justified external-event bounds fit the remaining thirty percent of
the `2^-100` budget.  This identity records that split without imposing an
arbitrary per-event allocation. -/
theorem hundred_bit_target_budget_is_core_plus_external :
    (7 : ℝ) / (10 * 2 ^ 100) + (3 : ℝ) / (10 * 2 ^ 100) =
      (1 : ℝ) / 2 ^ 100 := by
  norm_num

#print axioms corrected_batch_le_2120_div_two_pow_119
#print axioms corrected_batch_without_work_le_2120_div_two_pow_82
#print axioms raw_width19_reference_ceiling_is_above_two_pow_neg_100
#print axioms corrected_round_error_le_tight_union
#print axioms corrected_work_normalized_core_le_seven_tenths
#print axioms corrected_selected_release_core_le_seven_tenths
#print axioms core_plus_external_budget_le_two_pow_neg_100
#print axioms hundred_bit_target_budget_is_core_plus_external

end AspisV5HundredBitSecurityMargin
