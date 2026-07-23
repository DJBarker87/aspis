import AspisFormal.SoundnessWorkNormalizedEndpoint
import AspisFormal.V5WorkNormalizedApplicabilityRepair
import AspisFormal.V5SelectedGoodVerifierRelation
import AspisFormal.V5NonceWorkAuthentication

/-!
# Corrected implemented v5 work-normalized endpoint

This file composes, without replacing, the maintained arithmetic and deployment
interfaces for the feature-gated v5 verifier:

* the direct-C powers batch has width 19, degree 18, a challenge uniform on
  `F*`, and one 37-bit positioned work predicate;
* the four fold events use their distinct positioned difficulties
  `34, 33, 30, 25`;
* the final q18 miss uses its distinct positioned 32-bit predicate;
* the S-two `m0` convention gives exactly 30 public-coin rounds, not the old
  31 serialized boundaries;
* selected-good soundness applies the three-branch union factor exactly once.

The legacy `SoundnessWorkNormalizedEndpoint.roundError` uses a coefficient-28,
full-field batch expression.  It is not definitionally the deployed width-19
`F*` expression.  We prove below that it is a strict conservative upper bound,
then instantiate the generic endpoint with the actual corrected round error.
No claim equates the two expressions.

Every deployment edge remains an explicit premise: the separate grinding-output
reduction, virtual-oracle/code membership, Rust sampling/transcript and work-step
correspondence, authenticated public-coin round semantics, PCS/Merkle binding,
SHA/random-oracle and Fiat--Shamir applicability, and the cited MCA/BCS/CMS
theorems.  In particular, byte equality is never used to infer hash behavior.
-/

namespace AspisV5ImplementedWorkNormalizedEndpoint

open AspisSoundnessLedger
open AspisWorkNormalizedEndpoint
open AspisV5NonceWorkAuthentication
open AspisV5WorkNormalizedApplicabilityRepair
open AspisV5SelectedGoodVerifierRelation
open AspisFormal.V5ExactRuntimeWireRepair

/-! ## Exact six-event implemented ledger -/

/-- Exact deployed difficulty map, stated as one proposition so the final
endpoint exposes the implemented values rather than a host configuration. -/
def ExactImplementedDifficulties : Prop :=
  WorkKind.difficulty .batch = 37 ∧
    WorkKind.difficulty (.fold 0) = 34 ∧
    WorkKind.difficulty (.fold 1) = 33 ∧
    WorkKind.difficulty (.fold 2) = 30 ∧
    WorkKind.difficulty (.fold 3) = 25 ∧
    WorkKind.difficulty .finalQuery = 32

/-- Exact labels and transcript positions used by the six work predicates. -/
def ExactImplementedWorkPositions : Prop :=
  WorkKind.label .batch = 28 ∧
    WorkKind.stage .batch = .terminalBeforeGamma ∧
    (∀ round, WorkKind.label (.fold round) = 20 ∧
      WorkKind.stage (.fold round) = .foldBeforeAlpha round) ∧
    WorkKind.label .finalQuery = 5 ∧
    WorkKind.stage .finalQuery = .finalPolynomialBeforeSelector

theorem exact_implemented_difficulties : ExactImplementedDifficulties := by
  exact exact_difficulty_map

theorem exact_implemented_work_positions : ExactImplementedWorkPositions := by
  exact exact_label_and_stage_map

/-- The six alternative bad-event contributions that consume the six distinct
positioned work predicates, each written exactly once.  Work bits are not added
together as though all six predicates described one event. -/
noncomputable def exactSixWorkTermTotal : ℝ :=
  powersBatchArithmeticFStar 18 +
    fold0Term + fold1Term + fold2Term + fold3Term + rawTerm

/-- Every non-work-normalized term of the maintained interactive union. -/
noncomputable def noWorkRoundError : ℝ :=
  oodTerm
    + 24 / FIELD + 24 / FIELD + 30 / (FIELD - 1) + 28 / (FIELD - 1)
    + 3111 / FIELD + 4828 / FIELD + 10 / FIELD + 1 / FIELD + 1 / (FIELD - 1)
    + 270 / FIELD
    + 1 / 2 ^ 124 + 1 / 2 ^ 128

/-- All terms after the actual width-19 batch event. -/
noncomputable def correctedNonBatchRoundError : ℝ :=
  fold0Term + fold1Term + fold2Term + fold3Term + rawTerm + noWorkRoundError

/-- Corrected implemented interactive round-error ledger.  The batch term is
the coefficient-18 `F*` expression; every other maintained term is unchanged. -/
noncomputable def correctedRoundError : ℝ :=
  exactSixWorkTermTotal + noWorkRoundError

/-- Definitional six-work-event decomposition.  Together with the bijection
from actual work events to `WorkKind`, this is the no-omission/no-duplication
accounting statement used by the capstone. -/
theorem corrected_round_error_has_each_work_term_exactly_once :
    correctedRoundError = exactSixWorkTermTotal + noWorkRoundError := by
  rfl

/-- The corrected ledger is the actual batch bound plus the exact remaining
ledger. -/
theorem corrected_round_error_eq_batch_plus_nonbatch :
    correctedRoundError =
      powersBatchArithmeticFStar 18 + correctedNonBatchRoundError := by
  unfold correctedRoundError exactSixWorkTermTotal correctedNonBatchRoundError
  ring

/-! ## The legacy coefficient-28 endpoint is conservative, not exact -/

/-- The coefficient/denominator comparison that makes the old coefficient-28
full-field batch expression conservative for the deployed coefficient-18
nonzero-field expression. -/
theorem coefficient18_fstar_le_coefficient28_full_field :
    (18 : ℝ) / (FIELD - 1) ≤ 28 / FIELD := by
  have hfield : (0 : ℝ) < FIELD := FIELD_pos
  have hfieldMinusOne : (0 : ℝ) < FIELD - 1 := by
    unfold FIELD
    norm_num
  rw [div_le_div_iff₀ hfieldMinusOne hfield]
  unfold FIELD
  norm_num

/-- Exact mismatch characterization: the corrected deployed batch expression
is strictly smaller than the legacy coefficient-28 expression.  The latter may
therefore be used as an upper bound, never as an executable equality claim. -/
theorem corrected_batch_is_strictly_below_legacy_batch :
    powersBatchArithmeticFStar 18 < batchTerm := by
  let common : ℝ :=
    ((21 / 2) / Real.sqrt (1 / 512))
      * ((2 * ((21 / 2) / Real.sqrt (1 / 512)) ^ 4 / 3) * (1 / 512) + 1)
      * 524288 / 2 ^ 37
  have hsqrt : (0 : ℝ) < Real.sqrt (1 / 512) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hcommon : 0 < common := by
    dsimp [common]
    positivity
  have hfield : (0 : ℝ) < FIELD := FIELD_pos
  have hfieldMinusOne : (0 : ℝ) < FIELD - 1 := by
    unfold FIELD
    norm_num
  have hcoefficient : (18 : ℝ) / (FIELD - 1) < 28 / FIELD := by
    rw [div_lt_div_iff₀ hfieldMinusOne hfield]
    unfold FIELD
    norm_num
  calc
    powersBatchArithmeticFStar 18 = (18 / (FIELD - 1)) * common := by
      unfold powersBatchArithmeticFStar common
      ring
    _ < (28 / FIELD) * common :=
      mul_lt_mul_of_pos_right hcoefficient hcommon
    _ = batchTerm := by
      unfold batchTerm common
      ring

/-- Consequently the complete corrected ledger is bounded by the maintained
legacy ledger without identifying their batch expressions. -/
theorem corrected_round_error_le_legacy_round_error :
    correctedRoundError ≤ roundError := by
  have hlegacy : roundError = batchTerm + correctedNonBatchRoundError := by
    unfold roundError correctedNonBatchRoundError noWorkRoundError
    ring
  rw [corrected_round_error_eq_batch_plus_nonbatch, hlegacy]
  linarith [corrected_batch_is_strictly_below_legacy_batch]

theorem corrected_round_error_le_unionBound :
    correctedRoundError ≤ unionBound :=
  corrected_round_error_le_legacy_round_error.trans roundError_le_unionBound

/-! ## Actual-event and cited-theorem application -/

/-- The actual accepted-schedule round error is bounded by the corrected
ledger.  The batch term is obtained only after consuming every named width-19
`F*` deployment premise; the rest of the authenticated conditional-event union
remains the explicit `hdecomposition` premise. -/
theorem actual_round_error_le_corrected_round_error
    {Schedule : Type*}
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (separateGrindingOutputReduction : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualBatchEventProbability : Schedule → ℝ)
    (deployment : Width19FStarDeploymentPremises acceptedSchedule
      citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability)
    (schedule : Schedule) (haccepted : acceptedSchedule schedule)
    (epsRound : ℝ)
    (hdecomposition : epsRound ≤
      actualBatchEventProbability schedule + correctedNonBatchRoundError) :
    epsRound ≤ correctedRoundError := by
  have hbatch : actualBatchEventProbability schedule ≤
      powersBatchArithmeticFStar 18 :=
    deployment.citedCorrectedEventBound schedule
      (deployment.acceptedHasCitedMCAHypotheses schedule haccepted)
      (deployment.acceptedHasVirtualOracleAndCodeMembership schedule haccepted)
      (deployment.acceptedHasSeparateGrindingOutputReduction schedule haccepted)
      (deployment.acceptedHasRustSamplingAndTranscriptCorrespondence schedule haccepted)
  rw [corrected_round_error_eq_batch_plus_nonbatch]
  linarith

theorem actual_round_error_le_unionBound
    {Schedule : Type*}
    (acceptedSchedule citedMCAHypotheses : Schedule → Prop)
    (virtualOracleAndCodeMembership : Schedule → Prop)
    (separateGrindingOutputReduction : Schedule → Prop)
    (rustSamplingAndTranscriptCorrespondence : Schedule → Prop)
    (actualBatchEventProbability : Schedule → ℝ)
    (deployment : Width19FStarDeploymentPremises acceptedSchedule
      citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability)
    (schedule : Schedule) (haccepted : acceptedSchedule schedule)
    (epsRound : ℝ)
    (hdecomposition : epsRound ≤
      actualBatchEventProbability schedule + correctedNonBatchRoundError) :
    epsRound ≤ unionBound :=
  (actual_round_error_le_corrected_round_error
    acceptedSchedule citedMCAHypotheses virtualOracleAndCodeMembership
    separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
    actualBatchEventProbability deployment schedule haccepted epsRound
    hdecomposition).trans corrected_round_error_le_unionBound

/-! ## Selector factor is consumed once -/

theorem selector_inflation_is_exactly_three : selectorInflation = 3 := by
  rfl

/-- Regression tooth: on every positive error, applying the selector factor a
second time is observably different.  The endpoint below has only the single
factor introduced by `three_selected_branches_union_bound`. -/
theorem a_second_selector_factor_would_be_double_counting
    (error : ℝ) (herror : 0 < error) :
    selectorInflation * (selectorInflation * error) ≠
      selectorInflation * error := by
  unfold selectorInflation
  nlinarith

/-! ## Corrected conditional release endpoint -/

/-- Selected-good release bound with the actual corrected round error and the
S-two-corrected `R = 30`.  The semantic three-event union and per-branch cited
BCS bounds are explicit premises.  The proof applies `selectorInflation = 3`
once: first form the three-event union, then discharge exactly that expression
with the generic work-normalized endpoint. -/
theorem corrected_selected_good_release_endpoint
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
    unionError ≤ 1 / 2 ^ 100 := by
  have hround : epsRound ≤ unionBound :=
    actual_round_error_le_unionBound
      acceptedSchedule citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability widthDeployment schedule haccepted epsRound
      hdecomposition
  rcases m0_excluded_boundary_application_preserves_all_named_premises
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability bcsDeployment with
    ⟨hR30, hRbound, _hsemantics, _hm0, _hrofs, _hpcs, _hcited⟩
  have hRNonnegative : 0 ≤ R := by
    rw [hR30]
    norm_num
  calc
    unionError ≤ selectorInflation * bcsError epsRound T R capErr :=
      three_selected_branches_union_bound unionError branch0 branch1 branch2
        (bcsError epsRound T R capErr) hUnion hbranch0 hbranch1 hbranch2
    _ ≤ 1 / 2 ^ 100 :=
      work_normalized_endpoint epsRound R capErr T hepsRoundNonnegative hround
        hRNonnegative hRbound hcapNonnegative hcap hT1 hTmax

/-! ## Full implemented integration -/

/-- The corrected numerical endpoint together with exact executable work checks,
exactly-once actual-event accounting, `R = 30`, and every named computational
or executable seam.  The actual-event bijection is required explicitly: model
enumeration alone is not promoted to a deployed event partition. -/
theorem corrected_implemented_work_normalized_endpoint
    {Schedule RustBoundary State Challenge Digest ActualEvent : Type*}
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
    (rustAccepts : Prop)
    (rustHash : State → List Byte → Digest)
    (digestHasLeadingZeroBits : Digest → Nat → Prop)
    (rustFunctions : ExecutableWorkFunctions State Challenge)
    (workInputs : PositionedWorkInputs State Challenge)
    (workCorrespondence : ExactRustWorkVerifierCorrespondence rustAccepts
      rustHash digestHasLeadingZeroBits rustFunctions workInputs)
    (hrustAccepts : rustAccepts)
    (toLedger : ActualEvent → CreditedWorkEvent)
    (hActualEventInjective : InjectiveActualWorkEventToLedger toLedger)
    (hActualEventCoverage : CompleteActualWorkEventLedgerCoverage toLedger)
    (unionError branch0 branch1 branch2 capErr T : ℝ)
    (hUnion : unionError ≤ branch0 + branch1 + branch2)
    (hbranch0 : branch0 ≤ bcsError epsRound T R capErr)
    (hbranch1 : branch1 ≤ bcsError epsRound T R capErr)
    (hbranch2 : branch2 ≤ bcsError epsRound T R capErr)
    (hcapNonnegative : 0 ≤ capErr) (hcap : capErr ≤ roCapErr)
    (hT1 : 1 ≤ T) (hTmax : T ≤ 2 ^ 128) :
    unionError ≤ 1 / 2 ^ 100 ∧
      R = 30 ∧
      selectorInflation = 3 ∧
      powersBatchDegree directCBatchWidth = 18 ∧
      Fintype.card WorkKind = 6 ∧
      correctedRoundError = exactSixWorkTermTotal + noWorkRoundError ∧
      ExactImplementedDifficulties ∧
      ExactImplementedWorkPositions ∧
      HashRandomOracleWorkInterface rustHash digestHasLeadingZeroBits
        rustFunctions.grindingOK ∧
      (∀ kind, ExactWorkOK rustFunctions workInputs kind) ∧
      Function.Bijective (fun event => (toLedger event).workKind) ∧
      STwoBCSIOPRoundSemanticApplicability R rustRoundTrace semantics ∧
      rustInitialEnsembleM0Correspondence ∧
      randomOracleAndFiatShamirApplicability ∧
      pcsAndMerkleAuthenticationApplicability ∧
      citedBCSAndCMSApplicability := by
  have hrelease : unionError ≤ 1 / 2 ^ 100 :=
    corrected_selected_good_release_endpoint
      acceptedSchedule citedMCAHypotheses virtualOracleAndCodeMembership
      separateGrindingOutputReduction rustSamplingAndTranscriptCorrespondence
      actualBatchEventProbability widthDeployment schedule haccepted
      epsRound hepsRoundNonnegative hdecomposition
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability citedBCSAndCMSApplicability
      bcsDeployment unionError branch0 branch1 branch2 capErr T
      hUnion hbranch0 hbranch1 hbranch2 hcapNonnegative hcap hT1 hTmax
  rcases m0_excluded_boundary_application_preserves_all_named_premises
      R rustRoundTrace decode semantics
      rustInitialEnsembleM0Correspondence
      randomOracleAndFiatShamirApplicability
      pcsAndMerkleAuthenticationApplicability
      citedBCSAndCMSApplicability bcsDeployment with
    ⟨hR30, _hRbound, hsemantics, hm0, hrofs, hpcs, hcited⟩
  have hwork : ∀ kind, ExactWorkOK rustFunctions workInputs kind :=
    rust_acceptance_projects_six_exact_steps_under_correspondence
      workCorrespondence hrustAccepts
  have hexactlyOnce :
      Function.Bijective (fun event => (toLedger event).workKind) :=
    actual_event_correspondence_derives_exactly_once_accounting
      toLedger hActualEventInjective hActualEventCoverage
  exact ⟨hrelease, hR30, selector_inflation_is_exactly_three,
    direct_c_width19_powers_degree_is_18, work_kind_count_is_six,
    corrected_round_error_has_each_work_term_exactly_once,
    exact_implemented_difficulties, exact_implemented_work_positions,
    workCorrespondence.exactGrindingHashInput, hwork, hexactlyOnce,
    hsemantics, hm0, hrofs, hpcs, hcited⟩

/-! ## Axiom audit -/

#print axioms exact_implemented_difficulties
#print axioms exact_implemented_work_positions
#print axioms corrected_round_error_has_each_work_term_exactly_once
#print axioms corrected_round_error_eq_batch_plus_nonbatch
#print axioms coefficient18_fstar_le_coefficient28_full_field
#print axioms corrected_batch_is_strictly_below_legacy_batch
#print axioms corrected_round_error_le_legacy_round_error
#print axioms corrected_round_error_le_unionBound
#print axioms actual_round_error_le_corrected_round_error
#print axioms actual_round_error_le_unionBound
#print axioms selector_inflation_is_exactly_three
#print axioms a_second_selector_factor_would_be_double_counting
#print axioms corrected_selected_good_release_endpoint
#print axioms corrected_implemented_work_normalized_endpoint

end AspisV5ImplementedWorkNormalizedEndpoint
