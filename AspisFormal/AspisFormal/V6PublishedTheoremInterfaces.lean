import AspisFormal.V5Width19CorrelatedAgreement
import AspisFormal.V5FriDegreeThreeCorrelatedAgreement
import AspisFormal.V6EncoderDistance

/-!
# Exact published-theorem interfaces for the V6 one-fold profile

The cited papers are external inputs, so this file does not recreate their
proofs. It does something narrower and essential: states the exact predicates
Aspis needs from them and checks all finite parameter substitutions around
those predicates.

For the initial 19-column batch, the scalar-power curve has degree 18,
Guruswami--Sudan multiplicity three gives list expression 112, and the exact
challenge cap is `216558659960832`.

For the sole arity-four fold, the curve has degree three and the output-code
list expression is below 113. Using 113 as an integer upper bound gives the
challenge cap `9396508281246`.

Conditional on the two named published predicates, the already-formalized
root-union arguments turn those caps into bad-challenge cardinality bounds.
-/

namespace AspisV6PublishedTheoremInterfaces

open AspisSoundnessLedger
open AspisV5Width19CorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6OneFoldParameterAudit

def initialAgreementThreshold : Nat := 38229
def outputAgreementThreshold : Nat := 9557
def initialListExpressionCap : Nat := 112
def outputListExpressionCap : Nat := 113
def initialBatchCurveDegree : Nat := 18
def foldCurveDegree : Nat := 3

def initialBatchChallengeCap : Nat := 216558659960832
def foldChallengeCap : Nat := 9396508281246

theorem exact_initial_list_expression :
    (((3 : Real) + 1 / 2) / Real.sqrt (1 / 1024)) =
      initialListExpressionCap := by
  rw [show Real.sqrt (1 / 1024 : Real) = 1 / 32 by
    rw [show (1 / 1024 : Real) = (1 / 32) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num]
  norm_num [initialListExpressionCap]

theorem exact_initial_batch_challenge_cap :
    (initialListExpressionCap : Real) *
        ((2 * (initialListExpressionCap : Real) ^ 4 / 3) *
          (1 / 1024) + 1) *
        initialBatchCurveDegree * 1048576 =
      initialBatchChallengeCap := by
  norm_num [initialListExpressionCap, initialBatchCurveDegree,
    initialBatchChallengeCap]

private theorem sqrt_outputRate_pos : 0 < Real.sqrt outputRate :=
  Real.sqrt_pos.2 (by norm_num [outputRate, finalDomainSize])

private theorem sqrt_outputRate_sq :
    Real.sqrt outputRate ^ 2 = outputRate :=
  Real.sq_sqrt (by norm_num [outputRate, finalDomainSize])

theorem output_list_expression_lt_113 :
    (((3 : Real) + 1 / 2) / Real.sqrt outputRate) <
      outputListExpressionCap := by
  rw [div_lt_iff₀ sqrt_outputRate_pos]
  have hs := sqrt_outputRate_sq
  have hp := sqrt_outputRate_pos
  have h255 : Real.sqrt (255 : Real) ^ 2 = 255 :=
    Real.sq_sqrt (by norm_num)
  have h255p : 0 < Real.sqrt (255 : Real) :=
    Real.sqrt_pos.2 (by norm_num)
  norm_num [outputRate, finalDomainSize, outputListExpressionCap] at hs ⊢
  nlinarith [h255]

theorem conservative_fold_challenge_cap :
    (outputListExpressionCap : Real) *
        ((2 * (outputListExpressionCap : Real) ^ 4 / 3) *
          (255 / 262144) + 1) *
        foldCurveDegree * 262144 = foldChallengeCap := by
  norm_num [outputListExpressionCap, foldCurveDegree, foldChallengeCap]

/-- Exact Appendix-A.2 predicate needed for the B10 nineteen-column batch. -/
def PublishedInitialWidth19CurveDecodability
    {K Message : Type*} [Field K] [Fintype K] [DecidableEq K]
    (encoder : Message → Fin 1048576 → K) : Prop :=
  Width19CurveDecodable encoder initialAgreementThreshold
    initialBatchChallengeCap

/-- Exact degree-three curve predicate needed for the sole V6 fold. -/
def PublishedOneFoldCurveDecodability
    {K Message : Type*} [Field K] [Fintype K] [DecidableEq K]
    (encoder : Message → Fin 262144 → K) : Prop :=
  DegreeThreeCurveDecodable encoder outputAgreementThreshold foldChallengeCap

theorem initial_bad_response_challenges_card_le
    {K Message : Type*} [Field K] [Fintype K] [DecidableEq K]
    (encoder : Message → Fin 1048576 → K)
    (published : PublishedInitialWidth19CurveDecodability encoder)
    (lanes : Fin 19 → Fin 1048576 → K)
    (strategy : Width19ProximateStrategy K (Fin 1048576) Message) :
    (width19GoodChallenges encoder initialAgreementThreshold lanes
      (width19BadStrategy encoder initialAgreementThreshold lanes strategy)).card ≤
        initialBatchChallengeCap := by
  exact width19_bad_response_challenges_card_le
    encoder initialAgreementThreshold initialBatchChallengeCap published
    lanes strategy

theorem fold_bad_response_challenges_card_le
    {K Message : Type*} [Field K] [Fintype K] [DecidableEq K]
    (encoder : Message → Fin 262144 → K)
    (published : PublishedOneFoldCurveDecodability encoder)
    (lanes : Fin 4 → Fin 262144 → K)
    (strategy : ProximateStrategy K (Fin 262144) Message)
    (hfalse : ¬ HasJointAgreement encoder outputAgreementThreshold lanes) :
    (goodChallenges encoder outputAgreementThreshold lanes strategy).card ≤
      foldChallengeCap := by
  exact goodChallenges_card_le_of_no_jointAgreement
    encoder outputAgreementThreshold foldChallengeCap published lanes strategy
    hfalse

/-- The exact degree-18 initial theorem, with 34 bits of authenticated work,
is already below `2^-110`. The companion screen used coefficient 28 and is
therefore conservative for this particular published interface. -/
theorem conditional_initial_batch_probability_le :
    (initialBatchChallengeCap : Real) / (FIELD - 1) / 2 ^ 34 ≤
      (1 : Real) / 2 ^ 110 := by
  norm_num [initialBatchChallengeCap, FIELD]

/-- The integer-113 fold cap, with 31 bits of authenticated work, is below
`2^-111`. -/
theorem conditional_fold_probability_le :
    (foldChallengeCap : Real) / FIELD / 2 ^ 31 ≤
      (1 : Real) / 2 ^ 111 := by
  norm_num [foldChallengeCap, FIELD]

/-! ## Audit -/

#print axioms exact_initial_list_expression
#print axioms exact_initial_batch_challenge_cap
#print axioms output_list_expression_lt_113
#print axioms conservative_fold_challenge_cap
#print axioms initial_bad_response_challenges_card_le
#print axioms fold_bad_response_challenges_card_le
#print axioms conditional_initial_batch_probability_le
#print axioms conditional_fold_probability_le

end AspisV6PublishedTheoremInterfaces
