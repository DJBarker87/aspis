import AspisFormal.V5FriCircleEncoderDistance
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V6OneFoldCandidateExtraction

/-!
# Distance of the proposed V6 initial and final encoders

The B10 proposal doubles the initial V5 circle domain from `2^19` to `2^20`
without changing the 1024 message coefficients. This file proves that the new
half-odd circle coset is pairwise distinct, avoids the west pole, and therefore
retains the at-most-1024 overlap bound once the encoder's ordinary evaluation
identity is supplied.

It also packages the final `256 -> 2^18` line encoder as an ordinary
degree-at-most-255 evaluation code, yielding its at-most-255 overlap bound.
These are algebraic distance results, not list-decoder or FRI probability
theorems.
-/

set_option maxRecDepth 10000

namespace AspisV6EncoderDistance

open Polynomial
open AspisV5FriCircleEncoderDistance
open AspisV5FriConcreteEncoderApplicability
open AspisV6OneFoldCandidateExtraction

/-! ## Exact `2^20` circle domain -/

def initialCircleExponent (i : Nat) : Int :=
  (2 : Int) ^ 10 * (2 * i + 1)

def initialCirclePoint (i : Fin (2 ^ 20)) : AspisCircleGroupOrder.C :=
  AspisCircleGroupOrder.g ^ initialCircleExponent i

theorem initialCirclePoint_injective : Function.Injective initialCirclePoint := by
  intro i j hij
  have hm := (AspisCircleGroupOrder.g_zpow_eq_iff (initialCircleExponent i)
    (initialCircleExponent j)).mp hij
  apply Fin.ext
  unfold initialCircleExponent Int.ModEq at hm
  have hi := i.isLt
  have hj := j.isLt
  norm_num at hi hj
  omega

private lemma halfTurn_x_eq_neg_one :
    AspisCircleGroupOrder.X
      (AspisCircleGroupOrder.g ^ ((2 : Int) ^ 30)) = -1 := by
  rw [show (2 : Int) ^ 30 = ((2 ^ 30 : Nat) : Int) by norm_num, zpow_natCast]
  rw [← AspisCircleGroupOrder.sq_iterate 30 AspisCircleGroupOrder.g]
  decide

theorem initialCirclePoint_x_ne_neg_one (i : Fin (2 ^ 20)) :
    AspisCircleGroupOrder.X (initialCirclePoint i) ≠ -1 := by
  intro hx
  have hsame :
      AspisCircleGroupOrder.X
          (AspisCircleGroupOrder.g ^ initialCircleExponent i) =
        AspisCircleGroupOrder.X
          (AspisCircleGroupOrder.g ^ ((2 : Int) ^ 30)) := by
    simpa only [initialCirclePoint, halfTurn_x_eq_neg_one] using hx
  have hm := (AspisCircleGroupOrder.sameXCoord_exp
    (initialCircleExponent i) ((2 : Int) ^ 30)).mp hsame
  unfold initialCircleExponent Int.ModEq at hm
  have hi := i.isLt
  norm_num at hi
  rcases hm with hm | hm <;> omega

def initialStereo (i : Fin (2 ^ 20)) : ZMod AspisCircleGroupOrder.P :=
  (initialCirclePoint i).1.2 /
    (1 + AspisCircleGroupOrder.X (initialCirclePoint i))

theorem initialStereo_injective : Function.Injective initialStereo := by
  intro i j hij
  apply initialCirclePoint_injective
  apply AspisCircleGroupOrder.stereo_injective
  have hi : (initialCirclePoint i).1.1 ≠ -1 :=
    initialCirclePoint_x_ne_neg_one i
  have hj : (initialCirclePoint j).1.1 ≠ -1 :=
    initialCirclePoint_x_ne_neg_one j
  unfold AspisCircleGroupOrder.stereo
  rw [if_neg hi, if_neg hj, Option.some.injEq]
  simpa only [initialStereo, AspisCircleGroupOrder.X] using hij

/-! ## Initial circle-code overlap -/

variable {K Message : Type*} [Field K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

noncomputable def exactInitialCosetRealization
    (encoder : Message → Fin (2 ^ 20) → K)
    (p0 p1 : Message → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoder message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i)))) :
    CirclePolynomialRealization encoder where
  point := initialCirclePoint
  point_injective := initialCirclePoint_injective
  avoids_west_pole := initialCirclePoint_x_ne_neg_one
  p0 := p0
  p1 := p1
  p0_degree_lt := hp0
  p1_degree_lt := hp1
  coefficient_pair_injective := hinjective
  encoder_eq_circle_eval := heval

theorem exactInitialCoset_agreement_card_le_1024
    [Fintype K] [DecidableEq K]
    (encoder : Message → Fin (2 ^ 20) → K)
    (p0 p1 : Message → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoder message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i))))
    (left right : Message) (hne : left ≠ right) :
    (AspisV5FriCoherentCandidateExtraction.agreementSet
      (encoder left) (encoder right)).card ≤ 1024 :=
  agreementSet_card_le_1024 encoder
    (exactInitialCosetRealization encoder p0 p1 hp0 hp1 hinjective heval)
    left right hne

theorem v6_initial_encoder_overlap_cap
    [Fintype K] [DecidableEq K]
    (encoders : CodeEncoders K)
    (p0 p1 : InitialCoefficients K → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoders.initial message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i)))) :
    InitialEncoderOverlapCap encoders := by
  intro left right hne
  exact exactInitialCoset_agreement_card_le_1024
    encoders.initial p0 p1 hp0 hp1 hinjective heval left right hne

theorem initial_list_cap_failure_impossible_of_circle_realization
    [Fintype K] [DecidableEq K]
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (p0 p1 : InitialCoefficients K → K[X])
    (hp0 : ∀ message, (p0 message).natDegree < 512)
    (hp1 : ∀ message, (p1 message).natDegree < 512)
    (hinjective : Function.Injective (fun message => (p0 message, p1 message)))
    (heval : ∀ message i,
      encoders.initial message i =
        (p0 message).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (AspisCircleGroupOrder.X (initialCirclePoint i))) +
          algebraMap (ZMod AspisCircleGroupOrder.P) K
              (initialCirclePoint i).1.2 *
            (p1 message).eval
              (algebraMap (ZMod AspisCircleGroupOrder.P) K
                (AspisCircleGroupOrder.X (initialCirclePoint i)))) :
    ¬ InitialListCapFailure encoders transcript := by
  exact initial_list_cap_failure_impossible_of_overlap encoders transcript
    (v6_initial_encoder_overlap_cap encoders p0 p1 hp0 hp1 hinjective heval)

/-! ## Final line-code overlap -/

theorem v6_final_encoder_overlap_cap
    [Fintype K] [DecidableEq K] [NeZero (2 : K)]
    (encoders : CodeEncoders K)
    (identity : NaturalLineEvaluationIdentity encoders.final)
    (left right : FinalCoefficients K) (hne : left ≠ right) :
    (AspisV5FriCoherentCandidateExtraction.agreementSet
      (encoders.final left) (encoders.final right)).card ≤ 255 := by
  exact agreementSet_card_le_of_polynomialEvaluation
    encoders.final 255
    (naturalLinePolynomialRealization (K := K)
      (n := 256) (m := 262144) (by norm_num) encoders.final identity)
    left right hne

/-! ## Audit -/

#print axioms initialCirclePoint_injective
#print axioms initialCirclePoint_x_ne_neg_one
#print axioms initialStereo_injective
#print axioms exactInitialCoset_agreement_card_le_1024
#print axioms v6_initial_encoder_overlap_cap
#print axioms initial_list_cap_failure_impossible_of_circle_realization
#print axioms v6_final_encoder_overlap_cap

end AspisV6EncoderDistance
