import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.V5FriCompatibleCandidateChain

/-!
# Exact Tag-73 one-fold restoration strategy

This module turns the remaining K1.3 `OneFoldReductionFailure` into the exact
degree-three bad-challenge event covered by the published one-fold circle-code
theorem.

The response strategy is fixed before `alpha`: for every restored challenge it
returns the same disclosed final-256 message and uses exactly the corresponding
full-domain consistency set as its support.  The four received coefficient
lanes are obtained by locally decoding every authenticated circle fibre.  Lean
then proves:

* their degree-three curve is the deployed normalized circle fold;
* a non-resolving correlated-agreement response reconstructs four initial
  symbols per supported output coordinate;
* more than 9557 supported output coordinates therefore give at least 38230
  supported initial coordinates; and
* injectivity of the exact final encoder makes the reconstructed initial
  candidate fold to the disclosed final-256 message.

Consequently the bad set has the single published cap `foldChallengeCap`; no
decoder-list or independently selected-candidate union factor appears.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactOneFoldRestorationStrategy

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCompatibleCandidateChain
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable section

/-- Replace only the restored fold challenge.  The public inverse tables are
fixed by the statement and are identical in every restoration fork. -/
def scheduleAtAlpha (schedule : OneFoldSchedule F K) (alpha : K) :
    OneFoldSchedule F K where
  alpha := alpha
  circleInv2x := schedule.circleInv2x
  circleInv2y := schedule.circleInv2y

@[simp] theorem scheduleAtAlpha_alpha
    (schedule : OneFoldSchedule F K) (alpha : K) :
    (scheduleAtAlpha schedule alpha).alpha = alpha := rfl

@[simp] theorem scheduleAtAlpha_original
    (schedule : OneFoldSchedule F K) :
    scheduleAtAlpha schedule schedule.alpha = schedule := by
  cases schedule
  rfl

/-- Exact algebraic bridge for the deployed one-fold encoders.  It contains
only concrete encoder/geometry equalities and inverse identities.  The
degree-three decoding theorem is deliberately not a field of this structure. -/
structure OneFoldAlgebraBinding
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K) where
  finalLinear :
    (FinalCoefficients K) →ₗ[K] (FinalWord K)
  circleX : Fin 262144 → K
  circleY : Fin 262144 → K
  initialEncoderEq : encoders.initial = fun coefficients =>
    circleLiftEncoder finalLinear circleX circleY coefficients
  finalEncoderEq : encoders.final = fun coefficients =>
    finalLinear coefficients
  inverse2x : ∀ index,
    2 * circleX index *
      algebraMap F K (schedule.circleInv2x index) = 1
  inverse2y : ∀ index,
    2 * circleY index *
      algebraMap F K (schedule.circleInv2y index) = 1
  finalInjective : Function.Injective finalLinear

/-- The four coefficient lanes obtained by exactly inverting each received
circle fibre.  They are independent of `alpha`, as required by correlated
agreement. -/
def oneFoldDecodedLanes
    (schedule : OneFoldSchedule F K) (transcript : IdealTranscript K) :
    Fin 4 → FinalWord K :=
  fun lane index =>
    radix4Decode
      (algebraMap F K (schedule.circleInv2y index))
      (-algebraMap F K (schedule.circleInv2y index))
      (algebraMap F K (schedule.circleInv2x index))
      (fun slot => transcript.initial (childIndex index slot)) lane

/-- Evaluating the decoded-lane curve at any restored challenge is literally
the verifier's normalized circle fold at that challenge. -/
theorem curve_oneFoldDecodedLanes_eq_circleFold
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) (alpha : K) (index : Fin 262144) :
    curveValue (oneFoldDecodedLanes schedule transcript) alpha index =
      circleFoldLayer 262144 alpha schedule.circleInv2x
        schedule.circleInv2y transcript.initial index := by
  rw [AspisV5FriCompatibleCandidateChain.curveValue_eq_coefficientFoldValue,
    circleFoldLayer_apply]
  symm
  exact circleFoldValue_eq_coefficientFoldValue_decode
    alpha (binding.circleX index) (binding.circleY index)
      (algebraMap F K (schedule.circleInv2x index))
      (algebraMap F K (schedule.circleInv2y index))
      (binding.inverse2x index) (binding.inverse2y index)
      (fun slot => transcript.initial (childIndex index slot))

/-- The local decoded lanes reconstruct every one of the four received
symbols, not merely their folded value. -/
theorem oneFoldDecodedLanes_reconstruct
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) (index : Fin 262144) :
    radix4Evaluate (binding.circleY index) (-binding.circleY index)
        (binding.circleX index)
        (fun lane => oneFoldDecodedLanes schedule transcript lane index) =
      fun slot => transcript.initial (childIndex index slot) := by
  apply radix4Evaluate_radix4Decode
  · exact binding.inverse2y index
  · simpa only [neg_mul, mul_neg, neg_neg] using binding.inverse2y index
  · exact binding.inverse2x index

/-- Joint agreement of the four locally decoded lanes with four final-code
messages reconstructs the assembled initial codeword on the whole fibre. -/
theorem initial_assembled_eq_received_on_joint
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K)
    (components : Fin 4 → FinalCoefficients K)
    (index : Fin 262144)
    (joint : index ∈ jointAgreementSet binding.finalLinear
      (oneFoldDecodedLanes schedule transcript) components) :
    ∀ slot,
      encoders.initial (assembleCoefficientLanes components)
          (childIndex index slot) =
        transcript.initial (childIndex index slot) := by
  classical
  have laneEq : ∀ lane,
      oneFoldDecodedLanes schedule transcript lane index =
        binding.finalLinear (components lane) index := by
    simpa [jointAgreementSet] using joint
  intro slot
  calc
    encoders.initial (assembleCoefficientLanes components)
        (childIndex index slot) =
      radix4Evaluate (binding.circleY index) (-binding.circleY index)
        (binding.circleX index)
        (fun lane => binding.finalLinear (components lane) index) slot := by
          rw [binding.initialEncoderEq]
          simpa only [circleLiftEncoder, Pi.neg_apply,
            coefficientLane_assembleCoefficientLanes] using
            (radix4LiftEncoder_apply_child binding.finalLinear binding.circleY
              (-binding.circleY) binding.circleX
              (assembleCoefficientLanes components) index slot)
    _ = radix4Evaluate (binding.circleY index) (-binding.circleY index)
        (binding.circleX index)
        (fun lane => oneFoldDecodedLanes schedule transcript lane index) slot := by
          congr 1
          funext lane
          exact (laneEq lane).symm
    _ = transcript.initial (childIndex index slot) := by
      exact congrFun
        (oneFoldDecodedLanes_reconstruct schedule encoders binding transcript index)
        slot

/-- Four reconstructed symbols per response-support coordinate lie in the
literal `SupportedNearInitial` set. -/
theorem four_response_fibres_card_le_supportedAgreement
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K)
    (support : Finset (Fin 262144))
    (consistent : ∀ index ∈ support,
      QueryConsistent schedule encoders transcript index)
    (reconstruct : ∀ index ∈ support, ∀ slot : Fin 4,
      encoders.initial candidate (childIndex index slot) =
        transcript.initial (childIndex index slot)) :
    support.card * 4 ≤
      (supportedAgreementInitial schedule encoders transcript candidate).card := by
  classical
  have childInjective : Function.Injective
      (fun pair : Fin 262144 × Fin 4 =>
        (childIndex pair.1 pair.2 : Fin 1048576)) := by
    intro left right equal
    apply Prod.ext
    · have parentEqual := congrArg (parentIndex (n := 262144)) equal
      simpa using parentEqual
    · have slotEqual := congrArg (slotIndex (n := 262144)) equal
      simpa using slotEqual
  calc
    support.card * 4 =
        (support.product (Finset.univ : Finset (Fin 4))).card := by simp
    _ ≤ (supportedAgreementInitial schedule encoders transcript candidate).card := by
      apply Finset.card_le_card_of_injOn
        (fun pair : Fin 262144 × Fin 4 => childIndex pair.1 pair.2)
      · intro pair pairMember
        have pairMember' : pair ∈
            support.product (Finset.univ : Finset (Fin 4)) :=
          Finset.mem_coe.mp pairMember
        have indexMember : pair.1 ∈ support :=
          (Finset.mem_product.mp pairMember').1
        apply Finset.mem_coe.mpr
        simp only [supportedAgreementInitial, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · have parentEq :
              (⟨(childIndex pair.1 pair.2).val / 4, by omega⟩ :
                Fin 262144) = pair.1 := by
            apply Fin.ext
            simp only [childIndex_val]
            omega
          rw [parentEq]
          exact consistent pair.1 indexMember
        · exact (reconstruct pair.1 indexMember pair.2).symm
      · intro left _ right _ equal
        exact childInjective equal

/-- The one restoration-wide response strategy.  Its candidate is always the
disclosed final-256 object; its support at `alpha` is exactly the consistency
set produced by restoring that challenge. -/
noncomputable def restoredOneFoldStrategy
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) :
    ProximateStrategy K (Fin 262144) (FinalCoefficients K) where
  candidate := fun _ => transcript.disclosedFinal
  support := fun alpha =>
    consistencySet (scheduleAtAlpha schedule alpha) encoders transcript

@[simp] theorem restoredOneFoldStrategy_candidate
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (alpha : K) :
    (restoredOneFoldStrategy schedule encoders transcript).candidate alpha =
      transcript.disclosedFinal := rfl

@[simp] theorem restoredOneFoldStrategy_support
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (alpha : K) :
    (restoredOneFoldStrategy schedule encoders transcript).support alpha =
      consistencySet (scheduleAtAlpha schedule alpha) encoders transcript := rfl

/-- A dense restored consistency set is a valid response to the exact decoded
lane curve. -/
theorem restoredOneFoldStrategy_valid
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) (alpha : K)
    (dense : 9557 <
      (consistencySet (scheduleAtAlpha schedule alpha) encoders transcript).card) :
    ValidResponse binding.finalLinear outputAgreementThreshold
      (oneFoldDecodedLanes schedule transcript)
      (restoredOneFoldStrategy schedule encoders transcript) alpha := by
  constructor
  · exact dense
  · intro index member
    have consistent : QueryConsistent (scheduleAtAlpha schedule alpha)
        encoders transcript index := by
      simpa [restoredOneFoldStrategy, consistencySet] using member
    rw [curve_oneFoldDecodedLanes_eq_circleFold schedule encoders binding
      transcript alpha index]
    change circleFoldLayer 262144 alpha schedule.circleInv2x
        schedule.circleInv2y transcript.initial index =
      binding.finalLinear transcript.disclosedFinal index
    change circleFoldLayer 262144 alpha schedule.circleInv2x
        schedule.circleInv2y transcript.initial index =
      encoders.final transcript.disclosedFinal index at consistent
    rw [binding.finalEncoderEq] at consistent
    exact consistent

/-- A challenge is genuinely bad when the exact response is valid but no
supported initial predecessor folding to the disclosed terminal exists. -/
def OneFoldBadResponse
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) (alpha : K) : Prop :=
  ValidResponse binding.finalLinear outputAgreementThreshold
      (oneFoldDecodedLanes schedule transcript)
      (restoredOneFoldStrategy schedule encoders transcript) alpha ∧
    OneFoldReductionFailure (scheduleAtAlpha schedule alpha)
      encoders transcript

/-- Mask every response except genuine one-fold failures.  This lets the
published correlated-agreement theorem select from the bad responses
themselves. -/
noncomputable def oneFoldBadMaskedStrategy
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) :
    ProximateStrategy K (Fin 262144) (FinalCoefficients K) := by
  classical
  exact {
    candidate :=
      (restoredOneFoldStrategy schedule encoders transcript).candidate
    support := fun alpha =>
      if OneFoldBadResponse schedule encoders binding transcript alpha then
        (restoredOneFoldStrategy schedule encoders transcript).support alpha
      else ∅
  }

theorem valid_oneFoldBadMaskedStrategy_iff
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) (alpha : K) :
    ValidResponse binding.finalLinear outputAgreementThreshold
        (oneFoldDecodedLanes schedule transcript)
        (oneFoldBadMaskedStrategy schedule encoders binding transcript) alpha ↔
      OneFoldBadResponse schedule encoders binding transcript alpha := by
  classical
  by_cases bad : OneFoldBadResponse schedule encoders binding transcript alpha
  · have supportEq :
        (oneFoldBadMaskedStrategy schedule encoders binding transcript).support alpha =
          (restoredOneFoldStrategy schedule encoders transcript).support alpha := by
      simp [oneFoldBadMaskedStrategy, bad]
    constructor
    · intro _
      exact bad
    · intro _
      unfold ValidResponse
      rw [supportEq]
      exact bad.1
  · have supportEq :
        (oneFoldBadMaskedStrategy schedule encoders binding transcript).support alpha =
          ∅ := by
      simp [oneFoldBadMaskedStrategy, bad]
    constructor
    · intro impossible
      have : outputAgreementThreshold < 0 := by
        simpa only [supportEq, Finset.card_empty] using impossible.1
      exact (Nat.not_lt_zero _ this).elim
    · exact fun impossible => (bad impossible).elim

/-- The fixed pre-challenge set of genuine one-fold failures. -/
noncomputable def oneFoldBadChallenges
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) : Finset K :=
  goodChallenges binding.finalLinear outputAgreementThreshold
    (oneFoldDecodedLanes schedule transcript)
    (oneFoldBadMaskedStrategy schedule encoders binding transcript)

@[simp] theorem mem_oneFoldBadChallenges_iff
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K) (alpha : K) :
    alpha ∈ oneFoldBadChallenges schedule encoders binding transcript ↔
      OneFoldBadResponse schedule encoders binding transcript alpha := by
  rw [oneFoldBadChallenges, mem_goodChallenges_iff]
  exact valid_oneFoldBadMaskedStrategy_iff schedule encoders binding
    transcript alpha

/-- The complete deterministic one-fold reduction.  If the bad set exceeded
the published cap, curve decoding would select a non-resolving bad response.
Its own support then reconstructs a supported initial predecessor whose exact
coefficient fold is the disclosed final message, contradicting badness. -/
theorem oneFoldBadChallenges_card_le
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K)
    (published : PublishedOneFoldCurveDecodability binding.finalLinear) :
    (oneFoldBadChallenges schedule encoders binding transcript).card ≤
      foldChallengeCap := by
  classical
  by_contra notBounded
  have many : foldChallengeCap <
      (oneFoldBadChallenges schedule encoders binding transcript).card :=
    Nat.lt_of_not_ge notBounded
  let lanes := oneFoldDecodedLanes schedule transcript
  let strategy := restoredOneFoldStrategy schedule encoders transcript
  let masked := oneFoldBadMaskedStrategy schedule encoders binding transcript
  obtain ⟨components, selected, selectedGood, selectedLarge, onCurve⟩ :=
    published lanes masked many
  obtain ⟨alpha, alphaSelected, notResolving⟩ :=
    exists_selected_not_resolving binding.finalLinear lanes components
      selected selectedLarge
  have alphaBadMember : alpha ∈
      oneFoldBadChallenges schedule encoders binding transcript :=
    selectedGood alphaSelected
  have alphaBad : OneFoldBadResponse schedule encoders binding transcript alpha :=
    (mem_oneFoldBadChallenges_iff schedule encoders binding transcript alpha).mp
      alphaBadMember
  have maskedValid : ValidResponse binding.finalLinear outputAgreementThreshold
      lanes masked alpha :=
    (mem_goodChallenges_iff binding.finalLinear outputAgreementThreshold
      lanes masked alpha).mp alphaBadMember
  have maskedSubset : masked.support alpha ⊆
      jointAgreementSet binding.finalLinear lanes components :=
    support_subset_jointAgreement binding.finalLinear outputAgreementThreshold
      lanes masked components alpha maskedValid (onCurve alpha alphaSelected)
      notResolving
  have supportEq : masked.support alpha = strategy.support alpha := by
    change (if OneFoldBadResponse schedule encoders binding transcript alpha then
        consistencySet (scheduleAtAlpha schedule alpha) encoders transcript
      else ∅) =
        consistencySet (scheduleAtAlpha schedule alpha) encoders transcript
    simp [alphaBad]
  have strategySubset : strategy.support alpha ⊆
      jointAgreementSet binding.finalLinear lanes components := by
    rw [← supportEq]
    exact maskedSubset
  let candidate : InitialCoefficients K :=
    assembleCoefficientLanes components
  have reconstruct : ∀ index ∈ strategy.support alpha, ∀ slot : Fin 4,
      encoders.initial candidate (childIndex index slot) =
        transcript.initial (childIndex index slot) := by
    intro index indexMember slot
    exact initial_assembled_eq_received_on_joint schedule encoders binding
      transcript components index (strategySubset indexMember) slot
  have consistent : ∀ index ∈ strategy.support alpha,
      QueryConsistent (scheduleAtAlpha schedule alpha) encoders transcript index := by
    intro index indexMember
    change index ∈ consistencySet (scheduleAtAlpha schedule alpha)
      encoders transcript at indexMember
    simpa [consistencySet] using indexMember
  have supportedCard : (strategy.support alpha).card * 4 ≤
      (supportedAgreementInitial (scheduleAtAlpha schedule alpha)
        encoders transcript candidate).card :=
    four_response_fibres_card_le_supportedAgreement
      (scheduleAtAlpha schedule alpha) encoders transcript candidate
      (strategy.support alpha) consistent reconstruct
  have supportLarge : 9557 < (strategy.support alpha).card :=
    alphaBad.1.1
  have candidateSupported : SupportedNearInitial
      (scheduleAtAlpha schedule alpha) encoders transcript candidate := by
    unfold SupportedNearInitial
    have : 38230 ≤ (strategy.support alpha).card * 4 := by omega
    exact this.trans supportedCard
  have candidateFold : foldInitial (scheduleAtAlpha schedule alpha) candidate =
      transcript.disclosedFinal := by
    have foldEq := fold_assembled_eq_candidate_of_onCurve
      binding.finalLinear binding.finalInjective masked components alpha
        (onCurve alpha alphaSelected)
    change coefficientFoldLayer 256 alpha candidate =
      transcript.disclosedFinal
    change coefficientFoldLayer 256 alpha
        (assembleCoefficientLanes components) = transcript.disclosedFinal
    simpa [masked, oneFoldBadMaskedStrategy, strategy,
      restoredOneFoldStrategy] using foldEq
  exact alphaBad.2.2 ⟨candidate, candidateSupported, candidateFold⟩

/-- Pointwise inclusion for the actual accepted challenge. -/
theorem oneFoldReductionFailure_mem_badChallenges
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K)
    (failure : OneFoldReductionFailure schedule encoders transcript) :
    schedule.alpha ∈
      oneFoldBadChallenges schedule encoders binding transcript := by
  rw [mem_oneFoldBadChallenges_iff]
  constructor
  · simpa only [scheduleAtAlpha_original] using
      restoredOneFoldStrategy_valid schedule encoders binding transcript
        schedule.alpha (by simpa only [scheduleAtAlpha_original] using failure.1)
  · simpa only [scheduleAtAlpha_original] using failure

/-- The actual K1.3 one-fold failure is therefore charged once to the exact
published degree-three cap. -/
theorem oneFoldReductionFailure_has_published_cap
    [Fintype K] [DecidableEq K]
    (schedule : OneFoldSchedule F K) (encoders : CodeEncoders K)
    (binding : OneFoldAlgebraBinding schedule encoders)
    (transcript : IdealTranscript K)
    (published : PublishedOneFoldCurveDecodability binding.finalLinear)
    (failure : OneFoldReductionFailure schedule encoders transcript) :
    schedule.alpha ∈
        oneFoldBadChallenges schedule encoders binding transcript ∧
      (oneFoldBadChallenges schedule encoders binding transcript).card ≤
        foldChallengeCap :=
  ⟨oneFoldReductionFailure_mem_badChallenges schedule encoders binding
      transcript failure,
    oneFoldBadChallenges_card_le schedule encoders binding transcript published⟩

#print axioms curve_oneFoldDecodedLanes_eq_circleFold
#print axioms initial_assembled_eq_received_on_joint
#print axioms four_response_fibres_card_le_supportedAgreement
#print axioms restoredOneFoldStrategy_valid
#print axioms oneFoldBadChallenges_card_le
#print axioms oneFoldReductionFailure_has_published_cap

end

end AspisK1.V7Tag73ExactOneFoldRestorationStrategy
