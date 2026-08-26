import AspisFormal.V6Width29CorrelatedAgreement

/-!
# Constrained width-29 correlated extraction

The ordinary width-29 curve theorem permits the response strategy to choose a
different close codeword after seeing `gamma`.  Consequently, a root count for
one locally selected component tuple is not by itself a probability bound.

This file proves the stronger statement needed by K1.5.  Suppose every close
response also satisfies any family of linear-functional batching equations
(point evaluations are the production instance).  If the constrained response
set exceeds the published curve-decoding cap, the one fixed component tuple
returned by the correlated theorem satisfies every functional coordinate
exactly.  No decoder-list union and no post-selected root count is used.
-/

set_option autoImplicit false

namespace AspisV6Width29ConstrainedFunctionalExtraction

open AspisV6Width29CorrelatedAgreement

variable {K Domain Message Index : Type*}
  [Field K] [Fintype K] [DecidableEq K]
  [Fintype Domain] [DecidableEq Domain]

/-- A response candidate obeys the scalar-power batch of each claimed linear
functional. -/
def Width29FunctionalConstraint
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) : Prop :=
  ∀ index, functional index (strategy.candidate gamma) =
    width29Batch (claimed index) gamma

/-- Restrict a response strategy to challenges satisfying all functional
equations while retaining the same candidate. -/
noncomputable def constrainedWidth29Strategy
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message) :
    Width29ProximateStrategy K Domain Message := by
  classical
  exact {
    candidate := strategy.candidate
    support := fun gamma =>
      if Width29FunctionalConstraint functional claimed strategy gamma then
        strategy.support gamma
      else
        ∅
  }

@[simp] theorem constrainedWidth29Strategy_candidate
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K) :
    (constrainedWidth29Strategy functional claimed strategy).candidate gamma =
      strategy.candidate gamma := by
  rfl

theorem mem_constrained_good_implies_constraint
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K)
    (member : gamma ∈ width29GoodChallenges encoder agreementThreshold lanes
      (constrainedWidth29Strategy functional claimed strategy)) :
    Width29FunctionalConstraint functional claimed strategy gamma := by
  classical
  have valid := (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
    (constrainedWidth29Strategy functional claimed strategy) gamma).mp member
  by_contra missing
  have emptySupport :
      (constrainedWidth29Strategy functional claimed strategy).support gamma =
        ∅ := by
    simp [constrainedWidth29Strategy, missing]
  have impossible : agreementThreshold < 0 := by
    simpa only [emptySupport, Finset.card_empty] using valid.2.1
  exact (Nat.not_lt_zero _ impossible).elim

theorem mem_constrained_good_implies_original_valid
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (gamma : K)
    (member : gamma ∈ width29GoodChallenges encoder agreementThreshold lanes
      (constrainedWidth29Strategy functional claimed strategy)) :
    Width29ValidResponse encoder agreementThreshold lanes strategy gamma := by
  classical
  have constraint := mem_constrained_good_implies_constraint encoder
    agreementThreshold lanes functional claimed strategy gamma member
  have valid := (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
    (constrainedWidth29Strategy functional claimed strategy) gamma).mp member
  have supportExact :
      (constrainedWidth29Strategy functional claimed strategy).support gamma =
        strategy.support gamma := by
    simp [constrainedWidth29Strategy, constraint]
  constructor
  · simpa only [supportExact] using valid.2.1
  · intro point pointInSupport
    have pointInConstrained : point ∈
        (constrainedWidth29Strategy functional claimed strategy).support gamma := by
      simpa only [supportExact] using pointInSupport
    simpa only [constrainedWidth29Strategy_candidate] using
      valid.2.2 point pointInConstrained

/-- A large selected set from the published theorem fixes every functional
coordinate of its one shared component tuple. -/
theorem large_constrained_selected_fix_all_functionals
    (encoder : Message → Domain → K)
    (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (combine : (Fin 29 → Message) → K → Message)
    (encoderInjective : Function.Injective encoder)
    (encoderCombine : ∀ components gamma,
      encoder (combine components gamma) =
        fun point => width29CurveValue
          (fun lane => encoder (components lane)) gamma point)
    (functionalCombine : ∀ index components gamma,
      functional index (combine components gamma) =
        width29Batch (fun lane => functional index (components lane)) gamma)
    (domainNonempty : 0 < Fintype.card Domain)
    (components : Fin 29 → Message)
    (selected : Finset K)
    (selectedSubset : selected ⊆
      width29GoodChallenges encoder agreementThreshold lanes
        (constrainedWidth29Strategy functional claimed strategy))
    (selectedLarge : 28 * Fintype.card Domain < selected.card)
    (onCurve : ∀ gamma ∈ selected,
      Width29CandidateOnCurve encoder
        (constrainedWidth29Strategy functional claimed strategy)
        components gamma) :
    ∀ index, claimed index = fun lane => functional index (components lane) := by
  classical
  intro index
  by_contra differs
  let discrepancy : Fin 29 → K := fun lane =>
    claimed index lane - functional index (components lane)
  have discrepancyNonzero : discrepancy ≠ 0 := by
    intro zero
    apply differs
    funext lane
    have laneZero := congrFun zero lane
    exact sub_eq_zero.mp laneZero
  have selectedInRoots : selected ⊆
      width29NonzeroCollisionSet discrepancy := by
    intro gamma gammaSelected
    have constrainedMember := selectedSubset gammaSelected
    have constraint := mem_constrained_good_implies_constraint encoder
      agreementThreshold lanes functional claimed strategy gamma
      constrainedMember
    have candidateOnCurve := onCurve gamma gammaSelected
    have candidateEq : strategy.candidate gamma =
        combine components gamma := by
      apply encoderInjective
      calc
        encoder (strategy.candidate gamma) =
            encoder
              ((constrainedWidth29Strategy functional claimed strategy).candidate
                gamma) := by rfl
        _ = fun point => width29CurveValue
              (fun lane => encoder (components lane)) gamma point :=
            candidateOnCurve
        _ = encoder (combine components gamma) :=
            (encoderCombine components gamma).symm
    have batchZero : width29Batch discrepancy gamma = 0 := by
      have constrainedAt := constraint index
      rw [candidateEq, functionalCombine] at constrainedAt
      unfold discrepancy
      simp only [width29Batch] at constrainedAt ⊢
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr constrainedAt.symm
    have gammaNonzero :=
      (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
        (constrainedWidth29Strategy functional claimed strategy) gamma).mp
        constrainedMember |>.1
    simp only [width29NonzeroCollisionSet, Finset.mem_filter,
      Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨gammaNonzero, batchZero⟩
  have selectedCardLe : selected.card ≤ 28 :=
    (Finset.card_le_card selectedInRoots).trans
      (width29_nonzero_collision_card_le discrepancy discrepancyNonzero)
  have twentyEightLt : 28 < selected.card := by
    have : 28 ≤ 28 * Fintype.card Domain := by
      nlinarith
    omega
  omega

/-- The constrained correlated-decoding theorem.

`combine`, `encoderCombine`, and `functionalCombine` are the ordinary
linearity facts of the concrete coefficient-message encoder.  The theorem's
conclusion is a single component tuple whose individual functional values are
the complete claimed vectors.  In particular, the tuple is not selected as a
function of the sampled `gamma`. -/
theorem constrained_width29_many_responses_fix_all_functionals
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat)
    (published : Width29CurveDecodable encoder agreementThreshold
      challengeThreshold)
    (lanes : Fin 29 → Domain → K)
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (combine : (Fin 29 → Message) → K → Message)
    (encoderInjective : Function.Injective encoder)
    (encoderCombine : ∀ components gamma,
      encoder (combine components gamma) =
        fun point => width29CurveValue
          (fun lane => encoder (components lane)) gamma point)
    (functionalCombine : ∀ index components gamma,
      functional index (combine components gamma) =
        width29Batch (fun lane => functional index (components lane)) gamma)
    (domainNonempty : 0 < Fintype.card Domain)
    (many : challengeThreshold <
      (width29GoodChallenges encoder agreementThreshold lanes
        (constrainedWidth29Strategy functional claimed strategy)).card) :
    ∃ components : Fin 29 → Message,
      ∀ index, claimed index = fun lane => functional index (components lane) := by
  classical
  obtain ⟨components, selected, selectedSubset, selectedLarge, onCurve⟩ :=
    published lanes (constrainedWidth29Strategy functional claimed strategy)
      many
  exact ⟨components,
    large_constrained_selected_fix_all_functionals encoder agreementThreshold
      lanes functional claimed strategy combine encoderInjective encoderCombine
      functionalCombine domainNonempty components selected selectedSubset
      selectedLarge onCurve⟩

/-- The same theorem retaining one concrete good restored challenge.  Its
response has a common agreement support for the fixed component tuple, so it
can be packaged directly as the component part of a K1.4 certificate. -/
theorem constrained_width29_many_responses_extract_fixed_components
    (encoder : Message → Domain → K)
    (agreementThreshold challengeThreshold : Nat)
    (published : Width29CurveDecodable encoder agreementThreshold
      challengeThreshold)
    (lanes : Fin 29 → Domain → K)
    (functional : Index → Message → K)
    (claimed : Index → Fin 29 → K)
    (strategy : Width29ProximateStrategy K Domain Message)
    (combine : (Fin 29 → Message) → K → Message)
    (encoderInjective : Function.Injective encoder)
    (encoderCombine : ∀ components gamma,
      encoder (combine components gamma) =
        fun point => width29CurveValue
          (fun lane => encoder (components lane)) gamma point)
    (functionalCombine : ∀ index components gamma,
      functional index (combine components gamma) =
        width29Batch (fun lane => functional index (components lane)) gamma)
    (domainNonempty : 0 < Fintype.card Domain)
    (many : challengeThreshold <
      (width29GoodChallenges encoder agreementThreshold lanes
        (constrainedWidth29Strategy functional claimed strategy)).card) :
    ∃ (components : Fin 29 → Message) (gamma : K),
      gamma ∈ width29GoodChallenges encoder agreementThreshold lanes
        (constrainedWidth29Strategy functional claimed strategy) ∧
      Width29ValidResponse encoder agreementThreshold lanes strategy gamma ∧
      Width29CandidateOnCurve encoder strategy components gamma ∧
      strategy.support gamma ⊆
        width29JointAgreementSet encoder lanes components ∧
      ∀ index, claimed index =
        fun lane => functional index (components lane) := by
  classical
  obtain ⟨components, selected, selectedSubset, selectedLarge, onCurve⟩ :=
    published lanes (constrainedWidth29Strategy functional claimed strategy)
      many
  have exactFunctionals :=
    large_constrained_selected_fix_all_functionals encoder agreementThreshold
      lanes functional claimed strategy combine encoderInjective encoderCombine
      functionalCombine domainNonempty components selected selectedSubset
      selectedLarge onCurve
  obtain ⟨gamma, gammaSelected, notResolving⟩ :=
    exists_selected_not_width29Resolving encoder lanes components selected
      selectedLarge
  have constrainedMember := selectedSubset gammaSelected
  have originalValid := mem_constrained_good_implies_original_valid encoder
    agreementThreshold lanes functional claimed strategy gamma
    constrainedMember
  have gammaNonzero :=
    (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
      (constrainedWidth29Strategy functional claimed strategy) gamma).mp
      constrainedMember |>.1
  have constrainedOnCurve := onCurve gamma gammaSelected
  have originalOnCurve :
      Width29CandidateOnCurve encoder strategy components gamma := by
    simpa only [Width29CandidateOnCurve,
      constrainedWidth29Strategy_candidate] using constrainedOnCurve
  have shared := width29Support_subset_jointAgreement encoder
    agreementThreshold lanes strategy components gamma gammaNonzero
    originalValid originalOnCurve notResolving
  exact ⟨components, gamma, constrainedMember, originalValid, originalOnCurve,
    shared, exactFunctionals⟩

#print axioms mem_constrained_good_implies_constraint
#print axioms mem_constrained_good_implies_original_valid
#print axioms large_constrained_selected_fix_all_functionals
#print axioms constrained_width29_many_responses_fix_all_functionals
#print axioms constrained_width29_many_responses_extract_fixed_components

end AspisV6Width29ConstrainedFunctionalExtraction
