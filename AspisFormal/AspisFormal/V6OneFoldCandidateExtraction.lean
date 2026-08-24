import AspisFormal.V6OneFoldParameterAudit
import AspisFormal.V5WithoutReplacementQuerySoundness

/-!
# Deterministic candidate extraction for the V6 one-fold model

This file defines the exact ideal arithmetic check proposed for V6: one
authenticated initial word, one circle-to-line fold, and one disclosed
256-coefficient final object. It then proves the deterministic inclusion that
the probability argument will need.

If all sixteen ideal queries accept, and neither the query miss, the published
one-fold reduction failure, nor the initial-list overflow occurs, then one
member of a single at-most-100 initial candidate list folds exactly to the
disclosed final coefficients.

The result does not assign probabilities to the three failure events. The
one-fold reduction probability is where the S-two/Bordage theorem application
must enter; the query probability must include compact-sampler conditioning;
and Merkle/transcript/Rust connections come later.
-/

set_option maxRecDepth 10000

namespace AspisV6OneFoldCandidateExtraction

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldParameterAudit

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

abbrev InitialCoefficients (K : Type*) := Fin 1024 → K
abbrev FinalCoefficients (K : Type*) := Fin 256 → K
abbrev InitialWord (K : Type*) := Fin 1048576 → K
abbrev FinalWord (K : Type*) := Fin 262144 → K

/-- The sole fold challenge and the inverse tables used by the ideal verifier. -/
structure OneFoldSchedule (F K : Type*) where
  alpha : K
  circleInv2x : Fin 262144 → F
  circleInv2y : Fin 262144 → F

/-- The intended initial circle encoder and final degree-255 line encoder. -/
structure CodeEncoders (K : Type*) where
  initial : InitialCoefficients K → InitialWord K
  final : FinalCoefficients K → FinalWord K

/-- The authenticated initial word and disclosed terminal coefficients. -/
structure IdealTranscript (K : Type*) where
  initial : InitialWord K
  disclosedFinal : FinalCoefficients K

def foldInitial (schedule : OneFoldSchedule F K)
    (coefficients : InitialCoefficients K) : FinalCoefficients K :=
  coefficientFoldLayer 256 schedule.alpha coefficients

/-- The exact arithmetic equality checked at one V6 query fibre. -/
def QueryConsistent
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (query : Fin 262144) : Prop :=
  circleFoldLayer 262144 schedule.alpha
      schedule.circleInv2x schedule.circleInv2y transcript.initial query =
    encoders.final transcript.disclosedFinal query

section FiniteField

variable [Fintype K] [DecidableEq K]

noncomputable def consistencySet
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Finset (Fin 262144) := by
  classical
  exact Finset.univ.filter (QueryConsistent schedule encoders transcript)

def IdealAccepts
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 16 262144) : Prop :=
  ∀ i, QueryConsistent schedule encoders transcript (queries i)

theorem accepted_queries_mem_consistencySet
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 16 262144)
    (haccepts : IdealAccepts schedule encoders transcript queries) :
    AllQueriesIn (consistencySet schedule encoders transcript) queries := by
  intro i
  simpa [consistencySet] using haccepts i

/-- Every accepted query landed in a consistency set no larger than the
integer part of `(7/192) * 2^18`. -/
def QueryPhaseFailure
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 16 262144) : Prop :=
  IdealAccepts schedule encoders transcript queries ∧
    (consistencySet schedule encoders transcript).card ≤ 9557

theorem dense_consistency_of_accepts_not_queryFailure
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 16 262144)
    (haccepts : IdealAccepts schedule encoders transcript queries)
    (hnot : ¬ QueryPhaseFailure schedule encoders transcript queries) :
    9557 < (consistencySet schedule encoders transcript).card := by
  by_contra hsmall
  exact hnot ⟨haccepts, Nat.le_of_not_gt hsmall⟩

/-- Exact finite bound for sixteen uniform queries without replacement and
34 bits of final work, before compact-frontier conditioning. -/
theorem q16_raw_miss_div_work_le
    (bad : Finset (Fin 262144)) (hcard : bad.card ≤ 9557) :
    idealMissProbability (q := 16) bad / 2 ^ 34 ≤
      (1 : Real) / 2 ^ 110 := by
  have hmiss := ideal_miss_probability_mono_card
    (q := 16) (cap := 9557) bad hcard (by norm_num)
  calc
    idealMissProbability (q := 16) bad / 2 ^ 34 ≤
        (((9557 : Nat).descFactorial 16 : Nat) : Real) /
          ((262144 : Nat).descFactorial 16 : Nat) / 2 ^ 34 :=
      div_le_div_of_nonneg_right hmiss (by positivity)
    _ ≤ (1 : Real) / 2 ^ 110 := by
      norm_num [Nat.descFactorial]

/-- The compact sampler costs less than two bits in the rounded query bound.
If its compact event has probability at least `3/8`, elementary conditioning
and the exact descending-factorial calculation give a `2^-109` query-plus-work
bound. The probability premise is not inferred from the screening script. -/
theorem q16_conditioned_miss_div_work_le
    (bad : Finset (Fin 262144)) (hcard : bad.card ≤ 9557)
    (compactProbability conditionedProbability : Real)
    (hcompact : (3 : Real) / 8 ≤ compactProbability)
    (hcondition : conditionedProbability ≤
      (idealMissProbability (q := 16) bad / 2 ^ 34) /
        compactProbability) :
    conditionedProbability ≤ (1 : Real) / 2 ^ 109 := by
  have hp : 0 < compactProbability := by linarith
  have hmiss := ideal_miss_probability_mono_card
    (q := 16) (cap := 9557) bad hcard (by norm_num)
  let capRatio : Real :=
    (((9557 : Nat).descFactorial 16 : Nat) : Real) /
      ((262144 : Nat).descFactorial 16 : Nat) / 2 ^ 34
  have hraw : idealMissProbability (q := 16) bad / 2 ^ 34 ≤ capRatio := by
    exact div_le_div_of_nonneg_right hmiss (by positivity)
  have hcapnonneg : 0 ≤ capRatio := by
    dsimp [capRatio]
    positivity
  calc
    conditionedProbability ≤
        (idealMissProbability (q := 16) bad / 2 ^ 34) /
          compactProbability := hcondition
    _ ≤ capRatio / compactProbability :=
      div_le_div_of_nonneg_right hraw hp.le
    _ ≤ capRatio / ((3 : Real) / 8) :=
      div_le_div_of_nonneg_left hcapnonneg (by norm_num) hcompact
    _ ≤ (1 : Real) / 2 ^ 109 := by
      dsimp [capRatio]
      norm_num [Nat.descFactorial]

noncomputable def agreementSet {n : Nat}
    (received encoded : Fin n → K) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => received i = encoded i

def NearInitial
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K) : Prop :=
  38230 ≤
    (agreementSet transcript.initial (encoders.initial candidate)).card

noncomputable def supportedAgreementInitial
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K) : Finset (Fin 1048576) := by
  classical
  exact Finset.univ.filter fun i =>
    QueryConsistent schedule encoders transcript
        ⟨i.val / 4, by omega⟩ ∧
      transcript.initial i = encoders.initial candidate i

def SupportedNearInitial
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K) : Prop :=
  38230 ≤
    (supportedAgreementInitial schedule encoders transcript candidate).card

theorem SupportedNearInitial.nearInitial
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K)
    (hsupported : SupportedNearInitial schedule encoders transcript candidate) :
    NearInitial encoders transcript candidate := by
  have hsubset :
      supportedAgreementInitial schedule encoders transcript candidate ⊆
        agreementSet transcript.initial (encoders.initial candidate) := by
    intro i hi
    simp only [supportedAgreementInitial, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi
    simpa [agreementSet] using hi.2
  exact hsupported.trans (Finset.card_le_card hsubset)

noncomputable def initialCandidateList
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) :
    Finset (InitialCoefficients K) := by
  classical
  exact Finset.univ.filter (NearInitial encoders transcript)

@[simp] theorem mem_initialCandidateList_iff
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (candidate : InitialCoefficients K) :
    candidate ∈ initialCandidateList encoders transcript ↔
      NearInitial encoders transcript candidate := by
  simp [initialCandidateList]

/-- Exact distance premise needed from the intended initial circle encoder. -/
def InitialEncoderOverlapCap (encoders : CodeEncoders K) : Prop :=
  ∀ c d : InitialCoefficients K, c ≠ d →
    (Finset.univ.filter fun i : Fin 1048576 =>
      encoders.initial c i = encoders.initial d i).card ≤ 1024

theorem initialCandidateList_card_le_100
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (hoverlap : InitialEncoderOverlapCap encoders) :
    (initialCandidateList encoders transcript).card ≤ 100 := by
  classical
  let Candidate :=
    {c : InitialCoefficients K // c ∈ initialCandidateList encoders transcript}
  let candidateAgreement : Candidate → Finset (Fin 1048576) :=
    fun c => agreementSet transcript.initial (encoders.initial c.1)
  have hlarge : ∀ c : Candidate, 38230 ≤ (candidateAgreement c).card := by
    intro c
    exact (mem_initialCandidateList_iff encoders transcript c.1).1 c.2
  have hpairs : ∀ c d : Candidate, c ≠ d →
      ((candidateAgreement c) ∩ (candidateAgreement d)).card ≤ 1024 := by
    intro c d hcd
    have hvalues : c.1 ≠ d.1 := by
      intro heq
      apply hcd
      exact Subtype.ext heq
    calc
      ((candidateAgreement c) ∩ (candidateAgreement d)).card ≤
          (Finset.univ.filter fun i : Fin 1048576 =>
            encoders.initial c.1 i = encoders.initial d.1 i).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_inter, candidateAgreement, agreementSet,
          Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi.1.symm.trans hi.2
      _ ≤ 1024 := hoverlap c.1 d.1 hvalues
  have hlt : Fintype.card Candidate < 101 :=
    initial_list_card_lt_101 candidateAgreement hlarge hpairs
  have hcard : Fintype.card Candidate =
      (initialCandidateList encoders transcript).card := by
    simp only [Candidate, Fintype.card_coe]
  rw [← hcard]
  omega

/-- Dense accepting consistency did not yield a close initial candidate whose
single natural coefficient fold is the disclosed terminal object. The cited
one-round reduction must bound this event; it is not assumed away. -/
def OneFoldReductionFailure
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Prop :=
  9557 < (consistencySet schedule encoders transcript).card ∧
    ¬ ∃ candidate,
      SupportedNearInitial schedule encoders transcript candidate ∧
        foldInitial schedule candidate = transcript.disclosedFinal

def InitialListCapFailure
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Prop :=
  100 < (initialCandidateList encoders transcript).card

/-- The deterministic one-fold inclusion needed before assigning any
probability: outside three named failures, ideal acceptance supplies one
member of a single at-most-100 initial list whose fold is exactly the disclosed
final vector. -/
theorem accepted_ideal_onefold_supplies_matching_initial_candidate
    (schedule : OneFoldSchedule F K)
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 16 262144)
    (haccepts : IdealAccepts schedule encoders transcript queries)
    (hquery : ¬ QueryPhaseFailure schedule encoders transcript queries)
    (hfold : ¬ OneFoldReductionFailure schedule encoders transcript)
    (hcap : ¬ InitialListCapFailure encoders transcript) :
    ∃ candidate,
      candidate ∈ initialCandidateList encoders transcript ∧
      foldInitial schedule candidate = transcript.disclosedFinal ∧
      (initialCandidateList encoders transcript).card ≤ 100 := by
  have hdense := dense_consistency_of_accepts_not_queryFailure
    schedule encoders transcript queries haccepts hquery
  have hexists : ∃ candidate,
      SupportedNearInitial schedule encoders transcript candidate ∧
        foldInitial schedule candidate = transcript.disclosedFinal := by
    by_contra hnone
    exact hfold ⟨hdense, hnone⟩
  obtain ⟨candidate, hsupported, hfinal⟩ := hexists
  refine ⟨candidate, ?_, hfinal, Nat.le_of_not_gt hcap⟩
  exact (mem_initialCandidateList_iff encoders transcript candidate).2
    (SupportedNearInitial.nearInitial schedule encoders transcript candidate
      hsupported)

theorem initial_list_cap_failure_impossible_of_overlap
    (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (hoverlap : InitialEncoderOverlapCap encoders) :
    ¬ InitialListCapFailure encoders transcript := by
  exact Nat.not_lt_of_ge
    (initialCandidateList_card_le_100 encoders transcript hoverlap)

/-! ## Audit -/

#print axioms initialCandidateList_card_le_100
#print axioms q16_raw_miss_div_work_le
#print axioms q16_conditioned_miss_div_work_le
#print axioms accepted_ideal_onefold_supplies_matching_initial_candidate
#print axioms initial_list_cap_failure_impossible_of_overlap

end FiniteField

end AspisV6OneFoldCandidateExtraction
