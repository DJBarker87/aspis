import AspisFormal.V5ComponentCConcreteFoldLinearity
import AspisFormal.V5FriListCap
import AspisFormal.V5WithoutReplacementQuerySoundness

/-!
# Coherent candidate extraction for the ideal V5 FRI verifier

This file isolates the deterministic part of the missing V5 FRI argument.
It models the four committed words read by `check_v5_fri_queries`, the exact
circle/line fold equations checked for each of the eighteen query fibres, the
published four-coefficient final polynomial, and the four coefficient lists
used by the S-two round-reduction argument.

The central theorem does not assume that a matching initial candidate exists.
Instead it excludes six concrete FRI-side failures:

* all eighteen accepted queries landed in a consistency set of at most 6082
  initial fibres;
* at one of the four fold rounds, a close polynomial on the next layer has no
  close predecessor under the exact natural coefficient fold; and
* the initial Guruswami--Sudan list contains more than 240 close polynomials.

Outside those events, Lean selects predecessors backwards from the published
final polynomial and constructs one coherent chain

`1024 -> 256 -> 64 -> 16 -> 4`.

The last equality is the exact `finalCoefficientMap` used by the maintained
V5 model, so the result supplies the matching candidate required by the
custom relation proof.  Only the initial list contributes a factor: later
layers are witnesses on the same backwards chain, not independently chosen
list indices.

## Deliberate boundary

The theorem below is the deterministic inclusion layer.  It does not prove
the probability bounds for the four predecessor failures.  Those are the
round-reduction conclusions of S-two's multi-domain circle-FRI theorem.  It
also does not prove that a successful raw Merkle opening equals the committed
word modeled here, or that Fiat--Shamir and grinding produce the ideal random
challenges.  The exact remaining premises are therefore:

1. Merkle binding from accepted raw openings to the four ideal words;
2. applicability of the S-two batching/folding theorem to the deployed circle
   encoders, agreement predicates, and four arity-four challenges;
3. the Guruswami--Sudan theorem turning the checked numeric expression below
   into the actual `<= 240` initial-list cardinality; and
4. the random-oracle/work argument for the query and round-reduction event
   probabilities.

None of those premises mentions the relation repair event or assumes the
existence of a matching Tag-67 candidate.
-/

namespace AspisV5FriCoherentCandidateExtraction

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5WithoutReplacementQuerySoundness

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-! ## Exact V5 dimensions -/

abbrev Coeff0 (K : Type*) := Fin 1024 -> K
abbrev Coeff1 (K : Type*) := Fin 256 -> K
abbrev Coeff2 (K : Type*) := Fin 64 -> K
abbrev Coeff3 (K : Type*) := Fin 16 -> K
abbrev Coeff4 (K : Type*) := Fin 4 -> K

abbrev Word0 (K : Type*) := Fin 524288 -> K
abbrev Word1 (K : Type*) := Fin 131072 -> K
abbrev Word2 (K : Type*) := Fin 32768 -> K
abbrev Word3 (K : Type*) := Fin 8192 -> K

/-- The four code encoders whose close codewords form the decoder lists.

The first encoder is the batched circle encoder; the next three are the line
encoders at the committed V5 dimensions.  Their concrete algebraic
definitions and the theorem that the deployed folds commute with them are
part of the external S-two/circle-code applicability boundary. -/
structure CodeEncoders (K : Type*) where
  layer0 : Coeff0 K -> Word0 K
  layer1 : Coeff1 K -> Word1 K
  layer2 : Coeff2 K -> Word2 K
  layer3 : Coeff3 K -> Word3 K

/-- The four authenticated words and the plain final polynomial seen by the
ideal arithmetic verifier. -/
structure IdealTranscript (K : Type*) where
  layer0 : Word0 K
  layer1 : Word1 K
  layer2 : Word2 K
  layer3 : Word3 K
  publishedFinal : Coeff4 K

/-! ## The exact coherent coefficient chain -/

def fold0 (schedule : FixedSchedule F K) (c : Coeff0 K) : Coeff1 K :=
  coefficientFoldLayer 256 (schedule.alpha 0) c

def fold1 (schedule : FixedSchedule F K) (c : Coeff1 K) : Coeff2 K :=
  coefficientFoldLayer 64 (schedule.alpha 1) c

def fold2 (schedule : FixedSchedule F K) (c : Coeff2 K) : Coeff3 K :=
  coefficientFoldLayer 16 (schedule.alpha 2) c

def fold3 (schedule : FixedSchedule F K) (c : Coeff3 K) : Coeff4 K :=
  coefficientFoldLayer 4 (schedule.alpha 3) c

/-- One initial coefficient vector and its deterministic four-fold chain. -/
structure CoherentChain (schedule : FixedSchedule F K) where
  initial : Coeff0 K
  layer1 : Coeff1 K
  layer2 : Coeff2 K
  layer3 : Coeff3 K
  final : Coeff4 K
  layer1_eq : layer1 = fold0 schedule initial
  layer2_eq : layer2 = fold1 schedule layer1
  layer3_eq : layer3 = fold2 schedule layer2
  final_eq : final = fold3 schedule layer3

/-- Build the unique coherent chain from one initial vector. -/
def CoherentChain.fromInitial
    (schedule : FixedSchedule F K) (initial : Coeff0 K) :
    CoherentChain schedule where
  initial := initial
  layer1 := fold0 schedule initial
  layer2 := fold1 schedule (fold0 schedule initial)
  layer3 := fold2 schedule (fold1 schedule (fold0 schedule initial))
  final := fold3 schedule
    (fold2 schedule (fold1 schedule (fold0 schedule initial)))
  layer1_eq := rfl
  layer2_eq := rfl
  layer3_eq := rfl
  final_eq := rfl

/-- The maintained final coefficient map is exactly the four natural folds
used in `CoherentChain`. -/
theorem finalCoefficientMap_eq_four_folds
    (schedule : FixedSchedule F K) (initial : Coeff0 K) :
    finalCoefficientMap schedule initial =
      fold3 schedule (fold2 schedule (fold1 schedule (fold0 schedule initial))) := by
  rfl

/-! ## Exact ideal query checks -/

/-- Projection of one initial query fibre to the first later-layer fibre. -/
def queryParent1 (q : Fin 131072) : Fin 32768 :=
  ⟨q.val / 4, by omega⟩

/-- Projection to the second later-layer fibre. -/
def queryParent2 (q : Fin 131072) : Fin 8192 :=
  ⟨q.val / 16, by omega⟩

/-- Projection to the final line-domain position. -/
def queryParent3 (q : Fin 131072) : Fin 2048 :=
  ⟨q.val / 64, by omega⟩

/-- The initial query fibre containing one layer-zero symbol. -/
def queryFibreOfSymbol (i : Fin 524288) : Fin 131072 :=
  ⟨i.val / 4, by omega⟩

/-- The four arithmetic equalities checked on one ideal query path.

The indices are the Rust indices `q`, `q >> 2`, `q >> 4`, and `q >> 6`.
Each layer map uses the exact child order and twiddle order already proved in
`V5ComponentCConcreteFoldLinearity`. -/
def QueryConsistent
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (q : Fin 131072) : Prop :=
  circleFoldLayer 131072 (schedule.alpha 0)
      schedule.circleInv2x schedule.circleInv2y transcript.layer0 q =
        transcript.layer1 q /\
  lineFoldLayer 32768 (schedule.alpha 1) schedule.line1Inverse
      transcript.layer1 (queryParent1 q) = transcript.layer2 (queryParent1 q) /\
  lineFoldLayer 8192 (schedule.alpha 2) schedule.line2Inverse
      transcript.layer2 (queryParent2 q) = transcript.layer3 (queryParent2 q) /\
  lineFoldLayer 2048 (schedule.alpha 3) schedule.line3Inverse
      transcript.layer3 (queryParent3 q) =
    finalTensorValue
      (algebraMap F K (schedule.finalX (queryParent3 q)))
      transcript.publishedFinal

section FiniteField

variable [Fintype K] [DecidableEq K]

/-- All initial fibres on which the complete four-round arithmetic path is
consistent with the published final polynomial. -/
noncomputable def consistencySet
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter (QueryConsistent schedule transcript)

/-- Exact acceptance predicate for the ideal q18 arithmetic verifier. -/
def IdealAccepts
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072) : Prop :=
  ∀ i, QueryConsistent schedule transcript (queries i)

/-- If the ideal verifier accepts, every sampled query lies in the explicit
global consistency set. -/
theorem accepted_queries_mem_consistencySet
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (haccepts : IdealAccepts schedule transcript queries) :
    AllQueriesIn (consistencySet schedule transcript) queries := by
  intro i
  simpa [consistencySet] using haccepts i

/-- Concrete query-phase miss: every accepted query landed in a global
consistency set containing at most the deployed Johnson cap of 6082 fibres. -/
def QueryPhaseFailure
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072) : Prop :=
  IdealAccepts schedule transcript queries /\
    (consistencySet schedule transcript).card ≤ 6082

/-- A query-phase failure is exactly contained in the already-counted ordered
without-replacement miss event for its concrete consistency set. -/
theorem queryPhaseFailure_implies_ordered_miss
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (hfailure : QueryPhaseFailure schedule transcript queries) :
    AllQueriesIn (consistencySet schedule transcript) queries /\
      (consistencySet schedule transcript).card ≤ 6082 := by
  exact ⟨accepted_queries_mem_consistencySet schedule transcript queries hfailure.1,
    hfailure.2⟩

/-- The existing exact hypergeometric calculation applies directly to the
concrete consistency set appearing in `QueryPhaseFailure`. -/
theorem queryPhaseFailure_ideal_ratio_div_work_le
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (hfailure : QueryPhaseFailure schedule transcript queries) :
    idealMissProbability (q := 18) (consistencySet schedule transcript) / 2 ^ 32 ≤
      (1 : Real) / 2 ^ 111 :=
  deployed_q18_ideal_miss_ratio_div_2pow32_le
    (consistencySet schedule transcript) hfailure.2

/-- Outside the explicit query miss, ideal acceptance forces more than 6082
globally consistent initial fibres. -/
theorem dense_consistency_of_accepts_not_queryFailure
    (schedule : FixedSchedule F K) (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (haccepts : IdealAccepts schedule transcript queries)
    (hnot : ¬ QueryPhaseFailure schedule transcript queries) :
    6082 < (consistencySet schedule transcript).card := by
  by_contra hsmall
  exact hnot ⟨haccepts, Nat.le_of_not_gt hsmall⟩

/-! ## Concrete decoder lists -/

/-- Coordinates where a received word agrees with one encoded candidate. -/
noncomputable def agreementSet {n : Nat}
    (received encoded : Fin n -> K) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => received i = encoded i

/-- The four exact integer agreement floors for the common V5 agreement
fraction `(21/20) * sqrt(1/512)` at word sizes
`524288, 131072, 32768, 8192`.

Thus `cap < agreementSet.card` means strictly more than `alpha * N` symbols,
using integrality.  The square-root inequalities connecting these floors to
the real expression are checked below. -/
def agreementCap0 : Nat := 24328
def agreementCap1 : Nat := 6082
def agreementCap2 : Nat := 1520
def agreementCap3 : Nat := 380

def Near0 (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff0 K) : Prop :=
  agreementCap0 <
    (agreementSet transcript.layer0 (encoders.layer0 candidate)).card

def Near1 (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff1 K) : Prop :=
  agreementCap1 <
    (agreementSet transcript.layer1 (encoders.layer1 candidate)).card

def Near2 (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff2 K) : Prop :=
  agreementCap2 <
    (agreementSet transcript.layer2 (encoders.layer2 candidate)).card

def Near3 (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff3 K) : Prop :=
  agreementCap3 <
    (agreementSet transcript.layer3 (encoders.layer3 candidate)).card

/-! ### Consistency-weighted agreement used by the FRI reductions

S-two's intermediate relations use the conditional success measure of the
remaining query path, rather than unweighted Hamming distance.  Because the
ideal V5 checks are deterministic, that measure can be represented exactly
by lifting every layer back to the `131072` initial query fibres and counting
the fibres whose complete path is consistent.  Layer zero is counted on its
`524288` symbols, with the same consistency bit repeated on the four symbols
of each query fibre. -/

noncomputable def supportedAgreement0
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff0 K) :
    Finset (Fin 524288) := by
  classical
  exact Finset.univ.filter fun i =>
    QueryConsistent schedule transcript (queryFibreOfSymbol i) ∧
      transcript.layer0 i = encoders.layer0 candidate i

noncomputable def supportedAgreement1
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff1 K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter fun q =>
    QueryConsistent schedule transcript q ∧
      transcript.layer1 q = encoders.layer1 candidate q

noncomputable def supportedAgreement2
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff2 K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter fun q =>
    QueryConsistent schedule transcript q ∧
      transcript.layer2 (queryParent1 q) =
        encoders.layer2 candidate (queryParent1 q)

noncomputable def supportedAgreement3
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff3 K) :
    Finset (Fin 131072) := by
  classical
  exact Finset.univ.filter fun q =>
    QueryConsistent schedule transcript q ∧
      transcript.layer3 (queryParent2 q) =
        encoders.layer3 candidate (queryParent2 q)

def SupportedNear0
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff0 K) : Prop :=
  agreementCap0 <
    (supportedAgreement0 schedule encoders transcript candidate).card

def SupportedNear1
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff1 K) : Prop :=
  agreementCap1 <
    (supportedAgreement1 schedule encoders transcript candidate).card

def SupportedNear2
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff2 K) : Prop :=
  agreementCap1 <
    (supportedAgreement2 schedule encoders transcript candidate).card

def SupportedNear3
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff3 K) : Prop :=
  agreementCap1 <
    (supportedAgreement3 schedule encoders transcript candidate).card

/-- Consistency-weighted initial agreement is a subset of ordinary codeword
agreement, so every S-two initial witness is a member of the explicit decoder
list. -/
theorem SupportedNear0.near0
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) (candidate : Coeff0 K)
    (hsupported : SupportedNear0 schedule encoders transcript candidate) :
    Near0 encoders transcript candidate := by
  have hsubset :
      supportedAgreement0 schedule encoders transcript candidate ⊆
        agreementSet transcript.layer0 (encoders.layer0 candidate) := by
    intro i hi
    simp only [supportedAgreement0, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa [agreementSet] using hi.2
  exact hsupported.trans_le (Finset.card_le_card hsubset)

/-- The actual initial decoder list: every 1024-coefficient polynomial whose
encoded word beats the deployed agreement threshold. -/
noncomputable def initialCandidateList
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) :
    Finset (Coeff0 K) := by
  classical
  exact Finset.univ.filter (Near0 encoders transcript)

/-- The initial decoder list depends only on the first committed word.  Later
FRI words and the final polynomial cannot change the candidates over which
the relation union bound is taken. -/
theorem initialCandidateList_eq_of_layer0_eq
    (encoders : CodeEncoders K) (left right : IdealTranscript K)
    (hlayer0 : left.layer0 = right.layer0) :
    initialCandidateList encoders left = initialCandidateList encoders right := by
  classical
  apply Finset.ext
  intro candidate
  simp only [initialCandidateList, Finset.mem_filter, Finset.mem_univ, true_and,
    Near0]
  rw [hlayer0]

noncomputable def layer1CandidateList
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) :
    Finset (Coeff1 K) := by
  classical
  exact Finset.univ.filter (Near1 encoders transcript)

noncomputable def layer2CandidateList
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) :
    Finset (Coeff2 K) := by
  classical
  exact Finset.univ.filter (Near2 encoders transcript)

noncomputable def layer3CandidateList
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) :
    Finset (Coeff3 K) := by
  classical
  exact Finset.univ.filter (Near3 encoders transcript)

@[simp] theorem mem_initialCandidateList_iff
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff0 K) :
    candidate ∈ initialCandidateList encoders transcript ↔
      Near0 encoders transcript candidate := by
  simp [initialCandidateList]

@[simp] theorem mem_layer1CandidateList_iff
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff1 K) :
    candidate ∈ layer1CandidateList encoders transcript ↔
      Near1 encoders transcript candidate := by
  simp [layer1CandidateList]

@[simp] theorem mem_layer2CandidateList_iff
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff2 K) :
    candidate ∈ layer2CandidateList encoders transcript ↔
      Near2 encoders transcript candidate := by
  simp [layer2CandidateList]

@[simp] theorem mem_layer3CandidateList_iff
    (encoders : CodeEncoders K) (transcript : IdealTranscript K)
    (candidate : Coeff3 K) :
    candidate ∈ layer3CandidateList encoders transcript ↔
      Near3 encoders transcript candidate := by
  simp [layer3CandidateList]

/-! ## The four explicit S-two fold-reduction failures -/

/-- The final consistency relation holds, but no close degree-15 layer-three
polynomial folds to the published degree-three polynomial. -/
def Fold3ReductionFailure
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Prop :=
  6082 < (consistencySet schedule transcript).card /\
    ¬ (∃ c3, SupportedNear3 schedule encoders transcript c3 /\
      fold3 schedule c3 = transcript.publishedFinal)

/-- A close layer-three polynomial on a final-reaching chain has no close
layer-two predecessor under alpha two. -/
def Fold2ReductionFailure
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Prop :=
  ∃ c3, SupportedNear3 schedule encoders transcript c3 /\
    fold3 schedule c3 = transcript.publishedFinal /\
    ¬ (∃ c2, SupportedNear2 schedule encoders transcript c2 /\
      fold2 schedule c2 = c3)

/-- A close layer-two polynomial on a final-reaching chain has no close
layer-one predecessor under alpha one. -/
def Fold1ReductionFailure
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Prop :=
  ∃ c2 c3,
    SupportedNear2 schedule encoders transcript c2 /\
    SupportedNear3 schedule encoders transcript c3 /\
    fold2 schedule c2 = c3 /\
    fold3 schedule c3 = transcript.publishedFinal /\
    ¬ (∃ c1, SupportedNear1 schedule encoders transcript c1 /\
      fold1 schedule c1 = c2)

/-- A close layer-one polynomial on a final-reaching chain has no close
initial predecessor under alpha zero. -/
def Fold0ReductionFailure
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K) : Prop :=
  ∃ c1 c2 c3,
    SupportedNear1 schedule encoders transcript c1 /\
    SupportedNear2 schedule encoders transcript c2 /\
    SupportedNear3 schedule encoders transcript c3 /\
    fold1 schedule c1 = c2 /\
    fold2 schedule c2 = c3 /\
    fold3 schedule c3 = transcript.publishedFinal /\
    ¬ (∃ c0, SupportedNear0 schedule encoders transcript c0 /\
      fold0 schedule c0 = c1)

/-- The Guruswami--Sudan list theorem failed to give the deployed cap for the
explicit initial proximity list.  The numeric expression `< 240` is proved in
`V5FriListCap`; relating that expression to this actual list is deliberately
kept visible as the cited decoding theorem. -/
def InitialListCapFailure
    (encoders : CodeEncoders K) (transcript : IdealTranscript K) : Prop :=
  240 < (initialCandidateList encoders transcript).card

/-- All ideal FRI failures left to the standard query, folding, and list-size
soundness theorems.  Every disjunct is stated directly in terms of the exact
committed words, agreement lists, and coefficient folds above. -/
def FriSideFailure
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072) : Prop :=
  QueryPhaseFailure schedule transcript queries ∨
  Fold3ReductionFailure schedule encoders transcript ∨
  Fold2ReductionFailure schedule encoders transcript ∨
  Fold1ReductionFailure schedule encoders transcript ∨
  Fold0ReductionFailure schedule encoders transcript ∨
  InitialListCapFailure encoders transcript

/-! ## Backwards extraction -/

/-- Outside the four concrete fold-reduction failures, dense final
consistency yields one coherent chain starting from the explicit initial
decoder list and ending at the published final coefficients. -/
theorem coherent_chain_of_dense_consistency_outside_fold_failures
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (hdense : 6082 < (consistencySet schedule transcript).card)
    (h3 : ¬ Fold3ReductionFailure schedule encoders transcript)
    (h2 : ¬ Fold2ReductionFailure schedule encoders transcript)
    (h1 : ¬ Fold1ReductionFailure schedule encoders transcript)
    (h0 : ¬ Fold0ReductionFailure schedule encoders transcript) :
    ∃ chain : CoherentChain schedule,
      SupportedNear0 schedule encoders transcript chain.initial /\
      SupportedNear1 schedule encoders transcript chain.layer1 /\
      SupportedNear2 schedule encoders transcript chain.layer2 /\
      SupportedNear3 schedule encoders transcript chain.layer3 /\
      chain.final = transcript.publishedFinal := by
  have hpred3 : ∃ c3, SupportedNear3 schedule encoders transcript c3 /\
      fold3 schedule c3 = transcript.publishedFinal := by
    by_contra hnone
    exact h3 ⟨hdense, hnone⟩
  obtain ⟨c3, hc3Near, hc3Final⟩ := hpred3
  have hpred2 : ∃ c2, SupportedNear2 schedule encoders transcript c2 /\
      fold2 schedule c2 = c3 := by
    by_contra hnone
    exact h2 ⟨c3, hc3Near, hc3Final, hnone⟩
  obtain ⟨c2, hc2Near, hc2Fold⟩ := hpred2
  have hpred1 : ∃ c1, SupportedNear1 schedule encoders transcript c1 /\
      fold1 schedule c1 = c2 := by
    by_contra hnone
    exact h1 ⟨c2, c3, hc2Near, hc3Near, hc2Fold, hc3Final, hnone⟩
  obtain ⟨c1, hc1Near, hc1Fold⟩ := hpred1
  have hpred0 : ∃ c0, SupportedNear0 schedule encoders transcript c0 /\
      fold0 schedule c0 = c1 := by
    by_contra hnone
    exact h0 ⟨c1, c2, c3, hc1Near, hc2Near, hc3Near,
      hc1Fold, hc2Fold, hc3Final, hnone⟩
  obtain ⟨c0, hc0Near, hc0Fold⟩ := hpred0
  let chain : CoherentChain schedule := {
    initial := c0
    layer1 := c1
    layer2 := c2
    layer3 := c3
    final := transcript.publishedFinal
    layer1_eq := hc0Fold.symm
    layer2_eq := hc1Fold.symm
    layer3_eq := hc2Fold.symm
    final_eq := hc3Final.symm
  }
  exact ⟨chain, hc0Near, hc1Near, hc2Near, hc3Near, rfl⟩

/-- The decisive ideal-FRI inclusion.  If the exact q18 checks accept and none
of the explicit query/fold/list failures occurs, one member of a single
at-most-240 initial list folds to the published final polynomial. -/
theorem accepted_ideal_fri_supplies_matching_initial_candidate
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (haccepts : IdealAccepts schedule transcript queries)
    (hquery : ¬ QueryPhaseFailure schedule transcript queries)
    (h3 : ¬ Fold3ReductionFailure schedule encoders transcript)
    (h2 : ¬ Fold2ReductionFailure schedule encoders transcript)
    (h1 : ¬ Fold1ReductionFailure schedule encoders transcript)
    (h0 : ¬ Fold0ReductionFailure schedule encoders transcript)
    (hcap : ¬ InitialListCapFailure encoders transcript) :
    ∃ candidate,
      candidate ∈ initialCandidateList encoders transcript /\
      finalCoefficientMap schedule candidate = transcript.publishedFinal /\
      (initialCandidateList encoders transcript).card ≤ 240 := by
  have hdense := dense_consistency_of_accepts_not_queryFailure
    schedule transcript queries haccepts hquery
  obtain ⟨chain, hc0, hc1, hc2, hc3, hfinal⟩ :=
    coherent_chain_of_dense_consistency_outside_fold_failures
      schedule encoders transcript hdense h3 h2 h1 h0
  refine ⟨chain.initial, ?_, ?_, ?_⟩
  · simpa using
      SupportedNear0.near0 schedule encoders transcript chain.initial hc0
  · rw [finalCoefficientMap_eq_four_folds]
    rw [← chain.layer1_eq, ← chain.layer2_eq, ← chain.layer3_eq,
      ← chain.final_eq, hfinal]
  · exact Nat.le_of_not_gt hcap

set_option maxRecDepth 10000 in
/-- Subtype form used by a relation proof: the extracted object is one member
of the initial list, and the whole candidate type has cardinality at most 240.
-/
theorem accepted_ideal_fri_supplies_bounded_candidate_type
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (haccepts : IdealAccepts schedule transcript queries)
    (hquery : ¬ QueryPhaseFailure schedule transcript queries)
    (h3 : ¬ Fold3ReductionFailure schedule encoders transcript)
    (h2 : ¬ Fold2ReductionFailure schedule encoders transcript)
    (h1 : ¬ Fold1ReductionFailure schedule encoders transcript)
    (h0 : ¬ Fold0ReductionFailure schedule encoders transcript)
    (hcap : ¬ InitialListCapFailure encoders transcript) :
    ∃ candidate : {c // c ∈ initialCandidateList encoders transcript},
      finalCoefficientMap schedule candidate.1 = transcript.publishedFinal /\
      Fintype.card {c // c ∈ initialCandidateList encoders transcript} ≤ 240 := by
  obtain ⟨candidate, hmem, hfinal, hcard⟩ :=
    accepted_ideal_fri_supplies_matching_initial_candidate
      schedule encoders transcript queries haccepts hquery h3 h2 h1 h0 hcap
  refine ⟨⟨candidate, hmem⟩, hfinal, ?_⟩
  simpa using hcard

set_option maxRecDepth 10000 in
/-- Inclusion form used by an end-to-end union bound: every accepted ideal
V5 FRI execution either realizes one of the explicit FRI-side failures or
supplies a member of one initial candidate type of cardinality at most 240
whose exact four folds equal the published final coefficients. -/
theorem accepted_ideal_fri_failure_or_bounded_matching_candidate
    (schedule : FixedSchedule F K) (encoders : CodeEncoders K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (haccepts : IdealAccepts schedule transcript queries) :
    FriSideFailure schedule encoders transcript queries ∨
      ∃ candidate : {c // c ∈ initialCandidateList encoders transcript},
        finalCoefficientMap schedule candidate.1 = transcript.publishedFinal ∧
        Fintype.card {c // c ∈ initialCandidateList encoders transcript} ≤ 240 := by
  classical
  by_cases hfailure : FriSideFailure schedule encoders transcript queries
  · exact Or.inl hfailure
  · apply Or.inr
    apply accepted_ideal_fri_supplies_bounded_candidate_type
      schedule encoders transcript queries haccepts
    · intro hquery
      exact hfailure (Or.inl hquery)
    · intro h3
      exact hfailure (Or.inr (Or.inl h3))
    · intro h2
      exact hfailure (Or.inr (Or.inr (Or.inl h2)))
    · intro h1
      exact hfailure (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · intro h0
      exact hfailure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h0)))))
    · intro hcap
      exact hfailure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcap)))))

end FiniteField

/-! ## Exact integer floors used by the decoder predicates -/

private theorem sqrt_rate_sq :
    Real.sqrt (1 / 512 : Real) ^ 2 = 1 / 512 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_rate_nonneg :
    0 <= Real.sqrt (1 / 512 : Real) := Real.sqrt_nonneg _

/-- The four decoder thresholds are the exact floors of
`(21/20) * sqrt(1/512) * N` at the committed V5 word sizes. -/
theorem deployed_agreement_floors :
    (24328 : Real) <=
        (21 / 20) * Real.sqrt (1 / 512) * 524288 /\
      (21 / 20) * Real.sqrt (1 / 512) * 524288 < 24329 /\
    (6082 : Real) <=
        (21 / 20) * Real.sqrt (1 / 512) * 131072 /\
      (21 / 20) * Real.sqrt (1 / 512) * 131072 < 6083 /\
    (1520 : Real) <=
        (21 / 20) * Real.sqrt (1 / 512) * 32768 /\
      (21 / 20) * Real.sqrt (1 / 512) * 32768 < 1521 /\
    (380 : Real) <=
        (21 / 20) * Real.sqrt (1 / 512) * 8192 /\
      (21 / 20) * Real.sqrt (1 / 512) * 8192 < 381 := by
  have hs := sqrt_rate_sq
  have hn := sqrt_rate_nonneg
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-! ## Audit -/

#print axioms finalCoefficientMap_eq_four_folds
#print axioms queryPhaseFailure_implies_ordered_miss
#print axioms queryPhaseFailure_ideal_ratio_div_work_le
#print axioms initialCandidateList_eq_of_layer0_eq
#print axioms coherent_chain_of_dense_consistency_outside_fold_failures
#print axioms accepted_ideal_fri_supplies_matching_initial_candidate
#print axioms accepted_ideal_fri_supplies_bounded_candidate_type
#print axioms accepted_ideal_fri_failure_or_bounded_matching_candidate
#print axioms deployed_agreement_floors

end AspisV5FriCoherentCandidateExtraction
