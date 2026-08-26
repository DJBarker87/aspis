import Mathlib.Data.Fintype.Pi
import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import AspisFormal.V6Width29CorrelatedAgreement

/-!
# V7 width-29 component extraction

The deployed proximity test decodes one `gamma`-batched initial word.  That
word cannot be inverted to recover the 29 underlying trace columns.  This
module closes the distinction explicitly: it runs the already algorithmic
initial decoder on every reconstructed lane, forms the finite Cartesian
product of those outputs, and selects a tuple satisfying the *same* shared
agreement support and the exact correlated batching equation.

The degree-28 statement producing `HasMatchingWidth29Decomposition` remains
the published circle-code boundary.  Everything after that predicate --
individual decoder inclusion, finite tuple construction and deterministic
selection -- is proved here.
-/

set_option autoImplicit false

namespace AspisPool.V7Width29ComponentExtraction

open AspisPool.AlgorithmicCircleDecoderV7
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

abbrev Width29InitialWords (K : Type*) := Fin 29 → InitialWord K
abbrev Width29InitialMessages (K : Type*) := Fin 29 → InitialMessage K

/-- The literal pointwise batching used by the initial V7 commitment. -/
def batchInitialWords (lanes : Width29InitialWords K) (gamma : K) :
    InitialWord K :=
  fun index => width29Batch (fun lane => lanes lane index) gamma

/-- Every tuple returned by running the exact initial decoder independently
on all 29 reconstructed lane words.  Width 29 is a fixed protocol constant;
the extractor is finite and deterministic, although deliberately off-chain. -/
def componentCandidateSet (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K) :
    Finset (Width29InitialMessages K) :=
  Fintype.piFinset fun lane => (decoder.initialDecode (lanes lane)).toFinset

@[simp] theorem mem_componentCandidateSet_iff
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (components : Width29InitialMessages K) :
    components ∈ componentCandidateSet decoder lanes ↔
      ∀ lane, components lane ∈ decoder.initialDecode (lanes lane) := by
  simp [componentCandidateSet]

/-- Exact candidates matching the decomposition predicate supplied by the
published correlated circle-code theorem.  In particular, this does not
pretend that the single batched message determines its components. -/
noncomputable def matchingComponentSet (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K) : Finset (Width29InitialMessages K) := by
  classical
  exact (componentCandidateSet decoder lanes).filter fun components =>
    strategy.support gamma ⊆
        width29JointAgreementSet decoder.initialEncoder lanes components ∧
      Width29CandidateOnCurve decoder.initialEncoder strategy components gamma

@[simp] theorem mem_matchingComponentSet_iff
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K) (components : Width29InitialMessages K) :
    components ∈ matchingComponentSet decoder lanes strategy gamma ↔
      (∀ lane, components lane ∈ decoder.initialDecode (lanes lane)) ∧
      strategy.support gamma ⊆
        width29JointAgreementSet decoder.initialEncoder lanes components ∧
      Width29CandidateOnCurve decoder.initialEncoder strategy components gamma := by
  simp [matchingComponentSet, and_assoc]

/-- Canonical deterministic selection from the finite component search. -/
noncomputable def selectWidth29Components (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K) : Option (Width29InitialMessages K) := by
  classical
  exact (matchingComponentSet decoder lanes strategy gamma).toList.head?

private theorem shared_support_implies_lane_close
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K) (components : Width29InitialMessages K)
    (valid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        lanes strategy gamma)
    (shared : strategy.support gamma ⊆
      width29JointAgreementSet decoder.initialEncoder lanes components)
    (lane : Fin 29) :
    closeAtLeast AlgorithmicCircleDecoderV7.initialAgreementThreshold
      decoder.initialEncoder (lanes lane) (components lane) := by
  classical
  have supportSubset : strategy.support gamma ⊆
      Finset.univ.filter fun index =>
        lanes lane index = decoder.initialEncoder (components lane) index := by
    intro index hindex
    have hjointAll : ∀ lane,
        lanes lane index = decoder.initialEncoder (components lane) index := by
      simpa only [width29JointAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using (shared hindex)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjointAll lane⟩
  have countBound := Finset.card_le_card supportSubset
  unfold closeAtLeast agreementCount
  change 38230 ≤
    (Finset.univ.filter fun index =>
      lanes lane index = decoder.initialEncoder (components lane) index).card
  have validCard : 38229 < (strategy.support gamma).card := by
    simpa [AspisV6PublishedTheoremInterfaces.initialAgreementThreshold] using
      valid.1
  omega

/-- Any explicitly supplied tuple on the same large shared support enters all
twenty-nine deterministic decoder lists.  This public form lets a
restoration-wide correlated extractor retain its one fixed tuple instead of
reselecting an unrelated local tuple. -/
theorem shared_support_components_enter_decoder
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K) (components : Width29InitialMessages K)
    (valid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        lanes strategy gamma)
    (shared : strategy.support gamma ⊆
      width29JointAgreementSet decoder.initialEncoder lanes components) :
    ∀ lane, components lane ∈ decoder.initialDecode (lanes lane) := by
  intro lane
  exact decoder.initialComplete (lanes lane) (components lane)
    (shared_support_implies_lane_close decoder lanes strategy gamma
      components valid shared lane)

theorem matching_decomposition_enters_component_search
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K)
    (valid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        lanes strategy gamma)
    (matching : HasMatchingWidth29Decomposition
      decoder.initialEncoder lanes strategy gamma) :
    ∃ components,
      components ∈ matchingComponentSet decoder lanes strategy gamma := by
  classical
  obtain ⟨components, shared, onCurve⟩ := matching
  refine ⟨components, (mem_matchingComponentSet_iff
    decoder lanes strategy gamma components).2 ⟨?_, shared, onCurve⟩⟩
  intro lane
  exact decoder.initialComplete (lanes lane) (components lane)
    (shared_support_implies_lane_close decoder lanes strategy gamma
      components valid shared lane)

private theorem select_of_member
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K) (member : Width29InitialMessages K)
    (memberIn : member ∈ matchingComponentSet decoder lanes strategy gamma) :
    ∃ selected,
      selectWidth29Components decoder lanes strategy gamma = some selected ∧
      selected ∈ matchingComponentSet decoder lanes strategy gamma := by
  classical
  cases candidatesEq : (matchingComponentSet decoder lanes strategy gamma).toList with
  | nil =>
      have memberInList : member ∈
          (matchingComponentSet decoder lanes strategy gamma).toList := by
        simpa using memberIn
      simp [candidatesEq] at memberInList
  | cons first rest =>
      refine ⟨first, ?_, ?_⟩
      · simp [selectWidth29Components, candidatesEq]
      · have firstInList : first ∈
            (matchingComponentSet decoder lanes strategy gamma).toList := by
          simp [candidatesEq]
        simpa using firstInList

/-- End-to-end deterministic width-29 selection outside the named published
decomposition failure.  The result exposes all 29 component messages together
with their common support and exact gamma-batched codeword equation. -/
theorem matching_decomposition_selects_exact_components
    (decoder : ExactDecoderInstantiation K)
    (lanes : Width29InitialWords K)
    (strategy : Width29ProximateStrategy K (Fin 1048576) (InitialMessage K))
    (gamma : K)
    (valid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        lanes strategy gamma)
    (matching : HasMatchingWidth29Decomposition
      decoder.initialEncoder lanes strategy gamma) :
    ∃ selected,
      selectWidth29Components decoder lanes strategy gamma = some selected ∧
      (∀ lane, selected lane ∈ decoder.initialDecode (lanes lane)) ∧
      strategy.support gamma ⊆
        width29JointAgreementSet decoder.initialEncoder lanes selected ∧
      Width29CandidateOnCurve decoder.initialEncoder strategy selected gamma := by
  classical
  obtain ⟨member, memberIn⟩ :=
    matching_decomposition_enters_component_search
      decoder lanes strategy gamma valid matching
  obtain ⟨selected, selectedEq, selectedIn⟩ :=
    select_of_member decoder lanes strategy gamma member memberIn
  refine ⟨selected, selectedEq, ?_⟩
  exact (mem_matchingComponentSet_iff
    decoder lanes strategy gamma selected).1 selectedIn

#print axioms mem_componentCandidateSet_iff
#print axioms mem_matchingComponentSet_iff
#print axioms shared_support_components_enter_decoder
#print axioms matching_decomposition_enters_component_search
#print axioms matching_decomposition_selects_exact_components

end AspisPool.V7Width29ComponentExtraction
