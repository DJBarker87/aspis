import AspisFormal.K1.V7Tag73ExactRootFreshInputUniqueness
import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
import AspisFormal.K1.V7Tag73FinalWorkQ16CandidateController

/-!
# Exact root order of the accepted final-work pair

Both inputs that start an accepted final-work/q16 trial are literal fresh
coordinates in the adversary-then-verifier root chronology.  This file orders
those two coordinates without attempting to classify either coordinate from
its raw SHA bytes.  The result is the finite source split needed to run the
candidate controller from the earlier coordinate through the later one.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFinalWorkPairRootOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Two distinct members of a chronological list occur in one of the two
strict orders.  The witnesses retain the complete prefix, middle, and suffix
rather than comparing opaque numerical indices. -/
theorem distinct_members_have_strict_list_order
    {α : Type} (values : List α) (first second : α)
    (different : first ≠ second)
    (firstMember : first ∈ values) (secondMember : second ∈ values) :
    (∃ before middle after,
      values = before ++ first :: middle ++ second :: after) ∨
    (∃ before middle after,
      values = before ++ second :: middle ++ first :: after) := by
  obtain ⟨prior, later, decomposition⟩ :=
    (List.mem_iff_append).mp firstMember
  rw [decomposition] at secondMember
  rcases List.mem_append.mp secondMember with inPrior | atOrAfter
  · obtain ⟨before, middle, priorExact⟩ :=
    (List.mem_iff_append).mp inPrior
    right
    exact ⟨before, middle, later, by
      simpa only [decomposition, priorExact, List.cons_append,
        List.append_assoc]⟩
  · rcases List.mem_cons.mp atOrAfter with equal | inLater
    · exact (different equal.symm).elim
    · obtain ⟨middle, after, laterExact⟩ :=
        (List.mem_iff_append).mp inLater
      left
      exact ⟨prior, middle, after, by
        simpa only [decomposition, laterExact, List.cons_append,
          List.append_assoc]⟩

/-- Strict accepted execution exposes the work query and the nonce-absorb
query in one exact order in the combined adversary/verifier root list.  The
answer attached to the earlier coordinate may have been chosen by either
actor; no raw-coordinate role classifier is used. -/
theorem exact_compiler_accepted_final_work_pair_has_strict_root_order
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer q16Base : Digest256),
      FinalWork34Accepted workAnswer ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      ((∃ before middle after,
          exactRootFreshQueries input =
            before ++
              ((literalFinalWorkKey digest
                (exactOperationalTape input).messages.finalGrinding.selected
              ).workInput, workAnswer) ::
              middle ++
              ((literalFinalWorkKey digest
                (exactOperationalTape input).messages.finalGrinding.selected
              ).absorbInput, q16Base) :: after) ∨
        (∃ before middle after,
          exactRootFreshQueries input =
            before ++
              ((literalFinalWorkKey digest
                (exactOperationalTape input).messages.finalGrinding.selected
              ).absorbInput, q16Base) ::
              middle ++
              ((literalFinalWorkKey digest
                (exactOperationalTape input).messages.finalGrinding.selected
              ).workInput, workAnswer) :: after)) := by
  obtain ⟨digest, workAnswer, q16Base, workLookup, workAccepted,
      absorbLookup, q16BaseExact⟩ :=
    exact_operational_final_work_pair_lookups input
  let key := literalFinalWorkKey digest
    (exactOperationalTape input).messages.finalGrinding.selected
  have workMember : (key.workInput, workAnswer) ∈
      exactRootFreshQueries input := by
    rcases exact_compiler_final_lookup_in_ordered_root_suffix input
        key.workInput workAnswer workLookup with adversary | verifier
    · exact List.mem_append_left _ adversary
    · exact List.mem_append_right _ verifier
  have absorbMember : (key.absorbInput, q16Base) ∈
      exactRootFreshQueries input := by
    rcases exact_compiler_final_lookup_in_ordered_root_suffix input
        key.absorbInput q16Base absorbLookup with adversary | verifier
    · exact List.mem_append_left _ adversary
    · exact List.mem_append_right _ verifier
  have pairDifferent : (key.workInput, workAnswer) ≠
      (key.absorbInput, q16Base) := by
    intro equal
    have inputEqual : key.workInput = key.absorbInput :=
      congrArg Prod.fst equal
    exact key.absorbInput_ne_workInput inputEqual.symm
  have ordered := distinct_members_have_strict_list_order
    (exactRootFreshQueries input) (key.workInput, workAnswer)
      (key.absorbInput, q16Base) pairDifferent workMember absorbMember
  exact ⟨digest, workAnswer, q16Base, workAccepted, q16BaseExact, by
    simpa only [key] using ordered⟩

/-- Record-level form of the same order.  It retains the actual actor attached
to each first creation and is therefore directly composable with the unified
scheduler cursor and exposure-indexed candidate controller. -/
theorem exact_compiler_accepted_final_work_pair_has_strict_root_record_order
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (digest workAnswer q16Base : Digest256)
        (workActor absorbActor : QueryActor),
      FinalWork34Accepted workAnswer ∧
      q16Base = (exactOperationalRawTrace input).q16BaseDigest ∧
      ((∃ before middle after,
          exactFixedRootRecords input.package.root =
            before ++
              (.machineFresh workActor
                (literalFinalWorkKey digest
                  (exactOperationalTape input).messages.finalGrinding.selected
                ).workInput workAnswer : UnifiedExposureRecord) ::
              middle ++
              (.machineFresh absorbActor
                (literalFinalWorkKey digest
                  (exactOperationalTape input).messages.finalGrinding.selected
                ).absorbInput q16Base : UnifiedExposureRecord) :: after) ∨
        (∃ before middle after,
          exactFixedRootRecords input.package.root =
            before ++
              (.machineFresh absorbActor
                (literalFinalWorkKey digest
                  (exactOperationalTape input).messages.finalGrinding.selected
                ).absorbInput q16Base : UnifiedExposureRecord) ::
              middle ++
              (.machineFresh workActor
                (literalFinalWorkKey digest
                  (exactOperationalTape input).messages.finalGrinding.selected
                ).workInput workAnswer : UnifiedExposureRecord) :: after)) := by
  obtain ⟨digest, workAnswer, q16Base, workLookup, workAccepted,
      absorbLookup, q16BaseExact⟩ :=
    exact_operational_final_work_pair_lookups input
  let key := literalFinalWorkKey digest
    (exactOperationalTape input).messages.finalGrinding.selected
  obtain ⟨workActor, workMember⟩ :=
    exact_final_table_lookup_has_root_record input key.workInput workAnswer
      workLookup
  obtain ⟨absorbActor, absorbMember⟩ :=
    exact_final_table_lookup_has_root_record input key.absorbInput q16Base
      absorbLookup
  have pairDifferent :
      (.machineFresh workActor key.workInput workAnswer :
          UnifiedExposureRecord) ≠
        .machineFresh absorbActor key.absorbInput q16Base := by
    intro equal
    have inputEqual : key.workInput = key.absorbInput := by
      injection equal
    exact key.absorbInput_ne_workInput inputEqual.symm
  have ordered := distinct_members_have_strict_list_order
    (exactFixedRootRecords input.package.root)
    (.machineFresh workActor key.workInput workAnswer)
    (.machineFresh absorbActor key.absorbInput q16Base)
    pairDifferent workMember absorbMember
  exact ⟨digest, workAnswer, q16Base, workActor, absorbActor, workAccepted,
    q16BaseExact, by simpa only [key] using ordered⟩

#print axioms distinct_members_have_strict_list_order
#print axioms exact_compiler_accepted_final_work_pair_has_strict_root_order
#print axioms
  exact_compiler_accepted_final_work_pair_has_strict_root_record_order

end

end AspisK1.V7Tag73ExactFinalWorkPairRootOrder
