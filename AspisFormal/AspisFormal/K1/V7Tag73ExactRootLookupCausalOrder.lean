import AspisFormal.K1.V7Tag73ExactRootQueryCausalOrder
import AspisFormal.K1.V7Tag73ExactCompilerSourceAnchoredCut

/-!
# Causal order of exact final-table root lookups

Every exact final-table lookup has one positional first-creation record in the
chronological adversary/verifier root lists.  Target cleanliness then turns a
literal answer-to-input dependency into a strict source order: the producing
fresh query occurs before the dependent fresh query.  No raw-input role
classifier or adversary-first exclusion is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootLookupCausalOrder

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootQueryCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The chronological pair list created by the two literal root callbacks. -/
def exactRootFreshQueries
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : List (ShaInput × Digest256) :=
  input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
    input.package.root.full.projection.rootPrefixes.verifier.freshQueries

/-- A final-table lookup has an exact position in exactly one of the ordered
root segments.  The disjunction retains the actor needed by the source
chronology theorem. -/
theorem exact_compiler_final_lookup_has_root_position
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) (answer : Digest256)
    (found : tableLookup (exactOperationalTable input) target = some answer) :
    (∃ prior later,
      input.package.root.full.projection.rootPrefixes.adversary.freshQueries =
        prior ++ (target, answer) :: later) ∨
    (∃ prior later,
      input.package.root.full.projection.rootPrefixes.verifier.freshQueries =
        prior ++ (target, answer) :: later) := by
  rcases exact_compiler_final_lookup_in_ordered_root_suffix input target answer
      found with adversary | verifier
  · obtain ⟨prior, later, exact⟩ := (List.mem_iff_append).mp adversary
    exact Or.inl ⟨prior, later, exact⟩
  · obtain ⟨prior, later, exact⟩ := (List.mem_iff_append).mp verifier
    exact Or.inr ⟨prior, later, exact⟩

/-- Target cleanliness also excludes a fresh answer from being the literal
state prefix of its own input. -/
theorem exact_compiler_final_lookup_answer_avoids_own_input
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (target : ShaInput) (answer : Digest256)
    (found : tableLookup (exactOperationalTable input) target = some answer) :
    ¬ HasLiteralStatePrefix answer target := by
  rcases exact_compiler_final_lookup_has_root_position input target answer found
      with ⟨prior, later, decomposition⟩ |
        ⟨prior, later, decomposition⟩
  · have clean := input.package.root.wholeTraceClean.everyCoordinate
    rw [exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package] at clean
    unfold exactFixedOperationalStateMapTrace exactFixedRootRecords
      fullProjectedRootRecords at clean
    rw [decomposition] at clean
    simp only [projected_machine_fresh_records_append,
      projectedMachineFreshRecords, List.cons_append,
      List.append_assoc] at clean
    exact (chronologically_clean_machine_coordinate_of_append
      {zeroDigest256}
      (projectedMachineFreshRecords .adversary prior)
      (projectedMachineFreshRecords .adversary later ++
        (projectedMachineFreshRecords .verifier
            input.package.root.full.projection.rootPrefixes.verifier.freshQueries ++
          (exactFixedComputedClientTailRun transitionFuel configuration sample
            input.package.root).trace))
      .adversary target answer (by
        simpa only [List.append_assoc] using clean)).2
  · have clean := input.package.root.wholeTraceClean.everyCoordinate
    rw [exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package] at clean
    unfold exactFixedOperationalStateMapTrace exactFixedRootRecords
      fullProjectedRootRecords at clean
    rw [decomposition] at clean
    simp only [projected_machine_fresh_records_append,
      projectedMachineFreshRecords, List.cons_append,
      List.append_assoc] at clean
    exact (chronologically_clean_machine_coordinate_of_append
      {zeroDigest256}
      (projectedMachineFreshRecords .adversary
          input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier prior)
      (projectedMachineFreshRecords .verifier later ++
        (exactFixedComputedClientTailRun transitionFuel configuration sample
          input.package.root).trace)
      .verifier target answer (by
        simpa only [List.append_assoc] using clean)).2

/-! ## Generic strict-list ordering -/

/-- If a predicate is false on the prefix and selected element but true on a
member of the whole list, that member has a strict position after the selected
element. -/
theorem member_has_strict_later_position
    {α : Type} (predicate : α → Prop)
    (values prior later : List α) (selected dependent : α)
    (decomposition : values = prior ++ selected :: later)
    (priorRejected : ∀ value ∈ prior, ¬ predicate value)
    (selectedRejected : ¬ predicate selected)
    (dependentMember : dependent ∈ values)
    (dependentHit : predicate dependent) :
    ∃ middle after,
      values = prior ++ selected :: middle ++ dependent :: after := by
  rw [decomposition] at dependentMember
  rcases List.mem_append.mp dependentMember with inPrior | atOrAfter
  · exact (priorRejected dependent inPrior dependentHit).elim
  · rcases List.mem_cons.mp atOrAfter with equal | inLater
    · subst dependent
      exact (selectedRejected dependentHit).elim
    · obtain ⟨middle, after, laterExact⟩ :=
        (List.mem_iff_append).mp inLater
      refine ⟨middle, after, ?_⟩
      rw [decomposition, laterExact]
      simp only [List.cons_append, List.append_assoc]

/-- Core source-order theorem.  If one exact final-table answer is the literal
32-byte state prefix of another exact final-table input, the producer's root
fresh query occurs strictly before the dependent query in the combined
adversary-then-verifier chronology. -/
theorem exact_compiler_literal_dependency_has_strict_root_order
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (producerInput dependentInput : ShaInput)
    (producerAnswer dependentAnswer : Digest256)
    (producerFound : tableLookup (exactOperationalTable input) producerInput =
      some producerAnswer)
    (dependentFound : tableLookup (exactOperationalTable input) dependentInput =
      some dependentAnswer)
    (dependency : HasLiteralStatePrefix producerAnswer dependentInput) :
    ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producerInput, producerAnswer) ::
          middle ++ (dependentInput, dependentAnswer) :: after := by
  have selfRejected :=
    exact_compiler_final_lookup_answer_avoids_own_input input producerInput
      producerAnswer producerFound
  rcases exact_compiler_final_lookup_has_root_position input producerInput
      producerAnswer producerFound with
    ⟨producerPrior, producerLater, producerPosition⟩ |
      ⟨producerPrior, producerLater, producerPosition⟩
  · have priorRejected :=
      exact_root_adversary_answer_avoids_prior_query_prefixes transitionRoom
        input producerPrior producerInput producerAnswer producerLater
          producerPosition
    rcases exact_compiler_final_lookup_in_ordered_root_suffix input
        dependentInput dependentAnswer dependentFound with
      dependentAdversary | dependentVerifier
    · obtain ⟨middle, after, strictAdversary⟩ :=
        member_has_strict_later_position
          (fun query : ShaInput × Digest256 =>
            HasLiteralStatePrefix producerAnswer query.1)
          input.package.root.full.projection.rootPrefixes.adversary.freshQueries
          producerPrior producerLater (producerInput, producerAnswer)
          (dependentInput, dependentAnswer) producerPosition priorRejected
          selfRejected dependentAdversary dependency
      refine ⟨producerPrior, middle,
        after ++
          input.package.root.full.projection.rootPrefixes.verifier.freshQueries,
        ?_⟩
      unfold exactRootFreshQueries
      rw [strictAdversary]
      simp only [List.cons_append, List.append_assoc]
    · obtain ⟨verifierPrior, verifierLater, verifierPosition⟩ :=
        (List.mem_iff_append).mp dependentVerifier
      refine ⟨producerPrior, producerLater ++ verifierPrior, verifierLater,
        ?_⟩
      unfold exactRootFreshQueries
      rw [producerPosition, verifierPosition]
      simp only [List.cons_append, List.append_assoc]
  · obtain ⟨adversaryRejected, verifierPriorRejected⟩ :=
      exact_root_verifier_answer_avoids_prior_query_prefixes transitionRoom
        input producerPrior producerInput producerAnswer producerLater
          producerPosition
    rcases exact_compiler_final_lookup_in_ordered_root_suffix input
        dependentInput dependentAnswer dependentFound with
      dependentAdversary | dependentVerifier
    · exact (adversaryRejected (dependentInput, dependentAnswer)
        dependentAdversary dependency).elim
    · obtain ⟨middle, after, strictVerifier⟩ :=
        member_has_strict_later_position
          (fun query : ShaInput × Digest256 =>
            HasLiteralStatePrefix producerAnswer query.1)
          input.package.root.full.projection.rootPrefixes.verifier.freshQueries
          producerPrior producerLater (producerInput, producerAnswer)
          (dependentInput, dependentAnswer) producerPosition
          verifierPriorRejected selfRejected dependentVerifier dependency
      refine ⟨
        input.package.root.full.projection.rootPrefixes.adversary.freshQueries ++
          producerPrior,
        middle, after, ?_⟩
      unfold exactRootFreshQueries
      rw [strictVerifier]
      simp only [List.cons_append, List.append_assoc]

#print axioms exact_compiler_final_lookup_has_root_position
#print axioms exact_compiler_final_lookup_answer_avoids_own_input
#print axioms member_has_strict_later_position
#print axioms exact_compiler_literal_dependency_has_strict_root_order

end

end AspisK1.V7Tag73ExactRootLookupCausalOrder
