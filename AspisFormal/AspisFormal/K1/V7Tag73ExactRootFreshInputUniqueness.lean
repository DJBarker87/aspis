import AspisFormal.K1.V7Tag73ExactRootLookupCausalOrder
import AspisFormal.K1.V7Tag73SourceAnchoredSchedulerCut

/-!
# Exact uniqueness of root fresh-query inputs

The causal final-work/q16 router must not assign a named slot before the
literal source query that owns it.  The first source invariant needed for
that argument is input uniqueness: within each projected machine segment a
fresh input cannot recur, and a verifier-fresh input cannot already have
occurred in the adversary segment whose final table the verifier inherits.

This file derives that invariant from the executable projected traces.  It
does not assume a raw-coordinate classifier or identify protocol roles from
SHA bytes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootFreshInputUniqueness

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- Every projected fresh pair is installed in the returned segment's final
table, so its input cannot have a missing lookup there. -/
theorem projected_fresh_member_has_final_lookup
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor)
    {fuel : Nat} {state : OracleState} {program : OracleMachine Result}
    {freshQueries : List (ShaInput × Digest256)} {result : Result}
    {finalState : OracleState} {steps : Nat}
    (trace : ProjectedFreshReturnedTrace limits actor fuel state program
      freshQueries result finalState steps)
    (query : ShaInput × Digest256) (member : query ∈ freshQueries) :
    lookupEntry finalState query.1 ≠ none := by
  intro missing
  have tableExact := projected_fresh_returned_trace_table_exact limits actor
    fuel state program freshQueries result finalState steps trace
  have mappedMember : projectedFreshEntry query ∈ finalState.table := by
    rw [tableExact]
    exact List.mem_append_right state.table
      (List.mem_map.mpr ⟨query, member, rfl⟩)
  unfold lookupEntry at missing
  have rejected := List.find?_eq_none.mp missing
    (projectedFreshEntry query) mappedMember
  simp [projectedFreshEntry] at rejected

/-- Fresh inputs within one executable projected segment are pairwise
distinct.  A repeated input would already be present in the table inherited
by the recursive tail, contradicting that the later call is fresh. -/
theorem projected_fresh_returned_trace_inputs_nodup
    {Result : Type u} (limits : OracleLimits) (actor : QueryActor) :
    ∀ {fuel : Nat} {state : OracleState} {program : OracleMachine Result}
      {freshQueries : List (ShaInput × Digest256)} {result : Result}
      {finalState : OracleState} {steps : Nat},
      ProjectedFreshReturnedTrace limits actor fuel state program
          freshQueries result finalState steps →
        (freshQueries.map Prod.fst).Nodup := by
  intro fuel state program freshQueries result finalState steps trace
  induction trace with
  | returned =>
      exact List.nodup_nil
  | fresh fuel state requestState program coherent headInput next remainingFuel
      cachedSteps requestCoherent totalRoom freshRoom headMissing sought
      headAnswer rest result finalState tailSteps tail ih =>
      apply List.nodup_cons.mpr
      constructor
      · intro headInRest
        obtain ⟨query, queryMember, queryInput⟩ := List.mem_map.mp headInRest
        rcases query with ⟨laterInput, laterAnswer⟩
        have queryInputExact : laterInput = headInput := by
          simpa using queryInput
        subst laterInput
        have laterMissing :=
          projected_fresh_returned_trace_future_input_missing limits actor
            remainingFuel
            (freshQueryState actor requestState headInput headAnswer)
            (next headAnswer) rest result finalState tailSteps tail
            headInput laterAnswer queryMember
        unfold lookupEntry freshQueryState at laterMissing
        unfold lookupEntry at headMissing
        rw [List.find?_append, headMissing] at laterMissing
        simp at laterMissing
      · exact ih

/-- Inputs produced by a completed first segment are disjoint from the fresh
inputs of a second segment that starts from the first segment's final oracle.
This is the exact adversary-to-verifier boundary used by Tag-73. -/
theorem projected_fresh_successive_segments_inputs_disjoint
    {FirstResult SecondResult : Type u}
    (firstLimits secondLimits : OracleLimits)
    (firstActor secondActor : QueryActor)
    {firstFuel secondFuel : Nat}
    {firstState : OracleState}
    {firstProgram : OracleMachine FirstResult}
    {firstQueries : List (ShaInput × Digest256)}
    {firstResult : FirstResult} {middleState : OracleState}
    {firstSteps : Nat}
    {secondProgram : OracleMachine SecondResult}
    {secondQueries : List (ShaInput × Digest256)}
    {secondResult : SecondResult} {finalState : OracleState}
    {secondSteps : Nat}
    (firstTrace : ProjectedFreshReturnedTrace firstLimits firstActor firstFuel
      firstState firstProgram firstQueries firstResult middleState firstSteps)
    (secondTrace : ProjectedFreshReturnedTrace secondLimits secondActor
      secondFuel middleState secondProgram secondQueries secondResult finalState
      secondSteps) :
    List.Disjoint (firstQueries.map Prod.fst)
      (secondQueries.map Prod.fst) := by
  rw [List.disjoint_left]
  intro input inFirst inSecond
  obtain ⟨firstQuery, firstMember, firstInput⟩ := List.mem_map.mp inFirst
  obtain ⟨secondQuery, secondMember, secondInput⟩ :=
    List.mem_map.mp inSecond
  rcases firstQuery with ⟨firstQueryInput, firstAnswer⟩
  rcases secondQuery with ⟨secondQueryInput, secondAnswer⟩
  have firstInputExact : firstQueryInput = input := by simpa using firstInput
  have secondInputExact : secondQueryInput = input := by simpa using secondInput
  subst firstQueryInput
  subst secondQueryInput
  have present := projected_fresh_member_has_final_lookup firstLimits firstActor
    firstTrace (input, firstAnswer) firstMember
  have missing := projected_fresh_returned_trace_future_input_missing
    secondLimits secondActor secondFuel middleState secondProgram secondQueries
    secondResult finalState secondSteps secondTrace input secondAnswer
    secondMember
  exact present missing

/-- The complete adversary-then-verifier root fresh-query list has pairwise
distinct SHA inputs. -/
theorem exact_root_fresh_query_inputs_nodup
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
    ((exactRootFreshQueries input).map Prod.fst).Nodup := by
  let prefixes := input.package.root.full.projection.rootPrefixes
  have adversaryNodup := projected_fresh_returned_trace_inputs_nodup
    configuration.machine.adversaryLimits .adversary prefixes.adversary.trace
  have verifierNodup := projected_fresh_returned_trace_inputs_nodup
    configuration.machine.verifierLimits .verifier prefixes.verifier.trace
  have disjoint := projected_fresh_successive_segments_inputs_disjoint
    configuration.machine.adversaryLimits configuration.machine.verifierLimits
    .adversary .verifier prefixes.adversary.trace prefixes.verifier.trace
  unfold exactRootFreshQueries
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨adversaryNodup, verifierNodup, ?_⟩
  intro first firstMember second secondMember equal
  subst second
  exact (List.disjoint_left.mp disjoint firstMember) secondMember

/-- At an exact positional decomposition, the selected fresh input did not
occur in the strict prefix. -/
theorem exact_root_selected_input_not_mem_prior
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
    (prior later : List (ShaInput × Digest256))
    (selected : ShaInput × Digest256)
    (decomposition : exactRootFreshQueries input =
      prior ++ selected :: later) :
    selected.1 ∉ prior.map Prod.fst := by
  have nodup := exact_root_fresh_query_inputs_nodup input
  rw [decomposition, List.map_append] at nodup
  simp only [List.map_cons, List.nodup_append] at nodup
  intro selectedInPrior
  exact nodup.2.2 selected.1 selectedInPrior selected.1 (by simp) rfl

#print axioms projected_fresh_member_has_final_lookup
#print axioms projected_fresh_returned_trace_inputs_nodup
#print axioms projected_fresh_successive_segments_inputs_disjoint
#print axioms exact_root_fresh_query_inputs_nodup
#print axioms exact_root_selected_input_not_mem_prior

end

end AspisK1.V7Tag73ExactRootFreshInputUniqueness
