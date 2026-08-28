import AspisFormal.K1.V7Tag73ExactCompilerSourceAnchoredCut

/-!
# Cached gamma coordinates preserve the exact compiler root alignment

The scheduler-native gamma consumer is inert when its expected coordinate is
already in the retained oracle table with the expected answer.  This leaf
connects that definitional behavior to the exact compiler cursor invariant:
the cached coordinate is one of the already-consumed production fresh pairs,
and the complete cursor alignment is preserved unchanged.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ExactCompilerGammaCachedCoordinate

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73SourceAnchoredSchedulerCut
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut

noncomputable section

universe u

/-! ## Recover the original consumed pair from the exact table extension -/

/-- If a lookup succeeds in a table that is exactly the projection of a list
of fresh query/answer pairs, then the selected input and output occur as one
literal pair in that list. -/
theorem lookup_pair_mem_of_table_eq_projected_fresh
    (state : OracleState) (consumed : List (ShaInput × Digest256))
    (input : ShaInput) (answer : Digest256) (entry : TableEntry)
    (tableExact : state.table = consumed.map projectedFreshEntry)
    (found : lookupEntry state input = some entry)
    (answerExact : entry.output = answer) :
    (input, answer) ∈ consumed := by
  have selectedInput : entry.input = input := by
    unfold lookupEntry at found
    have selected := List.find?_some found
    exact of_decide_eq_true selected
  have entryMember : entry ∈ state.table := by
    unfold lookupEntry at found
    exact List.mem_of_find?_eq_some found
  rw [tableExact] at entryMember
  rcases List.mem_map.mp entryMember with
    ⟨query, queryMember, queryExact⟩
  rcases query with ⟨queryInput, queryAnswer⟩
  have queryInputExact : queryInput = input := by
    rw [← selectedInput, ← queryExact]
    rfl
  have queryAnswerExact : queryAnswer = answer := by
    rw [← answerExact, ← queryExact]
    rfl
  simpa [queryInputExact, queryAnswerExact] using queryMember

/-! ## Exact compiler cached-coordinate step -/

/-- An aligned compiler-root cache hit is necessarily an already-consumed
production fresh coordinate. -/
theorem exact_compiler_aligned_cached_coordinate_mem_consumed
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
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (AspisK1.V7Tag73SchedulerNativePlainRomExperiment.SchedulerNativePlainRomResult
        TapeIdentity Statement Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (entry : TableEntry)
    (found : lookupEntry state.oracle expectedInput = some entry)
    (answerExact : entry.output = expectedAnswer) :
    (expectedInput, expectedAnswer) ∈ aligned.consumed := by
  exact lookup_pair_mem_of_table_eq_projected_fresh state.oracle
    aligned.consumed expectedInput expectedAnswer entry aligned.tableExact found
      answerExact

/-- Complete cached branch for an exact compiler gamma coordinate.  The
consumer returns the identical state, all cursor/table/trace alignment facts
are reused without transport, and the coordinate is identified in the
already-consumed prefix. -/
theorem exact_compiler_cached_gamma_coordinate_step
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
    (state : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (AspisK1.V7Tag73SchedulerNativePlainRomExperiment.SchedulerNativePlainRomResult
        TapeIdentity Statement Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (entry : TableEntry)
    (found : lookupEntry state.oracle expectedInput = some entry)
    (answerExact : entry.output = expectedAnswer) :
    ∃ preserved : ExactCompilerRootGammaCursorAligned input state,
      consumeSchedulerNativeGammaCoordinate transitionFuel kind expectedInput
            expectedAnswer state = .ok state ∧
        (expectedInput, expectedAnswer) ∈ preserved.consumed := by
  exact ⟨aligned,
    consume_scheduler_native_gamma_cached_is_inert transitionFuel kind
      expectedInput expectedAnswer state entry found answerExact,
    exact_compiler_aligned_cached_coordinate_mem_consumed input state aligned
      expectedInput expectedAnswer entry found answerExact⟩

/-- Existential transition form, convenient for a caller that has already
named the result of `consumeSchedulerNativeGammaCoordinate`. -/
theorem exact_compiler_cached_gamma_coordinate_success_preserves_alignment
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
    (state nextState : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (AspisK1.V7Tag73SchedulerNativePlainRomExperiment.SchedulerNativePlainRomResult
        TapeIdentity Statement Tag73K12ParsedProof Payload Result))
    (aligned : ExactCompilerRootGammaCursorAligned input state)
    (kind : SchedulerNativeGammaQueryKind)
    (expectedInput : ShaInput) (expectedAnswer : Digest256)
    (entry : TableEntry)
    (found : lookupEntry state.oracle expectedInput = some entry)
    (answerExact : entry.output = expectedAnswer)
    (success : consumeSchedulerNativeGammaCoordinate transitionFuel kind
      expectedInput expectedAnswer state = .ok nextState) :
    nextState = state ∧
      ∃ nextAligned : ExactCompilerRootGammaCursorAligned input nextState,
        (expectedInput, expectedAnswer) ∈ nextAligned.consumed := by
  have inert := consume_scheduler_native_gamma_cached_is_inert transitionFuel
    kind expectedInput expectedAnswer state entry found answerExact
  rw [inert] at success
  cases success
  exact ⟨rfl, aligned,
    exact_compiler_aligned_cached_coordinate_mem_consumed input state aligned
      expectedInput expectedAnswer entry found answerExact⟩

#print axioms lookup_pair_mem_of_table_eq_projected_fresh
#print axioms exact_compiler_aligned_cached_coordinate_mem_consumed
#print axioms exact_compiler_cached_gamma_coordinate_step
#print axioms exact_compiler_cached_gamma_coordinate_success_preserves_alignment

end

end AspisK1.V7Tag73ExactCompilerGammaCachedCoordinate
