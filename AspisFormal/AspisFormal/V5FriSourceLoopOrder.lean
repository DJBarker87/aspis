import AspisFormal.V5MerkleConsumedValueBridge

/-!
# Source-shaped order of the V5 FRI opening reads

The production FRI checker has one loop over the layer-zero query list and
three loops over the later index lists.  The first three loops keep a mutable
ordinal for the next layer and pass it to
`opening_value_for_monotone_index`; the fourth loop reads the terminal layer
directly.

This file records those calls in their source order.  It proves that, for an
exact accepted opening, every mutable lookup starts no later than the unique
requested parent, every intervening entry is smaller, and the returned
ordinal/value is exactly the one used by `friReadScheduleFromDriver`.  These
are precisely the hypotheses of the extracted monotone-lookup theorem.

The generic observation boundary below asks that the four Rust loops emit
this trace.  The exact unchanged-source extraction and the concrete accepted-
call adapter discharge it in
`aeneas-verif/v5-fri-consumer-exact-20260815`; no cryptographic assumption is
used for that read-order result.
-/

namespace AspisV5FriSourceLoopOrder

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5MerkleConsumedValueBridge

/-- One call to the production monotone opening lookup.  `startOrdinal` is
the mutable ordinal on entry and `resultOrdinal` is its value on success. -/
structure MonotoneOpeningCall where
  sourceIndex : Nat
  requestedParent : Nat
  startOrdinal : Nat
  resultOrdinal : Nat
  returnedValue : List Byte
  deriving DecidableEq

/-- Source-shaped traversal of one FRI layer.  On success the production
helper leaves the mutable ordinal at the requested parent's position, which
becomes the next call's starting ordinal. -/
def monotoneOpeningCallsAux
    (opening : ReturnedOpening) (targetIndices : List Nat) :
    Nat -> List Nat -> List MonotoneOpeningCall
  | _start, [] => []
  | start, sourceIndex :: rest =>
      let requestedParent := sourceIndex / 4
      let resultOrdinal := targetIndices.idxOf requestedParent
      { sourceIndex := sourceIndex
        requestedParent := requestedParent
        startOrdinal := start
        resultOrdinal := resultOrdinal
        returnedValue := returnedValueOrEmpty opening resultOrdinal } ::
        monotoneOpeningCallsAux opening targetIndices resultOrdinal rest

def monotoneOpeningCalls
    (opening : ReturnedOpening) (sourceIndices targetIndices : List Nat) :
    List MonotoneOpeningCall :=
  monotoneOpeningCallsAux opening targetIndices 0 sourceIndices

/-- All facts needed to apply the extracted monotone-lookup theorem to one
call.  In particular, the requested entry is present at `resultOrdinal` and
every entry scanned over by the production `while` is strictly smaller. -/
def MonotoneOpeningCall.Valid
    (opening : ReturnedOpening) (targetIndices : List Nat)
    (call : MonotoneOpeningCall) : Prop :=
  call.requestedParent = call.sourceIndex / 4 ∧
    call.startOrdinal ≤ call.resultOrdinal ∧
    call.resultOrdinal < targetIndices.length ∧
    targetIndices[call.resultOrdinal]? = some call.requestedParent ∧
    (∀ position, (hpositionBound : position < targetIndices.length) ->
      call.startOrdinal ≤ position -> position < call.resultOrdinal ->
      targetIndices[position] < call.requestedParent) ∧
    call.returnedValue =
      returnedValueOrEmpty opening call.resultOrdinal

@[simp] theorem monotoneOpeningCallsAux_length
    (opening : ReturnedOpening) (targetIndices sourceIndices : List Nat)
    (start : Nat) :
    (monotoneOpeningCallsAux opening targetIndices start sourceIndices).length =
      sourceIndices.length := by
  induction sourceIndices generalizing start with
  | nil => rfl
  | cons sourceIndex rest ih =>
      simp [monotoneOpeningCallsAux, ih]

@[simp] theorem monotoneOpeningCallsAux_sourceIndices
    (opening : ReturnedOpening) (targetIndices sourceIndices : List Nat)
    (start : Nat) :
    (monotoneOpeningCallsAux opening targetIndices start sourceIndices).map
        (fun call => call.sourceIndex) = sourceIndices := by
  induction sourceIndices generalizing start with
  | nil => rfl
  | cons sourceIndex rest ih =>
      simp [monotoneOpeningCallsAux, ih]

@[simp] theorem monotoneOpeningCallsAux_resultOrdinals
    (opening : ReturnedOpening) (targetIndices sourceIndices : List Nat)
    (start : Nat) :
    (monotoneOpeningCallsAux opening targetIndices start sourceIndices).map
        (fun call => call.resultOrdinal) =
      sourceIndices.map (fun index => targetIndices.idxOf (index / 4)) := by
  induction sourceIndices generalizing start with
  | nil => rfl
  | cons sourceIndex rest ih =>
      simp [monotoneOpeningCallsAux, ih]

theorem getElem_lt_getElem_of_pairwise_le_of_nodup
    (values : List Nat) (hsorted : values.Pairwise (.≤.))
    (hnodup : values.Nodup)
    {left right : Nat} (hleft : left < values.length)
    (hright : right < values.length) (hlt : left < right) :
    values[left] < values[right] := by
  have hle := hsorted.rel_get_of_lt
    (a := (⟨left, hleft⟩ : Fin values.length))
    (b := (⟨right, hright⟩ : Fin values.length)) (by simpa using hlt)
  have hne : values[left] ≠ values[right] := by
    intro heq
    have hpositions : left = right :=
      hnodup.getElem_inj_iff.mp heq
    omega
  have hle' : values[left] ≤ values[right] := by
    simpa using hle
  exact Nat.lt_of_le_of_ne hle' hne

private theorem monotoneOpeningCallsAux_all_valid
    (opening : ReturnedOpening) (targetIndices sourceIndices : List Nat)
    (start : Nat)
    (htargetSorted : targetIndices.Pairwise (.≤.))
    (htargetNodup : targetIndices.Nodup)
    (hparents : ∀ index ∈ sourceIndices, index / 4 ∈ targetIndices)
    (hordinals :
      (sourceIndices.map (fun index =>
        targetIndices.idxOf (index / 4))).Pairwise (.≤.))
    (hstart : ∀ index, sourceIndices.head? = some index ->
      start ≤ targetIndices.idxOf (index / 4)) :
    ∀ call ∈ monotoneOpeningCallsAux opening targetIndices start sourceIndices,
      call.Valid opening targetIndices := by
  induction sourceIndices generalizing start with
  | nil => simp [monotoneOpeningCallsAux]
  | cons sourceIndex rest ih =>
      intro call hcall
      simp only [monotoneOpeningCallsAux, List.mem_cons] at hcall
      rcases hcall with rfl | htail
      · have hparent : sourceIndex / 4 ∈ targetIndices :=
          hparents sourceIndex (by simp)
        have hbound := List.idxOf_lt_length_of_mem hparent
        have hget := List.getElem?_idxOf hparent
        refine ⟨rfl, ?_, hbound, hget, ?_, rfl⟩
        · exact hstart sourceIndex (by simp)
        · intro position hpositionBound _hstartPosition hpositionTarget
          change position < targetIndices.idxOf (sourceIndex / 4) at hpositionTarget
          have hstrict := getElem_lt_getElem_of_pairwise_le_of_nodup
            targetIndices htargetSorted htargetNodup
            hpositionBound hbound hpositionTarget
          have htargetValue :
              targetIndices[targetIndices.idxOf (sourceIndex / 4)] =
                sourceIndex / 4 := by
            exact List.idxOf_get hbound
          rw [htargetValue] at hstrict
          exact hstrict
      · apply ih (targetIndices.idxOf (sourceIndex / 4))
        · exact fun index hindex => hparents index (by simp [hindex])
        · exact (List.pairwise_cons.mp hordinals).2
        · intro index hhead
          have hindexMem : index ∈ rest := by
            cases rest with
            | nil => simp at hhead
            | cons head tail =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                subst index
                simp
          have hheadLeAll := (List.pairwise_cons.mp hordinals).1
          exact hheadLeAll _ (by
            simpa only [List.mem_map] using
              ⟨index, hindexMem, rfl⟩)
        · exact htail

/-- A sorted, duplicate-free target list containing every requested parent
makes every source-shaped mutable lookup valid. -/
theorem monotoneOpeningCalls_all_valid
    (opening : ReturnedOpening) (sourceIndices targetIndices : List Nat)
    (htargetSorted : targetIndices.Pairwise (.≤.))
    (htargetNodup : targetIndices.Nodup)
    (hparents : ∀ index ∈ sourceIndices, index / 4 ∈ targetIndices)
    (hordinals :
      (sourceIndices.map (fun index =>
        targetIndices.idxOf (index / 4))).Pairwise (.≤.)) :
    ∀ call ∈ monotoneOpeningCalls opening sourceIndices targetIndices,
      call.Valid opening targetIndices := by
  apply monotoneOpeningCallsAux_all_valid opening targetIndices sourceIndices 0
    htargetSorted htargetNodup hparents hordinals
  intro index _hhead
  omega

/-! ## The exact three mutable lookup sequences -/

structure FriParentLookupCalls where
  layer0ToLine1 : List MonotoneOpeningCall
  line1ToLine2 : List MonotoneOpeningCall
  line2ToLine3 : List MonotoneOpeningCall
  deriving DecidableEq

def friParentLookupCallsFromDriver (output : V5DriverOutput) :
    FriParentLookupCalls where
  layer0ToLine1 := monotoneOpeningCalls output.line1
    output.layer0Indices output.line1Indices
  line1ToLine2 := monotoneOpeningCalls output.line2
    output.line1Indices output.line2Indices
  line2ToLine3 := monotoneOpeningCalls output.line3
    output.line2Indices output.line3Indices

@[simp] theorem monotoneOpeningCallsAux_observations
    (opening : ReturnedOpening) (targetIndices sourceIndices : List Nat)
    (start : Nat) :
    (monotoneOpeningCallsAux opening targetIndices start sourceIndices).map
        (fun call => (call.sourceIndex, call.requestedParent,
          call.resultOrdinal, call.returnedValue)) =
      sourceIndices.map (fun sourceIndex =>
        (sourceIndex, sourceIndex / 4,
          targetIndices.idxOf (sourceIndex / 4),
          returnedValueOrEmpty opening
            (targetIndices.idxOf (sourceIndex / 4)))) := by
  induction sourceIndices generalizing start with
  | nil => rfl
  | cons sourceIndex rest ih =>
      simp [monotoneOpeningCallsAux, ih]

theorem parentLookupCalls_match_read_schedule
    (output : V5DriverOutput) :
    ((friParentLookupCallsFromDriver output).layer0ToLine1.map
        (fun call => (call.sourceIndex, call.requestedParent,
          call.resultOrdinal, call.returnedValue))) =
        ((friReadScheduleFromDriver output).layer0ToLine1.map
          (fun read => (read.query, read.parentIndex,
            read.parentOrdinal, read.parentValue))) ∧
      ((friParentLookupCallsFromDriver output).line1ToLine2.map
        (fun call => (call.sourceIndex, call.requestedParent,
          call.resultOrdinal, call.returnedValue))) =
        ((friReadScheduleFromDriver output).line1ToLine2.map
          (fun read => (read.index, read.parentIndex,
            read.parentOrdinal, read.outgoing))) ∧
      ((friParentLookupCallsFromDriver output).line2ToLine3.map
        (fun call => (call.sourceIndex, call.requestedParent,
          call.resultOrdinal, call.returnedValue))) =
        ((friReadScheduleFromDriver output).line2ToLine3.map
          (fun read => (read.index, read.parentIndex,
            read.parentOrdinal, read.outgoing))) := by
  constructor
  · rw [show
      (friParentLookupCallsFromDriver output).layer0ToLine1 =
        monotoneOpeningCallsAux output.line1 output.line1Indices 0
          output.layer0Indices by rfl]
    rw [monotoneOpeningCallsAux_observations]
    simp [friReadScheduleFromDriver, layerZeroReadOfDriver]
  constructor
  · rw [show
      (friParentLookupCallsFromDriver output).line1ToLine2 =
        monotoneOpeningCallsAux output.line2 output.line2Indices 0
          output.line1Indices by rfl]
    rw [monotoneOpeningCallsAux_observations]
    simp [friReadScheduleFromDriver, line1ReadOfDriver]
  · rw [show
      (friParentLookupCallsFromDriver output).line2ToLine3 =
        monotoneOpeningCallsAux output.line3 output.line3Indices 0
          output.line2Indices by rfl]
    rw [monotoneOpeningCallsAux_observations]
    simp [friReadScheduleFromDriver, line2ReadOfDriver]

theorem exactRun_parentLookupCalls_all_valid
    {sha256 roots queries} (run : ExactV5Run sha256 roots queries) :
    (∀ call ∈
        (friParentLookupCallsFromDriver
          (driverOutputOfRun run [])).layer0ToLine1,
      call.Valid (openingOfTrace (run.sections .line1))
        (orderedActiveIndices .line1 queries 0)) ∧
    (∀ call ∈
        (friParentLookupCallsFromDriver
          (driverOutputOfRun run [])).line1ToLine2,
      call.Valid (openingOfTrace (run.sections .line2))
        (orderedActiveIndices .line2 queries 0)) ∧
    (∀ call ∈
        (friParentLookupCallsFromDriver
          (driverOutputOfRun run [])).line2ToLine3,
      call.Valid (openingOfTrace (run.sections .line3))
        (orderedActiveIndices .line3 queries 0)) := by
  simp only [friParentLookupCallsFromDriver, driverOutputOfRun]
  constructor
  · apply monotoneOpeningCalls_all_valid
    · exact orderedActiveIndices_sorted .line1 queries 0
    · exact Finset.sort_nodup _ _
    · intro index hindex
      apply layer0_parent_requests_all_present queries (index / 4)
      exact List.mem_map.mpr ⟨index, hindex, rfl⟩
    · exact layer0_parentOrdinals_sorted queries
  constructor
  · apply monotoneOpeningCalls_all_valid
    · exact orderedActiveIndices_sorted .line2 queries 0
    · exact Finset.sort_nodup _ _
    · intro index hindex
      apply line1_parent_requests_all_present queries (index / 4)
      exact List.mem_map.mpr ⟨index, hindex, rfl⟩
    · exact line1_parentOrdinals_sorted queries
  · apply monotoneOpeningCalls_all_valid
    · exact orderedActiveIndices_sorted .line3 queries 0
    · exact Finset.sort_nodup _ _
    · intro index hindex
      apply line2_parent_requests_all_present queries (index / 4)
      exact List.mem_map.mpr ⟨index, hindex, rfl⟩
    · exact line2_parentOrdinals_sorted queries

/-! ## Direct `enumerate()` reads -/

theorem mapIdx_uses_idxOf_of_nodup
    {A : Type} (values : List Nat) (hnodup : values.Nodup)
    (read : Nat -> Nat -> A) :
    values.mapIdx read =
      values.map (fun value => read (values.idxOf value) value) := by
  rw [List.mapIdx_eq_ofFn]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.length_ofFn, List.length_map] at hleft hright
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [hnodup.idxOf_getElem index hleft]
    rfl

def layerZeroReadAtOrdinal (output : V5DriverOutput)
    (ordinal query : Nat) : LayerZeroRead :=
  { (layerZeroReadOfDriver output query) with
    ordinal := ordinal
    c1Value := returnedValueOrEmpty output.c1 ordinal
    c2Value := returnedValueOrEmpty output.c2 ordinal }

def line1ReadAtOrdinal (output : V5DriverOutput)
    (ordinal index : Nat) : LineTransitionRead :=
  { (line1ReadOfDriver output index) with
    ordinal := ordinal
    incoming := returnedValueOrEmpty output.line1 ordinal }

def line2ReadAtOrdinal (output : V5DriverOutput)
    (ordinal index : Nat) : LineTransitionRead :=
  { (line2ReadOfDriver output index) with
    ordinal := ordinal
    incoming := returnedValueOrEmpty output.line2 ordinal }

def terminalReadAtOrdinal (output : V5DriverOutput)
    (ordinal index : Nat) : TerminalRead :=
  { (terminalReadOfDriver output index) with
    ordinal := ordinal
    incoming := returnedValueOrEmpty output.line3 ordinal }

/-- The four lists written in the same `enumerate()` shape as the production
Rust loops. -/
def sourceShapedFriReadSchedule (output : V5DriverOutput) : FriReadSchedule where
  layer0ToLine1 := output.layer0Indices.mapIdx
    (layerZeroReadAtOrdinal output)
  line1ToLine2 := output.line1Indices.mapIdx
    (line1ReadAtOrdinal output)
  line2ToLine3 := output.line2Indices.mapIdx
    (line2ReadAtOrdinal output)
  line3ToFinal := output.line3Indices.mapIdx
    (terminalReadAtOrdinal output)

/-- For every parser output whose four returned index arrays contain no
duplicates, the literal `enumerate()` schedule is exactly the deterministic
schedule used by the existing authentication-to-FRI bridge. -/
theorem sourceShapedFriReadSchedule_eq
    (output : V5DriverOutput)
    (hlayer0 : output.layer0Indices.Nodup)
    (hline1 : output.line1Indices.Nodup)
    (hline2 : output.line2Indices.Nodup)
    (hline3 : output.line3Indices.Nodup) :
    sourceShapedFriReadSchedule output = friReadScheduleFromDriver output := by
  unfold sourceShapedFriReadSchedule friReadScheduleFromDriver
  congr 1
  · rw [mapIdx_uses_idxOf_of_nodup output.layer0Indices hlayer0]
    apply List.map_congr_left
    intro query _hquery
    simp [layerZeroReadAtOrdinal, layerZeroReadOfDriver]
  · rw [mapIdx_uses_idxOf_of_nodup output.line1Indices hline1]
    apply List.map_congr_left
    intro index _hindex
    simp [line1ReadAtOrdinal, line1ReadOfDriver]
  · rw [mapIdx_uses_idxOf_of_nodup output.line2Indices hline2]
    apply List.map_congr_left
    intro index _hindex
    simp [line2ReadAtOrdinal, line2ReadOfDriver]
  · rw [mapIdx_uses_idxOf_of_nodup output.line3Indices hline3]
    apply List.map_congr_left
    intro index _hindex
    simp [terminalReadAtOrdinal, terminalReadOfDriver]

theorem exactRun_sourceShapedFriReadSchedule_eq
    {sha256 roots queries} (run : ExactV5Run sha256 roots queries) :
    sourceShapedFriReadSchedule (driverOutputOfRun run []) =
      friReadScheduleOfRun run := by
  rw [sourceShapedFriReadSchedule_eq]
  · exact friReadScheduleFromDriver_eq_run run
  all_goals exact Finset.sort_nodup _ _

/-! ## Generic observation boundary and concrete source discharge -/

/-- Exact successful-read observation required from the production
`check_v5_fri_queries` function.  It says that the function reads the returned
opening views in the literal order of its four Rust loops:

* `queries.iter().enumerate()` for C1, C2, and the first parent layer;
* the first later-layer loop;
* the second later-layer loop; and
* the terminal later-layer loop.

This statement contains no Merkle or decoder assumption.  The driver output
already contains the five returned byte views and four returned index arrays;
`sourceShapedFriReadSchedule` merely records the exact accessor calls made on
those values. -/
def CheckV5FriQueriesSuccessfulReadTraceEquality
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation) :
    Prop :=
  ∀ call observation, rustObservation call = some observation ->
    observation.friReads = sourceShapedFriReadSchedule observation.driver

/- The concrete theorem for the accepted production adapter is
`AspisV5FriConsumerObservationBridge.accepted_resolver_read_trace_equality` in
the pinned Aeneas replay package.  This module keeps the proposition generic
so the maintained mathematical development does not import generated source
snapshots. -/

/-- Once the five returned parser views are fixed to an exact authenticated
run, the literal four-loop read order is exactly the maintained FRI read
schedule.  This removes the old broad FRI-consumer premise: the only remaining
source fact is the successful read trace of `check_v5_fri_queries` itself. -/
theorem openingParser_and_checkV5FriQueriesReadTrace_imply_consumerEquality
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
    (hparser : ExactRustV5OpeningParserOutputEquality sha256 rustObservation)
    (hreads : CheckV5FriQueriesSuccessfulReadTraceEquality rustObservation) :
    ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation := by
  apply (exactRustV5OpeningAndFriConsumerEquality_iff_split
    sha256 rustObservation).2
  refine ⟨hparser, ?_⟩
  intro call observation run hrust hbytes hdriver
  calc
    observation.friReads =
        sourceShapedFriReadSchedule observation.driver :=
      hreads call observation hrust
    _ = sourceShapedFriReadSchedule (driverOutputOfRun run []) := by
      rw [hdriver]
    _ = friReadScheduleOfRun run :=
      exactRun_sourceShapedFriReadSchedule_eq run

/-- Equivalent smaller split of the former whole parser-and-consumer source
boundary.  The reverse direction is stated relative to an exact parser output:
under that fact, the maintained schedule and the literal source-shaped
schedule coincide. -/
theorem openingAndFriConsumerEquality_iff_parser_and_checkReadTrace
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation) :
    ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation ↔
      ExactRustV5OpeningParserOutputEquality sha256 rustObservation ∧
        CheckV5FriQueriesSuccessfulReadTraceEquality rustObservation := by
  constructor
  · intro hfull
    have hsplit := (exactRustV5OpeningAndFriConsumerEquality_iff_split
      sha256 rustObservation).1 hfull
    refine ⟨hsplit.1, ?_⟩
    intro call observation hrust
    obtain ⟨run, hbytes, hdriver⟩ := hsplit.1 call observation hrust
    have hfri := hsplit.2 call observation run hrust hbytes hdriver
    calc
      observation.friReads = friReadScheduleOfRun run := hfri
      _ = sourceShapedFriReadSchedule (driverOutputOfRun run []) :=
        (exactRun_sourceShapedFriReadSchedule_eq run).symm
      _ = sourceShapedFriReadSchedule observation.driver := by rw [hdriver]
  · rintro ⟨hparser, hreads⟩
    exact openingParser_and_checkV5FriQueriesReadTrace_imply_consumerEquality
      sha256 rustObservation hparser hreads

theorem shiftRight_two_eq_div_four (index : Nat) :
    index >>> 2 = index / 4 := by
  rw [Nat.shiftRight_eq_div_pow]

#print axioms monotoneOpeningCalls_all_valid
#print axioms parentLookupCalls_match_read_schedule
#print axioms exactRun_parentLookupCalls_all_valid
#print axioms mapIdx_uses_idxOf_of_nodup
#print axioms sourceShapedFriReadSchedule_eq
#print axioms exactRun_sourceShapedFriReadSchedule_eq
#print axioms openingParser_and_checkV5FriQueriesReadTrace_imply_consumerEquality
#print axioms openingAndFriConsumerEquality_iff_parser_and_checkReadTrace
#print axioms shiftRight_two_eq_div_four

end AspisV5FriSourceLoopOrder
