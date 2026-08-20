import V5MerkleQueryReuseProof
import V5MerkleTopologyConstructorModel
import V5MerkleUnchangedFull.Funs
import V5MerkleUnchangedFullSectionTopologyAlignment

/-! Connect the unchanged extracted query-index helper to the maintained
five-section index lists. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedQueryModelBridge

open V5MerkleUnchangedFull
open V5MerkleQueryReuseProof
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction
open AspisV5MerkleTopologyConstructorModel
open AspisV5MerkleUnchangedFullSectionTopologyAlignment

abbrev QueryIndices :=
  aspis_core.circle_line_merkle.CircleLineQueryIndices

/-- Success of the unchanged namespace adapter inherits the exact layer-zero
and three shifted lists proved about the extracted helper it calls. -/
theorem generated_adapter_query_indices_exact
    (queries : Slice Std.U32) (queryCount : Std.Usize)
    (indices : QueryIndices)
    (hne : queries.val ≠ [])
    (hrange : ∀ query ∈ queries.val,
      query < UScalar.cast .U32 queryCount)
    (hrun :
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries queryCount = .ok (.Ok indices)) :
    indices.layer0.val = expectedLayer0 queries.val ∧
      indices.later.val.map (fun later => later.val) =
        expectedLater queries.val := by
  obtain ⟨reuseResult, reuseRun, reusePost⟩ := WP.spec_imp_exists
    (generated_query_indices_exact queries queryCount hne hrange)
  unfold
    aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count at hrun
  rw [reuseRun] at hrun
  rcases reusePost with ⟨output, hresult, hlayer0, hlater⟩
  subst reuseResult
  simp only [Bind.bind, Aeneas.Std.bind] at hrun
  have hindices : mapQueryIndices output = indices := by
    exact core.result.Result.Ok.inj (Result.ok.inj hrun)
  rw [← hindices]
  exact ⟨hlayer0, hlater⟩

private theorem array_index_vec_value
    {n : Std.Usize} (values : Array (alloc.vec.Vec Std.U32) n)
    (index : Std.Usize) (output : alloc.vec.Vec Std.U32)
    (bound : index.val < values.length)
    (run : Array.index_usize values index = .ok output) :
    output.val = (values.val.map (fun value => value.val))[index.val]! := by
  obtain ⟨read, readRun, readValue⟩ := WP.spec_imp_exists
    (Array.index_usize_spec values index bound)
  have readEq : read = output := Result.ok.inj (readRun.symm.trans run)
  calc
    output.val = read.val := congrArg (fun value => value.val) readEq.symm
    _ = values.val[index.val].val := congrArg (fun value => value.val) readValue
    _ = (values.val.map (fun value => value.val))[index.val]! := by
      have valueSome :
          (values.val.map (fun value => value.val))[index.val]? =
            some values.val[index.val].val := by
        have bound' : index.val < values.val.length := by simpa using bound
        have inputSome : values.val[index.val]? =
            some values.val[index.val] := by simp [bound']
        simpa [List.getElem?_map, inputSome]
      exact (List.getElem!_of_getElem? valueSome).symm

/-- Project the three fixed later arrays after exact query-index derivation. -/
theorem generated_adapter_later_reads_exact
    (queries : Slice Std.U32) (queryCount : Std.Usize)
    (indices : QueryIndices)
    (later0 later1 later2 : alloc.vec.Vec Std.U32)
    (hne : queries.val ≠ [])
    (hrange : ∀ query ∈ queries.val,
      query < UScalar.cast .U32 queryCount)
    (hrun :
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        queries queryCount = .ok (.Ok indices))
    (read0 : Array.index_usize indices.later 0#usize = .ok later0)
    (read1 : Array.index_usize indices.later 1#usize = .ok later1)
    (read2 : Array.index_usize indices.later 2#usize = .ok later2) :
    indices.layer0.val = expectedLayer0 queries.val ∧
      later0.val = (expectedLater queries.val)[0]! ∧
      later1.val = (expectedLater queries.val)[1]! ∧
      later2.val = (expectedLater queries.val)[2]! := by
  obtain ⟨layer0, later⟩ := generated_adapter_query_indices_exact
    queries queryCount indices hne hrange hrun
  have h0 := array_index_vec_value indices.later 0#usize later0 (by scalar_tac)
    read0
  have h1 := array_index_vec_value indices.later 1#usize later1 (by scalar_tac)
    read1
  have h2 := array_index_vec_value indices.later 2#usize later2 (by scalar_tac)
    read2
  refine ⟨layer0, ?_, ?_, ?_⟩
  · calc
      later0.val = (indices.later.val.map (fun value => value.val))[0]! := h0
      _ = (expectedLater queries.val)[0]! :=
        congrArg (fun values => values[0]!) later
  · calc
      later1.val = (indices.later.val.map (fun value => value.val))[1]! := h1
      _ = (expectedLater queries.val)[1]! :=
        congrArg (fun values => values[1]!) later
  · calc
      later2.val = (indices.later.val.map (fun value => value.val))[2]! := h2
      _ = (expectedLater queries.val)[2]! :=
        congrArg (fun values => values[2]!) later

/-- Direct division by a released power of four maps the sorted layer-zero
set to the corresponding maintained shared level. -/
theorem sorted_division_image_shared_level_zero
    (queries : Finset V5Query) (level : Nat) :
    ((sharedLevelIndices queries 0).toFinset.image
        (fun value => value / 4 ^ level)).sort (.≤.) =
      sharedLevelIndices queries level := by
  unfold sharedLevelIndices orderedActiveIndices activeIndices
  congr 1
  ext value
  simp only [Finset.mem_image, Finset.mem_sort, List.mem_toFinset]
  constructor
  · rintro ⟨input, ⟨query, hquery, hinput⟩, hvalue⟩
    refine ⟨query, hquery, ?_⟩
    subst input
    subst value
    simp [sectionIndex, indexAtRadixLevel_eq_div_pow]
  · rintro ⟨query, hquery, hvalue⟩
    refine ⟨query.val, ⟨query, hquery, ?_⟩, ?_⟩
    · simp [sectionIndex, indexAtRadixLevel_eq_div_pow]
    · simpa [sectionIndex, indexAtRadixLevel_eq_div_pow] using hvalue

/-- The exact sorted layer-zero output is also the maintained C1 and C2 leaf
list. -/
theorem expected_layer0_models_c1_c2
    (input : List Std.U32) (queries : Finset V5Query)
    (model : (expectedLayer0 input).map (fun index => index.val) =
      sharedLevelIndices queries 0) :
    (expectedLayer0 input).map (fun index => index.val) =
        orderedActiveIndices .c1 queries 0 ∧
      (expectedLayer0 input).map (fun index => index.val) =
        orderedActiveIndices .c2 queries 0 := by
  letI : V5MerkleUnchangedCompat.HashContext := {
    hash := fun _ => Array.repeat 32#usize 0#u8 }
  constructor
  · simpa [sharedLevelIndices] using model
  · rw [model]
    rw [orderedActiveIndices_eq_shared_suffix]
    rfl

/-- A nonempty maintained query set cannot be represented by an empty raw
query slice. -/
theorem query_model_implies_nonempty
    (input : List Std.U32) (queries : Finset V5Query)
    (queryCount : queries.card = 18)
    (model : (expectedLayer0 input).map (fun index => index.val) =
      sharedLevelIndices queries 0) :
    input ≠ [] := by
  intro inputEmpty
  subst input
  have queriesNonempty : queries.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨query, queryMem⟩ := queriesNonempty
  have activeMem : query.val ∈ sharedLevelIndices queries 0 := by
    unfold sharedLevelIndices orderedActiveIndices activeIndices
    simp only [Finset.mem_sort, Finset.mem_image]
    exact ⟨query, queryMem, by simp [sectionIndex, indexAtRadixLevel]⟩
  have impossible : query.val ∈
      (expectedLayer0 ([] : List Std.U32)).map (fun index => index.val) := by
    rw [model]
    exact activeMem
  simp [expectedLayer0] at impossible

/-- The query-view equation itself proves that every raw query is within the
released 17-bit domain; no separate range assumption is needed. -/
theorem query_model_implies_17_bit_range
    (input : List Std.U32) (queries : Finset V5Query)
    (model : (expectedLayer0 input).map (fun index => index.val) =
      sharedLevelIndices queries 0) :
    ∀ query ∈ input, query.val < 131072 := by
  intro query queryMem
  have expectedMem : query ∈ expectedLayer0 input := by
    simp [expectedLayer0, queryMem]
  have valueMem : query.val ∈
      (expectedLayer0 input).map (fun index => index.val) :=
    List.mem_map.mpr ⟨query, expectedMem, rfl⟩
  rw [model] at valueMem
  unfold sharedLevelIndices orderedActiveIndices activeIndices at valueMem
  simp only [Finset.mem_sort, Finset.mem_image] at valueMem
  obtain ⟨modelQuery, _modelQueryMem, valueEq⟩ := valueMem
  have modelBound : modelQuery.val < 131072 := modelQuery.isLt
  simpa [sectionIndex, indexAtRadixLevel] using valueEq ▸ modelBound

/-- Each of the three exact shifted outputs is the maintained leaf-index list
for its corresponding later section. -/
theorem expected_later_models_sections
    (input : List Std.U32) (queries : Finset V5Query)
    (model : (expectedLayer0 input).map (fun index => index.val) =
      sharedLevelIndices queries 0) :
    (expectedLater input)[0]!.map (fun index => index.val) =
        orderedActiveIndices .line1 queries 0 ∧
      (expectedLater input)[1]!.map (fun index => index.val) =
        orderedActiveIndices .line2 queries 0 ∧
      (expectedLater input)[2]!.map (fun index => index.val) =
        orderedActiveIndices .line3 queries 0 := by
  letI : V5MerkleUnchangedCompat.HashContext := {
    hash := fun _ => Array.repeat 32#usize 0#u8 }
  have sorted : (expectedLayer0 input).Pairwise (.≤.) := by
    exact Finset.pairwise_sort _ _
  have shift2 := shiftedUnique_nats_eq_sorted_division_image
    (expectedLayer0 input) 2#u32 (by norm_num) sorted
  have shift4 := shiftedUnique_nats_eq_sorted_division_image
    (expectedLayer0 input) 4#u32 (by norm_num) sorted
  have shift6 := shiftedUnique_nats_eq_sorted_division_image
    (expectedLayer0 input) 6#u32 (by norm_num) sorted
  unfold expectedLater
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ,
    List.map_cons, List.map_nil]
  constructor
  · rw [shift2, model]
    have h := sorted_division_image_shared_level_zero queries 1
    norm_num at h ⊢
    rw [orderedActiveIndices_eq_shared_suffix]
    simpa [sectionRadixStart] using h
  · constructor
    · rw [shift4, model]
      have h := sorted_division_image_shared_level_zero queries 2
      norm_num at h ⊢
      rw [orderedActiveIndices_eq_shared_suffix]
      simpa [sectionRadixStart] using h
    · rw [shift6, model]
      have h := sorted_division_image_shared_level_zero queries 3
      norm_num at h ⊢
      rw [orderedActiveIndices_eq_shared_suffix]
      simpa [sectionRadixStart] using h

/-- Complete five-slice result used by the unchanged outer driver. -/
theorem generated_query_slices_model_five_sections
    (input : Slice Std.U32) (queryLimit : Std.Usize)
    (indices : QueryIndices)
    (later0 later1 later2 : alloc.vec.Vec Std.U32)
    (queries : Finset V5Query)
    (hne : input.val ≠ [])
    (hrange : ∀ query ∈ input.val,
      query < UScalar.cast .U32 queryLimit)
    (run :
      aspis_core.circle_line_merkle.derive_circle_line_query_indices_for_count
        input queryLimit = .ok (.Ok indices))
    (read0 : Array.index_usize indices.later 0#usize = .ok later0)
    (read1 : Array.index_usize indices.later 1#usize = .ok later1)
    (read2 : Array.index_usize indices.later 2#usize = .ok later2)
    (model : (expectedLayer0 input.val).map (fun index => index.val) =
      sharedLevelIndices queries 0) :
    indices.layer0.val.map (fun index => index.val) =
        orderedActiveIndices .c1 queries 0 ∧
      indices.layer0.val.map (fun index => index.val) =
        orderedActiveIndices .c2 queries 0 ∧
      later0.val.map (fun index => index.val) =
        orderedActiveIndices .line1 queries 0 ∧
      later1.val.map (fun index => index.val) =
        orderedActiveIndices .line2 queries 0 ∧
      later2.val.map (fun index => index.val) =
        orderedActiveIndices .line3 queries 0 := by
  obtain ⟨layer0, later0Exact, later1Exact, later2Exact⟩ :=
    generated_adapter_later_reads_exact input queryLimit indices later0 later1
      later2 hne hrange run read0 read1 read2
  obtain ⟨c1, c2⟩ := expected_layer0_models_c1_c2 input.val queries model
  obtain ⟨line1, line2, line3⟩ :=
    expected_later_models_sections input.val queries model
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [layer0]
    exact c1
  · rw [layer0]
    exact c2
  · rw [later0Exact]
    exact line1
  · rw [later1Exact]
    exact line2
  · rw [later2Exact]
    exact line3

#print axioms generated_adapter_query_indices_exact
#print axioms generated_adapter_later_reads_exact
#print axioms sorted_division_image_shared_level_zero
#print axioms query_model_implies_nonempty
#print axioms query_model_implies_17_bit_range
#print axioms expected_later_models_sections
#print axioms generated_query_slices_model_five_sections

end AspisV5MerkleUnchangedQueryModelBridge
