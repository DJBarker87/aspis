import RuntimeLaterRoundLoopCorrespondence

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeFourRoundLaterRelease

open aspis_prover
open ComponentCRuntimeRoundDeepControlFlow
open ComponentCRuntimeLaterRoundLoopCorrespondence

abbrev RawQM31 := aspis_core.field.QM31
abbrev RuntimeSchedule :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeSchedule
abbrev RuntimeRelation :=
  v5_mask.relation_prover.V5IncrementalRelation
abbrev RuntimeTables :=
  v5_mask.component_c_runtime.V5ComponentCRuntimeRelationTables
abbrev RuntimeLater := Array (alloc.vec.Vec RawQM31) 3#usize

/-- Across the actual four-round control flow, each of the first three rounds
fills exactly its corresponding later-family vector and preserves the other
two; round three leaves the complete later array unchanged.  Starting from
the source-created empty vectors, the final arrays are therefore precisely
the three flattened `(fibre, slot)` lists in runtime order. -/
theorem generated_four_round_later_release_exact
    (schedule : RuntimeSchedule)
    (relation0 relation1 relation2 relation3 relation4 : RuntimeRelation)
    (folded0 folded1 folded2 folded3 folded4 : alloc.vec.Vec RawQM31)
    (later0 later1 later2 later3 later4 : RuntimeLater)
    (tables0 tables1 tables2 tables3 tables4 : RuntimeTables)
    (fibres0 fibres1 fibres2 : alloc.vec.Vec Std.U32)
    (htrace0 : GeneratedRuntimeRoundTrace schedule relation0 relation1
      folded0 folded1 later0 later1 tables0 tables1 0#usize)
    (htrace1 : GeneratedRuntimeRoundTrace schedule relation1 relation2
      folded1 folded2 later1 later2 tables1 tables2 1#usize)
    (htrace2 : GeneratedRuntimeRoundTrace schedule relation2 relation3
      folded2 folded3 later2 later3 tables2 tables3 2#usize)
    (htrace3 : GeneratedRuntimeRoundTrace schedule relation3 relation4
      folded3 folded4 later3 later4 tables3 tables4 3#usize)
    (hfibres0 : schedule.later_fibres.val[0]! = fibres0)
    (hfibres1 : schedule.later_fibres.val[1]! = fibres1)
    (hfibres2 : schedule.later_fibres.val[2]! = fibres2)
    (hempty0 : later0.val[0]!.val = [])
    (hempty1 : later0.val[1]!.val = [])
    (hempty2 : later0.val[2]!.val = [])
    (hread0 : ∀ fibre ∈ fibres0.val,
      4 * fibre.val + 4 ≤ folded1.val.length)
    (hread1 : ∀ fibre ∈ fibres1.val,
      4 * fibre.val + 4 ≤ folded2.val.length)
    (hread2 : ∀ fibre ∈ fibres2.val,
      4 * fibre.val + 4 ≤ folded3.val.length)
    (hcapacity0 : 4 * fibres0.val.length ≤ Std.Usize.max)
    (hcapacity1 : 4 * fibres1.val.length ≤ Std.Usize.max)
    (hcapacity2 : 4 * fibres2.val.length ≤ Std.Usize.max) :
    later4.val[0]!.val =
        releasedFibresPrefix (alloc.vec.Vec.deref folded1)
          fibres0 fibres0.val.length ∧
    later4.val[1]!.val =
        releasedFibresPrefix (alloc.vec.Vec.deref folded2)
          fibres1 fibres1.val.length ∧
    later4.val[2]!.val =
        releasedFibresPrefix (alloc.vec.Vec.deref folded3)
          fibres2 fibres2.val.length := by
  have hcap0 :
      later0.val[0]!.val.length + 4 * fibres0.val.length ≤
        Std.Usize.max := by
    rw [hempty0]
    simpa using hcapacity0
  have hround0 := generated_runtime_round_trace_later_exact
    schedule relation0 relation1 folded0 folded1 later0 later1
    tables0 tables1 0#usize fibres0 htrace0 (by norm_num)
    hfibres0 hread0 hcap0
  have hround0Nat :
      later1.val[0]!.val = later0.val[0]!.val ++
        releasedFibresPrefix (alloc.vec.Vec.deref folded1)
          fibres0 fibres0.val.length := by
    simpa using hround0
  have hround0Preserves := generated_runtime_round_trace_later_preserves_other
    schedule relation0 relation1 folded0 folded1 later0 later1
    tables0 tables1 0#usize fibres0 htrace0 (by norm_num)
    hfibres0 hread0 hcap0
  have hlater1One : later1.val[1]! = later0.val[1]! :=
    hround0Preserves (1 : Fin 3) (by norm_num)
  have hlater1Two : later1.val[2]! = later0.val[2]! :=
    hround0Preserves (2 : Fin 3) (by norm_num)
  have hcap1 :
      later1.val[1]!.val.length + 4 * fibres1.val.length ≤
        Std.Usize.max := by
    rw [hlater1One, hempty1]
    simpa using hcapacity1
  have hround1 := generated_runtime_round_trace_later_exact
    schedule relation1 relation2 folded1 folded2 later1 later2
    tables1 tables2 1#usize fibres1 htrace1 (by norm_num)
    hfibres1 hread1 hcap1
  have hround1Nat :
      later2.val[1]!.val = later1.val[1]!.val ++
        releasedFibresPrefix (alloc.vec.Vec.deref folded2)
          fibres1 fibres1.val.length := by
    simpa using hround1
  have hround1Preserves := generated_runtime_round_trace_later_preserves_other
    schedule relation1 relation2 folded1 folded2 later1 later2
    tables1 tables2 1#usize fibres1 htrace1 (by norm_num)
    hfibres1 hread1 hcap1
  have hlater2Zero : later2.val[0]! = later1.val[0]! :=
    hround1Preserves (0 : Fin 3) (by norm_num)
  have hlater2Two : later2.val[2]! = later1.val[2]! :=
    hround1Preserves (2 : Fin 3) (by norm_num)
  have hcap2 :
      later2.val[2]!.val.length + 4 * fibres2.val.length ≤
        Std.Usize.max := by
    rw [hlater2Two, hlater1Two, hempty2]
    simpa using hcapacity2
  have hround2 := generated_runtime_round_trace_later_exact
    schedule relation2 relation3 folded2 folded3 later2 later3
    tables2 tables3 2#usize fibres2 htrace2 (by norm_num)
    hfibres2 hread2 hcap2
  have hround2Nat :
      later3.val[2]!.val = later2.val[2]!.val ++
        releasedFibresPrefix (alloc.vec.Vec.deref folded3)
          fibres2 fibres2.val.length := by
    simpa using hround2
  have hround2Preserves := generated_runtime_round_trace_later_preserves_other
    schedule relation2 relation3 folded2 folded3 later2 later3
    tables2 tables3 2#usize fibres2 htrace2 (by norm_num)
    hfibres2 hread2 hcap2
  have hlater3Zero : later3.val[0]! = later2.val[0]! :=
    hround2Preserves (0 : Fin 3) (by norm_num)
  have hlater3One : later3.val[1]! = later2.val[1]! :=
    hround2Preserves (1 : Fin 3) (by norm_num)
  have hlater4 : later4 = later3 := by
    have h := htrace3.2.2.1
    rw [if_neg (by norm_num : ¬ (3#usize < 3#usize))] at h
    exact h
  rw [hlater4]
  constructor
  · rw [hlater3Zero, hlater2Zero, hround0Nat, hempty0]
    simp
  constructor
  · rw [hlater3One, hround1Nat, hlater1One, hempty1]
    simp
  · rw [hround2Nat, hlater2Two, hlater1Two, hempty2]
    simp

#print axioms generated_four_round_later_release_exact

end aspis_prover.ComponentCRuntimeFourRoundLaterRelease
