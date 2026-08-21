import V5FriConsumerValueSemantics
import V5FriConsumerReadSemantics
import V5FriCoordinateReleasedPointConnection

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-!
# Production FRI coordinates and the released tables

The unchanged consumer extraction leaves the production coordinate helper as
an external call.  The coordinate extraction proves the accepted adapter
implementation.  This file records only the source-tool boundary for the one
successful coordinate call already present in a production execution trace.
It does not assume equality for arbitrary slices, rejected calls, or inverse
functions.  All mathematical claims about the returned value are derived from
the translated adapter proof.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriConsumerCoordinateBridge

open AspisV5FriConsumerExactProof
open AspisV5FriCoordinateReleasedPointConnection
open AspisV5FriConsumerObservationBridge
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge

namespace Consumer
open V5FriConsumerExact

abbrev Output :=
  aspis_core.circle_fri.DerivedCircleQueryFoldInverses

end Consumer

namespace Coordinate
open V5FriCoordinateAdapter

abbrev Output :=
  aspis_core.circle_fri.DerivedCircleQueryFoldInverses

end Coordinate

theorem generated_indices_below_of_eq_ordered
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (_run : ExactV5Run sha256 roots queries)
    (tree : V5PrivateSection) (indices : alloc.vec.Vec Std.U32)
    (heq : generatedIndicesToNat indices =
      orderedActiveIndices tree queries 0) :
    IndicesBelow (alloc.vec.Vec.deref indices) (2 ^ binaryDepth tree) := by
  unfold IndicesBelow
  change ∀ ordinal, ordinal < indices.val.length →
    indices.val[ordinal]!.val < 2 ^ binaryDepth tree
  intro ordinal hordinal
  have hlength : indices.val.length =
      (orderedActiveIndices tree queries 0).length := by
    calc
      indices.val.length = (generatedIndicesToNat indices).length := by
        simp [generatedIndicesToNat]
      _ = (orderedActiveIndices tree queries 0).length :=
        congrArg List.length heq
  have hmodelBound : ordinal <
      (orderedActiveIndices tree queries 0).length := by omega
  let modelValue :=
    (orderedActiveIndices tree queries 0)[ordinal]'hmodelBound
  have hmember : modelValue ∈
      activeIndices tree queries 0 := by
    apply (Finset.mem_sort (.≤.)).mp
    exact List.getElem_mem hmodelBound
  obtain ⟨query, _hquery, hvalue⟩ := Finset.mem_image.mp hmember
  have hsourceValue : indices.val[ordinal]!.val =
      modelValue := by
    have hget := congrArg (fun values => values[ordinal]?) heq
    simp only [generatedIndicesToNat, List.getElem?_map] at hget
    rw [List.getElem?_eq_getElem hordinal,
      List.getElem?_eq_getElem hmodelBound] at hget
    have hbang : indices.val[ordinal]! = indices.val[ordinal] := by
      apply List.getElem!_of_getElem?
      simp [hordinal]
    rw [hbang]
    simpa [modelValue] using hget
  rw [hsourceValue, ← hvalue]
  simp only [indexAtRadixLevel]
  exact sectionIndex_lt_leaf_count tree query

theorem generated_indices_length_le_18
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (tree : V5PrivateSection) (indices : alloc.vec.Vec Std.U32)
    (heq : generatedIndicesToNat indices =
      orderedActiveIndices tree queries 0) :
    indices.val.length ≤ 18 := by
  have hlength : indices.val.length =
      (activeIndices tree queries 0).card := by
    calc
      indices.val.length = (generatedIndicesToNat indices).length := by
        simp [generatedIndicesToNat]
      _ = (orderedActiveIndices tree queries 0).length :=
        congrArg List.length heq
      _ = (activeIndices tree queries 0).card := by
        simp [orderedActiveIndices]
  rw [hlength, ← run.query_count]
  exact Finset.card_image_le

/-- Equality with one exact sorted model list identifies the generated value
at the model's unique section ordinal. -/
theorem generated_index_at_sectionOrdinal
    {tree : V5PrivateSection} {queries : Finset V5Query}
    (indices : alloc.vec.Vec Std.U32) {index : Nat}
    (hindex : index ∈ activeIndices tree queries 0)
    (heq : generatedIndicesToNat indices =
      orderedActiveIndices tree queries 0) :
    ∃ hordinal : sectionOrdinal tree queries index < indices.val.length,
      indices.val[sectionOrdinal tree queries index]!.val = index := by
  have hmodelBound := sectionOrdinal_lt_count tree hindex
  have hlength : indices.val.length =
      (orderedActiveIndices tree queries 0).length := by
    calc
      indices.val.length = (generatedIndicesToNat indices).length := by
        simp [generatedIndicesToNat]
      _ = (orderedActiveIndices tree queries 0).length :=
        congrArg List.length heq
  have hordinal : sectionOrdinal tree queries index < indices.val.length := by
    omega
  refine ⟨hordinal, ?_⟩
  have hget := congrArg
    (fun values => values[sectionOrdinal tree queries index]?) heq
  have hmodel := sectionOrdinal_getElem?_eq tree hindex
  rw [List.getElem?_eq_getElem hmodelBound] at hmodel
  have hmodelValue :
      (orderedActiveIndices tree queries 0)[sectionOrdinal tree queries index] =
        index :=
    Option.some.inj hmodel
  rw [List.getElem?_eq_getElem hmodelBound, hmodelValue] at hget
  simp only [generatedIndicesToNat, List.getElem?_map,
    List.getElem?_eq_getElem hordinal, Option.map_some,
    Option.some.injEq] at hget
  have hbang :
      indices.val[sectionOrdinal tree queries index]! =
        indices.val[sectionOrdinal tree queries index] := by
    apply List.getElem!_of_getElem?
    simp [hordinal]
  rw [hbang]
  simpa using hget

theorem generated_layer0_indices_nonempty
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (indices : alloc.vec.Vec Std.U32)
    (heq : generatedIndicesToNat indices =
      orderedActiveIndices .c1 queries 0) :
    0 < indices.val.length := by
  have hqueryCard : 0 < queries.card := by
    rw [run.query_count]
    norm_num
  have hqueries : queries.Nonempty := Finset.card_pos.mp hqueryCard
  obtain ⟨query, hquery⟩ := hqueries
  have hactive : sectionIndex .c1 query ∈ activeIndices .c1 queries 0 :=
    sectionIndex_mem_active .c1 hquery
  have hordered : 0 < (orderedActiveIndices .c1 queries 0).length := by
    have hcard : 0 < (activeIndices .c1 queries 0).card :=
      Finset.card_pos.mpr ⟨_, hactive⟩
    simpa [orderedActiveIndices] using hcard
  simpa [generatedIndicesToNat] using
    (show 0 < (generatedIndicesToNat indices).length by
      rw [heq]
      exact hordered)

theorem preparation_trace_indices_match_driver
    {openings : V5FriConsumerExact.private_openings.VerifiedV5PrivateOpenings}
    {alphas : Array V5FriConsumerExact.aspis_core.field.QM31 4#usize}
    {inverse : V5FriConsumerExact.aspis_core.field.M31 →
      V5FriConsumerExact.aspis_core.field.M31}
    {coordinates : Consumer.Output}
    {alphaPowers : Array
      (Array V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier
        3#usize) 4#usize}
    (trace : ProductionFriPreparationTrace openings alphas inverse
      coordinates alphaPowers) :
    generatedIndicesToNat trace.later0 =
        (generatedDriverOutput openings).line1Indices ∧
      generatedIndicesToNat trace.later1 =
        (generatedDriverOutput openings).line2Indices ∧
      generatedIndicesToNat trace.later2 =
        (generatedDriverOutput openings).line3Indices := by
  have h0 := trace.later0Read
  have h1 := trace.later1Read
  have h2 := trace.later2Read
  simp [Array.index_usize] at h0 h1 h2
  constructor
  · simpa [generatedDriverOutput] using
      congrArg generatedIndicesToNat h0.symm
  constructor
  · simpa [generatedDriverOutput] using
      congrArg generatedIndicesToNat h1.symm
  · simpa [generatedDriverOutput] using
      congrArg generatedIndicesToNat h2.symm

/-- Structural conversion between the duplicate Aeneas output types.  Both
translations use the same `U32` representation for `M31`. -/
def toCoordinateOutput (output : Consumer.Output) : Coordinate.Output where
  circle := output.circle
  later := output.later
  final_x := output.final_x

@[simp] theorem toCoordinateOutput_circle (output : Consumer.Output) :
    (toCoordinateOutput output).circle = output.circle := rfl

@[simp] theorem toCoordinateOutput_later (output : Consumer.Output) :
    (toCoordinateOutput output).later = output.later := rfl

@[simp] theorem toCoordinateOutput_finalX (output : Consumer.Output) :
    (toCoordinateOutput output).final_x = output.final_x := rfl

/-! The equality below is deliberately a source-tool boundary, not a theorem
proved by Lean's kernel.  Its arguments identify one successful call already
recorded by `ProductionFriPreparationTrace`: the domain-19 layer-zero slice,
the three exact later-layer slices read by the production caller, and the
returned output.  The reproducible coordinate source bundle pins the unchanged
Rust, its extraction patch, the directly translated private parent helper, and
the translated adapter used on the right-hand side. -/

/-- Adapter equality for one successful production preparation trace. -/
def AcceptedProductionCoordinateAdapterEquality
    {openings : V5FriConsumerExact.private_openings.VerifiedV5PrivateOpenings}
    {alphas : Array V5FriConsumerExact.aspis_core.field.QM31 4#usize}
    {inverse :
      V5FriConsumerExact.aspis_core.field.M31 →
        V5FriConsumerExact.aspis_core.field.M31}
    {coordinates : Consumer.Output}
    {alphaPowers : Array
      (Array V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier
        3#usize) 4#usize}
    (trace : ProductionFriPreparationTrace openings alphas inverse
      coordinates alphaPowers) : Prop :=
  V5FriCoordinateAdapter.aspis_core.circle_fri.derive_query_fold_inverses_for_circle
      19#u32
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref trace.later0)
      (alloc.vec.Vec.deref trace.later1)
      (alloc.vec.Vec.deref trace.later2) =
    .ok (.Ok (toCoordinateOutput coordinates))

/-- Source-certificate boundary for the preparation trace contained in one
accepted production execution.  Unlike the former statement, this does not
quantify over calls unrelated to that execution. -/
def AcceptedExecutionCoordinateSourceCertificate
    {openings : V5FriConsumerExact.private_openings.VerifiedV5PrivateOpenings}
    {prepared : V5FriConsumerExact.fri_checks.V5PreparedPcsClaims}
    {finalPolynomial : Array V5FriConsumerExact.aspis_core.field.QM31 4#usize}
    {sink : V5FriConsumerExact.fri_checks.V5FriCheckSink}
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink) : Prop :=
  ∀ trace : ProductionFriPreparationTrace openings execution.sourceAlphas
      execution.sourceInverse execution.coordinates execution.alphaPowers,
    AcceptedProductionCoordinateAdapterEquality trace

/-- An accepted production preparation call returns exactly the released
coordinate tables once the source/adapter equality is supplied. -/
theorem production_trace_released_coordinate_tables_exact
    {openings : V5FriConsumerExact.private_openings.VerifiedV5PrivateOpenings}
    {alphas : Array V5FriConsumerExact.aspis_core.field.QM31 4#usize}
    {inverse :
      V5FriConsumerExact.aspis_core.field.M31 →
        V5FriConsumerExact.aspis_core.field.M31}
    {coordinates : Consumer.Output}
    {alphaPowers : Array
      (Array V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier
        3#usize) 4#usize}
    (trace : ProductionFriPreparationTrace openings alphas inverse
      coordinates alphaPowers)
    (hValidate : ValidationSuccessPreservesShape)
    (hAdapter : AcceptedProductionCoordinateAdapterEquality trace)
    (hlayer0 : IndicesBelow
      (alloc.vec.Vec.deref openings.indices.layer0) 131072)
    (hlater0 : IndicesBelow (alloc.vec.Vec.deref trace.later0) 32768)
    (hlater1 : IndicesBelow (alloc.vec.Vec.deref trace.later1) 8192)
    (hlater2 : IndicesBelow (alloc.vec.Vec.deref trace.later2) 2048)
    (hnonempty : 0 < openings.indices.layer0.val.length)
    (hcapacity : 2 * openings.indices.layer0.val.length +
        3 * (trace.later0.val.length + trace.later1.val.length +
          trace.later2.val.length) ≤ Std.Usize.max) :
    ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref trace.later0)
      (alloc.vec.Vec.deref trace.later1)
      (alloc.vec.Vec.deref trace.later2)
      (toCoordinateOutput coordinates) := by
  have hdomain := trace.domainLog_eq_19 hValidate
  have _hproduction := trace.coordinateCall
  rw [hdomain] at _hproduction
  exact accepted_released_coordinate_tables_exact
    (alloc.vec.Vec.deref openings.indices.layer0)
    (alloc.vec.Vec.deref trace.later0)
    (alloc.vec.Vec.deref trace.later1)
    (alloc.vec.Vec.deref trace.later2)
    (toCoordinateOutput coordinates) hlayer0 hlater0 hlater1 hlater2
    hnonempty hcapacity hAdapter

/-- The exact authenticated parser run supplies all range, nonempty, and
capacity facts required by the coordinate theorem.  Callers no longer need to
state those routine bounds separately. -/
theorem production_trace_released_coordinate_tables_from_exact_run
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    {openings : V5FriConsumerExact.private_openings.VerifiedV5PrivateOpenings}
    {alphas : Array V5FriConsumerExact.aspis_core.field.QM31 4#usize}
    {inverse : V5FriConsumerExact.aspis_core.field.M31 →
      V5FriConsumerExact.aspis_core.field.M31}
    {coordinates : Consumer.Output}
    {alphaPowers : Array
      (Array V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier
        3#usize) 4#usize}
    (trace : ProductionFriPreparationTrace openings alphas inverse
      coordinates alphaPowers)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (hValidate : ValidationSuccessPreservesShape)
    (hAdapter : AcceptedProductionCoordinateAdapterEquality trace) :
    ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref trace.later0)
      (alloc.vec.Vec.deref trace.later1)
      (alloc.vec.Vec.deref trace.later2)
      (toCoordinateOutput coordinates) := by
  have hlayer0Eq : generatedIndicesToNat openings.indices.layer0 =
      orderedActiveIndices .c1 queries 0 := by
    have h := congrArg V5DriverOutput.layer0Indices hdriver
    simpa [generatedDriverOutput, driverOutputOfRun] using h
  have htraceIndices := preparation_trace_indices_match_driver trace
  have hline1Driver :
      (generatedDriverOutput openings).line1Indices =
        orderedActiveIndices .line1 queries 0 := by
    have h := congrArg V5DriverOutput.line1Indices hdriver
    simpa [driverOutputOfRun] using h
  have hline2Driver :
      (generatedDriverOutput openings).line2Indices =
        orderedActiveIndices .line2 queries 0 := by
    have h := congrArg V5DriverOutput.line2Indices hdriver
    simpa [driverOutputOfRun] using h
  have hline3Driver :
      (generatedDriverOutput openings).line3Indices =
        orderedActiveIndices .line3 queries 0 := by
    have h := congrArg V5DriverOutput.line3Indices hdriver
    simpa [driverOutputOfRun] using h
  have hline1Eq : generatedIndicesToNat trace.later0 =
      orderedActiveIndices .line1 queries 0 :=
    htraceIndices.1.trans hline1Driver
  have hline2Eq : generatedIndicesToNat trace.later1 =
      orderedActiveIndices .line2 queries 0 :=
    htraceIndices.2.1.trans hline2Driver
  have hline3Eq : generatedIndicesToNat trace.later2 =
      orderedActiveIndices .line3 queries 0 :=
    htraceIndices.2.2.trans hline3Driver
  have hlayer0 := generated_indices_below_of_eq_ordered run .c1
    openings.indices.layer0 hlayer0Eq
  have hline1 := generated_indices_below_of_eq_ordered run .line1
    trace.later0 hline1Eq
  have hline2 := generated_indices_below_of_eq_ordered run .line2
    trace.later1 hline2Eq
  have hline3 := generated_indices_below_of_eq_ordered run .line3
    trace.later2 hline3Eq
  have hlayer0Len := generated_indices_length_le_18 run .c1
    openings.indices.layer0 hlayer0Eq
  have hline1Len := generated_indices_length_le_18 run .line1
    trace.later0 hline1Eq
  have hline2Len := generated_indices_length_le_18 run .line2
    trace.later1 hline2Eq
  have hline3Len := generated_indices_length_le_18 run .line3
    trace.later2 hline3Eq
  have hnonempty := generated_layer0_indices_nonempty run
    openings.indices.layer0 hlayer0Eq
  have hmax : 198 ≤ Std.Usize.max := by
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      norm_num [Std.Usize.max, UScalar.max, UScalar.size,
        Std.Usize.size, Std.Usize.numBits, UScalarTy.Usize_numBits_eq,
        hbits]
  have hcapacity :
      2 * openings.indices.layer0.val.length +
        3 * (trace.later0.val.length + trace.later1.val.length +
          trace.later2.val.length) ≤ Std.Usize.max := by
    omega
  apply production_trace_released_coordinate_tables_exact trace hValidate
    hAdapter
  · simpa [binaryDepth] using hlayer0
  · simpa [binaryDepth] using hline1
  · simpa [binaryDepth] using hline2
  · simpa [binaryDepth] using hline3
  · exact hnonempty
  · exact hcapacity

#print axioms production_trace_released_coordinate_tables_exact
#print axioms production_trace_released_coordinate_tables_from_exact_run

end AspisV5FriConsumerCoordinateBridge
