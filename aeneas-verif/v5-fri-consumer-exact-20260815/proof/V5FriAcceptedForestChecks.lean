import V5FriConsumerCoordinateBridge
import V5FriDecoderReferenceSemantics
import AspisFormal.V5MerkleTranscriptProjection
import AspisFormal.V5AcceptedExecutionReleasedSchedule
import AspisFormal.V5AcceptedExecutionReleasedSecurity

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-!
# Accepted production FRI checks on authenticated values

This file joins the facts already proved separately about one accepted Rust
execution: the exact parser run, every read made by the four FRI loops, the
field meaning of the accepted arithmetic calls, and the released coordinate
tables.  Its target is `ForestFriChecks`, the four concrete comparisons which
the maintained soundness theorem needs.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriAcceptedForestChecks

open AspisV5AcceptedExecutionSecurityBridge
open AspisV5AcceptedExecutionReleasedSchedule
open AspisV5AcceptedExecutionReleasedSecurity
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriArithmeticSemantics
open AspisV5FriConsumerCoordinateBridge
open AspisV5FriConsumerExactProof
open AspisV5FriConsumerObservationBridge
open AspisV5FriConsumerReadSemantics
open AspisV5FriConsumerValueSemantics
open AspisV5FriCoordinateReleasedPointConnection
open AspisV5FriDecoderReferenceSemantics
open AspisV5FriFoldSemantics
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriPreparedSumSemantics
open AspisV5FriSourceLoopOrder
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge
open AspisV5MerkleTranscriptProjection
open AspisV5WithoutReplacementQuerySoundness
open V5FriConsumerExact

abbrev K := ExactQM31
abbrev Decoder := OpeningFibreDecoder K

/-- The exact four-limb field used by the released verifier has odd
characteristic, so the accepted-execution projection's `2 != 0` requirement
is proved here rather than left as a caller input. -/
private theorem exactQM31_two_ne_zero : (2 : K) ≠ 0 := by
  open AspisV5ComponentCQM31TowerExact in
    intro h
    have hmap : algebraMap M31Exact QM31Exact (2 : M31Exact) =
        algebraMap M31Exact QM31Exact (0 : M31Exact) := by
      calc
        algebraMap M31Exact QM31Exact (2 : M31Exact) =
            (2 : QM31Exact) := map_ofNat _ 2
        _ = 0 := h
        _ = algebraMap M31Exact QM31Exact (0 : M31Exact) := (map_zero _).symm
    have hbase := FaithfulSMul.algebraMap_injective M31Exact QM31Exact hmap
    exact AspisCircleGroupOrder.two_ne_zero_ZModP hbase

local instance exactQM31NeZeroTwo : NeZero (2 : K) :=
  ⟨exactQM31_two_ne_zero⟩

/-- Exact agreement required only at the literal successful Rust calls used
by one accepted FRI execution with this prepared claim object.  It identifies
no fold equation: the fold equations are consequences of the generated-call
proofs in `V5FriConsumerValueSemantics`. -/
structure AcceptedCallDecoderAgreement
    (prepared : fri_checks.V5PreparedPcsClaims)
    (decoder : Decoder) : Prop where
  layer0 : ∀ c1 c2 combined,
    fri_checks.gamma_combine_v5_layer0_exact c1 c2 prepared =
        .ok (.Ok combined) →
      ∀ slot : Fin 4,
        decoder.layer0 (c1.val.map generatedU8ToByte)
            (c2.val.map generatedU8ToByte) slot =
          qm31View (toExactQM31 combined.val[slot.val]!)
  laterReference : ∀ tree leaf slot,
    decoder.later tree (leaf.val.map generatedU8ToByte) slot =
      referenceDecoded leaf slot
  layerZeroParent : ∀ leaf selected query value,
    core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) leaf
        { start := Std.Usize.wrapping_mul
            (UScalar.cast .Usize (query &&& 3#u32)) 16#usize,
          «end» := Std.Usize.wrapping_add
            (Std.Usize.wrapping_mul
              (UScalar.cast .Usize (query &&& 3#u32)) 16#usize) 16#usize } =
      .ok selected →
    aspis_core.field.QM31.from_le_bytes selected = .ok (some value) →
    decoder.later .line1 (leaf.val.map generatedU8ToByte)
        ⟨(query &&& 3#u32).val, by
          rw [UScalar.val_and]
          exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ =
      qm31View (toExactQM31 value)

/-- The values entering the accepted Rust FRI call are the mathematical
schedule and public final polynomial.  These are direct value equalities and
canonical-representation facts; no FRI fold conclusion appears here. -/
structure AcceptedFriModelInputBinding
    (prepared : fri_checks.V5PreparedPcsClaims)
    (sourceAlphas finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (transcript : IdealTranscript K) : Prop where
  alphaCanonical : ∀ layer : Fin 4,
    canonicalQM31 (toExactQM31 sourceAlphas.val[layer.val]!)
  alphaValue : ∀ layer : Fin 4,
    qm31View (toExactQM31 sourceAlphas.val[layer.val]!) =
      schedule.alpha layer
  combinedCanonical : ∀ c1 c2 combined,
    fri_checks.gamma_combine_v5_layer0_exact c1 c2 prepared =
        .ok (.Ok combined) →
      CanonicalQM31Array4 (mapArray toExactQM31 combined)
  finalCanonical : CanonicalQM31Array4
    (mapArray toExactQM31 finalPolynomial)
  finalValue : ∀ slot : Fin 4,
    qm31View (toExactQM31 finalPolynomial.val[slot.val]!) =
      transcript.publishedFinal slot

private theorem array_index_usize_zero
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 0#usize = .ok output)
    (hzero : 0 < N.val) : output = values.val[0]! := by
  unfold Array.index_usize at h
  simp [hzero] at h
  have hlength : values.val.length = N.val := Array.length_eq values
  have hbound : 0 < values.val.length := by simpa [hlength] using hzero
  have hbang : values.val[0]! = values.val[0]'hbound := by
    apply List.getElem!_of_getElem?
    simp [hbound]
  rw [hbang]
  exact h.symm

private theorem array_index_usize_one
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 1#usize = .ok output)
    (hone : 1 < N.val) : output = values.val[1]! := by
  unfold Array.index_usize at h
  simp [hone] at h
  have hlength : values.val.length = N.val := Array.length_eq values
  have hbound : 1 < values.val.length := by simpa [hlength] using hone
  have hbang : values.val[1]! = values.val[1]'hbound := by
    apply List.getElem!_of_getElem?
    simp [hbound]
  rw [hbang]
  exact h.symm

private theorem array_index_usize_two
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 2#usize = .ok output)
    (htwo : 2 < N.val) : output = values.val[2]! := by
  unfold Array.index_usize at h
  simp [htwo] at h
  have hlength : values.val.length = N.val := Array.length_eq values
  have hbound : 2 < values.val.length := by simpa [hlength] using htwo
  have hbang : values.val[2]! = values.val[2]'hbound := by
    apply List.getElem!_of_getElem?
    simp [hbound]
  rw [hbang]
  exact h.symm

private theorem array_index_usize_three
    {T : Type} [Inhabited T] {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 3#usize = .ok output)
    (hthree : 3 < N.val) : output = values.val[3]! := by
  unfold Array.index_usize at h
  simp [hthree] at h
  have hlength : values.val.length = N.val := Array.length_eq values
  have hbound : 3 < values.val.length := by simpa [hlength] using hthree
  have hbang : values.val[3]! = values.val[3]'hbound := by
    apply List.getElem!_of_getElem?
    simp [hbound]
  rw [hbang]
  exact h.symm

/-- Zero-index projection without an `Inhabited` requirement on the element
type.  This is used for the generated opening records themselves. -/
private theorem array_index_usize_zero_get
    {T : Type} {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 0#usize = .ok output)
    (hzero : 0 < N.val) (hbound : 0 < values.val.length) :
    output = values.val.get ⟨0, hbound⟩ := by
  unfold Array.index_usize at h
  simp [hzero] at h
  exact h.symm

private theorem array_index_usize_one_get
    {T : Type} {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 1#usize = .ok output)
    (hone : 1 < N.val) (hbound : 1 < values.val.length) :
    output = values.val.get ⟨1, hbound⟩ := by
  unfold Array.index_usize at h
  simp [hone] at h
  exact h.symm

private theorem array_index_usize_two_get
    {T : Type} {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 2#usize = .ok output)
    (htwo : 2 < N.val) (hbound : 2 < values.val.length) :
    output = values.val.get ⟨2, hbound⟩ := by
  unfold Array.index_usize at h
  simp [htwo] at h
  exact h.symm

private theorem array_index_usize_three_get
    {T : Type} {N : Std.Usize}
    (values : Array T N) (output : T)
    (h : Array.index_usize values 3#usize = .ok output)
    (hthree : 3 < N.val) (hbound : 3 < values.val.length) :
    output = values.val.get ⟨3, hbound⟩ := by
  unfold Array.index_usize at h
  simp [hthree] at h
  exact h.symm

/-- Field projection of the exact five-section driver equality. -/
theorem generated_driver_opening_eq_trace
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
  (tree : V5PrivateSection) :
    (generatedDriverOutput openings).opening tree =
      openingOfTrace (run.sections tree) := by
  rw [hdriver]
  exact driverOutputOfRun_opening run [] tree

/-- Index-list projection of the exact five-section driver equality. -/
theorem generated_driver_indices_eq_ordered
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
  (tree : V5PrivateSection) :
    (generatedDriverOutput openings).indices tree =
      orderedActiveIndices tree queries 0 := by
  rw [hdriver]
  exact driverOutputOfRun_indices run [] tree

/-- The generated layer-zero index at the model section ordinal is the exact
query value used by the mathematical schedule. -/
theorem layerZero_source_index_at_query
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32}
    {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (query : V5Query) (hquery : query ∈ queries) :
    ∃ (target : Std.Usize)
        (htarget : target.val < openings.indices.layer0.val.length),
      target.val = sectionOrdinal .c1 queries query.val ∧
        (sliceValueAt (alloc.vec.Vec.deref openings.indices.layer0)
          target htarget).val = query.val := by
  have heq : generatedIndicesToNat openings.indices.layer0 =
      orderedActiveIndices .c1 queries 0 := by
    have h := congrArg V5DriverOutput.layer0Indices hdriver
    simpa [generatedDriverOutput, driverOutputOfRun] using h
  have hactive : query.val ∈ activeIndices .c1 queries 0 := by
    simpa [sectionIndex] using sectionIndex_mem_active .c1 hquery
  obtain ⟨hordinal, hvalue⟩ := generated_index_at_sectionOrdinal
    openings.indices.layer0 hactive heq
  have hsize : sectionOrdinal .c1 queries query.val <
      2 ^ UScalarTy.Usize.numBits := by
    have hmax := openings.indices.layer0.property
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      norm_num [Std.Usize.max, UScalar.max, UScalar.size,
        Std.Usize.size, Std.Usize.numBits, UScalarTy.Usize_numBits_eq,
        hbits] at hmax ⊢ <;> omega
  let target := Std.Usize.ofNatCore
    (sectionOrdinal .c1 queries query.val) hsize
  have htargetVal : target.val = sectionOrdinal .c1 queries query.val := by
    simp [target]
  have htarget : target.val < openings.indices.layer0.val.length := by
    simpa [htargetVal] using hordinal
  refine ⟨target, htarget, htargetVal, ?_⟩
  have hbang :
      openings.indices.layer0.val[sectionOrdinal .c1 queries query.val]! =
        openings.indices.layer0.val[sectionOrdinal .c1 queries query.val]'hordinal := by
    apply List.getElem!_of_getElem?
    simp [hordinal]
  simpa [sliceValueAt, alloc.vec.Vec.deref, target, hbang] using hvalue

#print axioms layerZero_source_index_at_query

/-- Equality with a duplicate-free model index list makes the generated U32
index vector duplicate-free as well. -/
theorem generated_indices_nodup_of_eq_ordered
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (indices : alloc.vec.Vec Std.U32)
    (heq : generatedIndicesToNat indices =
      orderedActiveIndices tree queries 0) :
    indices.val.Nodup := by
  have hnat : (generatedIndicesToNat indices).Nodup := by
    rw [heq]
    exact orderedActiveIndices_nodup tree queries 0
  apply List.Nodup.of_map (fun index : Std.U32 => index.val)
  simpa [generatedIndicesToNat] using hnat

private theorem u32_wrapping_shr_two_val (value : Std.U32) :
    (Std.U32.wrapping_shr value 2#u32).val = value.val / 4 := by
  change (value.bv.ushiftRight (2 % 32)).toNat = value.bv.toNat / 4
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem u32_and_three_val (value : Std.U32) :
    (value &&& 3#u32).val = value.val % 4 := by
  rw [UScalar.val_and]
  change value.val &&& 3 = value.val % 4
  rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem usize_and_three_val (value : Std.Usize) :
    (value &&& 3#usize).val = value.val % 4 := by
  rw [UScalar.val_and]
  change value.val &&& 3 = value.val % 4
  rw [show (3 : Nat) = 2 ^ 2 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem section_ordinal_fits_usize
    (indices : alloc.vec.Vec Std.U32) {ordinal : Nat}
    (hordinal : ordinal < indices.val.length) :
    ordinal < 2 ^ UScalarTy.Usize.numBits := by
  have hmax := indices.property
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [Std.Usize.max, UScalar.max, UScalar.size,
      Std.Usize.size, Std.Usize.numBits, UScalarTy.Usize_numBits_eq,
      hbits] at hmax ⊢ <;> omega

private theorem sliceValueAt_eq_bang
    (indices : alloc.vec.Vec Std.U32) (target : Std.Usize)
    (htarget : target.val < indices.val.length) :
    sliceValueAt (alloc.vec.Vec.deref indices) target htarget =
      indices.val[target.val]! := by
  have hbang : indices.val[target.val]! =
      indices.val[target.val]'htarget := by
    apply List.getElem!_of_getElem?
    simp [htarget]
  rw [hbang]
  rfl

/-- A successful mutable parent lookup is the exact authenticated model value
at the requested index, independently of its starting scan ordinal. -/
theorem successful_parent_read_matches_exact_run
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries) (tree : V5PrivateSection)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (indices : alloc.vec.Vec Std.U32)
    (hopening : generatedOpeningToReturned opening =
      openingOfTrace (run.sections tree))
    (hindices : generatedIndicesToNat indices =
      orderedActiveIndices tree queries 0)
    (carried resultOrdinal : Std.Usize) (rustIndex : Std.U32)
    (layer : Std.U8) (value : Slice Std.U8) (modelIndex : Nat)
    (hactive : modelIndex ∈ activeIndices tree queries 0)
    (hrustIndex : rustIndex.val = modelIndex)
    (hcall : fri_checks.opening_value_for_monotone_index opening
      (alloc.vec.Vec.deref indices) carried rustIndex layer =
        .ok (.Ok value, resultOrdinal)) :
    resultOrdinal.val = sectionOrdinal tree queries modelIndex ∧
      value.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections tree) modelIndex := by
  have hindicesLength := congrArg List.length hindices
  have htargetBoundNat : sectionOrdinal tree queries modelIndex <
      indices.val.length := by
    have hmodel := sectionOrdinal_lt_count tree hactive
    simpa [generatedIndicesToNat] using hmodel.trans_eq hindicesLength.symm
  have htargetIndexVal :
      indices.val[sectionOrdinal tree queries modelIndex]!.val = modelIndex := by
    have hmap := congrArg
      (fun values : List Nat =>
        values[sectionOrdinal tree queries modelIndex]!) hindices
    have hget := sectionOrdinal_getElem?_eq tree hactive
    have hmodelBang :
        (orderedActiveIndices tree queries 0)[sectionOrdinal tree queries
            modelIndex]! = modelIndex := by
      rw [List.getElem!_of_getElem?]
      simpa using hget
    rw [hmodelBang] at hmap
    simpa [generatedIndicesToNat, htargetBoundNat] using hmap
  have hfits := section_ordinal_fits_usize indices htargetBoundNat
  let target := Std.Usize.ofNatCore
    (sectionOrdinal tree queries modelIndex) hfits
  have htargetVal : target.val = sectionOrdinal tree queries modelIndex := by
    simp [target]
  have htargetBound : target.val < indices.val.length := by
    simpa [htargetVal] using htargetBoundNat
  have htargetIndex : indices.val[target.val]! = rustIndex := by
    apply UScalar.eq_of_val_eq
    rw [htargetVal, htargetIndexVal, hrustIndex]
  have hlookup := successful_production_monotone_call_hits_unique_target
    opening (alloc.vec.Vec.deref indices) carried target resultOrdinal
    rustIndex layer value (generated_indices_nodup_of_eq_ordered tree queries
      indices hindices) htargetBound htargetIndex hcall
  have hbytes := generated_value_at_sectionOrdinal_matches_trace opening
    (run.sections tree) hopening target htargetVal hactive value hlookup.2
  exact ⟨by rw [hlookup.1, htargetVal], hbytes⟩

/-- The three byte slices consumed by one successful first-pass iteration are
exactly the C1, C2, and line-one values authenticated by the exact parser run.
The mutable parent scan is identified by uniqueness of the sorted index list,
so this theorem does not assume where that scan started. -/
theorem layerZero_read_matches_exact_run
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    {claims powers : alloc.vec.Vec aspis_core.field.QM31}
    {weights : Array (Array Std.U32 4#usize) 16#usize}
    {multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize}
    {coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {iterNext iterOut : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter Std.U32)}
    {ordinal carried : Std.Usize} {rustQuery : Std.U32}
    (read : LayerZeroBodyReadEvidence openings openings.c1.count
      openings.c1.value_width openings.c1.offsets openings.c2.count
      openings.c2.value_width openings.c2.offsets openings.later
      openings.indices.later claims powers weights multipliers coordinates
      alphaPowers iterNext iterOut ordinal carried rustQuery)
    (query : V5Query) (hquery : query ∈ queries)
    (hordinal : ordinal.val = sectionOrdinal .c1 queries query.val)
    (hrustQuery : rustQuery.val = query.val) :
    read.c1Value.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .c1) query.val ∧
      read.c2Value.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .c2) query.val ∧
      read.parentValue.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .line1) (query.val / 4) := by
  have hc1Active : query.val ∈ activeIndices .c1 queries 0 := by
    simpa [sectionIndex] using sectionIndex_mem_active .c1 hquery
  have hc2Active : query.val ∈ activeIndices .c2 queries 0 := by
    simpa [sectionIndex] using sectionIndex_mem_active .c2 hquery
  have hparentActive : query.val / 4 ∈ activeIndices .line1 queries 0 :=
    layer0_parent_mem_line1 hc1Active
  have hc1Opening : generatedOpeningToReturned openings.c1 =
      openingOfTrace (run.sections .c1) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .c1
    simpa [generatedDriverOutput, V5DriverOutput.opening] using h
  have hc2Opening : generatedOpeningToReturned openings.c2 =
      openingOfTrace (run.sections .c2) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .c2
    simpa [generatedDriverOutput, V5DriverOutput.opening] using h
  have hc1Read : openings.c1.value ordinal = .ok (some read.c1Value) := by
    simpa [checkedC1] using read.c1Read
  have hc2Read : openings.c2.value ordinal = .ok (some read.c2Value) := by
    simpa [checkedC2] using read.c2Read
  have hc2Ordinal : ordinal.val = sectionOrdinal .c2 queries query.val := by
    calc
      ordinal.val = sectionOrdinal .c1 queries query.val := hordinal
      _ = sectionOrdinal .c2 queries query.val :=
        sectionOrdinal_c1_eq_c2 queries query.val
  have hc1Bytes := generated_value_at_sectionOrdinal_matches_trace
    openings.c1 (run.sections .c1) hc1Opening ordinal hordinal hc1Active
    read.c1Value hc1Read
  have hc2Bytes := generated_value_at_sectionOrdinal_matches_trace
    openings.c2 (run.sections .c2) hc2Opening ordinal hc2Ordinal hc2Active
    read.c2Value hc2Read

  have hlaterBound : 0 < openings.later.val.length := by
    have hlength : openings.later.val.length = 3 := by
      simpa using Array.length_eq openings.later
    omega
  have hlaterIndicesBound : 0 < openings.indices.later.val.length := by
    have hlength : openings.indices.later.val.length = 3 := by
      simpa using Array.length_eq openings.indices.later
    omega
  have hparentOpeningAt := array_index_usize_zero_get openings.later
    read.parentOpening read.parentOpeningAt (by norm_num) hlaterBound
  have hparentIndicesAt := array_index_usize_zero_get openings.indices.later
    read.parentIndices read.parentIndicesAt (by norm_num) hlaterIndicesBound
  have hline1Opening : generatedOpeningToReturned read.parentOpening =
      openingOfTrace (run.sections .line1) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .line1
    simpa [generatedDriverOutput, V5DriverOutput.opening,
      hparentOpeningAt] using h
  have hline1Indices : generatedIndicesToNat read.parentIndices =
      orderedActiveIndices .line1 queries 0 := by
    have h := generated_driver_indices_eq_ordered run openings hdriver .line1
    simpa [generatedDriverOutput, V5DriverOutput.indices,
      hparentIndicesAt] using h
  have hline1Length := congrArg List.length hline1Indices
  have hparentOrdinal : sectionOrdinal .line1 queries (query.val / 4) <
      read.parentIndices.val.length := by
    have hmodel := sectionOrdinal_lt_count .line1 hparentActive
    simpa [generatedIndicesToNat] using hmodel.trans_eq hline1Length.symm
  have hparentIndex :
      read.parentIndices.val[sectionOrdinal .line1 queries (query.val / 4)]!.val =
        query.val / 4 := by
    have hmap := congrArg
      (fun values : List Nat =>
        values[sectionOrdinal .line1 queries (query.val / 4)]!)
      hline1Indices
    have hget := sectionOrdinal_getElem?_eq .line1 hparentActive
    have hmodelBang :
        (orderedActiveIndices .line1 queries 0)[sectionOrdinal .line1 queries
            (query.val / 4)]! =
          query.val / 4 := by
      rw [List.getElem!_of_getElem?]
      simpa using hget
    rw [hmodelBang] at hmap
    simpa [generatedIndicesToNat, hparentOrdinal] using hmap
  have hfits := section_ordinal_fits_usize read.parentIndices hparentOrdinal
  let target := Std.Usize.ofNatCore
    (sectionOrdinal .line1 queries (query.val / 4)) hfits
  have htargetVal : target.val =
      sectionOrdinal .line1 queries (query.val / 4) := by simp [target]
  have htargetBound : target.val < read.parentIndices.val.length := by
    simpa [htargetVal] using hparentOrdinal
  have hshiftVal : (Std.U32.wrapping_shr rustQuery 2#u32).val =
      query.val / 4 := by
    rw [u32_wrapping_shr_two_val, hrustQuery]
  have htargetIndex : read.parentIndices.val[target.val]! =
      Std.U32.wrapping_shr rustQuery 2#u32 := by
    apply UScalar.eq_of_val_eq
    rw [htargetVal, hparentIndex, hshiftVal]
  have hparentCall := successful_production_monotone_call_hits_unique_target
    read.parentOpening (alloc.vec.Vec.deref read.parentIndices) carried target
    read.parentOrdinal (Std.U32.wrapping_shr rustQuery 2#u32) 1#u8
    read.parentValue (generated_indices_nodup_of_eq_ordered .line1 queries
      read.parentIndices hline1Indices) htargetBound htargetIndex
    read.parentRead
  have hparentBytes := generated_value_at_sectionOrdinal_matches_trace
    read.parentOpening (run.sections .line1) hline1Opening target htargetVal
    hparentActive read.parentValue hparentCall.2
  exact ⟨hc1Bytes, hc2Bytes, hparentBytes⟩

/-- The line-one input and line-two parent consumed by the first later FRI
pass are exactly the two authenticated values at `index` and `index / 4`. -/
theorem laterZero_read_matches_exact_run
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    {coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {ordinal carried : Std.Usize} {rustIndex : Std.U32}
    (read : LaterBodyReadEvidence openings.later openings.indices.later
      coordinates alphaPowers 0#usize ordinal carried rustIndex)
    (index : Nat) (hactive : index ∈ activeIndices .line1 queries 0)
    (hordinal : ordinal.val = sectionOrdinal .line1 queries index)
    (hrustIndex : rustIndex.val = index) :
    read.incomingValue.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .line1) index ∧
      read.parentValue.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .line2) (index / 4) := by
  have hlaterLength : openings.later.val.length = 3 := by
    simpa using Array.length_eq openings.later
  have hlaterIndicesLength : openings.indices.later.val.length = 3 := by
    simpa using Array.length_eq openings.indices.later
  have hzero : 0 < openings.later.val.length := by omega
  have hone : 1 < openings.later.val.length := by omega
  have honeIndices : 1 < openings.indices.later.val.length := by omega
  have hincomingAt := array_index_usize_zero_get openings.later
    read.incomingOpening read.incomingOpeningAt (by norm_num) hzero
  have hincomingOpening : generatedOpeningToReturned read.incomingOpening =
      openingOfTrace (run.sections .line1) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .line1
    simpa [generatedDriverOutput, V5DriverOutput.opening, hincomingAt] using h
  have hincomingBytes := generated_value_at_sectionOrdinal_matches_trace
    read.incomingOpening (run.sections .line1) hincomingOpening ordinal hordinal
    hactive read.incomingValue read.incomingRead
  have hzeroAddOne : Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [Std.Usize.wrapping_add_val_eq]
    have hzeroVal : (0#usize : Std.Usize).val = 0 := by
      apply UScalar.ofNatCore_val_eq
    have honeVal : (1#usize : Std.Usize).val = 1 := by
      apply UScalar.ofNatCore_val_eq
    rw [hzeroVal, honeVal, Nat.zero_add]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with hbits | hbits <;>
      norm_num [UScalar.size, Std.Usize.size,
        Std.Usize.numBits, UScalarTy.Usize_numBits_eq, hbits]
  have hparentOpeningCall :
      Array.index_usize openings.later 1#usize = .ok read.parentOpening := by
    simpa only [hzeroAddOne] using read.parentOpeningAt
  have hparentIndicesCall :
      Array.index_usize openings.indices.later 1#usize =
        .ok read.parentIndices := by
    simpa only [hzeroAddOne] using read.parentIndicesAt
  have hparentOpeningAt := array_index_usize_one_get openings.later
    read.parentOpening hparentOpeningCall (by norm_num) hone
  have hparentIndicesAt := array_index_usize_one_get openings.indices.later
    read.parentIndices hparentIndicesCall (by norm_num) honeIndices
  have hparentOpening : generatedOpeningToReturned read.parentOpening =
      openingOfTrace (run.sections .line2) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .line2
    simpa [generatedDriverOutput, V5DriverOutput.opening, hparentOpeningAt]
      using h
  have hparentIndices : generatedIndicesToNat read.parentIndices =
      orderedActiveIndices .line2 queries 0 := by
    have h := generated_driver_indices_eq_ordered run openings hdriver .line2
    simpa [generatedDriverOutput, V5DriverOutput.indices, hparentIndicesAt]
      using h
  have hparentActive : index / 4 ∈ activeIndices .line2 queries 0 :=
    line1_parent_mem_line2 hactive
  have hshiftVal : (Std.U32.wrapping_shr rustIndex 2#u32).val = index / 4 := by
    rw [u32_wrapping_shr_two_val, hrustIndex]
  have hparentBytes := successful_parent_read_matches_exact_run run .line2
    read.parentOpening read.parentIndices hparentOpening hparentIndices carried
    read.parentOrdinal (Std.U32.wrapping_shr rustIndex 2#u32)
    (Std.U8.wrapping_add (UScalar.cast .U8 0#usize) 2#u8)
    read.parentValue (index / 4) hparentActive hshiftVal read.parentRead
  exact ⟨hincomingBytes, hparentBytes.2⟩

private theorem usize_wrapping_one_add_one :
    Std.Usize.wrapping_add 1#usize 1#usize = 2#usize := by
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_add_val_eq]
  have honeVal : (1#usize : Std.Usize).val = 1 := by
    apply UScalar.ofNatCore_val_eq
  have htwoVal : (2#usize : Std.Usize).val = 2 := by
    apply UScalar.ofNatCore_val_eq
  rw [honeVal, htwoVal]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits,
      UScalarTy.Usize_numBits_eq, hbits]

private theorem usize_wrapping_zero_add_one :
    Std.Usize.wrapping_add 0#usize 1#usize = 1#usize := by
  apply UScalar.eq_of_val_eq
  rw [Std.Usize.wrapping_add_val_eq]
  have hzeroVal : (0#usize : Std.Usize).val = 0 := by
    apply UScalar.ofNatCore_val_eq
  have honeVal : (1#usize : Std.Usize).val = 1 := by
    apply UScalar.ofNatCore_val_eq
  rw [hzeroVal, honeVal]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    norm_num [UScalar.size, Std.Usize.size, Std.Usize.numBits,
      UScalarTy.Usize_numBits_eq, hbits]

/-- The line-two input and line-three parent consumed by the second later FRI
pass are exactly the two authenticated values at `index` and `index / 4`. -/
theorem laterOne_read_matches_exact_run
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    {coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {ordinal carried : Std.Usize} {rustIndex : Std.U32}
    (read : LaterBodyReadEvidence openings.later openings.indices.later
      coordinates alphaPowers 1#usize ordinal carried rustIndex)
    (index : Nat) (hactive : index ∈ activeIndices .line2 queries 0)
    (hordinal : ordinal.val = sectionOrdinal .line2 queries index)
    (hrustIndex : rustIndex.val = index) :
    read.incomingValue.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .line2) index ∧
      read.parentValue.val.map generatedU8ToByte =
        sectionValueAtIndex (run.sections .line3) (index / 4) := by
  have hlaterLength : openings.later.val.length = 3 := by
    simpa using Array.length_eq openings.later
  have hlaterIndicesLength : openings.indices.later.val.length = 3 := by
    simpa using Array.length_eq openings.indices.later
  have hone : 1 < openings.later.val.length := by omega
  have htwo : 2 < openings.later.val.length := by omega
  have htwoIndices : 2 < openings.indices.later.val.length := by omega
  have hincomingAt := array_index_usize_one_get openings.later
    read.incomingOpening read.incomingOpeningAt (by norm_num) hone
  have hincomingOpening : generatedOpeningToReturned read.incomingOpening =
      openingOfTrace (run.sections .line2) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .line2
    simpa [generatedDriverOutput, V5DriverOutput.opening, hincomingAt] using h
  have hincomingBytes := generated_value_at_sectionOrdinal_matches_trace
    read.incomingOpening (run.sections .line2) hincomingOpening ordinal hordinal
    hactive read.incomingValue read.incomingRead
  have hparentOpeningCall :
      Array.index_usize openings.later 2#usize = .ok read.parentOpening := by
    simpa only [usize_wrapping_one_add_one] using read.parentOpeningAt
  have hparentIndicesCall :
      Array.index_usize openings.indices.later 2#usize =
        .ok read.parentIndices := by
    simpa only [usize_wrapping_one_add_one] using read.parentIndicesAt
  have hparentOpeningAt := array_index_usize_two_get openings.later
    read.parentOpening hparentOpeningCall (by norm_num) htwo
  have hparentIndicesAt := array_index_usize_two_get openings.indices.later
    read.parentIndices hparentIndicesCall (by norm_num) htwoIndices
  have hparentOpening : generatedOpeningToReturned read.parentOpening =
      openingOfTrace (run.sections .line3) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .line3
    simpa [generatedDriverOutput, V5DriverOutput.opening, hparentOpeningAt]
      using h
  have hparentIndices : generatedIndicesToNat read.parentIndices =
      orderedActiveIndices .line3 queries 0 := by
    have h := generated_driver_indices_eq_ordered run openings hdriver .line3
    simpa [generatedDriverOutput, V5DriverOutput.indices, hparentIndicesAt]
      using h
  have hparentActive : index / 4 ∈ activeIndices .line3 queries 0 :=
    line2_parent_mem_line3 hactive
  have hshiftVal : (Std.U32.wrapping_shr rustIndex 2#u32).val = index / 4 := by
    rw [u32_wrapping_shr_two_val, hrustIndex]
  have hparentBytes := successful_parent_read_matches_exact_run run .line3
    read.parentOpening read.parentIndices hparentOpening hparentIndices carried
    read.parentOrdinal (Std.U32.wrapping_shr rustIndex 2#u32)
    (Std.U8.wrapping_add (UScalar.cast .U8 1#usize) 2#u8)
    read.parentValue (index / 4) hparentActive hshiftVal read.parentRead
  exact ⟨hincomingBytes, hparentBytes.2⟩

/-- The terminal pass consumes exactly the authenticated line-three value at
the requested index. -/
theorem terminal_read_matches_exact_run
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    {finalPolynomial : Array aspis_core.field.QM31 4#usize}
    {coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {ordinal : Std.Usize} {rustIndex : Std.U32}
    (read : TerminalBodyReadEvidence openings.later finalPolynomial coordinates
      alphaPowers 2#usize ordinal rustIndex)
    (index : Nat) (hactive : index ∈ activeIndices .line3 queries 0)
    (hordinal : ordinal.val = sectionOrdinal .line3 queries index) :
    read.incomingValue.val.map generatedU8ToByte =
      sectionValueAtIndex (run.sections .line3) index := by
  have hlaterLength : openings.later.val.length = 3 := by
    simpa using Array.length_eq openings.later
  have htwo : 2 < openings.later.val.length := by omega
  have hincomingAt := array_index_usize_two_get openings.later
    read.incomingOpening read.incomingOpeningAt (by norm_num) htwo
  have hincomingOpening : generatedOpeningToReturned read.incomingOpening =
      openingOfTrace (run.sections .line3) := by
    have h := generated_driver_opening_eq_trace run openings hdriver .line3
    simpa [generatedDriverOutput, V5DriverOutput.opening, hincomingAt] using h
  exact generated_value_at_sectionOrdinal_matches_trace read.incomingOpening
    (run.sections .line3) hincomingOpening ordinal hordinal hactive
    read.incomingValue read.incomingRead

/-- Usize form of the exact source position for any one of the four generated
query-index vectors. -/
theorem source_index_at_active
    (tree : V5PrivateSection) (queries : Finset V5Query)
    (indices : alloc.vec.Vec Std.U32)
    (heq : generatedIndicesToNat indices =
      orderedActiveIndices tree queries 0)
    (index : Nat) (hactive : index ∈ activeIndices tree queries 0) :
    ∃ (target : Std.Usize) (htarget : target.val < indices.val.length),
      target.val = sectionOrdinal tree queries index ∧
        (sliceValueAt (alloc.vec.Vec.deref indices) target htarget).val =
          index := by
  obtain ⟨hordinal, hvalue⟩ := generated_index_at_sectionOrdinal indices
    hactive heq
  have hfits := section_ordinal_fits_usize indices hordinal
  let target := Std.Usize.ofNatCore (sectionOrdinal tree queries index) hfits
  have htargetVal : target.val = sectionOrdinal tree queries index := by
    simp [target]
  have htarget : target.val < indices.val.length := by
    simpa [htargetVal] using hordinal
  refine ⟨target, htarget, htargetVal, ?_⟩
  have hbang : indices.val[sectionOrdinal tree queries index]! =
      indices.val[sectionOrdinal tree queries index]'hordinal := by
    apply List.getElem!_of_getElem?
    simp [hordinal]
  simpa [sliceValueAt, alloc.vec.Vec.deref, target, hbang] using hvalue

theorem later_run_zero_indices_eq_ordered
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (indices : alloc.vec.Vec Std.U32)
    (hcall : Array.index_usize openings.indices.later 0#usize = .ok indices) :
    generatedIndicesToNat indices = orderedActiveIndices .line1 queries 0 := by
  have hlength : openings.indices.later.val.length = 3 := by
    simpa using Array.length_eq openings.indices.later
  have hbound : 0 < openings.indices.later.val.length := by omega
  have hat := array_index_usize_zero_get openings.indices.later indices hcall
    (by norm_num) hbound
  have h := generated_driver_indices_eq_ordered run openings hdriver .line1
  simpa [generatedDriverOutput, V5DriverOutput.indices, hat] using h

theorem later_run_one_indices_eq_ordered
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (indices : alloc.vec.Vec Std.U32)
    (hcall : Array.index_usize openings.indices.later 1#usize = .ok indices) :
    generatedIndicesToNat indices = orderedActiveIndices .line2 queries 0 := by
  have hlength : openings.indices.later.val.length = 3 := by
    simpa using Array.length_eq openings.indices.later
  have hbound : 1 < openings.indices.later.val.length := by omega
  have hat := array_index_usize_one_get openings.indices.later indices hcall
    (by norm_num) hbound
  have h := generated_driver_indices_eq_ordered run openings hdriver .line2
  simpa [generatedDriverOutput, V5DriverOutput.indices, hat] using h

theorem later_run_two_indices_eq_ordered
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (indices : alloc.vec.Vec Std.U32)
    (hcall : Array.index_usize openings.indices.later 2#usize = .ok indices) :
    generatedIndicesToNat indices = orderedActiveIndices .line3 queries 0 := by
  have hlength : openings.indices.later.val.length = 3 := by
    simpa using Array.length_eq openings.indices.later
  have hbound : 2 < openings.indices.later.val.length := by omega
  have hat := array_index_usize_two_get openings.indices.later indices hcall
    (by norm_num) hbound
  have h := generated_driver_indices_eq_ordered run openings hdriver .line3
  simpa [generatedDriverOutput, V5DriverOutput.indices, hat] using h

private theorem core_slice_get_some_eq
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (output : T)
    (hread : core.slice.Slice.get
      (core.slice.index.SliceIndexUsizeSlice T) values index =
        .ok (some output)) :
    index.val < values.val.length ∧ values.val[index.val]! = output := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexUsizeSlice
    core.slice.index.Usize.get at hread
  change ok values.val[index.val]? = ok (some output) at hread
  have hget : values.val[index.val]? = some output := Result.ok.inj hread
  have hbound : index.val < values.val.length := by
    by_contra hnot
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hnot)] at hget
    cases hget
  constructor
  · exact hbound
  · rw [List.getElem!_of_getElem?]
    simpa using hget

/-- The two inverse coordinates read by one first-pass iteration are the exact
released schedule entries for that query, and are canonical raw M31 values. -/
theorem layerZero_read_has_released_coordinates
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (layer0 line1 line2 line3 : Slice Std.U32)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (hevidence : ReleasedCoordinateOutputEvidence layer0 line1 line2 line3
      (toCoordinateOutput coordinates))
    {openings : private_openings.VerifiedV5PrivateOpenings}
    {claims powers : alloc.vec.Vec aspis_core.field.QM31}
    {weights : Array (Array Std.U32 4#usize) 16#usize}
    {multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {iterNext iterOut : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter Std.U32)}
    {ordinal carried : Std.Usize} {rustQuery : Std.U32}
    (read : LayerZeroBodyReadEvidence openings openings.c1.count
      openings.c1.value_width openings.c1.offsets openings.c2.count
      openings.c2.value_width openings.c2.offsets openings.later
      openings.indices.later claims powers weights multipliers coordinates
      alphaPowers iterNext iterOut ordinal carried rustQuery)
    (query : V5Query) (htarget : ordinal.val < layer0.val.length)
    (hindex : layer0.val[ordinal.val]!.val = query.val) :
    canonicalM31 read.inv2x ∧ canonicalM31 read.inv2y ∧
      m31View read.inv2x =
        algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2x query) ∧
      m31View read.inv2y =
        algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2y query) := by
  have hpairRead := core_slice_get_some_eq
    (alloc.vec.Vec.deref coordinates.circle) ordinal read.circlePair
    read.circleRead
  have hxRead := array_index_usize_zero read.circlePair read.inv2x
    read.inv2xRead (by norm_num)
  have hyRead := array_index_usize_one read.circlePair read.inv2y
    read.inv2yRead (by norm_num)
  have hpairEq : read.circlePair =
      coordinates.circle.val[ordinal.val]! := by
    simpa [alloc.vec.Vec.deref] using hpairRead.2.symm
  have hxEq : read.inv2x = coordinates.circle.val[ordinal.val]!.val[0]! := by
    rw [hxRead, hpairEq]
  have hyEq : read.inv2y = coordinates.circle.val[ordinal.val]!.val[1]! := by
    rw [hyRead, hpairEq]
  have hrawBound : layer0.val[ordinal.val]!.val < 131072 := by
    rw [hindex]
    exact query.isLt
  have hfin : Fin.ofNat 131072 layer0.val[ordinal.val]!.val = query := by
    apply Fin.ext
    change layer0.val[ordinal.val]!.val % 131072 = query.val
    rw [Nat.mod_eq_of_lt hrawBound, hindex]
  have hcanonical := hevidence.circleCanonical ordinal.val htarget
  have hxCanonical : canonicalM31 read.inv2x := by
    rw [hxEq]
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      coordinates.circle.val[ordinal.val]!.val[0]!
    exact hcanonical.1
  have hyCanonical : canonicalM31 read.inv2y := by
    rw [hyEq]
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      coordinates.circle.val[ordinal.val]!.val[1]!
    exact hcanonical.2
  have hvalues := hevidence.circle ordinal.val htarget
  have hxValue : AspisV5FriCoordinateFieldSemantics.m31Value read.inv2x =
      schedule.circleInv2x query := by
    rw [hxEq]
    have hreleased := hvalues.1
    change AspisV5FriCoordinateFieldSemantics.m31Value
      coordinates.circle.val[ordinal.val]!.val[0]! = _ at hreleased
    rw [hfin] at hreleased
    exact hreleased.trans (hsource.circleInv2x query).symm
  have hyValue : AspisV5FriCoordinateFieldSemantics.m31Value read.inv2y =
      schedule.circleInv2y query := by
    rw [hyEq]
    have hreleased := hvalues.2
    change AspisV5FriCoordinateFieldSemantics.m31Value
      coordinates.circle.val[ordinal.val]!.val[1]! = _ at hreleased
    rw [hfin] at hreleased
    exact hreleased.trans (hsource.circleInv2y query).symm
  refine ⟨hxCanonical, hyCanonical, ?_, ?_⟩
  · change algebraMap (ZMod AspisCircleGroupOrder.P) K
        (AspisV5FriCoordinateFieldSemantics.m31Value read.inv2x) = _
    rw [hxValue]
  · change algebraMap (ZMod AspisCircleGroupOrder.P) K
        (AspisV5FriCoordinateFieldSemantics.m31Value read.inv2y) = _
    rw [hyValue]

/-- A successful first later-pass read uses the three released line-one
inverse coordinates at the exact authenticated parent index. -/
theorem laterZero_read_has_released_coordinates
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (layer0 line1 line2 line3 : Slice Std.U32)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (hevidence : ReleasedCoordinateOutputEvidence layer0 line1 line2 line3
      (toCoordinateOutput coordinates))
    {later : Array Opening 3#usize}
    {laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {ordinal carried : Std.Usize} {rustIndex : Std.U32}
    (read : LaterBodyReadEvidence later laterIndices coordinates alphaPowers
      0#usize ordinal carried rustIndex)
    (index : Fin 32768) (htarget : ordinal.val < line1.val.length)
    (hindex : line1.val[ordinal.val]!.val = index.val) :
    CanonicalM31Array3 read.coordinate ∧
      ∀ slot : Fin 3,
        m31View read.coordinate.val[slot.val]! =
          algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line1Inverse index slot) := by
  have hlaterLength : coordinates.later.val.length = 3 := by
    simpa using Array.length_eq coordinates.later
  have hlaterBound : 0 < coordinates.later.val.length := by omega
  have harrayGet := array_index_usize_zero_get coordinates.later
    read.coordinateArray read.coordinateArrayAt (by norm_num) hlaterBound
  have harrayBang : coordinates.later.val[0]! =
      coordinates.later.val.get ⟨0, hlaterBound⟩ := by
    apply List.getElem!_of_getElem?
    simp [hlaterBound]
  have harrayEq : read.coordinateArray = coordinates.later.val[0]! :=
    harrayGet.trans harrayBang.symm
  have hrowRead := core_slice_get_some_eq
    (alloc.vec.Vec.deref read.coordinateArray) ordinal read.coordinate
      read.coordinateRead
  have hrowEq : read.coordinate =
      coordinates.later.val[0]!.val[ordinal.val]! := by
    rw [harrayEq] at hrowRead
    exact hrowRead.2.symm
  have hrawBound : line1.val[ordinal.val]!.val < 32768 := by
    rw [hindex]
    exact index.isLt
  have hfin : Fin.ofNat 32768 line1.val[ordinal.val]!.val = index := by
    apply Fin.ext
    change line1.val[ordinal.val]!.val % 32768 = index.val
    rw [Nat.mod_eq_of_lt hrawBound, hindex]
  constructor
  · intro rawSlot hslot
    let slot : Fin 3 := ⟨rawSlot, hslot⟩
    rw [hrowEq]
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      coordinates.later.val[0]!.val[ordinal.val]!.val[slot.val]!
    exact hevidence.line1Canonical ordinal.val htarget slot
  · intro slot
    have hvalue := hevidence.line1Values ordinal.val htarget slot
    change AspisV5FriCoordinateFieldSemantics.m31Value
      coordinates.later.val[0]!.val[ordinal.val]!.val[slot.val]! = _ at hvalue
    rw [hfin] at hvalue
    rw [hrowEq]
    change algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV5FriCoordinateFieldSemantics.m31Value
        coordinates.later.val[0]!.val[ordinal.val]!.val[slot.val]!) = _
    rw [hvalue, ← hsource.line1Inverse index slot]

/-- A successful second later-pass read uses the released line-two inverse
coordinates.  The equality premise is the already-proved fact that the Rust
loop threads the coordinate table without mutation. -/
theorem laterOne_read_has_released_coordinates
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (layer0 line1 line2 line3 : Slice Std.U32)
    (baseCoordinates currentCoordinates :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (hcurrent : currentCoordinates = baseCoordinates)
    (hevidence : ReleasedCoordinateOutputEvidence layer0 line1 line2 line3
      (toCoordinateOutput baseCoordinates))
    {later : Array Opening 3#usize}
    {laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {ordinal carried : Std.Usize} {rustIndex : Std.U32}
    (read : LaterBodyReadEvidence later laterIndices currentCoordinates
      alphaPowers 1#usize ordinal carried rustIndex)
    (index : Fin 8192) (htarget : ordinal.val < line2.val.length)
    (hindex : line2.val[ordinal.val]!.val = index.val) :
    CanonicalM31Array3 read.coordinate ∧
      ∀ slot : Fin 3,
        m31View read.coordinate.val[slot.val]! =
          algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line2Inverse index slot) := by
  subst currentCoordinates
  have hlaterLength : baseCoordinates.later.val.length = 3 := by
    simpa using Array.length_eq baseCoordinates.later
  have hlaterBound : 1 < baseCoordinates.later.val.length := by omega
  have harrayGet := array_index_usize_one_get baseCoordinates.later
    read.coordinateArray read.coordinateArrayAt (by norm_num) hlaterBound
  have harrayBang : baseCoordinates.later.val[1]! =
      baseCoordinates.later.val.get ⟨1, hlaterBound⟩ := by
    apply List.getElem!_of_getElem?
    simp [hlaterBound]
  have harrayEq : read.coordinateArray = baseCoordinates.later.val[1]! :=
    harrayGet.trans harrayBang.symm
  have hrowRead := core_slice_get_some_eq
    (alloc.vec.Vec.deref read.coordinateArray) ordinal read.coordinate
      read.coordinateRead
  have hrowEq : read.coordinate =
      baseCoordinates.later.val[1]!.val[ordinal.val]! := by
    rw [harrayEq] at hrowRead
    exact hrowRead.2.symm
  have hrawBound : line2.val[ordinal.val]!.val < 8192 := by
    rw [hindex]
    exact index.isLt
  have hfin : Fin.ofNat 8192 line2.val[ordinal.val]!.val = index := by
    apply Fin.ext
    change line2.val[ordinal.val]!.val % 8192 = index.val
    rw [Nat.mod_eq_of_lt hrawBound, hindex]
  constructor
  · intro rawSlot hslot
    let slot : Fin 3 := ⟨rawSlot, hslot⟩
    rw [hrowEq]
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      baseCoordinates.later.val[1]!.val[ordinal.val]!.val[slot.val]!
    exact hevidence.line2Canonical ordinal.val htarget slot
  · intro slot
    have hvalue := hevidence.line2Values ordinal.val htarget slot
    change AspisV5FriCoordinateFieldSemantics.m31Value
      baseCoordinates.later.val[1]!.val[ordinal.val]!.val[slot.val]! = _ at hvalue
    rw [hfin] at hvalue
    rw [hrowEq]
    change algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV5FriCoordinateFieldSemantics.m31Value
        baseCoordinates.later.val[1]!.val[ordinal.val]!.val[slot.val]!) = _
    rw [hvalue, ← hsource.line2Inverse index slot]

/-- The terminal pass uses the released line-three inverse coordinates and
the released final-domain x-coordinate at the exact source index. -/
theorem terminal_read_has_released_coordinates
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (layer0 line1 line2 line3 : Slice Std.U32)
    (baseCoordinates currentCoordinates :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (hcurrent : currentCoordinates = baseCoordinates)
    (hevidence : ReleasedCoordinateOutputEvidence layer0 line1 line2 line3
      (toCoordinateOutput baseCoordinates))
    {later : Array Opening 3#usize}
    {finalPolynomial : Array aspis_core.field.QM31 4#usize}
    {alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize}
    {ordinal : Std.Usize} {rustIndex : Std.U32}
    (read : TerminalBodyReadEvidence later finalPolynomial currentCoordinates
      alphaPowers 2#usize ordinal rustIndex)
    (index : Fin 2048) (htarget : ordinal.val < line3.val.length)
    (hindex : line3.val[ordinal.val]!.val = index.val) :
    CanonicalM31Array3 read.coordinate ∧
      (∀ slot : Fin 3,
        m31View read.coordinate.val[slot.val]! =
          algebraMap (ZMod AspisCircleGroupOrder.P) K
            (schedule.line3Inverse index slot)) ∧
      canonicalM31 read.finalX ∧
      m31View read.finalX =
        algebraMap (ZMod AspisCircleGroupOrder.P) K (schedule.finalX index) := by
  subst currentCoordinates
  have hlaterLength : baseCoordinates.later.val.length = 3 := by
    simpa using Array.length_eq baseCoordinates.later
  have hlaterBound : 2 < baseCoordinates.later.val.length := by omega
  have harrayGet := array_index_usize_two_get baseCoordinates.later
    read.coordinateArray read.coordinateArrayAt (by norm_num) hlaterBound
  have harrayBang : baseCoordinates.later.val[2]! =
      baseCoordinates.later.val.get ⟨2, hlaterBound⟩ := by
    apply List.getElem!_of_getElem?
    simp [hlaterBound]
  have harrayEq : read.coordinateArray = baseCoordinates.later.val[2]! :=
    harrayGet.trans harrayBang.symm
  have hrowRead := core_slice_get_some_eq
    (alloc.vec.Vec.deref read.coordinateArray) ordinal read.coordinate
      read.coordinateRead
  have hrowEq : read.coordinate =
      baseCoordinates.later.val[2]!.val[ordinal.val]! := by
    rw [harrayEq] at hrowRead
    exact hrowRead.2.symm
  have hfinalRead := core_slice_get_some_eq
    (alloc.vec.Vec.deref baseCoordinates.final_x) ordinal read.finalX
      read.finalXRead
  have hfinalEq : read.finalX = baseCoordinates.final_x.val[ordinal.val]! :=
    hfinalRead.2.symm
  have hrawBound : line3.val[ordinal.val]!.val < 2048 := by
    rw [hindex]
    exact index.isLt
  have hfin : Fin.ofNat 2048 line3.val[ordinal.val]!.val = index := by
    apply Fin.ext
    change line3.val[ordinal.val]!.val % 2048 = index.val
    rw [Nat.mod_eq_of_lt hrawBound, hindex]
  have hcoordinatesCanonical : CanonicalM31Array3 read.coordinate := by
    intro rawSlot hslot
    let slot : Fin 3 := ⟨rawSlot, hslot⟩
    rw [hrowEq]
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      baseCoordinates.later.val[2]!.val[ordinal.val]!.val[slot.val]!
    exact hevidence.line3Canonical ordinal.val htarget slot
  have hcoordinateValues : ∀ slot : Fin 3,
      m31View read.coordinate.val[slot.val]! =
        algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse index slot) := by
    intro slot
    have hvalue := hevidence.line3Values ordinal.val htarget slot
    change AspisV5FriCoordinateFieldSemantics.m31Value
      baseCoordinates.later.val[2]!.val[ordinal.val]!.val[slot.val]! = _ at hvalue
    rw [hfin] at hvalue
    rw [hrowEq]
    change algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisV5FriCoordinateFieldSemantics.m31Value
        baseCoordinates.later.val[2]!.val[ordinal.val]!.val[slot.val]!) = _
    rw [hvalue, ← hsource.line3Inverse index slot]
  have hfinalCanonical : canonicalM31 read.finalX := by
    rw [hfinalEq]
    change AspisV5FriCoordinateFieldSemantics.canonicalM31
      baseCoordinates.final_x.val[ordinal.val]!
    exact hevidence.finalXCanonical ordinal.val htarget
  have hfinalValue :
      AspisV5FriCoordinateFieldSemantics.m31Value read.finalX =
        schedule.finalX index := by
    rw [hfinalEq]
    have hvalue := hevidence.finalX ordinal.val htarget
    change AspisV5FriCoordinateFieldSemantics.m31Value
      baseCoordinates.final_x.val[ordinal.val]! = _ at hvalue
    rw [hfin] at hvalue
    exact hvalue.trans (hsource.finalX index).symm
  refine ⟨hcoordinatesCanonical, hcoordinateValues,
    hfinalCanonical, ?_⟩
  change algebraMap (ZMod AspisCircleGroupOrder.P) K
    (AspisV5FriCoordinateFieldSemantics.m31Value read.finalX) = _
  rw [hfinalValue]

/-! ## Authenticated forest projections for the exact run -/

theorem exact_run_circle_fibre
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries) (decoder : Decoder)
    (query : V5Query) (hquery : query ∈ queries) :
    decodedFibre decoder (sha256MerkleHashing sha256) run.forest .c1 query
        hquery =
      decoder.layer0
        (sectionValueAtIndex (run.sections .c1) query.val)
        (sectionValueAtIndex (run.sections .c2) query.val) := by
  rfl

theorem exact_run_line1_fibre
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries) (decoder : Decoder)
    (query : V5Query) (hquery : query ∈ queries) :
    decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line1 query
        hquery =
      decoder.later .line1
        (sectionValueAtIndex (run.sections .line1) (query.val / 4)) := by
  rfl

theorem exact_run_line2_fibre
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries) (decoder : Decoder)
    (query : V5Query) (hquery : query ∈ queries) :
    decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line2 query
        hquery =
      decoder.later .line2
        (sectionValueAtIndex (run.sections .line2) (query.val / 16)) := by
  rfl

theorem exact_run_line3_fibre
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {queries : Finset V5Query}
    (run : ExactV5Run sha256 roots queries) (decoder : Decoder)
    (query : V5Query) (hquery : query ∈ queries) :
    decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line3 query
        hquery =
      decoder.later .line3
        (sectionValueAtIndex (run.sections .line3) (query.val / 64)) := by
  rfl

/-! ## One accepted source iteration implies one model check -/

theorem accepted_execution_circle_check
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (transcript : IdealTranscript K)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hBinding : AcceptedFriModelInputBinding prepared execution.sourceAlphas
      finalPolynomial schedule transcript)
    (hCoordinates : ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref execution.laterRuns.indices0)
      (alloc.vec.Vec.deref execution.laterRuns.indices1)
      (alloc.vec.Vec.deref execution.laterRuns.indices2)
      (toCoordinateOutput execution.coordinates))
    (hPowers : ∀ (layer : Nat) (hLayer : layer < 4),
      PreparedArrayRepresents
        (mapArray hCalls.prepared
          (execution.alphaPowers.val.get
            ⟨layer, by simpa using hLayer⟩))
        (fun index => schedule.alpha ⟨layer, hLayer⟩ ^ (index + 1)))
    (query : V5Query) (hquery : query ∈ querySet) :
    AspisV5ComponentCConcreteFoldLinearity.circleFoldValue
        (schedule.alpha 0)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2x query))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2y query))
        (decodedFibre decoder (sha256MerkleHashing sha256) run.forest .c1
          query hquery) =
      decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line1
        query hquery (@slotIndex 32768 query) := by
  obtain ⟨target, htarget, hordinal, hrustQuery⟩ :=
    layerZero_source_index_at_query run openings hdriver query hquery
  obtain ⟨carried, nextPosition, _hnext, ⟨read⟩⟩ :=
    execution.layerZeroReads target htarget
  have hrustQuery' :
      openings.indices.layer0.val[target.val]!.val = query.val := by
    have hbang : openings.indices.layer0.val[target.val]! =
        openings.indices.layer0.val[target.val]'htarget := by
      apply List.getElem!_of_getElem?
      simp [htarget]
    rw [hbang]
    simpa [sliceValueAt, alloc.vec.Vec.deref] using hrustQuery
  have hbytes := layerZero_read_matches_exact_run run openings hdriver read
    query hquery hordinal hrustQuery
  have hcoordinate := layerZero_read_has_released_coordinates schedule
    hsource
    (alloc.vec.Vec.deref openings.indices.layer0)
    (alloc.vec.Vec.deref execution.laterRuns.indices0)
    (alloc.vec.Vec.deref execution.laterRuns.indices1)
    (alloc.vec.Vec.deref execution.laterRuns.indices2)
    execution.coordinates hCoordinates read query htarget hrustQuery'
  have hAlphaLength : execution.alphaPowers.val.length = 4 := by
    simpa using Array.length_eq execution.alphaPowers
  have hAlphaBound : 0 < execution.alphaPowers.val.length := by omega
  have hAlphaAt := array_index_usize_zero_get execution.alphaPowers read.alpha
    read.alphaRead (by norm_num) hAlphaBound
  have hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha)
      (fun index => schedule.alpha 0 ^ (index + 1)) := by
    rw [hAlphaAt]
    exact hPowers 0 (by norm_num)
  have hCombinedCanonical : CanonicalQM31Array4
      (mapArray toExactQM31 read.combined) := by
    apply hBinding.combinedCanonical read.c1Value read.c2Value
    simpa using read.combineCall
  have hfold := layer_zero_read_yields_circle_equation read hCalls
    (schedule.alpha 0) hCombinedCanonical hcoordinate.1 hcoordinate.2.1
    hAlphaPowers
  have hslot :
      (⟨((sliceValueAt (alloc.vec.Vec.deref openings.indices.layer0)
          target htarget) &&& 3#u32).val, by
        rw [UScalar.val_and]
        exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ : Fin 4) =
        @slotIndex 32768 query := by
    apply Fin.ext
    simp only [slotIndex, Fin.val_mk]
    rw [u32_and_three_val, hrustQuery]
  rw [exact_run_circle_fibre run decoder query hquery,
    exact_run_line1_fibre run decoder query hquery]
  rw [← hbytes.1, ← hbytes.2.1, ← hbytes.2.2]
  calc
    AspisV5ComponentCConcreteFoldLinearity.circleFoldValue
        (schedule.alpha 0)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2x query))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.circleInv2y query))
        (decoder.layer0 (read.c1Value.val.map generatedU8ToByte)
          (read.c2Value.val.map generatedU8ToByte)) =
      AspisV5ComponentCConcreteFoldLinearity.circleFoldValue
        (schedule.alpha 0) (m31View read.inv2x) (m31View read.inv2y)
        (fun slot => qm31View
          (toExactQM31 read.combined.val[slot.val]!)) := by
            rw [hcoordinate.2.2.1, hcoordinate.2.2.2]
            congr 1
            funext slot
            exact hAgreement.layer0 read.c1Value read.c2Value
              read.combined (by simpa using read.combineCall) slot
    _ = qm31View (toExactQM31 read.decodedParent) := hfold
    _ = decoder.later .line1
        (read.parentValue.val.map generatedU8ToByte)
        (@slotIndex 32768 query) := by
          rw [← hslot]
          exact (hAgreement.layerZeroParent read.parentValue
            read.selectedSlice
            (sliceValueAt (alloc.vec.Vec.deref openings.indices.layer0)
              target htarget)
            read.decodedParent
            read.selectedSliceRead read.decodeParentCall).symm

theorem accepted_execution_line1_check
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hCoordinates : ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref execution.laterRuns.indices0)
      (alloc.vec.Vec.deref execution.laterRuns.indices1)
      (alloc.vec.Vec.deref execution.laterRuns.indices2)
      (toCoordinateOutput execution.coordinates))
    (hPowers : ∀ (layer : Nat) (hLayer : layer < 4),
      PreparedArrayRepresents
        (mapArray hCalls.prepared
          (execution.alphaPowers.val.get
            ⟨layer, by simpa using hLayer⟩))
        (fun index => schedule.alpha ⟨layer, hLayer⟩ ^ (index + 1)))
    (query : V5Query) (hquery : query ∈ querySet) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 1)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 query) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 query) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 query) 2))
        (decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line1
          query hquery) =
      decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line2
        query hquery (@slotIndex 8192 (queryParent1 query)) := by
  have hc1Active : query.val ∈ activeIndices .c1 querySet 0 := by
    simpa [sectionIndex] using sectionIndex_mem_active .c1 hquery
  have hactive : query.val / 4 ∈ activeIndices .line1 querySet 0 :=
    layer0_parent_mem_line1 hc1Active
  have hindices := later_run_zero_indices_eq_ordered run openings hdriver
    execution.laterRuns.indices0 execution.laterRuns.indicesAt0
  obtain ⟨target, htarget, hordinal, hrustIndex⟩ := source_index_at_active
    .line1 querySet execution.laterRuns.indices0 hindices
      (query.val / 4) hactive
  obtain ⟨carried, nextPosition, _hnext, ⟨read⟩⟩ :=
    execution.later0Reads target htarget
  have hbytes := laterZero_read_matches_exact_run run openings hdriver read
    (query.val / 4) hactive hordinal hrustIndex
  have hrustIndex' :
      execution.laterRuns.indices0.val[target.val]!.val = query.val / 4 := by
    rw [← sliceValueAt_eq_bang execution.laterRuns.indices0 target htarget]
    exact hrustIndex
  have hcoordinate := laterZero_read_has_released_coordinates schedule hsource
    (alloc.vec.Vec.deref openings.indices.layer0)
    (alloc.vec.Vec.deref execution.laterRuns.indices0)
    (alloc.vec.Vec.deref execution.laterRuns.indices1)
    (alloc.vec.Vec.deref execution.laterRuns.indices2)
    execution.coordinates hCoordinates read (queryParent1 query) htarget
    (by
      change execution.laterRuns.indices0.val[target.val]!.val =
        (queryParent1 query).val
      simpa [queryParent1] using hrustIndex')
  have hAlphaLength : execution.alphaPowers.val.length = 4 := by
    simpa using Array.length_eq execution.alphaPowers
  have hAlphaBound : 1 < execution.alphaPowers.val.length := by omega
  have hAlphaCall : Array.index_usize execution.alphaPowers 1#usize =
      .ok read.alpha := by
    simpa only [usize_wrapping_zero_add_one] using read.alphaRead
  have hAlphaAt := array_index_usize_one_get execution.alphaPowers read.alpha
    hAlphaCall (by norm_num) hAlphaBound
  have hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha)
      (fun index => schedule.alpha 1 ^ (index + 1)) := by
    rw [hAlphaAt]
    exact hPowers 1 (by norm_num)
  have hfold := later_read_yields_line_equation read hCalls referenceDecoded
    (production_decoders_have_reference_semantics hDecoder)
    (schedule.alpha 1) hcoordinate.1 hAlphaPowers
  have hslot :
      (⟨((UScalar.cast .Usize
          (sliceValueAt (alloc.vec.Vec.deref execution.laterRuns.indices0)
            target htarget)) &&& 3#usize).val, by
        rw [UScalar.val_and]
        exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ : Fin 4) =
        @slotIndex 8192 (queryParent1 query) := by
    have hcastValue :
        (UScalar.cast .Usize
          (sliceValueAt (alloc.vec.Vec.deref execution.laterRuns.indices0)
            target htarget)).val = query.val / 4 := by
      rw [Std.U32.cast_Usize_val_eq]
      exact hrustIndex
    apply Fin.ext
    simp only [slotIndex, Fin.val_mk]
    rw [usize_and_three_val, hcastValue]
    rfl
  rw [exact_run_line1_fibre run decoder query hquery,
    exact_run_line2_fibre run decoder query hquery]
  have hdiv : query.val / 4 / 4 = query.val / 16 := by omega
  rw [← hbytes.1, ← hdiv, ← hbytes.2]
  calc
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 1)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 query) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 query) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line1Inverse (queryParent1 query) 2))
        (decoder.later .line1
          (read.incomingValue.val.map generatedU8ToByte)) =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 1)
        (m31View read.coordinate.val[0]!)
        (m31View read.coordinate.val[1]!)
        (m31View read.coordinate.val[2]!)
        (referenceDecoded read.incomingValue) := by
          rw [← hcoordinate.2 0, ← hcoordinate.2 1, ← hcoordinate.2 2]
          congr 1
          funext slot
          exact hAgreement.laterReference .line1 read.incomingValue slot
    _ = referenceDecoded read.parentValue
        ⟨((UScalar.cast .Usize
          (sliceValueAt (alloc.vec.Vec.deref execution.laterRuns.indices0)
            target htarget)) &&& 3#usize).val, by
          rw [UScalar.val_and]
          exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ := hfold
    _ = decoder.later .line2
        (read.parentValue.val.map generatedU8ToByte)
        (@slotIndex 8192 (queryParent1 query)) := by
          rw [← hslot]
          exact (hAgreement.laterReference .line2 read.parentValue _).symm

theorem accepted_execution_line2_check
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hCoordinates : ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref execution.laterRuns.indices0)
      (alloc.vec.Vec.deref execution.laterRuns.indices1)
      (alloc.vec.Vec.deref execution.laterRuns.indices2)
      (toCoordinateOutput execution.coordinates))
    (hPowers : ∀ (layer : Nat) (hLayer : layer < 4),
      PreparedArrayRepresents
        (mapArray hCalls.prepared
          (execution.alphaPowers.val.get
            ⟨layer, by simpa using hLayer⟩))
        (fun index => schedule.alpha ⟨layer, hLayer⟩ ^ (index + 1)))
    (query : V5Query) (hquery : query ∈ querySet) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 2)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 query) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 query) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 query) 2))
        (decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line2
          query hquery) =
      decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line3
        query hquery (@slotIndex 2048 (queryParent2 query)) := by
  have hc1Active : query.val ∈ activeIndices .c1 querySet 0 := by
    simpa [sectionIndex] using sectionIndex_mem_active .c1 hquery
  have hline1Active : query.val / 4 ∈ activeIndices .line1 querySet 0 :=
    layer0_parent_mem_line1 hc1Active
  have hactiveRaw := line1_parent_mem_line2 hline1Active
  have hactive : query.val / 16 ∈ activeIndices .line2 querySet 0 := by
    have hdiv : query.val / 4 / 4 = query.val / 16 := by omega
    simpa only [hdiv] using hactiveRaw
  have hindices := later_run_one_indices_eq_ordered run openings hdriver
    execution.laterRuns.indices1 execution.laterRuns.indicesAt1
  obtain ⟨target, htarget, hordinal, hrustIndex⟩ := source_index_at_active
    .line2 querySet execution.laterRuns.indices1 hindices
      (query.val / 16) hactive
  obtain ⟨carried, nextPosition, _hnext, ⟨read⟩⟩ :=
    execution.later1Reads target htarget
  have hbytes := laterOne_read_matches_exact_run run openings hdriver read
    (query.val / 16) hactive hordinal hrustIndex
  have hrustIndex' :
      execution.laterRuns.indices1.val[target.val]!.val = query.val / 16 := by
    rw [← sliceValueAt_eq_bang execution.laterRuns.indices1 target htarget]
    exact hrustIndex
  have hcoordinate := laterOne_read_has_released_coordinates schedule hsource
    (alloc.vec.Vec.deref openings.indices.layer0)
    (alloc.vec.Vec.deref execution.laterRuns.indices0)
    (alloc.vec.Vec.deref execution.laterRuns.indices1)
    (alloc.vec.Vec.deref execution.laterRuns.indices2)
    execution.coordinates execution.laterRuns.coordinates1
    execution.laterRuns.coordinates_preserved.1 hCoordinates read
    (queryParent2 query) htarget
    (by
      change execution.laterRuns.indices1.val[target.val]!.val =
        (queryParent2 query).val
      simpa [queryParent2] using hrustIndex')
  have hAlphaLength : execution.alphaPowers.val.length = 4 := by
    simpa using Array.length_eq execution.alphaPowers
  have hAlphaBound : 2 < execution.alphaPowers.val.length := by omega
  have hAlphaCall : Array.index_usize execution.alphaPowers 2#usize =
      .ok read.alpha := by
    simpa only [usize_wrapping_one_add_one] using read.alphaRead
  have hAlphaAt := array_index_usize_two_get execution.alphaPowers read.alpha
    hAlphaCall (by norm_num) hAlphaBound
  have hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha)
      (fun index => schedule.alpha 2 ^ (index + 1)) := by
    rw [hAlphaAt]
    exact hPowers 2 (by norm_num)
  have hfold := later_read_yields_line_equation read hCalls referenceDecoded
    (production_decoders_have_reference_semantics hDecoder)
    (schedule.alpha 2) hcoordinate.1 hAlphaPowers
  have hslot :
      (⟨((UScalar.cast .Usize
          (sliceValueAt (alloc.vec.Vec.deref execution.laterRuns.indices1)
            target htarget)) &&& 3#usize).val, by
        rw [UScalar.val_and]
        exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ : Fin 4) =
        @slotIndex 2048 (queryParent2 query) := by
    have hcastValue :
        (UScalar.cast .Usize
          (sliceValueAt (alloc.vec.Vec.deref execution.laterRuns.indices1)
            target htarget)).val = query.val / 16 := by
      rw [Std.U32.cast_Usize_val_eq]
      exact hrustIndex
    apply Fin.ext
    simp only [slotIndex, Fin.val_mk]
    rw [usize_and_three_val, hcastValue]
    rfl
  rw [exact_run_line2_fibre run decoder query hquery,
    exact_run_line3_fibre run decoder query hquery]
  have hdiv : query.val / 16 / 4 = query.val / 64 := by omega
  rw [← hbytes.1, ← hdiv, ← hbytes.2]
  calc
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 2)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 query) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 query) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line2Inverse (queryParent2 query) 2))
        (decoder.later .line2
          (read.incomingValue.val.map generatedU8ToByte)) =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 2)
        (m31View read.coordinate.val[0]!)
        (m31View read.coordinate.val[1]!)
        (m31View read.coordinate.val[2]!)
        (referenceDecoded read.incomingValue) := by
          rw [← hcoordinate.2 0, ← hcoordinate.2 1, ← hcoordinate.2 2]
          congr 1
          funext slot
          exact hAgreement.laterReference .line2 read.incomingValue slot
    _ = referenceDecoded read.parentValue
        ⟨((UScalar.cast .Usize
          (sliceValueAt (alloc.vec.Vec.deref execution.laterRuns.indices1)
            target htarget)) &&& 3#usize).val, by
          rw [UScalar.val_and]
          exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ := hfold
    _ = decoder.later .line3
        (read.parentValue.val.map generatedU8ToByte)
        (@slotIndex 2048 (queryParent2 query)) := by
          rw [← hslot]
          exact (hAgreement.laterReference .line3 read.parentValue _).symm

theorem accepted_execution_line3_check
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (transcript : IdealTranscript K)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hBinding : AcceptedFriModelInputBinding prepared execution.sourceAlphas
      finalPolynomial schedule transcript)
    (hCoordinates : ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref execution.laterRuns.indices0)
      (alloc.vec.Vec.deref execution.laterRuns.indices1)
      (alloc.vec.Vec.deref execution.laterRuns.indices2)
      (toCoordinateOutput execution.coordinates))
    (hPowers : ∀ (layer : Nat) (hLayer : layer < 4),
      PreparedArrayRepresents
        (mapArray hCalls.prepared
          (execution.alphaPowers.val.get
            ⟨layer, by simpa using hLayer⟩))
        (fun index => schedule.alpha ⟨layer, hLayer⟩ ^ (index + 1)))
    (query : V5Query) (hquery : query ∈ querySet) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 3)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 query) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 query) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 query) 2))
        (decodedFibre decoder (sha256MerkleHashing sha256) run.forest .line3
          query hquery) =
      AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.finalX (queryParent3 query)))
        transcript.publishedFinal := by
  have hc1Active : query.val ∈ activeIndices .c1 querySet 0 := by
    simpa [sectionIndex] using sectionIndex_mem_active .c1 hquery
  have hline1Active : query.val / 4 ∈ activeIndices .line1 querySet 0 :=
    layer0_parent_mem_line1 hc1Active
  have hline2ActiveRaw := line1_parent_mem_line2 hline1Active
  have hline2Active : query.val / 16 ∈ activeIndices .line2 querySet 0 := by
    have hdiv : query.val / 4 / 4 = query.val / 16 := by omega
    simpa only [hdiv] using hline2ActiveRaw
  have hactiveRaw := line2_parent_mem_line3 hline2Active
  have hactive : query.val / 64 ∈ activeIndices .line3 querySet 0 := by
    have hdiv : query.val / 16 / 4 = query.val / 64 := by omega
    simpa only [hdiv] using hactiveRaw
  have hindices := later_run_two_indices_eq_ordered run openings hdriver
    execution.laterRuns.indices2 execution.laterRuns.indicesAt2
  obtain ⟨target, htarget, hordinal, hrustIndex⟩ := source_index_at_active
    .line3 querySet execution.laterRuns.indices2 hindices
      (query.val / 64) hactive
  obtain ⟨nextPosition, _hnext, ⟨read⟩⟩ :=
    execution.later2Reads target htarget
  have hbytes := terminal_read_matches_exact_run run openings hdriver read
    (query.val / 64) hactive hordinal
  have hrustIndex' :
      execution.laterRuns.indices2.val[target.val]!.val = query.val / 64 := by
    rw [← sliceValueAt_eq_bang execution.laterRuns.indices2 target htarget]
    exact hrustIndex
  have hcoordinate := terminal_read_has_released_coordinates schedule hsource
    (alloc.vec.Vec.deref openings.indices.layer0)
    (alloc.vec.Vec.deref execution.laterRuns.indices0)
    (alloc.vec.Vec.deref execution.laterRuns.indices1)
    (alloc.vec.Vec.deref execution.laterRuns.indices2)
    execution.coordinates execution.laterRuns.coordinates2
    execution.laterRuns.coordinates_preserved.2.1 hCoordinates read
    (queryParent3 query) htarget
    (by
      change execution.laterRuns.indices2.val[target.val]!.val =
        (queryParent3 query).val
      simpa [queryParent3] using hrustIndex')
  have hAlphaLength : execution.alphaPowers.val.length = 4 := by
    simpa using Array.length_eq execution.alphaPowers
  have hAlphaBound : 3 < execution.alphaPowers.val.length := by omega
  have hAlphaAt := array_index_usize_three_get execution.alphaPowers
    read.alpha read.alphaRead (by norm_num) hAlphaBound
  have hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha)
      (fun index => schedule.alpha 3 ^ (index + 1)) := by
    rw [hAlphaAt]
    exact hPowers 3 (by norm_num)
  have hfold := terminal_read_yields_final_equation read hCalls
    referenceDecoded (production_decoders_have_reference_semantics hDecoder)
    (schedule.alpha 3) hBinding.finalCanonical hcoordinate.1
    hcoordinate.2.2.1 hAlphaPowers
  rw [exact_run_line3_fibre run decoder query hquery, ← hbytes]
  calc
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 3)
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 query) 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 query) 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.line3Inverse (queryParent3 query) 2))
        (decoder.later .line3
          (read.incomingValue.val.map generatedU8ToByte)) =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
        (schedule.alpha 3)
        (m31View read.coordinate.val[0]!)
        (m31View read.coordinate.val[1]!)
        (m31View read.coordinate.val[2]!)
        (referenceDecoded read.incomingValue) := by
          rw [← hcoordinate.2.1 0, ← hcoordinate.2.1 1,
            ← hcoordinate.2.1 2]
          congr 1
          funext slot
          exact hAgreement.laterReference .line3 read.incomingValue slot
    _ = AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
        (m31View read.finalX)
        (fun slot => qm31View
          (toExactQM31 finalPolynomial.val[slot.val]!)) := hfold
    _ = AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (schedule.finalX (queryParent3 query)))
        transcript.publishedFinal := by
          rw [hcoordinate.2.2.2]
          congr 1
          funext slot
          exact hBinding.finalValue slot

/-- Collision freedom makes the decoded FRI fibre independent of which valid
opening witness is chosen for fixed roots and query indices. -/
theorem decoded_fibre_eq_of_collision_free
    {Digest : Type*} (decoder : Decoder) (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (hfree : CollisionFree hashing)
    (left right : AcceptedV5Forest hashing roots querySet)
    (tree : V5PrivateSection) (query : V5Query) (hquery : query ∈ querySet) :
    decodedFibre decoder hashing left tree query hquery =
      decodedFibre decoder hashing right tree query hquery := by
  cases tree with
  | c1 =>
      unfold decodedFibre
      rw [acceptedV5Forest_values_unique hashing hfree left right .c1 query
        hquery]
      rw [acceptedV5Forest_values_unique hashing hfree left right .c2 query
        hquery]
  | c2 =>
      unfold decodedFibre
      rw [acceptedV5Forest_values_unique hashing hfree left right .c2 query
        hquery]
  | line1 =>
      unfold decodedFibre
      rw [acceptedV5Forest_values_unique hashing hfree left right .line1 query
        hquery]
  | line2 =>
      unfold decodedFibre
      rw [acceptedV5Forest_values_unique hashing hfree left right .line2 query
        hquery]
  | line3 =>
      unfold decodedFibre
      rw [acceptedV5Forest_values_unique hashing hfree left right .line3 query
        hquery]

/-- The four authenticated arithmetic checks transport to every other valid
forest with the same roots and queries, unless the explicit Merkle collision
event occurs. -/
theorem forest_fri_checks_of_collision_free
    {Digest : Type*} (decoder : Decoder) (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (hfree : CollisionFree hashing)
    (reference accepted : AcceptedV5Forest hashing roots querySet)
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (hchecks : ForestFriChecks decoder hashing reference schedule transcript
      queries) :
    ForestFriChecks decoder hashing accepted schedule transcript queries := by
  refine {
    queryMember := hchecks.queryMember
    circle := ?_
    line1 := ?_
    line2 := ?_
    line3 := ?_ }
  · intro i
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .c1 (queries i) (hchecks.queryMember i)]
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .line1 (queries i) (hchecks.queryMember i)]
    exact hchecks.circle i
  · intro i
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .line1 (queries i) (hchecks.queryMember i)]
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .line2 (queries i) (hchecks.queryMember i)]
    exact hchecks.line1 i
  · intro i
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .line2 (queries i) (hchecks.queryMember i)]
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .line3 (queries i) (hchecks.queryMember i)]
    exact hchecks.line2 i
  · intro i
    rw [decoded_fibre_eq_of_collision_free decoder hashing hfree accepted
      reference .line3 (queries i) (hchecks.queryMember i)]
    exact hchecks.line3 i

/-- One accepted execution of the extracted production FRI verifier implies
all four arithmetic comparisons over the values authenticated by the exact
Merkle run.  The remaining inputs name only the source-call, decoder,
released-table, and transcript-value equalities used at their literal
boundaries. -/
theorem accepted_production_execution_yields_forest_fri_checks
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (hqueryMember : ∀ i, queries i ∈ querySet)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hBinding : AcceptedFriModelInputBinding prepared execution.sourceAlphas
      finalPolynomial schedule transcript)
    (hValidate : ValidationSuccessPreservesShape)
    (hCoordinateSource :
      AcceptedExecutionCoordinateSourceCertificate execution) :
    ForestFriChecks decoder (sha256MerkleHashing sha256) run.forest schedule
      transcript queries := by
  rcases execution.preparationTrace with ⟨trace⟩
  have hAdapter : AcceptedProductionCoordinateAdapterEquality trace :=
    hCoordinateSource trace
  have hlater0 : trace.later0 = execution.laterRuns.indices0 := by
    have h := execution.laterRuns.indicesAt0
    rw [trace.later0Read] at h
    exact Result.ok.inj h
  have hlater1 : trace.later1 = execution.laterRuns.indices1 := by
    have h := execution.laterRuns.indicesAt1
    rw [trace.later1Read] at h
    exact Result.ok.inj h
  have hlater2 : trace.later2 = execution.laterRuns.indices2 := by
    have h := execution.laterRuns.indicesAt2
    rw [trace.later2Read] at h
    exact Result.ok.inj h
  have hCoordinatesTrace :=
    production_trace_released_coordinate_tables_from_exact_run run trace
      hdriver hValidate hAdapter
  have hCoordinates : ReleasedCoordinateOutputEvidence
      (alloc.vec.Vec.deref openings.indices.layer0)
      (alloc.vec.Vec.deref execution.laterRuns.indices0)
      (alloc.vec.Vec.deref execution.laterRuns.indices1)
      (alloc.vec.Vec.deref execution.laterRuns.indices2)
      (toCoordinateOutput execution.coordinates) := by
    simpa only [hlater0, hlater1, hlater2] using hCoordinatesTrace
  have hSourceLength : execution.sourceAlphas.val.length = 4 := by
    simpa using Array.length_eq execution.sourceAlphas
  have hCanonicalGet : ∀ (layer : Nat) (hLayer : layer < 4),
      canonicalQM31 (toExactQM31
        (execution.sourceAlphas.val.get
          ⟨layer, by simpa using hLayer⟩)) := by
    intro layer hLayer
    have hbound : layer < execution.sourceAlphas.val.length := by omega
    have hbang : execution.sourceAlphas.val[layer]! =
        execution.sourceAlphas.val.get ⟨layer, hbound⟩ := by
      apply List.getElem!_of_getElem?
      simp [hbound]
    rw [← hbang]
    exact hBinding.alphaCanonical ⟨layer, hLayer⟩
  have hPowersRaw := source_alpha_map_yields_exact_powers hCalls
    execution.sourceAlphas execution.alphaPowers hCanonicalGet
    trace.alphaPowersCall
  have hPowers : ∀ (layer : Nat) (hLayer : layer < 4),
      PreparedArrayRepresents
        (mapArray hCalls.prepared
          (execution.alphaPowers.val.get
            ⟨layer, by simpa using hLayer⟩))
        (fun index => schedule.alpha ⟨layer, hLayer⟩ ^ (index + 1)) := by
    intro layer hLayer
    have hp := hPowersRaw layer hLayer
    have hbound : layer < execution.sourceAlphas.val.length := by omega
    have hbang : execution.sourceAlphas.val[layer]! =
        execution.sourceAlphas.val.get ⟨layer, hbound⟩ := by
      apply List.getElem!_of_getElem?
      simp [hbound]
    have hvalue : qm31View (toExactQM31
        (execution.sourceAlphas.val.get ⟨layer, hbound⟩)) =
        schedule.alpha ⟨layer, hLayer⟩ := by
      rw [← hbang]
      exact hBinding.alphaValue ⟨layer, hLayer⟩
    simpa only [hvalue] using hp
  refine {
    queryMember := hqueryMember
    circle := ?_
    line1 := ?_
    line2 := ?_
    line3 := ?_ }
  · intro i
    exact accepted_execution_circle_check run openings prepared finalPolynomial
      sink execution hdriver schedule hsource transcript decoder hCalls
      hAgreement hBinding hCoordinates hPowers (queries i) (hqueryMember i)
  · intro i
    exact accepted_execution_line1_check run openings prepared finalPolynomial
      sink execution hdriver schedule hsource decoder hCalls hAgreement
      hDecoder hCoordinates hPowers (queries i) (hqueryMember i)
  · intro i
    exact accepted_execution_line2_check run openings prepared finalPolynomial
      sink execution hdriver schedule hsource decoder hCalls hAgreement
      hDecoder hCoordinates hPowers (queries i) (hqueryMember i)
  · intro i
    exact accepted_execution_line3_check run openings prepared finalPolynomial
      sink execution hdriver schedule hsource transcript decoder hCalls
      hAgreement hDecoder hBinding hCoordinates hPowers (queries i)
      (hqueryMember i)

/-- The query-membership input above is already a consequence of the exact
transcript projection used by the released security theorem.  This wrapper
keeps that fact connected to its source instead of asking a caller to repeat
it as a separate premise. -/
theorem accepted_production_execution_yields_forest_fri_checks_of_projection
    {PointValue : Type*}
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (hsource : ProductionUsesReleasedFriTables schedule)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (relationInput : AspisV5RelationStressSourceBridge.SourceRelationInput K)
    (transcriptInput : AspisV5TranscriptConnection.V5TranscriptInputs)
    (derived : AspisV5TranscriptConnection.V5DerivedValues K PointValue)
    (driverResult : AspisV5TranscriptConnection.V5TranscriptDriverResult K
      PointValue)
    (projection : TranscriptExecutionProjection relationInput transcriptInput
      derived driverResult querySet queries)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hBinding : AcceptedFriModelInputBinding prepared execution.sourceAlphas
      finalPolynomial schedule transcript)
    (hValidate : ValidationSuccessPreservesShape)
    (hCoordinateSource :
      AcceptedExecutionCoordinateSourceCertificate execution) :
    ForestFriChecks decoder (sha256MerkleHashing sha256) run.forest schedule
      transcript queries := by
  exact accepted_production_execution_yields_forest_fri_checks run openings
    prepared finalPolynomial sink execution hdriver schedule hsource transcript
    queries (scheduledQuery_mem_of_projection relationInput transcriptInput
      derived driverResult querySet queries projection) decoder hCalls
    hAgreement hDecoder hBinding hValidate hCoordinateSource

/-- Specializing the schedule to the exact released tables removes the
separate table-equality premise.  The transcript projection also supplies all
18 query-membership facts. -/
theorem accepted_production_execution_yields_released_forest_fri_checks
    {PointValue : Type*}
    {sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32}
    {roots : V5PrivateRoots Digest32} {querySet : Finset V5Query}
    (run : ExactV5Run sha256 roots querySet)
    (openings : private_openings.VerifiedV5PrivateOpenings)
    (prepared : fri_checks.V5PreparedPcsClaims)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (sink : fri_checks.V5FriCheckSink)
    (execution : AcceptedProductionFriExecution openings prepared
      finalPolynomial sink)
    (hdriver : generatedDriverOutput openings = driverOutputOfRun run [])
    (base : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (relationInput : AspisV5RelationStressSourceBridge.SourceRelationInput K)
    (transcriptInput : AspisV5TranscriptConnection.V5TranscriptInputs)
    (derived : AspisV5TranscriptConnection.V5DerivedValues K PointValue)
    (driverResult : AspisV5TranscriptConnection.V5TranscriptDriverResult K
      PointValue)
    (projection : TranscriptExecutionProjection relationInput transcriptInput
      derived driverResult querySet queries)
    (decoder : Decoder) (hCalls : ExactFriHelperCallEquality)
    (hAgreement : AcceptedCallDecoderAgreement prepared decoder)
    (hDecoder : ProductionDecoderReferenceEquality)
    (hBinding : AcceptedFriModelInputBinding prepared execution.sourceAlphas
      finalPolynomial (exactReleasedFriTables base) transcript)
    (hValidate : ValidationSuccessPreservesShape)
    (hCoordinateSource :
      AcceptedExecutionCoordinateSourceCertificate execution) :
    ForestFriChecks decoder (sha256MerkleHashing sha256) run.forest
      (exactReleasedFriTables base) transcript queries := by
  exact
    accepted_production_execution_yields_forest_fri_checks_of_projection run
      openings prepared finalPolynomial sink execution hdriver
      (exactReleasedFriTables base) (exactReleasedFriTables_source_shape base)
      transcript queries relationInput transcriptInput derived driverResult
      projection decoder hCalls hAgreement hDecoder hBinding hValidate
      hCoordinateSource

/-- Once one exact accepted forest has all four FRI checks, the FRI-arithmetic
failure arm of the released security event is impossible.  A purported
different accepted forest either exposes the already explicit Merkle
collision event or has the same decoded values and therefore the same four
checks. -/
theorem remove_released_fri_arithmetic_failure_into_collision
    {Digest : Type*} (decoder : Decoder) (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (reference : AcceptedV5Forest hashing roots querySet)
    (schedule : FixedSchedule (ZMod AspisCircleGroupOrder.P) K)
    (transcript : IdealTranscript K)
    (queries : QuerySchedule 18 131072)
    (hchecks : ForestFriChecks decoder hashing reference schedule transcript
      queries)
    {sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      workFailure queryMiss countedFriFibre candidateTraceFailure
      relationRepair poseidonFailure : Prop}
    (event : ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      (HashCollision hashing) workFailure
      (∃ forest : AcceptedV5Forest hashing roots querySet,
        ¬ ForestFriChecks decoder hashing forest schedule transcript queries)
      queryMiss countedFriFibre candidateTraceFailure relationRepair
      poseidonFailure) :
    ReleasedAcceptedExecutionSecurityEvent
      sourceRelationProjectionFailure familyProjectionFailure
      transcriptProjectionFailure workProjectionFailure
      referenceForestFailure rustOpeningCorrespondenceFailure
      (HashCollision hashing) workFailure False queryMiss countedFriFibre
      candidateTraceFailure relationRepair poseidonFailure := by
  cases event with
  | sourceRelationProjection failure => exact .sourceRelationProjection failure
  | familyProjection failure => exact .familyProjection failure
  | transcriptProjection failure => exact .transcriptProjection failure
  | workProjection failure => exact .workProjection failure
  | releasedFinalDomain failure => exact failure.elim
  | releasedInverseTable failure => exact failure.elim
  | referenceForest failure => exact .referenceForest failure
  | globalCausalSelection failure => exact failure.elim
  | rustOpeningCorrespondence failure =>
      exact .rustOpeningCorrespondence failure
  | merkleHashCollision failure => exact .merkleHashCollision failure
  | workCheck failure => exact .workCheck failure
  | friArithmetic failure =>
      rcases failure with ⟨accepted, hfailure⟩
      by_cases hcollision : HashCollision hashing
      · exact .merkleHashCollision hcollision
      · exact (hfailure (forest_fri_checks_of_collision_free decoder hashing
          hcollision reference accepted schedule transcript queries hchecks)).elim
  | queryPhase failure => exact .queryPhase failure
  | friFibre failure => exact .friFibre failure
  | candidateTrace failure => exact .candidateTrace failure
  | relationRepairEvent failure => exact .relationRepairEvent failure
  | poseidon failure => exact .poseidon failure
  | publishedDecoding failure => exact failure.elim

#print axioms generated_indices_nodup_of_eq_ordered
#print axioms successful_parent_read_matches_exact_run
#print axioms layerZero_read_matches_exact_run
#print axioms laterZero_read_matches_exact_run
#print axioms laterOne_read_matches_exact_run
#print axioms terminal_read_matches_exact_run
#print axioms source_index_at_active
#print axioms layerZero_read_has_released_coordinates
#print axioms accepted_execution_circle_check
#print axioms accepted_execution_line1_check
#print axioms accepted_execution_line2_check
#print axioms accepted_execution_line3_check
#print axioms forest_fri_checks_of_collision_free
#print axioms accepted_production_execution_yields_forest_fri_checks
#print axioms AspisV5FriAcceptedForestChecks.accepted_production_execution_yields_forest_fri_checks_of_projection
#print axioms AspisV5FriAcceptedForestChecks.accepted_production_execution_yields_released_forest_fri_checks
#print axioms remove_released_fri_arithmetic_failure_into_collision

end AspisV5FriAcceptedForestChecks
