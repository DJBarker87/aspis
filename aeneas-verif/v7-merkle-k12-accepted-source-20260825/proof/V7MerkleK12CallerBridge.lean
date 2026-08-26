import V7MerkleK12OuterTraceBridge
import V7MerkleCallerNamespaceBridge

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Production V7 caller to accepted-opening bridge

This file starts at the transparent `v7_onefold` caller extraction.  It uses
the kernel-checked namespace bridge for the duplicate Merkle functions and
constructs source seeds from literal caller query and leaf-hash calls.
-/

namespace AspisV7MerkleK12CallerBridge

attribute [local simp]
  core.option.Option.ok_or
  core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  core.convert.FromSame core.convert.FromSame.from

private theorem usize_result_mul_exact (left right result : Std.Usize)
    (bound : left.val * right.val ≤ Std.Usize.max)
    (value : result.val = left.val * right.val) :
    (left * right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.mul_spec (x := left) (y := right) bound)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_result_add_exact (left right result : Std.Usize)
    (bound : left.val + right.val ≤ Std.Usize.max)
    (value : result.val = left.val + right.val) :
    (left + right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.add_spec (x := left) (y := right) bound)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem usize_result_div_exact (left right result : Std.Usize)
    (nonzero : right.val ≠ 0)
    (value : result.val = left.val / right.val) :
    (left / right : Result Std.Usize) = (ok result : Result Std.Usize) := by
  obtain ⟨actual, run, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.div_spec left (y := right) nonzero)
  have actualEq : actual = result := by
    apply UScalar.eq_of_val_eq
    omega
  rw [run, actualEq]

private theorem caller_c1_bytes_exact :
    V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY =
      .ok 403#usize := by
  have mul_4_26 : (4#usize * 26#usize : Result Std.Usize) =
      .ok 104#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_104_31 : (104#usize * 31#usize : Result Std.Usize) =
      .ok 3224#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_3224_7 : (3224#usize + 7#usize : Result Std.Usize) =
      .ok 3231#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_3231_8 : (3231#usize / 8#usize : Result Std.Usize) =
      .ok 403#usize := by
    apply usize_result_div_exact <;> scalar_tac
  simp [V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_C1_BYTES_PER_QUERY,
    V7MerkleCallerGenerated.v6_onefold.V6_C1_PACKED_BYTES_PER_QUERY,
    V7MerkleCallerGenerated.v6_onefold.V6_C1_LIMBS_PER_QUERY,
    V7MerkleCallerGenerated.v6_onefold.V6_C1_COLUMNS,
    V7MerkleCallerGenerated.v6_onefold.packed_bytes, mul_4_26, mul_104_31,
    add_3224_7, div_3231_8]

private theorem caller_c2_bytes_exact :
    V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY =
      .ok 186#usize := by
  have mul_4_4 : (4#usize * 4#usize : Result Std.Usize) =
      .ok 16#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_16_3 : (16#usize * 3#usize : Result Std.Usize) =
      .ok 48#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have mul_48_31 : (48#usize * 31#usize : Result Std.Usize) =
      .ok 1488#usize := by
    apply usize_result_mul_exact <;> scalar_tac
  have add_1488_7 : (1488#usize + 7#usize : Result Std.Usize) =
      .ok 1495#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have div_1495_8 : (1495#usize / 8#usize : Result Std.Usize) =
      .ok 186#usize := by
    apply usize_result_div_exact <;> scalar_tac
  simp [V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_C2_BYTES_PER_QUERY,
    V7MerkleCallerGenerated.v6_onefold.V6_C2_PACKED_BYTES_PER_QUERY,
    V7MerkleCallerGenerated.v6_onefold.V6_C2_LIMBS_PER_QUERY,
    V7MerkleCallerGenerated.v6_onefold.V6_C2_COLUMNS,
    V7MerkleCallerGenerated.v6_onefold.packed_bytes, mul_4_4, mul_16_3,
    mul_48_31, add_1488_7, div_1495_8]

private theorem caller_query_bytes_exact :
    V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_QUERY_BYTES =
      .ok 621#usize := by
  have add_403_186 : (403#usize + 186#usize : Result Std.Usize) =
      .ok 589#usize := by
    apply usize_result_add_exact <;> scalar_tac
  have add_589_32 : (589#usize + 32#usize : Result Std.Usize) =
      .ok 621#usize := by
    apply usize_result_add_exact <;> scalar_tac
  simp [V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_QUERY_BYTES,
    caller_c1_bytes_exact, caller_c2_bytes_exact,
    V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES,
    add_403_186, add_589_32]

private theorem range_index_success_length
    (data : Slice Std.U8) (start finish : Std.Usize) (out : Slice Std.U8)
    (success : core.slice.index.SliceIndexRangeUsizeSlice.index
      { start, «end» := finish } data = .ok out) :
    out.val.length = finish.val - start.val := by
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at success
  split at success
  · rename_i bounds
    simp only [Result.ok.injEq] at success
    subst out
    have specification :=
      core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
        { start, «end» := finish } data bounds.1 bounds.2
    simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,
      bounds.1, bounds.2, and_self, ↓reduceIte, Aeneas.Std.WP.spec_ok]
      at specification
    exact specification.2
  · simp at success

/- Successful production query access fixes both packed-value widths exactly.
The shared salt remains the single fixed array field of the returned record. -/
theorem caller_query_success_lengths
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (ordinal : Std.Usize)
    (record : V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord)
    (run : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query
      wire ordinal = .ok (some record)) :
    (AspisV7MerkleK12SourceBridge.generatedSliceBytes record.c1_packed).length =
        403 ∧
      (AspisV7MerkleK12SourceBridge.generatedSliceBytes record.c2_packed).length =
        186 := by
  unfold V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query at run
  by_cases ordinalOutside :
      ordinal ≥ V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT
  · change V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT.val ≤
      ordinal.val at ordinalOutside
    simp [ordinalOutside] at run
  · simp only [if_neg ordinalOutside, caller_query_bytes_exact,
      Aeneas.Std.bind_tc_ok] at run
    generalize startEquation : ordinal * 621#usize = startResult at run
    cases startResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
    | div => simp [Bind.bind, Aeneas.Std.bind] at run
    | ok start =>
      simp only [Aeneas.Std.bind_tc_ok, caller_c1_bytes_exact] at run
      generalize c1EndEquation : start + 403#usize = c1EndResult at run
      cases c1EndResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok c1End =>
        simp only [Aeneas.Std.bind_tc_ok, caller_c2_bytes_exact] at run
        generalize c2EndEquation : c1End + 186#usize = c2EndResult at run
        cases c2EndResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
        | div => simp [Bind.bind, Aeneas.Std.bind] at run
        | ok c2End =>
          simp only [Aeneas.Std.bind_tc_ok] at run
          generalize endEquation : c2End +
              V7MerkleCallerGenerated.v7_onefold.V7_COMPACT_PRIVATE_SALT_BYTES =
                endResult at run
          cases endResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
          | div => simp [Bind.bind, Aeneas.Std.bind] at run
          | ok finish =>
            simp only [Aeneas.Std.bind_tc_ok] at run
            generalize c1SliceEquation :
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                  wire.query_section { start, «end» := c1End } =
                    c1SliceResult at run
            cases c1SliceResult with
            | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
            | div => simp [Bind.bind, Aeneas.Std.bind] at run
            | ok c1Slice =>
              simp only [Aeneas.Std.bind_tc_ok] at run
              generalize c2SliceEquation :
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                    wire.query_section { start := c1End, «end» := c2End } =
                      c2SliceResult at run
              cases c2SliceResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
              | div => simp [Bind.bind, Aeneas.Std.bind] at run
              | ok c2Slice =>
                simp only [Aeneas.Std.bind_tc_ok] at run
                generalize saltSliceEquation :
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
                      wire.query_section { start := c2End, «end» := finish } =
                        saltSliceResult at run
                cases saltSliceResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                | div => simp [Bind.bind, Aeneas.Std.bind] at run
                | ok saltSlice =>
                  simp only [Aeneas.Std.bind_tc_ok] at run
                  generalize saltCopyEquation :
                      core.array.TryFromSharedArraySlice.try_from 32#usize
                        saltSlice = saltCopyResult at run
                  cases saltCopyResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
                  | div => simp [Bind.bind, Aeneas.Std.bind] at run
                  | ok saltCopyOutput =>
                    cases saltCopyOutput with
                    | Err error =>
                      simp [core.result.Result.ok,
                        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                        Bind.bind, Aeneas.Std.bind] at run
                    | Ok salt =>
                      simp [core.result.Result.ok,
                        core.option.Option.Insts.CoreOpsTry_traitTry.branch]
                        at run
                      subst record
                      have c1Length := range_index_success_length
                        wire.query_section start c1End c1Slice (by
                          change
                            core.slice.index.SliceIndexRangeUsizeSlice.index
                              { start, «end» := c1End } wire.query_section =
                                .ok c1Slice
                          exact c1SliceEquation)
                      have c2Length := range_index_success_length
                        wire.query_section c1End c2End c2Slice (by
                          change
                            core.slice.index.SliceIndexRangeUsizeSlice.index
                              { start := c1End, «end» := c2End }
                              wire.query_section = .ok c2Slice
                          exact c2SliceEquation)
                      have c1EndValue :=
                        AspisV7MerkleK12InnerTraceBridge.usize_add_success_val
                          start 403#usize c1End c1EndEquation
                      have c2EndValue :=
                        AspisV7MerkleK12InnerTraceBridge.usize_add_success_val
                          c1End 186#usize c2End c2EndEquation
                      simp only [
                        AspisV7MerkleK12SourceBridge.generatedSliceBytes,
                        List.length_map]
                      norm_num at c1Length c2Length c1EndValue c2EndValue ⊢
                      omega

/-- One successful translated caller iteration constructs exactly one paired
source seed.  The two distinct production leaf tags are normalized by
unfolding their extracted constants, and both calls use the single salt field
of the same translated query record. -/
def pairedSourceSeedOfCallerLeafRuns
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (ordinal : Std.Usize) (position : Std.U32)
    (record : V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord)
    (c1Leaf c2Leaf : Array Std.U8 26#usize)
    (positionBound : position.val <
      2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth)
    (queryRun :
      V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query wire
        ordinal = .ok (some record))
    (c1LeafRun :
      V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 hash
        V7MerkleCallerGenerated.v7_merkle208.V7_C1_TREE_TAG record.c1_packed
        record.salt = .ok c1Leaf)
    (c2LeafRun :
      V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 hash
        V7MerkleCallerGenerated.v7_merkle208.V7_C2_TREE_TAG record.c2_packed
        record.salt = .ok c2Leaf) :
    AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash := by
  have lengths := caller_query_success_lengths wire ordinal record queryRun
  have c1Standalone := c1LeafRun
  have c2Standalone := c2LeafRun
  rw [AspisV7MerkleCallerNamespaceBridge.caller_private_leaf_hash_v7_eq]
    at c1Standalone c2Standalone
  unfold V7MerkleCallerGenerated.v7_merkle208.V7_C1_TREE_TAG at c1Standalone
  unfold V7MerkleCallerGenerated.v7_merkle208.V7_C2_TREE_TAG at c2Standalone
  exact
    { position := position
      positionBound := positionBound
      c1Value := record.c1_packed
      c2Value := record.c2_packed
      salt := record.salt
      c1ValueLength := lengths.1
      c2ValueLength := lengths.2
      c1Leaf := c1Leaf
      c2Leaf := c2Leaf
      c1LeafRun := c1Standalone
      c2LeafRun := c2Standalone }

abbrev CallerIter :=
  core.array.iter.IntoIter (Std.U32 × Std.Usize) 16#usize

abbrev CallerCombined :=
  Array (Array V7MerkleCallerGenerated.field.QM31 4#usize) 16#usize

abbrev CallerEntries := AspisV7MerkleK12SourceBridge.GeneratedLevel

abbrev CallerLoopState := CallerIter × CallerCombined × CallerEntries

abbrev CallerLoopOutput :=
  Option (core.result.Result CallerCombined
    V7MerkleCallerGenerated.v6_onefold.V6WireError)

def exactCallerBody
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers) :
    CallerLoopState → Result (ControlFlow CallerLoopState CallerLoopOutput) :=
  fun state =>
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body
      wire hash powers state.1 state.2.1 state.2.2

theorem caller_loop_success_yields_exact_control_flow_trace
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined output : CallerCombined)
    (entries : CallerEntries)
    (run :
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop
        wire iter hash powers combined entries = .ok (some (.Ok output))) :
    Nonempty (AspisV7MerkleK12SourceBridge.ExactLoopTrace
      (exactCallerBody wire hash powers) (iter, combined, entries)
      (some (.Ok output))) := by
  unfold
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop
    at run
  exact AspisV7MerkleK12SourceBridge.loop_success_yields_exact_trace
    (exactCallerBody wire hash powers) (iter, combined, entries)
    (some (.Ok output)) run

/-! An accepting caller trace contains one literal query/leaf/push step for
each array iterator element, followed by the literal successful production
Merkle-verifier call.  It stores no authentication or accepted-predicate
premise. -/
inductive ExactAcceptedCallerTrace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers) :
    CallerIter → CallerCombined → CallerEntries → CallerCombined →
      List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash) → Type
  | done {iter iterAfter : CallerIter} {combined : CallerCombined}
      {entries outputLevel outputNext : CallerEntries}
      (iteratorRun :
        core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
          iter = .ok (none, iterAfter))
      (verifierRun :
        V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
          hash (wire.c1_root, wire.c2_root) 18#u32
          (alloc.vec.Vec.deref entries) (wire.c1_frontier, wire.c2_frontier)
          (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
            V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
          (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
            V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
            .ok (true, outputLevel, outputNext)) :
      ExactAcceptedCallerTrace hash wire powers iter combined entries combined
        []
  | step {iter iterAfter : CallerIter}
      {combined combinedAfter finalCombined : CallerCombined}
      {entries entriesAfter : CallerEntries}
      {seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash)}
      (position : Std.U32) (ordinal : Std.Usize)
      (record : V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord)
      (combinedValue : Array V7MerkleCallerGenerated.field.QM31 4#usize)
      (c1Leaf c2Leaf : Array Std.U8 26#usize)
      (positionBound : position.val <
        2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth)
      (iteratorRun :
        core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
          iter = .ok (some (position, ordinal), iterAfter))
      (queryRun :
        V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query wire
          ordinal = .ok (some record))
      (gammaRun :
        V7MerkleCallerGenerated.v6_onefold.gamma_combine_v6_packed_layer0
          record.c1_packed record.c2_packed powers = .ok (.Ok combinedValue))
      (combinedUpdateRun : Array.update combined ordinal combinedValue =
        .ok combinedAfter)
      (c1LeafRun :
        V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 hash
          V7MerkleCallerGenerated.v7_merkle208.V7_C1_TREE_TAG
          record.c1_packed record.salt = .ok c1Leaf)
      (c2LeafRun :
        V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 hash
          V7MerkleCallerGenerated.v7_merkle208.V7_C2_TREE_TAG
          record.c2_packed record.salt = .ok c2Leaf)
      (pushRun : alloc.vec.Vec.push entries (position, c1Leaf, c2Leaf) =
        .ok entriesAfter)
      (tail : ExactAcceptedCallerTrace hash wire powers iterAfter combinedAfter
        entriesAfter finalCombined seeds) :
      ExactAcceptedCallerTrace hash wire powers iter combined entries
        finalCombined
        (pairedSourceSeedOfCallerLeafRuns hash wire ordinal position record
          c1Leaf c2Leaf positionBound queryRun c1LeafRun c2LeafRun :: seeds)

/-- Every continuing edge of the translated caller body is forced to have
exactly the query/gamma/update/two-leaf-hash/push shape recorded by the
inductive accepted trace.  This is an inversion of the generated body, not a
semantic premise about the verifier. -/
structure ExactCallerContinueStep
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined : CallerCombined) (entries : CallerEntries)
    (outputIter : CallerIter) (outputCombined : CallerCombined)
    (outputEntries : CallerEntries) where
  position : Std.U32
  ordinal : Std.Usize
  record : V7MerkleCallerGenerated.v7_onefold.V7CompactQueryRecord
  combinedValue : Array V7MerkleCallerGenerated.field.QM31 4#usize
  c1Leaf : Array Std.U8 26#usize
  c2Leaf : Array Std.U8 26#usize
  iteratorRun :
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
      .ok (some (position, ordinal), outputIter)
  queryRun :
    V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query wire
      ordinal = .ok (some record)
  gammaRun :
    V7MerkleCallerGenerated.v6_onefold.gamma_combine_v6_packed_layer0
      record.c1_packed record.c2_packed powers = .ok (.Ok combinedValue)
  combinedUpdateRun : Array.update combined ordinal combinedValue =
    .ok outputCombined
  c1LeafRun :
    V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 hash
      V7MerkleCallerGenerated.v7_merkle208.V7_C1_TREE_TAG
      record.c1_packed record.salt = .ok c1Leaf
  c2LeafRun :
    V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7 hash
      V7MerkleCallerGenerated.v7_merkle208.V7_C2_TREE_TAG
      record.c2_packed record.salt = .ok c2Leaf
  pushRun : alloc.vec.Vec.push entries (position, c1Leaf, c2Leaf) =
    .ok outputEntries

theorem exact_caller_body_cont_yields_step
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter outputIter : CallerIter)
    (combined outputCombined : CallerCombined)
    (entries outputEntries : CallerEntries)
    (bodyRun : exactCallerBody wire hash powers (iter, combined, entries) =
      .ok (.cont (outputIter, outputCombined, outputEntries))) :
    Nonempty (ExactCallerContinueStep hash wire powers iter combined entries
      outputIter outputCombined outputEntries) := by
  unfold exactCallerBody at bodyRun
  unfold
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body
    at bodyRun
  generalize iteratorEquation :
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
        iteratorResult at bodyRun
  cases iteratorResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok iteratorOutput =>
      rcases iteratorOutput with ⟨item, iterAfter⟩
      simp only [Aeneas.Std.bind_tc_ok] at bodyRun
      cases item with
      | none =>
          generalize verifierEquation :
              V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
                hash (wire.c1_root, wire.c2_root) 18#u32
                (alloc.vec.Vec.deref entries)
                (wire.c1_frontier, wire.c2_frontier)
                (alloc.vec.Vec.with_capacity
                  AspisV7MerkleK12SourceBridge.GeneratedEntry
                  V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
                (alloc.vec.Vec.with_capacity
                  AspisV7MerkleK12SourceBridge.GeneratedEntry
                  V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
                  verifierResult at bodyRun
          cases verifierResult with
          | fail error =>
              simp [verifierEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [verifierEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok verifierOutput =>
              rcases verifierOutput with ⟨accepted, outputLevel, outputNext⟩
              cases accepted <;>
                simp [verifierEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
      | some item =>
          rcases item with ⟨position, ordinal⟩
          generalize queryEquation :
              V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query
                wire ordinal = queryResult at bodyRun
          cases queryResult with
          | fail error =>
              simp [queryEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [queryEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok queryOutput =>
              cases queryOutput with
              | none =>
                  simp [queryEquation, core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    Bind.bind, Aeneas.Std.bind] at bodyRun
              | some record =>
                  simp only [queryEquation, core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    Aeneas.Std.bind_tc_ok] at bodyRun
                  generalize gammaEquation :
                      V7MerkleCallerGenerated.v6_onefold.gamma_combine_v6_packed_layer0
                        record.c1_packed record.c2_packed powers = gammaResult
                    at bodyRun
                  cases gammaResult with
                  | fail error =>
                      simp [queryEquation, gammaEquation, Bind.bind,
                        Aeneas.Std.bind] at bodyRun
                  | div =>
                      simp [queryEquation, gammaEquation, Bind.bind,
                        Aeneas.Std.bind] at bodyRun
                  | ok gammaOutput =>
                      cases gammaOutput with
                      | Err error =>
                          simp [queryEquation, gammaEquation,
                            Bind.bind, Aeneas.Std.bind] at bodyRun
                      | Ok combinedValue =>
                          simp [queryEquation, gammaEquation, Bind.bind,
                            Aeneas.Std.bind] at bodyRun
                          generalize updateEquation :
                              Array.update combined ordinal combinedValue =
                                updateResult at bodyRun
                          cases updateResult with
                          | fail error =>
                              simp [queryEquation, gammaEquation,
                                updateEquation, Bind.bind, Aeneas.Std.bind]
                                at bodyRun
                          | div =>
                              simp [queryEquation, gammaEquation,
                                updateEquation, Bind.bind, Aeneas.Std.bind]
                                at bodyRun
                          | ok combinedAfter =>
                              simp [queryEquation, gammaEquation,
                                updateEquation, Bind.bind, Aeneas.Std.bind]
                                at bodyRun
                              generalize c1LeafEquation :
                                  V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7
                                    hash
                                    V7MerkleCallerGenerated.v7_merkle208.V7_C1_TREE_TAG
                                    record.c1_packed record.salt = c1LeafResult
                                at bodyRun
                              cases c1LeafResult with
                              | fail error =>
                                  simp [queryEquation, gammaEquation,
                                    updateEquation, c1LeafEquation, Bind.bind,
                                    Aeneas.Std.bind] at bodyRun
                              | div =>
                                  simp [queryEquation, gammaEquation,
                                    updateEquation, c1LeafEquation, Bind.bind,
                                    Aeneas.Std.bind] at bodyRun
                              | ok c1Leaf =>
                                  simp [queryEquation, gammaEquation,
                                    updateEquation, c1LeafEquation, Bind.bind,
                                    Aeneas.Std.bind] at bodyRun
                                  generalize c2LeafEquation :
                                      V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7
                                        hash
                                        V7MerkleCallerGenerated.v7_merkle208.V7_C2_TREE_TAG
                                        record.c2_packed record.salt =
                                          c2LeafResult at bodyRun
                                  cases c2LeafResult with
                                  | fail error =>
                                      simp [queryEquation, gammaEquation,
                                        updateEquation, c1LeafEquation,
                                        c2LeafEquation, Bind.bind,
                                        Aeneas.Std.bind] at bodyRun
                                  | div =>
                                      simp [queryEquation, gammaEquation,
                                        updateEquation, c1LeafEquation,
                                        c2LeafEquation, Bind.bind,
                                        Aeneas.Std.bind] at bodyRun
                                  | ok c2Leaf =>
                                      simp [queryEquation, gammaEquation,
                                        updateEquation, c1LeafEquation,
                                        c2LeafEquation, Bind.bind,
                                        Aeneas.Std.bind] at bodyRun
                                      generalize pushEquation :
                                          alloc.vec.Vec.push entries
                                            (position, c1Leaf, c2Leaf) =
                                              pushResult at bodyRun
                                      cases pushResult with
                                      | fail error =>
                                          simp [queryEquation, gammaEquation,
                                            updateEquation, c1LeafEquation,
                                            c2LeafEquation, pushEquation,
                                            Bind.bind, Aeneas.Std.bind]
                                            at bodyRun
                                      | div =>
                                          simp [queryEquation, gammaEquation,
                                            updateEquation, c1LeafEquation,
                                            c2LeafEquation, pushEquation,
                                            Bind.bind, Aeneas.Std.bind]
                                            at bodyRun
                                      | ok entriesAfter =>
                                          simp [queryEquation, gammaEquation,
                                            updateEquation, c1LeafEquation,
                                            c2LeafEquation, pushEquation,
                                            Bind.bind, Aeneas.Std.bind]
                                            at bodyRun
                                          rcases bodyRun with ⟨rfl, rfl, rfl⟩
                                          exact ⟨{
                                            position := position
                                            ordinal := ordinal
                                            record := record
                                            combinedValue := combinedValue
                                            c1Leaf := c1Leaf
                                            c2Leaf := c2Leaf
                                            iteratorRun := iteratorEquation
                                            queryRun := queryEquation
                                            gammaRun := gammaEquation
                                            combinedUpdateRun := updateEquation
                                            c1LeafRun := c1LeafEquation
                                            c2LeafRun := c2LeafEquation
                                            pushRun := pushEquation }⟩

/-- An accepting terminal body edge can only be the exhausted-array branch,
and that branch exposes the literal successful Merkle verifier call. -/
theorem exact_caller_body_accept_done_yields_terminal
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined output : CallerCombined)
    (entries : CallerEntries)
    (bodyRun : exactCallerBody wire hash powers (iter, combined, entries) =
      .ok (.done (some (.Ok output)))) :
    combined = output ∧
      ∃ iterAfter outputLevel outputNext,
        core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
            iter = .ok (none, iterAfter) ∧
          V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
            hash (wire.c1_root, wire.c2_root) 18#u32
            (alloc.vec.Vec.deref entries)
            (wire.c1_frontier, wire.c2_frontier)
            (alloc.vec.Vec.with_capacity
              AspisV7MerkleK12SourceBridge.GeneratedEntry
              V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
            (alloc.vec.Vec.with_capacity
              AspisV7MerkleK12SourceBridge.GeneratedEntry
              V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
              .ok (true, outputLevel, outputNext) := by
  unfold exactCallerBody at bodyRun
  unfold
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop.body
    at bodyRun
  generalize iteratorEquation :
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
        iteratorResult at bodyRun
  cases iteratorResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | div => simp [Bind.bind, Aeneas.Std.bind] at bodyRun
  | ok iteratorOutput =>
      rcases iteratorOutput with ⟨item, iterAfter⟩
      simp only [Aeneas.Std.bind_tc_ok] at bodyRun
      cases item with
      | none =>
          generalize verifierEquation :
              V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
                hash (wire.c1_root, wire.c2_root) 18#u32
                (alloc.vec.Vec.deref entries)
                (wire.c1_frontier, wire.c2_frontier)
                (alloc.vec.Vec.with_capacity
                  AspisV7MerkleK12SourceBridge.GeneratedEntry
                  V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
                (alloc.vec.Vec.with_capacity
                  AspisV7MerkleK12SourceBridge.GeneratedEntry
                  V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
                  verifierResult at bodyRun
          cases verifierResult with
          | fail error =>
              simp [verifierEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [verifierEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok verifierOutput =>
              simp only [verifierEquation, Aeneas.Std.bind_tc_ok] at bodyRun
              rcases verifierOutput with ⟨accepted, outputLevel, outputNext⟩
              cases accepted <;> simp at bodyRun
              exact ⟨bodyRun, iterAfter, outputLevel, outputNext, rfl, rfl⟩
      | some item =>
          rcases item with ⟨position, ordinal⟩
          generalize queryEquation :
              V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire.query
                wire ordinal = queryResult at bodyRun
          cases queryResult with
          | fail error =>
              simp [queryEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | div =>
              simp [queryEquation, Bind.bind, Aeneas.Std.bind] at bodyRun
          | ok queryOutput =>
              cases queryOutput with
              | none =>
                  simp [queryEquation, core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    Bind.bind, Aeneas.Std.bind] at bodyRun
              | some record =>
                  simp only [queryEquation, core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    Aeneas.Std.bind_tc_ok] at bodyRun
                  generalize gammaEquation :
                      V7MerkleCallerGenerated.v6_onefold.gamma_combine_v6_packed_layer0
                        record.c1_packed record.c2_packed powers = gammaResult
                    at bodyRun
                  cases gammaResult with
                  | fail error =>
                      simp [queryEquation, gammaEquation, Bind.bind,
                        Aeneas.Std.bind] at bodyRun
                  | div =>
                      simp [queryEquation, gammaEquation, Bind.bind,
                        Aeneas.Std.bind] at bodyRun
                  | ok gammaOutput =>
                      cases gammaOutput with
                      | Err error =>
                          simp [queryEquation, gammaEquation,
                            Bind.bind, Aeneas.Std.bind] at bodyRun
                      | Ok combinedValue =>
                          simp [queryEquation, gammaEquation, Bind.bind,
                            Aeneas.Std.bind] at bodyRun
                          generalize updateEquation :
                              Array.update combined ordinal combinedValue =
                                updateResult at bodyRun
                          cases updateResult with
                          | fail error =>
                              simp [queryEquation, gammaEquation,
                                updateEquation, Bind.bind, Aeneas.Std.bind]
                                at bodyRun
                          | div =>
                              simp [queryEquation, gammaEquation,
                                updateEquation, Bind.bind, Aeneas.Std.bind]
                                at bodyRun
                          | ok combinedAfter =>
                              simp [queryEquation, gammaEquation,
                                updateEquation, Bind.bind, Aeneas.Std.bind]
                                at bodyRun
                              generalize c1LeafEquation :
                                  V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7
                                    hash
                                    V7MerkleCallerGenerated.v7_merkle208.V7_C1_TREE_TAG
                                    record.c1_packed record.salt = c1LeafResult
                                at bodyRun
                              cases c1LeafResult with
                              | fail error =>
                                  simp [queryEquation, gammaEquation,
                                    updateEquation, c1LeafEquation, Bind.bind,
                                    Aeneas.Std.bind] at bodyRun
                              | div =>
                                  simp [queryEquation, gammaEquation,
                                    updateEquation, c1LeafEquation, Bind.bind,
                                    Aeneas.Std.bind] at bodyRun
                              | ok c1Leaf =>
                                  simp [queryEquation, gammaEquation,
                                    updateEquation, c1LeafEquation, Bind.bind,
                                    Aeneas.Std.bind] at bodyRun
                                  generalize c2LeafEquation :
                                      V7MerkleCallerGenerated.v7_merkle208.private_leaf_hash_v7
                                        hash
                                        V7MerkleCallerGenerated.v7_merkle208.V7_C2_TREE_TAG
                                        record.c2_packed record.salt =
                                          c2LeafResult at bodyRun
                                  cases c2LeafResult with
                                  | fail error =>
                                      simp [queryEquation, gammaEquation,
                                        updateEquation, c1LeafEquation,
                                        c2LeafEquation, Bind.bind,
                                        Aeneas.Std.bind] at bodyRun
                                  | div =>
                                      simp [queryEquation, gammaEquation,
                                        updateEquation, c1LeafEquation,
                                        c2LeafEquation, Bind.bind,
                                        Aeneas.Std.bind] at bodyRun
                                  | ok c2Leaf =>
                                      simp [queryEquation, gammaEquation,
                                        updateEquation, c1LeafEquation,
                                        c2LeafEquation, Bind.bind,
                                        Aeneas.Std.bind] at bodyRun
                                      generalize pushEquation :
                                          alloc.vec.Vec.push entries
                                            (position, c1Leaf, c2Leaf) =
                                              pushResult at bodyRun
                                      cases pushResult <;>
                                        simp [queryEquation, gammaEquation,
                                          updateEquation, c1LeafEquation,
                                          c2LeafEquation, pushEquation,
                                          Bind.bind, Aeneas.Std.bind]
                                          at bodyRun

private theorem caller_iter_array_length (iter : CallerIter) :
    iter.array.val.length = 16 := by
  exact iter.array.length_eq

private theorem caller_iterator_next_some_facts
    (iter iterAfter : CallerIter) (position : Std.U32) (ordinal : Std.Usize)
    (run :
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
        .ok (some (position, ordinal), iterAfter)) :
    iter.index < 16 ∧
      (position, ordinal) = iter.array.val[iter.index]! ∧
      iterAfter.array = iter.array ∧ iterAfter.index = iter.index + 1 := by
  unfold core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    at run
  split at run
  · rename_i active
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
    rcases run with ⟨itemExact, iteratorExact⟩
    subst iterAfter
    have itemBang : (position, ordinal) =
        iter.array.val[iter.index]! :=
      itemExact.symm.trans
        (List.Inhabited_getElem_eq_getElem! iter.array.val iter.index active)
    exact ⟨by simpa [caller_iter_array_length] using active,
      itemBang, rfl, rfl⟩
  · simp at run

private theorem caller_iterator_next_none_exhausted
    (iter iterAfter : CallerIter)
    (run :
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
        .ok (none, iterAfter)) :
    16 ≤ iter.index ∧ iterAfter = iter := by
  unfold core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    at run
  split at run
  · simp at run
  · rename_i exhausted
    simp only [Result.ok.injEq, Prod.mk.injEq, true_and]
      at run
    exact ⟨by simpa [caller_iter_array_length] using exhausted, run.symm⟩

def CallerArrayPositionBound (iter : CallerIter) : Prop :=
  ∀ index, index < iter.array.val.length →
    (iter.array.val[index]!).1.val <
      2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth

abbrev CallerScheduleItem := Std.U32 × Std.Usize

def callerInitialCombined : CallerCombined :=
  Array.repeat 16#usize (Array.repeat 4#usize
    V7MerkleCallerGenerated.field.QM31.ZERO)

def callerInitialEntries : CallerEntries :=
  alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
    V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT

/-- All intermediate values on the accepting branch of the transparent
production wrapper.  Its fields are literal extracted calls and branch facts;
there is no schedule, traversal, root, or accepted-predicate assumption. -/
structure ExactCallerWrapperControlFlow
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (queries : Array Std.U32 16#usize)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : CallerCombined) where
  unsorted : Array CallerScheduleItem 16#usize
  mutableSlice : Slice CallerScheduleItem
  writeBack : Slice CallerScheduleItem → Array CallerScheduleItem 16#usize
  sortedSlice : Slice CallerScheduleItem
  order : Array CallerScheduleItem 16#usize
  lastIndex : Std.Usize
  lastPosition : Std.U32
  lastOrdinal : Std.Usize
  limit : Std.U32
  sharedSlice : Slice CallerScheduleItem
  windows : core.slice.iter.Windows CallerScheduleItem
  windowsAfterDuplicateCheck : core.slice.iter.Windows CallerScheduleItem
  iterator : CallerIter
  fromFnRun :
    core.array.from_fn 16#usize
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize
      queries = .ok unsorted
  mutableSliceRun : lift (Array.to_slice_mut unsorted) =
    .ok (mutableSlice, writeBack)
  sortRun : core.slice.Slice.sort_unstable_by_key
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
    core.cmp.OrdU32 mutableSlice () = .ok sortedSlice
  orderExact : order = writeBack sortedSlice
  lastIndexRun :
    V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT - 1#usize =
      (.ok lastIndex : Result Std.Usize)
  lastRun : Array.index_usize order lastIndex =
    .ok (lastPosition, lastOrdinal)
  limitRun : 1#u32 <<< 18#i32 = .ok limit
  lastBoundGuard : ¬ lastPosition ≥ limit
  sharedSliceRun : lift (Array.to_slice order) = .ok sharedSlice
  windowsRun : core.slice.Slice.windows sharedSlice 2#usize = .ok windows
  duplicateGuardRun :
    core.iter.traits.iterator.Iterator.any.default
      (V7MerkleCallerGenerated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
        CallerScheduleItem)
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool
      windows () = .ok (false, windowsAfterDuplicateCheck)
  iteratorRun :
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter order =
      .ok iterator
  callerLoopRun :
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop
      wire iterator hash powers callerInitialCombined callerInitialEntries =
        .ok (some (.Ok output))

/-- Literal inversion of an accepting translated production caller. -/
theorem translated_caller_success_yields_exact_wrapper_control_flow
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (queries : Array Std.U32 16#usize)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : CallerCombined)
    (run :
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
        hash wire queries powers = .ok (.Ok output)) :
    Nonempty (ExactCallerWrapperControlFlow hash wire queries powers output) := by
  unfold
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
    at run
  generalize fromFnEquation :
      core.array.from_fn 16#usize
        V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure.Insts.CoreOpsFunctionFnMutTupleUsizePairU32Usize
        queries = fromFnResult at run
  cases fromFnResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok unsorted =>
      simp only [Aeneas.Std.bind_tc_ok] at run
      generalize mutableSliceEquation : lift (Array.to_slice_mut unsorted) =
        mutableSliceResult at run
      cases mutableSliceResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
      | div => simp [Bind.bind, Aeneas.Std.bind] at run
      | ok mutableSliceOutput =>
          rcases mutableSliceOutput with ⟨mutableSlice, writeBack⟩
          simp only [Aeneas.Std.bind_tc_ok] at run
          generalize sortEquation :
              core.slice.Slice.sort_unstable_by_key
                V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
                core.cmp.OrdU32 mutableSlice () = sortResult at run
          cases sortResult with
          | fail error =>
              simp [sortEquation, Bind.bind, Aeneas.Std.bind] at run
          | div =>
              simp [sortEquation, Bind.bind, Aeneas.Std.bind] at run
          | ok sortedSlice =>
              let order := writeBack sortedSlice
              generalize lastIndexEquation :
                  V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT -
                    1#usize = lastIndexResult at run
              cases lastIndexResult with
              | fail error =>
                  simp [sortEquation, lastIndexEquation, Bind.bind,
                    Aeneas.Std.bind] at run
              | div =>
                  simp [sortEquation, lastIndexEquation, Bind.bind,
                    Aeneas.Std.bind] at run
              | ok lastIndex =>
                  simp [sortEquation, lastIndexEquation, Bind.bind,
                    Aeneas.Std.bind] at run
                  generalize lastEquation : Array.index_usize order lastIndex =
                    lastResult at run
                  cases lastResult with
                  | fail error =>
                      simp [sortEquation, lastIndexEquation, lastEquation,
                        Bind.bind, Aeneas.Std.bind] at run
                  | div =>
                      simp [sortEquation, lastIndexEquation, lastEquation,
                        Bind.bind, Aeneas.Std.bind] at run
                  | ok lastOutput =>
                      rcases lastOutput with ⟨lastPosition, lastOrdinal⟩
                      simp [sortEquation, lastIndexEquation, lastEquation,
                        Bind.bind, Aeneas.Std.bind] at run
                      generalize limitEquation : 1#u32 <<< 18#i32 =
                        limitResult at run
                      cases limitResult with
                      | fail error =>
                          simp [sortEquation, lastIndexEquation, lastEquation,
                            limitEquation, Bind.bind, Aeneas.Std.bind] at run
                      | div =>
                          simp [sortEquation, lastIndexEquation, lastEquation,
                            limitEquation, Bind.bind, Aeneas.Std.bind] at run
                      | ok limit =>
                          simp [sortEquation, lastIndexEquation, lastEquation,
                            limitEquation, Bind.bind, Aeneas.Std.bind] at run
                          by_cases lastTooLarge : lastPosition ≥ limit
                          · have lastTooLargeVal : limit.val ≤
                                lastPosition.val := by simpa using lastTooLarge
                            simp [lastTooLargeVal] at run
                          · have lastNotTooLargeVal : ¬ limit.val ≤
                                lastPosition.val := by simpa using lastTooLarge
                            simp only [if_neg lastNotTooLargeVal] at run
                            generalize sharedSliceEquation :
                                lift (Array.to_slice order) = sharedSliceResult
                              at run
                            cases sharedSliceResult with
                            | fail error =>
                                simp [sortEquation, lastIndexEquation,
                                  lastEquation, limitEquation,
                                  sharedSliceEquation, Bind.bind,
                                  Aeneas.Std.bind] at run
                            | div =>
                                simp [sortEquation, lastIndexEquation,
                                  lastEquation, limitEquation,
                                  sharedSliceEquation, Bind.bind,
                                  Aeneas.Std.bind] at run
                            | ok sharedSlice =>
                                simp [sortEquation, lastIndexEquation,
                                  lastEquation, limitEquation,
                                  sharedSliceEquation, Bind.bind,
                                  Aeneas.Std.bind] at run
                                generalize windowsEquation :
                                    core.slice.Slice.windows sharedSlice
                                      2#usize = windowsResult at run
                                cases windowsResult with
                                | fail error =>
                                    simp [sortEquation, lastIndexEquation,
                                      lastEquation, limitEquation,
                                      sharedSliceEquation, windowsEquation,
                                      Bind.bind, Aeneas.Std.bind] at run
                                | div =>
                                    simp [sortEquation, lastIndexEquation,
                                      lastEquation, limitEquation,
                                      sharedSliceEquation, windowsEquation,
                                      Bind.bind, Aeneas.Std.bind] at run
                                | ok windows =>
                                    simp [sortEquation, lastIndexEquation,
                                      lastEquation, limitEquation,
                                      sharedSliceEquation, windowsEquation,
                                      Bind.bind, Aeneas.Std.bind] at run
                                    generalize duplicateEquation :
                                        core.iter.traits.iterator.Iterator.any.default
                                          (V7MerkleCallerGenerated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
                                            CallerScheduleItem)
                                          V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool
                                          windows () = duplicateResult at run
                                    cases duplicateResult with
                                    | fail error =>
                                        simp [sortEquation, lastIndexEquation,
                                          lastEquation, limitEquation,
                                          sharedSliceEquation, windowsEquation,
                                          duplicateEquation, Bind.bind,
                                          Aeneas.Std.bind] at run
                                    | div =>
                                        simp [sortEquation, lastIndexEquation,
                                          lastEquation, limitEquation,
                                          sharedSliceEquation, windowsEquation,
                                          duplicateEquation, Bind.bind,
                                          Aeneas.Std.bind] at run
                                    | ok duplicateOutput =>
                                        rcases duplicateOutput with
                                          ⟨hasDuplicate, duplicateClosure⟩
                                        simp [sortEquation, lastIndexEquation,
                                          lastEquation, limitEquation,
                                          sharedSliceEquation, windowsEquation,
                                          duplicateEquation, Bind.bind,
                                          Aeneas.Std.bind] at run
                                        cases hasDuplicate with
                                        | true => simp at run
                                        | false =>
                                            generalize iteratorEquation :
                                                Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
                                                  order = iteratorResult at run
                                            cases iteratorResult with
                                            | fail error =>
                                                simp [sortEquation,
                                                  lastIndexEquation,
                                                  lastEquation, limitEquation,
                                                  sharedSliceEquation,
                                                  windowsEquation,
                                                  duplicateEquation,
                                                  iteratorEquation, Bind.bind,
                                                  Aeneas.Std.bind] at run
                                            | div =>
                                                simp [sortEquation,
                                                  lastIndexEquation,
                                                  lastEquation, limitEquation,
                                                  sharedSliceEquation,
                                                  windowsEquation,
                                                  duplicateEquation,
                                                  iteratorEquation, Bind.bind,
                                                  Aeneas.Std.bind] at run
                                            | ok iterator =>
                                                simp [sortEquation,
                                                  lastIndexEquation,
                                                  lastEquation, limitEquation,
                                                  sharedSliceEquation,
                                                  windowsEquation,
                                                  duplicateEquation,
                                                  iteratorEquation, Bind.bind,
                                                  Aeneas.Std.bind] at run
                                                generalize loopEquation :
                                                    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings_loop
                                                      wire iterator hash powers
                                                      (Array.repeat 16#usize
                                                        (Array.repeat 4#usize
                                                          V7MerkleCallerGenerated.field.QM31.ZERO))
                                                      (alloc.vec.Vec.with_capacity
                                                        (Std.U32 ×
                                                          Array Std.U8 26#usize ×
                                                          Array Std.U8 26#usize)
                                                        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
                                                        loopResult at run
                                                cases loopResult with
                                                | fail error =>
                                                    cases run
                                                | div =>
                                                    cases run
                                                | ok loopOutput =>
                                                    cases loopOutput with
                                                    | none => simp at run
                                                    | some callerOutput =>
                                                        cases callerOutput with
                                                        | Err error =>
                                                            simp at run
                                                        | Ok actualOutput =>
                                                            have outputExact :
                                                                actualOutput =
                                                                  output := by
                                                              simpa using
                                                                Result.ok.inj run
                                                            subst actualOutput
                                                            exact ⟨{
                                                              unsorted := unsorted
                                                              mutableSlice :=
                                                                mutableSlice
                                                              writeBack := writeBack
                                                              sortedSlice := sortedSlice
                                                              order := order
                                                              lastIndex := lastIndex
                                                              lastPosition :=
                                                                lastPosition
                                                              lastOrdinal :=
                                                                lastOrdinal
                                                              limit := limit
                                                              sharedSlice :=
                                                                sharedSlice
                                                              windows := windows
                                                              windowsAfterDuplicateCheck :=
                                                                duplicateClosure
                                                              iterator := iterator
                                                              fromFnRun :=
                                                                fromFnEquation
                                                              mutableSliceRun :=
                                                                mutableSliceEquation
                                                              sortRun := sortEquation
                                                              orderExact := rfl
                                                              lastIndexRun :=
                                                                lastIndexEquation
                                                              lastRun := by
                                                                exact lastEquation
                                                              limitRun :=
                                                                limitEquation
                                                              lastBoundGuard :=
                                                                lastTooLarge
                                                              sharedSliceRun :=
                                                                sharedSliceEquation
                                                              windowsRun :=
                                                                windowsEquation
                                                              duplicateGuardRun := by
                                                                simpa using
                                                                  duplicateEquation
                                                              iteratorRun :=
                                                                iteratorEquation
                                                              callerLoopRun :=
                                                                loopEquation }⟩

private def positionLE (left right : CallerScheduleItem) : Prop :=
  left.1.val ≤ right.1.val

private theorem caller_sort_key_call (closure : Unit)
    (item : CallerScheduleItem) :
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32.call_mut
      closure item = .ok (item.1, closure) := by
  cases closure
  rfl

private theorem caller_u32_compare (left right : Std.U32) :
    core.cmp.OrdU32.cmp left right = .ok (compare left.val right.val) := by
  rfl

/-- The executable insertion used by the extracted `sort_unstable_by_key`
preserves all elements and preserves nondecreasing production position keys. -/
private theorem caller_insert_by_key_sorted
    (value : CallerScheduleItem) (input output : List CallerScheduleItem)
    (sorted : input.Pairwise positionLE)
    (run : V7MerkleCallerExternal.insertByKey
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
      core.cmp.OrdU32 value input () = .ok (output, ())) :
    List.Perm (value :: input) output ∧ output.Pairwise positionLE := by
  induction input generalizing output with
  | nil =>
      simp [V7MerkleCallerExternal.insertByKey] at run
      subst output
      simp
  | cons head tail inductionHypothesis =>
      have sortedParts := List.pairwise_cons.mp sorted
      have reducedRun := run
      simp only [V7MerkleCallerExternal.insertByKey] at reducedRun
      simp only [caller_sort_key_call, Aeneas.Std.bind_tc_ok,
        core.cmp.impls.OrdU32.cmp] at reducedRun
      cases comparison : compare value.1.val head.1.val with
      | lt =>
          have outputExact : output = value :: head :: tail := by
            simpa [comparison] using reducedRun.symm
          subst output
          have valueLtHead : value.1.val < head.1.val :=
            Nat.compare_eq_lt.mp comparison
          constructor
          · exact List.Perm.refl _
          · apply List.pairwise_cons.mpr
            constructor
            · intro item itemIn
              simp only [List.mem_cons] at itemIn
              rcases itemIn with rfl | itemIn
              · exact Nat.le_of_lt valueLtHead
              · exact Nat.le_trans (Nat.le_of_lt valueLtHead)
                  (sortedParts.1 item itemIn)
            · exact sorted
      | eq =>
          generalize recursiveEquation :
              V7MerkleCallerExternal.insertByKey
                V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
                core.cmp.OrdU32 value tail () = recursiveResult
            at reducedRun
          cases recursiveResult with
          | fail error =>
              simp [comparison, recursiveEquation, Bind.bind,
                Aeneas.Std.bind] at reducedRun
          | div =>
              simp [comparison, recursiveEquation, Bind.bind,
                Aeneas.Std.bind] at reducedRun
          | ok recursiveOutput =>
              rcases recursiveOutput with ⟨inserted, closure⟩
              have closureExact : closure = () := Subsingleton.elim _ _
              subst closure
              simp [comparison, recursiveEquation, Bind.bind,
                Aeneas.Std.bind] at reducedRun
              have outputExact : output = head :: inserted := by
                exact reducedRun.symm
              subst output
              have recursive := inductionHypothesis inserted sortedParts.2
                recursiveEquation
              have valueEqHead : value.1.val = head.1.val :=
                Nat.compare_eq_eq.mp comparison
              constructor
              · exact (List.Perm.swap head value tail).trans
                  (List.Perm.cons head recursive.1)
              · apply List.pairwise_cons.mpr
                constructor
                · intro item itemIn
                  have originalIn : item = value ∨ item ∈ tail := by
                    have := (recursive.1.mem_iff).mpr itemIn
                    simpa only [List.mem_cons] using this
                  rcases originalIn with rfl | itemIn
                  · exact Nat.le_of_eq valueEqHead.symm
                  · exact sortedParts.1 item itemIn
                · exact recursive.2
      | gt =>
          generalize recursiveEquation :
              V7MerkleCallerExternal.insertByKey
                V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
                core.cmp.OrdU32 value tail () = recursiveResult
            at reducedRun
          cases recursiveResult with
          | fail error =>
              simp [comparison, recursiveEquation, Bind.bind,
                Aeneas.Std.bind] at reducedRun
          | div =>
              simp [comparison, recursiveEquation, Bind.bind,
                Aeneas.Std.bind] at reducedRun
          | ok recursiveOutput =>
              rcases recursiveOutput with ⟨inserted, closure⟩
              have closureExact : closure = () := Subsingleton.elim _ _
              subst closure
              simp [comparison, recursiveEquation, Bind.bind,
                Aeneas.Std.bind] at reducedRun
              have outputExact : output = head :: inserted := by
                exact reducedRun.symm
              subst output
              have recursive := inductionHypothesis inserted sortedParts.2
                recursiveEquation
              have headLtValue : head.1.val < value.1.val :=
                Nat.compare_eq_gt.mp comparison
              constructor
              · exact (List.Perm.swap head value tail).trans
                  (List.Perm.cons head recursive.1)
              · apply List.pairwise_cons.mpr
                constructor
                · intro item itemIn
                  have originalIn : item = value ∨ item ∈ tail := by
                    have := (recursive.1.mem_iff).mpr itemIn
                    simpa only [List.mem_cons] using this
                  rcases originalIn with rfl | itemIn
                  · exact Nat.le_of_lt headLtValue
                  · exact sortedParts.1 item itemIn
                · exact recursive.2

/-- Transparent recursion over the extracted insertion-sort implementation. -/
private theorem caller_sort_list_by_key_sorted
    (input output : List CallerScheduleItem)
    (run : V7MerkleCallerExternal.sortListByKey
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
      core.cmp.OrdU32 input () = .ok (output, ())) :
    List.Perm input output ∧ output.Pairwise positionLE := by
  induction input generalizing output with
  | nil =>
      simp [V7MerkleCallerExternal.sortListByKey] at run
      subst output
      simp
  | cons head tail inductionHypothesis =>
      unfold V7MerkleCallerExternal.sortListByKey at run
      generalize tailEquation :
          V7MerkleCallerExternal.sortListByKey
            V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
            core.cmp.OrdU32 tail () = tailResult at run
      cases tailResult with
      | fail error =>
          simp [tailEquation, Bind.bind, Aeneas.Std.bind] at run
      | div =>
          simp [tailEquation, Bind.bind, Aeneas.Std.bind] at run
      | ok tailOutput =>
          rcases tailOutput with ⟨sortedTail, closure⟩
          have closureExact : closure = () := Subsingleton.elim _ _
          subst closure
          simp only [tailEquation, Aeneas.Std.bind_tc_ok] at run
          have tailEvidence := inductionHypothesis sortedTail tailEquation
          have insertEvidence := caller_insert_by_key_sorted head sortedTail
            output tailEvidence.2 run
          exact ⟨(List.Perm.cons head tailEvidence.1).trans insertEvidence.1,
            insertEvidence.2⟩

theorem ExactCallerWrapperControlFlow.order_sorted
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    flow.order.val.Pairwise positionLE := by
  have sortRun := flow.sortRun
  unfold core.slice.Slice.sort_unstable_by_key at sortRun
  generalize sortListEquation :
      V7MerkleCallerExternal.sortListByKey
        V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedPairU32UsizeU32
        core.cmp.OrdU32 flow.mutableSlice.val () = sortListResult
    at sortRun
  cases sortListResult with
  | fail error =>
      simp [sortListEquation, Bind.bind, Aeneas.Std.bind] at sortRun
  | div =>
      simp [sortListEquation, Bind.bind, Aeneas.Std.bind] at sortRun
  | ok sortListOutput =>
      rcases sortListOutput with ⟨sortedValues, closure⟩
      have closureExact : closure = () := Subsingleton.elim _ _
      subst closure
      simp only [sortListEquation, Aeneas.Std.bind_tc_ok] at sortRun
      change (if h : sortedValues.length ≤ Std.Usize.max then
          (.ok (⟨sortedValues, h⟩ : Slice CallerScheduleItem) :
            Result (Slice CallerScheduleItem))
        else .fail Error.panic) = .ok flow.sortedSlice at sortRun
      split at sortRun
      · have sliceExact : flow.sortedSlice.val = sortedValues := by
          simpa using (congrArg
            (fun slice : Slice CallerScheduleItem => slice.val)
            (Result.ok.inj sortRun)).symm
        have mutableExact := Result.ok.inj flow.mutableSliceRun
        have mutableValues : flow.mutableSlice.val = flow.unsorted.val := by
          simpa [lift, Array.to_slice_mut, Array.to_slice] using
            (congrArg (fun output => output.1.val) mutableExact).symm
        have writeBackExact : flow.writeBack =
            Array.from_slice flow.unsorted := by
          simpa [lift, Array.to_slice_mut] using
            (congrArg (fun output => output.2) mutableExact).symm
        have sortEvidence := caller_sort_list_by_key_sorted
          flow.mutableSlice.val sortedValues sortListEquation
        have sortedLength : sortedValues.length = 16 := by
          calc
            sortedValues.length = flow.mutableSlice.val.length :=
              sortEvidence.1.length_eq.symm
            _ = flow.unsorted.val.length := congrArg List.length mutableValues
            _ = 16 := flow.unsorted.length_eq
        have orderValues : flow.order.val = sortedValues := by
          rw [flow.orderExact, writeBackExact]
          simpa [Array.from_slice_val flow.unsorted flow.sortedSlice
            (by simpa [sliceExact] using sortedLength), sliceExact]
        rw [orderValues]
        exact sortEvidence.2
      · simp at sortRun

abbrev DuplicateWindowState :=
  core.slice.iter.Windows CallerScheduleItem × Unit

abbrev exactDuplicateWindowBody : DuplicateWindowState →
    Result (ControlFlow DuplicateWindowState
      (Bool × core.slice.iter.Windows CallerScheduleItem × Unit)) :=
  fun (self', predicate') => do
    let (item, nextWindows) ←
      (V7MerkleCallerGenerated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
        CallerScheduleItem).next self'
    match item with
    | none => .ok (.done (false, nextWindows, predicate'))
    | some window =>
        let (isDuplicate, nextClosure) ←
          V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
            predicate' window
        if isDuplicate = true then
          .ok (.done (true, nextWindows, nextClosure))
        else
          .ok (.cont (nextWindows, nextClosure))

private theorem exactLoopTrace_congr
    {state output : Type}
    {body₁ body₂ : state → Result (ControlFlow state output)}
    (bodyExact : body₁ = body₂)
    {start : state} {result : output}
    (trace : Nonempty (AspisV7MerkleK12SourceBridge.ExactLoopTrace
      body₁ start result)) :
    Nonempty (AspisV7MerkleK12SourceBridge.ExactLoopTrace
      body₂ start result) := by
  cases bodyExact
  exact trace

theorem duplicate_guard_success_yields_exact_trace
    (windows finalWindows : core.slice.iter.Windows CallerScheduleItem)
    (run :
      core.iter.traits.iterator.Iterator.any.default
        (V7MerkleCallerGenerated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          CallerScheduleItem)
        V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool
        windows () = .ok (false, finalWindows)) :
    Nonempty (AspisV7MerkleK12SourceBridge.ExactLoopTrace
      exactDuplicateWindowBody (windows, ()) (false, finalWindows, ())) := by
  unfold core.iter.traits.iterator.Iterator.any.default at run
  generalize loopEquation : loop _ (windows, ()) = loopResult at run
  cases loopResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at run
  | div => simp [Bind.bind, Aeneas.Std.bind] at run
  | ok loopOutput =>
      rcases loopOutput with ⟨found, windowsAfter, closure⟩
      simp only [Aeneas.Std.bind_tc_ok] at run
      have outputExact : (found, windowsAfter) = (false, finalWindows) := by
        simpa using Result.ok.inj run
      cases outputExact
      have closureExact : closure = () := Subsingleton.elim _ _
      subst closure
      let literalTrace :=
        AspisV7MerkleK12SourceBridge.loop_success_yields_exact_trace
          _
          (windows, ()) (false, finalWindows, ()) loopEquation
      refine exactLoopTrace_congr ?_ literalTrace
      funext state
      rcases state with ⟨self, predicate⟩
      unfold exactDuplicateWindowBody
      unfold V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2
      generalize nextEquation :
        core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
          self = nextResult
      cases nextResult with
      | fail error => simp [nextEquation, Bind.bind, Aeneas.Std.bind]
      | div => simp [nextEquation, Bind.bind, Aeneas.Std.bind]
      | ok next =>
          rcases next with ⟨item, nextWindows⟩
          cases item with
          | none => simp [nextEquation, Bind.bind, Aeneas.Std.bind]
          | some window =>
              generalize closureEquation :
                V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
                  predicate window = closureResult
              cases closureResult <;>
                simp [nextEquation, closureEquation, Bind.bind, Aeneas.Std.bind]

inductive ExactNoDuplicateWindows (slice : Slice CallerScheduleItem) :
    Nat → Type
  | done (index : Nat) (exhausted : slice.val.length < index + 2) :
      ExactNoDuplicateWindows slice index
  | step (index : Nat) (room : index + 2 ≤ slice.val.length)
      (closureRun :
        V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
          () (core.slice.iter.Windows.windowAt slice index 2) =
            .ok (false, ()))
      (tail : ExactNoDuplicateWindows slice (index + 1)) :
      ExactNoDuplicateWindows slice index

private theorem exact_duplicate_body_done_false
    (windows finalWindows : core.slice.iter.Windows CallerScheduleItem)
    (widthExact : windows.width = 2#usize)
    (run : exactDuplicateWindowBody (windows, ()) =
      .ok (.done (false, finalWindows, ()))) :
    windows.slice.val.length < windows.index + 2 := by
  unfold exactDuplicateWindowBody at run
  generalize nextEquation :
      core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
        windows = nextResult at run
  cases nextResult with
  | fail error => simp [nextEquation, Bind.bind, Aeneas.Std.bind] at run
  | div => simp [nextEquation, Bind.bind, Aeneas.Std.bind] at run
  | ok nextOutput =>
      rcases nextOutput with ⟨item, windowsAfter⟩
      simp [nextEquation, Bind.bind, Aeneas.Std.bind] at run
      cases item with
      | none =>
          change (if windows.index + windows.width.val ≤
              windows.slice.val.length then
              ok (some (core.slice.iter.Windows.windowAt windows.slice
                  windows.index windows.width.val),
                { windows with index := windows.index + 1 })
            else ok (none, windows)) = ok (none, windowsAfter)
            at nextEquation
          split at nextEquation
          · simp at nextEquation
          · rename_i exhausted
            simpa [widthExact, Nat.not_le] using exhausted
      | some window =>
          generalize closureEquation :
              V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
                () window = closureResult at run
          cases closureResult with
          | fail error =>
              simp [nextEquation, closureEquation, Bind.bind,
                Aeneas.Std.bind] at run
          | div =>
              simp [nextEquation, closureEquation, Bind.bind,
                Aeneas.Std.bind] at run
          | ok closureOutput =>
              rcases closureOutput with ⟨isDuplicate, closure⟩
              simp [nextEquation, closureEquation, Bind.bind,
                Aeneas.Std.bind] at run
              cases isDuplicate <;> simp at run

private theorem exact_duplicate_body_cont
    (windows nextWindows : core.slice.iter.Windows CallerScheduleItem)
    (widthExact : windows.width = 2#usize)
    (run : exactDuplicateWindowBody (windows, ()) =
      .ok (.cont (nextWindows, ()))) :
    windows.index + 2 ≤ windows.slice.val.length ∧
      nextWindows.slice = windows.slice ∧
      nextWindows.width = 2#usize ∧
      nextWindows.index = windows.index + 1 ∧
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
        () (core.slice.iter.Windows.windowAt windows.slice windows.index 2) =
          .ok (false, ()) := by
  unfold exactDuplicateWindowBody at run
  generalize nextEquation :
      core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
        windows = nextResult at run
  cases nextResult with
  | fail error => simp [nextEquation, Bind.bind, Aeneas.Std.bind] at run
  | div => simp [nextEquation, Bind.bind, Aeneas.Std.bind] at run
  | ok nextOutput =>
      rcases nextOutput with ⟨item, windowsAfter⟩
      simp [nextEquation, Bind.bind, Aeneas.Std.bind] at run
      cases item with
      | none => simp at run
      | some window =>
          generalize closureEquation :
              V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
                () window = closureResult at run
          cases closureResult with
          | fail error =>
              simp [nextEquation, closureEquation, Bind.bind,
                Aeneas.Std.bind] at run
          | div =>
              simp [nextEquation, closureEquation, Bind.bind,
                Aeneas.Std.bind] at run
          | ok closureOutput =>
              rcases closureOutput with ⟨isDuplicate, closure⟩
              simp [nextEquation, closureEquation, Bind.bind,
                Aeneas.Std.bind] at run
              cases isDuplicate with
              | true => simp at run
              | false =>
                  have outputExact : (windowsAfter, closure) =
                      (nextWindows, ()) := by
                    simpa using Result.ok.inj run
                  rcases outputExact with ⟨rfl, rfl⟩
                  change (if windows.index + windows.width.val ≤
                      windows.slice.val.length then
                      ok (some (core.slice.iter.Windows.windowAt windows.slice
                          windows.index windows.width.val),
                        { windows with index := windows.index + 1 })
                    else ok (none, windows)) =
                      ok (some window, nextWindows) at nextEquation
                  split at nextEquation
                  · rename_i room
                    simp only [Result.ok.injEq, Prod.mk.injEq,
                      Option.some.injEq] at nextEquation
                    rcases nextEquation with ⟨windowExact, nextExact⟩
                    subst nextWindows
                    have windowExactTwo :
                        core.slice.iter.Windows.windowAt windows.slice
                            windows.index 2 = window := by
                      simpa [widthExact] using windowExact
                    exact ⟨by simpa [widthExact] using room, rfl,
                      widthExact, rfl, by
                        rw [windowExactTwo]
                        exact closureEquation⟩
                  · simp at nextEquation

noncomputable def exact_duplicate_trace_yields_no_duplicate_windows_of_result_false
    (slice : Slice CallerScheduleItem) (index : Nat)
    (start : DuplicateWindowState)
    (result : Bool × core.slice.iter.Windows CallerScheduleItem × Unit)
    (sliceExact : start.1.slice = slice)
    (widthExact : start.1.width = 2#usize)
    (indexExact : start.1.index = index)
    (resultFalse : result.1 = false)
    (raw : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      exactDuplicateWindowBody start result) :
    ExactNoDuplicateWindows slice index := by
  induction raw generalizing slice index with
  | @done start result bodyRun =>
      rcases start with ⟨windows, closure⟩
      rcases result with ⟨found, finalWindows, finalClosure⟩
      have closureExact : closure = () := Subsingleton.elim _ _
      have finalClosureExact : finalClosure = () := Subsingleton.elim _ _
      subst closure
      subst finalClosure
      cases found with
      | false =>
          subst slice
          subst index
          exact .done windows.index
            (exact_duplicate_body_done_false windows finalWindows widthExact
              bodyRun)
      | true => cases resultFalse
  | @cont start next result bodyRun tail inductionHypothesis =>
      rcases start with ⟨currentWindows, currentClosure⟩
      rcases next with ⟨nextWindows, nextClosure⟩
      have currentClosureExact : currentClosure = () := Subsingleton.elim _ _
      have nextClosureExact : nextClosure = () := Subsingleton.elim _ _
      subst currentClosure
      subst nextClosure
      have step := exact_duplicate_body_cont currentWindows nextWindows
        widthExact bodyRun
      subst slice
      subst index
      exact .step currentWindows.index step.1 (by simpa using step.2.2.2.2)
        (inductionHypothesis currentWindows.slice (currentWindows.index + 1)
          step.2.1 step.2.2.1 step.2.2.2.1 resultFalse)

noncomputable def exact_duplicate_trace_yields_no_duplicate_windows
    (slice : Slice CallerScheduleItem) (index : Nat)
    (windows finalWindows : core.slice.iter.Windows CallerScheduleItem)
    (sliceExact : windows.slice = slice)
    (widthExact : windows.width = 2#usize)
    (indexExact : windows.index = index)
    (raw : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      exactDuplicateWindowBody (windows, ()) (false, finalWindows, ())) :
    ExactNoDuplicateWindows slice index :=
  exact_duplicate_trace_yields_no_duplicate_windows_of_result_false slice
    index (windows, ()) (false, finalWindows, ()) sliceExact widthExact
    indexExact rfl raw

private theorem window_at_two_values
    (slice : Slice CallerScheduleItem) (index : Nat)
    (room : index + 2 ≤ slice.val.length) :
    (core.slice.iter.Windows.windowAt slice index 2).val =
      [slice.val[index]!, slice.val[index + 1]!] := by
  unfold core.slice.iter.Windows.windowAt
  have firstRoom : index < slice.val.length := by omega
  have secondRoom : index + 1 < slice.val.length := by omega
  change List.take 2 (List.drop index slice.val) =
    [slice.val[index]!, slice.val[index + 1]!]
  rw [List.drop_eq_getElem_cons firstRoom,
    List.drop_eq_getElem_cons secondRoom]
  simp only [List.take,
    List.Inhabited_getElem_eq_getElem! slice.val index firstRoom,
    List.Inhabited_getElem_eq_getElem! slice.val (index + 1) secondRoom]

private theorem duplicate_closure_false_yields_positions_distinct
    (slice : Slice CallerScheduleItem) (index : Nat)
    (room : index + 2 ≤ slice.val.length)
    (run :
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
        () (core.slice.iter.Windows.windowAt slice index 2) =
          .ok (false, ())) :
    (slice.val[index]!).1 ≠ (slice.val[index + 1]!).1 := by
  have values := window_at_two_values slice index room
  unfold
    V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings.closure_2.Insts.CoreOpsFunctionFnMutTupleSharedSlicePairU32UsizeBool.call_mut
    at run
  simp [Slice.index_usize, values] at run
  have firstRoom : index < slice.val.length := by omega
  have secondRoom : index + 1 < slice.val.length := by omega
  rw [List.getElem?_eq_getElem firstRoom,
    List.getElem?_eq_getElem secondRoom] at run
  simp only [Option.getD_some] at run
  have decided : decide ((slice.val[index]).1 =
      (slice.val[index + 1]).1) = false :=
    congrArg Prod.fst (Result.ok.inj run)
  have distinct : (slice.val[index]).1 ≠
      (slice.val[index + 1]).1 := by
    simpa only [decide_eq_false_iff_not] using decided
  simpa only [
    List.Inhabited_getElem_eq_getElem! slice.val index firstRoom,
    List.Inhabited_getElem_eq_getElem! slice.val (index + 1) secondRoom]
    using distinct

theorem ExactNoDuplicateWindows.adjacent_positions_distinct
    {slice : Slice CallerScheduleItem} {start : Nat}
    (trace : ExactNoDuplicateWindows slice start) :
    ∀ index, start ≤ index → index + 1 < slice.val.length →
      (slice.val[index]!).1 ≠ (slice.val[index + 1]!).1 := by
  induction trace with
  | done terminal exhausted =>
      intro index startLe room
      omega
  | step current room closureRun tail inductionHypothesis =>
      intro index currentLe indexRoom
      by_cases currentExact : index = current
      · subst index
        exact duplicate_closure_false_yields_positions_distinct slice current
          room closureRun
      · apply inductionHypothesis index
        · omega
        · exact indexRoom

noncomputable def ExactCallerWrapperControlFlow.noDuplicateWindows
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    ExactNoDuplicateWindows (Array.to_slice flow.order) 0 := by
  have windowsRun := flow.windowsRun
  unfold core.slice.Slice.windows at windowsRun
  have widthNonzero : (2#usize : Std.Usize) ≠ 0#usize := by scalar_tac
  rw [if_neg widthNonzero] at windowsRun
  have windowsExact := Result.ok.inj windowsRun
  have windowsSlice : flow.windows.slice = flow.sharedSlice := by
    exact (congrArg
      (fun windows : core.slice.iter.Windows CallerScheduleItem => windows.slice)
      windowsExact).symm
  have windowsWidth : flow.windows.width = 2#usize := by
    exact (congrArg
      (fun windows : core.slice.iter.Windows CallerScheduleItem => windows.width)
      windowsExact).symm
  have windowsIndex : flow.windows.index = 0 := by
    exact (congrArg
      (fun windows : core.slice.iter.Windows CallerScheduleItem => windows.index)
      windowsExact).symm
  have sharedExact := Result.ok.inj flow.sharedSliceRun
  simp [lift, Array.to_slice] at sharedExact
  let raw := Classical.choice
    (duplicate_guard_success_yields_exact_trace flow.windows
      flow.windowsAfterDuplicateCheck flow.duplicateGuardRun)
  have exactTrace := exact_duplicate_trace_yields_no_duplicate_windows
    (Array.to_slice flow.order) 0 flow.windows
    flow.windowsAfterDuplicateCheck
    (windowsSlice.trans sharedExact.symm) windowsWidth windowsIndex raw
  exact exactTrace

theorem ExactCallerWrapperControlFlow.order_positions_strict
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    ∀ left right,
      left < flow.order.val.length → right < flow.order.val.length →
      left < right →
      (flow.order.val[left]!).1.val < (flow.order.val[right]!).1.val := by
  intro left right leftRoom rightRoom leftBefore
  have sorted := (List.pairwise_iff_getElem.mp flow.order_sorted)
  have endpointLE : (flow.order.val[left]!).1.val ≤
      (flow.order.val[right]!).1.val := by
    have ordered := sorted left right leftRoom rightRoom leftBefore
    unfold positionLE at ordered
    simpa only [
      List.Inhabited_getElem_eq_getElem! flow.order.val left leftRoom,
      List.Inhabited_getElem_eq_getElem! flow.order.val right rightRoom]
      using ordered
  have adjacentRoom : left + 1 < flow.order.val.length := by omega
  have adjacentDistinct :=
    flow.noDuplicateWindows.adjacent_positions_distinct left (by omega)
      adjacentRoom
  have adjacentLE : (flow.order.val[left]!).1.val ≤
      (flow.order.val[left + 1]!).1.val := by
    have ordered := sorted left (left + 1) leftRoom adjacentRoom (by omega)
    unfold positionLE at ordered
    simpa only [
      List.Inhabited_getElem_eq_getElem! flow.order.val left leftRoom,
      List.Inhabited_getElem_eq_getElem! flow.order.val (left + 1) adjacentRoom]
      using ordered
  have nextToEndpointLE : (flow.order.val[left + 1]!).1.val ≤
      (flow.order.val[right]!).1.val := by
    by_cases nextExact : left + 1 = right
    · subst right
      exact Nat.le_refl _
    · have ordered := sorted (left + 1) right adjacentRoom rightRoom (by omega)
      unfold positionLE at ordered
      simpa only [
        List.Inhabited_getElem_eq_getElem! flow.order.val (left + 1)
          adjacentRoom,
        List.Inhabited_getElem_eq_getElem! flow.order.val right rightRoom]
        using ordered
  have endpointDistinct : (flow.order.val[left]!).1.val ≠
      (flow.order.val[right]!).1.val := by
    intro endpointEqual
    have adjacentEqual : (flow.order.val[left]!).1.val =
        (flow.order.val[left + 1]!).1.val := by omega
    apply adjacentDistinct
    apply UScalar.eq_of_val_eq
    exact adjacentEqual
  omega

private theorem usize_sub_success_val
    (left right output : Std.Usize) (rightLe : right.val ≤ left.val)
    (run : left - right = (.ok output : Result Std.Usize)) :
    output.val = left.val - right.val := by
  obtain ⟨actual, actualRun, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.Usize.sub_spec (x := left) (y := right) rightLe)
  rw [actualRun] at run
  have actualExact := Result.ok.inj run
  subst output
  exact actualValue.1

private theorem caller_limit_value (limit : Std.U32)
    (run : 1#u32 <<< 18#i32 = (.ok limit : Result Std.U32)) :
    limit.val = 2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth := by
  obtain ⟨actual, actualRun, actualValue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Std.U32.ShiftLeft_IScalar_spec 1#u32 18#i32 (by scalar_tac)
      (by scalar_tac))
  rw [actualRun] at run
  have actualExact := Result.ok.inj run
  subst limit
  simpa [AspisPool.V7MerkleQueryGrammar.treeDepth, Std.U32.size,
    Std.U32.numBits] using actualValue.1

theorem ExactCallerWrapperControlFlow.iterator_exact
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    flow.iterator.array = flow.order ∧ flow.iterator.index = 0 := by
  have iteratorRun := flow.iteratorRun
  unfold Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    at iteratorRun
  have iteratorExact := Result.ok.inj iteratorRun
  constructor
  · exact (congrArg (fun iter : CallerIter => iter.array) iteratorExact).symm
  · exact (congrArg (fun iter : CallerIter => iter.index) iteratorExact).symm

theorem ExactCallerWrapperControlFlow.last_index_exact
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    flow.lastIndex.val = 15 := by
  have value := usize_sub_success_val
    V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT 1#usize flow.lastIndex
    (by unfold V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT; scalar_tac)
    flow.lastIndexRun
  simpa [V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT] using value

theorem ExactCallerWrapperControlFlow.last_position_exact
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    (flow.order.val[15]!).1 = flow.lastPosition := by
  have lastRun := flow.lastRun
  unfold Array.index_usize at lastRun
  have indexExact : flow.lastIndex = 15#usize := by
    apply UScalar.eq_of_val_eq
    exact flow.last_index_exact
  rw [indexExact] at lastRun
  have room : 15 < flow.order.val.length := by
    simpa using flow.order.length_eq
  simp [getElem?_pos flow.order.val 15 room] at lastRun
  have positionExact := congrArg Prod.fst lastRun
  simpa only [List.Inhabited_getElem_eq_getElem! flow.order.val 15 room]
    using positionExact

theorem ExactCallerWrapperControlFlow.order_position_bound
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    ∀ index, index < flow.order.val.length →
      (flow.order.val[index]!).1.val <
        2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth := by
  intro index room
  have lengthExact : flow.order.val.length = 16 := flow.order.length_eq
  have lastBound : flow.lastPosition.val < flow.limit.val := by
    simpa using flow.lastBoundGuard
  have limitValue := caller_limit_value flow.limit flow.limitRun
  rw [limitValue] at lastBound
  by_cases last : index = 15
  · subst index
    rw [flow.last_position_exact]
    exact lastBound
  · have beforeLast : index < 15 := by omega
    have endpointBound : (flow.order.val[15]!).1.val <
        2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth := by
      rw [flow.last_position_exact]
      exact lastBound
    exact (flow.order_positions_strict index 15 room (by omega) beforeLast).trans
      endpointBound

theorem ExactCallerWrapperControlFlow.iterator_position_bound
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    CallerArrayPositionBound flow.iterator := by
  unfold CallerArrayPositionBound
  rw [flow.iterator_exact.1]
  exact flow.order_position_bound

private theorem caller_array_position_bound_after_next
    (iter iterAfter : CallerIter) (position : Std.U32) (ordinal : Std.Usize)
    (bounds : CallerArrayPositionBound iter)
    (run :
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
        .ok (some (position, ordinal), iterAfter)) :
    CallerArrayPositionBound iterAfter := by
  have facts := caller_iterator_next_some_facts iter iterAfter position ordinal run
  unfold CallerArrayPositionBound at bounds ⊢
  rw [facts.2.2.1]
  exact bounds

structure ExactAcceptedCallerTraceEvidence
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined : CallerCombined) (entries : CallerEntries)
    (output : CallerCombined) where
  seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash)
  trace : ExactAcceptedCallerTrace hash wire powers iter combined entries output
    seeds
  seedCount : seeds.length + iter.index = 16
  seedPositions : seeds.map
      AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.position =
    (iter.array.val.drop iter.index).map Prod.fst

noncomputable def exact_caller_control_flow_trace_yields_accepted_trace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined : CallerCombined) (entries : CallerEntries)
    (output : CallerCombined)
    (bounds : CallerArrayPositionBound iter)
    (indexBound : iter.index ≤ 16)
    (raw : AspisV7MerkleK12SourceBridge.ExactLoopTrace
      (exactCallerBody wire hash powers) (iter, combined, entries)
      (some (.Ok output))) :
    ExactAcceptedCallerTraceEvidence hash wire powers iter combined entries
      output := by
  generalize startEquation : (iter, combined, entries) = start at raw
  generalize resultEquation :
    some (core.result.Result.Ok output) = result at raw
  induction raw generalizing iter combined entries output bounds indexBound with
  | @done start result bodyRun =>
      cases startEquation
      cases resultEquation
      have terminal := exact_caller_body_accept_done_yields_terminal hash wire
        powers iter combined output entries bodyRun
      have combinedExact := terminal.1
      let iterAfter := Classical.choose terminal.2
      have iterAfterSpec := Classical.choose_spec terminal.2
      let outputLevel := Classical.choose iterAfterSpec
      have outputLevelSpec := Classical.choose_spec iterAfterSpec
      let outputNext := Classical.choose outputLevelSpec
      have terminalRuns := Classical.choose_spec outputLevelSpec
      have iteratorRun := terminalRuns.1
      have verifierRun := terminalRuns.2
      subst output
      have exhausted := caller_iterator_next_none_exhausted iter
        iterAfter iteratorRun
      have indexExact : iter.index = 16 := by omega
      exact
        { seeds := []
          trace := .done iteratorRun verifierRun
          seedCount := by simp [indexExact]
          seedPositions := by simp [indexExact, caller_iter_array_length] }
  | @cont start next result bodyRun tail inductionHypothesis =>
      cases startEquation
      cases resultEquation
      rcases next with ⟨nextIter, nextCombined, nextEntries⟩
      let step := Classical.choice
        (exact_caller_body_cont_yields_step hash wire powers iter
          nextIter combined nextCombined entries nextEntries
          bodyRun)
      have nextFacts := caller_iterator_next_some_facts iter nextIter
        step.position step.ordinal step.iteratorRun
      have active : iter.index < iter.array.val.length := by
        simpa [caller_iter_array_length] using nextFacts.1
      have exactItem := nextFacts.2.1
      rw [getElem!_pos iter.array.val iter.index active] at exactItem
      have positionBound : step.position.val <
          2 ^ AspisPool.V7MerkleQueryGrammar.treeDepth := by
        have itemBound := bounds iter.index active
        rw [getElem!_pos iter.array.val iter.index active] at itemBound
        have positionExact := congrArg Prod.fst exactItem
        rw [← positionExact] at itemBound
        exact itemBound
      have nextBounds := caller_array_position_bound_after_next iter
        nextIter step.position step.ordinal bounds step.iteratorRun
      have nextIndexBound : nextIter.index ≤ 16 := by
        rw [nextFacts.2.2.2]
        omega
      let tailEvidence := inductionHypothesis nextIter nextCombined nextEntries
        output nextBounds nextIndexBound rfl rfl
      let seed := pairedSourceSeedOfCallerLeafRuns hash wire step.ordinal
        step.position step.record step.c1Leaf step.c2Leaf positionBound
        step.queryRun step.c1LeafRun step.c2LeafRun
      have seedPosition : seed.position = step.position := rfl
      exact
        { seeds := seed :: tailEvidence.seeds
          trace := .step step.position step.ordinal step.record
            step.combinedValue step.c1Leaf step.c2Leaf positionBound
            step.iteratorRun step.queryRun step.gammaRun step.combinedUpdateRun
            step.c1LeafRun step.c2LeafRun step.pushRun tailEvidence.trace
          seedCount := by
            simp only [List.length_cons]
            have tailCount := tailEvidence.seedCount
            rw [nextFacts.2.2.2] at tailCount
            omega
          seedPositions := by
            simp only [List.map_cons]
            rw [tailEvidence.seedPositions, nextFacts.2.2.1,
              nextFacts.2.2.2]
            rw [List.drop_eq_getElem_cons active]
            simp only [List.map_cons]
            rw [seedPosition]
            congr 1
            simpa using congrArg Prod.fst exactItem }

noncomputable def ExactCallerWrapperControlFlow.acceptedTraceEvidenceOfWrapper
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    ExactAcceptedCallerTraceEvidence hash wire powers flow.iterator
      callerInitialCombined callerInitialEntries output := by
  let raw := Classical.choice
    (caller_loop_success_yields_exact_control_flow_trace wire hash powers
      flow.iterator callerInitialCombined output callerInitialEntries
      flow.callerLoopRun)
  exact exact_caller_control_flow_trace_yields_accepted_trace hash wire powers
    flow.iterator callerInitialCombined callerInitialEntries output
    flow.iterator_position_bound (by rw [flow.iterator_exact.2]; omega) raw

def sixteenSeedBatch
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    (seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash))
    (lengthExact : seeds.length = 16) :
    AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash :=
  fun ordinal => seeds.get (Fin.cast lengthExact.symm ordinal)

theorem list_ofFn_sixteenSeedBatch
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    (seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash))
    (lengthExact : seeds.length = 16) :
    List.ofFn (sixteenSeedBatch seeds lengthExact) = seeds := by
  change List.ofFn (fun ordinal : Fin 16 =>
    seeds.get (Fin.cast lengthExact.symm ordinal)) = seeds
  rw [← List.ofFn_congr lengthExact seeds.get]
  exact List.ofFn_get seeds

theorem ExactCallerWrapperControlFlow.seed_positions_exact
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    (flow.acceptedTraceEvidenceOfWrapper.seeds.map
        AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.position) =
      flow.order.val.map Prod.fst := by
  have positions := flow.acceptedTraceEvidenceOfWrapper.seedPositions
  rw [flow.iterator_exact.1, flow.iterator_exact.2] at positions
  simpa using positions

theorem ExactCallerWrapperControlFlow.seed_length_exact
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    flow.acceptedTraceEvidenceOfWrapper.seeds.length = 16 := by
  have count := flow.acceptedTraceEvidenceOfWrapper.seedCount
  rw [flow.iterator_exact.2] at count
  simpa using count

noncomputable def ExactCallerWrapperControlFlow.seedBatch
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash :=
  sixteenSeedBatch flow.acceptedTraceEvidenceOfWrapper.seeds
    flow.seed_length_exact

theorem ExactCallerWrapperControlFlow.seedBatch_list
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    List.ofFn flow.seedBatch = flow.acceptedTraceEvidenceOfWrapper.seeds := by
  exact list_ofFn_sixteenSeedBatch _ flow.seed_length_exact

theorem ExactCallerWrapperControlFlow.seedBatch_positionsInjective
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    Function.Injective (fun ordinal => (flow.seedBatch ordinal).finitePosition) := by
  intro left right equalPositions
  apply Fin.ext
  by_contra indicesDistinct
  have leftPositionExact : (flow.seedBatch left).position =
      (flow.order.val[left.val]!).1 := by
    have listExact := flow.seed_positions_exact
    have leftRoom : left.val <
        flow.acceptedTraceEvidenceOfWrapper.seeds.length := by
      rw [flow.seed_length_exact]
      exact left.isLt
    have leftOrderRoom : left.val < flow.order.val.length := by
      rw [flow.order.length_eq]
      exact left.isLt
    have leftSeedMapRoom : left.val <
        (flow.acceptedTraceEvidenceOfWrapper.seeds.map
          AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.position).length := by
      simpa only [List.length_map] using leftRoom
    have leftOrderMapRoom : left.val <
        (flow.order.val.map Prod.fst).length := by
      simpa only [List.length_map] using leftOrderRoom
    have mappedGet := congrArg
      (fun values => values[left.val]!) listExact
    rw [getElem!_pos
        (flow.acceptedTraceEvidenceOfWrapper.seeds.map
          AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.position)
        left.val leftSeedMapRoom,
      getElem!_pos (flow.order.val.map Prod.fst) left.val leftOrderMapRoom]
      at mappedGet
    simp only [List.getElem_map] at mappedGet
    rw [getElem!_pos flow.order.val left.val leftOrderRoom]
    simpa [ExactCallerWrapperControlFlow.seedBatch, sixteenSeedBatch]
      using mappedGet
  have rightPositionExact : (flow.seedBatch right).position =
      (flow.order.val[right.val]!).1 := by
    have listExact := flow.seed_positions_exact
    have rightRoom : right.val <
        flow.acceptedTraceEvidenceOfWrapper.seeds.length := by
      rw [flow.seed_length_exact]
      exact right.isLt
    have rightOrderRoom : right.val < flow.order.val.length := by
      rw [flow.order.length_eq]
      exact right.isLt
    have rightSeedMapRoom : right.val <
        (flow.acceptedTraceEvidenceOfWrapper.seeds.map
          AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.position).length := by
      simpa only [List.length_map] using rightRoom
    have rightOrderMapRoom : right.val <
        (flow.order.val.map Prod.fst).length := by
      simpa only [List.length_map] using rightOrderRoom
    have mappedGet := congrArg
      (fun values => values[right.val]!) listExact
    rw [getElem!_pos
        (flow.acceptedTraceEvidenceOfWrapper.seeds.map
          AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.position)
        right.val rightSeedMapRoom,
      getElem!_pos (flow.order.val.map Prod.fst) right.val rightOrderMapRoom]
      at mappedGet
    simp only [List.getElem_map] at mappedGet
    rw [getElem!_pos flow.order.val right.val rightOrderRoom]
    simpa [ExactCallerWrapperControlFlow.seedBatch, sixteenSeedBatch]
      using mappedGet
  have positionValuesEqual : (flow.seedBatch left).position.val =
      (flow.seedBatch right).position.val := by
    exact congrArg
      (fun position : AspisPool.V7MerkleQueryExtractor.Position => position.val)
      equalPositions
  have leftOrderRoom : left.val < flow.order.val.length := by
    rw [flow.order.length_eq]
    exact left.isLt
  have rightOrderRoom : right.val < flow.order.val.length := by
    rw [flow.order.length_eq]
    exact right.isLt
  rcases Nat.lt_or_gt_of_ne indicesDistinct with leftBefore | rightBefore
  · have strict := flow.order_positions_strict left.val right.val
      leftOrderRoom rightOrderRoom leftBefore
    rw [← leftPositionExact, ← rightPositionExact] at strict
    omega
  · have strict := flow.order_positions_strict right.val left.val
      rightOrderRoom leftOrderRoom rightBefore
    rw [← leftPositionExact, ← rightPositionExact] at strict
    omega

noncomputable def ExactCallerWrapperControlFlow.acceptedTrace
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    ExactAcceptedCallerTrace hash wire powers flow.iterator
      callerInitialCombined callerInitialEntries output
      (List.ofFn flow.seedBatch) := by
  rw [flow.seedBatch_list]
  exact flow.acceptedTraceEvidenceOfWrapper.trace


structure CallerTerminalEvidence
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (initialEntries : CallerEntries)
    (seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash)) where
  terminalCombined : CallerCombined
  terminalEntries : CallerEntries
  outputLevel : CallerEntries
  outputNext : CallerEntries
  entriesExact : terminalEntries.val = initialEntries.val ++
    seeds.map AspisV7MerkleK12AcceptedBridge.PairedSourceSeed.entry
  verifierRun :
    V7MerkleCallerGenerated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      hash (wire.c1_root, wire.c2_root) 18#u32
      (alloc.vec.Vec.deref terminalEntries)
      (wire.c1_frontier, wire.c2_frontier)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
        .ok (true, outputLevel, outputNext)

/-- Exact caller pushes determine the verifier's entry slice. -/
noncomputable def ExactAcceptedCallerTrace.terminalEvidence
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {iter : CallerIter} {combined finalCombined : CallerCombined}
    {entries : CallerEntries}
    {seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash)}
    (trace : ExactAcceptedCallerTrace hash wire powers iter combined entries
      finalCombined seeds) : CallerTerminalEvidence hash wire entries seeds := by
  induction trace with
  | @done iter iterAfter combined terminalEntries outputLevel outputNext
      iteratorRun verifierRun =>
      exact
        { terminalCombined := combined
          terminalEntries := terminalEntries
          outputLevel := outputLevel
          outputNext := outputNext
          entriesExact := by simp
          verifierRun := verifierRun }
  | @step iter iterAfter combined combinedAfter finalCombined entries
      entriesAfter seeds position ordinal record combinedValue c1Leaf c2Leaf
      positionBound iteratorRun queryRun gammaRun combinedUpdateRun c1LeafRun
      c2LeafRun pushRun tail inductionHypothesis =>
      let seed := pairedSourceSeedOfCallerLeafRuns hash wire ordinal position
        record c1Leaf c2Leaf positionBound queryRun c1LeafRun c2LeafRun
      have seedEntry : seed.entry = (position, c1Leaf, c2Leaf) := rfl
      have pushedValues :=
        AspisV7MerkleK12TraversalBridge.vec_push_success_values_append entries
          entriesAfter (position, c1Leaf, c2Leaf) pushRun
      exact
        { terminalCombined := inductionHypothesis.terminalCombined
          terminalEntries := inductionHypothesis.terminalEntries
          outputLevel := inductionHypothesis.outputLevel
          outputNext := inductionHypothesis.outputNext
          entriesExact := by
            rw [inductionHypothesis.entriesExact, pushedValues]
            simp only [List.map_cons, List.append_assoc]
            rw [← seedEntry]
            simpa only [seed, List.singleton_append]
          verifierRun := inductionHypothesis.verifierRun }

theorem CallerTerminalEvidence.standaloneVerifierRun
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {initialEntries : CallerEntries}
    {seeds : List (AspisV7MerkleK12AcceptedBridge.PairedSourceSeed hash)}
    (evidence : CallerTerminalEvidence hash wire initialEntries seeds) :
    V7MerkleK12Generated.v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      hash (wire.c1_root, wire.c2_root) 18#u32
      (alloc.vec.Vec.deref evidence.terminalEntries)
      (wire.c1_frontier, wire.c2_frontier)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT) =
        .ok (true, evidence.outputLevel, evidence.outputNext) := by
  rw [← AspisV7MerkleCallerNamespaceBridge.caller_verify_two_minimal_subtrees_v7_bytes_eq]
  exact evidence.verifierRun

noncomputable def exactTraversalOfCallerTrace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined output : CallerCombined)
    (initialEntries : CallerEntries)
    (seeds : AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash)
    (trace : ExactAcceptedCallerTrace hash wire powers iter combined
      initialEntries output (List.ofFn seeds)) :
    let evidence := trace.terminalEvidence
    AspisV7MerkleK12SourceBridge.ExactAcceptedTwoTreeTraversal hash
      wire.c1_root wire.c2_root 18#u32
      (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
      wire.c2_frontier
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      evidence.outputLevel evidence.outputNext := by
  dsimp only
  exact AspisV7MerkleK12OuterTraceBridge.exactTraversalOfVerifierSuccess hash
    wire.c1_root wire.c2_root
    (alloc.vec.Vec.deref trace.terminalEvidence.terminalEntries)
    wire.c1_frontier wire.c2_frontier
    (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
      V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
    (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
      V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
    trace.terminalEvidence.outputLevel trace.terminalEvidence.outputNext
    trace.terminalEvidence.standaloneVerifierRun

noncomputable def openingProofOfExactCallerTrace
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined output : CallerCombined)
    (initialEntries : CallerEntries)
    (seeds : AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash)
    (trace : ExactAcceptedCallerTrace hash wire powers iter combined
      initialEntries output (List.ofFn seeds))
    (initialEntriesEmpty : initialEntries.val = []) :
    AspisPool.V7MerkleQueryExtractor.TwoTreeOpeningProof := by
  let evidence := trace.terminalEvidence
  let traversal := exactTraversalOfCallerTrace hash wire powers iter combined
    output initialEntries seeds trace
  have entriesExact : evidence.terminalEntries.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry) := by
    rw [evidence.entriesExact, initialEntriesEmpty]
    simp only [List.nil_append]
    rw [List.map_ofFn]
    congr 1
  exact AspisV7MerkleK12AcceptedBridge.proofOfSourceOpeningBatch
    (AspisV7MerkleK12AcceptedBridge.sourceOpeningBatchOfRounds seeds
      traversal.initialization.seededLevel evidence.outputLevel
      (AspisV7MerkleK12OuterTraceBridge.outerEdgeTraceOfExactTraversal hash
        wire.c1_root wire.c2_root
        (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
        wire.c2_frontier
        (alloc.vec.Vec.with_capacity
          AspisV7MerkleK12SourceBridge.GeneratedEntry
          V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
        (alloc.vec.Vec.with_capacity
          AspisV7MerkleK12SourceBridge.GeneratedEntry
          V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
        evidence.outputLevel evidence.outputNext traversal).toPairedHashRounds
      (by
        rw [AspisV7MerkleK12TraversalBridge.exact_traversal_seeded_level_values
          hash wire.c1_root wire.c2_root 18#u32
          (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
          wire.c2_frontier
          (alloc.vec.Vec.with_capacity
            AspisV7MerkleK12SourceBridge.GeneratedEntry
            V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
          (alloc.vec.Vec.with_capacity
            AspisV7MerkleK12SourceBridge.GeneratedEntry
            V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
          evidence.outputLevel evidence.outputNext traversal]
        exact entriesExact)
      (AspisV7MerkleK12TraversalBridge.exact_traversal_final_level_values hash
        wire.c1_root wire.c2_root 18#u32
        (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
        wire.c2_frontier
        (alloc.vec.Vec.with_capacity
          AspisV7MerkleK12SourceBridge.GeneratedEntry
          V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
        (alloc.vec.Vec.with_capacity
          AspisV7MerkleK12SourceBridge.GeneratedEntry
          V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
        evidence.outputLevel evidence.outputNext traversal))

/-- Exact translated caller trace to the existing frozen accepted predicate.
The only non-control-flow input is the SHA callback semantics.  Schedule
injectivity is a direct caller guard fact and will be supplied by top-level
caller-success inversion. -/
theorem exact_translated_caller_trace_implies_accepted_two_tree_openings
    (sha256 : List AspisPool.V7MerkleQueryGrammar.Byte →
      List AspisPool.V7MerkleQueryGrammar.Byte)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256
      sha256 hash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (iter : CallerIter) (combined output : CallerCombined)
    (initialEntries : CallerEntries)
    (seeds : AspisV7MerkleK12AcceptedBridge.PairedSourceSeedBatch hash)
    (trace : ExactAcceptedCallerTrace hash wire powers iter combined
      initialEntries output (List.ofFn seeds))
    (initialEntriesEmpty : initialEntries.val = [])
    (positionsInjective : Function.Injective
      (fun ordinal => (seeds ordinal).finitePosition)) :
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings
      (AspisV7MerkleK12AcceptedBridge.frozenTruncate sha256)
      (AspisV7MerkleK12AcceptedBridge.rootsOfGeneratedDigests wire.c1_root
        wire.c2_root)
      (openingProofOfExactCallerTrace hash wire powers iter combined output
        initialEntries seeds trace initialEntriesEmpty) := by
  let evidence := trace.terminalEvidence
  have entriesExact : evidence.terminalEntries.val =
      List.ofFn (fun ordinal => (seeds ordinal).entry) := by
    rw [evidence.entriesExact, initialEntriesEmpty]
    simp only [List.nil_append]
    rw [List.map_ofFn]
    congr 1
  exact
    AspisV7MerkleK12OuterTraceBridge.translated_verifier_success_implies_accepted_two_tree_openings
      sha256 hash hashSemantics wire.c1_root wire.c2_root
      (alloc.vec.Vec.deref evidence.terminalEntries) wire.c1_frontier
      wire.c2_frontier
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      (alloc.vec.Vec.with_capacity AspisV7MerkleK12SourceBridge.GeneratedEntry
        V7MerkleCallerGenerated.v6_onefold.V6_QUERY_COUNT)
      evidence.outputLevel evidence.outputNext evidence.standaloneVerifierRun
      seeds entriesExact positionsInjective

noncomputable def ExactCallerWrapperControlFlow.openingProof
    {hash : AspisV7MerkleK12SourceBridge.GeneratedHash}
    {wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire}
    {queries : Array Std.U32 16#usize}
    {powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers}
    {output : CallerCombined}
    (flow : ExactCallerWrapperControlFlow hash wire queries powers output) :
    AspisPool.V7MerkleQueryExtractor.TwoTreeOpeningProof :=
  openingProofOfExactCallerTrace hash wire powers flow.iterator
    callerInitialCombined output callerInitialEntries flow.seedBatch
    flow.acceptedTrace (by
      simp [callerInitialEntries, alloc.vec.Vec.with_capacity,
        alloc.vec.Vec.new])

noncomputable def exactWrapperControlFlowOfCallerSuccess
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (queries : Array Std.U32 16#usize)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : CallerCombined)
    (run :
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
        hash wire queries powers = .ok (.Ok output)) :
    ExactCallerWrapperControlFlow hash wire queries powers output :=
  Classical.choice
    (translated_caller_success_yields_exact_wrapper_control_flow hash wire
      queries powers output run)

noncomputable def openingProofOfTranslatedCallerSuccess
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (queries : Array Std.U32 16#usize)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : CallerCombined)
    (run :
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
        hash wire queries powers = .ok (.Ok output)) :
    AspisPool.V7MerkleQueryExtractor.TwoTreeOpeningProof :=
  (exactWrapperControlFlowOfCallerSuccess hash wire queries powers output run).openingProof

/-- Literal translated production caller success implies the existing frozen
accepted-opening predicate.  SHA-256 callback semantics is the only semantic
boundary. -/
theorem translated_caller_success_implies_accepted_two_tree_openings
    (sha256 : List AspisPool.V7MerkleQueryGrammar.Byte →
      List AspisPool.V7MerkleQueryGrammar.Byte)
    (hash : AspisV7MerkleK12SourceBridge.GeneratedHash)
    (hashSemantics : AspisV7MerkleK12SourceBridge.HashCallbackEqualsSha256
      sha256 hash)
    (wire : V7MerkleCallerGenerated.v7_onefold.V7CompactOneFoldWire)
    (queries : Array Std.U32 16#usize)
    (powers :
      V7MerkleCallerGenerated.state_only_spend_query.StateOnlySpendQueryPowers)
    (output : CallerCombined)
    (run :
      V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
        hash wire queries powers = .ok (.Ok output)) :
    AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings
      (AspisV7MerkleK12AcceptedBridge.frozenTruncate sha256)
      (AspisV7MerkleK12AcceptedBridge.rootsOfGeneratedDigests wire.c1_root
        wire.c2_root)
      (openingProofOfTranslatedCallerSuccess hash wire queries powers output
        run) := by
  let flow := exactWrapperControlFlowOfCallerSuccess hash wire queries powers
    output run
  change AspisPool.V7MerkleQueryExtractor.accepted_two_tree_openings
    (AspisV7MerkleK12AcceptedBridge.frozenTruncate sha256)
    (AspisV7MerkleK12AcceptedBridge.rootsOfGeneratedDigests wire.c1_root
      wire.c2_root) flow.openingProof
  exact exact_translated_caller_trace_implies_accepted_two_tree_openings
    sha256 hash hashSemantics wire powers flow.iterator callerInitialCombined
    output callerInitialEntries flow.seedBatch flow.acceptedTrace
    (by
      simp [callerInitialEntries, alloc.vec.Vec.with_capacity,
        alloc.vec.Vec.new])
    flow.seedBatch_positionsInjective

#print axioms caller_query_success_lengths
#print axioms pairedSourceSeedOfCallerLeafRuns
#print axioms caller_loop_success_yields_exact_control_flow_trace
#print axioms ExactAcceptedCallerTrace.terminalEvidence
#print axioms CallerTerminalEvidence.standaloneVerifierRun
#print axioms exactTraversalOfCallerTrace
#print axioms openingProofOfExactCallerTrace
#print axioms exact_translated_caller_trace_implies_accepted_two_tree_openings
#print axioms translated_caller_success_yields_exact_wrapper_control_flow
#print axioms ExactCallerWrapperControlFlow.order_positions_strict
#print axioms exact_caller_control_flow_trace_yields_accepted_trace
#print axioms translated_caller_success_implies_accepted_two_tree_openings

end AspisV7MerkleK12CallerBridge
