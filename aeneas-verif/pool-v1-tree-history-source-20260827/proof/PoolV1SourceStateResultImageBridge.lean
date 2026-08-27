import PoolV1SourceStateResultImage.Funs

/-!
# Pool V1 literal state/result-image bridge

This follows the production `source_state_and_result_image_match` caller and
exposes every accepted byte comparison.  In particular, successful checking
pins the persisted state sequence, root-history page and slot, tree sequence,
tree root, and pool identity in `next_pool_image`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace PoolV1SourceStateResultImageBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1SourceStateResultImage

def transitionCount :
    aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind → Nat
  | .PrivateTransfer => 2
  | .Withdrawal => 1

theorem literal_source_state_result_image_success_has_exact_checks
    (plan : prepared_settlement_format.PreparedSettlementPlanViewV1)
    (source : Array Std.U8 1000#usize)
    (run : prepared_settlement.source_state_and_result_image_match plan source =
      .ok (.Ok ())) :
    ∃ sourceSequence sourceTreeSequence count finalSequence : Std.U64,
    ∃ finalReceipt :
        aspis_statement.pool_v1.incremental_merkle.AppendOneV1,
    ∃ location : aspis_statement.pool_v1.root_history.RootHistoryLocationV1,
    ∃ sourceRoot nextSequence nextPage nextSlot nextTreeSequence nextRoot
        identity : Slice Std.U8,
    ∃ sourceRootBytes nextRootBytes : Array Std.U8 32#usize,
    ∃ nextSequenceBytes nextPageBytes nextTreeSequenceBytes :
        Array Std.U8 8#usize,
    ∃ nextSlotBytes : Array Std.U8 2#usize,
      (sourceSequence != plan.source_sequence) = false ∧
      (sourceTreeSequence != plan.source_sequence) = false ∧
      count.val = transitionCount plan.transition_kind ∧
      U64.checked_add plan.source_sequence count = .some finalSequence ∧
      core.option.Option.unwrap_or plan.second_receipt plan.first_receipt =
        finalReceipt ∧
      aspis_statement.pool_v1.root_history.root_history_location finalSequence =
        Result.ok location ∧
      aspis_statement.atomic_statement.encode_digest_canonical
        plan.source_root = Result.ok sourceRootBytes ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 sourceRoot
        sourceRootBytes = Result.ok false ∧
      core.num.U64.to_le_bytes finalSequence = nextSequenceBytes ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 nextSequence
        nextSequenceBytes = Result.ok false ∧
      core.num.U64.to_le_bytes location.page_number = nextPageBytes ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 nextPage
        nextPageBytes = Result.ok false ∧
      core.num.U16.to_le_bytes location.slot = nextSlotBytes ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 nextSlot
        nextSlotBytes = Result.ok false ∧
      core.num.U64.to_le_bytes finalSequence = nextTreeSequenceBytes ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 nextTreeSequence
        nextTreeSequenceBytes = Result.ok false ∧
      aspis_statement.atomic_statement.encode_digest_canonical
        finalReceipt.root = Result.ok nextRootBytes ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 nextRoot
        nextRootBytes = Result.ok false ∧
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 identity
        plan.pool = Result.ok false := by
  unfold prepared_settlement.source_state_and_result_image_match at run
  generalize sourceSequenceSliceRun :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) source
      { start := prepared_settlement.STATE_SEQUENCE_OFFSET,
        «end» := prepared_settlement.STATE_PAGE_OFFSET } = sourceSequenceSliceResult
      at run
  cases sourceSequenceSliceResult with
  | fail error => simp at run
  | div => simp at run
  | ok sourceSequenceSlice =>
    simp only [bind_tc_ok] at run
    generalize sourceSequenceArrayRun :
      core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
        sourceSequenceSlice = sourceSequenceArrayResult at run
    cases sourceSequenceArrayResult with
    | fail error => simp at run
    | div => simp at run
    | ok sourceSequenceArray =>
      simp only [bind_tc_ok] at run
      generalize mapRun : core.result.Result.map_err
        prepared_settlement.source_state_and_result_image_match.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorProgramError
        sourceSequenceArray () = mappedResult at run
      cases mappedResult with
      | fail error => simp at run
      | div => simp at run
      | ok mapped =>
        cases mapped with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
            at run
        | Ok sourceSequenceBytes =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
          generalize sourceSequenceRun :
            core.num.U64.from_le_bytes sourceSequenceBytes = sourceSequence at run
          simp only [lift, bind_tc_ok] at run
          focus
            generalize treeOffsetRun : state.POOL_V1_STATE_TREE_OFFSET =
              treeOffsetResult at run
            cases treeOffsetResult with
            | fail error => simp at run
            | div => simp at run
            | ok treeOffset =>
              simp only [bind_tc_ok] at run
              generalize treeSequenceOffsetRun :
                treeOffset + prepared_settlement.TREE_SEQUENCE_RELATIVE_OFFSET =
                  treeSequenceOffsetResult at run
              cases treeSequenceOffsetResult with
              | fail error => simp at run
              | div => simp at run
              | ok treeSequenceOffset =>
                simp only [bind_tc_ok] at run
                generalize treeRootOffsetRun :
                  treeOffset + prepared_settlement.TREE_ROOT_RELATIVE_OFFSET =
                    treeRootOffsetResult at run
                cases treeRootOffsetResult with
                | fail error => simp at run
                | div => simp at run
                | ok treeRootOffset =>
                  simp only [bind_tc_ok] at run
                  generalize sourceTreeSliceRun :
                    core.array.Array.index (core.ops.index.IndexSlice
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) source
                      { start := treeSequenceOffset, «end» := treeRootOffset } =
                        sourceTreeSliceResult at run
                  cases sourceTreeSliceResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok sourceTreeSlice =>
                    simp only [bind_tc_ok] at run
                    generalize sourceTreeArrayRun :
                      core.array.TryFromArrayCopySlice.try_from 8#usize
                        core.marker.CopyU8 sourceTreeSlice = sourceTreeArrayResult at run
                    cases sourceTreeArrayResult with
                    | fail error => simp at run
                    | div => simp at run
                    | ok sourceTreeArray =>
                      simp only [bind_tc_ok] at run
                      generalize mapTreeRun : core.result.Result.map_err
                        prepared_settlement.source_state_and_result_image_match.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorProgramError
                        sourceTreeArray () = mappedTreeResult at run
                      cases mappedTreeResult with
                      | fail error => simp at run
                      | div => simp at run
                      | ok mappedTree =>
                        cases mappedTree with
                        | Err error =>
                          simp [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                            at run
                        | Ok sourceTreeBytes =>
                          simp only [core.result.Result.Insts.CoreOpsTry.branch,
                            bind_tc_ok] at run
                          generalize sourceTreeSequenceRun :
                            core.num.U64.from_le_bytes sourceTreeBytes =
                              sourceTreeSequence at run
                          focus
                            generalize sourceMismatchRun :
                              (sourceSequence != plan.source_sequence) =
                                sourceMismatch at run
                            cases sourceMismatch with
                            | true => simp at run
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte] at run
                              generalize treeMismatchRun :
                                (sourceTreeSequence != plan.source_sequence) =
                                  treeMismatch at run
                              cases treeMismatch with
                              | true => simp at run
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte] at run
                                generalize sourceRootEndRun : treeOffset +
                                  prepared_settlement.TREE_FRONTIER_RELATIVE_OFFSET =
                                    sourceRootEndResult at run
                                cases sourceRootEndResult with
                                | fail error => simp at run
                                | div => simp at run
                                | ok sourceRootEnd =>
                                  simp only [bind_tc_ok] at run
                                  generalize sourceRootSliceRun :
                                    core.array.Array.index
                                      (core.ops.index.IndexSlice
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8)) source
                                      { start := treeRootOffset,
                                        «end» := sourceRootEnd } =
                                          sourceRootSliceResult at run
                                  cases sourceRootSliceResult with
                                  | fail error => simp at run
                                  | div => simp at run
                                  | ok sourceRoot =>
                                    simp only [bind_tc_ok] at run
                                    generalize sourceRootEncodingRun :
                                      aspis_statement.atomic_statement.encode_digest_canonical
                                        plan.source_root = sourceRootEncodingResult at run
                                    cases sourceRootEncodingResult with
                                    | fail error => simp at run
                                    | div => simp at run
                                    | ok sourceRootBytes =>
                                      simp only [bind_tc_ok] at run
                                      generalize sourceRootCompareRun :
                                        Slice.Insts.CoreCmpPartialEqArray.ne
                                          core.cmp.PartialEqU8 sourceRoot
                                          sourceRootBytes = sourceRootMismatchResult at run
                                      cases sourceRootMismatchResult with
                                      | fail error => simp at run
                                      | div => simp at run
                                      | ok sourceRootMismatch =>
                                        cases sourceRootMismatch with
                                        | true => simp at run
                                        | false =>
                                          -- The remainder is the straight-line accepted branch.
                                          simp only [bind_tc_ok,
                                            Bool.false_eq_true, ↓reduceIte] at run
                                          cases kind : plan.transition_kind
                                          all_goals
                                            simp only [kind, bind_tc_ok] at run
                                            let count : Std.U64 :=
                                              match plan.transition_kind with
                                              | .PrivateTransfer => 2#u64
                                              | .Withdrawal => 1#u64
                                            have countExact : count.val =
                                                transitionCount
                                                  plan.transition_kind := by
                                              simp [count, kind, transitionCount]
                                            generalize checkedAddRun :
                                              U64.checked_add plan.source_sequence
                                                count = checkedAddResult at run
                                            have checkedAddConcreteRun :
                                                U64.checked_add plan.source_sequence
                                                  (match plan.transition_kind with
                                                  | .PrivateTransfer => 2#u64
                                                  | .Withdrawal => 1#u64) =
                                                    checkedAddResult := by
                                              simpa [count] using checkedAddRun
                                            simp only [kind] at checkedAddConcreteRun
                                            rw [checkedAddConcreteRun] at run
                                            cases checkedAddResult with
                                            | none =>
                                              simp only [core.option.Option.ok_or,
                                                core.result.Result.Insts.CoreOpsTry.branch,
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                                bind_tc_ok] at run
                                              generalize conversionRun :
                                                solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from
                                                  error.PoolV1ProgramError.ArithmeticOverflow =
                                                    conversionResult at run
                                              cases conversionResult <;> simp at run
                                            | some finalSequence =>
                                              simp only [core.option.Option.ok_or,
                                                core.result.Result.Insts.CoreOpsTry.branch,
                                                bind_tc_ok] at run
                                              generalize finalReceiptRun :
                                                core.option.Option.unwrap_or
                                                  plan.second_receipt
                                                  plan.first_receipt =
                                                    finalReceipt at run
                                              generalize locationRun :
                                                aspis_statement.pool_v1.root_history.root_history_location
                                                  finalSequence = locationResult at run
                                              cases locationResult with
                                              | fail error => simp at run
                                              | div => simp at run
                                              | ok location =>
                                                simp only [bind_tc_ok] at run
                                                generalize prefixNextRun :
                                                  core.array.Array.index
                                                    (core.ops.index.IndexSlice
                                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                                        Std.U8))
                                                    plan.next_pool_image
                                                    { «end» := 40#usize } =
                                                      prefixNextResult at run
                                                cases prefixNextResult with
                                                | fail error => simp at run
                                                | div => simp at run
                                                | ok prefixNext =>
                                                  simp only [bind_tc_ok] at run
                                                  generalize prefixSourceRun :
                                                    core.array.Array.index
                                                      (core.ops.index.IndexSlice
                                                        (core.slice.index.SliceIndexRangeToUsizeSlice
                                                          Std.U8)) source
                                                      { «end» := 40#usize } =
                                                        prefixSourceResult at run
                                                  cases prefixSourceResult with
                                                  | fail error => simp at run
                                                  | div => simp at run
                                                  | ok prefixSource =>
                                                    simp only [bind_tc_ok] at run
                                                    generalize prefixCompareRun :
                                                      core.cmp.PartialEq.ne.trait_default
                                                        (Slice.Insts.CoreCmpPartialEqSlice
                                                          core.cmp.PartialEqU8)
                                                        prefixNext prefixSource =
                                                          prefixMismatchResult at run
                                                    cases prefixMismatchResult with
                                                    | fail error => simp at run
                                                    | div => simp at run
                                                    | ok prefixMismatch =>
                                                      cases prefixMismatch with
                                                      | true => simp at run
                                                      | false =>
                                                        simp only [bind_tc_ok,
                                                          Bool.false_eq_true,
                                                          ↓reduceIte] at run
                                                        generalize middleNextRun :
                                                          core.array.Array.index
                                                            (core.ops.index.IndexSlice
                                                              (core.slice.index.SliceIndexRangeUsizeSlice
                                                                Std.U8))
                                                            plan.next_pool_image
                                                            { start := 58#usize,
                                                              «end» := treeOffset } =
                                                                middleNextResult at run
                                                        cases middleNextResult with
                                                        | fail error => simp at run
                                                        | div => simp at run
                                                        | ok middleNext =>
                                                          simp only [bind_tc_ok] at run
                                                          generalize middleSourceRun :
                                                            core.array.Array.index
                                                              (core.ops.index.IndexSlice
                                                                (core.slice.index.SliceIndexRangeUsizeSlice
                                                                  Std.U8)) source
                                                              { start := 58#usize,
                                                                «end» := treeOffset } =
                                                                  middleSourceResult at run
                                                          cases middleSourceResult with
                                                          | fail error => simp at run
                                                          | div => simp at run
                                                          | ok middleSource =>
                                                            simp only [bind_tc_ok] at run
                                                            generalize middleCompareRun :
                                                              core.cmp.PartialEq.ne.trait_default
                                                                (Slice.Insts.CoreCmpPartialEqSlice
                                                                  core.cmp.PartialEqU8)
                                                                middleNext middleSource =
                                                                  middleMismatchResult at run
                                                            cases middleMismatchResult with
                                                            | fail error => simp at run
                                                            | div => simp at run
                                                            | ok middleMismatch =>
                                                              cases middleMismatch with
                                                              | true => simp at run
                                                              | false =>
                                                                simp only [bind_tc_ok,
                                                                  Bool.false_eq_true,
                                                                  ↓reduceIte] at run
                                                                generalize treePrefixNextRun :
                                                                  core.array.Array.index
                                                                    (core.ops.index.IndexSlice
                                                                      (core.slice.index.SliceIndexRangeUsizeSlice
                                                                        Std.U8))
                                                                    plan.next_pool_image
                                                                    { start := treeOffset,
                                                                      «end» := treeSequenceOffset } =
                                                                        treePrefixNextResult at run
                                                                cases treePrefixNextResult with
                                                                | fail error => simp at run
                                                                | div => simp at run
                                                                | ok treePrefixNext =>
                                                                  simp only [bind_tc_ok] at run
                                                                  generalize treePrefixSourceRun :
                                                                    core.array.Array.index
                                                                      (core.ops.index.IndexSlice
                                                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                                                          Std.U8)) source
                                                                      { start := treeOffset,
                                                                        «end» := treeSequenceOffset } =
                                                                          treePrefixSourceResult at run
                                                                  cases treePrefixSourceResult with
                                                                  | fail error => simp at run
                                                                  | div => simp at run
                                                                  | ok treePrefixSource =>
                                                                    simp only [bind_tc_ok] at run
                                                                    generalize treePrefixCompareRun :
                                                                      core.cmp.PartialEq.ne.trait_default
                                                                        (Slice.Insts.CoreCmpPartialEqSlice
                                                                          core.cmp.PartialEqU8)
                                                                        treePrefixNext treePrefixSource =
                                                                          treePrefixMismatchResult at run
                                                                    cases treePrefixMismatchResult with
                                                                    | fail error => simp at run
                                                                    | div => simp at run
                                                                    | ok treePrefixMismatch =>
                                                                      cases treePrefixMismatch with
                                                                      | true => simp at run
                                                                      | false =>
                                                                        simp only [bind_tc_ok,
                                                                          Bool.false_eq_true,
                                                                          ↓reduceIte] at run
                                                                        generalize nextSequenceSliceRun :
                                                                          core.array.Array.index
                                                                            (core.ops.index.IndexSlice
                                                                              (core.slice.index.SliceIndexRangeUsizeSlice
                                                                                Std.U8))
                                                                            plan.next_pool_image
                                                                            { start := prepared_settlement.STATE_SEQUENCE_OFFSET,
                                                                              «end» := prepared_settlement.STATE_PAGE_OFFSET } =
                                                                                nextSequenceSliceResult at run
                                                                        cases nextSequenceSliceResult with
                                                                        | fail error => simp at run
                                                                        | div => simp at run
                                                                        | ok nextSequence =>
                                                                          simp only [bind_tc_ok] at run
                                                                          generalize nextSequenceCompareRun :
                                                                            Slice.Insts.CoreCmpPartialEqArray.ne
                                                                              core.cmp.PartialEqU8 nextSequence
                                                                              (core.num.U64.to_le_bytes finalSequence) =
                                                                                nextSequenceMismatchResult at run
                                                                          cases nextSequenceMismatchResult with
                                                                          | fail error => simp at run
                                                                          | div => simp at run
                                                                          | ok nextSequenceMismatch =>
                                                                            cases nextSequenceMismatch with
                                                                            | true => simp at run
                                                                            | false =>
                                                                              simp only [bind_tc_ok,
                                                                                Bool.false_eq_true,
                                                                                ↓reduceIte] at run
                                                                              generalize nextPageSliceRun :
                                                                                core.array.Array.index
                                                                                  (core.ops.index.IndexSlice
                                                                                    (core.slice.index.SliceIndexRangeUsizeSlice
                                                                                      Std.U8))
                                                                                  plan.next_pool_image
                                                                                  { start := prepared_settlement.STATE_PAGE_OFFSET,
                                                                                    «end» := prepared_settlement.STATE_SLOT_OFFSET } =
                                                                                      nextPageSliceResult at run
                                                                              cases nextPageSliceResult with
                                                                              | fail error => simp at run
                                                                              | div => simp at run
                                                                              | ok nextPage =>
                                                                                simp only [bind_tc_ok] at run
                                                                                generalize nextPageCompareRun :
                                                                                  Slice.Insts.CoreCmpPartialEqArray.ne
                                                                                    core.cmp.PartialEqU8 nextPage
                                                                                    (core.num.U64.to_le_bytes
                                                                                      location.page_number) =
                                                                                        nextPageMismatchResult at run
                                                                                cases nextPageMismatchResult with
                                                                                | fail error => simp at run
                                                                                | div => simp at run
                                                                                | ok nextPageMismatch =>
                                                                                  cases nextPageMismatch with
                                                                                  | true => simp at run
                                                                                  | false =>
                                                                                    simp only [bind_tc_ok,
                                                                                      Bool.false_eq_true,
                                                                                      ↓reduceIte] at run
                                                                                    generalize nextSlotSliceRun :
                                                                                      core.array.Array.index
                                                                                        (core.ops.index.IndexSlice
                                                                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                                                                            Std.U8))
                                                                                        plan.next_pool_image
                                                                                        { start := prepared_settlement.STATE_SLOT_OFFSET,
                                                                                          «end» := 58#usize } =
                                                                                            nextSlotSliceResult at run
                                                                                    cases nextSlotSliceResult with
                                                                                    | fail error => simp at run
                                                                                    | div => simp at run
                                                                                    | ok nextSlot =>
                                                                                      simp only [bind_tc_ok] at run
                                                                                      generalize nextSlotCompareRun :
                                                                                        Slice.Insts.CoreCmpPartialEqArray.ne
                                                                                          core.cmp.PartialEqU8 nextSlot
                                                                                          (core.num.U16.to_le_bytes
                                                                                            location.slot) =
                                                                                              nextSlotMismatchResult at run
                                                                                      cases nextSlotMismatchResult with
                                                                                      | fail error => simp at run
                                                                                      | div => simp at run
                                                                                      | ok nextSlotMismatch =>
                                                                                        cases nextSlotMismatch with
                                                                                        | true => simp at run
                                                                                        | false =>
                                                                                          simp only [bind_tc_ok,
                                                                                            Bool.false_eq_true,
                                                                                            ↓reduceIte] at run
                                                                                          generalize nextTreeSequenceSliceRun :
                                                                                            core.array.Array.index
                                                                                              (core.ops.index.IndexSlice
                                                                                                (core.slice.index.SliceIndexRangeUsizeSlice
                                                                                                  Std.U8))
                                                                                              plan.next_pool_image
                                                                                              { start := treeSequenceOffset,
                                                                                                «end» := treeRootOffset } =
                                                                                                  nextTreeSequenceSliceResult at run
                                                                                          cases nextTreeSequenceSliceResult with
                                                                                          | fail error => simp at run
                                                                                          | div => simp at run
                                                                                          | ok nextTreeSequence =>
                                                                                            simp only [bind_tc_ok] at run
                                                                                            generalize nextTreeSequenceCompareRun :
                                                                                              Slice.Insts.CoreCmpPartialEqArray.ne
                                                                                                core.cmp.PartialEqU8 nextTreeSequence
                                                                                                (core.num.U64.to_le_bytes
                                                                                                  finalSequence) =
                                                                                                    nextTreeSequenceMismatchResult at run
                                                                                            cases nextTreeSequenceMismatchResult with
                                                                                            | fail error => simp at run
                                                                                            | div => simp at run
                                                                                            | ok nextTreeSequenceMismatch =>
                                                                                              cases nextTreeSequenceMismatch with
                                                                                              | true => simp at run
                                                                                              | false =>
                                                                                                simp only [bind_tc_ok,
                                                                                                  Bool.false_eq_true,
                                                                                                  ↓reduceIte] at run
                                                                                                generalize nextRootSliceRun :
                                                                                                  core.array.Array.index
                                                                                                    (core.ops.index.IndexSlice
                                                                                                      (core.slice.index.SliceIndexRangeUsizeSlice
                                                                                                        Std.U8))
                                                                                                    plan.next_pool_image
                                                                                                    { start := treeRootOffset,
                                                                                                      «end» := sourceRootEnd } =
                                                                                                        nextRootSliceResult at run
                                                                                                cases nextRootSliceResult with
                                                                                                | fail error => simp at run
                                                                                                | div => simp at run
                                                                                                | ok nextRoot =>
                                                                                                  simp only [bind_tc_ok] at run
                                                                                                  generalize nextRootEncodingRun :
                                                                                                    aspis_statement.atomic_statement.encode_digest_canonical
                                                                                                      finalReceipt.root =
                                                                                                        nextRootEncodingResult at run
                                                                                                  cases nextRootEncodingResult with
                                                                                                  | fail error => simp at run
                                                                                                  | div => simp at run
                                                                                                  | ok nextRootBytes =>
                                                                                                    simp only [bind_tc_ok] at run
                                                                                                    generalize nextRootCompareRun :
                                                                                                      Slice.Insts.CoreCmpPartialEqArray.ne
                                                                                                        core.cmp.PartialEqU8 nextRoot
                                                                                                        nextRootBytes =
                                                                                                          nextRootMismatchResult at run
                                                                                                    cases nextRootMismatchResult with
                                                                                                    | fail error => simp at run
                                                                                                    | div => simp at run
                                                                                                    | ok nextRootMismatch =>
                                                                                                      cases nextRootMismatch with
                                                                                                      | true => simp at run
                                                                                                      | false =>
                                                                                                        simp only [bind_tc_ok,
                                                                                                          Bool.false_eq_true,
                                                                                                          ↓reduceIte] at run
                                                                                                        generalize identityStartRun :
                                                                                                          state.POOL_V1_STATE_IDENTITY_OFFSET +
                                                                                                            8#usize = identityStartResult at run
                                                                                                        cases identityStartResult with
                                                                                                        | fail error => simp at run
                                                                                                        | div => simp at run
                                                                                                        | ok identityStart =>
                                                                                                          simp only [bind_tc_ok] at run
                                                                                                          generalize identityEndRun :
                                                                                                            state.POOL_V1_STATE_IDENTITY_OFFSET +
                                                                                                              40#usize = identityEndResult at run
                                                                                                          cases identityEndResult with
                                                                                                          | fail error => simp at run
                                                                                                          | div => simp at run
                                                                                                          | ok identityEnd =>
                                                                                                            simp only [bind_tc_ok] at run
                                                                                                            generalize identitySliceRun :
                                                                                                              core.array.Array.index
                                                                                                                (core.ops.index.IndexSlice
                                                                                                                  (core.slice.index.SliceIndexRangeUsizeSlice
                                                                                                                    Std.U8))
                                                                                                                plan.next_pool_image
                                                                                                                { start := identityStart,
                                                                                                                  «end» := identityEnd } =
                                                                                                                    identitySliceResult at run
                                                                                                            cases identitySliceResult with
                                                                                                            | fail error => simp at run
                                                                                                            | div => simp at run
                                                                                                            | ok identity =>
                                                                                                              simp only [bind_tc_ok] at run
                                                                                                              generalize identityCompareRun :
                                                                                                                Slice.Insts.CoreCmpPartialEqArray.ne
                                                                                                                  core.cmp.PartialEqU8 identity
                                                                                                                  plan.pool =
                                                                                                                    identityMismatchResult at run
                                                                                                              cases identityMismatchResult with
                                                                                                              | fail error => simp at run
                                                                                                              | div => simp at run
                                                                                                              | ok identityMismatch =>
                                                                                                                cases identityMismatch with
                                                                                                                | true => simp at run
                                                                                                                | false =>
                                                                                                                  refine ⟨sourceSequence,
                                                                                                                    sourceTreeSequence, count,
                                                                                                                    finalSequence, finalReceipt,
                                                                                                                    location, sourceRoot,
                                                                                                                    nextSequence, nextPage,
                                                                                                                    nextSlot, nextTreeSequence,
                                                                                                                    nextRoot, identity,
                                                                                                                    sourceRootBytes,
                                                                                                                    nextRootBytes,
                                                                                                                    core.num.U64.to_le_bytes
                                                                                                                      finalSequence,
                                                                                                                    core.num.U64.to_le_bytes
                                                                                                                      location.page_number,
                                                                                                                    core.num.U64.to_le_bytes
                                                                                                                      finalSequence,
                                                                                                                    core.num.U16.to_le_bytes
                                                                                                                      location.slot,
                                                                                                                    sourceMismatchRun,
                                                                                                                    treeMismatchRun, ?_,
                                                                                                                    checkedAddRun, rfl,
                                                                                                                    locationRun, rfl,
                                                                                                                    sourceRootCompareRun, rfl,
                                                                                                                    nextSequenceCompareRun,
                                                                                                                    rfl, nextPageCompareRun,
                                                                                                                    rfl, nextSlotCompareRun,
                                                                                                                    rfl,
                                                                                                                    nextTreeSequenceCompareRun,
                                                                                                                    nextRootEncodingRun,
                                                                                                                    nextRootCompareRun,
                                                                                                                    identityCompareRun⟩
                                                                                                                  simpa [kind] using countExact

#print axioms literal_source_state_result_image_success_has_exact_checks

end PoolV1SourceStateResultImageBridge
