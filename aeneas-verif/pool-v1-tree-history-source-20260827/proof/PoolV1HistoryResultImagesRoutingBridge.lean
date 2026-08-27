import PoolV1HistoryResultImages.Funs

/-!
# Pool V1 literal result-image current/rollover routing bridge

This theorem follows the production prepared-settlement result-image checker.
It exposes its exact root-page validation and checked distribution call, then
proves the deployed option grammar: zero rollover roots requires all three
next-page values to be absent; a nonzero rollover requires all three to be
present.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace PoolV1HistoryResultImagesRoutingBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1HistoryResultImages

def transitionCount :
    aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind → Nat
  | .PrivateTransfer => 2
  | .Withdrawal => 1

theorem history_result_images_success_has_exact_page_route
    (programId pool : solana_pubkey.Pubkey)
    (plan : prepared_settlement_format.PreparedSettlementPlanViewV1)
    (sourceCurrent : Array Std.U8 8256#usize)
    (sourceNext : Option (Array Std.U8 8256#usize))
    (run : prepared_settlement.history_result_images_match
      programId pool plan sourceCurrent sourceNext = .ok (.Ok ())) :
    ∃ location : aspis_statement.pool_v1.root_history.RootHistoryLocationV1,
      ∃ header : history.RootPageHeaderV1,
      ∃ count : Std.U64, ∃ current next : Std.Usize,
        aspis_statement.pool_v1.root_history.root_history_location
            plan.source_sequence = .ok location ∧
        history.validate_root_page_bytes sourceCurrent.to_slice pool
            location.page_number = .ok (.Ok header) ∧
        count.val = transitionCount plan.transition_kind ∧
        prepared_settlement.checked_history_distribution
            plan.source_sequence header count = .ok (.Ok (current, next)) ∧
        ((next.val = 0 ∧ plan.next_page_address = none ∧
            sourceNext = none ∧ plan.next_rollover_page_image = none) ∨
          (next.val ≠ 0 ∧
            ∃ address source result,
              plan.next_page_address = some address ∧
              sourceNext = some source ∧
              plan.next_rollover_page_image = some result)) := by
  unfold prepared_settlement.history_result_images_match at run
  generalize locationRun :
    aspis_statement.pool_v1.root_history.root_history_location
      plan.source_sequence = locationResult at run
  cases locationResult with
  | fail error => simp at run
  | div => simp at run
  | ok location =>
    simp only [bind_tc_ok, lift] at run
    generalize validationRun : history.validate_root_page_bytes
      sourceCurrent.to_slice pool location.page_number = validationResult at run
    cases validationResult with
    | fail error => simp at run
    | div => simp at run
    | ok validation =>
      cases validation with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          at run
      | Ok header =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at run
        generalize filledRun : location.slot + 1#u16 = filledResult at run
        cases filledResult with
        | fail error => simp at run
        | div => simp at run
        | ok expectedFilled =>
          simp only [bind_tc_ok] at run
          by_cases filledMismatch : header.filled ≠ expectedFilled
          · simp [filledMismatch] at run
          · have filledExact : header.filled = expectedFilled :=
              not_ne_iff.mp filledMismatch
            have filledValueExact : header.filled.val = expectedFilled.val :=
              congrArg UScalar.val filledExact
            have mismatchFalse : (header.filled != expectedFilled) = false := by
              simp [filledExact]
            rw [mismatchFalse] at run
            simp only [Bool.false_eq_true, ↓reduceIte] at run
            generalize addressRun : history.pool_v1_root_page_address
              programId pool location.page_number = addressResult at run
            cases addressResult with
            | fail error => simp at run
            | div => simp at run
            | ok derivedAddress =>
              rcases derivedAddress with ⟨pageAddress, bump⟩
              simp (config := { zeta := true }) only
                [bind_tc_ok, Prod.rec, Prod.fst, Prod.snd] at run
              simp only [solana_pubkey.Pubkey.to_bytes, bind_tc_ok] at run
              change (do
                let mismatch ←
                  core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                    plan.current_page_address pageAddress
                if mismatch then _ else _) =
                  Result.ok (core.result.Result.Ok ()) at run
              generalize addressCompareRun :
                core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
                  plan.current_page_address pageAddress = compareResult at run
              cases compareResult with
              | fail error => simp at run
              | div => simp at run
              | ok addressMismatch =>
                cases addressMismatch with
                | true => simp at run
                | false =>
                  change (do
                    let count ←
                      match plan.transition_kind with
                      | .PrivateTransfer =>
                          (Result.ok 2#u64 : Result Std.U64)
                      | .Withdrawal => Result.ok 1#u64
                    _) = Result.ok (core.result.Result.Ok ()) at run
                  generalize countRun :
                    (match plan.transition_kind with
                    | .PrivateTransfer => (Result.ok 2#u64 : Result Std.U64)
                    | .Withdrawal => Result.ok 1#u64) = countResult at run
                  cases countResult with
                  | fail error => simp at run
                  | div => simp at run
                  | ok count =>
                    simp only [bind_tc_ok] at run
                    have countExact :
                        count.val = transitionCount plan.transition_kind := by
                      cases kind : plan.transition_kind
                      · rw [kind] at countRun
                        cases countRun
                        rfl
                      · rw [kind] at countRun
                        cases countRun
                        rfl
                    generalize distributionRun :
                      prepared_settlement.checked_history_distribution
                        plan.source_sequence header count =
                          distributionResult at run
                    cases distributionResult with
                    | fail error => simp at run
                    | div => simp at run
                    | ok distribution =>
                      cases distribution with
                      | Err error =>
                        simp [core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                          at run
                      | Ok routed =>
                        rcases routed with ⟨current, next⟩
                        simp only [core.result.Result.Insts.CoreOpsTry.branch,
                          bind_tc_ok] at run
                        change (do
                          let roots ← prepared_settlement.append_roots
                            { first := plan.first_receipt,
                              second := plan.second_receipt }
                          _) = Result.ok (core.result.Result.Ok ()) at run
                        generalize appendRun :
                          prepared_settlement.append_roots
                            { first := plan.first_receipt,
                              second := plan.second_receipt } = appendResult at run
                        cases appendResult with
                        | fail error => simp at run
                        | div => simp at run
                        | ok appended =>
                          cases appended with
                          | Err error =>
                            simp [core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                              at run
                          | Ok roots =>
                            simp only [core.result.Result.Insts.CoreOpsTry.branch,
                              bind_tc_ok] at run
                            generalize zeroedRun :
                              prepared_settlement.zeroed_page_box = zeroedResult at run
                            cases zeroedResult with
                            | fail error => simp at run
                            | div => simp at run
                            | ok zeroed =>
                              cases zeroed with
                              | Err error =>
                                simp [core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
                                  at run
                              | Ok pageBox =>
                                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                                  bind_tc_ok] at run
                                generalize sliceRun :
                                  Array.to_slice_mut pageBox = slicePair
                                rcases slicePair with ⟨pageSlice, pageBack⟩
                                rw [sliceRun] at run
                                change (do
                                  let copied ← core.slice.Slice.copy_from_slice
                                    core.marker.CopyU8 pageSlice sourceCurrent.to_slice
                                  _) = Result.ok (core.result.Result.Ok ()) at run
                                generalize copyRun :
                                  core.slice.Slice.copy_from_slice core.marker.CopyU8
                                    pageSlice sourceCurrent.to_slice = copyResult at run
                                cases copyResult with
                                | fail error => simp at run
                                | div => simp at run
                                | ok copied =>
                                  simp only [bind_tc_ok] at run
                                  generalize currentNonzeroRun :
                                    (current != 0#usize) = currentNonzero at run
                                  cases currentNonzero with
                                  | false =>
                                    simp only [Bool.false_eq_true, ↓reduceIte,
                                      bind_tc_ok] at run
                                    generalize asRefRun :
                                      Box.Insts.CoreConvertAsRef.as_ref Global
                                        (pageBack copied) = asRefResult at run
                                    cases asRefResult with
                                    | fail error => simp at run
                                    | div => simp at run
                                    | ok expectedSlice =>
                                      simp only [bind_tc_ok] at run
                                      generalize currentCompareRun :
                                        core.cmp.impls.PartialEqShared.ne
                                          (Array.Insts.CoreCmpPartialEqArray
                                            8256#usize core.cmp.PartialEqU8)
                                          expectedSlice plan.next_current_page_image =
                                            currentCompareResult at run
                                      cases currentCompareResult with
                                      | fail error => simp at run
                                      | div => simp at run
                                      | ok currentMismatch =>
                                        cases currentMismatch with
                                        | true => simp at run
                                        | false =>
                                          change (match next.val with
                                            | 0 => _
                                            | _ => _) =
                                              Result.ok
                                                (core.result.Result.Ok ()) at run
                                          cases nextValue : next.val with
                                          | zero =>
                                            cases pageOpt : plan.next_page_address <;>
                                              cases nextOpt : sourceNext <;>
                                              cases resultOpt :
                                                plan.next_rollover_page_image <;>
                                              simp [nextValue, pageOpt, nextOpt,
                                                resultOpt] at run
                                            exact ⟨location, header, count, current,
                                              next, rfl, validationRun, countExact,
                                              distributionRun,
                                              Or.inl ⟨nextValue, rfl, rfl, rfl⟩⟩
                                          | succ successor =>
                                            cases pageOpt : plan.next_page_address with
                                            | none =>
                                              simp [nextValue, pageOpt] at run
                                            | some address =>
                                              cases nextOpt : sourceNext with
                                              | none =>
                                                simp [nextValue, pageOpt, nextOpt] at run
                                              | some source =>
                                                cases resultOpt :
                                                    plan.next_rollover_page_image with
                                                | none =>
                                                  simp [nextValue, pageOpt, nextOpt,
                                                    resultOpt] at run
                                                | some result =>
                                                  exact ⟨location, header, count,
                                                    current, next, rfl, validationRun,
                                                    countExact, distributionRun,
                                                    Or.inr ⟨by omega, address,
                                                      source, result, rfl, rfl,
                                                      rfl⟩⟩
                                  | true =>
                                    simp only [↓reduceIte] at run
                                    generalize asMutRun :
                                      alloc.boxed.AsMutBox.as_mut (pageBack copied) =
                                        asMutPair
                                    rcases asMutPair with ⟨rootArray, rootArrayBack⟩
                                    rw [asMutRun] at run
                                    change (do
                                      let expectedCurrent ←
                                        match Array.to_slice_mut rootArray with
                                        | (rootSlice, rootSliceBack) => do
                                          let selected ← core.array.Array.index
                                            (core.ops.index.IndexSlice
                                              (core.slice.index.SliceIndexRangeToUsizeSlice
                                                (Array aspis_core.field.M31 8#usize)))
                                            roots { «end» := current }
                                          let updated ← history.append_roots_unchecked
                                            rootSlice header selected
                                          Result.ok
                                            (rootArrayBack (rootSliceBack updated))
                                      _) = Result.ok (core.result.Result.Ok ()) at run
                                    generalize rootSliceRun :
                                      Array.to_slice_mut rootArray = rootSlicePair
                                    rcases rootSlicePair with
                                      ⟨rootSlice, rootSliceBack⟩
                                    rw [rootSliceRun] at run
                                    change (do
                                      let expectedCurrent ← do
                                        let selected ← core.array.Array.index
                                          (core.ops.index.IndexSlice
                                            (core.slice.index.SliceIndexRangeToUsizeSlice
                                              (Array aspis_core.field.M31 8#usize)))
                                          roots { «end» := current }
                                        let updated ← history.append_roots_unchecked
                                          rootSlice header selected
                                        Result.ok
                                          (rootArrayBack (rootSliceBack updated))
                                      _) = Result.ok (core.result.Result.Ok ()) at run
                                    generalize selectedRun :
                                      core.array.Array.index
                                        (core.ops.index.IndexSlice
                                          (core.slice.index.SliceIndexRangeToUsizeSlice
                                            (Array aspis_core.field.M31 8#usize)))
                                        roots { «end» := current } = selectedResult at run
                                    cases selectedResult with
                                    | fail error => simp at run
                                    | div => simp at run
                                    | ok selected =>
                                      simp only [bind_tc_ok] at run
                                      generalize updateRun :
                                        history.append_roots_unchecked
                                          rootSlice header selected = updateResult at run
                                      cases updateResult with
                                      | fail error => simp at run
                                      | div => simp at run
                                      | ok updated =>
                                        simp only [bind_tc_ok] at run
                                        generalize asRefRun :
                                          Box.Insts.CoreConvertAsRef.as_ref Global
                                            (rootArrayBack (rootSliceBack updated)) =
                                              asRefResult at run
                                        cases asRefResult with
                                        | fail error => simp at run
                                        | div => simp at run
                                        | ok expectedSlice =>
                                          simp only [bind_tc_ok] at run
                                          generalize currentCompareRun :
                                            core.cmp.impls.PartialEqShared.ne
                                              (Array.Insts.CoreCmpPartialEqArray
                                                8256#usize core.cmp.PartialEqU8)
                                              expectedSlice
                                                plan.next_current_page_image =
                                                  currentCompareResult at run
                                          cases currentCompareResult with
                                          | fail error => simp at run
                                          | div => simp at run
                                          | ok currentMismatch =>
                                            cases currentMismatch with
                                            | true => simp at run
                                            | false =>
                                              change (match next.val with
                                                | 0 => _
                                                | _ => _) =
                                                  Result.ok
                                                    (core.result.Result.Ok ()) at run
                                              cases nextValue : next.val with
                                              | zero =>
                                                cases pageOpt :
                                                    plan.next_page_address <;>
                                                  cases nextOpt : sourceNext <;>
                                                  cases resultOpt :
                                                    plan.next_rollover_page_image <;>
                                                  simp [nextValue, pageOpt, nextOpt,
                                                    resultOpt] at run
                                                exact ⟨location, header, count,
                                                  current, next, rfl, validationRun,
                                                  countExact, distributionRun,
                                                  Or.inl ⟨nextValue, rfl, rfl,
                                                    rfl⟩⟩
                                              | succ successor =>
                                                cases pageOpt :
                                                    plan.next_page_address with
                                                | none =>
                                                  simp [nextValue, pageOpt] at run
                                                | some address =>
                                                  cases nextOpt : sourceNext with
                                                  | none =>
                                                    simp [nextValue, pageOpt,
                                                      nextOpt] at run
                                                  | some source =>
                                                    cases resultOpt :
                                                        plan.next_rollover_page_image with
                                                    | none =>
                                                      simp [nextValue, pageOpt,
                                                        nextOpt, resultOpt] at run
                                                    | some result =>
                                                      exact ⟨location, header,
                                                        count, current, next, rfl,
                                                        validationRun, countExact,
                                                        distributionRun,
                                                        Or.inr ⟨by omega, address,
                                                          source, result, rfl, rfl,
                                                          rfl⟩⟩

#print axioms history_result_images_success_has_exact_page_route

end PoolV1HistoryResultImagesRoutingBridge
