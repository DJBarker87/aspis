import PoolV1NormalizedNewPageData.Funs

/-!
# Pool V1 normalized new-page data source bridge

The Solana runtime account borrow is intentionally outside this module.  The
verification-only Rust normalization begins with the exact byte slice returned
by that borrow and keeps the production 8,256-byte and all-zero checks literal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace PoolV1NormalizedNewPageDataBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1NormalizedNewPageData

theorem anyAux_false_predicate_at
    {T : Type} (predicate : core.ops.function.FnMut Unit T Bool)
    (test : T → Bool)
    (predicateExact : ∀ value,
      predicate.call_mut () value = Result.ok (test value, ())) :
    ∀ (fuel : Nat) (slice : Slice T) (i : Nat)
      (final : core.slice.iter.Iter T) (j : Nat),
      ∀ (hij : i ≤ j) (hj : j < slice.len) (hFuel : j - i < fuel),
      core.slice.iter.Iter.anyAux predicate fuel ⟨slice, i⟩ () =
          Result.ok (false, final, ()) →
      test (slice[j]'hj) = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro slice i final j hij hj hFuel run
    omega
  | succ fuel ih =>
    intro slice i final j hij hj hFuel run
    unfold core.slice.iter.Iter.anyAux at run
    have hi : i < slice.len := lt_of_le_of_lt hij hj
    simp only [core.slice.iter.IteratorSliceIter.next] at run
    rw [dif_pos hi] at run
    simp only [bind_tc_ok, predicateExact] at run
    change (if test (slice[i]'hi) = true then
      Result.ok (true, ({ slice := slice, i := i + 1 } :
        core.slice.iter.Iter T), ())
    else core.slice.iter.Iter.anyAux predicate fuel
      { slice := slice, i := i + 1 } ()) =
        Result.ok (false, final, ()) at run
    by_cases currentFound : test (slice[i]'hi) = true
    · rw [if_pos currentFound] at run
      simp at run
    · have currentFalse : test (slice[i]'hi) = false :=
        Bool.eq_false_of_not_eq_true currentFound
      rw [if_neg currentFound] at run
      by_cases currentIndex : j = i
      · subst j
        simpa using currentFalse
      · have nextLe : i + 1 ≤ j := by omega
        have remainingFuel : j - (i + 1) < fuel := by omega
        exact ih slice (i + 1) final j nextLe hj remainingFuel run

theorem anyAux_false_all_zero
    (data : Slice Std.U8) (fuel : Nat)
    (final : core.slice.iter.Iter Std.U8)
    (enough : data.length < fuel)
    (run : core.slice.iter.Iter.anyAux
      normalized_validate_new_page_borrowed_data.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
      fuel ⟨data, 0⟩ () = Result.ok (false, final, ())) :
    ∀ j (hj : j < data.length), data.val[j] = 0#u8 := by
  intro j hj
  have predicateExact : ∀ value : Std.U8,
      normalized_validate_new_page_borrowed_data.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut
        () value = Result.ok (value != 0#u8, ()) := by
    intro value
    rfl
  have testedFalse := anyAux_false_predicate_at
    normalized_validate_new_page_borrowed_data.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
    (fun value : Std.U8 => value != 0#u8) predicateExact
    fuel data 0 final j (Nat.zero_le j) (by simpa using hj) (by omega) run
  have sliceZero : data[j]'(by simpa using hj) = 0#u8 :=
    bne_eq_false_iff_eq.mp testedFalse
  have getEq := Slice.getElem_Nat_eq data j hj
  rw [getEq] at sliceZero
  exact sliceZero

theorem normalized_validate_new_page_borrowed_data_success_exact
    (data : Slice Std.U8)
    (run : normalized_validate_new_page_borrowed_data data = .ok true) :
    data.len = 8256#usize ∧
      ∀ j (hj : j < data.length), data.val[j] = 0#u8 := by
  unfold normalized_validate_new_page_borrowed_data at run
  simp only [aspis_statement.pool_v1.root_history.POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    bind_tc_ok] at run
  by_cases lengthExact : data.len = 8256#usize
  · rw [if_pos lengthExact] at run
    simp only [core.slice.Slice.iter, bind_tc_ok] at run
    unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any at run
    dsimp only at run
    simp only [Slice.len_val, Nat.sub_zero] at run
    let fuel := data.length + 1
    let initial : core.slice.iter.Iter Std.U8 := ⟨data, 0⟩
    let aux := core.slice.iter.Iter.anyAux
      normalized_validate_new_page_borrowed_data.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
      fuel initial ()
    have auxRun : core.slice.iter.Iter.anyAux
        normalized_validate_new_page_borrowed_data.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
        fuel initial () = aux := rfl
    rw [auxRun] at run
    cases auxCase : aux with
    | fail error => simp [auxCase] at run
    | div => simp [auxCase] at run
    | ok value =>
      rcases value with ⟨found, final, state⟩
      simp only [auxCase, bind_tc_ok, Bool.not_eq_true] at run
      have foundFalse : found = false := by
        cases found <;> simp_all
      subst found
      have stateUnit : state = () := Subsingleton.elim _ _
      subst state
      refine ⟨lengthExact, ?_⟩
      apply anyAux_false_all_zero data fuel final
      · simp [fuel]
      · have exactRun := auxRun.trans auxCase
        simpa [initial] using exactRun
  · rw [if_neg lengthExact] at run
    simp at run

#print axioms anyAux_false_predicate_at
#print axioms anyAux_false_all_zero
#print axioms normalized_validate_new_page_borrowed_data_success_exact

end PoolV1NormalizedNewPageDataBridge
