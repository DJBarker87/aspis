import PoolV1NormalizedUnique.Funs
import PoolV1MutableAccountStoreBridge

/-!
# Pool V1 normalized account-key uniqueness bridge

The production uniqueness gate reads only account keys.  This extraction-only
projection retains its exact two nested ranges and first-duplicate rejection.
The theorem below pins the critical inner-loop behavior directly to translated
Rust.  Full recursion-to-pairwise composition remains a separate theorem.
-/

set_option autoImplicit false

namespace PoolV1NormalizedUniqueAccountsBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open pool_v1_tree_history_source_harness

def rangeAt (start stop : Std.Usize) : core.ops.range.Range Std.Usize :=
  { start, «end» := stop }

theorem range_at_next
    (start stop : Std.Usize) (active : start.val < stop.val) :
    ∃ next : Std.Usize, next.val = start.val + 1 ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize
          (rangeAt start stop) =
        .ok (.some start, rangeAt next stop) := by
  have startMax : start.val < UScalar.max .Usize := by
    have := stop.hBounds
    scalar_tac
  have inBounds : start.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
    have := stop.hBounds
    omega
  let next : Std.Usize := UScalar.ofNatCore (start.val + 1) inBounds
  refine ⟨next, rfl, ?_⟩
  unfold rangeAt core.iter.range.IteratorRange.next
    core.iter.range.StepUsize core.iter.range.UScalarStep
  simp [core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    Aeneas.Std.liftFun2, active,
    core.clone.CloneUsize, core.clone.impls.CloneUsize.clone,
    core.iter.range.UScalarStep.forward_checked, startMax, next]

theorem range_at_done
    (start stop : Std.Usize) (done : stop.val ≤ start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        (rangeAt start stop) =
      .ok (.none, rangeAt start stop) := by
  unfold rangeAt core.iter.range.IteratorRange.next
    core.iter.range.StepUsize core.iter.range.UScalarStep
  simp [core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    Aeneas.Std.liftFun2, done,
    core.clone.CloneUsize, core.clone.impls.CloneUsize.clone]

private theorem list_allM_u8_self_is_true :
    ∀ (values : List Std.U8),
      List.allM (fun pair : Std.U8 × Std.U8 =>
        Result.ok (decide (pair.1.val = pair.2.val)))
        (List.zip values values) = Result.ok true := by
  intro values
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [List.allM, ih]

private theorem list_allM_u8_is_ok :
    ∀ (pairs : List (Std.U8 × Std.U8)), ∃ result : Bool,
      List.allM (fun pair : Std.U8 × Std.U8 =>
        Result.ok (decide (pair.1.val = pair.2.val))) pairs =
        Result.ok result := by
  intro pairs
  induction pairs with
  | nil => exact ⟨true, rfl⟩
  | cons pair tail ih =>
      rcases ih with ⟨tailResult, tailRun⟩
      by_cases equal : pair.1.val = pair.2.val
      · exact ⟨tailResult, by simp [List.allM, equal, tailRun, pure]⟩
      · exact ⟨false, by simp [List.allM, equal, pure]⟩

theorem partial_eq_u8_array_refl
    (key : Array Std.U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 key key =
      .ok true := by
  unfold core.array.equality.PartialEqArray.eq
  simp only [Array.length, ↓reduceIte]
  simpa [core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.ne,
    Aeneas.Std.liftFun2] using list_allM_u8_self_is_true key.val

theorem partial_eq_u8_array_is_ok
    (left right : Array Std.U8 32#usize) : ∃ result : Bool,
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right =
      .ok result := by
  unfold core.array.equality.PartialEqArray.eq
  simp only [Array.length, ↓reduceIte]
  simpa [core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.ne,
    Aeneas.Std.liftFun2] using list_allM_u8_is_ok (List.zip left.val right.val)

theorem partial_eq_u8_array_false_implies_ne
    (left right : Array Std.U8 32#usize)
    (run : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      left right = .ok false) : left ≠ right := by
  intro equal
  subst right
  rw [partial_eq_u8_array_refl left] at run
  cases run

theorem slice_index_usize_eq
    (keys : Slice (Array Std.U8 32#usize)) (index : Std.Usize)
    (bound : index.val < keys.val.length) :
    Slice.index_usize keys index = .ok keys.val[index.val] := by
  have spec := Slice.index_usize_spec keys index (by simpa using bound)
  cases run : Slice.index_usize keys index with
  | fail error => simp [run] at spec
  | div => simp [run] at spec
  | ok value =>
      simp [run] at spec
      simpa [run, spec]

inductive InnerDistinctTrace
    (keys : Slice (Array Std.U8 32#usize)) (left stop : Std.Usize) :
    Std.Usize → Prop
  | done (start : Std.Usize) (pastEnd : stop.val ≤ start.val) :
      InnerDistinctTrace keys left stop start
  | step (start next : Std.Usize)
      (active : start.val < stop.val)
      (nextValue : next.val = start.val + 1)
      (distinct : keys.val[left.val]? ≠ keys.val[start.val]?)
      (tail : InnerDistinctTrace keys left stop next) :
      InnerDistinctTrace keys left stop start

theorem inner_loop_success_is_false_or_distinct
    (keys : Slice (Array Std.U8 32#usize))
    (left start stop : Std.Usize)
    (leftBound : left.val < keys.val.length)
    (stopBound : stop.val ≤ keys.val.length)
    (result : Option Bool)
    (run : normalized_require_unique_account_keys_loop0_loop0
      (rangeAt start stop) keys left = .ok result) :
    result = some false ∨
      (result = none ∧ InnerDistinctTrace keys left stop start) := by
  unfold normalized_require_unique_account_keys_loop0_loop0 at run
  rw [loop.eq_def] at run
  by_cases active : start.val < stop.val
  · obtain ⟨next, nextValue, nextRun⟩ := range_at_next start stop active
    have startBound : start.val < keys.val.length := by omega
    have leftRun := slice_index_usize_eq keys left leftBound
    have rightRun := slice_index_usize_eq keys start startBound
    generalize bodyRun :
      normalized_require_unique_account_keys_loop0_loop0.body
        keys left (rangeAt start stop) = bodyResult at run
    unfold normalized_require_unique_account_keys_loop0_loop0.body at bodyRun
    rw [nextRun] at bodyRun
    simp only [bind_tc_ok] at bodyRun
    rw [leftRun] at bodyRun
    simp only [bind_tc_ok] at bodyRun
    change (do
      let selected ← Slice.index_usize keys start
      let equal ← core.array.equality.PartialEqArray.eq
        core.cmp.PartialEqU8 keys.val[left.val] selected
      if equal then ok (done (some false)) else ok (cont (rangeAt next stop))) =
        bodyResult at bodyRun
    rw [rightRun] at bodyRun
    simp only [bind_tc_ok] at bodyRun
    obtain ⟨equal, compareRun⟩ := partial_eq_u8_array_is_ok
      keys.val[left.val] keys.val[start.val]
    rw [compareRun] at bodyRun
    cases equal with
    | true =>
        simp at bodyRun
        subst bodyResult
        simp at run
        exact Or.inl run.symm
    | false =>
        simp at bodyRun
        subst bodyResult
        simp only [bind_tc_ok] at run
        rcases inner_loop_success_is_false_or_distinct keys left next stop
            leftBound stopBound result run with falseResult | ⟨noneResult, tail⟩
        · exact Or.inl falseResult
        · exact Or.inr ⟨noneResult,
            InnerDistinctTrace.step start next active nextValue
              (by
                rw [getElem?_pos keys.val left.val leftBound,
                  getElem?_pos keys.val start.val startBound]
                intro optionsEqual
                exact (partial_eq_u8_array_false_implies_ne _ _ compareRun)
                  (Option.some.inj optionsEqual)) tail⟩
  · have pastEnd : stop.val ≤ start.val := by omega
    have nextRun := range_at_done start stop pastEnd
    unfold normalized_require_unique_account_keys_loop0_loop0.body at run
    rw [nextRun] at run
    simp at run
    exact Or.inr ⟨run.symm, InnerDistinctTrace.done start pastEnd⟩
termination_by stop.val - start.val
decreasing_by omega

theorem inner_loop_none_has_distinct_trace
    (keys : Slice (Array Std.U8 32#usize))
    (left start stop : Std.Usize)
    (leftBound : left.val < keys.val.length)
    (stopBound : stop.val ≤ keys.val.length)
    (run : normalized_require_unique_account_keys_loop0_loop0
      (rangeAt start stop) keys left = .ok none) :
    InnerDistinctTrace keys left stop start := by
  rcases inner_loop_success_is_false_or_distinct keys left start stop
      leftBound stopBound none run with falseResult | ⟨_, trace⟩
  · cases falseResult
  · exact trace

theorem inner_distinct_trace_covers
    (keys : Slice (Array Std.U8 32#usize))
    (left stop start : Std.Usize)
    (trace : InnerDistinctTrace keys left stop start) :
    ∀ index : Nat, start.val ≤ index → index < stop.val →
      keys.val[left.val]? ≠ keys.val[index]? := by
  induction trace with
  | done current pastEnd =>
      intro index lower upper
      omega
  | step current next active nextValue distinct tail ih =>
      intro index lower upper
      by_cases here : index = current.val
      · simpa [here] using distinct
      · exact ih index (by omega) upper

theorem usize_add_one_eq
    (value next : Std.Usize)
    (nextValue : next.val = value.val + 1) :
    (value + 1#usize) = Result.ok next := by
  have addSpec := @UScalar.add_equiv .Usize value 1#usize
  cases addRun : value + 1#usize with
  | fail error =>
      rw [addRun] at addSpec
      simp [UScalar.inBounds] at addSpec
      have nextBound : value.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
        rw [← nextValue]
        exact next.hBounds
      simp only [UScalarTy.Usize_numBits_eq] at nextBound
      omega
  | div =>
      rw [addRun] at addSpec
      simp at addSpec
  | ok actual =>
      rw [addRun] at addSpec
      have actualNext : actual = next := by
        apply UScalar.eq_of_val_eq
        exact addSpec.2.1.trans nextValue.symm
      simpa [actualNext] using addRun

inductive OuterDistinctTrace
    (keys : Slice (Array Std.U8 32#usize)) : Std.Usize → Prop
  | done (start : Std.Usize)
      (pastEnd : keys.val.length ≤ start.val) :
      OuterDistinctTrace keys start
  | step (left next : Std.Usize)
      (active : left.val < keys.val.length)
      (nextValue : next.val = left.val + 1)
      (inner : InnerDistinctTrace keys left (Slice.len keys) next)
      (tail : OuterDistinctTrace keys next) :
      OuterDistinctTrace keys left

theorem outer_loop_success_is_false_or_distinct
    (keys : Slice (Array Std.U8 32#usize))
    (start : Std.Usize) (result : Option Bool)
    (run : normalized_require_unique_account_keys_loop0
      (rangeAt start (Slice.len keys)) keys = .ok result) :
    result = some false ∨
      (result = none ∧ OuterDistinctTrace keys start) := by
  unfold normalized_require_unique_account_keys_loop0 at run
  rw [loop.eq_def] at run
  by_cases active : start.val < keys.val.length
  · have activeLen : start.val < (Slice.len keys).val := by simpa using active
    obtain ⟨next, nextValue, nextRun⟩ :=
      range_at_next start (Slice.len keys) activeLen
    have addRun := usize_add_one_eq start next nextValue
    generalize bodyRun : normalized_require_unique_account_keys_loop0.body
      keys (rangeAt start (Slice.len keys)) = bodyResult at run
    unfold normalized_require_unique_account_keys_loop0.body at bodyRun
    rw [nextRun] at bodyRun
    simp (config := { zeta := true }) only [bind_tc_ok] at bodyRun
    change (do
      let innerStart ← start + 1#usize
      let pending ← normalized_require_unique_account_keys_loop0_loop0
        { start := innerStart, «end» := Slice.len keys } keys start
      match pending with
      | none => ok (cont (rangeAt next (Slice.len keys)))
      | some _ => ok (done pending)) = bodyResult at bodyRun
    rw [addRun] at bodyRun
    simp only [bind_tc_ok]
      at bodyRun
    change (do
      let pending ← normalized_require_unique_account_keys_loop0_loop0
        (rangeAt next (Slice.len keys)) keys start
      match pending with
      | none => ok (cont (rangeAt next (Slice.len keys)))
      | some _ => ok (done pending)) = bodyResult at bodyRun
    generalize innerRun : normalized_require_unique_account_keys_loop0_loop0
      (rangeAt next (Slice.len keys)) keys start = innerResult at bodyRun
    cases innerResult with
    | fail error =>
        simp at bodyRun
        subst bodyResult
        simp at run
    | div =>
        simp at bodyRun
        subst bodyResult
        simp at run
    | ok pending =>
        have classified := inner_loop_success_is_false_or_distinct
          keys start next (Slice.len keys) active (by simp) pending innerRun
        cases pending with
        | none =>
            simp at bodyRun
            subst bodyResult
            simp only [bind_tc_ok] at run
            rcases classified with falseResult | ⟨_, innerTrace⟩
            · cases falseResult
            · rcases outer_loop_success_is_false_or_distinct keys next result run with
                falseResult | ⟨noneResult, tail⟩
              · exact Or.inl falseResult
              · exact Or.inr ⟨noneResult,
                  OuterDistinctTrace.step start next active nextValue
                    innerTrace tail⟩
        | some pendingBool =>
            rcases classified with falseResult | noneResult
            · have pendingFalse : pendingBool = false := Option.some.inj falseResult
              subst pendingBool
              simp at bodyRun
              subst bodyResult
              simp at run
              exact Or.inl run.symm
            · cases noneResult.1
  · have pastEnd : keys.val.length ≤ start.val := by omega
    have nextRun := range_at_done start (Slice.len keys) (by simpa using pastEnd)
    unfold normalized_require_unique_account_keys_loop0.body at run
    rw [nextRun] at run
    simp at run
    exact Or.inr ⟨run.symm, OuterDistinctTrace.done start pastEnd⟩
termination_by keys.val.length - start.val
decreasing_by omega

theorem outer_distinct_trace_covers
    (keys : Slice (Array Std.U8 32#usize))
    (start : Std.Usize) (trace : OuterDistinctTrace keys start) :
    ∀ left right : Nat, start.val ≤ left → left < right →
      right < keys.val.length →
      keys.val[left]? ≠ keys.val[right]? := by
  induction trace with
  | done current pastEnd =>
      intro left right lower ordered rightBound
      omega
  | step current next active nextValue inner tail ih =>
      intro left right lower ordered rightBound
      by_cases here : left = current.val
      · subst left
        apply inner_distinct_trace_covers keys current (Slice.len keys) next
          inner right
        · omega
        · simpa using rightBound
      · exact ih left right (by omega) ordered rightBound

def PairwiseDistinctKeys
    (keys : Slice (Array Std.U8 32#usize)) : Prop :=
  ∀ left right : Nat, left < right → right < keys.val.length →
    keys.val[left]? ≠ keys.val[right]?

theorem normalized_unique_success_implies_pairwise_distinct
    (keys : Slice (Array Std.U8 32#usize))
    (run : normalized_require_unique_account_keys keys = .ok true) :
    PairwiseDistinctKeys keys := by
  unfold normalized_require_unique_account_keys at run
  dsimp only at run
  generalize outerRun : normalized_require_unique_account_keys_loop0
    { start := 0#usize, «end» := Slice.len keys } keys = outerResult at run
  cases outerResult with
  | fail error =>
      simp at run
  | div =>
      simp at run
  | ok pending =>
      have classified := outer_loop_success_is_false_or_distinct
        keys 0#usize pending (by simpa [rangeAt] using outerRun)
      rcases classified with falseResult | ⟨noneResult, trace⟩
      · simp [falseResult] at run
      · subst pending
        intro left right ordered rightBound
        exact outer_distinct_trace_covers keys 0#usize trace
          left right (by simp) ordered rightBound

theorem pairwise_distinct_prepared_keys_of_ordered_lookups
    (keys : Slice (Array Std.U8 32#usize))
    (poolPosition currentPosition : Nat)
    (rolloverPosition : Option Nat)
    (poolKey currentKey : Array Std.U8 32#usize)
    (rolloverKey : Option (Array Std.U8 32#usize))
    (pairwise : PairwiseDistinctKeys keys)
    (poolBeforeCurrent : poolPosition < currentPosition)
    (currentBound : currentPosition < keys.val.length)
    (poolLookup : keys.val[poolPosition]? = some poolKey)
    (currentLookup : keys.val[currentPosition]? = some currentKey)
    (rolloverLookup : ∀ position key,
      rolloverPosition = some position → rolloverKey = some key →
      currentPosition < position ∧ position < keys.val.length ∧
        keys.val[position]? = some key)
    (rolloverShape : rolloverPosition.isSome = rolloverKey.isSome) :
    PoolV1MutableAccountStoreBridge.PairwiseDistinctPreparedKeys
      poolKey currentKey rolloverKey := by
  constructor
  · intro equal
    have distinct := pairwise poolPosition currentPosition
      poolBeforeCurrent currentBound
    apply distinct
    simpa [poolLookup, currentLookup, equal]
  · intro key keyExact
    have rolloverSome : rolloverPosition.isSome = true := by
      rw [rolloverShape, keyExact]
      rfl
    obtain ⟨position, positionExact⟩ := Option.isSome_iff_exists.mp rolloverSome
    obtain ⟨currentBefore, positionBound, positionLookup⟩ :=
      rolloverLookup position key positionExact keyExact
    constructor
    · intro equal
      have distinct := pairwise poolPosition position
        (by omega) positionBound
      apply distinct
      simpa [poolLookup, positionLookup, equal]
    · intro equal
      have distinct := pairwise currentPosition position
        currentBefore positionBound
      apply distinct
      simpa [currentLookup, positionLookup, equal]

theorem inner_loop_body_rejects_equal_selected_keys
    (keys : Slice (Array Std.U8 32#usize))
    (left right : Std.Usize)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (leftKey rightKey : Array Std.U8 32#usize)
    (nextRun : core.iter.range.IteratorRange.next
      core.iter.range.StepUsize iter = .ok (.some right, nextIter))
    (leftRun : Slice.index_usize keys left = .ok leftKey)
    (rightRun : Slice.index_usize keys right = .ok rightKey)
    (equalRun : core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 leftKey rightKey = .ok true) :
    normalized_require_unique_account_keys_loop0_loop0.body
      keys left iter = .ok (done (.some false)) := by
  unfold normalized_require_unique_account_keys_loop0_loop0.body
  rw [nextRun]
  simp (config := { zeta := true }) only [bind_tc_ok]
  rw [leftRun]
  simp only [bind_tc_ok]
  change (do
    let selected ← Slice.index_usize keys right
    let equal ← core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 leftKey selected
    if equal then ok (done (some false)) else ok (cont nextIter)) =
      .ok (done (some false))
  rw [rightRun]
  simp only [bind_tc_ok]
  rw [equalRun]
  rfl

#print axioms inner_loop_body_rejects_equal_selected_keys
#print axioms inner_loop_success_is_false_or_distinct
#print axioms outer_loop_success_is_false_or_distinct
#print axioms normalized_unique_success_implies_pairwise_distinct
#print axioms pairwise_distinct_prepared_keys_of_ordered_lookups

end PoolV1NormalizedUniqueAccountsBridge
