import PoolV1NormalizedPreparedWriteback.Funs

/-!
# Pool V1 mutable account-store composition

This is the generic, non-Solana part of the final account write-back.  It
models accounts as a key-indexed store, executes the production copy order,
and proves that pairwise-distinct keys make all three writes non-aliasing.
No Pool predicate or Solana callback occurs in this model.
-/

set_option autoImplicit false

namespace PoolV1MutableAccountStoreBridge

open Aeneas Aeneas.Std Result ControlFlow Error

inductive PreparedHistoryAccountImage where
  | pool : Array Std.U8 1000#usize → PreparedHistoryAccountImage
  | page : Array Std.U8 8256#usize → PreparedHistoryAccountImage

def writeAccount {Key : Type} [DecidableEq Key]
    (store : Key → PreparedHistoryAccountImage) (key : Key)
    (image : PreparedHistoryAccountImage) : Key → PreparedHistoryAccountImage :=
  Function.update store key image

def persistPreparedHistory {Key : Type} [DecidableEq Key]
    (store : Key → PreparedHistoryAccountImage)
    (poolKey currentKey : Key) (rolloverKey : Option Key)
    (nextPool : Array Std.U8 1000#usize)
    (nextCurrent : Array Std.U8 8256#usize)
    (nextRollover : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool) : Option (Key → PreparedHistoryAccountImage) :=
  let afterPool := writeAccount store poolKey (.pool nextPool)
  let afterCurrent := if currentWritable then
      writeAccount afterPool currentKey (.page nextCurrent)
    else afterPool
  match rolloverKey, nextRollover with
  | none, none => some afterCurrent
  | some key, some image => some (writeAccount afterCurrent key (.page image))
  | _, _ => none

def PairwiseDistinctPreparedKeys {Key : Type}
    (poolKey currentKey : Key) (rolloverKey : Option Key) : Prop :=
  poolKey ≠ currentKey ∧
    ∀ key, rolloverKey = some key →
      poolKey ≠ key ∧ currentKey ≠ key

theorem persisted_prepared_history_reads_are_exact
    {Key : Type} [DecidableEq Key]
    (store : Key → PreparedHistoryAccountImage)
    (poolKey currentKey : Key) (rolloverKey : Option Key)
    (nextPool : Array Std.U8 1000#usize)
    (nextCurrent : Array Std.U8 8256#usize)
    (nextRollover : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool)
    (after : Key → PreparedHistoryAccountImage)
    (distinct : PairwiseDistinctPreparedKeys poolKey currentKey rolloverKey)
    (run : persistPreparedHistory store poolKey currentKey rolloverKey
      nextPool nextCurrent nextRollover currentWritable = some after) :
    after poolKey = .pool nextPool ∧
      after currentKey =
        (if currentWritable then .page nextCurrent else store currentKey) ∧
      (∀ key image, rolloverKey = some key → nextRollover = some image →
        after key = .page image) ∧
      (∀ key, key ≠ poolKey → key ≠ currentKey →
        rolloverKey ≠ some key → after key = store key) := by
  rcases distinct with ⟨poolCurrent, rolloverDistinct⟩
  cases writable : currentWritable <;>
    cases keyEq : rolloverKey <;>
    cases imageEq : nextRollover <;>
    simp [persistPreparedHistory, writable, keyEq, imageEq] at run
  all_goals
    subst after
    simp_all [writeAccount, Function.update]
  all_goals aesop

#print axioms persisted_prepared_history_reads_are_exact

end PoolV1MutableAccountStoreBridge
