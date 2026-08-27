import PoolV1NormalizedPreparedWriteback.Funs
import PoolV1NormalizedUniqueAccountsBridge
import PoolV1HistoryReadAfterWriteBridge

/-!
# Pool V1 Solana mutable persistence boundary

All Pool routing, option grammar, byte images and account-key nonaliasing are
proved before this file.  `SuccessfulPreparedHistoryBorrowRelease` is the
single remaining Solana runtime statement: successful mutable account-data
borrows, fixed-length copies and releases make the already-proved images
visible in the key-indexed post-state.  Its definition is exactly the generic
store transition; it contains no Pool predicate or cryptographic premise.
-/

set_option autoImplicit false

namespace PoolV1SolanaMutablePersistenceBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open PoolV1MutableAccountStoreBridge

abbrev Digest := PoolV1HistoryReadAfterWriteBridge.Digest

namespace SolanaAccountDataBorrow

def SuccessfulPreparedHistoryBorrowRelease
    {Key : Type} [DecidableEq Key]
    (before after : Key → PreparedHistoryAccountImage)
    (poolKey currentKey : Key) (rolloverKey : Option Key)
    (poolImage : Array Std.U8 1000#usize)
    (currentImage : Array Std.U8 8256#usize)
    (rolloverImage : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool) : Prop :=
  persistPreparedHistory before poolKey currentKey rolloverKey
    poolImage currentImage rolloverImage currentWritable = some after

end SolanaAccountDataBorrow

theorem normalized_writeback_success_exact_runtime
    (sourceCurrent : Array Std.U8 8256#usize)
    (sourceRollover : Option (Array Std.U8 8256#usize))
    (nextPool : Array Std.U8 1000#usize)
    (nextCurrent : Array Std.U8 8256#usize)
    (nextRollover : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool)
    (out : PoolV1NormalizedPreparedWriteback.NormalizedPreparedHistoryWritebackV1)
    (run :
      PoolV1NormalizedPreparedWriteback.normalized_prepared_history_writeback
        sourceCurrent sourceRollover nextPool nextCurrent nextRollover
          currentWritable = .ok (.some out)) :
    out.pool = nextPool ∧
      out.current = (if currentWritable then nextCurrent else sourceCurrent) ∧
      out.rollover = nextRollover := by
  unfold PoolV1NormalizedPreparedWriteback.normalized_prepared_history_writeback at run
  cases writable : currentWritable <;>
    cases sourceEq : sourceRollover <;>
    cases nextEq : nextRollover <;>
    simp_all
  all_goals (cases run; simp_all)

theorem normalized_source_images_runtime_persist_exactly
    {Key : Type} [DecidableEq Key]
    (before after : Key → PreparedHistoryAccountImage)
    (poolKey currentKey : Key) (rolloverKey : Option Key)
    (sourceCurrent : Array Std.U8 8256#usize)
    (sourceRollover : Option (Array Std.U8 8256#usize))
    (nextPool : Array Std.U8 1000#usize)
    (nextCurrent : Array Std.U8 8256#usize)
    (nextRollover : Option (Array Std.U8 8256#usize))
    (currentWritable : Bool)
    (out : PoolV1NormalizedPreparedWriteback.NormalizedPreparedHistoryWritebackV1)
    (normalizedRun :
      PoolV1NormalizedPreparedWriteback.normalized_prepared_history_writeback
        sourceCurrent sourceRollover nextPool nextCurrent nextRollover
          currentWritable = .ok (.some out))
    (distinct : PairwiseDistinctPreparedKeys poolKey currentKey rolloverKey)
    (runtimeRun : SolanaAccountDataBorrow.SuccessfulPreparedHistoryBorrowRelease
      before after poolKey currentKey rolloverKey out.pool out.current
        out.rollover currentWritable) :
    after poolKey = .pool nextPool ∧
      after currentKey =
        (if currentWritable then .page nextCurrent else before currentKey) ∧
      (∀ key image, rolloverKey = some key → nextRollover = some image →
        after key = .page image) ∧
      (∀ key, key ≠ poolKey → key ≠ currentKey →
        rolloverKey ≠ some key → after key = before key) := by
  obtain ⟨poolExact, currentExact, rolloverExact⟩ :=
    normalized_writeback_success_exact_runtime sourceCurrent sourceRollover
      nextPool nextCurrent nextRollover currentWritable out normalizedRun
  have persisted := persisted_prepared_history_reads_are_exact before
    poolKey currentKey rolloverKey out.pool out.current out.rollover
      currentWritable after distinct runtimeRun
  rw [poolExact, currentExact, rolloverExact] at persisted
  cases writable : currentWritable <;> simp [writable] at persisted ⊢
  all_goals exact persisted

theorem persisted_rollover_page_selected_root_decodes
    {Key : Type} [DecidableEq Key]
    (before after : Key → PreparedHistoryAccountImage)
    (poolKey currentKey rolloverKey : Key)
    (sourceCurrent sourceRollover : Array Std.U8 8256#usize)
    (nextPool : Array Std.U8 1000#usize)
    (nextCurrent final : Array Std.U8 8256#usize)
    (currentWritable : Bool)
    (out : PoolV1NormalizedPreparedWriteback.NormalizedPreparedHistoryWritebackV1)
    (normalizedRun :
      PoolV1NormalizedPreparedWriteback.normalized_prepared_history_writeback
        sourceCurrent (.some sourceRollover) nextPool nextCurrent (.some final)
          currentWritable = .ok (.some out))
    (distinct : PairwiseDistinctPreparedKeys poolKey currentKey (.some rolloverKey))
    (runtimeRun : SolanaAccountDataBorrow.SuccessfulPreparedHistoryBorrowRelease
      before after poolKey currentKey (.some rolloverKey) out.pool out.current
        out.rollover currentWritable)
    (data : Slice Std.U8) (pool : solana_pubkey.Pubkey)
    (page first : Std.U64) (roots : Slice Digest) (selected : Nat)
    (dataLength : data.length = 8256)
    (rootsCapacity : roots.val.length ≤ 256)
    (selectedBound : selected < roots.val.length)
    (canonical : ∀ index : Fin 8,
      roots[selected].val[index.val].val < _root_.m31Prime)
    (writeRun :
      PoolV1HistoryPersistGenerated.history.write_new_page_unchecked
        data pool page first roots = .ok (Array.to_slice final)) :
    after rolloverKey = .page final ∧
      _root_.decodeDigest
        (PoolV1HistoryReadAfterWriteBridge.rootWindow
          (Array.to_slice final) selected) =
          some roots[selected] := by
  have persisted := normalized_source_images_runtime_persist_exactly
    before after poolKey currentKey (.some rolloverKey)
      sourceCurrent (.some sourceRollover) nextPool nextCurrent (.some final)
      currentWritable out normalizedRun distinct runtimeRun
  constructor
  · exact persisted.2.2.1 rolloverKey final rfl rfl
  · exact PoolV1HistoryReadAfterWriteBridge.new_page_success_selected_root_decodes
      data pool page first roots (Array.to_slice final) selected dataLength
        rootsCapacity selectedBound canonical writeRun

theorem persisted_writable_current_page_selected_root_decodes
    {Key : Type} [DecidableEq Key]
    (before after : Key → PreparedHistoryAccountImage)
    (poolKey currentKey : Key) (rolloverKey : Option Key)
    (sourceCurrent : Array Std.U8 8256#usize)
    (sourceRollover : Option (Array Std.U8 8256#usize))
    (nextPool : Array Std.U8 1000#usize)
    (final : Array Std.U8 8256#usize)
    (nextRollover : Option (Array Std.U8 8256#usize))
    (out : PoolV1NormalizedPreparedWriteback.NormalizedPreparedHistoryWritebackV1)
    (normalizedRun :
      PoolV1NormalizedPreparedWriteback.normalized_prepared_history_writeback
        sourceCurrent sourceRollover nextPool final nextRollover true =
          .ok (.some out))
    (distinct : PairwiseDistinctPreparedKeys poolKey currentKey rolloverKey)
    (runtimeRun : SolanaAccountDataBorrow.SuccessfulPreparedHistoryBorrowRelease
      before after poolKey currentKey rolloverKey out.pool out.current
        out.rollover true)
    (data : Slice Std.U8)
    (header : PoolV1HistoryPersistGenerated.history.RootPageHeaderV1)
    (roots : Slice Digest) (selected : Nat)
    (dataLength : data.length = 8256)
    (selectedBound : selected < roots.val.length)
    (canonical : ∀ index : Fin 8,
      roots[selected].val[index.val].val < _root_.m31Prime)
    (writeRun : PoolV1HistoryPersistGenerated.history.append_roots_unchecked
      data header roots = .ok (Array.to_slice final)) :
    after currentKey = .page final ∧
      _root_.decodeDigest
        (PoolV1HistoryReadAfterWriteBridge.rootWindow (Array.to_slice final)
          (header.filled.val + selected)) = some roots[selected] := by
  have persisted := normalized_source_images_runtime_persist_exactly
    before after poolKey currentKey rolloverKey sourceCurrent sourceRollover
      nextPool final nextRollover true out normalizedRun distinct runtimeRun
  constructor
  · simpa using persisted.2.1
  · exact PoolV1HistoryReadAfterWriteBridge.existing_page_success_selected_root_decodes
      data header roots (Array.to_slice final) selected dataLength selectedBound
        canonical writeRun

#print axioms normalized_source_images_runtime_persist_exactly
#print axioms normalized_writeback_success_exact_runtime
#print axioms persisted_rollover_page_selected_root_decodes
#print axioms persisted_writable_current_page_selected_root_decodes

end PoolV1SolanaMutablePersistenceBridge
