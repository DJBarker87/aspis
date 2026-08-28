import V7ForestTerminal.Funs

/-!
# ASF8 / ASR8 translated layout bridge

This file pins the byte counts and every top-level offset used by the literal
translated Rust codec.  Nested late-statement, payment, digest and afterstate
codecs remain explicit source interfaces in `FunsExternal.lean`.
-/

set_option autoImplicit false

namespace V7ForestTerminalLayoutBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open V7ForestTerminalGenerated

private theorem usize_add_exact (left right sum : Std.Usize)
    (h : left.val + right.val = sum.val)
    (bounds : left.val + right.val < 2 ^ System.Platform.numBits) :
    (left + right : Result Std.Usize) = .ok sum := by
  change UScalar.add left right = .ok sum
  simp [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption, bounds]
  exact UScalar.eq_of_val_eq h

private theorem usize_mul_exact (left right product : Std.Usize)
    (h : left.val * right.val = product.val)
    (bounds : left.val * right.val < 2 ^ System.Platform.numBits) :
    (left * right : Result Std.Usize) = .ok product := by
  change UScalar.mul left right = .ok product
  simp [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
    UScalar.check_bounds, UScalar.inBounds, Result.ofOption, bounds]
  exact UScalar.eq_of_val_eq h

theorem exact_statement_and_result_sizes :
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES =
      .ok 1880#usize ∧
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES =
      .ok 792#usize := by
  have add32_800 : (32#usize + 800#usize : Result Std.Usize) = .ok 832#usize := by
    apply usize_add_exact <;> scalar_tac
  have add8_680 : (8#usize + 680#usize : Result Std.Usize) = .ok 688#usize := by
    apply usize_add_exact <;> scalar_tac
  have add832_688 : (832#usize + 688#usize : Result Std.Usize) = .ok 1520#usize := by
    apply usize_add_exact <;> scalar_tac
  have add144_1520 : (144#usize + 1520#usize : Result Std.Usize) = .ok 1664#usize := by
    apply usize_add_exact <;> scalar_tac
  have add1664_216 : (1664#usize + 216#usize : Result Std.Usize) = .ok 1880#usize := by
    apply usize_add_exact <;> scalar_tac
  have mul3_32 : (3#usize * 32#usize : Result Std.Usize) = .ok 96#usize := by
    apply usize_mul_exact <;> scalar_tac
  have add8_96 : (8#usize + 96#usize : Result Std.Usize) = .ok 104#usize := by
    apply usize_add_exact <;> scalar_tac
  have add104_688 : (104#usize + 688#usize : Result Std.Usize) = .ok 792#usize := by
    apply usize_add_exact <;> scalar_tac
  simp [pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES,
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,
    pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES,
    add32_800, add8_680, add832_688, add144_1520, add1664_216,
    mul3_32, add8_96, add104_688]

theorem exact_statement_offsets :
    pool_v1.pair_forest_terminal.MASTER_OFFSET = 8#usize ∧
    pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET = 40#usize ∧
    pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET = 72#usize ∧
    pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET = 104#usize ∧
    pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET = 112#usize ∧
    pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET = 144#usize ∧
    pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET = .ok 1664#usize := by
  have add32_800 : (32#usize + 800#usize : Result Std.Usize) = .ok 832#usize := by
    apply usize_add_exact <;> scalar_tac
  have add8_680 : (8#usize + 680#usize : Result Std.Usize) = .ok 688#usize := by
    apply usize_add_exact <;> scalar_tac
  have add832_688 : (832#usize + 688#usize : Result Std.Usize) = .ok 1520#usize := by
    apply usize_add_exact <;> scalar_tac
  have add144_1520 : (144#usize + 1520#usize : Result Std.Usize) = .ok 1664#usize := by
    apply usize_add_exact <;> scalar_tac
  simp [pool_v1.pair_forest_terminal.MASTER_OFFSET,
    pool_v1.pair_forest_terminal.CHECKPOINT_ACCOUNT_OFFSET,
    pool_v1.pair_forest_terminal.SELECTED_LANE_ACCOUNT_OFFSET,
    pool_v1.pair_forest_terminal.CHECKPOINT_SEQUENCE_OFFSET,
    pool_v1.pair_forest_terminal.HISTORICAL_ANCHOR_OFFSET,
    pool_v1.pair_forest_terminal.LATE_STATEMENT_OFFSET,
    pool_v1.pair_forest_terminal.PAYMENT_STATEMENT_OFFSET,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,
    add32_800, add8_680, add832_688, add144_1520]

theorem exact_result_offsets :
    pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET = 8#usize ∧
    pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET = 40#usize ∧
    pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET = 72#usize ∧
    pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET = 104#usize := by
  simp [pool_v1.pair_forest_terminal.RESULT_MASTER_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_SELECTED_LANE_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_NULLIFIER_OFFSET,
    pool_v1.pair_forest_terminal.RESULT_AFTERSTATE_OFFSET]

#print axioms exact_statement_and_result_sizes
#print axioms exact_statement_offsets
#print axioms exact_result_offsets

end V7ForestTerminalLayoutBridge
