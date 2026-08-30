import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk10

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 91:0-91:57
    Name pattern: [aspis_statement::atomic_state_only_terminal::ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS"]
def
  aspis_statement.atomic_state_only_terminal.ATOMIC_STATE_ONLY_COMPILED_COPY_PATTERNS
  : Std.Usize := 15#usize

/-- [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_INACTIVE_ROW_GROUPS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 9:0-9:67
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_INACTIVE_ROW_GROUPS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_INACTIVE_ROW_GROUPS"]
def
  aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_INACTIVE_ROW_GROUPS
  : Array Std.U8 64#usize :=
  Array.make 64#usize [
    0#u8, 0#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 2#u8,
    1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8,
    1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 2#u8, 0#u8, 2#u8, 0#u8, 1#u8,
    1#u8, 3#u8, 3#u8, 3#u8, 3#u8, 4#u8, 5#u8, 6#u8, 6#u8, 6#u8, 6#u8, 6#u8,
    6#u8, 6#u8, 6#u8, 6#u8
    ]

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_groups_owned_v3]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 144:0-144:72
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_groups_owned_v3]
    Visibility: public -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_groups_owned_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_groups_owned_v3
  : Result (Array Std.U8 64#usize) := do
  ok
    aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_INACTIVE_ROW_GROUPS

/-- [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_INACTIVE_GROUP_MASKS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 10:0-10:68
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_INACTIVE_GROUP_MASKS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_INACTIVE_GROUP_MASKS"]
def
  aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_INACTIVE_GROUP_MASKS
  : Array Std.U16 7#usize :=
  Array.make 7#usize [
    59391#u16, 59390#u16, 61438#u16, 0#u16, 65520#u16, 65530#u16, 65535#u16
    ]

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_group_masks_owned_v3]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 154:0-154:73
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_group_masks_owned_v3]
    Visibility: public -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_group_masks_owned_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_group_masks_owned_v3
  : Result (Array Std.U16 7#usize) := do
  ok
    aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_INACTIVE_GROUP_MASKS

/-- [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 186:4-194:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64] -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64"]
def
  aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_64_loop.body
  (values : Array aspis_core.field.QM31 64#usize) (complement : Bool)
  (mask : Std.U64) (sum : aspis_core.field.QM31) :
  Result (ControlFlow (Std.U64 × aspis_core.field.QM31) aspis_core.field.QM31)
  := do
  if mask != 0#u64
  then
    let i ← core.num.U64.trailing_zeros mask
    let index ← lift (UScalar.cast .Usize i)
    let sum1 ←
      if complement
      then
        do
        let q ← Array.index_usize values index
        aspis_core.field.QM31.sub sum q
      else
        do
        let q ← Array.index_usize values index
        aspis_core.field.QM31.add sum q
    let i1 ← mask - 1#u64
    let mask1 ← lift (mask &&& i1)
    ok (cont (mask1, sum1))
  else ok (done sum)

/-- [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 186:4-194:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64] -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64"]
def aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_64_loop
  (values : Array aspis_core.field.QM31 64#usize) (mask : Std.U64)
  (complement : Bool) (sum : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (mask1, sum1) =>
      aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_64_loop.body
      values complement mask1 sum1)
    (mask, sum)

/-- [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 180:0-180:74
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_selector_mask_sum_64"]
def aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_64
  (values : Array aspis_core.field.QM31 64#usize) (mask : Std.U64) :
  Result aspis_core.field.QM31
  := do
  let i ← core.num.U64.count_ones mask
  let (mask1, complement) ←
    if i > 32#u32
    then do
         let mask2 ← lift (~~~ mask)
         ok (mask2, true)
    else ok (mask, false)
  let sum ←
    if complement
    then ok aspis_core.field.QM31.ONE
    else ok aspis_core.field.QM31.ZERO
  aspis_statement.atomic_state_only_terminal.atomic_selector_mask_sum_64_loop
    values mask1 complement sum


end V7Tag73CurrentHelpersOpaque
