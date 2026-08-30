# V7 Pool nullifier-marker Rust-to-Lean/Aeneas bridge

This focused bundle closes the fresh nullifier-PDA lifecycle added at
`da77d5f5a22681200cceec8e90fc69ac2cc81ad8`. It changes no production Rust,
proof relation, transcript, ASQ8/ASF8/ASR8 codec, or transaction wire. A
fixed-width Rust projection is extracted by pinned Charon/Aeneas, while
`source-audit.sh` pins the corresponding production files and caller order.

The production terminal account layout adds a writable System-owned signer
payer and the executable native-loader-owned System Program. It deliberately
does **not** add a Rent account meta: the top-level processor obtains the
canonical schedule through `Rent::get()` and passes `&Rent` into the caller.
The projection represents that boundary as `loaded_from_sysvar` plus the exact
nonzero minimum-balance value.

## Exact four reservation paths

The Lean statements keep all four admissible entry shapes separate:

1. zero-lamport System account: `create_account`;
2. underfunded dusted System account: transfer deficit, allocate, assign;
3. already-funded dusted System account: allocate, assign;
4. precreated Pool-owned 208-byte zero account: no System CPI.

Every path requires the exact canonical marker PDA derivation, seed tag, Pool
and nullifier, distinct/non-executable/non-signer writable marker, canonical
owner and size, zero data, no stored marker, authenticated payer/System
Program, and canonical Rent reserve. After reservation the caller replans the
live account and requires the same bump and marker image before verifier CPI.

The principal path theorems are:

- `translated_create_account_reservation_is_exact`
- `translated_transfer_allocate_assign_reservation_is_exact`
- `translated_allocate_assign_reservation_is_exact`
- `translated_already_program_owned_reservation_is_exact`
- `translated_accepted_create_account_path_is_exact`
- `translated_accepted_transfer_allocate_assign_path_is_exact`
- `translated_accepted_allocate_assign_path_is_exact`
- `translated_accepted_already_program_owned_path_is_exact`
- `translated_accepted_atomic_has_one_exact_marker_lifecycle`

They prove exact payer lamport effects, System CPI path, reserved owner/size,
the post-verifier marker write, and path-specific trace. Those traces prove:

```text
System reservation -> live replan -> verifier CPI -> Pool core writeback
                   -> marker consumption
```

The successful result stores the exact expected marker, sets the caller core
writeback flag, and preserves unrelated state.
`translated_accepted_atomic_has_one_exact_marker_lifecycle` is exhaustive: it
starts from the accepted translated atomic wrapper and kernel-checks that its
reservation is exactly one of those four paths. No path tag or preparation
kind remains as an external premise in this capstone.

## Replay and rollback

`translated_rejected_atomic_marker_terminal_is_exact_prestate` proves that
every translated rejection has the exact prestate and no certificate.
`translated_spent_replay_is_exact_and_atomic` proves a consumed canonical
marker is rejected as `SpentNullifier` with the exact prestate and an all-zero
pre-verifier trace. Thus replay rejection does not call the verifier.

The Rust tests cover all four successful paths and the adversarial cases for:

- spoofed/malformed payer, System Program, PDA, owner, size, zero state and
  Rent schedule;
- insufficient payer funds and every create/transfer/allocate/assign failure;
- verifier, Pool-core and marker-write failure after reservation;
- exact rollback of payer, marker and unrelated state;
- success followed by replay rejection.

## Source and trust boundary

The generated Rust harness is an operational projection, not a claim that
Charon translates Solana's `AccountInfo` or CPI runtime. The production
correspondence is separately fail-closed and hash-pinned by `source-audit.sh`,
including the account layout, canonical seeds, `Rent::get`, System
create/transfer/allocate/assign calls, post-CPI replan, rent-exemption check,
verifier ordering and final marker write.

Remaining explicit boundaries are Solana PDA derivation, System CPI behavior,
Rent sysvar behavior and instruction-level rollback; Charon/Aeneas/compiler
provenance; and Lean's kernel. The cryptographic verifier is only a Boolean
runtime outcome in this focused bridge and its mathematics is unchanged.

Every printed theorem depends on exactly a subset of `propext`,
`Classical.choice` and `Quot.sound`. Compiled source contains no `sorry`,
`admit`, `sorryAx`, `native_decide`, project-specific axiom or abstract restore
function.

## Replay

```sh
./source-audit.sh
./replay-rust.sh
CHARON_BIN=/path/to/charon AENEAS_BIN=/path/to/aeneas ./replay-extraction.sh
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
  LEAN_BIN=/path/to/lean-4.31.0 ./replay-lean.sh
```

All replay scripts use one Cargo job and one Lean thread. The exact local
release replay is recorded in `REPLAY-RESULT.txt`.
