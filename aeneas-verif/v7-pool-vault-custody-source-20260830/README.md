# V7 Pool vault-custody Rust-to-Lean/Aeneas bridge

This focused bundle closes the current vault-backed deposit and withdrawal
custody seam without changing production Rust, the Tag-73 relation, Pool wire,
or verifier code. It composes a pinned fixed-width Rust projection with the
existing one-terminal caller/source bridge and hash-pinned production control
flow.

## Deliberate launch scope

The launch path supports the original SPL Token program only. It accepts the
three supported executable-program loaders (legacy BPF, upgradeable BPF, and
loader-v4), but requires the exact legacy Token program ID and exact 82-byte
mint / 165-byte token-account layouts. Token-2022 owners, extensions,
noncanonical option tags, wrong loader owners, aliases, signer/writable shape
errors and unexpected executable accounts fail closed.

The principal planner theorems are:

- `translated_token_program_success_is_exact`
- `translated_mint_success_is_exact`
- `translated_token_account_success_is_exact`
- `translated_deposit_plan_success_is_exact`
- `translated_withdrawal_plan_success_is_exact`

A successful deposit plan binds the source signer, mint, canonical vault PDA
and authority, excludes vault delegate/native/close side channels, and exposes
the exact checked equations:

```text
source_after = source_before - amount
vault_after  = vault_before  + amount
```

A successful withdrawal additionally binds the public destination token
account and system-owned vault-authority PDA, and exposes:

```text
vault_after       = vault_before       - amount
destination_after = destination_before + amount
```

Both plans construct exactly one legacy SPL `TransferChecked`; deposits use
the authenticated source signer and withdrawals use the canonical Pool PDA.

## CPI effects and the public atomic caller

`translated_deposit_execution_success_is_exact` and
`translated_withdrawal_execution_success_is_exact` prove that a translated
successful execution must have succeeded at the required CPI stages, observed
the exact planned balances, passed the post-CPI delta check, and only then
written the exact lane/history image (plus nullifier consumption for a
withdrawal). Every unrelated state component is preserved.

The public-caller capstones are:

- `translated_atomic_deposit_success_is_exact`
- `translated_atomic_withdrawal_success_is_exact`
- `translated_atomic_rejection_is_exact_prestate`
- `translated_deposit_token_cpi_failure_is_exact_rollback`
- `translated_withdrawal_token_cpi_failure_is_exact_rollback`

They start at the literal translated `execute_atomic_custody` caller. Every
rejected call returns the exact prestate and no certificate; the explicit CPI
failure theorems also identify the exact error and call trace. Thus a failed
withdrawal after verifier success and a failed deposit token CPI cannot persist
Pool, custody, history, or marker effects in this operational model.

`translated_committed_deposit_is_legacy_not_token2022` and its withdrawal
counterpart prove that any committed call has legacy Token ownership throughout.
The two `translated_token2022_*_is_rejected_with_exact_rollback` theorems make
the Token-2022 exclusion operational: supplying its program ID cannot commit
and returns the exact prestate.

## Production correspondence

`source-audit.sh` pins the current production hashes and exact order in
`process_pair_forest_deposit_with_runtime_v1`:

```text
account/loader authentication -> transfer plan -> acquire Pool borrows
  -> token CPI -> exact balance delta -> lane/history writes
```

It composes the existing one-terminal source audit, whose withdrawal order is:

```text
layout/marker/token plan -> marker reservation -> verifier CPI
  -> acquire all Pool borrows -> PDA-signed token CPI -> exact balance delta
  -> lane/history/marker writes
```

No fallible operation follows the first Pool write in either pinned caller.
The production tests cover accepted deposits and withdrawals, alias/delta
failure without Pool writes, loader authentication, failed custody CPI, and
Token-2022-shaped rejection before transfer.

## Trust boundary

The harness is an operational projection, not a claim that Charon translates
Solana `AccountInfo`, SPL Token, or CPI runtime internals. Correspondence to the
literal current production source is fail-closed and hash-pinned, and the
existing one-terminal and lane bridges cover their caller/writeback seams.

Remaining explicit boundaries are SPL Token `TransferChecked` behavior,
Solana instruction-level atomic rollback, PDA derivation/runtime account
semantics, the fixed-width projection correspondence, Charon/Aeneas/compiler
provenance, and Lean's kernel. The verifier is represented only by its already
authenticated success bit here; no cryptographic theorem or relation changes.

Every printed theorem depends on exactly a subset of `propext`,
`Classical.choice`, and `Quot.sound`. Compiled generated/proof source contains
no `sorry`, `admit`, `sorryAx`, `native_decide`, project-specific axiom, or
abstract restore function.

## Replay

```sh
./source-audit.sh
./replay-rust.sh
CHARON_BIN=/path/to/charon AENEAS_BIN=/path/to/aeneas ./replay-extraction.sh
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
  LEAN_BIN=/path/to/lean-4.31.0 ./replay-lean.sh
```

All replay scripts use one Cargo job and one Lean thread. Exact focused release
evidence is in `REPLAY-RESULT.txt`.
