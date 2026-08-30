# V7 pair-forest static inactive schedule — 2026-08-30

## Result

The selected one-transaction eight-lane Pool verifier no longer reconstructs
and deduplicates its fixed 64-row inactive Copy schedule at runtime. The host
generator now emits the exact row-to-group map and seven distinct inactive
masks alongside the authoritative active-row table.

The real combined worst-case lifecycle improved from 1,201,757 CU to:

\[
\boxed{1,198,735\ \mathrm{CU}}
\]

This saves 3,022 CU and leaves 1,265 CU below the preferred 1.2M target and
101,265 CU below the hard 1.3M gate. The TxV1 packet remains exactly 997 bytes,
leaving 3,099 bytes below the 4,096-byte target.

| Shape | Previous CU | Current CU | Delta | TxV1 bytes |
|---|---:|---:|---:|---:|
| Withdrawal, rollover, 255 populated pairs | 1,201,757 | 1,198,735 | -3,022 | 997 |

Evidence:

- `results/v7-static-schedule-cu-check-20260830/withdrawal-rollover-counter0.json`
- verifier SBF: 1,700,384 bytes, SHA-256 `4ee9b4789533e049e2d9e1f43c84fa97f745a98151f9477ebd828de742b75e5c`
- frozen Pool SBF: SHA-256 `61f80ab33bff36b38716df944d7851a473be0ed065b2d57864082fd966ec8810`

Simulation and execution consume the same CU. The proof, registry, verifier
entry, checkpoint and master remain byte-exact. The selected lane, rollover
history page and nullifier marker change exactly. The SPL withdrawal moves
exactly 250 tokens from the vault to the bound destination and leaves the mint
unchanged.

## Semantic preservation

The change does not alter the proof, transcript, relation, query count, digest
width, work checks, terminal statement or state bindings. For each row `r`, the
generated tables satisfy

```text
INACTIVE_GROUP_MASKS[INACTIVE_ROW_GROUPS[r]] == !ACTIVE_ROW_MASKS[r].
```

The focused Rust test independently rebuilds the schedule from the active
masks, checks the complement identity, checks group bounds and uniqueness, and
compares both emitted tables byte-for-byte with the runtime reference.

The generator derives all three tables from the same typed Copy registry. No
second hand-maintained semantic table is introduced.

## Source-verification consequence

The old runtime helper used `iter().copied().enumerate()`, `position` and an
adaptive deduplication closure. Those imported inconsistent current-nightly
standard-library iterator trait signatures into Charon and stopped Aeneas
before it reached Aspis code.

After selecting the generated static schedule, exact selected-feature Charon
extraction reports no trait-transformation error. Its artifact contains the
two static schedule accessors and the selected four-slot gamma path, while it
contains neither the runtime `pool_inactive_schedule` helper nor the obsolete
slot-major gamma path. This removes a tool obstruction without adding an
opaque semantic boundary.

The ordinary-kernel bridge
`AspisFormal.Pool.V7StaticInactiveScheduleBridge` pins production revision
`6702cfcc987e29381085039d9da8715dafbbfce8`, records the exact 64-entry group
map and seven masks, and proves:

```text
inactiveGroupMask_injective
inactiveGroupMask_complements_activeMask
inactiveSchedule_lookup_complements_activeRow
```

The focused NUC replay completed all 8,699 dependencies and the new target in
6.67 seconds with maximum RSS 6,667,420 KiB and zero swap. The complete axiom
union is exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no
project-specific axiom, `sorry`, `admit`, `sorryAx`, or `native_decide`.

## Focused replay

```sh
cargo test -p aspis-verifier \
  --no-default-features \
  --features v7-pair-forest-one-tx-candidate \
  pool_inactive_schedules_are_exact_complements_and_deduplicated

NO_DNA=1 cargo build-sbf \
  --manifest-path programs/aspis-verifier/Cargo.toml \
  --no-default-features \
  --features v7-pair-forest-one-tx-candidate \
  --sbf-out-dir results/v7-static-schedule-cu-check-20260830/verifier

results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/target/release/aspis-v7-pair-forest-combined-rejection \
  results/v7-static-schedule-cu-check-20260830/pool/aspis_pool.so \
  results/v7-static-schedule-cu-check-20260830/verifier/aspis_verifier.so \
  results/v7-static-schedule-cu-check-20260830/withdrawal-rollover-counter0.json \
  results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/withdrawal-rollover-counter0-strict-canonical.bin \
  success 1400000 asq8 255 withdrawal
```

No RPC, signing, devnet or mainnet operation occurred.
