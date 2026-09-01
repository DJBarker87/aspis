# V7 literal pair-forest caller source-unblock

This bundle records the strongest honest Rust -> Charon -> Aeneas result for
the production Tag-73 Registry V2 one-transaction caller at source revision
`309b9c73353366a32671901be64cf8386404fd89`.

It changes no production Rust, cryptography, Pool state, deployment or
transaction.  The source changes under `toolchain/` are extraction-only,
behavior-preserving normalizations applied to a disposable source copy.

## Completed result

The complete current root

`crate::v7_pair_forest_dispatch::process_with_clear_return_data`

now passes Charon and Aeneas through final Lean emission.  The emitted
definition is in
`V7LiteralCallerCurrent309bMetadataAccountOpaqueAcceptedToolR1/Funs.lean`.
The original `SymbolicToPureTypes` iterator explosion, the nested
`AccountInfo` borrow join and the M31 type/constructor emitter clash are no
longer translation blockers.

The accepted Charon profile keeps exactly two static-schedule accessors opaque:

- `pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1`;
- `pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1`.

Their exact 64-entry row map and seven masks are unchanged from revision
`6702cfcc987e29381085039d9da8715dafbbfce8`, and are kernel checked by
`AspisFormal.Pool.V7StaticInactiveScheduleBridge`.  Other explicit source and
platform boundaries are inventoried below; “two” refers only to schedule
opacities, not to the entire caller trust boundary.

The large caller leaves `readonly_account_metadata_v1` opaque only to prevent
Solana's interior-borrow graph from re-entering that extraction.  A separate
fresh-current-source extraction translates the literal helper with transparent
`AccountInfo`.  Lean then defines the large caller's exact external function by
calling that translation and proves:

- `readonly_account_metadata_v1_exact`;
- `readonly_account_metadata_v1_success_fields`.

Both theorems report exactly `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry`, `admit`, `sorryAx`, `native_decide`, project axiom or
conclusion-shaped premise in the compiled bridge.

## Exact remaining source obstruction

The next finite helper is `exact_six_account_refs_v1`.  Charon translates it,
but Aeneas rejects the slice-pattern destructure at production-source lines
424:8--424:106 with:

`Inconsistent projection: PtrMetadata`

for a shared `&[AccountInfo]`.  This happens in `InterpPaths.ml:236` before
Lean emission.  The diagnostic LLBC and complete failure log are frozen.  No
translator patch and no broader opacity was introduced.

Consequently, this milestone proves the metadata projection exactly and emits
the complete caller, but it does **not** yet claim a kernel-checked literal
`process_with_clear_return_data` accepted-path theorem.  That theorem is still
blocked by the six-account shared-slice projection and by the remaining
explicit external functions.

## Remaining explicit boundaries

The generated whole-caller template has 84 external function declarations:
69 ordinary Rust/core/alloc operations and 15 protocol/platform functions.
The protocol/platform set is:

- `qm31_dot3`;
- the two static inactive-schedule accessors;
- Solana `set_return_data` and `Clock::get`;
- five exact PDA wrappers;
- `readonly_account_metadata_v1` (closed in this bundle);
- `borrow_readonly_account_data`;
- `exact_six_account_refs_v1` (the immediate Aeneas blocker);
- `sbf_hashv`;
- Pubkey equality/construction/byte conversion.

The PDA, SHA-256, Solana syscall/borrow/return-data and remaining Rust library
semantics must be supplied by focused source bridges or retained explicitly as
platform assumptions.  The already existing Poseidon, SHA, semantic-terminal,
Registry V2 and K1 boundaries are not weakened here.

## Extraction normalization

`toolchain/literal-caller-current309b-to-accepted-source.patch` is the canonical
replay patch.  It is an exact diff from the pinned commit to the source mirror
used for the successful extraction; applying it reproduces source hashes:

- `v7_verifier.rs`: `ede2541418bb566d9dada7598d49b3acb41a3b4636f47446a65f274761b1641c`;
- `v7_pair_forest_dispatch.rs`: `d5a380e7782b1cb9673794470ed3951421d1df6e19b4fff7695ea1d8522e8df3`.

The older experiment-by-experiment fragments are retained only under
`evidence/superseded-fragments/`; they are not the replay interface.  Failed
borrow/source shapes and the rejected generic Aeneas patch are under
`evidence/rejected/`.

## Replay

Quick source/artifact audit:

```bash
./source-audit.sh
```

Focused Lean replay on a host with the pinned Aeneas backend:

```bash
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
LEAN_BIN=/path/to/lean-4.31.0/bin/lean \
LAKE_BIN=/path/to/lake \
./replay-lean.sh
```

The complete Charon/Aeneas replay is intentionally separate and must be run
inside a no-swap cgroup.  It takes about eleven and a half minutes, dominated
by Aeneas emission:

```bash
CHARON_BIN=/pinned/charon \
AENEAS_BIN=/pinned/aeneas \
RUSTUP_BIN=/path/to/rustup \
./replay-extraction-nuc.sh
```

Exact tools, hashes, units, invocations and resource results are in
`TOOLCHAIN.md` and `REPLAY-RESULT.txt`.
