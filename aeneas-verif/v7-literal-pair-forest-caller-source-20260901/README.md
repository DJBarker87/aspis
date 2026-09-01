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

now passes Charon and Aeneas through final Lean emission with
`exact_six_account_refs_v1` transparent.  The strongest emitted definition is
in `V7LiteralCallerCurrent309bExactSixTransparentSharedIndexR1/Funs.lean`.
The original `SymbolicToPureTypes` iterator explosion, the caller-level
`AccountInfo` projection joins and the M31 type/constructor emitter clash are
no longer translation blockers.  The literal Solana `RefCell` dynamic-borrow
implementation remains a separately isolated platform/tool boundary, described
below.

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

The next source seam, `borrow_readonly_account_data`, is now closed in the
focused **borrow-ready production-entry model**.  `core.cell.Ref` is represented
by the exact read-only value it guards, and the external helper returns the
literal account byte slice.  Lean proves:

- `borrow_readonly_account_data_borrow_ready_exact`;
- `borrow_readonly_account_data_success_is_exact_view`;
- `readonly_data_guard_deref_is_exact`.

This is not a claim that arbitrary host calls with an already outstanding
mutable `RefCell` borrow succeed.  That dynamic check is the explicit Solana
entry-state/platform boundary.  The production verifier starts from freshly
provided transaction accounts, and the modeled accepted path is restricted to
that borrow-ready state.

Three deterministic core-library clusters are now supplied by executable Lean
definitions matching the generated Rust signatures.  The focused accepted
graph defines 34 formerly external operations.  The first cluster covers
boolean `then_some`, the `u16`/`u64` bit counts, `usize` bit reversal, both
checked shifts, `u32::is_power_of_two`, `Option::{as_ref,ok_or}`, and
`Slice::{first,last}`.  The second covers range cloning, option comparison and
try control flow, result inspection/mapping, boxed-value identity, and five
owned-vector operations (`into_boxed_slice`, `truncate`, `remove`, `clear`, and
`is_empty`).  The third replaces the empty `Windows` carrier by its exact
finite state and closes slice/array comparison, window creation/iteration,
boxed-slice and vector-to-array conversion, and shared-vector iteration.  The
accompanying bridge proves branch-sensitive behavior, failure cases, and exact
list images.  These definitions are ordinary Rust library semantics; they
introduce no protocol or cryptographic premise.

The formerly blocked six-account helper is now independently translated as
six literal shared-slice indices, in order `0` through `5`.  Lean proves:

- `exact_six_account_refs_v1_literal_order`;
- `exact_six_account_refs_v1_success_has_literal_order`.

The second theorem applies to every slice whose value is exactly the six
caller accounts and proves that no account can be permuted, duplicated or
dropped.  Both the focused helper and the complete caller use the same pinned
patched Aeneas binary.  The complete caller's external-function template no
longer declares `exact_six_account_refs_v1`.

## Closed PtrMetadata obstruction

The previous Aeneas failure at the production six-account slice pattern was:

`Inconsistent projection: PtrMetadata`

The accepted extraction-only source normalization adds a redundant
`accounts.len() != 6` guard immediately before the existing exact-six pattern.
The only production caller already rejects every non-six input before this
private helper is called, and the original pattern's `else` branch is also
unreachable, so the reachable verifier behavior is unchanged.

Two narrowly scoped translator patches then:

1. replace only an identity reborrow of the same immutable shared slice with a
   copy of that shared reference; and
2. permit only immutable, single-element slice indexing when the element type
   structurally contains mutable borrows.

Raw pointers, mutable indexing, arrays, ranges/subslices, mismatched metadata
origins and all other nested-borrow builtins retain the original fail-closed
behavior.  The patched tree and static binary hash are pinned in
`TOOLCHAIN.md`; the build script reproduces and asserts both.

## Exact remaining source boundary

This milestone still does **not** claim a kernel-checked literal
`process_with_clear_return_data` accepted-path theorem.  The complete emitted
caller has 83 generated external function templates (73 rendered as archival
Lean axioms), down from 84/74.  The six-account helper is no longer among them.
The accepted compile graph now supplies executable definitions for the metadata
accessor, borrow-ready account-data view, and read-only guard dereference rather
than importing those archival axioms.  It also supplies executable definitions
for 34 deterministic core-library templates.  The archival generated
`FunsExternal_Template.lean` remains an inventory and still displays all of its
original declarations; it is not imported by the focused accepted graph.

The literal `AccountInfo::try_borrow_data` implementation itself is not
translated: current Aeneas cannot synthesize nested mutable ADT write-back
projections.  This is now the smallest explicit Solana platform boundary, not
an opaque caller-acceptance premise.  A single-premise literal caller theorem
also still requires filling or explicitly classifying the remaining 35
ordinary Rust-library templates and the platform templates.

## Remaining explicit boundaries

The generated whole-caller template has 83 external function declarations:
69 ordinary Rust/core/alloc operations and 14 protocol/platform groups.
Thirty-four of the 69 ordinary declarations now have executable definitions
in the focused accepted graph, leaving 35 ordinary templates to fill or
classify.
The protocol/platform set is:

- `qm31_dot3`;
- the two static inactive-schedule accessors;
- Solana `set_return_data` and `Clock::get`;
- five exact PDA wrappers;
- `readonly_account_metadata_v1` (closed in this bundle);
- `borrow_readonly_account_data` (closed for borrow-ready production entry;
  literal `RefCell` dynamic-borrow behavior remains a named platform boundary);
- `sbf_hashv`;
- Pubkey equality/construction/byte conversion.

The PDA, SHA-256, Solana syscall/borrow/return-data and remaining Rust library
semantics must be supplied by focused source bridges or retained explicitly as
platform assumptions.  The already existing Poseidon, SHA, semantic-terminal,
Registry V2 and K1 boundaries are not weakened here.

## Extraction normalization

`toolchain/literal-caller-current309b-to-accepted-source.patch` followed by
`toolchain/literal-caller-exact-six-len-preflight-normalization.patch` is the
canonical replay sequence.  Applying both to the pinned commit reproduces
source hashes:

- `v7_verifier.rs`: `ede2541418bb566d9dada7598d49b3acb41a3b4636f47446a65f274761b1641c`;
- `v7_pair_forest_dispatch.rs`: `39d280b72c19c8fa0e3f0b8e06bd3df26fe4b7ae0e87e94873b0a59f1737d5a5`.

The older experiment-by-experiment fragments are retained only under
`evidence/superseded-fragments/`; they are not the replay interface.  Failed
borrow/source shapes and the rejected generic Aeneas patch are under
`evidence/rejected/`.

`toolchain/borrow-readonly-owned-result-probe.patch` is a diagnostic only.  It
keeps the exact production borrow and `Ref::map`, consumes the guard locally,
and returns only an owned length.  Charon succeeds, but Aeneas still fails at
the same nested mutable projection.  This proves the obstruction is the
literal Solana `RefCell` borrow itself, rather than the guard escaping the
helper.  The exact evidence and model scope are in
`BORROW-READY-BOUNDARY.md`.

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
