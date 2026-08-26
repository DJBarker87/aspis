# Pool V1 prepared-settlement kernel (2026-08-26)

## Status and scope

This checkpoint now includes the public preparation instruction and public
final atomic settlement processor. It is host-checked and SBF-build clean, but
it is **not** a LiteSVM lifecycle/CU result or a deployable release. Preparation
persists the plan PDA(s); final settlement consumes them in one locked call,
creates/populates the nullifier marker, copies the authenticated next
Pool/history images, performs and balance-checks an authenticated withdrawal,
securely retires/refunds the plan accounts, and emits success-only `ASTR` data.

The purpose of the kernel is to move both depth-20 Poseidon append operations
out of the final atomic transaction while preserving the exact direct Pool V1
state transition. Preparation performs the checked append and constructs an
authenticated plan; final apply uses SHA-256 and byte comparisons only.

## Canonical plan

The `ASPS` V1 core has one exact **10,000-byte** representation. Bytes through
offset 9,904 preserve the original authenticated fields and precomputed next
Pool/current-page images. The final 96 bytes contain an optional rollover-shard
address, its SHA-256 digest, and the core's domain-separated SHA-256 digest.
The Pool-owned core PDA is derived from:

```text
[b"aspis-settle-plan-v1", pool, statement_digest,
 source_sequence_le, plan_authority]
```

When no rollover occurs, the shard address/digest are zero and supplying a
shard is rejected. A rollover uses one exact **8,504-byte** `ASRS` account:
16-byte header, core/program/Pool/statement/source-sequence/authority/next-page
bindings, the exact 8,256-byte rollover-page image, and a domain-separated
SHA-256 digest. Its PDA is derived from:

```text
[b"aspis-settle-roll-v1", core_plan_address]
```

The core authenticates the shard address/digest; the shard authenticates the
core address and all transition-identity fields. Both account sizes are at or
below Solana's 10,240-byte per-instruction account-data-increase limit, so each
can use the Pool's one-shot signed PDA creator without staging or realloc.
The builder allocates the 10,000-byte core first and writes the updated current
history page directly into its final slice. It then allocates the optional
8,504-byte shard and writes the rollover page directly into that final slice.
No standalone 8,256-byte history-page staging buffers coexist with the two
outputs; a compile-time bound places the owned output images below the default
32 KiB SBF heap before runtime measurement.

The nonzero `plan_authority` is also the only accepted close/refund authority.
Including source sequence and authority prevents same-statement stale-plan
squatting and permits independent authorities to prepare parallel plans.

The authenticated body binds:

- Pool program, Pool identity, exact source sequence/root, and SHA-256 of the
  exact 1,000-byte source Pool image;
- exact current history-page address/image digest and, at rollover, exact next
  page address/zero-source digest;
- transition kind, canonical statement digest, nullifier, and ordered output
  commitments;
- exact verifier-owned 720-byte `ASRA` address and image digest;
- both exact append receipts and chronological roots for a private transfer;
- exact precomputed next Pool/current-page/optional-rollover-page images; and
- an activation/expiry interval.

## Preparation authorization

The exact public `ASPP` instruction is a fixed 24-byte timing/kind header plus
one byte-identical 432-byte canonical `ASPT` or `ASWD` spend instruction. The
nested kind is checked rather than trusted. Its account layout is canonical:

```text
plan_authority/payer (signer,writable), Pool (writable),
anchor page (read-only), [distinct current page (read-only)],
[fresh rollover page (writable)], finalized ASRA (read-only),
registry (read-only), entry (read-only), core plan PDA (writable),
[rollover shard PDA (writable)], System Program (read-only executable)
```

The processor rejects trailing/missing accounts, every account alias, wrong
owners, executable/signing data accounts, writable receipt/registry/history
inputs, a non-system payer, and noncanonical PDA addresses. It takes one Clock
slot, builds against the live registry and exact receipt/history/state images,
creates each required Pool PDA at its exact sub-10,240-byte size, rechecks
post-CPI owner/length/zero state and rent exemption, and only then copies the
authenticated image. An exact-size, program-owned zero account is rejected if
it is underfunded, closing the same-transaction revival/non-persistence path.
Any later failure rolls all preceding creations back atomically.

Preparation accepts only a canonical verified `ASRA` wrapper. It recomputes
the request, statement and binding digests, validates the receipt PDA under
the selected verifier, binds the exact 720-byte image, and rejects a writable,
signer, executable or aliased receipt account.

The receipt-derived verifier program/profile/release/statement-version is
authenticated against the Pool state's exact registry policy and active entry
at the preparation slot. The resulting registry capability is sealed: its
fields are private and it records both the exact `VerifierPolicyV1` used for
authentication and the exact authentication slot. Apply decodes the canonical
policy from the hash-bound source Pool image and requires equality, so an
attacker registry authenticated under a fabricated policy is not a substitute.

The statement's canonical historical-anchor envelope is recomputed and its
digest must equal the receipt binding. The exact historical root is then
authenticated against retained Pool history before the current page is
validated. Only after those gates does preparation use the sealed canonical
Pool/tree token to compute the append result.

## Final pure apply gate

Apply reauthenticates the plan, source images, statement, exact `ASRA`, ordered
commitments, receipts, roots, page writes, time interval and Pool/nullifier
bindings. It requires a sealed registry capability authenticated at the exact
settlement slot; a capability from the preceding slot is rejected even when
all selected identities match. The final processor re-reads the live registry,
so pause/inactivation/retirement between preparation and settlement fails
closed.

The nullifier input is also a sealed `PlannedNullifierMarkerV1`, obtainable only
by validating the actual writable marker account. The final processor obtains
it in the same locked settlement call and atomically creates/populates the
marker with the Pool/history/custody writes.

Apply returns a sealed authenticated action. For withdrawals it exposes the
canonical amount and destination token account derived inside the receipt- and
statement-authenticated parse, so the custody processor need not perform a
second unchecked parse.

There is no Poseidon or Merkle append in the apply function or its byte-checking
helpers. Poseidon remains in preparation and direct-path parity supplies the
cryptographic provenance of the precomputed frontier/root images.

## Public final atomic settlement

`ASPF` is exactly 224 bytes: an 8-byte canonical header followed by the exact
216-byte `ASCP` or `ASWP` statement authenticated by the plan and `ASRA`.
The nested statement kind is decoded and checked; wrong length, trailing bytes,
wrong magic/version/kind/digest encoding, nonzero reserved data and
noncanonical statements reject.

The account prefix is plan authority/payer (signer,writable,System-owned), Pool
(writable), current page (writable exactly when the first new root stays in the
page), and optional next page (writable, rollover only). The suffix is marker
(writable), finalized `ASRA` (read-only), registry (read-only), entry
(read-only), core `ASPS` (writable), optional `ASRS` (writable, rollover only),
and executable System Program. Withdrawal alone appends mint (read-only), vault
(writable), authenticated destination (writable), vault authority (read-only),
and executable original SPL Token program. The processor rejects every alias,
missing/trailing account, wrong owner, privilege, PDA, bump, executable state,
or exact plan length.

One `Clock::get()` slot drives receipt finality, registry liveness and plan
activation. The processor authenticates the exact source Pool/current/optional
next-page images through the pure apply gate before mutation. It then creates
or validates the rent-exempt marker PDA and, for withdrawal, executes one
legacy SPL-token transfer signed by the canonical vault-authority PDA using
only the authenticated amount/destination. Exact pre/post vault debit and
destination credit are required.

Only authenticated next Pool/history images are copied. The marker is then
populated, the optional shard is retired before its authenticating core, and
each plan account is filled with a tombstone, refunded with checked lamport
arithmetic, assigned to System and resized to zero. `ASTR` return data is set
only after both closes succeed; the entrypoint clears return data before
dispatch and on every error. The spent marker plus retired plans reject replay,
while exact owner/length checks and rent-exempt creation rules resist revival.
Private transfer retains both ordered outputs and emits the normal 1-to-2
receipt.

## Focused evidence

Command:

```text
NO_DNA=1 cargo test -p aspis-pool prepared_settlement --lib --no-default-features
```

Result: **17 passed, 0 failed, 50 filtered out**.

The exact `ASPF` wire test also passes independently:

```text
NO_DNA=1 cargo test -p aspis-pool settle_prepared --lib --no-default-features
```

Result: **1 passed, 0 failed, 66 filtered out**.

The focused cases cover:

- byte-exact withdrawal and private-transfer parity with the direct path;
- both chronological roots across the 254 -> 256 page boundary;
- mutation of every plan byte;
- stale source Pool/current/next page, receipt and time;
- reauthenticated root, append-receipt and output-order substitution;
- statement/nullifier substitution using a genuinely validated marker plan;
- authority, source-sequence, parallel-authority and close/refund bindings;
- pending/bad-digest/bad-PDA/bad-binding/altered-nested `ASRA` rejection;
- a fully self-consistent receipt for a non-Pool historical root; and
- paused/inactive/wrong-program/wrong-profile registry selection plus
  retirement between preparation and settlement;
- exact public `ASPP` core persistence with authority/privilege/alias
  rejection; and
- exact rollover core+shard persistence while leaving the fresh rollover
  history page zero for final settlement; and
- fail-closed rejection of underfunded program-owned zero rollover-page, core
  and shard accounts before any plan bytes are persisted;
- final private-transfer rollover with exact 1-to-2 images/receipt, authority
  and alias rejection, shard/core retirement/refund, replay rejection and no
  failure return data; and
- withdrawal driven by the authenticated amount/destination with exact
  vault/destination deltas, marker/state/history persistence, core retirement
  and success-only `ASTR`.

The touched Rust files pass file-scoped `rustfmt`, `cargo check`, the mandatory
Solana program autofixer, and `cargo-build-sbf`. The final SBF build reports no
stack-offset/frame-clobber diagnostic; the authenticated statement aggregate is
heap-owned so the exact composition stays below the 4 KiB SBF frame limit.

## Remaining release gate

The exact atomic processor composition is present and SBF-build clean. The
remaining focused gate is a validator/LiteSVM lifecycle run proving System CPI
creation/rent behavior, real SPL-token CPI and close semantics, rollback after
an already successful CPI followed by a later outer error, serialized
transaction/account-lock feasibility, and strict 1,400,000-CU headroom for both
non-rollover and worst-case private-transfer rollover. Until that evidence is
recorded, this is an atomic prepared-settlement checkpoint rather than a
deployable release.
