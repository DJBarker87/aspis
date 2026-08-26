# Pool V1 prepared-settlement kernel (2026-08-26)

## Status and scope

This checkpoint is a host-checked kernel plus public preparation instruction.
It is **not** an SBF measurement, a LiteSVM lifecycle result, or a deployable
final-settlement path. Preparation can create and persist the plan PDA(s) (and
an empty rollover history page when needed), but it does not create a
nullifier marker, mutate Pool/root-history state, invoke the token program,
transfer a withdrawal, close/refund a plan, or emit an `ASTR` receipt.

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
all selected identities match. This forces the future processor to re-read the
live registry, so pause/inactivation/retirement between preparation and
settlement fails closed.

The nullifier input is also a sealed `PlannedNullifierMarkerV1`, obtainable only
by validating the actual writable marker account. The future processor must
obtain it in the same locked settlement call and atomically create/populate the
marker with the Pool/history/custody writes.

Apply returns a sealed authenticated action. For withdrawals it exposes the
canonical amount and destination token account derived inside the receipt- and
statement-authenticated parse, so the custody processor need not perform a
second unchecked parse.

There is no Poseidon or Merkle append in the apply function or its byte-checking
helpers. Poseidon remains in preparation and direct-path parity supplies the
cryptographic provenance of the precomputed frontier/root images.

## Focused evidence

Command:

```text
NO_DNA=1 cargo test -p aspis-pool prepared_settlement --lib --no-default-features
```

Result: **15 passed, 0 failed, 49 filtered out**.

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
  and shard accounts before any plan bytes are persisted.

The touched Rust files also pass a file-scoped `rustfmt --check`.

## Mandatory next checkpoint

The split format and public preparation composition are host-green, but their
System CPI creation paths are not yet SBF/LiteSVM measured. The next checkpoint
must first prove creation/rent/heap/CU behavior for the 10,000-byte core and
optional 8,504-byte shard, then add the separate final-settlement processor.
That final processor must, in one locked call:

1. require the exact plan authority signer and exact core/optional shard;
2. enforce all signer/writable/owner/alias constraints;
3. reauthenticate the live registry using the same `Clock` settlement slot;
4. re-plan the actual marker account and atomically create/populate it;
5. copy the authenticated Pool/history images;
6. execute and balance-check the authenticated withdrawal token CPI, if any;
7. expose success-only return data; and
8. enforce plan/shard close, tombstone and refund behavior without replay.

Only after that composition has strict 1.4M-CU runtime evidence may this be
described as an atomic prepared-settlement transaction.
