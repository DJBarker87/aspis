# Pool V1 prepared-settlement kernel (2026-08-26)

## Status and scope

This checkpoint is a host-checked, crate-private kernel. It is **not** a public
instruction, an SBF measurement, a LiteSVM lifecycle result, or a deployable
settlement path. In particular, it does not create/allocate the plan PDA,
persist any image, invoke the System or token programs, transfer a withdrawal,
close/refund a plan, or emit return data.

The purpose of the kernel is to move both depth-20 Poseidon append operations
out of the final atomic transaction while preserving the exact direct Pool V1
state transition. Preparation performs the checked append and constructs an
authenticated plan; final apply uses SHA-256 and byte comparisons only.

## Canonical plan

The `ASPS` V1 plan has one exact 18,192-byte representation. Its trailing
domain-separated SHA-256 digest authenticates every preceding byte. The
Pool-owned PDA is derived from:

```text
[b"aspis-settle-plan-v1", pool, statement_digest,
 source_sequence_le, plan_authority]
```

The 18,192-byte monolith exceeds Solana's 10,240-byte per-instruction account
data-increase limit. The next processor therefore cannot use the generic
one-shot `create_or_allocate` path: it must use authenticated staged
pending-plus-reallocation, or preferably two hash-bound shards each smaller
than 10,240 bytes.

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
NO_DNA=1 cargo test -p aspis-pool prepared_settlement -- --nocapture
```

Result: **10 passed, 0 failed, 49 filtered out**.

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
  retirement between preparation and settlement.

The touched Rust files also pass a file-scoped `rustfmt --check`.

## Mandatory next checkpoint

The current 18,192-byte monolithic plan exceeds Solana's 10,240-byte maximum
per-instruction account-data increase. The public processor therefore must not
reuse the generic one-shot PDA creator: it must either use a fail-closed staged
pending/reallocation protocol or, preferably, split the plan into two mutually
hash-bound PDAs whose individual images are each below that limit.

The next commit must add the public processor/instruction composition and test
it under SBF/LiteSVM. That processor must, in one locked call:

1. require the exact plan authority signer when creating/funding a plan PDA;
2. enforce all signer/writable/owner/alias constraints;
3. reauthenticate the live registry using the same `Clock` settlement slot;
4. re-plan the actual marker account and atomically create/populate it;
5. copy the authenticated Pool/history images;
6. execute and balance-check the authenticated withdrawal token CPI, if any;
7. expose success-only return data; and
8. enforce close/tombstone/refund behavior without enabling replay.

Only after that composition has strict 1.4M-CU runtime evidence may this be
described as an atomic prepared-settlement transaction.
