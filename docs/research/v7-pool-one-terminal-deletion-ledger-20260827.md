# V7 Pool one-terminal deletion and CU ledger

Date: 2026-08-27

Audit base: `200c2eb974b4a66304aee425c2feb599556fd0ab`

Scope: the direct Pool private-transfer call graph, Tag-73 read-only CPI,
pair-tree append alternatives, return-data coverage, and Solana execution
constraints. This audit changed no production program, proof system, deployed
account, or network state.

## Decision

The frozen-proof, execution-time append route does not fit with the current
Poseidon implementation. A focused SBF/LiteSVM measurement of the literal
production `pool_v1_tree_parent` reports 469,391 incremental CU for twenty
parents and 492,863 CU for a pair compression plus twenty parents. The frozen
V7 verifier's measured 1,258,013 CU leaves only 141,987 CU under 1.4M.

Even granting every explicit duplicate-SHA deletion in this ledger, the
optimistic projections which retain the measured Tag-73 profile are:

| Frozen 30,504-byte proof route | Projected CU | Over 1.4M |
| --- | ---: | ---: |
| verifier + returned pair digest + 20 Pool parents - duplicate SHA | 1,680,407 | 280,407 |
| verifier + Pool pair compression + 20 Pool parents - duplicate SHA | 1,703,879 | 303,879 |

These projections omit all Pool parsing, registry checks, CPI overhead, PDA work,
history/marker creation, account writes and receipt serialization. Route B is
therefore rejected for the current measured Tag-73 and Poseidon
implementations, not merely unmeasured. The 1,258,013-CU evidence includes the
old atomic wrapper, so the table is not a same-binary measurement; reopening B
would require the new read-only verifier/composition to recover more than
280,000 additional CU beyond every SHA deletion listed here, then also fit all
omitted Pool work.
A compatible custom tree-hash implementation would need a separately proved
cryptographic equivalence and a very large measured speedup before reopening
it.

The proof-carried append route remains the only evidenced near-term
one-terminal candidate. Its corrected maximum body is 35,216 bytes, 4,712
bytes more than the stable 30,504-byte maximum, and it adds 64 C2 leaf SHA-256
message blocks. The correction retains four packed late QM31 wire lanes but
opens and gamma-binds all sixteen underlying logical M31 trace columns. It removes
the native twenty-parent append, but a completed proof is tied to one live
Pool snapshot. A competing append makes those final bytes stale; only its
expensive Stage A is reusable. This is optimistic concurrency, not a
wait-free append.

## Current production call graph

The direct private transfer is dispatched by
`programs/aspis-pool/src/processor.rs:1863-2023`:

1. decode the 432-byte Pool instruction;
2. decode the complete 1,000-byte Pool state and reconstruct its depth-20
   root (`state.rs:93-115`);
3. validate historical/current history pages, unique accounts, marker and
   rollover page;
4. derive a proof claim, including a complete proof-body SHA-256
   (`verifier_dispatch.rs:56-90`);
5. plan the selected registry dispatch, reparsing and rehashing the proof body
   (`verifier_dispatch.rs:171-303`);
6. construct and clone a 600-byte ASVQ request, invoke the verifier read-only,
   copy its 384-byte ASVS return data, decode it and compare every byte
   (`verifier_dispatch.rs:355-381`);
7. create the rollover page if required;
8. append recipient and change as two independent depth-20 leaves, create the
   marker, persist Pool/history, and return a 200-byte receipt.

Inside the verifier (`programs/aspis-verifier/src/v7_pool_native_dispatch.rs`):

1. decode ASVQ and recompute its statement digest;
2. decode the profile statement;
3. reconstruct and hash the 208-byte historical envelope;
4. parse the proof-account header and hash the complete proof body a third
   time (`:167-179`);
5. call Tag-73, whose proof grammar is parsed once at
   `v7_verifier.rs:215-245`;
6. encode and set a 384-byte ASVS result.

The existing atomic Tag-73 wrapper directly verifies the finalized proof body
without a generic body digest (`v7_transaction.rs:48-96`). This demonstrates
that the three outer body hashes are dispatch redundancy, not part of the
Tag-73 cryptographic transcript.

The populated-tree native Poseidon inventory is exactly sixty parent calls:
twenty to reconstruct and validate the source root, then two twenty-parent
appends. `incremental_merkle.rs:181-225` makes each append exactly depth 20;
`:372-398` is the source reconstruction. The cheaper program-invariant decoder
at `programs/aspis-pool/src/state.rs:117-147` avoids the first twenty only if
every initialization and mutation path is source-proved to preserve the
root/frontier invariant.

## Exact deletion ledger

Agave 4.2.1 charges one-slice SHA-256 as
`85 + max(10, floor(bytes / 2))` CU. For a 30,504-byte proof body that is
15,337 CU per pass. The figures below credit only explicit SHA syscall cost;
they deliberately do not guess VM copying, parsing, allocation or branch
costs.

| Deletion | Current source | Count | Conservative saving |
| --- | --- | ---: | ---: |
| Pool claim full-body SHA | `aspis-pool/src/verifier_dispatch.rs:56-90` | 1 | 15,337 CU |
| Pool planner full-body SHA and duplicate header parse | `verifier_dispatch.rs:171-217` | 1 | 15,337 CU plus uncredited parsing |
| Verifier full-body SHA and duplicate header parse | `aspis-verifier/src/v7_pool_native_dispatch.rs:167-179` | 1 | 15,337 CU plus uncredited parsing |
| **Three full proof-body passes subtotal** |  | **3** | **46,011 CU** |
| Duplicate statement digests | request binding/encoding and ASVQ decoding | 2 of 3 | 558 CU |
| Redundant envelope digests | Pool binding and verifier reconstruction | 2 | 428 CU |
| **Gross exact SHA saving** |  |  | **46,997 CU** |

The fixed route can safely remove all three proof-body digests only as one
coherent change: the finalized proof account is verifier-owned, read-only and
locked for the CPI; Tag-73 consumes the exact same bytes; the Pool checks the
returning program id and selected registry release. A body mutation is thus
either impossible during execution or changes the bytes Tag-73 actually
verifies. This deletion must be source-bridged, not applied piecemeal while
retaining a caller-supplied digest claim.

The statement digest remains cryptographic transcript input and must be
computed once. The two extra computations are removable by making the
verifier-derived digest the authenticated result and comparing it with the
Pool's one expected digest. The envelope digest is redundant because every
envelope field is already in the exact request/result binding.

Further duplicated work is real but receives zero CU credit until measured:

- the 208-byte envelope is decoded, re-encoded and decoded again;
- the 216-byte statement is copied into a 600-byte ASVQ and decoded again;
- the Pool constructs expected ASVS bytes, the verifier constructs actual
  ASVS bytes, the runtime copies 384 bytes, and the Pool decodes plus compares;
- the CPI instruction clones the 600-byte request and two AccountInfos;
- marker planning is repeated before and after the verifier CPI;
- page PDAs and account readiness are checked at layout, creation and append
  boundaries, especially on rollover.

The correct optimization is a typed sealed preflight object whose fields are
consumed after the read-only CPI. It must preserve account locks, registry
selection and immediate return-data capture; it must not replace checks with
caller-provided booleans or digests.

## Route A versus Route B

| Property | A: proof-carried append | B: Pool execution-time append |
| --- | --- | --- |
| Maximum proof body | 35,216 bytes | 30,504 bytes |
| Added proof bytes | 4,712 | 0 |
| C2 leaf SHA work | +64 message blocks | unchanged |
| Semantic Poseidon schedule | 34 stable + 20 late = 54 blocks | 34 stable blocks |
| Pool-native tree work | 0 parents after verified after-state | 20 if pair digest returned; 21 if Pool recompresses |
| Current implementation CU | staged verifier not yet measured | 469,391 / 492,863 incremental CU: cannot fit |
| Completed-proof concurrency | pinned to one live snapshot; stale after competing append | append uses the current locked state; no proof staleness |
| State trust | proof checks source-to-afterstate | program-owned inductive root/frontier invariant plus runtime append |

The exact Lean wire arithmetic for A proves 30,504 -> 35,216 bytes, 32 -> 37
960-byte upload chunks, and the additional 64 C2 leaf SHA blocks. It also
proves that one completed proof cannot accept against two different live
snapshots. The late snapshot does not solve completed-proof staleness.

Route B can use only twenty Pool parents if the verifier returns the exact
output-pair digest already represented by stable semantic block 33. That is
not available in the current 384-byte ASVS, and a STARK verifier does not
automatically expose an internal trace cell. Production needs one of:

- make the block-33 output digest an exact public profile value bound by the
  terminal relation, then return it; or
- derive it in the selected verifier after acceptance and return it under a
  source-proved equality to the two statement commitments and occupancy kind.

The Pool must authenticate the returning program id, profile/release,
statement digest and returned pair digest before appending. With that bridge,
the conceptual inventory is 34 proof-side semantic blocks plus 20 Pool-side
parents. Without it, the Pool must recompress the pair: 34 + 1 + 20 = 55
blocks across proof and execution. Both runtime variants fail the current CU
gate by the measurements above.

## Conservative 968-byte layout and minimal 688-byte result

The originally audited conservative result is within Solana's 1,024-byte
return-data ceiling and has 56 bytes spare. This layout covers every Pool write
and echoes every identity binding for Route A:

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 16 | magic, version, success, transition kind, storage format, occupancy, reserved |
| 16 | 32 | exact statement digest |
| 48 | 32 | exact live-snapshot digest |
| 80 | 8 | source sequence |
| 88 | 8 | next sequence |
| 96 | 8 | next pair index |
| 104 | 32 | verified next current root |
| 136 | 640 | verified twenty-node next frontier |
| 776 | 8 | history page number |
| 784 | 8 | history slot |
| 792 | 32 | output-pair digest |
| 824 | 8 | appended pair-leaf index |
| 832 | 8 | retained membership-anchor sequence |
| 840 | 32 | Pool address |
| 872 | 32 | proof-account address |
| 904 | 32 | verifier profile binding |
| 936 | 32 | verifier release binding |

Required cross-checks are deterministic rather than conventions:

- private transfer has occupancy `11`; withdrawal has `01` and its second
  commitment is algebraically zero;
- `next_sequence = source_sequence + 1`;
- pair-leaf index equals the source pair index and next pair index increments
  exactly once;
- history page/slot is the canonical location of `next_sequence`;
- the next root is the root stored both in Pool state and history;
- the statement digest binds the retained historical root, nullifier, output
  commitments, value/custody data and withdrawal destination/amount;
- the live-snapshot digest binds Pool/domain/format, current sequence/index,
  current root and all twenty source frontier nodes;
- the returned program id separately equals the registry-selected executable.

Consequently that layout covers the versioned Pool state write, one history
root/header update, nullifier marker, withdrawal authorization, and receipt.
It is a conservative audit reference, not the minimum production wire.

The Pool caller already holds the exact statement, live state, selected program,
proof account, profile and release in a sealed preflight across the immediate
read-only CPI. History page/slot and the appended pair index are deterministic
from the old and new indices. Subject to the source theorem that the selected
handler emits return data only after accepting that exact CPI request and proof
account, none of those values need to be echoed. The minimum candidate is:

| Bytes | Field |
| ---: | --- |
| 8 | magic/version/kind/success/reserved |
| 8 | next pair index |
| 32 | verified next pair-tree root |
| 640 | verified twenty-node next frontier |
| **688** | **total** |

The raw afterstate is exactly 680 bytes. The Pool must check the immediate
return-data program id, exact 688-byte length and version, canonical digest
encodings, exact locked old-state binding in the request, and
`next_pair_index = old_pair_index + 1` before any write. This removes identity
echoes, not identity checks. Route B would use a different, smaller result
because the Pool computes its own afterstate, but Route B is rejected by CU.

## Solana and security constraints

No account/CPI rule inherently prevents one terminal transaction:

- both the conservative 968-byte reference and preferred 688-byte result fit
  return data;
- the current 600-byte internal ASVQ plus an 800-byte snapshot would remain
  below the CPI instruction-data limit and is not outer transaction data;
- the verifier receives only its read-only proof account and executable
  program, not writable Pool/history/marker/vault accounts;
- the Pool captures return data immediately and checks its program id;
- the writable Pool lock serializes the live append state;
- page/marker creation, state writes and withdrawal CPI roll back atomically
  on failure;
- current CPI depth is shallow.

The remaining non-CU release gates are concrete:

1. freeze a v0-message/ALT account layout for private transfer, rollover and
   withdrawal and prove it fits the 1,232-byte transaction packet;
2. source-prove the pair-tree program invariant if root reconstruction is
   omitted;
3. source-prove that authenticated verifier success returns the exact
   statement-bound output pair/after-state;
4. keep historical membership acceptance separate from current append state;
5. pin upgrade/registry governance so a selected release cannot silently
   change code between audit and execution;
6. measure the final same-binary Route-A verifier and complete Pool suffix.

The limiting fact is therefore CU, followed by Route-A liveness under
concurrent appends—not Solana transparency or transaction atomicity.

## Focused runtime evidence

`audit/poseidon-pair-probe` builds a tiny SBF program around the literal
production parent and runs it in LiteSVM 0.16.0 / Agave 4.2.1. The transaction
totals were:

| Parent calls | Transaction CU | Increment over zero |
| ---: | ---: | ---: |
| 0 | 407 | 0 |
| 1 | 23,886 | 23,479 |
| 20 | 469,798 | 469,391 |
| 21 | 493,270 | 492,863 |
| 40 | 939,210 | 938,803 |

This isolates the implementation cost but does not claim the tiny probe has
the exact instruction overhead, register pressure or binary layout of the
eventual combined program. Its conclusion is nevertheless decisive here:
the twenty-parent delta alone exceeds all available verifier headroom by more
than 327,000 CU. Exact toolchains and artifact hashes are recorded in
`audit/poseidon-pair-probe/evidence.json`.
