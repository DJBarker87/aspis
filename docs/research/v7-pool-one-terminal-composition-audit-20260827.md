# V7 Pool one-terminal-transaction composition audit

Date: 2026-08-27

Status: read-only source/CU audit. No production Rust, verifier profile,
dispatch entrypoint, account format, deployment, or transaction was changed by
this checkpoint.

## Decision

The production target is one terminal transaction which both verifies the
transparent proof and atomically applies the Pool transition. Proof-account
creation and uploads may occur earlier. `ASPP -> ASPF` is not the production
architecture.

The existing prepared lifecycle is useful measurement and negative-design
evidence, but its two successful transactions cannot be concatenated:

```text
1,256,357 CU  ASPP preparation
  643,108 CU  ASPF settlement
-----------
1,899,465 CU  exact sum, before any Tag-73 proof verification
```

The viable route is deletion and proof-carried computation, not moving the
same work into one call. The twenty live append parents must be proved inside
the late Tag-73 Stage B and the terminal Pool suffix must perform only exact
source comparison, byte persistence, nullifier creation, optional custody CPI,
and success-data emission.

## What the measurements prove

Three measurements answer different questions and must not be presented as a
single executable profile.

| Evidence | Exact result | What it proves |
| --- | ---: | --- |
| Frozen V7 Tag-73 atomic execution | 1,258,013 CU | The old 30,504-byte proof, all work checks, old 80-byte atomic state and nullifier fit with 141,987 CU below 1.4M. |
| Current direct Pool private-transfer path with a 485-CU mock verifier | failed after consuming 1,399,850 CU | The current Pool path alone does not fit. The mock verifier is not cryptographic evidence. |
| Current prepared Pool lifecycle | 1,256,357 + 643,108 = 1,899,465 CU | Pool append/image preparation and later authenticated settlement each fit separately, but no proof verification is included. |

The direct-path red gate records 846,646 CU remaining when the mock verifier is
entered. Therefore the exact pre-verifier Pool prefix consumes:

```text
1,399,850 - 846,646 = 553,204 CU.
```

The mock consumes 485 CU and returns, leaving 846,161 CU, after which the
current append/marker/persistence suffix still exhausts the meter. Thus the
strict, directly measured lower bound for the current one-terminal source is
`> 1,399,850 CU` even without a real verifier. Replacing the mock by Tag-73 can
only increase this execution.

For design pressure only, adding the exact 553,204-CU prefix to the separately
measured 1,258,013-CU frozen V7 atomic transaction gives 1,811,217 CU before
the current Pool suffix. This is not a same-binary measurement and it
double-counts some small statement/state-wrapper work; it must not be cited as
an exact combined execution. It does show that ordinary local deduplication
cannot recover the required margin.

The ASVQ selected-verifier measurement is not available: the one attempted
profile simulation failed with `UnsupportedProgramId` before entering the
handler. Any CU claim for that handler is therefore currently unmeasured.

## Exact duplicated and removable work

### Across prepared construction and settlement

Preparation starts at `processor.rs:1052`; settlement starts at
`processor.rs:1513`.

| Work | Current execution | One-terminal disposition |
| --- | --- | --- |
| Pool state decode, format and identity checks | Preparation at `processor.rs:1068`; settlement at `processor.rs:1530` | Decode once at terminal entry and keep a sealed source token across the read-only verifier CPI. |
| Statement and finalized authorization-receipt authentication | Preparation through `build_prepared_settlement_plan_v1`; settlement first at `processor.rs:1556-1563`, then again inside `apply_prepared_settlement_plan_v1` | Delete ASRA from the terminal route. The selected verifier accepts the exact statement and returns a profile-specific verified result in the same transaction. |
| Registry selection | Preparation inside the builder; settlement at `processor.rs:1567-1574` | Authenticate the selected verifier once, at the terminal slot, immediately before CPI. |
| Current Pool/page source binding | Preparation hashes exact images into ASPS; settlement re-hashes them and also checks field slices | Compare one account-derived live snapshot to the proof's late snapshot. Account locking and the absence of a Pool account in the read-only CPI preserve it until writeback. |
| History distribution and output-page construction | Preparation builds current/rollover images; settlement reconstructs and compares them | Keep only one checked chronological root append. Write the verified new root into its exact slot and update the page header. |
| Plan encoding, SHA authentication and source-image digests | 10,000-byte ASPS plus optional 8,504-byte ASRS | Delete completely from the terminal route. |
| Plan PDA creation, zero/rent rechecks and full-image copies | `processor.rs:1138-1232` | Delete completely. |
| Plan decoding and exact-image comparisons | `prepared_settlement.rs:866-1021` | Delete completely. |
| Plan close, tombstone and refund | `processor.rs:1728-1746` | Delete completely. There is no terminal plan account. |
| Poseidon tree append | Preparation only | Move the necessary append equations into the late proof stage; do not execute a second on-chain Poseidon calculation. |
| Nullifier marker and withdrawal custody | Settlement only | Retain in the terminal transaction. These are state/economic effects, not reusable preparation. |

The prepared lifecycle's historical-page/current-page concurrency fixture
remains useful: it proves that retained membership sequence 100 and live append
sequence 510 can be distinct. Its plan accounts and two terminal calls are not
carried into the production design.

### In the current direct verifier dispatch

The current direct path performs three full SHA-256 passes over the same
30,504-byte proof body before or during verification:

1. `derive_verifier_dispatch_claim_v1` hashes it at
   `verifier_dispatch.rs:56-90`;
2. `authenticate_proof_account_body_v1` hashes it again at
   `verifier_dispatch.rs:171-216`; and
3. the native Tag-73 handler hashes it again at
   `v7_pool_native_dispatch.rs:167-179`.

Tag-73's transcript verification does not require this whole-body digest; the
frozen direct atomic wrapper reads a finalized proof account and passes the
body directly to the verifier (`v7_transaction.rs:71-95`). The digest exists
for the generic ASVQ binding.

The one-terminal profile should instead bind a finalized, verifier-owned,
read-only proof account by program id, account key, exact finalized header,
exact body length, release/profile and attempt id. The selected verifier reads
that exact locked account and returns success for those bytes. This removes
the three wrapper SHA passes without removing any transcript hash, Merkle hash,
work hash, statement hash, or proof equation. The required source theorem is
that a finalized proof account cannot change between the Pool's preflight and
the selected verifier's read-only CPI.

The direct private-transfer source also plans the same marker twice: once at
`processor.rs:1945` before verifier dispatch and again at
`processor.rs:1994-1996` in the append callback. The CPI account list contains
only the read-only proof account plus the verifier program
(`verifier_dispatch.rs:363-368`), so neither the marker nor the Pool/history
accounts can be changed by the callee. A private sealed preflight token may be
carried to the persistence suffix instead of decoding and PDA-checking the
marker again. This is a small source simplification, not the primary CU
saving.

### What is reusable and what must be rebuilt

| Artifact or work | Reusable after an intervening live append? | Terminal use |
| --- | --- | --- |
| Stable Stage-A witness/trace and its commitment | Yes | Reused unchanged while the historical membership root remains retained. |
| Historical membership-anchor envelope | Yes, subject to retention policy and registry validity | Reauthenticated read-only in the terminal transaction. |
| Nullifier, output commitments, value/custody statement and output pair | Yes | Bound by both the stable proof prefix and the final terminal statement. |
| Live 800-byte append snapshot | No | Must be reconstructed from the currently locked Pool state. |
| Twenty late append parents, Stage-B commitment and downstream proof suffix | No | Rebuilt whenever the live snapshot changes. |
| Verified next root, next pair index and twenty-node next frontier | Yes only for that exact live snapshot | Returned by the verifier and persisted byte-for-byte in the same successful transaction. |
| Generic proof-body digest, ASRA and ASPS/ASRS images | Not needed | Deleted from the one-terminal profile. |

## Append semantics that must remain in the terminal transaction

Moving Poseidon arithmetic into the proof does not move the state decision
off-chain. The terminal transaction must still do all of the following:

1. read and canonically decode the live Pool-owned state;
2. authenticate the independently retained historical membership root;
3. construct the exact 800-byte live append snapshot from the current Pool
   identity, deployment domain, pair sequence/index, root and all twenty
   frontier nodes;
4. invoke the registry-selected Tag-73 profile with that exact snapshot after
   `lambda, chi` and require immediate authenticated return data;
5. reject unless the verified transition's source snapshot is the live
   snapshot read in this same locked transaction;
6. persist exactly the verified next sequence, root and frontier;
7. append exactly one new root chronologically to retained history, including
   rollover routing;
8. create/populate the exact fresh nullifier marker once;
9. for withdrawal, execute and delta-check the exact authenticated token
   transfer; and
10. expose success only after every write/CPI has completed.

What need not remain as a second on-chain computation is evaluation of the
twenty Poseidon parent functions. The proof verifies those equations. The Pool
only checks that the proof started at the live locked snapshot and writes the
proved afterstate.

Staleness remains fail-closed. If another transaction changes the live Pool
before this terminal transaction locks it, the completed proof rejects. The
expensive stable Stage A is reusable; only the 20-parent Stage B and the proof
suffix must be rebuilt. This is optimistic concurrency, not a claim that old
final proof bytes survive a competing append.

## Why the pair tree is the minimum viable append relation

The current Pool stores two transfer outputs as two sequential depth-20 leaf
appends. Proving both upper paths would require forty additional Poseidon
blocks and does not fit the frozen 64-block semantic trace.

The already frozen production-inactive pair profile instead computes one
pair-leaf compression and twenty upper parents. Its exact trace inventory is:

| Region | Blocks | Rows |
| --- | ---: | ---: |
| Stable Poseidon work, including output pair | 34 | 544 |
| Late live append parents | 20 | 320 |
| Path auxiliaries | 6 | 96 |
| Value/occupancy auxiliaries | 1 | 16 |
| Unused | 3 | 48 |
| Total | 64 | 1,024 |

Lean proves 976 allocated rows, exactly 48 unused rows, and unchanged maximum
degree 27. The source constants are in
`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:216-263`; the root
roles and exact 800-byte snapshot are at lines 265-480.

Private transfer appends `(occupied recipient, occupied change)`. Withdrawal
appends `(occupied change, algebraically empty second slot)`. Spending a
selected second slot requires its occupancy field to equal one. Empty-slot
unspendability therefore comes from the proof relation, not an assumed
hash-without-preimage convention.

The pair-tree format binding is intentionally distinct. Existing single-leaf
Pool roots cannot be reinterpreted or migrated by assertion; production must
initialize a new versioned pair-tree Pool or prove an explicit migration.

## Smallest viable production shape

Keep the Pool program as the state owner and the verifier as a registry-selected
read-only CPI. Embedding the complete verifier into the Pool binary would
remove a small CPI/return-data layer but would discard the already implemented
registry boundary and greatly enlarge the source/reproducibility surface.

The minimum code changes are:

1. **Pair-tree state codec.** Add a versioned Pool state whose canonical bytes
   contain pair sequence/index, current root and twenty frontier digests. Add
   an exact source-to-`PoolV1PairLiveSnapshotV1` projection. Do not reinterpret
   the current `ASTS` tree format.
2. **Staged Tag-73 profile.** Compile the existing 54-block pair registry,
   occupancy residuals and late-snapshot transcript order into prover and
   verifier. Preserve q16, digest-208, work 35/31/34, degree 27 and the existing
   one-fold backend unless measurement forces a separately proved change.
3. **Digest-free sealed-proof dispatch.** Replace the generic proof-body-digest
   ASVQ path for this profile by exact finalized account identity/length and
   immediate selected-program return authentication. Keep registry policy,
   program/profile/release and statement binding.
4. **Compact verified transition result.** Return the source-snapshot binding
   and exact next sequence/root/frontier. A concrete 968-byte layout fits the
   1,024-byte Solana return-data maximum:

   ```text
    16  header/version/kind/status
    64  statement digest + live-snapshot digest
    24  source sequence + next sequence + next pair index
    32  next root
   640  twenty next-frontier digests
    16  root-history page/slot routing
    32  output-pair digest
    16  pair leaf index + retained-root sequence
   128  Pool + proof account + profile + release bindings
   ---
   968 bytes
   ```

   This is a size screen, not yet a frozen wire. Redundant fields may be
   removed, but no source/snapshot/profile binding may be omitted merely to
   save bytes.
5. **Byte-only atomic suffix.** Add one Pool instruction which consumes that
   result and the sealed marker preflight, performs optional withdrawal
   custody, writes only the exact state fields and one chronological root
   slot/header, writes the marker, and emits a versioned pair-tree `ASTR`. It
   must have no ASPS, ASRS or ASRA account and no Pool-side Poseidon call.
6. **Rollover policy.** Prefer a pre-existing canonical zero/rent-exempt next
   root page in the first CU gate. Page creation is setup plumbing, not proof
   authorization. A later worst-case gate must separately show whether
   same-terminal System creation also fits; production cannot silently assume
   it without an account-policy and runtime theorem.

The smallest source cut is therefore a new versioned sibling of
`process_private_transfer_with_runtime_v1`/`process_withdrawal_with_runtime_v1`
and one proof-carried write helper beside
`apply_authorized_append_after_checked_state_v1`. The new helper replaces the
current `source.prepare(request)` Poseidon call at `transition.rs:697` with an
opaque, authenticated verifier-result token whose constructor is private to
the immediate CPI-return parser. Existing account uniqueness, signer/owner,
canonical PDA, history routing, writable-shape, capacity, checked arithmetic,
token-account/delta, and all-before-success checks stay in place. No existing
instruction tag or state format should silently change meaning.

## Exact live accounts and bytes

The private-transfer terminal requires, at maximum rollover shape:

| Account | Privilege | Relevant bytes |
| --- | --- | ---: |
| payer | signer, writable | System account |
| pair-tree Pool | writable | versioned state; current V1 reference is 1,000 |
| retained anchor page | read-only | 8,256 |
| current root page | writable unless the first new root starts the next page | 8,256 |
| optional next root page | writable | 8,256 |
| nullifier marker | writable | 208 |
| registry | read-only | 128 |
| registry entry | read-only | 192 |
| selected verifier program | read-only, executable | program account |
| finalized proof | read-only | 40-byte header + 30,504-byte current reference body |
| System Program | read-only, executable | native |

Withdrawal adds the mint, vault, destination, vault authority and original SPL
Token program. The 10,000-byte ASPS, 8,504-byte ASRS and 720-byte ASRA are not
terminal accounts in this design.

Exact transaction serialization still requires a v0 message and a frozen ALT
for the worst withdrawal/rollover shape. This audit does not claim a measured
1,232-byte wire for the new account set.

## CU gate

The present 1,258,013-CU V7 result leaves 141,987 CU, but it is the old
49-block relation and old atomic state, not the pair profile. The pair profile
adds five semantic Poseidon blocks while deleting generic Pool dispatch SHA
passes and all plan machinery. No numerical net saving may be claimed before
an instrumented same-binary run.

The production engineering gate should be split without repeated regression
runs:

1. measure the staged pair verifier alone, with exact proof and compact result;
2. measure the byte-only Pool suffix with a verifier transport double;
3. perform one combined private-transfer same-page run;
4. perform one combined private-transfer rollover run; and
5. perform one combined withdrawal run with real SPL Token CPI.

Every final case must be `< 1,400,000 CU`. A practical release target is
`<= 1,350,000 CU`, preserving at least 50,000 CU against small runtime and
wrapper variation. Until step 1 exists, there is no honest ETA or guarantee
that the unchanged 30,504-byte pair proof will meet this gate.

## Formal/source closure map

Already kernel checked or source-closed:

- algebraic occupied/empty slot semantics and spendability;
- historical-membership versus live-append root roles;
- exact 54-block/976-row/48-row/degree-27 geometry;
- ordinary Pool tree append, chronological root-history routing, page rollover,
  byte codec and mutable-store source bridges;
- verifier-registry authorization source bridge; and
- pure nullifier freshness and atomic settlement models.

Still required for the one-terminal profile:

1. literal Rust tuple/residual registry and terminal equal the pair Lean model;
2. prover and verifier absorb the exact 800-byte snapshot after `lambda, chi`;
3. accepted Tag-73 pair proof implies the exact source-to-afterstate append
   relation and occupied output semantics;
4. pair-tree Pool state bytes project to exactly the verifier snapshot;
5. compact return bytes decode to exactly the accepted verifier result;
6. finalized proof-account identity/immutability replaces the removed body
   digest without weakening binding;
7. literal Pool success composes registry selection, verifier result, source
   snapshot equality, chronological history write, marker single-use and
   optional custody delta into the atomic Lean state transition;
8. stale snapshot, duplicate marker, malformed result, wrong selected program,
   wrong page and every late CPI failure select Solana rollback/no afterstate;
9. Aeneas reaches the literal production caller, with only named SHA,
   Poseidon, Solana account/CPI/rollback and source-tool boundaries; and
10. exact SBF build, CU, v0+ALT wire, adversarial lifecycle and finalized
    devnet evidence are replayed from a clean commit.

The existing prepared-plan source proofs remain valid audits of that optional
experimental lifecycle. They do not discharge any of items 1-10 merely by
showing that a two-transaction plan is authenticated.
