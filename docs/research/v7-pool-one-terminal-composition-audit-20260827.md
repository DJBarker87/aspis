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

The viable route is deletion rather than moving the prepared work into one
call. The primary candidate keeps the 30,504-byte proof independent of the live
append state: it proves the historical spend relation and exact output pair,
then the locked Pool computes the twenty current append parents during the same
terminal instruction. A late Tag-73 Stage-B append proof remains a fallback,
not the default, because its exact wire cost is materially larger.

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
| Current Pool/page source binding | Preparation hashes exact images into ASPS; settlement re-hashes them and also checks field slices | Decode the locked current state once under the Pool write invariant, carry its sealed token across the read-only verifier CPI, and apply the verified output pair to that exact state. |
| History distribution and output-page construction | Preparation builds current/rollover images; settlement reconstructs and compares them | Keep only one checked chronological root append. Write the verified new root into its exact slot and update the page header. |
| Plan encoding, SHA authentication and source-image digests | 10,000-byte ASPS plus optional 8,504-byte ASRS | Delete completely from the terminal route. |
| Plan PDA creation, zero/rent rechecks and full-image copies | `processor.rs:1138-1232` | Delete completely. |
| Plan decoding and exact-image comparisons | `prepared_settlement.rs:866-1021` | Delete completely. |
| Plan close, tombstone and refund | `processor.rs:1728-1746` | Delete completely. There is no terminal plan account. |
| Poseidon tree append | Preparation only | Compute one pair append from the locked current frontier exactly once in the terminal suffix. The proof authenticates the output pair; there is no prepared duplicate. |
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
| Live append root/frontier | Not part of the primary proof | Read only after the terminal transaction locks the Pool; the Pool computes the one pair append against that exact state. |
| Completed 30,504-byte proof | Yes | Remains valid across intervening appends while its historical membership root is retained and its nullifier remains fresh. |
| Late 800-byte snapshot and Stage-B suffix | Fallback only | Required only by the proof-carried-append alternative; that completed fallback proof is stale after a competing append. |
| Generic proof-body digest, ASRA and ASPS/ASRS images | Not needed | Deleted from the one-terminal profile. |

## Append semantics that must remain in the terminal transaction

The primary route keeps the append decision and its deterministic arithmetic in
the terminal transaction. It must do all of the following:

1. read and canonically decode the live Pool-owned state;
2. authenticate the independently retained historical membership root;
3. invoke the registry-selected Tag-73 profile and require immediate
   authenticated success for the historical spend, nullifier and exact output
   pair;
4. compress that verified output pair and compute exactly twenty Poseidon
   parents from the currently locked pair-tree frontier;
5. persist exactly the locally computed next sequence, root and frontier;
6. append exactly one new root chronologically to retained history, including
   rollover routing;
7. create/populate the exact fresh nullifier marker once;
8. for withdrawal, execute and delta-check the exact authenticated token
   transfer; and
9. expose success only after every write/CPI has completed.

There is no second append computation: ASPS preparation is absent. Since the
proof does not bind a prospective current append root, another user's append
does not make its bytes stale. Solana's writable lock serializes the terminal
state read and write, and the Pool applies the verified output pair to whichever
canonical current state it actually locked. Historical membership and current
append roots therefore remain separate without a proof-rebuild race.

The proof-carried fallback has different concurrency. It absorbs an exact
800-byte live snapshot after `lambda, chi`; any competing append then requires
rebuilding Stage B and the entire downstream suffix.

## Why the pair tree is the minimum viable append relation

The current Pool stores two transfer outputs as two sequential depth-20 leaf
appends. Proving both upper paths would require forty additional Poseidon
blocks and does not fit the frozen 64-block semantic trace.

The already frozen production-inactive staged pair profile computes one
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

That 48-row result closes the staged fallback's geometry, but it is not the
primary wire choice. Omitting the twenty live append blocks from the proof
leaves the 34 stable Poseidon blocks plus the same seven auxiliary blocks: 656
allocated rows and 368 unused rows. Its tuple registry, mask rank and generated
terminal still require a separate exact compilation; this audit does not infer
them merely by subtracting rows.

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
   contain pair sequence/index, current root and twenty frontier digests. Do not
   reinterpret the current `ASTS` tree format.
2. **Stable pair Tag-73 profile.** Compile the 34 stable pair-relation Poseidon
   blocks, occupancy residuals and output-pair binding into the existing
   30,504-byte geometry. Preserve q16, digest-208, work 35/31/34, degree 27 and
   the existing one-fold backend.
3. **Digest-free sealed-proof dispatch.** Replace the generic proof-body-digest
   ASVQ path for this profile by exact finalized account identity/length and
   immediate selected-program return authentication. Keep registry policy,
   program/profile/release and statement binding.
4. **Compact verifier result.** Return only an exact success image (and,
   optionally, the already verified 32-byte output-pair digest) rather than
   echoing the sealed request. The Pool already retains the statement, selected
   program, proof account, profile and release across the immediate read-only
   CPI. The runtime identifies the return-data writer, and the source bridge
   must prove that the selected handler emits a result only after accepting that
   exact CPI instruction and proof account. Consequently every identity binding
   is derived from the caller's sealed values and need not be serialized back
   by the callee. If the Pool computes the pair compression itself, the minimum
   candidate is an 8-byte success image. If the source bridge exposes the
   relation's already computed pair digest, the candidate is 40 bytes:

   ```text
     8  magic/version/kind/success/reserved
    32  optional verified output-pair digest
   ---
  8/40 bytes
   ```

   This is a size screen, not yet a frozen wire. Omitting the echoes is sound
   only with the immediate-CPI/sealed-plan source theorem just stated. It does
   not remove any statement/profile binding from the request or proof.
5. **Single-append atomic suffix.** Add one Pool instruction which consumes that
   result and the sealed marker preflight, performs exactly one pair-tree append
   from the locked current frontier, optional withdrawal custody, writes the
   exact state fields and one chronological root slot/header, writes the marker,
   and emits a versioned pair-tree `ASTR`. It has no ASPS, ASRS or ASRA account
   and no duplicated append.
6. **Rollover policy.** Prefer a pre-existing canonical zero/rent-exempt next
   root page in the first CU gate. Page creation is setup plumbing, not proof
   authorization. A later worst-case gate must separately show whether
   same-terminal System creation also fits; production cannot silently assume
   it without an account-policy and runtime theorem.

The smallest source cut is therefore a new versioned sibling of
`process_private_transfer_with_runtime_v1`/`process_withdrawal_with_runtime_v1`
and one pair-append helper beside
`apply_authorized_append_after_checked_state_v1`. The new helper replaces the
current two-single-leaf `source.prepare(request)` path at `transition.rs:697`
with one pair append authorized by an opaque verifier-result token whose
constructor is private to the immediate CPI-return parser. Existing account uniqueness, signer/owner,
canonical PDA, history routing, writable-shape, capacity, checked arithmetic,
token-account/delta, and all-before-success checks stay in place. No existing
instruction tag or state format should silently change meaning.

### Selected-program code identity

The current registry authenticates an executable account's program id plus the
exact profile and release bindings. It accepts legacy BPF, upgradeable-loader
and loader-v4 owners, but it does not inspect ProgramData or prove that the
selected program's deployed bytes cannot change. The registry's own
`IMMUTABLE` flag freezes registry governance; it does not make an upgradeable
verifier program immutable.

This does not require a larger verifier result and should not be charged to the
cryptographic CU profile. It is nevertheless a hard release gate: the signed
deployment manifest and startup checks must pin the selected program's loader,
deployed executable hash and upgrade authority, and the production release must
either be immutable or use the explicitly reviewed governance policy. A future
on-chain ProgramData check is optional defence in depth; until implemented,
program upgradeability remains an explicit operational/Solana trust boundary.

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
49-block relation and old atomic state, not the pair profile. The stable pair
relation has 34 rather than 49 proof-side Poseidon blocks, while the Pool adds
one pair compression and twenty execution-time append parents. Generic dispatch
SHA passes and all plan machinery are deleted. No numerical net saving may be
claimed before an instrumented same-binary run.

The staged proof-carried alternative is not a 30,504-byte proof. The exact Lean
wire theorem `exact_staged_wire_cost_if_four_late_lanes_authenticated` gives
34,658 bytes: 4,154 bytes more, five additional upload chunks, and 64 additional
C2 leaf SHA-256 message blocks across q16. It also makes completed proofs stale
after a competing append. That route is retained only if exact measurement
shows the twenty execution-time parents cannot fit.

One older V6 component probe measured its complete 49-block Poseidon terminal
segment at 88,217 CU. Scaling that observation gives about 37,807 CU for 21
permutations, but this is design pressure only: different wrappers, routing and
compiler output prevent citing it as a pair-append measurement. It is sufficient
reason to measure the small execution-time append before building a proof format
which is already known to add 4,154 bytes.

The production engineering gate should be split without repeated regression
runs:

1. measure the stable 30,504-byte pair verifier alone, with exact proof and
   compact result;
2. measure the one-pair Pool append/suffix with a verifier transport double;
3. perform one combined private-transfer same-page run;
4. perform one combined private-transfer rollover run; and
5. perform one combined withdrawal run with real SPL Token CPI.

Every final case must be `< 1,400,000 CU`. A practical release target is
`<= 1,350,000 CU`, preserving at least 50,000 CU against small runtime and
wrapper variation. Until steps 1 and 2 exist, there is no honest ETA or
guarantee that the combined path will meet this gate.

## Formal/source closure map

Already kernel checked or source-closed:

- algebraic occupied/empty slot semantics and spendability;
- historical-membership versus live-append root roles;
- exact staged 54-block/976-row/48-row/degree-27 geometry and exact 4,154-byte
  staged wire penalty;
- ordinary Pool tree append, chronological root-history routing, page rollover,
  byte codec and mutable-store source bridges;
- verifier-registry authorization source bridge; and
- pure nullifier freshness and atomic settlement models.

Still required for the one-terminal profile:

1. literal Rust tuple/residual registry and terminal equal the stable pair Lean
   model;
2. prover and verifier bind the exact historical spend and occupied output-pair
   semantics without a live append snapshot;
3. accepted Tag-73 pair proof authorizes exactly the output pair consumed by
   the terminal append;
4. pair-tree Pool bytes decode under the inductive state invariant and the
   single execution-time append produces the exact next bytes;
5. compact return bytes decode to exactly the accepted verifier result;
6. finalized proof-account identity/immutability replaces the removed body
   digest without weakening binding;
7. literal Pool success composes registry selection, verifier result, current
   pair append, chronological history write, marker single-use and optional
   custody delta into the atomic Lean state transition;
8. duplicate marker, malformed result, wrong selected program, wrong page and
   every late CPI failure select Solana rollback/no afterstate;
9. Aeneas reaches the literal production caller, with only named SHA,
   Poseidon, Solana account/CPI/rollback and source-tool boundaries; and
10. exact SBF build, CU, v0+ALT wire, adversarial lifecycle and finalized
    devnet evidence are replayed from a clean commit.

The existing prepared-plan source proofs remain valid audits of that optional
experimental lifecycle. They do not discharge any of items 1-10 merely by
showing that a two-transaction plan is authenticated.
