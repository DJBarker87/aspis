# V7 Pool one-terminal-transaction composition audit

Date: 2026-08-27

Status: active source/CU audit. The pair-afterstate profile and Pool route are
still production-disabled, but their exact codecs, focused source prototypes,
and local LiteSVM evidence now exist. No deployment or network transaction was
performed.

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
call. An exact SBF/LiteSVM probe ruled out computing the current append inside
the Pool suffix: one pair compression plus twenty upper parents costs 492,863
CU over the zero-parent baseline before Pool parsing, history, marker or
custody work. The primary candidate therefore carries the live append through
late Tag-73 Stage B and returns the verified next pair-tree state. The Pool
terminal suffix only checks and byte-writes that result atomically with history,
nullifier and custody effects.

This primary route has a measured/formal cost which must be faced explicitly:
its maximum proof body is 34,658 bytes, 4,154 bytes larger than the frozen
30,504-byte maximum, and a completed proof becomes stale after a competing append. It remains
one terminal transaction; proof-account creation and uploads are preparatory
data transport, not a separate authorization or settlement transaction.

## What the measurements prove

These measurements answer different questions and must not be presented as a
single executable profile.

| Evidence | Exact result | What it proves |
| --- | ---: | --- |
| Frozen V7 Tag-73 atomic execution | 1,258,013 CU | The old 30,504-byte proof, all work checks, old 80-byte atomic state and nullifier fit with 141,987 CU below 1.4M. |
| Current direct Pool private-transfer path with a 485-CU mock verifier | failed after consuming 1,399,850 CU | The current Pool path alone does not fit. The mock verifier is not cryptographic evidence. |
| Current real native Pool proof, direct verifier only | failed after consuming the full 1,400,000-CU transaction limit | The current 30,192-byte single-leaf Pool relation verifier itself exceeds the limit. This is not the final staged pair profile. |
| Same proof after exact semantic-terminal prefactorization | **1,395,868 CU accepted** | The terminal fell from 821,667 to 407,973 CU, saving 413,694 CU without changing the proof, transcript, constraints, hashes, or cryptography. This establishes direct-verifier feasibility with only 4,132 CU headroom; it is not the final pair/Pool lifecycle. |
| Current real native Pool proof, combined direct Pool call | failed at 1,400,000 CU | The Pool consumed a 585,258-CU prefix, the verifier exhausted all 814,592 CU passed to it, no suffix ran, and Pool/history/vault/nullifier rolled back exactly. |
| Current prepared Pool lifecycle | 1,256,357 + 643,108 = 1,899,465 CU | Pool append/image preparation and later authenticated settlement each fit separately, but no proof verification is included. |
| Literal production Pool Poseidon probe | 20 parents: 469,798 CU total; 21 parents: 493,270 CU total | The zero-parent transaction costs 407 CU, so twenty upper parents add 469,391 CU and pair compression plus twenty parents add 492,863 CU. This rejects execution-time append under the present implementation. |
| Proof-carried byte-only Pool path with authenticated verifier transport double | **150,223 CU same-page; 119,206 CU rollover** | Pool parsing, registry selection, CPI/688-byte result transport, exact state/history/marker/custody persistence, and return fit with zero Pool Poseidon. This is isolated plumbing evidence, not a combined real-verifier measurement. |

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

The native selected-verifier result is frozen in
`results/pool-v1-one-terminal-runtime-20260827/`. The direct selected verifier
consumed the entire 1.4M-CU limit and failed before return. The combined call
therefore has a conservative deficit greater than 585,258 CU before any Pool
suffix. Its proof is 30,192 bytes with SHA-256
`656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c`;
it is a current single-leaf baseline, not evidence for the unbuilt 34,658-byte
staged pair verifier.

The exact post-prefactor phase ledger is frozen in
`results/v7-pool-terminal-cu-profile-optimized-20260827/`. Of the complete
1,395,868-CU transaction, the semantic terminal consumes 407,973 CU, the V7
two-tree authentication consumes 383,343 CU, and the authentication checkpoint
through verifier exit consumes 560,003 CU. The nonterminal direct-verifier
work is exactly 987,895 CU, so the terminal could consume at most 412,105 CU;
the prefactorization clears that direct gate by 4,132 CU.

The byte-only Pool evidence is frozen in
`results/pool-v1-pair-afterstate-litesvm-20260827/`. Its same-page path is the
conservative persistence case at 150,223 CU. Adding that independent number to
the optimized direct transaction is only a budgeting screen, because it
double-counts transaction/wrapper work and substitutes a transport double for
the real verifier. That screen is 146,091 CU above 1.4M before the larger
seven-lane pair proof and before a release margin. Therefore the next exact
target is at least about 180k CU of noncryptographic verifier/plumbing saving,
followed by a single integrated measurement; no independent totals will be
presented as proof that the lifecycle fits.

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
| Poseidon tree append | Preparation only | Move the one pair compression and twenty upper parents into late Stage B of the proof. The terminal suffix consumes the verified afterstate and performs no Pool Poseidon. |
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
| Live append root/frontier | No | Captured in the exact 800-byte late snapshot after `lambda, chi` and bound by Stage B. |
| Stable Stage-A proof prefix | Yes | May be reused while the historical membership root remains retained and the nullifier remains fresh. |
| Completed staged proof (at most 34,658 bytes) | No | Becomes stale after a competing append changes the current pair root/index/frontier. |
| Late 800-byte snapshot and Stage-B suffix | No | Must be rebuilt from the changed live state after a competing append. |
| Generic proof-body digest, ASRA and ASPS/ASRS images | Not needed | Deleted from the one-terminal profile. |

## Append semantics that must remain in the terminal transaction

The primary route keeps append authorization and every state/economic effect in
the terminal transaction, while the append arithmetic is proof-carried. It must
do all of the following:

1. read and canonically decode the live Pool-owned state;
2. authenticate the independently retained historical membership root;
3. invoke the registry-selected Tag-73 profile and require immediate
   authenticated success for the historical spend, nullifier, exact output
   pair and late current-state append;
4. receive the canonical verified afterstate containing next pair index, root
   and twenty frontier digests;
5. require its old-state binding to match the currently locked Pool, require
   `next_index = old_index + 1`, and persist exactly those verified bytes;
6. append exactly one new root chronologically to retained history, including
   rollover routing;
7. create/populate the exact fresh nullifier marker once;
8. for withdrawal, execute and delta-check the exact authenticated token
   transfer; and
9. expose success only after every write/CPI has completed.

There is no second append computation and ASPS preparation is absent. The
proof absorbs an exact 800-byte live snapshot after `lambda, chi`; a competing
append makes the completed proof stale and requires rebuilding Stage B and the
downstream suffix. Historical membership and current append roots remain
semantically separate, but this conservative design accepts optimistic
concurrency rather than pretending to have removed proof staleness.

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

That 48-row result closes the primary staged geometry. The exact Lean wire
theorem gives a 34,658-byte maximum: four late QM31 C2 lanes add 4,154 bytes, five upload
chunks and 64 C2 leaf SHA message blocks across q16.

A layout-only reduction from seven total C2 lanes to four is not sound in the
current protocol. The existing lanes are H1, G and D. G and D are independently
expanded over all 1,024 rows; H1 occupies copy-active rows and is independently
padded on the rest except its balance row. The late append occupies rows
544--863 and its copy links make those rows H1-active too. At a late row the
existing lanes carry twelve M31 coordinates and the late trace carries sixteen
more, while four QM31 lanes expose only sixteen coordinates. A fusion would
therefore change the hiding and terminal mathematics and require a new mask-rank
proof. It is not a serialization optimization. Even a hypothetical sound
four-total-lane redesign would be 31,542 bytes, not 30,504 bytes.

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
2. **Staged pair Tag-73 profile.** Compile the 34 stable relation blocks, twenty
   late current-append blocks, occupancy residuals and exact old/new pair-tree
   binding into the proven 54-block/976-row geometry. Preserve q16, digest-208,
   work 35/31/34, degree 27 and the existing one-fold backend. Freeze the
   conservative seven-lane C2 wire at 34,658 bytes before considering any new
   masking construction.
3. **Digest-free sealed-proof dispatch.** Replace the generic proof-body-digest
   ASVQ path for this profile by exact finalized account identity/length and
   immediate selected-program return authentication. Keep registry policy,
   program/profile/release and statement binding.
4. **Compact verifier result.** Return only the canonical verified pair-tree
   afterstate rather than echoing the sealed request. The Pool already retains
   the statement, selected program, proof account, profile and release across
   the immediate read-only CPI. The runtime identifies the return-data writer,
   and the source bridge must prove that the selected handler emits the result
   only after accepting that exact CPI instruction and proof account. The raw
   afterstate is 680 bytes and an eight-byte version/status envelope makes the
   exact candidate 688 bytes:

   ```text
     8  magic/version/kind/success/reserved
     8  next pair index
    32  next pair-tree root
   640  next frontier (20 * 32 bytes)
   ---
   688 bytes
   ```

   This is a size screen, not yet a frozen wire. Omitting identity echoes is
   sound only with the immediate-CPI/sealed-plan source theorem just stated. It
   removes no statement/profile binding from the request or proof.
5. **Byte-only atomic suffix.** Add one Pool instruction which consumes that
   result and the sealed marker preflight, checks it against the locked old
   state, performs optional withdrawal custody, writes the exact state fields
   and one chronological root slot/header, writes the marker, and emits a
   versioned pair-tree `ASTR`. It performs no Pool Poseidon and has no ASPS,
   ASRS or ASRA account.
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
with one verified pair-afterstate write authorized by an opaque verifier-result
token whose constructor is private to the immediate CPI-return parser. Existing account uniqueness, signer/owner,
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
| finalized proof | read-only | 40-byte header + staged pair body, at most 34,658 bytes |
| System Program | read-only, executable | native |

Withdrawal adds the mint, vault, destination, vault authority and original SPL
Token program. The 10,000-byte ASPS, 8,504-byte ASRS and 720-byte ASRA are not
terminal accounts in this design.

Exact transaction serialization still requires a v0 message and a frozen ALT
for the worst withdrawal/rollover shape. This audit does not claim a measured
1,232-byte wire for the new account set.

## CU gate

The present 1,258,013-CU V7 result leaves 141,987 CU, but it is the old
49-block relation and old atomic state, not the staged pair profile. The exact
production-function probe measured the runtime alternative at 469,798 CU for
twenty parents and 493,270 CU for twenty-one, with a 407-CU zero-parent
baseline. Thus the twenty upper parents alone exceed the frozen verifier's
headroom by 327,404 CU before any Pool suffix; the runtime-append route is
rejected under the present Poseidon implementation.

The staged proof-carried candidate is not a 30,504-byte proof. The exact Lean
wire theorem `exact_staged_wire_cost_if_four_late_lanes_authenticated` gives
34,658 bytes: 4,154 bytes more, five additional upload chunks, and 64 additional
C2 leaf SHA-256 message blocks across q16. It also makes completed proofs stale
after a competing append. It is nevertheless now the only conservative
one-terminal candidate which has not been experimentally ruled out.

The current Pool semantic terminal must be prefactorized before the staged
profile can plausibly pass. Its source evaluator scans the 49 Poseidon blocks
and 16 lanes repeatedly and evaluates copy endpoints individually, whereas the
frozen atomic terminal already demonstrates selector-mask and routing
factorizations for the same multilinear-evaluation pattern. This is an exact
algebraic optimization target: every factorized evaluator must be proved equal
to the unfactored compiled reference and must preserve the tuple registry,
masking rank, degree and transcript. Removing constraints is not an option.

The execution-time alternative is now ruled out by a literal SBF benchmark:
twenty `pool_v1_tree_parent` calls cost 469,798 CU and twenty-one cost 493,270
CU.  The production route is consequently the conservative seven-C2-lane,
34,658-byte proof-carried append.  Its verifier returns only the 680-byte
`(next index, next root, next frontier)` payload in an exact 688-byte typed
envelope; the Pool performs no Poseidon append work.

The production engineering gate should be split without repeated regression
runs:

1. prefactorize and measure the current native Pool terminal against the same
   preserved 30,192-byte proof, proving exact equality to its compiled reference;
2. measure an honest staged pair verifier and separately gate the accepted
   maximum-frontier/34,658-byte case, with the exact 688-byte result;
3. measure the byte-only Pool suffix with a verifier transport double;
4. perform one combined private-transfer same-page run;
5. perform one combined private-transfer rollover run; and
6. perform one combined withdrawal run with real SPL Token CPI.

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

1. literal Rust tuple/residual registry and terminal equal the staged pair Lean
   model;
2. prover and verifier bind the exact historical spend, occupied output-pair
   semantics and 800-byte late live-append snapshot;
3. accepted Tag-73 pair proof authorizes exactly the 680-byte pair afterstate
   consumed by the terminal write;
4. pair-tree Pool bytes decode under the inductive state invariant and the
   verified afterstate produces the exact next bytes without a second append;
5. compact return bytes decode to exactly the accepted verifier result;
6. finalized proof-account identity/immutability replaces the removed body
   digest without weakening binding;
7. literal Pool success composes registry selection, verifier result, verified
   pair-afterstate write, chronological history write, marker single-use and optional
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
