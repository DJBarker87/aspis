# V7 byte-for-CU Pareto audit

Date: 2026-08-27

Status: active measurement audit. No production profile, deployed program,
proof-system security parameter, or network state has been changed.

## Decision status

**NO DECISION — NEED REAL COMBINED CU FIRST**

This is an interim status, not the final recommendation. At the frozen base
there is no executable honest `ASQ8 -> Tag-73 -> ASR8` eight-lane verifier
path. Consequently no current result is a real combined one-terminal CU
measurement, and independent component totals are not reported as if they
were one execution. The corrected eight-lane masking-rank gate and the actual
ASQ8 cryptographic handler must both close before the production decision.

## 1. Frozen baseline

The audit starts from clean `origin/main`:

```text
041780f4ef0be98c5b1675df87917046b62b4c2f
proof: bridge ASQ8 pool caller source flow
```

The relevant path revisions present in that tree are:

| Boundary | Path | Last path-changing revision |
| --- | --- | --- |
| Tag-73 arithmetic verifier | `programs/aspis-verifier/src/v7_verifier.rs` | `28a19d17ea82f02b76d5e7d21e28d2423425e16d` |
| Frozen V7 atomic wrapper | `programs/aspis-verifier/src/v7_transaction.rs` | `1589706d38a5e8ca705fbf7aaed2c82cf8595510` |
| Native Pool Tag-73 dispatch | `programs/aspis-verifier/src/v7_pool_native_dispatch.rs` | `9fde8009514f3e80962105139b2b14257b8fc85d` |
| Eight-lane ASQ8 verifier boundary | `programs/aspis-verifier/src/v7_pair_forest_dispatch.rs` | `5ef4aaedde3a2904734329156dea3171fc41ba5a` |
| Eight-lane Pool caller | `programs/aspis-pool/src/pair_forest_dispatch.rs` | `041780f4ef0be98c5b1675df87917046b62b4c2f` |
| TxV1 wallet builder | `crates/aspis-pool-wallet-v1/src/lane_forest_transaction_v1.rs` | `7d419af297c2ccf05191799b9884a4b7b7d5da3b` |
| ASQ8/ASF8/ASR8 codecs | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs` | `cd07213d3b0c1fa19f097d7d862f4408f9ce7aa5` |
| Selected forest trace/layout | `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs` | `0eb2f79128a2896cc3a8e9e8130c619e4d335a83` |
| Semantic terminal prefactorisation | `crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs` | `de2d898e8066de084be54a20b5634ac7abe928c8` |
| ASQ8 Pool caller source bridge | `aeneas-verif/v7-asq8-pool-caller-source-20260827/` | `041780f4ef0be98c5b1675df87917046b62b4c2f` |
| Inactive forest terminal source bridge | `aeneas-verif/v7-forest-terminal-source-20260827/` | `8b2e6f8f032496eed2cc00ecabb6276884695be0` |

The base's selected eight-lane masking layout is not activatable: its corrected
rank certificate is still a hard prerequisite. All experimental variants in
this audit remain default-off until that prerequisite is replaced by a passing
frozen certificate.

## 2. Frozen profile and exact sizes

| Item | Exact value | Source of truth |
| --- | ---: | --- |
| Maximum proof body | 30,504 B | `V7_STAGED_PAIR_MAX_BODY_BYTES` |
| C1 / C2 committed widths | 26 / 3 columns | `V7_STAGED_PAIR_C1_COLUMNS`, `V7_STAGED_PAIR_C2_COLUMNS` |
| Logical gamma width / degree | 29 / 28 | `V7_STAGED_PAIR_TOTAL_LOGICAL_GAMMA_COLUMNS`, `V7_STAGED_PAIR_GAMMA_DEGREE` |
| Semantic sumcheck intrinsic degree cap | 27 | selected pair/forest relation profile |
| Semantic trace | 16 columns x 1,024 rows | selected merged-C1 pair/forest profile |
| Fixed proof values | 641 QM31 = 2,564 M31 limbs | `V7_STAGED_PAIR_FIXED_QM31_VALUES` |
| Query count | 16 | `V6_QUERY_COUNT` / frozen Tag-73 profile |
| Query candidate cap | 64 | `V7_COMPACT_QUERY_CANDIDATES` |
| Frontier cap | 203 nodes per tree | `V7_COMPACT_FRONTIER_CAP_PER_TREE` |
| Merkle profile | two typed trees, 26-byte / 208-bit nodes | selected Tag-73 profile |
| Private query salt | 32 B | `V7_COMPACT_PRIVATE_SALT_BYTES` |
| Work stages | 35 / 31 / 34 bits | selected Tag-73 profile |
| ASQ8 | 320 B | `POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES` |
| ASF8 | 1,880 B | `POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES` |
| ASR8 | 792 B | `POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES` |

The proof body remains account-backed. None of the transaction-size figures
below carries the 30,504-byte body in instruction data.

### Exact serialized TxV1 sizes

These are complete serialized TxV1 messages, including placeholder signatures,
TxV1 config, inline keys, account metas, and instruction framing.

| Operation | Compact ASQ8 | Full ASF8 experiment | Delta | ASF8 headroom to 4,096 |
| --- | ---: | ---: | ---: | ---: |
| Private transfer, same page | 811 B | 2,371 B | +1,560 B | 1,725 B |
| Private transfer, rollover | 844 B | 2,404 B | +1,560 B | 1,692 B |
| Withdrawal, same page | 976 B | 2,536 B | +1,560 B | 1,560 B |
| Withdrawal, rollover | 1,009 B | 2,569 B | +1,560 B | 1,527 B |
| Init | 904 B | unaffected | 0 | 3,192 B |
| Checkpoint | 662 B | unaffected | 0 | 3,434 B |
| Largest 512-byte rollover deposit | 1,277 B | unaffected | 0 | 2,819 B |

The exact ASF8 delta is therefore +1,560 bytes in every affected transaction,
not an instruction-payload approximation. No tested ASF8 shape crosses the
3,500-byte scrutiny threshold.

## 3. Current CU evidence and its limits

Evidence classes used throughout this audit:

- **MEASURED REAL CU**: an executable transaction containing the stated real
  component(s).
- **MEASURED COMPONENT CU**: an executable isolated component or transport
  double, not a complete eight-lane transaction.
- **STATIC/INSTRUMENTED ESTIMATE**: instruction counts, runtime cost formulae,
  host timings, or sums that did not execute as one transaction.

| Evidence | Classification | CU | Scope and limitation |
| --- | --- | ---: | --- |
| Frozen V7 atomic Tag-73 | MEASURED COMPONENT CU | 1,258,013 | Real proof verification and old atomic state wrapper; not ASQ8/eight-lane Pool. |
| Optimised native Pool-relation Tag-73 | MEASURED COMPONENT CU | 1,255,491 | Real 30,192-byte single-leaf proof after terminal prefactorisation and fixed-width decoding; not the final forest relation. |
| Optimised native query openings | MEASURED COMPONENT CU | 242,966 | 136,824 decode/gamma, 11,024 private-leaf hashes, 94,845 paired Merkle walk, 273 checkpoints. |
| Byte-only Pool same-page terminal | MEASURED COMPONENT CU | 81,922 | Authenticated verifier transport double plus Pool writes; no cryptographic verifier. |
| Byte-only Pool rollover baseline | MEASURED COMPONENT CU | 119,206 | Earlier isolated rollover plumbing; no cryptographic verifier. |
| Instrumented ASQ8/ASF8/ASR8 + byte-only forest transfer | MEASURED COMPONENT CU | 635,345 | Matched-marker baseline: real Pool-to-verifier CPI, account/PDA/registry checks, canonical proof-wire scan, ASF8 reconstruction, 792-byte ASR8 return and atomic byte writes; no Tag-73 equations and no Pool Poseidon. The 827-byte harness transaction is not the wallet TxV1 shape. The earlier return sweep used the same path without three decomposition markers and measured 634,663 CU. |
| Complete ASQ8 + Tag-73 + Pool transaction | unavailable | unavailable | No active ASQ8 cryptographic handler exists at the frozen base. |

The 1,255,491 and 81,922 results must not be added and presented as exact
combined CU. Their independent sum is only a budgeting screen and may double
count wrappers while omitting forest-specific work.

## 4. Instrumented one-terminal CU breakdown

This table is populated only with executable checkpoints. Forest-specific
transport instrumentation is default-off and cannot be called cryptographic
acceptance until the real ASQ8 handler exists.

| Category | Current evidence | Classification | Variant deltas |
| --- | ---: | --- | ---: |
| ASQ8 parse | included before first marker | MEASURED COMPONENT CU | no material byte-for-CU candidate identified |
| account/registry authentication | registry 7,598; master 7,123; checkpoint 2,154; lane 5,803 | MEASURED COMPONENT CU | pending |
| ASF8 reconstruction | 3,011 | MEASURED COMPONENT CU | pending |
| canonical codecs/copies/comparisons | exact wire phase 515,274; 4,996-limb canonical scan alone 515,000 | MEASURED COMPONENT CU | direct typed snapshot saves 2,191 CU transaction-wide; deferred canonicality saves 515,003 CU but is measurement-only until the real crypto path canonically consumes every limb exactly once |
| transcript absorption | pending | — | pending |
| SHA/Merkle authentication | 105,869 CU within query-opening profile | MEASURED COMPONENT CU | pending |
| field decode/gamma arithmetic | 136,824 CU within query-opening profile | MEASURED COMPONENT CU | pending |
| terminal/prefactorised semantic checks | pending exact current split | MEASURED COMPONENT CU | pending |
| ASR8 construction/validation | encode 2,487; set-return phase 360; Pool get/decode 3,512; validate/apply-byte prep 4,663 | MEASURED COMPONENT CU | 792--1,024 B sweep complete; every expansion costs CU and deletes no safe work |
| selected-lane/history/nullifier writes | final persistence marker delta 517; earlier planning is included in preflight/custody-plan | MEASURED COMPONENT CU | full split pending |
| withdrawal SPL CPI/rollback | pending | — | pending |
| wrapper/account overhead | pending | — | pending |

The 635,345-CU matched-marker profile uses the deliberately small but valid 14-node-per-tree
fixture: 20,676 proof bytes, 21,364 upload-payload bytes and a 21,404-byte proof
account. The selected grammar maximum remains 30,504 bytes. Matched probes pin
the exact 4,996-limb packed-M31 canonical scan at 515,000 CU: 2,564 fixed
limbs plus 2,432 query limbs. The deferred parser still enforces exact body,
section, frontier-cap, frontier-length and packed-padding rules, but it
deliberately accepts a limb equal to the field modulus and therefore cannot
authorize acceptance by itself. The sound integration rule is to parse the
layout once, then let the real transcript/query verifier canonically decode
and consume every limb exactly once. A separate direct-typed-snapshot probe
reduces the account-derived 800-byte snapshot phase from 3,188 to 979 CU,
saving 2,191 CU transaction-wide while retaining the full canonical wire
scan. Its source bridge must preserve that the typed value came from the exact
PDA, owner and canonical account decoders.

## 5. Candidate inventory

Every candidate remains experimental/default-off. A supplied value is never
trusted; it must be checked against authenticated accounts or by an exact
algebraic/cryptographic equality which is cheaper than recomputation.

| Candidate | Extra Tx bytes | Extra proof/account bytes | Candidate CU saving | Evidence now | Security/formal/source cost | Status |
| --- | ---: | ---: | ---: | --- | --- | --- |
| Supply full ASF8 and compare it with authenticated reconstruction | +1,560 | 0 | host-negative; real CU unmeasured | exact TxV1 sizes plus default-off authenticated profile `337d6eba` | Must retain master, checkpoint, selected-lane, deployment, profile/release and afterstate checks | unlikely to win; retain only for combined confirmation |
| Finalization-computed sealed proof-body SHA in the existing 32-byte authority slot | 0 | 0 | none on current ASQ8: it performs no terminal body-digest pass | default-off `ASD1` implementation at `609e18fc`; old native dispatch measured 15,597 CU | Exact lifecycle/source invariant, cache/request binding and close-path activation proof | exclude unless final ASQ8 introduces an authenticated body-digest claim |
| Checked aggregate M31 inverse hint | 0 or +4 | +4 or 0 | one inversion minus equality check; unmeasured | static arithmetic inventory | Prove nonzero/input binding and exact multiplication check | benchmark if SBF delta is material |
| Two checked QM31 circle-map inverses | 0 or +32 | +32 or 0 | two inversions minus equality checks; unmeasured | static arithmetic inventory | Same relation, new canonical hint framing/source bridge | benchmark |
| Canonical final-vector representation | 0 | +128 | isolated SBF **+5,802 CU** | default-off Variant B at `f4756ede`; evidence `9d4fb5e8` | Encoding/canonicality bridge, no changed claims | reject |
| Canonical fixed-prefix representation | 0 | +192 | isolated SBF **-35,620 CU** | default-off Variant A at `f4756ede`; evidence `9d4fb5e8` | Encoding/canonicality bridge, no changed claims | retain only as fallback |
| Canonical complete 641-QM31 fixed section | 0 | +320 | isolated SBF **-117,790 CU** | default-off Variant C at `f4756ede`; evidence `9d4fb5e8` | Fresh profile/release, transcript-reader equivalence and source bridge; no changed claims | leading proof-byte candidate |
| Expand ASR8 within the 1,024-byte return-data cap | 0 | 0 | none; measured gross cost is +38 to +58 CU | five distinct LiteSVM component executions | Every added field must be verifier-derived and immediately bound to the selected program/profile/release/statement/accounts | reject: keep 792 B |
| Remove live-snapshot encode/decode round trip | 0 | 0 | **-2,191 CU** in matched component transaction | default-off direct-typed probe at `f8804061` | Source bridge from exact canonical master/lane PDA+owner decoders to the unchanged snapshot predicate | retain for production integration |
| Defer standalone 4,996-limb canonical scan and consume canonically inside real crypto | 0 | 0 | potential **-515,003 CU of duplicate work**; not a standalone saving claim | default-off measurement probe at `f8804061` | Must prove every fixed/query limb is canonically decoded exactly once before acceptance; no field may escape the crypto consumer | mandatory integration discipline, not an independently activatable variant |

Hints for residuals, gamma dot products, SHA midstates, Merkle parents, query
counters, or transcript challenges are rejected unless the existing verifier
fully recomputes them or a new cryptographic relation is first proved. No such
candidate receives a CU credit in this audit.

The zero-byte digest-cache experiment preserves the exact 40-byte proof
header: `ASD1`, the existing little-endian body length, the raw SHA-256 body
digest in the former finalized-authority bytes, then the unchanged body. It is
feature-gated and inactive. Finalization authenticates the uploader state and
writes the version magic last; every existing mutator rejects the sealed
image. The hot validator checks owner, read-only/non-signer/non-executable
shape, exact framing, expected length and expected digest without rehashing.
Its focused host tests and minimal feature compile pass. The older native Pool
dispatch measured a 15,597-CU proof-body SHA interval, but compact ASQ8 carries
and compares no proof-body digest and its current source performs no equivalent
hash. The cache therefore earns zero CU credit here. It remains lifecycle
research only if final ASQ8 later introduces an independently authenticated
body-digest claim; the release must not add such a hash merely to create work
for the cache to remove.

The proof-account sweep is not restricted to the old 30-KiB grammar boundary.
The exact requested size points, before any candidate-specific framing, are:

| Proof-account body experiment | Maximum body | Delta from 30,504 B |
| --- | ---: | ---: |
| Canonical final256 only | 30,632 B | +128 B |
| Canonical pre-final 385 QM31 only | 30,696 B | +192 B |
| Both fixed subsections canonical | 30,824 B | +320 B |
| Generic +0.5 KiB sweep | 31,016 B | +512 B |
| Generic +1 KiB sweep | 31,528 B | +1,024 B |
| Generic +2 KiB sweep | 32,552 B | +2,048 B |
| Generic +4 KiB sweep | 34,600 B | +4,096 B |

Crossing 30 KiB is not itself a rejection. Any larger grammar must have an
exact version/profile binding and earns its rent/upload/formal complexity only
through a repeatable CU reduction.

The isolated codec prototype implements all three exact grammars with
fail-closed length, padding and canonical-field checks, unchanged proof-tail
framing, and equality of both the 641 decoded QM31 sequence and canonical
transcript field image. In a 20,000-iteration release host probe, the selected
packed codec took 5,087 ns per decode; Variant A took 8,267 ns, Variant B
10,348 ns, and fully canonical Variant C 4,050 ns. These are **host codec
timings, not CU**.

The repeated isolated LiteSVM/SBF component transaction measured 174,747 CU
for selected packed, 139,127 for A, 180,549 for B, and 56,957 for C. The
corresponding deltas are -35,620, +5,802 and **-117,790 CU**. The component
includes account borrow, canonical validation, decoding, the same 641 QM31
additions and a return write; it does not execute the real transcript,
relation, Merkle/query verifier or Pool. The values therefore cannot be
mechanically subtracted from a full-verifier number. They establish that C is
the leading candidate for fresh-profile integration and real combined
measurement; B is dominated and rejected.

### Matched parser and snapshot decomposition

Three stack-clean SBF artifacts execute the same Pool-to-verifier component
transaction with matched subphase markers:

| Probe | Total CU | Snapshot phase | Candidate decode | Wire phase | Tail |
| --- | ---: | ---: | ---: | ---: | ---: |
| Exact canonical baseline | 635,345 | 3,188 | 1,834 | 515,274 | 299 |
| Deferred wire canonicality | 120,342 | 3,185 | 1,834 | 274 | 299 |
| Direct typed snapshot | 633,154 | 979 | 1,834 | 515,274 | 317 |

The exact-minus-deferred wire delta is 515,000 CU inside the matched phase and
515,003 CU transaction-wide. This measures the complete 4,996-limb canonical
scan; it does not make deferred parsing safe. The deferred parser deliberately
accepts a field-modulus limb in its adversarial test, so acceptance requires
the real cryptographic consumer to canonically decode all fixed and query
limbs exactly once. The snapshot optimization is independently safe in shape:
it retains full canonical proof parsing and the unchanged semantic snapshot
predicate, and saves 2,191 CU transaction-wide. It still needs the source
bridge proving provenance from the canonical authenticated Pool accounts.

## 6. Experimental variants

| Variant | Transport | Proof/account representation | State |
| --- | --- | --- | --- |
| 0 — current | compact ASQ8 | current sealed proof | pending real combined path |
| 1 — fat semantic request | full ASF8, equality-checked against authenticated state | unchanged | Tx size and host component measured; real CU pending |
| 2 — best safe Tx hints | selected only after isolated measurements | unchanged | pending |
| 3 — best safe proof hints | ASQ8 | selected only after isolated measurements | pending |
| 4 — combined best | independently winning Tx and proof candidates | independently winning candidates | pending |
| 5 — ASR8 return sweep | compact ASQ8 | unchanged | measured and rejected: extra bytes add CU and delete no safe work |

## 7. Pareto frontier

No candidate enters the production Pareto frontier until its real combined CU
is measured against Variant 0 in the same executable path.

| Variant | Tx bytes | Proof max | Transfer CU | Withdrawal CU | Delta CU | Delta bytes | Security/formal cost |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 0 — compact ASQ8 | 811 / 844 | 30,504 | pending | pending | baseline | 0 | existing boundaries |
| 1 — full ASF8 | 2,371 / 2,404 | 30,504 | pending | pending | pending | +1,560 Tx | authenticated equality/source bridge |
| 2 — safe Tx hints | pending | 30,504 | pending | pending | pending | pending | pending |
| 3 — safe proof hints | 811 / 844 | pending | pending | pending | pending | pending | pending |
| 4 — combined | pending | pending | pending | pending | pending | pending | pending |

Withdrawal TxV1 values are 976/1,009 bytes for Variant 0 and 2,536/2,569
bytes for Variant 1. They will receive their own CU rows once executable.

### Isolated proof-codec frontier (not combined CU)

| Fixed-field codec | Maximum proof | Isolated component CU | Delta CU | Delta proof bytes | CU saved / 100 B | Current disposition |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| selected packed | 30,504 | 174,747 | 0 | 0 | — | baseline |
| A: canonical pre-final | 30,696 | 139,127 | -35,620 | +192 | 18,552 | fallback; only 24 B below 30 KiB |
| B: canonical final256 | 30,632 | 180,549 | +5,802 | +128 | -4,533 | rejected |
| C: fully canonical | 30,824 | 56,957 | **-117,790** | +320 | **36,809** | leading integration candidate |

These transactions isolate the exact fixed-section decoder and a common
algebraic checksum. They prove a real SBF byte/compute trade, but not its net
effect inside Tag-73. Variant C needs a fresh profile/release binding and
exact transcript-reader/source equivalence before it can enter the combined
Pareto table.

### Full-ASF8 host component evidence

The default-off full-ASF8 profile independently authenticates the proof,
master, checkpoint and selected-lane accounts; rederives their PDAs; derives
the Pool program from account ownership; uses compiled profile/release
bindings; compares the complete account-derived live snapshot and candidate
afterstate; and then fail-closes without ASR8 or dispatch. On a 30,504-byte
proof, 256 release-host iterations measured 31,738 ns for full ASF8 versus
31,260 ns for compact ASQ8. Parsing ASF8 was 483 ns and the exact statement
comparison 43 ns. These are **host timings, not CU**. The dedicated streaming
SBF profile compiles without an oversized called frame, but has not executed
in LiteSVM. Combined with the measured 3,011-CU ASF8 reconstruction cost, the
current evidence gives no positive reason to spend 1,560 TxV1 bytes; Variant 1
remains outside the Pareto frontier unless a same-binary combined run reverses
that result.

### ASR8 return-data sweep

ASR8 is currently 792 bytes, leaving exactly 232 bytes below the 1,024-byte
Solana return-data limit. Return bytes are not transaction bytes, so this is a
separate Pareto axis. The required sweep points are:

| ASR8 bytes | Added bytes | Static syscall total | Measured component CU | Delta CU | Safe Pool work deleted |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 792 | 0 | 206 | 634,663 | 0 | 0 |
| 824 | 32 | 206 | 634,701 | +38 | 0 |
| 856 | 64 | 206 | 634,708 | +45 | 0 |
| 920 | 128 | 206 | 634,718 | +55 | 0 |
| 1,024 | 232 | 208 | 634,721 | +58 | 0 |

The five measurements include runtime return-data copy, Pool tail checking,
decoding and canonical validation. The final Pool result is still the canonical
792-byte ASR8. The synthetic verifier extension repeats a deterministic prefix
of that accepted result solely to measure transport cost. Source inspection
found no safe additional verifier-derived field that deletes Pool work: the
current ASR8 already carries the full 688-byte afterstate and every material
settlement binding. The exact verifier-return / Pool-copy-and-decode / post-CPI
marker deltas were 360/3,512/314 CU at 792 bytes and 390/3,540/314 CU at 1,024
bytes. `asr8-validated` remained 4,663 CU at every point.

Agave 4.2.1's syscall schedule predicted the observed direction:
`set_return_data` charges `100 + floor(len/250)` CU and `get_return_data`
charges `100 + floor((copied_len+32)/250)` CU. Thus the explicit syscall
schedule rises by only 2 CU between 792 and 1,024 bytes. This is a
**STATIC/INSTRUMENTED ESTIMATE**, while the table above is the executable SBF
result including allocation, copying, parsing and validation. Every expanded
point is strictly dominated by 792 bytes.

The requested upper endpoint is **1,024 bytes**, not 1,024 KiB: Solana return
data is capped at 1,024 bytes. Return-data size does not enlarge the serialized
TxV1 packet, but it can increase CPI memory/copy and validation work.

## 8. Cryptographic and source constraints

No byte-for-CU experiment may alter transcript ordering or causality, C1
commitment timing, two-tree Merkle authentication, 208-bit nodes, q16,
grinding, canonical field decoding, retained historical anchors, the exact
selected live lane, nullifier freshness, registry/release/program binding,
custody conservation, withdrawal destination binding, replay rejection,
rollback, or exact ASF8/ASR8 equality.

An optimisation that changes the proved relation is not a byte-for-CU variant.
It is excluded from this audit until the affected Lean security theorem and
the accepted-source bridge are identified and reproved.

The corrected nonredundant forest path layout now has a focused structural
Lean theorem: booleanity plus
`(1-b)(left-current)=0` and `b(right-current)=0` force the selected child to be
the running digest, with the unselected child serving as the ordinary Merkle
sibling. The resulting Poseidon node is therefore exactly one paper `Parent`
step. The focused theorem compiles with axiom set
`[propext, Classical.choice, Quot.sound]` only. This proves relation
equivalence; activation still requires the complete masking-rank certificate
and updated Rust-to-Lean/Aeneas source bridge.

## 9. Rejected candidates

| Candidate | Reason |
| --- | --- |
| Trust caller-supplied ASF8 | It would permit invented state/deployment bindings. Full ASF8 is viable only as an equality-checked representation of authenticated facts. |
| Trust terminal residuals or gamma results | Verifying them requires the original computation or a new proof relation. |
| Trust SHA midstates/Merkle parents | This weakens authentication unless every compression step is checked, eliminating the claimed shortcut. |
| Expand ASR8 above 792 bytes | Five real component executions cost 38--58 additional CU and no candidate deletes safe Pool work. The extra return capacity is cheap but useless for this result schema. |
| Change PCS width, query count, digest width, or grinding | Changes the cryptographic profile and soundness proof; outside this audit. |
| Present independent CU sums as a combined result | They did not execute as one transaction and may double count or omit work. |

## 10. Measurement and replay commands

### Freeze baseline

```bash
git fetch origin
git rev-parse origin/main
git status --short
```

### Exact TxV1 ASQ8/ASF8 sizes

```bash
CARGO_BUILD_JOBS=2 cargo test --locked \
  --features eight-lane-plumbing-v2 \
  lane_forest_transaction_v1::tests --quiet
```

### Corrected masking preflight

```bash
cargo test -q -p aspis-statement \
  pool_v1::pair_forest_hiding::tests:: -- --nocapture
cargo test -q -p aspis-statement \
  pair_forest_constraint_residuals -- --nocapture
```

### Matched parser/snapshot SBF component probes

The checked-in artifacts and phase ledgers are under
`results/v7-pair-forest-byte-cu-20260827/artifacts/components/` and
`evidence-{component-baseline,wire-deferred,snapshot-direct}.json`. They were
built in:

```text
systemd unit: aspis-v7-byte-cu-components-04.service
invocation:   bd27d7c866d242daab2237b3cc220ce8
MemoryHigh:   6G
MemoryMax:    8G
swap:         0
jobs:         1
peak RSS:     245,404 KiB
```

The exact source/evidence commit is
`f880406169e9145aca4ff929864a5e8abf157c64`.

The exact SBF/LiteSVM/Agave replay commands and artifact hashes will be added
with the real combined measurements. Solana CLI use must set `NO_DNA=1`; no
network signing or submission is part of this audit.

## 11. Release decision rule

Keep the 30,504-byte proof frozen unless a fatter account-backed representation
produces a material, repeatable combined-CU reduction after its verification,
upload, rent, wallet, formal, and source-bridge costs are included. Keep ASQ8
unless full ASF8 or checked Tx-carried hints produce a material same-binary CU
reduction while every affected TxV1 shape remains comfortably below 4,096
bytes.

The final report will replace the interim decision at the top with exactly one
of the required production choices after the real combined frontier exists.
