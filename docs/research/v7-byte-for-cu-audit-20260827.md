# V7 byte-for-CU Pareto audit

Date: 2026-08-28

Status: active measurement audit. No production profile, deployed program,
proof-system security parameter, or network state has been changed.

## Decision status

**SPEND PROOF BYTES FOR CU**

The measured selected frontier keeps compact 320-byte ASQ8, spends exactly
320 proof-account bytes on the canonical fixed section, keeps ASR8 at 792
bytes, and composes the separately gated state/source optimisations. The real
strict-work true-TxV1 transfer succeeds atomically at **1,376,652 CU**, with
**23,348 CU headroom** under the 1.4M limit. Its exact sizes are 799 transaction
bytes, 30,720 honest proof bytes and 792 return-data bytes. The selected
verifier CPI consumes 1,286,678 CU.

This is a Pareto decision, not production activation. The selected route is
still default-off and requires generated production Pool/registry/release
identities, fresh initialized lane PDAs, reproducible selected binaries,
integrated source/formal evidence, and the remaining withdrawal-CU and
adversarial lifecycle gates. Transfer rollover already accepts at 1,385,365 CU,
but withdrawals still exceed 1.4M (1,593,988 same-page and 1,487,132 rollover
under diagnostic limits), so this selected configuration is not yet a complete
Pool release. Full ASF8 is measured and strictly dominated:
it adds 1,560 transaction bytes and 12,901 CU. Expanding ASR8 adds 38--58 CU
and deletes no safe work.

## 1. Frozen baseline

The positive-path integration base is:

```text
e4c317fe4fa420c8d2aab613d400abc3607b45db
test: freeze strict-work forest dispatch KAT
```

The selected default-off measurement stack additionally contains the
authenticated fresh-PDA lane invariant, immutable six-account verifier release
gate, +320-byte canonical fixed section, packed digest selector, direct
canonical ASR8 reuse, binary Copy weights and exact-tag endpoint selector
cache. The source experiments are pinned at `e86d48cc`, `efc928fc`,
`d14ea1b1`, `6045276e` and `b6760f7d`; the focused source/Aeneas bridge ports
are recorded separately and do not change the measured binaries.

The relevant path revisions present in that tree are:

| Boundary | Path | Last path-changing revision |
| --- | --- | --- |
| Tag-73 arithmetic verifier | `programs/aspis-verifier/src/v7_verifier.rs` | `b996eeff84bc3202316e5ae64bc06c0522a876da` |
| Frozen V7 atomic wrapper | `programs/aspis-verifier/src/v7_transaction.rs` | `1589706d38a5e8ca705fbf7aaed2c82cf8595510` |
| Native Pool Tag-73 dispatch | `programs/aspis-verifier/src/v7_pool_native_dispatch.rs` | `9fde8009514f3e80962105139b2b14257b8fc85d` |
| Eight-lane ASQ8 verifier boundary | `programs/aspis-verifier/src/v7_pair_forest_dispatch.rs` | `e4c317fe` |
| Strict-work fixture/prover entry | `crates/aspis-prover/src/v7_pair_forest_fixture.rs` | `e4c317fe` |
| Eight-lane Pool terminal | `programs/aspis-pool/src/pair_forest.rs` | `9b8e4e0548c2a03db2bff51848fc7cc9f755f96b` |
| Eight-lane selected-verifier caller | `programs/aspis-pool/src/pair_forest_dispatch.rs` | `5cda8649cff34edc7dc2c6c56dba440d27eb70ff` |
| TxV1 wallet builder | `crates/aspis-pool-wallet-v1/src/lane_forest_transaction_v1.rs` | `372bb804a390d1e7e5d9968bdf093d7e26655a87` |
| ASQ8/ASF8/ASR8 codecs | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs` | `b996eeff84bc3202316e5ae64bc06c0522a876da` |
| Semantic terminal prefactorisation | `crates/aspis-statement/src/pool_v1/payment_semantic_terminal.rs` | `de2d898e8066de084be54a20b5634ac7abe928c8` |
| ASQ8 Pool caller source bridge | `aeneas-verif/v7-asq8-pool-caller-source-20260827/` | `041780f4ef0be98c5b1675df87917046b62b4c2f` |
| Inactive forest terminal source bridge | `aeneas-verif/v7-forest-terminal-source-20260827/` | `8b2e6f8f032496eed2cc00ecabb6276884695be0` |

The corrected complete-view masking-rank prerequisite passed on the NUC:
sumcheck rank `1080/1084`, joint PCS rank `4092/4360`, ambient deficit 268,
and physical/legal/helper witness containment all `Some(true)`. This removes
the prior mathematical activation blocker. Experimental byte/CU variants
remain default-off because they still need same-binary combined measurements
and, if selected, fresh release/source/formal closure.

## 2. Frozen profile and exact sizes

| Item | Exact value | Source of truth |
| --- | ---: | --- |
| Maximum proof body | 30,504 B | `V7_STAGED_PAIR_MAX_BODY_BYTES` |
| Honest strict-work KAT proof body | 30,400 B | frozen dispatcher KAT at `e4c317fe` |
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
- **HOST TIMING (NOT CU)**: native wall-clock measurement used only to compare
  codec/control-flow shapes; it cannot be converted into Solana CU.
- **STATIC/INSTRUMENTED ESTIMATE**: instruction counts, runtime cost formulae,
  or sums that did not execute as one transaction.

| Evidence | Classification | CU | Scope and limitation |
| --- | --- | ---: | --- |
| Frozen V7 atomic Tag-73 | MEASURED COMPONENT CU | 1,258,013 | Real proof verification and old atomic state wrapper; not ASQ8/eight-lane Pool. |
| Optimised native Pool-relation Tag-73 | MEASURED COMPONENT CU | 1,255,491 | Real 30,192-byte single-leaf proof after terminal prefactorisation and fixed-width decoding; not the final forest relation. |
| Optimised native query openings | MEASURED COMPONENT CU | 242,966 | 136,824 decode/gamma, 11,024 private-leaf hashes, 94,845 paired Merkle walk, 273 checkpoints. |
| Byte-only Pool same-page terminal | MEASURED COMPONENT CU | 81,922 | Authenticated verifier transport double plus Pool writes; no cryptographic verifier. |
| Byte-only Pool rollover baseline | MEASURED COMPONENT CU | 119,206 | Earlier isolated rollover plumbing; no cryptographic verifier. |
| Instrumented ASQ8/ASF8/ASR8 + byte-only forest transfer | MEASURED COMPONENT CU | 635,345 | Matched-marker baseline: real Pool-to-verifier CPI, account/PDA/registry checks, canonical proof-wire scan, ASF8 reconstruction, 792-byte ASR8 return and atomic byte writes; no Tag-73 equations and no Pool Poseidon. The 827-byte harness transaction is not the wallet TxV1 shape. The earlier return sweep used the same path without three decomposition markers and measured 634,663 CU. |
| Historical full-ASF8 authenticated component | HOST TIMING (NOT CU) | not applicable | On a 30,504-byte wire, 256 native release iterations measured 31,738 ns full ASF8 versus 31,260 ns compact ASQ8. That historical profile had no dispatcher arm and emitted no ASR8; the later real combined ASF8 row is classified separately. |
| Honest ASQ8 -> Tag-73 -> ASR8 strict-work host KAT | HOST ACCEPTANCE (NOT CU) | not applicable | Exact 30,400-byte proof, 201 frontier nodes, exact 35/31/34-bit work, complete semantic terminal/relation/openings and exact 792-byte ASR8 all pass through the production dispatcher. |
| Empty-lane combined Pool -> selected verifier entry | MEASURED REAL CU (incomplete) | 82,493 CU before CPI; 1,317,507 remaining | Real combined SBF transaction and account path. It establishes entry budget, not acceptance or total successful CU. |
| Populated 13-pair honest lane combined attempt | MEASURED REAL CU (failed/rollback) | 554,530 CU before CPI; exactly 1,400,000 exhausted | Real 30,140-byte honest unmined proof under strict production `check_work=true`; selected verifier entered with 845,470 CU, no result returned, exact rollback. Logs do not identify a later verifier phase. |
| Populated 13-pair zero/min-frontier control | MEASURED REAL CU (failed/rollback) | 554,492 CU before CPI; exactly 1,400,000 exhausted | Selected verifier entered with 845,508 CU and exhausted. This pins the populated prefix independently of proof length/content; it is not cryptographic acceptance. |
| Strict compact ASQ8 with Pool source+result invariant | MEASURED REAL CU | 2,069,373 total; 1,970,586 verifier CPI | True TxV1, exact settlement, 799-byte transaction, 30,400-byte honest proof and 792-byte ASR8. This is the fair compact baseline after removing duplicate Pool root provenance work. |
| Strict full ASF8 with the same invariants | MEASURED REAL CU | 2,082,274 total; 1,975,765 verifier CPI | 2,359-byte true TxV1; same proof/result and settlement. Delta versus compact is **+12,901 CU and +1,560 Tx bytes**, so full ASF8 is dominated. |
| Strict compact ASQ8 + canonical fixed section (Variant C) | MEASURED REAL CU | 1,912,443 total; 1,813,655 verifier CPI | Exact 30,720-byte proof (+320), 799-byte true TxV1, exact 792-byte result and settlement; saves 156,930 CU versus its fair 2,069,373-CU compact baseline. |
| Variant C + hardened six-account verifier lane invariant | MEASURED REAL CU | 1,452,893 total; 1,353,473 verifier CPI | Independently authenticates immutable registry root, Pool/verifier/profile/release/version and active slot. Audit fixture identities are not production identities. |
| Variant C + hardened lane invariant + direct ASR8 + binary Copy weights | MEASURED REAL CU | 1,386,744 total; 1,296,770 verifier CPI | First strict true-TxV1 atomic success below 1.4M; exact lane/history/nullifier settlement. |
| Selected stack + exact-tag endpoint selector cache | MEASURED REAL CU | **1,376,652 total; 1,286,678 verifier CPI** | Current best real Pareto point: 799-byte true TxV1, 30,720-byte proof, 792-byte ASR8, 23,348 CU headroom and exact atomic settlement. |
| Selected stack, transfer rollover | MEASURED REAL CU | **1,385,365 total; 1,266,387 verifier CPI** | Accepted at the real 1.4M limit, 832-byte true TxV1, 14,635 CU headroom and exact rollover settlement. |
| Selected stack, withdrawal same-page | MEASURED REAL CU (over-limit diagnostic plus 1.4M rollback) | 1,593,988 total at 1.6M; exactly 1,400,000 rejected at deployable limit | 964-byte true TxV1; diagnostic success includes exact SPL CPI and settlement but is not deployability evidence. |
| Selected stack, withdrawal rollover | MEASURED REAL CU (over-limit diagnostic plus 1.4M rollback) | 1,487,132 total at 1.65M; exactly 1,400,000 rejected at deployable limit | 997-byte true TxV1; diagnostic success includes exact SPL CPI and rollover settlement but is not deployability evidence. |

The 1,255,491 and 81,922 component results must not be added and presented as
exact combined CU. The later rows are actual complete transactions and replace
that old inference. The populated-lane blocker was duplicate 20-Poseidon
provenance reconstruction, not missing transaction bytes. Its source/result
invariant removal saved 939,227 CU in the matched strict run. Variant C then
bought another 156,930 CU for 320 account-backed proof bytes; full ASF8 bought
nothing and is rejected.

## 4. Instrumented one-terminal CU breakdown

This table is populated only with executable checkpoints. Forest-specific
transport instrumentation is default-off and cannot be called cryptographic
acceptance until the real ASQ8 handler exists.

| Category | Current evidence | Classification | Variant deltas |
| --- | ---: | --- | ---: |
| ASQ8 parse | included before first marker | MEASURED COMPONENT CU | no material byte-for-CU candidate identified; deprioritized behind populated-lane pre-CPI work |
| account/registry authentication | registry 7,598; master 7,123; checkpoint 2,154; lane 5,803 | MEASURED COMPONENT CU | pending |
| ASF8 reconstruction | 3,011 | MEASURED COMPONENT CU | pending |
| canonical codecs/copies/comparisons | exact wire phase 515,274; 4,996-limb canonical scan alone 515,000 | MEASURED COMPONENT CU | direct typed snapshot saves 2,191 CU transaction-wide; deferred canonicality saves 515,003 CU but is measurement-only until the real crypto path canonically consumes every limb exactly once |
| transcript absorption | pending | — | pending |
| SHA/Merkle authentication | 105,869 CU within query-opening profile | MEASURED COMPONENT CU | pending |
| field decode/gamma arithmetic | 136,824 CU within query-opening profile | MEASURED COMPONENT CU | pending |
| terminal/prefactorised semantic checks | pending exact current split | MEASURED COMPONENT CU | pending |
| ASR8 construction/validation | encode 2,487; set-return phase 360; Pool get/decode 3,512; validate/apply-byte prep 4,663 | MEASURED COMPONENT CU | 792--1,024 B sweep complete; every expansion costs CU and deletes no safe work |
| populated selected-lane pre-CPI validation | legacy strict path 554,530 before verifier entry; selected invariant path reduces complete Pool pre/post-CPI overhead to 89,974 around a 1,286,678-CU verifier CPI | MEASURED REAL CU | duplicate root provenance reconstruction removed under the explicit fresh-PDA/program-writer invariant; all owner/PDA/version/index/canonical inactive-frontier checks retained |
| selected complete verifier CPI | 1,286,678 | MEASURED REAL CU | includes Variant C, authenticated verifier lane invariant, packed digest selector, binary Copy weight specialization and exact-tag endpoint selector cache |
| selected-lane/history/nullifier writes | final persistence marker delta 517; earlier planning is included in preflight/custody-plan | MEASURED COMPONENT CU | full split pending |
| withdrawal SPL CPI/rollback | selected same-page and rollover diagnostic successes execute exact SPL CPI and settlement; both deployable-limit replays reject at exactly 1.4M and roll back | MEASURED REAL CU | total selected withdrawal CU remains 1,593,988 / 1,487,132, so further verifier/withdrawal work is mandatory |
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
| Replace repeated populated-lane root reconstruction with authenticated Pool-owned lane-state provenance | 0 | 0 | **-939,227 CU** for source+result invariant in matched strict real transaction | complete executable TxV1 plus focused exhaustive writer/source/Aeneas bridge | Zero-byte CU optimisation. Fresh initialized release PDAs only; owner/PDA alone is insufficient. Every initializer/deposit/settlement writer preserves the exact active root/frontier invariant and all retained codec/account checks remain fail-closed | **selected prerequisite** |
| Supply a populated-root/frontier certificate in Tx/proof bytes | pending | pending | only viable if checking is cheaper than twenty Poseidon parents | no measurement yet | Untrusted bytes cannot replace account provenance; either verify a cryptographic certificate under an already authenticated commitment or reject | inventory only; do not trust raw hint |
| Supply full ASF8 and compare it with authenticated reconstruction | +1,560 | 0 | **+12,901 CU** (worse) | real strict combined 2,082,274 versus compact 2,069,373 | All master, checkpoint, selected-lane, deployment, profile/release and afterstate checks retained | **reject: strictly dominated** |
| Finalization-computed sealed proof-body SHA in the existing 32-byte authority slot | 0 | 0 | none on current ASQ8: it performs no terminal body-digest pass | default-off `ASD1` implementation at `609e18fc`; old native dispatch measured 15,597 CU | Exact lifecycle/source invariant, cache/request binding and close-path activation proof | exclude unless final ASQ8 introduces an authenticated body-digest claim |
| Checked aggregate M31 inverse hint | 0 or +4 | +4 or 0 | one inversion minus equality check; unmeasured | static arithmetic inventory | Prove nonzero/input binding and exact multiplication check | benchmark if SBF delta is material |
| Two checked QM31 circle-map inverses | 0 or +32 | +32 or 0 | two inversions minus equality checks; unmeasured | static arithmetic inventory | Same relation, new canonical hint framing/source bridge | benchmark |
| Canonical final-vector representation | 0 | +128 | isolated SBF **+5,802 CU** | default-off Variant B at `f4756ede`; evidence `9d4fb5e8` | Encoding/canonicality bridge, no changed claims | reject |
| Canonical fixed-prefix representation | 0 | +192 | isolated SBF **-35,620 CU** | default-off Variant A at `f4756ede`; evidence `9d4fb5e8` | Encoding/canonicality bridge, no changed claims | retain only as fallback |
| Canonical complete 641-QM31 fixed section | 0 | +320 | **-156,930 CU real combined** | 1,912,443 versus fair 2,069,373 compact baseline; isolated decoder also saved 117,790 | Fresh production profile/release and exact transcript-reader/source bridge; no changed claims | **selected proof-byte trade** |
| Expand ASR8 within the 1,024-byte return-data cap | 0 | 0 | none; measured gross cost is +38 to +58 CU | five distinct LiteSVM component executions | Every added field must be verifier-derived and immediately bound to the selected program/profile/release/statement/accounts | reject: keep 792 B |
| Remove live-snapshot encode/decode round trip | 0 | 0 | **-2,191 CU** in matched component transaction | default-off direct-typed probe at `f8804061` | Source bridge from exact canonical master/lane PDA+owner decoders to the unchanged snapshot predicate | retain for production integration |
| Defer standalone 4,996-limb canonical scan and consume canonically inside real crypto | 0 | 0 | potential **-515,003 CU of duplicate work**; not a standalone saving claim | default-off measurement probe at `f8804061` | Must prove every fixed/query limb is canonically decoded exactly once before acceptance; no field may escape the crypto consumer | mandatory integration discipline, not an independently activatable variant |
| Reuse canonical decoded ASR8 bytes after exact selected-program authentication | 0 | 0 | **-9,446 CU** at the selected integration step | real strict combined measurement plus translated exact 4-prerequisite/6-binding gate | Raw return bytes are never trusted; exact 792-byte canonical decode and selected return program precede reuse | selected |
| Packed digest selector + binary Copy weights + endpoint selector cache | 0 | 0 | binary step reaches 1,386,744; cache reaches **1,376,652** (-10,092 further) | real strict combined selected stack; focused source/Aeneas algebra/tag/order bridges | Same residual schedule, all endpoints preserved in order, weights exact {0,1}; cache hits require complete row-tag equality and collisions recompute | selected |

The populated-lane source audit explains why bytes are not automatically the
right answer. The selected lane account already contains root, index and
frontier under a Pool-owned PDA. The expensive current decoder recomputes the
nonempty root from the frontier using all twenty Poseidon parents. A raw
caller-supplied duplicate of those values adds no authentication. The
security-equivalent shortcut is an inductive source theorem over authenticated
account state: initialization writes the unique empty image, deposits write
the exact append result, terminal settlement writes only the selected
verifier's exact ASR8 afterstate, and no other instruction can mutate a lane.
Only after that Rust/Aeneas invariant exists may the runtime decoder skip the
redundant root recomputation while retaining owner, PDA, codec, bounds and
canonical inactive-frontier checks. The current root, frontier, account and
semantic bindings remain unchanged; the shortcut removes only duplicate
twenty-Poseidon provenance recomputation. Release activation must be fenced to
newly initialized lane PDAs, or use a strict one-time migration which validates
the old image before it enters the invariant-governed state set. Alternatively, a byte-carried certificate
must be independently cheaper to verify under an authenticated commitment;
untrusted root/frontier hints are rejected.

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
| 0 — current | compact ASQ8 | current sealed proof | real fair invariant baseline 2,069,373 CU |
| 1 — fat semantic request | full ASF8, equality-checked against authenticated state | unchanged | real 2,082,274 CU; rejected as dominated |
| 2 — best safe Tx hints | selected only after isolated measurements | unchanged | pending |
| 3 — best safe proof hints | ASQ8 | +320-byte canonical fixed section | selected; real 1,912,443 CU before the remaining zero-byte cuts |
| 4 — combined best | compact ASQ8 | Variant C plus selected zero-byte invariant/arithmetic/cache cuts | real strict success at 1,376,652 CU |
| 5 — ASR8 return sweep | compact ASQ8 | unchanged | measured and rejected: extra bytes add CU and delete no safe work |

## 7. Pareto frontier

The current measured frontier selects compact ASQ8 plus the +320-byte
account-backed fixed section. Zero-byte state/source and algebraic cuts are
required alongside it, but are not themselves byte trades. Full ASF8 is
strictly dominated.

| Variant | Tx bytes | Proof max | Transfer CU | Withdrawal CU | Delta CU | Delta bytes | Security/formal cost |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 0 — compact ASQ8 invariant baseline | 799 measured harness; 811 / 844 wallet shapes | 30,504 max; 30,400 honest | 2,069,373 | pending | baseline | 0 | fresh-PDA invariant/release authentication |
| 1 — full ASF8 | 2,359 measured harness; 2,371 / 2,404 wallet shapes | 30,504 | 2,082,274 | pending | +12,901 | +1,560 Tx | authenticated equality/source bridge; dominated |
| 2 — safe Tx hints | pending | 30,504 | pending | pending | pending | pending | pending |
| 3 — Variant C only | 799 measured harness; 811 / 844 wallet shapes | 30,824 max; 30,720 honest | 1,912,443 | pending | -156,930 | +320 proof | canonical fixed-section transcript/source bridge |
| 4 — selected combined | 799 same-page / 832 rollover measured harness; 811 / 844 wallet shapes | 30,824 max; 30,720 honest | **1,376,652 same-page; 1,385,365 rollover** | 1,593,988 same-page; 1,487,132 rollover (**both over 1.4M**) | **-692,721** vs fair V0 transfer | +320 proof | selected source/formal stack; fresh IDs/build/lifecycle activation and withdrawal CU reduction still required |

The selected harness withdrawal packets are 964/997 bytes; the broader wallet
matrix values are 976/1,009 for Variant 0 and 2,536/2,569 for Variant 1. Both
selected withdrawals currently reject at 1.4M, so the transfer Pareto win does
not close the release CU gate by itself.

### Isolated proof-codec frontier (not combined CU)

| Fixed-field codec | Maximum proof | Isolated component CU | Delta CU | Delta proof bytes | CU saved / 100 B | Current disposition |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| selected packed | 30,504 | 174,747 | 0 | 0 | — | baseline |
| A: canonical pre-final | 30,696 | 139,127 | -35,620 | +192 | 18,552 | fallback; only 24 B below 30 KiB |
| B: canonical final256 | 30,632 | 180,549 | +5,802 | +128 | -4,533 | rejected |
| C: fully canonical | 30,824 | 56,957 | **-117,790** | +320 | **36,809** | leading integration candidate |

These transactions isolate the exact fixed-section decoder and a common
algebraic checksum. They prove a real SBF byte/compute trade, but not its net
effect inside Tag-73. The audit-only Variant C verifier now consumes its 641
canonical records directly rather than transcoding them back to packed form.
The ASPU header and 688-byte ASJA prefix stay byte-for-byte unchanged; only the
first 9,936 proof bytes become 10,256 canonical bytes and the complete tail is
unchanged. Thus the 30,400-byte strict-work KAT becomes 30,720 bytes for the
paired audit input. Production adoption still needs a fresh profile/release
binding and exact transcript-reader/source equivalence before it can enter the
release Pareto table.

### Full-ASF8 host component evidence

The historical default-off full-ASF8 profile from source experiment
`337d6ebaab3fb8feb613a5d7a06f0dfb2f90c0db` independently authenticates the proof,
master, checkpoint and selected-lane accounts; rederives their PDAs; derives
the Pool program from account ownership; uses compiled profile/release
bindings; compares the complete account-derived live snapshot and candidate
afterstate; and then fail-closes without ASR8 or dispatch. On a 30,504-byte
proof, 256 release-host iterations measured 31,738 ns for full ASF8 versus
31,260 ns for compact ASQ8. Parsing ASF8 was 483 ns and the exact statement
comparison 43 ns. These are **host timings, not CU**. The dedicated streaming
SBF profile compiles without an oversized called frame. The current audit branch additionally provides a real default-off
`ASF8` dispatcher which requires exact equality with independently
reconstructed authenticated state and then invokes the same verifier with
production `check_work=true`. Its Pool route forwards the same exact 1,880
bytes under the same nine account metas and preserves registry, ASR8 and
settlement semantics. The real strict run consumes 2,082,274 CU and 2,359
true-TxV1 bytes versus 2,069,373 CU and 799 bytes for compact ASQ8. Variant 1
is therefore rejected: +1,560 bytes buys **negative** CU savings.

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
equivalence. The complete masking-rank certificate has since passed;
activation still requires updated Rust-to-Lean/Aeneas source closure and the
successful one-transaction CU/lifecycle gates.

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

A focused post-integration replay of the checked-in direct-typed artifact
reproduced 633,154 CU and 827 transaction bytes, with
`cryptographic_tag73_executed=false` and exact 792-byte verifier and final
Pool return data:

```bash
replay_dir=$(mktemp -d /tmp/aspis-bytecu-replay.XXXXXX)
CARGO_BUILD_JOBS=2 cargo run --quiet \
  --manifest-path results/v7-pair-forest-byte-cu-20260827/harness/Cargo.toml -- \
  results/v7-pair-forest-byte-cu-20260827/artifacts/components/snapshot-direct/aspis_pool.so \
  results/v7-pair-forest-byte-cu-20260827/artifacts/components/snapshot-direct/aspis_verifier.so \
  "$replay_dir/evidence.json" 792
```

This remains a **MEASURED COMPONENT CU** replay, not an honest Tag-73 or
combined one-terminal transaction.

### Current combined populated-lane blocker

The current combined-harness source is based on harness branch commit
`b0be5240` (itself based on verifier integration `b996eeff`). The exact SBF
artifacts used for the first populated measurement are:

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| Pool | 554,288 | `26ecd0118781b0198d8b552d5635564831e0ff2bf71c6f6400708d6de27e1476` |
| verifier | 1,579,872 | `5be2d15ab1bd69f7e1509bfe8eb746954c12ca4ee658a700fc4db0e2054686b2` |

The populated honest upload payload is 30,828 bytes: unchanged 688-byte ASJA
plus a 30,140-byte proof. Its harness-specific unmined fixture has 196 frontier
nodes and is distinct from the frozen strict-work KAT's 201-node, 30,400-byte
proof. The transaction invokes the strict production verifier with
`check_work=true`; because the fixture is deliberately unmined it could not
accept even with more CU. The measurement is used only to locate compute
before proof completion. It enters the verifier with 845,470 CU and exhausts
exactly 1,400,000 CU. A zero/min-frontier control under the same populated lane
enters with 845,508 CU and exhausts the same cap. No result is returned and all
Pool writes roll back. That historical failure only located the blocker; the
later strict positive path reported above supplies the complete combined CU
and exact atomic settlement evidence.

### Selected combined strict replay

The selected combined harness source ends at `8178d3de`. The exact accepted
same-page evidence is
`results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/strict-selected-endpoint-cache-txv1-runtime1400000.json`.
It records Pool SBF SHA-256
`62509dd10f735bdd207370813352b62d02cb0e02b80eae5640bee7c2282826b5`,
verifier SBF SHA-256
`206658aa7205fae6a7e0de5368f90000d6f1904c1eda788fb8d9c994a6136003`,
and strict canonical proof SHA-256
`ce2aa9bcb2fa4eed70f0f1f09befd656e5146e2208bd590c07c348d7dff2cfe3`.

The selected programs are built with:

```bash
cargo build-sbf --manifest-path programs/aspis-pool/Cargo.toml \
  --features pair-forest-source-result-invariant-audit,pair-forest-verifier-lane-invariant-audit,pair-forest-direct-result-audit \
  --sbf-out-dir "$artifact_dir"

cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml \
  --features v7-pair-forest-fixed-canonical-exact-once-audit,v7-pair-forest-lane-invariant-audit,v7-pair-forest-packed-digest-audit,v7-pair-forest-binary-copy-weights-audit,v7-pair-forest-endpoint-selector-cache-audit \
  --sbf-out-dir "$artifact_dir"
```

The exact deployable-limit replay shape is:

```bash
cargo run --release \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml -- \
  "$artifact_dir/aspis_pool.so" \
  "$artifact_dir/aspis_verifier.so" \
  "$evidence_path" \
  results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin \
  success 1400000 asq8
```

The transaction matrix evidence files are
`transfer-same-page-selected-txv1-1400000.json`,
`transfer-rollover-selected-txv1-1400000.json`,
`withdrawal-same-page-selected-txv1-1400000-ooc.json` and
`withdrawal-rollover-selected-txv1-1400000-ooc.json`. The two withdrawal
success totals come only from explicitly over-limit local diagnostic runs;
they are not deployability claims.

### Full-ASF8 authenticated component

The integrated source experiment is
`337d6ebaab3fb8feb613a5d7a06f0dfb2f90c0db`. Its focused authentication and
fail-closed tests are:

```bash
CARGO_BUILD_JOBS=2 cargo test -p aspis-verifier asf8 -- --nocapture
CARGO_BUILD_JOBS=2 cargo check -p aspis-verifier --no-default-features \
  --features v7-pair-forest-asf8-audit
```

The original 256-iteration native timing replay, which is deliberately not a
CU measurement, is:

```bash
CARGO_BUILD_JOBS=2 cargo test --release -p aspis-verifier \
  asf8_host_component_measurement_separates_all_three_phases \
  -- --ignored --nocapture
```

The exact phase means retained from that run are ASF8 parse 483 ns,
account/PDA authentication 14,926 ns, exact statement comparison 43 ns,
canonical 30,504-byte proof-wire scan 16,029 ns, full ASF8 composition
31,738 ns, and compact ASQ8 composition 31,260 ns. Those numbers remain host
wall-clock observations only. Separately, the later real combined strict
measurement is 2,082,274 total / 1,975,765 verifier CPI / 2,359 true-TxV1
bytes, against 2,069,373 / 1,970,586 / 799 for compact ASQ8.

The current paired audit routes are compiled independently so one SBF binary
contains exactly one grammar:

```bash
# Variant 0: unchanged compact ASQ8.
cargo check -p aspis-verifier --no-default-features \
  --features no-entrypoint,v7-pair-forest-asq8
cargo check -p aspis-pool --no-default-features \
  --features no-entrypoint,pair-forest-account-evidence

# Variant 1: exact 1,880-byte ASF8 at Pool and verifier entrypoints.
cargo check -p aspis-verifier --no-default-features \
  --features no-entrypoint,v7-pair-forest-asf8-audit
cargo check -p aspis-pool --no-default-features \
  --features no-entrypoint,pair-forest-full-asf8-audit

# Variant C: unchanged ASQ8 transport, +320 canonical proof fixed section.
cargo check -p aspis-verifier --no-default-features \
  --features no-entrypoint,v7-pair-forest-fixed-canonical-audit
```

Focused host checks for the new support are:

```bash
cargo test -p aspis-verifier \
  v7_pair_forest_dispatch::tests::full_asf8_is_authenticated_against_the_same_accounts_and_asja \
  -- --exact
cargo test -p aspis-core --features v7-fixed-canonical-audit \
  v7_fixed_canonical_audit::tests::canonical_fixed_delta_is_exactly_320_bytes \
  -- --exact
```

The exact selected SBF/LiteSVM command and hashes are recorded above. Solana
CLI use must set `NO_DNA=1`; no network signing or submission is part of this
audit.

## 11. Release decision rule

Adopt the +320-byte canonical fixed section for the selected release profile:
it saves 156,930 real combined CU and the complete selected stack lands at
1,376,652 CU. Keep compact ASQ8 because full ASF8 adds both bytes and CU. Keep
ASR8 at 792 bytes because every larger measured point is dominated.

The 30,504-byte original proof ceiling therefore becomes a 30,824-byte ceiling
for this fresh profile; the measured honest selected proof is 30,720 bytes.
This decision does not authorize production activation until the fresh-PDA,
generated release identities, reproducible build, formal/source composition
and remaining lifecycle matrix are all green.
