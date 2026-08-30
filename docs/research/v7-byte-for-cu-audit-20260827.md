# V7 byte-for-CU Pareto audit

Date: 2026-08-28

Status: CU configuration locked on the research branch. No deployed program,
proof-system security parameter, terminal transport, or network
state has been changed. Sections 3--10 retain the measurement chronology that
led to the final result; this section supersedes their earlier blocker status.

## Decision status

**SPEND PROOF BYTES FOR CU**

The final configuration combines the previously measured +320-byte canonical
fixed-field proof representation with zero-byte sparsity/basis refactorings.
It completes the real combined
`TxV1 -> Pool -> Tag-73 verifier -> ASR8 -> atomic settlement` path for all
four selected transfer/withdrawal and same-page/rollover shapes. It keeps the
320-byte ASQ8 and 792-byte ASR8. The account-backed proof maximum is 30,824
bytes rather than the compact baseline's 30,504 bytes; the four honest strict
fixtures range from 30,720 to 30,824 bytes. No transaction-carried hint or
other fatter-proof hint was selected.

| Operation | History path | Real combined CU | TxV1 bytes | Headroom to 1.3M CU | Headroom to 4,096 B |
| --- | --- | ---: | ---: | ---: | ---: |
| Private transfer | same page | 1,145,926 | 799 | 154,074 | 3,297 |
| Private transfer | rollover | 1,191,499 | 832 | 108,501 | 3,264 |
| Withdrawal | same page | 1,136,171 | 964 | 163,829 | 3,132 |
| Withdrawal | rollover | 1,201,754 | 997 | 98,246 | 3,099 |

Every row is **MEASURED REAL CU** from a successful strict-work LiteSVM
transaction at the deployable 1,400,000-CU runtime limit. The proof performs
the exact 35/31/34-bit work checks. Simulation and execution agree. The worst
case is 1,754 CU above the preferred 1.2M target and 98,246 CU below the hard
1.3M release gate. Further speculative CU work is deferred; formal/source
closure and TxV1 devnet lifecycle evidence now have higher release value.

The locked verifier binary is 1,968,872 bytes with SHA-256
`ad84706b714dedfe89e5f3ebcf91dff8ab300ab3dfe3eb2d7d846e1bf0c635d4`.
The unchanged Pool binary is 526,656 bytes with SHA-256
`f3ae8d96164189bec2e134b659e4fc5bd39a6b16488cde1bbd23f278a9369c76`.
The exact optimisation/equivalence record is
`docs/research/v7-cu-sparsity-lock-20260828.md`.

## 1. Frozen baseline

The positive-path integration base is:

```text
e4c317fe4fa420c8d2aab613d400abc3607b45db
test: freeze strict-work forest dispatch KAT
```

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
| Selected lane-invariant/CU-cut source bridge | `aeneas-verif/v7-forest-lane-invariant-source-20260828/` | `572b8211` integrated endpoint-cache closure |

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
| Historical full-ASF8 authenticated component | HOST TIMING (NOT CU) | not applicable | On a 30,504-byte wire, 256 native release iterations measured 31,738 ns full ASF8 versus 31,260 ns compact ASQ8. That pinned source profile had no dispatcher arm and emitted no ASR8. The new real audit route is prepared but not yet measured. |
| Honest ASQ8 -> Tag-73 -> ASR8 strict-work host KAT | HOST ACCEPTANCE (NOT CU) | not applicable | Exact 30,400-byte proof, 201 frontier nodes, exact 35/31/34-bit work, complete semantic terminal/relation/openings and exact 792-byte ASR8 all pass through the production dispatcher. |
| Empty-lane combined Pool -> selected verifier entry | MEASURED REAL CU (incomplete) | 82,493 CU before CPI; 1,317,507 remaining | Real combined SBF transaction and account path. It establishes entry budget, not acceptance or total successful CU. |
| Populated 13-pair honest lane combined attempt | MEASURED REAL CU (failed/rollback) | 554,530 CU before CPI; exactly 1,400,000 exhausted | Real 30,140-byte honest unmined proof under strict production `check_work=true`; selected verifier entered with 845,470 CU, no result returned, exact rollback. Logs do not identify a later verifier phase. |
| Populated 13-pair zero/min-frontier control | MEASURED REAL CU (failed/rollback) | 554,492 CU before CPI; exactly 1,400,000 exhausted | Selected verifier entered with 845,508 CU and exhausted. This pins the populated prefix independently of proof length/content; it is not cryptographic acceptance. |
| Fair complete Variant 0 | MEASURED REAL CU | 3,008,600 | One true-TxV1 transaction completes compact ASQ8, strict Tag-73 verification, exact ASR8 validation, selected-lane/history/nullifier settlement and readonly checks. This measurement uses the same revision and harness as the variants below. |
| Source invariant decoder | MEASURED REAL CU | 2,538,942 | Same complete transaction; removes only redundant active root reconstruction from a fresh initialized Pool-owned lane image. Saves 469,658 CU. |
| Source + authenticated-result invariant encoder | MEASURED REAL CU | 2,069,373 | Same complete transaction; additionally avoids reconstructing the verifier-authenticated result root a second time. Saves 939,227 CU from Variant 0. |
| Corrected exact-once canonical fixed section | MEASURED REAL CU | **1,912,443** | Same source/result invariant path and exact settlement, with 641 fixed QM31 values canonical in the proof. Fixed limbs are consumed once by the canonical reader and query limbs once by the opening decoder. Proof is 30,720 B (+320); transaction is unchanged; saves 156,930 CU from the invariant Variant 0. |
| Full authenticated ASF8 | MEASURED REAL CU | 2,082,274 | Same strict source/result-invariant path and 30,400-byte proof; complete authenticated fieldwise equality, verifier, 792-byte ASR8 and exact settlement. Verifier CPI is 1,975,765 CU and the harness true-TxV1 packet is 2,359 B. This is +12,901 total CU, +5,179 verifier CU and +1,560 Tx bytes versus matched ASQ8. |
| Hardened verifier lane invariant | MEASURED REAL CU | 1,452,893 | Six-account CPI independently authenticates the pinned Pool/registry/policy release root and canonical entry before consuming the fresh-PDA lane invariant. Saves 459,550 CU from 1,912,443. Current pinned IDs are audit fixtures, not production activation. |
| Packed public-digest selectors | MEASURED REAL CU | 1,409,554 | Exact linear factorization packs four digest differences before multiplying by their shared selector. Same relation, transcript and wire; saves 43,339 CU. |
| Direct canonical ASR8 reuse | MEASURED REAL CU | 1,400,108 | Pool reuses verifier-authenticated canonical result bytes and checks the same fieldwise binding instead of rebuilding the encoding; saves 9,446 CU. |
| Binary copy weights | MEASURED REAL CU | **1,386,744** | Generated copy weights are proved to be exactly 0/1; the accumulator skips/adds while values remain accumulated unconditionally. Saves 13,364 CU. Exact strict 1.4M execution succeeds with 13,256 CU headroom. |
| Endpoint selector cache | MEASURED REAL CU | **1,376,652** | Exact-tag common-subexpression cache replaces 56 of 272 endpoint selector recomputations; collisions miss and recompute. Saves another 10,092 CU, with the same 799-byte TxV1 harness packet, 30,720-byte proof and 792-byte ASR8. Exact strict 1.4M execution succeeds with 23,348 CU headroom. |
| Selected transfer rollover | MEASURED REAL CU | **1,385,365** | Exact strict 35/31/34-bit proof, 832-byte true-TxV1 packet, pair index 255→256, old page readonly, new page/lane/history/nullifier atomic; 14,635 CU headroom. |
| Withdrawal same-page, unconstrained honest q16 counter | MEASURED REAL CU (diagnostic limit) | 1,593,988 | Exact SPL and Pool settlement succeed only above the deployable limit; exact 1.4M run rejects and rolls back all Pool/token bytes. The q16 scan alone costs 232,351 CU. |
| Withdrawal rollover, unconstrained honest q16 counter | MEASURED REAL CU (diagnostic limit) | 1,487,132 | Exact SPL and rollover settlement succeed only above the deployable limit; exact 1.4M run rejects and rolls back. The q16 scan alone costs 95,549 CU. |
| Withdrawal same-page, accepted counter-zero honest proof | MEASURED REAL CU | **1,367,025** | Unchanged strict verifier, 964-byte true-TxV1 packet, 30,824-byte proof, frontier 203, exact SPL and Pool settlement; 32,975 CU headroom. Measurement-only pending nonce-selection cryptographic review. |
| Withdrawal rollover, accepted counter-zero honest proof | MEASURED REAL CU | **1,395,583** | Unchanged strict verifier, 997-byte true-TxV1 packet, 30,772-byte proof, frontier 202, exact SPL and rollover settlement; only 4,417 CU headroom. Measurement-only and below desired release margin. |
| Withdrawal same-page, selected CU stack | MEASURED REAL CU | **1,295,086** | Same strict counter-zero proof and 964-byte TxV1 packet after the Pool history invariant, exact semantic common factoring and frozen Copy-pattern CSE; exact SPL/Pool atomic settlement and all three work checks pass. 104,914 CU headroom, but activation remains source/formal gated. |
| Withdrawal rollover, selected CU stack | MEASURED REAL CU | **1,360,640** | Same strict counter-zero proof and 997-byte TxV1 packet; exact rollover settlement passes with 39,360 CU headroom. Relation, transcript, proof, wire and ASR8 are unchanged. Counter-zero conditioning and history-writer provenance remain release gates. |

The 1,255,491 and 81,922 historical component results must not be added and
presented as exact combined CU.  The new 3,008,600 / 2,538,942 / 2,069,373 /
1,912,443 figures are different: each is a complete matched executable path.
They supersede the earlier failed-entry measurements for Pareto decisions.

## 4. Instrumented one-terminal CU breakdown

This table is populated only with executable checkpoints. The corrected-VC
strict profiler measured 1,921,654 CU versus 1,912,443 uninstrumented, so the
checkpoint overhead is 9,211 CU; phase deltas below are used for attribution,
while release totals use uninstrumented binaries.

| Category | Current evidence | Classification | Variant deltas |
| --- | ---: | --- | ---: |
| ASQ8 parse | included before first marker | MEASURED COMPONENT CU | no material byte-for-CU candidate identified; deprioritized behind populated-lane pre-CPI work |
| pre-verifier dispatch/account reconstruction/digests | 494,414 | MEASURED REAL CU (instrumented) | hardened six-account verifier invariant reduces total by 459,550 CU after paying the independent registry gate |
| ASF8 reconstruction | 3,011 | MEASURED COMPONENT CU | pending |
| canonical codecs/copies/comparisons | exact wire phase 515,274; 4,996-limb canonical scan alone 515,000 | MEASURED COMPONENT CU | direct typed snapshot saves 2,191 CU transaction-wide; the exact-once production reader is integrated and its Rust-to-Lean/Aeneas bridge proves 2,564 fixed plus 2,432 query limbs are consumed exactly once |
| semantic sumcheck | 119,854 | MEASURED REAL CU (instrumented) | unchanged |
| gamma combine | 136,982 | MEASURED REAL CU (instrumented) | unchanged |
| paired Merkle authentication | 96,525 | MEASURED REAL CU (instrumented) | unchanged |
| terminal/prefactorised semantic checks | 627,529 | MEASURED REAL CU (instrumented) | packed digest selectors save 43,339 total CU; binary copy weights save another 13,364 total CU |
| relation round-3 weights | 69,662 | MEASURED REAL CU (instrumented) | pending additional margin audit |
| relation prepared weights | 39,131 | MEASURED REAL CU (instrumented) | pending additional margin audit |
| relation round-1 values | 36,466 | MEASURED REAL CU (instrumented) | unchanged |
| q16 schedule | transfer 29,389; withdrawal same-page 232,351; withdrawal rollover 95,549 | MEASURED REAL CU (instrumented) | counter-zero honest proofs retain the unchanged first-cap-203 scan but exit after candidate zero; exact full-transaction savings are 226,963 / 91,549 CU, pending cryptographic review |
| final256 | 26,866 | MEASURED REAL CU (instrumented) | unchanged |
| query fold | 20,877 | MEASURED REAL CU (instrumented) | unchanged |
| ASR8 construction/validation | encode 2,487; set-return phase 360; Pool get/decode 3,512; validate/apply-byte prep 4,663 | MEASURED COMPONENT CU | expansion rejected; direct authenticated canonical reuse saves 9,446 total CU |
| populated selected-lane pre-CPI validation | redundant source and result reconstruction removed by separate source invariants | MEASURED REAL CU | -469,658 CU source decoder; -469,569 CU result encoder; -939,227 CU combined |
| selected-lane/history/nullifier writes | final persistence marker delta 517; earlier planning is included in preflight/custody-plan | MEASURED COMPONENT CU | full split pending |
| withdrawal SPL CPI/rollback | exact SPL and atomic settlement pass for both counter-zero withdrawal shapes; unconstrained fixtures above 1.4M and their deployable-limit rollback controls are also measured | MEASURED REAL CU | selected stack: same-page 1,295,086; rollover 1,360,640, leaving 104,914 / 39,360 CU; still formal/source gated |
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
| Replace repeated populated-lane root reconstruction with authenticated Pool-owned lane-state provenance | 0 | 0 | potentially the observed roughly 472k empty-to-13-pair pre-CPI delta; exact phase probe pending | real combined entry budget plus source audit: nonempty `decode_with_empty_roots` executes `reconstruct_nonfull_root`, twenty Poseidon parents | This is a zero-byte CU optimisation, not a byte trade. Must prove the Pool-owned lane PDA is an inductive invariant: every initializer/deposit/settlement writer stores an exact root/frontier pair, no alternate writer exists, and owner/PDA/version/index/inactive-frontier checks remain fail-closed. Activation requires newly initialized PDAs or a strict one-time migration boundary | **highest priority** |
| Supply a populated-root/frontier certificate in Tx/proof bytes | pending | pending | only viable if checking is cheaper than twenty Poseidon parents | no measurement yet | Untrusted bytes cannot replace account provenance; either verify a cryptographic certificate under an already authenticated commitment or reject | inventory only; do not trust raw hint |
| Supply full ASF8 and compare it with authenticated reconstruction | +1,560 | 0 | **+12,901 CU regression** | complete matched strict path: 2,082,274 versus ASQ8 2,069,373 | Exact fieldwise comparison retains master, checkpoint, selected-lane, deployment, profile/release and afterstate checks | **reject: strictly dominated** |
| Finalization-computed sealed proof-body SHA in the existing 32-byte authority slot | 0 | 0 | none on current ASQ8: it performs no terminal body-digest pass | default-off `ASD1` implementation at `609e18fc`; old native dispatch measured 15,597 CU | Exact lifecycle/source invariant, cache/request binding and close-path activation proof | exclude unless final ASQ8 introduces an authenticated body-digest claim |
| Checked aggregate M31 inverse hint | 0 or +4 | +4 or 0 | one inversion minus equality check; unmeasured | static arithmetic inventory | Prove nonzero/input binding and exact multiplication check | benchmark if SBF delta is material |
| Two checked QM31 circle-map inverses | 0 or +32 | +32 or 0 | two inversions minus equality checks; unmeasured | static arithmetic inventory | Same relation, new canonical hint framing/source bridge | benchmark |
| Canonical final-vector representation | 0 | +128 | isolated SBF **+5,802 CU** | default-off Variant B at `f4756ede`; evidence `9d4fb5e8` | Encoding/canonicality bridge, no changed claims | reject |
| Canonical fixed-prefix representation | 0 | +192 | isolated SBF **-35,620 CU** | default-off Variant A at `f4756ede`; evidence `9d4fb5e8` | Encoding/canonicality bridge, no changed claims | retain only as fallback |
| Canonical complete 641-QM31 fixed section | 0 | +320 | complete transaction **-156,930 CU** | corrected exact-once implementation integrated at `356734cf`; strict combined 1,912,443 versus invariant baseline 2,069,373 | Exact transcript-reader equivalence and all-4,996-limb coverage are bridged at `6c2d085c`; fresh production profile/release still required | **measured Pareto winner; about 490 CU saved per added byte** |
| Verifier-side fresh-PDA lane invariant | 0 | 0 | **-459,550 CU** after independent registry hardening | hardened six-account path `e86d48cc`: 1,912,443 to 1,452,893 | Immutable selected-release Pool/registry/policy root plus fresh-PDA source theorem; fake Pool+fake registry fail closed | source bridge integrated; activation still needs production constants |
| Pack public digest differences before shared selector | 0 | 0 | **-43,339 CU** | `efc928fc`: 1,452,893 to 1,409,554 | Exact QM31 linear identity; no relation/wire/transcript change | select |
| Reuse authenticated canonical ASR8 bytes | 0 | 0 | **-9,446 CU** | `d14ea1b1`: 1,409,554 to 1,400,108 | Fieldwise equivalence and exact verifier-result provenance | selected; source bridge integrated at `17a83e1f` |
| Specialize generated binary copy weights | 0 | 0 | **-13,364 CU** | `6045276e`: 1,400,108 to 1,386,744 | Generated weights remain exactly 0/1; unconditional value accumulation preserved | selected; source bridge integrated at `17a83e1f` |
| Cache exact-tag endpoint selectors | 0 | 0 | **-10,092 CU** | `b6760f7d` / harness `8178d3de`: 1,386,744 to 1,376,652 | Exact-key hits only; collisions miss and recompute; 1,024 Boolean and 64 off-domain equality cases pass | selected; source bridge integrated at `572b8211` |
| Factor exact semantic common terms | 0 | 0 | **-5,722 CU** on rollover | selected strict withdrawal comparison frozen in `ROLLOVER-CU-MARGIN-EVIDENCE.md` | Exact algebraic common-factor identities; 128 off-domain semantic and all-1,024 honest-terminal cases pass; production activation needs the corresponding Lean/source bridge | measured, source/formal gated |
| Cache frozen Copy-pattern windows | 0 | 0 | **-19,191 CU** on rollover | selected strict withdrawal comparison frozen in `ROLLOVER-CU-MARGIN-EVIDENCE.md` | Exact overlapping-window subtraction under the frozen generated Copy table; 256 pattern and typed Copy-reference cases pass; production activation needs the generated-table/source bridge | measured, source/formal gated |
| Use the authenticated history-page writer invariant | 0 | 0 | **-47,056 CU same-page; -10,030 CU rollover** | exact strict Pool/withdrawal transactions | Must prove every initializer/writer maintains the canonical page image and that the fresh rollover page has no alternate writer | measured, source/Aeneas gated |
| Honest final-nonce search for an already-accepted counter-zero compact schedule | 0 | 0 | **-226,963 CU same-page withdrawal; -91,549 CU rollover withdrawal** before the later zero-byte cuts | real strict unchanged-verifier transactions; selected stack reaches 1,295,086 / 1,360,640 CU | Accepted language is unchanged; Lean `compact_candidate_zero_is_first` proves the deterministic first-compact fact. Must still close honest search distribution against K1.6/grinding and pointwise hiding and record prover cost | measurement-only; release margin recovered, cryptographic review remains |
| Expand ASR8 within the 1,024-byte return-data cap | 0 | 0 | none; measured gross cost is +38 to +58 CU | five distinct LiteSVM component executions | Every added field must be verifier-derived and immediately bound to the selected program/profile/release/statement/accounts | reject: keep 792 B |
| Remove live-snapshot encode/decode round trip | 0 | 0 | **-2,191 CU** in matched component transaction | default-off direct-typed probe at `f8804061` | Source bridge from exact canonical master/lane PDA+owner decoders to the unchanged snapshot predicate | retain for production integration |
| Defer standalone 4,996-limb canonical scan and consume canonically inside real crypto | 0 | 0 | the duplicate scan removal is already reflected in the selected exact-once representation | runtime integration `356734cf`; Lean/Aeneas bridge `6c2d085c` | Proven coverage is 2,564 fixed plus 2,432 query limbs with truncation, trailing, oversized and noncanonical rejection and unchanged transcript observations | integrated discipline, not an independent variant |

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
| 0 — current | compact ASQ8 | current sealed proof | complete fair path measured at 3,008,600 CU; source-invariant form 2,069,373 CU |
| 1 — fat semantic request | full ASF8, equality-checked against authenticated state | unchanged | measured 2,082,274 CU; strictly dominated and rejected |
| 2 — best safe Tx hints | selected only after isolated measurements | unchanged | pending |
| 3 — best safe proof hints | ASQ8 | selected only after isolated measurements | pending |
| 4 — combined best | compact ASQ8 | +320-byte canonical fixed section plus selected zero-byte cuts | transfer and both counter-zero withdrawal shapes fit; worst-case withdrawal is 1,360,640 CU, pending cryptographic and source/formal closure |
| 5 — ASR8 return sweep | compact ASQ8 | unchanged | measured and rejected: extra bytes add CU and delete no safe work |

## 7. Pareto frontier

The corrected canonical fixed-section candidate is the measured Pareto
winner: it was measured against Variant 0 in the same complete executable
path, while full ASF8 is worse in both bytes and CU and ASR8 expansion is also
strictly worse. The selected configuration fits the exact 1.4M-CU limit for
both transfer shapes. Both withdrawal shapes also fit when the honest prover
finds an already-valid counter-zero schedule. The selected zero-byte stack now
leaves 39,360 CU on rollover, but remains a provisional frontier pending the
counter-zero distribution audit and the history/semantic-pattern source and
formal bridges.

| Variant | Tx bytes | Proof max | Transfer CU | Withdrawal CU | Delta CU | Delta bytes | Security/formal cost |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 0 — compact ASQ8, source/result invariant | 811 / 844 | 30,504 max; 30,400 strict KAT | 2,069,373 | pending | baseline after source-safe zero-byte work | 0 | inductive fresh-PDA lane-state provenance |
| 1 — full ASF8 | 2,371 / 2,404 | 30,504 | 2,082,274 (2,359-B harness packet) | pending | +12,901 | +1,560 Tx | exact authenticated equality; rejected |
| 2 — safe Tx hints | pending | 30,504 | pending | pending | pending | pending | pending |
| 3 — canonical fixed section + selected zero-byte stack | 811 / 844 wallet; 799 / 832 strict harness; withdrawal 964 / 997 | 30,824 max; 30,720 strict KAT | **1,376,652 same-page; 1,385,365 rollover** | unconstrained-counter: 1,593,988 / 1,487,132; selected counter-zero: **1,295,086 / 1,360,640** | **-692,721** same-page transfer from invariant Variant 0 | +320 proof | exact-once canonical reader and source bridge are integrated; counter-zero, history writer invariant and latest semantic-pattern cuts remain formal/source gated |
| 4 — combined Tx/proof bytes | not selected | not selected | full ASF8 combination not run because ASF8 is independently dominated | pending | — | — | rejected by decision rule |

The selected strict-harness withdrawal packets are 964 bytes same-page and
997 bytes rollover; both remain well below 4,096 bytes. Unconstrained-counter
diagnostic runs above the release ceiling accept at 1,593,988 and 1,487,132 CU,
perform the exact SPL `TransferChecked`, and settle Pool state atomically. Their
exact-1.4M controls exhaust CU and roll back every Pool and token account
byte-for-byte. Matched profiling identifies the data-dependent q16 scan as the
dominant delta, not transport or the semantic terminal. Already-valid
counter-zero honest proofs initially reduced the same exact operations to
1,367,025 and 1,395,583 CU without changing verifier acceptance. The selected
history and terminal cuts reduce those totals to 1,295,086 and 1,360,640 CU.
That is adequate measured margin, but it is not release-selected until the
explicit cryptographic and source/formal gates above are discharged.

The strict rollover fixture advances pair index 255 to 256 using a fresh
statement-specific 35/31/34-bit-work proof. It leaves the full current page
readonly and byte-exact, writes the exact new root to page 1, and atomically
settles the lane, history and nullifier. At 1,385,365 CU it retains 14,635 CU
under the exact limit.

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
SBF profile compiles without an oversized called frame. The current audit
branch additionally implements a real default-off `ASF8` dispatcher which
requires exhaustive fieldwise equality with independently reconstructed
authenticated state and then invokes the same verifier with production
`check_work=true`. Its Pool route forwards the same exact 1,880 bytes under
the same nine account metas and preserves registry, ASR8 and settlement
semantics. The matched complete run measured 2,082,274 CU and a 2,359-byte
harness TxV1 packet, versus 2,069,373 CU and 799 bytes for compact ASQ8.
Therefore the +1,560-byte transport is rejected without combining it with
Variant C.

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

These 634k values are **not** semantic-terminal measurements and do not undo
the earlier 413,694-CU prefactorisation saving.  That earlier matched profile
reduced the old single-leaf semantic terminal from 821,667 to 407,973 CU.  The
return sweep instead measures a transport/component harness whose dominant
work is the roughly 515k-CU canonical proof-wire scan, plus Pool-to-verifier
CPI, registry/account checks, ASF8 reconstruction, return-data handling and
atomic byte writes; it deliberately executes no Tag-73 equations or Pool
Poseidon.  The selected complete one-transaction totals remain 1,376,652 CU
for transfer and 1,295,086 / 1,360,640 CU for same-page / rollover withdrawal.

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

The frozen artifacts and phase ledgers are retained on the dedicated audit
branch `research/v7-byte-cu-audit-20260827` under
`results/v7-pair-forest-byte-cu-20260827/`.  The five ASR8 sweep points and
their executable evidence are pinned by `4d4d87f4`; the later component
decomposition is pinned by `f8804061`.  They are not silently attributed to
the current production branch.  The artifacts were built in:

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

The exact return-data sweep can be replayed from that audit worktree with:

```bash
audit_root=<repo>
for asr8_bytes in 792 824 856 920 1024; do
  replay_dir=$(mktemp -d "/tmp/aspis-asr8-${asr8_bytes}.XXXXXX")
  CARGO_BUILD_JOBS=2 cargo run --quiet \
    --manifest-path "$audit_root/results/v7-pair-forest-byte-cu-20260827/harness/Cargo.toml" -- \
    "$audit_root/results/v7-pair-forest-byte-cu-20260827/artifacts/${asr8_bytes}/aspis_pool.so" \
    "$audit_root/results/v7-pair-forest-byte-cu-20260827/artifacts/${asr8_bytes}/aspis_verifier.so" \
    "$replay_dir/evidence.json" "$asr8_bytes"
done
```

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

### Historical populated-lane blocker (superseded)

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
Pool writes roll back. Phase instrumentation and an over-budget positive path
were still required at that point. These failed-entry runs are retained as
provenance only: the later strict complete paths at 3,008,600, 2,538,942,
2,069,373 and 1,912,443 CU supersede them. Phase instrumentation is now
complete, and the selected hardened stack subsequently reaches 1,376,652 CU
under the exact 1.4M limit.

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
31,738 ns, and compact ASQ8 composition 31,260 ns. These numbers are host
wall-clock observations only. No LiteSVM transaction, real verifier CU, or
combined one-terminal CU is attributed to this experiment.

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

The real combined frontier now exists. The selected production direction is
**SPEND PROOF BYTES FOR CU**: retain the compact 320-byte ASQ8 and 792-byte
ASR8, but use the +320-byte canonical fixed-field proof representation with a
30,824-byte maximum body. The later sparsity/basis gains are exact zero-byte
evaluator refactorings. Activation remains gated on the corresponding
Lean/Aeneas/source closure and the finalized TxV1 devnet lifecycle; this audit
alone is not a mainnet authorization.
