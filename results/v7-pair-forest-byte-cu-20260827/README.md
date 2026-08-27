# V7 pair-forest byte-for-CU profile

This directory contains a default-off LiteSVM component profile for the
non-cryptographic ASQ8/ASF8/ASR8 transport and the byte-only eight-lane Pool
state wrapper.  It is pinned to source revision
`041780f4ef0be98c5b1675df87917046b62b4c2f`.

The frozen byte inventory is:

| Item | Bytes |
|---|---:|
| ASQ8 compact request | 320 |
| reconstructed ASF8 statement | 1,880 |
| ASR8 result | 792 |
| verifier-derived candidate afterstate | 688 |
| staged-pair grammar maximum | 30,504 |
| minimum-frontier proof body used by this fixture | 20,676 |
| fixture upload payload (688-byte candidate + proof) | 21,364 |
| fixture proof account (40-byte header + payload) | 21,404 |

The profile executes account, PDA, owner, registry, profile/release, codec,
copy, comparison, result-transport, lane/history, and nullifier plumbing.  It
does **not** execute Tag-73 cryptography: the normal ASQ8 handler still fails
closed with `V7_PAIR_FOREST_ASQ8_CRYPTO_NOT_INTEGRATED` after reconstructing
the statement.  The profile-only Pool encoder also skips the strict encoder's
20 Poseidon root reconstructions so those operations do not contaminate this
non-cryptographic component measurement.  A profile result therefore cannot
be reported as a combined verifier transaction.

The marker log calls are themselves metered.  The JSON evidence records both
the total profiled transaction and consecutive marker deltas so this overhead
remains visible.

## Host gates

- normal verifier ASQ8 focused tests: 6 passed;
- verifier profile focused check: passed;
- Pool profile focused tests: 1 passed (96 filtered);
- standalone LiteSVM harness check: passed;
- Solana program autofixer: zero issues in all five changed program Rust
  files, with no repeat requested.

The 30,504-byte number is the selected grammar maximum.  It is not replaced
by the smaller fixture: this measurement uses the pinned minimum legal
frontier of 14 nodes per tree, hence
`19,948 + 2 * 14 * 26 = 20,676` proof bytes.

## Executable component measurement

All five points executed as distinct LiteSVM transactions.  The exact
profile-harness transaction is 827 wire bytes; it is not the wallet TxV1
811/844-byte transaction shape.  Every final Pool return is canonical
792-byte ASR8.

| Verifier CPI return | Total CU | Delta from 792 | Safe Pool work deleted |
|---:|---:|---:|---:|
| 792 | 634,663 | 0 | 0 |
| 824 | 634,701 | +38 | 0 |
| 856 | 634,708 | +45 | 0 |
| 920 | 634,718 | +55 | 0 |
| 1,024 | 634,721 | +58 | 0 |

The 792-byte phase ledger is in `evidence-792.json`.  Its dominant
`staged-codecs` phase is 519,913 CU.  That phase:

- encodes the account-derived 800-byte live snapshot and decodes it through
  the existing byte-oriented parser (an eliminable interface round trip);
- decodes and canonical-checks the 688-byte candidate afterstate;
- parses exact proof sections and frontier lengths; and
- canonical-checks 4,996 packed M31 limbs: 2,564 fixed limbs plus
  `16 * (104 C1 + 48 C2)` query limbs.

It executes no SHA, Poseidon, Merkle authentication, sumcheck, or terminal
equation.  The proof parse and packed-M31 scan are work the real verifier must
perform once and can reuse; they must not be added to a verifier CU figure a
second time.  Only the live-snapshot encode/decode round trip is clearly
wrapper-specific duplication.

The remaining notable 792-byte marker deltas are registry authentication
7,598 CU, master decode 7,123, lane decode 5,803, verifier CPI entry to first
marker 4,354, Pool result validation/apply-byte preparation 4,663, return
copy/tail-check/decode 3,512, ASF8 reconstruction 3,011, and persistence 517.
Marker logging is metered, so totals are conservative profile measurements.

## Return-data sweep

The additional default-off features measure 824, 856, 920, and 1,024-byte
return-data points beside the 792-byte baseline.  Sweep tails repeat a prefix
of the canonical ASR8 and are byte-checked by the Pool.  They are synthetic:
source inspection found no additional verifier-derived field that deletes Pool
work beyond what the existing authenticated ASR8 already authorizes.  In
particular, checkpoint, anchor, profile/release, and statement-digest repeats
are either already available to the Pool or require new hashing/comparison.
The sweep therefore measures gross return copy/decode/validation cost, with
zero claimed production deletion for every extension point.

The measured verifier-return / Pool-copy-decode / post-CPI marker deltas are:

| Return bytes | Verifier return | Pool copy/decode | Post-CPI |
|---:|---:|---:|---:|
| 792 | 360 | 3,512 | 314 |
| 824 | 371 | 3,538 | 314 |
| 856 | 379 | 3,538 | 314 |
| 920 | 389 | 3,538 | 314 |
| 1,024 | 390 | 3,540 | 314 |

Conclusion: keep exact 792-byte ASR8.  Expanding it costs CU and deletes no
safe work.

## SBF provenance

- builder: `solana-cargo-build-sbf 2.3.0`, platform-tools v1.48,
  SBF Rust 1.84.1;
- 792 stack-clean build: unit
  `aspis-v7-byte-cu-sbf-stackfix-02.service`, invocation
  `ccfed6e1251c4c0390f2b387b7dd67ee`;
- 824/856/920/1024 builds: unit
  `aspis-v7-byte-cu-sbf-returns-01.service`, invocation
  `ba8443a17f1e4f7da69f4c730aa23938`;
- both scopes used `MemoryHigh=6G`, `MemoryMax=8G`,
  `MemorySwapMax=0`, and `CARGO_BUILD_JOBS=1`;
- return sweep observed peak: 219,418,624 bytes; swap: zero.

Each evidence JSON pins its exact Pool and verifier ELF SHA-256.  SBF still
reports oversized frames in uncalled deposit/checkpoint/full-dispatch and
standalone statement-decoder functions compiled into these inactive feature
artifacts.  No oversized-frame warning remains on the profile entrypoint's
executed call graph; all five LiteSVM executions completed successfully.

## Phase 1 staged-codec decomposition

Three additional default-off verifier artifacts carry identical matched
subphase markers. They reuse the same 792-byte Pool artifact and the same
20,676-byte minimum-frontier fixture.

| Probe | Total CU | Snapshot phase | Candidate decode | Wire phase | Tail |
|---|---:|---:|---:|---:|---:|
| Exact component baseline | 635,345 | 3,188 | 1,834 | 515,274 | 299 |
| Deferred wire canonicality | 120,342 | 3,185 | 1,834 | 274 | 299 |
| Direct typed snapshot | 633,154 | 979 | 1,834 | 515,274 | 317 |

The component markers and called-path stack-safe boxing add 682 CU to the
earlier 634,663-CU 792-byte total, so comparisons in this table use the matched
635,345-CU component baseline.

The complete 4,996-limb packed-M31 canonical scan costs exactly 515,000 CU
relative to the exact deferred layout/padding parser. Transaction-wide, the
deferred probe saves 515,003 CU. The deferred parser still checks exact body
length, section boundaries, frontier cap and lengths, and the fixed packed
padding bits.

This is **not** an accepting optimization by itself. A focused test sets the
first packed limb to the field modulus: the exact parser rejects it while the
deferred measurement parser accepts its layout. The only sound integration is
for the later real cryptographic verifier to consume the deferred wire and
canonically decode every one of the 2,564 fixed limbs and every one of the
`16 * (104 C1 + 48 C2)` query limbs exactly once before acceptance. Running
the current complete scan and then decoding the fields again would waste the
measured 515k CU.

The account-derived 800-byte live-snapshot encode/decode round trip costs
3,188 CU versus 979 CU for direct typed validation: 2,209 CU at the matched
subphase, or 2,191 CU transaction-wide after code-layout/tail differences.
The direct route retains the full wire canonical scan and calls the same
semantic live-snapshot predicate. It is a candidate plumbing optimization,
conditional on the source bridge preserving that the typed object comes from
the exact canonical master/lane account decoders and PDA/owner checks.

The candidate-afterstate decode is independently stable at 1,834 CU in all
three builds.

Final component SBF provenance:

- unit: `aspis-v7-byte-cu-components-04.service`;
- invocation: `bd27d7c866d242daab2237b3cc220ce8`;
- limits: `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, jobs=1;
- maximum per-command RSS: 245,404 KiB; swap: zero; all three exits: 0.

The called profile path has no SBF stack-limit warning after boxing the typed
live snapshot and encoded 800-byte buffer. The build still links the existing
standalone full terminal-statement decoder and reports its known 6,464-byte
frame, but this measurement-only dispatch never calls that decoder.
