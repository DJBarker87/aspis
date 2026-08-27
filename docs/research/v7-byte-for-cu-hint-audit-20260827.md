# V7 byte-for-CU hint and proof-account audit

Date: 2026-08-27

Audited revision: `041780f4ef0be98c5b1675df87917046b62b4c2f`

Scope: current Tag-73 proof/parser/verifier and sealed proof-account transport.

This is a factual implementation inventory, not a protocol selection or a CU
result. Only costs already present in checked-in phase ledgers are called
measured. Every proposed saving which has not run in SBF is marked as a static
hypothesis. No cryptographic or production source was changed for this audit.

## Baseline fixed by source and evidence

The selected wire is defined in
`crates/aspis-core/src/v7_onefold.rs:26-62` and parsed at
`crates/aspis-core/src/v7_onefold.rs:118-183`.

| Section | Exact maximum bytes | Exact 197-frontier proof bytes |
| --- | ---: | ---: |
| 641 packed QM31 fixed fields | 9,936 | 9,936 |
| two 208-bit roots | 52 | 52 |
| three `u64` work nonces | 24 | 24 |
| q16 records: 403-byte C1 + 186-byte C2 + 32-byte salt | 9,936 | 9,936 |
| two 208-bit frontiers | 10,556 (203 nodes/tree) | 10,244 (197 nodes/tree) |
| **proof body** | **30,504** | **30,192** |
| current `ASPU` header | 40 | 40 |
| **proof account** | **30,544** | **30,232** |

The maximum proof has 216 bytes of headroom below the frozen 30 KiB body
limit. Both the maximum and the 30,192-byte fixture take 32 uploads at the
recorded 960-byte chunk size.

The latest checked-in direct Pool diagnostic transaction, after both the
fixed-width query decoder and the composed relation-weight tail, is 1,254,737
CU. Its measured regions relevant to this audit are:

| Region | CU | Evidence |
| --- | ---: | --- |
| proof-body SHA-256 | 15,597 | `results/v7-pool-nonterminal-cu-profile-20260827/phase-ledger.json` |
| semantic sumcheck | 193,735 | same |
| point claims | 27,039 | same |
| selected Pool terminal | 407,973 | `results/v7-pool-terminal-cu-profile-optimized-20260827/phase-ledger.json` |
| final256 decode and transcript absorption | 79,883 | same |
| query coordinate preparation | 7,660 | same |
| packed q16 decode and gamma combination | 136,824 | nonterminal ledger |
| 32 private-leaf hashes | 11,024 | nonterminal ledger |
| paired two-tree Merkle walk | 94,845 | nonterminal ledger |
| composed structured weight tail | 70,562 | `results/v7-pool-composed-weight-cu-profile-20260827/phase-ledger.json` |
| three final-vector folds | 49,438 | nonterminal ledger |

These diagnostic intervals include their adjacent checkpoint. They are upper
bounds on what a change inside the interval can save, not promised savings.

## Ranked inventory

### 1. Cache the proof-body digest when the account is sealed

**Classification:** noncryptographic lifecycle cache; strongest measured
byte-for-CU candidate.

Current finalization merely overwrites the 32-byte upload authority with zero
(`programs/aspis-verifier/src/lifecycle.rs:156-171`). The Pool verifier later
hashes the complete body and compares it to `ASVQ`
(`programs/aspis-verifier/src/v7_pool_native_dispatch.rs:167-179`). For the
30,192-byte fixture that raw SHA-256 call covers exactly 472 SHA-256
compression blocks and occupies the measured 15,597-CU interval.

A versioned sealed magic can reuse header bytes `[8..40]` for the digest which
finalization computes before irrevocably sealing the account. That costs:

- proof-body bytes: `+0`;
- account-header bytes: `+0` (the authority slot is reused);
- upload chunks: `+0`;
- terminal-transaction work moved to finalization: one 30,192-byte SHA-256 on
  the measured fixture, or 477 blocks at the 30,504-byte maximum;
- measured terminal-transaction ceiling: 15,597 CU, less the new constant-size
  header check. This is not yet a measured net saving.

Required security checks are exact declared-length equality, no trailing
account data, program ownership, upload-authority signature before sealing,
digest computed from precisely `[40..40+declared_len]`, a one-way unsealed to
sealed transition, and no program path capable of changing either body or
cached digest afterwards. The verifier must compare the cached value to the
request binding before proof acceptance. A proof-carried digest inside the
body is not an alternative: validating it would still require hashing the
body.

Formal/source impact:

- replace the zero-authority definition of `proof_account_finalized` at
  `programs/aspis-verifier/src/lifecycle.rs:22-52` with a versioned sealed
  header and prove the lifecycle invariant;
- update the Pool dispatch equality at
  `programs/aspis-verifier/src/v7_pool_native_dispatch.rs:167-179`, the receipt
  finalizer, wallet account constructors, and close-path parsing;
- strengthen `AspisFormal/AspisFormal/Pool/V7Tag73ReadOnlyProfileV1.lean`, where
  body-digest equality is currently a verifier premise, with the seal-time
  cache invariant;
- re-extract the lifecycle/Pool caller and the current ASQ8 caller source
  bridges. Solana account immutability and program ownership remain explicit
  runtime boundaries.

### 2. Use canonical 16-byte QM31 for the 385-field prefix only

**Classification:** proof codec trade; no algebra change; static CU hypothesis.

The first 385 fixed QM31 values comprise the initial claim, 270 semantic
coefficients, 87 point claims, inactive claim, two circle OOD values and 24
relation coefficients (`crates/aspis-core/src/v6_onefold.rs:27-47`). They
occupy 47,740 meaningful bits, rounded to 5,968 bytes when separated. Their
canonical 16-byte encoding is 6,160 bytes: a `+192`-byte body delta.

| Quantity | Current | Candidate |
| --- | ---: | ---: |
| maximum body | 30,504 | 30,696 |
| 30 KiB headroom | 216 | 24 |
| 197-frontier body | 30,192 | 30,384 |
| 960-byte uploads | 32 | 32 |

The candidate removes packed-bit decoding of 1,540 M31 limbs. It also permits
the point-claim record and other already-canonical transcript records to be
absorbed from borrowed proof slices instead of decoding and writing them into
temporary byte vectors. Current decoding and re-encoding are visible at
`crates/aspis-core/src/v6_transcript.rs:353-432` and
`crates/aspis-core/src/v6_transcript.rs:520-543`.

The 193,735-CU semantic and 27,039-CU point-claim intervals are only ceilings:
most semantic cost is polynomial evaluation and SHA transcript work that this
codec does not remove. No SBF saving is claimed.

Security requires four canonical little-endian `u32 < P` limbs per QM31,
exact field order, exact transcript byte equality to today's decoded
canonical records, rejection of all alternate encodings and a new
profile/release binding. The arithmetic terminal and proof equations remain
unchanged.

Formal/source impact is large relative to the byte delta: the deferred parser,
`V6FixedFieldReader`, fixed-field read schedule, transcript source bridge and
K1 parsed-proof binding all change. In particular the generated/read-schedule
work rooted at
`aeneas-verif/v7-tag73-compact-semantic-source-20260825/` and the parser/root
bundles under `aeneas-verif/v7-onefold-accepted-source-20260825/` need new
extractions. The mathematical semantic/relation theorems need only a codec
equivalence theorem if transcript records are proved byte-identical.

### 3. Use canonical 16-byte QM31 for final256 only

**Classification:** proof codec trade; no algebra change; static CU hypothesis.

The final256 contributes exactly 3,968 packed bytes. Encoding the same 256
QM31 values canonically costs 4,096 bytes, a `+128`-byte delta:

| Quantity | Current | Candidate |
| --- | ---: | ---: |
| maximum body | 30,504 | 30,632 |
| 30 KiB headroom | 216 | 88 |
| 197-frontier body | 30,192 | 30,320 |
| 960-byte uploads | 32 | 32 |

This removes packed extraction of 1,024 M31 limbs, a 4,096-byte temporary
encoding allocation, and 4,096 bytes of field-to-byte writes in
`decode_and_absorb_final256`
(`crates/aspis-core/src/v6_transcript.rs:566-583`). The 79,883-CU measured
interval is an upper bound; transcript SHA-256, canonical checks,
materialization for later folds and every fold remain.

Security and formal obligations are the same codec obligations as rank 2.
The final256 hiding/factorization theorem is unaffected at the value level,
but the fixed-field parser/source bridge, exact grammar/profile binding and K1
accepted-proof source model must be revised.

Ranks 2 and 3 are mutually exclusive under the present 216-byte maximum
headroom. Canonicalizing all 641 fixed values would add 320 bytes, producing a
30,824-byte maximum and violating the frozen 30 KiB limit by 104 bytes.

### 4. Carry one checked M31 batch-inverse witness

**Classification:** exact proof hint; `+4` bytes; static CU hypothesis.

Query coordinate preparation derives 32 nonzero M31 denominators and applies
one Montgomery batch inversion
(`crates/aspis-core/src/v6_onefold.rs:822-854`). The implementation performs
one fixed-chain M31 inversion plus the prefix/suffix multiplication schedule
(`crates/aspis-core/src/field.rs:2019-2044`). `M31::inv` is exactly 38 M31
multiplications (`crates/aspis-core/src/field.rs:149-167`).

The prover can carry the canonical inverse of the aggregate product. The
verifier still constructs every transcript-derived denominator, runs the same
prefix/suffix schedule and retains the existing product-equals-one check. The
only removed operation is the 38-multiplication inversion itself.

| Quantity | Candidate delta |
| --- | ---: |
| proof body | +4 bytes |
| maximum body | 30,508 bytes |
| 30 KiB headroom | 212 bytes |
| uploads | unchanged at 32 |
| static arithmetic | one 38-multiplication M31 inverse replaced by canonical decode |
| measured CU | none; entire coordinate interval is only 7,660 CU |

Security requires all 32 denominators to be reconstructed, every zero case to
reject, the hint to be canonical, and the resulting inverse batch to pass an
exact multiplication-equals-one check. Because a nonzero field element has a
unique inverse, a checked canonical hint does not introduce accepted-proof
malleability and need not alter the Fiat-Shamir transcript.

Formal/source impact: add and prove an injected-inverse twin of
`prepare_v6_onefold_coordinates`, then re-extract the V7 accepted-kernel/root
bridge. The current Aeneas production root treats this function as an external
boundary in
`aeneas-verif/v7-onefold-accepted-source-20260825/production-root/generated-exact/V7ProductionRoot/FunsExternal.lean:47-52`;
closing the hint check is an opportunity to reduce that boundary. K1 one-fold
conditioning needs an acceptance-equivalence lemma, not a new soundness term.

### 5. Carry two checked QM31 circle-map inverse witnesses

**Classification:** exact proof hints; `+32` bytes; static CU hypothesis.

The relation prefix samples two secure circle points
(`crates/aspis-core/src/v6_transcript.rs:689-705`). Each accepted rational map
computes `(1+t^2)^{-1}` in QM31
(`crates/aspis-core/src/circle.rs:27-64`). From the checked field kernels, one
QM31 inversion uses 52 M31 multiplications: four for its two CM31 squares, 42
for the CM31 inverse including the 38-multiplication base inverse, and six for
the final two CM31 products. Checking a supplied inverse with one QM31
multiplication costs nine M31 multiplications. Thus the first-try accepted
path has a static net reduction of 43 M31 multiplications per point, 86 total.

| Quantity | Candidate delta |
| --- | ---: |
| proof body | +32 bytes |
| maximum body | 30,536 bytes |
| 30 KiB headroom | 184 bytes |
| uploads | unchanged at 32 |
| measured CU | none; the complete two-point interval is 12,931 CU |

The sampler must first reject subfield parameters and zero denominators, then
consume the unique canonical hint only for the accepted parameter. The exact
retry behavior must be proved equivalent to today's sampler; no hint may
choose the challenge parameter. The verifier must check
`(1+t^2) * hint = 1` before constructing the point. Unabsorbed hints preserve
the current random-oracle schedule and are nonmalleable because the inverse is
unique.

Formal/source impact reaches the circle sampler source bundle, transcript
schedule and K1 causal trace, unlike rank 4's post-query local change. The
existing `challenge_secure_circle_point` extraction and its bounded retry
proof must be regenerated and an exact sampler-equivalence theorem supplied.

Ranks 4 and 5 can coexist for `+36` bytes, a 30,540-byte maximum and 180 bytes
of remaining 30 KiB headroom. That arithmetic is not a recommendation and no
combined CU has been measured.

## Compactness and operation inventory for rejected hints

The current q16 opening path already exposes where proof bytes buy verifier
work. At 197 frontier nodes per tree it performs:

- 2,432 canonical packed-limb decodes;
- 8,384 base-field products in the gamma combination;
- 32 typed private-leaf hashes covering 176 SHA-256 blocks;
- 424 parent hashes, one SHA-256 block each;
- 600 SHA-256 compression blocks in total.

Those counts follow the implementation at
`crates/aspis-core/src/v7_onefold.rs:186-229` and
`crates/aspis-core/src/v7_merkle208.rs:49-128` and match the checked-in
nonterminal phase ledger.

| Proposed hint | Extra bytes | Why it does not save unchanged verification work |
| --- | ---: | --- |
| 16 gamma-combined fibres | 1,024 | Checking equality to the authenticated 26+3 openings still performs all 2,432 decodes and 8,384 products. Trusting them disconnects PCS openings from the relation. |
| 32 private-leaf digests | 832 | Checking them still hashes all 176 leaf blocks. Trusting them disconnects opened values/salts from the Merkle roots. |
| all 424 parent outputs | 11,024 | Checking every parent still performs all 424 parent hashes; omitting checks breaks root authentication. |
| three intermediate final-vector folds (64/16/4 QM31) | 1,344 | Deterministic equality checking repeats the 49,438-CU fold work. A random batch check is a new proof protocol and soundness term. |
| four final structured weights | 64 | Establishing that they are the correct folded accumulator repeats the 70,562-CU work unless a new argument is introduced. |
| selected terminal value | 16 | It is already the proof's terminal claim. Acceptance requires recomputing the 407,973-CU semantic/copy/Poseidon expression. |
| packed q16 indices plus compact counter | at least 37 | The verifier must still derive the challenges and prove every earlier counter failed the cap. Trusting these bytes gives the prover query-selection bias. |
| SHA-256 midstates | implementation-dependent | A verifier cannot know a midstate represents the claimed prefix without hashing that prefix or verifying a separate SHA proof. |

### Hard rejects under the frozen cryptography

1. **Do not trust terminal residual, selector, gamma-dot, folded-weight or
   final-vector hints.** Their defining computation is the security check.
2. **Do not accept a proof-carried compact counter without replaying all prior
   candidates.** The source itself warns about this at
   `crates/aspis-core/src/v6_onefold.rs:459-473`; Tag-73 requires the first
   cap-203 schedule at `crates/aspis-core/src/v7_onefold.rs:73-98`.
3. **Do not trust leaf, parent or SHA midstate hints.** They save hashes only by
   removing authentication.
4. **Do not replace the 16 salts by one public seed as a codec trick.** It saves
   480 bytes but changes the paired-salt hiding experiment and cross-query salt
   correlation. It is cryptographic research, not an equivalent hint.
5. **Do not remove frontier nodes, narrow the 208-bit digest, shorten q16 or
   replace final256 here.** Those are proof-system/security-parameter changes.
6. **Do not add an unsealed decoded sidecar and trust it.** It is safe only if
   seal-time code proves byte-for-byte equality to the canonical proof and the
   lifecycle theorem proves immutability; otherwise it creates a second,
   unauthenticated proof interpretation.

## Codec alternatives which cross the 30 KiB gate

These are useful cost facts but rank below the candidates above because they
break the frozen maximum immediately:

| Alternative | Body delta | Maximum body | 197-frontier body | 960-byte uploads at maximum / fixture |
| --- | ---: | ---: | ---: | ---: |
| canonical `u32` for every fixed limb | +320 | 30,824 | 30,512 | 33 / 32 |
| canonical `u32` for q16 C1/C2 only | +304 | 30,808 | 30,496 | 33 / 32 |
| canonical `u32` for all fixed and q16 limbs | +624 | 31,128 | 30,816 | 33 / 33 |

The query-only variant would replace 2,432 fixed-width packed loads by 2,432
aligned `u32` loads, but the current packed decoder already reduced its phase
by 140,377 CU without changing a byte. Its remaining 136,824-CU interval also
contains all 8,384 gamma products, so a large further saving must not be
inferred from byte alignment alone.

## Source-only comparators

Two current costs do not need proof hints or proof bytes:

- the runtime construction/deduplication of the 64-row inactive schedule at
  `programs/aspis-verifier/src/v7_verifier.rs:77-99` occupied 3,983 CU in the
  diagnostic ledger and can instead consume a frozen generated schedule;
- the structured relation accumulator is a source representation problem,
  not a proof-hint problem. The current composed kernel saved only 754 CU in
  the complete verifier while adding 35,040 SBF bytes. Any further source-only
  change must retain exact equality with `fold_tag73_relation_tail_arity4` at
  `crates/aspis-core/src/sumcheck.rs:1557-1663`.

They are included to prevent a byte-carrying design from receiving credit for
a saving available with zero wire change.

## Audit conclusion

The only high-confidence byte-for-CU transfer backed by a measured interval is
the sealed-header body-digest cache: zero extra bytes and at most the measured
15,597-CU body-hash region moved out of the terminal transaction. The two
inverse-witness families are algebraically exact and cheap in bytes, but their
CU value is bounded by small existing intervals and remains unmeasured. The
canonical-prefix and canonical-final variants have plausible decoder/copy
savings and remain under 30 KiB separately, but each forces a new wire profile
and broad parser/source-proof replay.

Everything else in the current hot path is either already a proof hint (the
Merkle frontier and sumcheck messages), costs essentially the same to check as
to recompute, or changes the cryptographic protocol.
