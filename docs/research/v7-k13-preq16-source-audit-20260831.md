# V7 Tag-73 pre-q16 production-source audit

Date: 2026-08-31
Pinned source revision: `bcd03b12293f2737dfa1da1436092a0a24a6ae24`

## Verdict

The current production source contains an exact control-flow cut at which the
honest prover has fixed the C1/C2 committed data, gamma context, alpha zero,
and final256 before final-work mining and q16 derivation. A second exact cut
exists after the selected final nonce has been absorbed and immediately before
the first q16 candidate hash.

That is **not**, however, the K1.3 adversary-first causal certificate.

The current Rust hash interface is a stateless function pointer. It exposes
neither a shared-oracle history nor whether a call was a first exposure or a
cache hit. The current production verifier sees a completed proof and the
current production prover is only one honest implementation. Translating
either with Aeneas can prove their operation order, but cannot prove that an
arbitrary black-box adversary had fixed the four K1.3 inputs when that
adversary first queried the same raw SHA coordinate.

Therefore:

* **YES:** an honest-prover or verifier-state pre-q16 snapshot is source-real
  and can be exposed by a small behavior-preserving Rust split/hook.
* **NO:** production Rust/Aeneas, as currently shaped, cannot by itself close
  the adversary-first K1.3 causality seam.
* **NO:** the completed `BuiltV7CompactOneFoldProof`, `V6QueryBatchView`, or
  `V6VerifiedTranscript` may be substituted for the missing prefix. They are
  all downstream of q16.

The remaining K1.3 endpoint belongs at the shared lazy-oracle/same-tape
scheduler boundary, or needs a separate causal hash-chain/preimage argument.
It is not a raw parser or final-return source bridge.

## Frozen source files

| File | SHA-256 |
|---|---|
| `crates/aspis-core/src/v6_transcript.rs` | `48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf` |
| `crates/aspis-core/src/transcript.rs` | `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119` |
| `crates/aspis-core/src/v7_onefold.rs` | `6abb0376100611c5553258062480777187785579f402c9c1d3ce72379518258f` |
| `crates/aspis-prover/src/v6_onefold_prover.rs` | `e479317314f4765f046ff4fca88be5c8cf505c027d2226726e1630e9f143bdfd` |
| `crates/aspis-prover/src/pow.rs` | `bf722ae2c8ca6ca9595a559c7827aa12961c8fbcf1e5aec82edd1c8f41df4dea` |
| `programs/aspis-verifier/src/v7_verifier.rs` | `06b6f32cf7a75e0a84ef2d7671eb8a6c3e91a61049414288ff682e801834a951` |
| `programs/aspis-verifier/src/verify.rs` | `819951203e6149d3ca51ebdf65a416492674e5e57e0e21621dff3cf6419bb9ad` |

These files are byte-identical at the later source-closure commit
`91b6863aa2074ecc82d0f91baaacce525b6fd6dc`.

## Exact honest-prover cut

The production Pool entry points
`build_v7_pool_pair_forest_private_transfer_onefold_proof_production` and
`build_v7_pool_pair_forest_withdrawal_onefold_proof_production` call the shared
`build_onefold_proof_with_pow_mode` with `StateOnlyPowMode::Mine` and
`OneFoldBuildProfile::V7Compact`:

* `crates/aspis-prover/src/v6_onefold_prover.rs:942-950`
* `crates/aspis-prover/src/v6_onefold_prover.rs:1821-1851`
* `crates/aspis-prover/src/v6_onefold_prover.rs:1854-1882`

The source fixes the relevant inputs in this order:

1. C1 columns, complete codeword, and C1 tree are built at
   `v6_onefold_prover.rs:1135-1155`; the C1 root is absorbed and lambda/chi
   sampled at `v6_onefold_prover.rs:1156-1169`.
2. C2 messages, complete codeword, and C2 tree are built at
   `v6_onefold_prover.rs:1223-1237`; the C2 root is absorbed before batching
   challenges at `v6_onefold_prover.rs:1238-1248`.
3. The initial claim and semantic fixed fields begin at
   `v6_onefold_prover.rs:1250-1258`.
4. Gamma is sampled at `v6_onefold_prover.rs:1402-1407`, after the batch work
   record, and is immediately used to construct the combined message and
   codeword at `v6_onefold_prover.rs:1409-1418`.
5. Alpha zero is sampled at `v6_onefold_prover.rs:1482-1488`; the message and
   weight folds occur at `v6_onefold_prover.rs:1489-1502`.
6. The exact 256-element folded message is serialized and absorbed as
   final256 at `v6_onefold_prover.rs:1503`.
7. Only then does final-work mining start at
   `v6_onefold_prover.rs:1505-1506`.
8. The selected final nonce is absorbed at `v6_onefold_prover.rs:1507`.
9. Only then is the first-cap-203 q16 forest derived at
   `v6_onefold_prover.rs:1508-1518`.

There are consequently two useful source cuts:

| Cut | Exact location | What is already fixed |
|---|---|---|
| P0: pre-final-work | after line 1503, before line 1505 | committed C1/C2 data and roots, all initial/semantic claims, gamma context, alpha0, final256, pre-final-work transcript state |
| P1: pre-q16 | after line 1507, before line 1508 | everything in P0, plus the selected final nonce and the common post-final-nonce q16 base state |

At P1, every candidate starts by cloning the same base transcript. The sole
counter stream is implemented in
`crates/aspis-core/src/v7_onefold.rs:74-117`.

### Important K1.2 qualification

The full C1/C2 encoded data and trees are fixed before P0. The formal K1.2
`ExtractedWords` object is not a Rust local, however. It is defined from the
actual prover-final shared-oracle history in
`AspisFormal/K1/V7Tag73ExactFixedK12PrefixClassifier.lean:41-53`.

The production honest prover has the committed word sources. It does not have
the proof-relevant `proverFinalOracle.history` value required by K1.2. Roots or
a later set of q16 openings are not a replacement for that history.

## Exact verifier cut

The verifier has the same transcript order in
`crates/aspis-core/src/v6_transcript.rs`:

* gamma and its query powers: `v6_transcript.rs:700-723`;
* relation round zero and alpha0: `v6_transcript.rs:761-776`;
* final256 decode and absorb: `v6_transcript.rs:778-780`;
* final-work check and nonce absorb: `v6_transcript.rs:782-789`;
* q16 derivation: `v6_transcript.rs:790-796`;
* authenticated query callback: `v6_transcript.rs:816-834`.

The selected Tag-73 wrapper supplies `derive_first_v7_compact_queries` at
`v6_transcript.rs:963-1004`. The production caller parses the complete wire
before this execution at
`programs/aspis-verifier/src/v7_verifier.rs:252-279`.

This proves verifier ordering, not prover-query causality. In particular, the
wire having been fixed before the on-chain verifier runs says nothing about
when an off-chain adversary first queried the corresponding random-oracle
coordinate while constructing that wire.

### Existing interfaces are too late or too weak

* `V6RelationDiagnosticPhase::Final256` is only a zero-data enum event, and
  production passes a no-op callback (`v6_transcript.rs:88-125` and
  `v6_transcript.rs:1197-1207`).
* `V6QueryBatchView` is constructed after q16, and selected full-C2 Tag-73
  deliberately sets `final256_coefficients` to `None`
  (`v6_transcript.rs:185-202` and `v6_transcript.rs:818-832`).
* `V6VerifiedTranscript.transcript_state_after_queries` is a post-q16 result
  (`v6_transcript.rs:170-183`).
* `BuiltOneFoldProof` is returned only after q16, query batching, later
  alphas, Merkle frontier construction, and body serialization.

None is a valid pre-query prefix.

## Exact SHA inputs around the cut

The transcript contains only a 32-byte state and a `HashFn`
(`crates/aspis-core/src/transcript.rs:301-312`). The relevant calls are:

1. Final-work predicate:
   `SHA256(state || DOM_GRIND || nonce_le)`, a 41-byte input
   (`transcript.rs:541-545`).
2. Selected final-nonce absorb:
   `SHA256(state || DOM_ABSORB || GRIND_NONCE || nonce_le)`, a 42-byte input
   through the small-record absorb path (`transcript.rs:315-330`).
3. q16 counter absorb:
   `SHA256(state || DOM_ABSORB || V7_QUERY_CANDIDATE || counter)`, the
   unambiguous 35-byte candidate input
   (`v7_onefold.rs:74-81`).
4. Each q16 block then uses the 33-byte squeeze input followed by the 33-byte
   advance input (`transcript.rs:348-357`).

This gives a precise source coordinate for a scheduler-level pause. It does
not label an earlier adversary-origin call to the same 35-byte input.

## Why current Rust cannot evidence adversary-first/cache-hit causality

`HashFn` is exactly:

```rust
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];
```

at `crates/aspis-core/src/transcript.rs:44-45`.

It has no oracle table, actor, logical role, cursor, history, first-exposure
flag, or cache-hit result. The host implementation simply hashes all slices
with `sha2` (`crates/aspis-prover/src/lib.rs:79-89`). The SBF implementation
simply invokes Solana `hashv`
(`programs/aspis-verifier/src/verify.rs:1-18`). A repeated input is recomputed;
no source value distinguishes it from a first call.

The production PoW path makes this boundary even sharper:

* `work_nonce` delegates to `find_grinding_nonce_unpublished`
  (`v6_onefold_prover.rs:727-736`).
* An external miner can perform the search out of process and return only a
  nonce; Rust rechecks one predicate (`pow.rs:115-148`).
* The bundled large-difficulty path hashes in parallel worker threads
  (`pow.rs:158-180` and following).

Thus current production source does not retain the exact ordered final-work
query history either. This is acceptable for proof construction and consensus
verification, but it is not the formal shared lazy-oracle trace.

The current formal source interface accurately reflects that limitation.
`RawTag73SameTapeSource.blackBox` starts an oracle machine whose observable
result is one atomic checked return
(`AspisFormal/K1/V7Tag73RawSameTapeSource.lean:122-149`), and `rawMessages` is
projected from that completed return (`RawSameTapeSource.lean:111-118`). The
desired virtual order alpha0, final256, final work, then q16 appears in
`V7Tag73FutureFreeFullControl.lean:101-128`, but that is the verifier
interpreter's schedule. It does not manufacture an intermediate state of the
arbitrary adversary.

A source hook that calls SHA to “check” the coordinate would be wrong for the
requested theorem: it would create another call and would not preserve the
formal distinction between an existing cache entry and a fresh query.

## Aeneas feasibility and limit

The separately committed accepted current-caller bundle at commit
`91b6863aa2074ecc82d0f91baaacce525b6fd6dc`, under
`aeneas-verif/v7-tag73-current-caller-source-20260830`, already translates the
complete verifier caller, `finish_onefold_relation`, and
`derive_first_v7_compact_queries` at the pinned revision. Its strongest caller
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Consequently Aeneas can feasibly certify a small, ordinary Rust helper that
materializes P0 or P1 from the live verifier locals, and can certify that the
q16 call follows it. The least risky extraction shape is an explicit helper or
function split, not a new closure capturing a large mutable environment.

Such a theorem would establish only:

```text
production verifier reached P1
  -> roots / gamma / alpha0 / final256 are the values used by its later q16
```

It would not establish:

```text
the arbitrary adversary had fixed those values at the first historical
exposure of the same q16 SHA input
```

Translating the honest `build_onefold_proof_with_pow_mode` would not repair
that quantifier mismatch. It would also pull host threading/external-miner
behavior into a source proof without constraining a malicious prover.

## Smallest honest next step

Do not add another parser projection and do not read the final proof return as
an earlier state.

For the K1.3 theorem, keep query execution in the existing shared
lazy-oracle/same-tape scheduler and use a real pause before resolution of the
35-byte q16 candidate input. The scheduler must:

1. retain the exact pre-query `OracleState` and actor;
2. perform the normal table lookup;
3. leave an existing entry as a cache hit, consuming no fresh answer;
4. consume a new answer only on a missing entry;
5. connect the paused program continuation to a proof-relevant prefix that
   already fixes the K1.2 word-source history, gamma context, final256, and
   alpha0.

Step 5 is not supplied by current production Rust. For an arbitrary black-box
adversary it must come from the operational program/continuation model or from
a separate causal hash-chain/preimage reduction. Requiring the adversary to
emit an honest-prover snapshot would silently restrict the adversary class and
is not an acceptable closure.

A production Rust P1 snapshot may still be useful as a source-alignment/KAT
theorem, but it should be treated as supporting evidence after the generic
causal lemma—not as that lemma.

## Classification

**SOURCE-AVAILABLE STATE, SECURITY-ENDPOINT UNAVAILABLE.**

The source has the exact P0/P1 values and order. The missing fact is the
arbitrary-adversary, all-actor, cache-preserving causal lineage. No production
Rust change, Aeneas translation, parser theorem, or final-return projection
alone can supply it.
