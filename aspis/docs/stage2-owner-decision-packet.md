# Stage 2 owner decision packet

Date: `2026-07-11`

Status: **evidence packet only; no protocol, transport, parameter, or
architecture option is selected by this document.**

This packet puts the currently comparable evidence in one place for a later
project-owner decision. It does not turn a diagnostic into a production proof,
add overlapping measurements, waive an existing threshold, or infer a final
cost from an isolated kernel.

## Evidence map

- [Stage 2 feasibility ledger](../results/stage2/feasibility_decision.json)
- [Reconciled current-CM31 v4 scaffold](../results/stage2/v4_exact_wide_reconciled_g16.json)
- [Exact-wide CM31 diagnostic](../results/stage2/exact_wide_v4_diagnostic.json)
- [Provisional M31 circle-basis probe](../results/stage2/m31_circle_basis_probe.json)
- [M31 host conformance and conjugate audit](../results/stage2/m31_circle_conformance.json)
- [M31 later-line host conformance](../results/stage2/m31_line_fri_conformance.json)
- [M31 candidate encoder and root differential](../results/stage2/m31_circle_candidate_encoder.json)
- [M31 combined fold commitments and terminal tensor](../results/stage2/m31_circle_fold_commitments.json)
- [M31 layer-zero C1/C2 Merkle opening conformance and teeth](../results/stage2/m31_circle_merkle_opening.json)
- [M31 later-line Merkle opening conformance and teeth](../results/stage2/m31_circle_line_merkle_opening.json)
- [Official Stwo full-circle digest anchor](../results/stage2/m31_circle_official_stwo_anchor.json)
- [Verifier-side circle-FRI arithmetic primitives](../results/stage2/m31_circle_fri_core_primitives.json)
- [Fixed per-query circle arithmetic consistency](../results/stage2/m31_circle_query_consistency.json)
- [Still-rejecting fixed prefix and through-gamma transcript teeth](../results/stage2/m31_circle_prefix_candidate.json)
- [Still-unselected full transcript-tail ordering teeth](../results/stage2/m31_circle_transcript_tail_candidate.json)
- [Host prefix-writer/core-parser byte round trip](../results/stage2/m31_circle_prefix_serializer.json)
- [Two-point 102-value statement-block conformance](../results/stage2/m31_circle_statement_evaluations.json)
- [Four-round circle/line relation builder conformance](../results/stage2/m31_circle_relation_builder.json)
- [Sequential causal candidate prefixes](../results/stage2/m31_circle_sequential_candidate_prefix.json)
- [Composed authenticated openings and query arithmetic](../results/stage2/m31_circle_composed_openings.json)
- [Selected fresh-kappa full host PCS candidate](../results/stage2/m31_circle_fresh_kappa_candidate.json)
- [Selected fresh-kappa SBF measurement](../results/stage2/m31_circle_fresh_kappa_sbf.json)
- [M31 representation teeth](../results/stage2/m31_representation_teeth.json)
- [C1 column-basis source audit](stage2-column-basis-audit.md)
- [Production-candidate implementation plan](stage2-m31-production-plan.md)
- [Circle-PCS soundness transport audit](stage2-circle-soundness-transport.md)
- [Two-point MLE batching options](stage2-two-point-batching-options.md)
- [Two-point MLE batching same-build diagnostic](../results/stage2/two_point_batching_probe.json)
- [SolMath ZK extraction record](solmath-zk-candidates.md)
- [Stage 2 feasibility note](stage2-feasibility.md)
- [Soundness note and cryptographic contingency](aspis-soundness-note.md)
- [Theta re-derivation and held q34 profile](stage1-theta-rederivation.md)
- [Current split receipt prototype](../crates/aspis-statement/src/split.rs)

## Measurement-accounting rule

Only an in-place measurement of one concrete execution path can be quoted as
that path's transaction cost. Partial artifacts that contain overlapping work
must not be added, even if one is described as a delta.

In particular:

- do not add the `829,963.25`-CU scalar-C1 v4 scaffold mean to the
  `1,066,396`-CU exact-wide arithmetic/parser diagnostic;
- do not add tag-23 RLC, leaf, or fold rows to a scalar or CM31 verifier total;
- do not revive the historical q36/q34 component projections as product
  totals;
- do not subtract a structural limb-count estimate from a measured verifier;
- if an execution exhausts the `1,400,000`-CU meter, record only the observed
  cap and the lower bound `>= 1,400,001`, unless a separately configured
  diagnostic obtains an exact value without changing the work being priced.

Every candidate must ultimately be measured with its own encoding, transcript,
roots, proof parser, folds, statement semantics, account checks, and corruption
tests under the standard `1,400,000`-CU limit and `262,144`-byte heap frame.

## Current custom-CM31 PCS evidence

The reconciled tag-22 path replaces the scalar layer-zero operation inside the
real PCS verifier flow with the prepared canonical-byte combination of 49 CM31
C1 columns and two QM31 C2 helpers. It retains v4/s2 transcript work,
sumchecks, query derivation, C1/C2 Merkle authentication, all folds, the final
polynomial check, and grinding. Production `VerifyWithClaim` tag 6 rejects the
diagnostic wide flag; only append-only diagnostic tag 22 enables it.

Across eight independent q36/g16 transcripts:

| observation | result |
| --- | ---: |
| unique layer-zero fibers | 34–36 |
| proof bytes | 80,500–85,204 |
| accepted under 1.4M | 0 / 8 |
| compute-meter exhaustion | 8 / 8 |
| required CU per seed | **>= 1,400,001** |
| minimum excess over 1.19M | **>= 210,001 CU** |
| minimum excess over 1.4M | **>= 1 CU** |

The corruption evidence is conclusive rather than cap-laundered: canonical C1
and C2 leaf mutations reject on host and SBF with Merkle errors, and
noncanonical C1/C2 limbs reject on host and SBF with the canonical-value error.
Production tag 6 rejects the flagged proof before performing the diagnostic
work.

This is a structural result for the current custom PCS. It is not a full
payment proof and excludes:

- the second statement point and the final 102 pre-gamma C1/C2 evaluations;
- the randomized `ConstraintId` registry and payment constraint composition;
- final LogUp payment semantics and both total-sum lanes;
- masking/hiding;
- proof-account sealing and any phase receipt;
- the pool, nullifier, and output transition;
- the final q36/g32 profile.

Therefore the tag-22 result does not price a completed payment transaction. It
also does not rule on a different PCS.

### Root-count correction

The current wide C1 commitment has **one layer-zero C1 root**. Each leaf under
that root contains all 49 C1 columns across four slots: `49 * 4 * 8 = 1,568`
bytes. C2 has one separate root over 128-byte leaves. There are not four C1
roots. Later PCS rounds have their own roots and must be covered by a sealed
proof hash or an explicit roots/transcript digest in any receipt design.

## Source-audited M31 circle-PCS candidate

The source audit establishes two facts that must remain together:

1. M31-valued C1 code symbols are valid under a genuine circle-polynomial PCS.
2. Dropping the imaginary CM31 limb from the current ordinary-univariate Aspis
   PCS is not valid.

The audited alternative follows the circle-polynomial structure used by Stwo
at pinned commit
`5d10e6b4baa559766e7bbae133b918121211a9c5`. Moving Aspis to that basis would be
one protocol change containing all of the following:

- circle FFT encoding with mechanically pinned coefficient/bit-reversed order;
- M31 C1 leaves and a new wire discriminator;
- a normalized circle-to-line first fold followed by line folds;
- secure-circle OOD points and circle-basis relation weights;
- new roots, query derivation, offsets, transcript KAT, and corruption vectors;
- a re-derived circle-FRI/S-two soundness transport and T1/T2 ledger.

It is not a serialization-only optimization.

## Tag-23 provisional shape evidence

Tag 23 is an account-backed, standard-heap diagnostic. It does not implement a
circle FFT, OOD relation, statement proof, final polynomial check, or
production verifier. Its currently checked-in rows are useful shape evidence:

| provisional tag-23 row | CU |
| --- | ---: |
| four independent structured QM31-by-M31 dots | 556,596 |
| fused canonical-byte QM31-by-M31 dot4 | 644,816 |
| decoded typed four-slot dot4 | 734,512 |
| one-slot streaming decode plus independent dots | 552,405 |
| exact-49 prepared-limb canonical-byte dot4 | **501,989** |
| empty-leaf hash control | 1,344 |
| 784-byte M31 C1 leaf hash | 1,726 |
| normalized fold, prevalidated coordinates/inverses | 93,284 |
| fold with cached coordinate derivation | 103,981 |
| fold with cached coordinates and batch-inverse syscall | 108,111 |

These rows are not additive to tag 22 or any PCS measurement. The frozen
tag-23 winner is the exact-49 prepared-limb path at **501,989 CU**. It is 54,607
CU (9.8109%) below the same-build structured control and 50,416 CU below the
one-slot streaming path. Both generic sixteen-accumulator four-slot paths lose
on SBF; exact production bounds and one-time weight decomposition reverse that
result. All five prior RLC implementations plus the new specialization produce the
same host sink; noncanonical C1 inputs reject on host and SBF for the winning,
typed-fused, and original fused-byte paths. The candidate remains a diagnostic
shape, not a PCS or product total. Its protocol-neutral streaming M31 dot,
normalized first fold, and checked/prevalidated batch-inversion APIs are frozen
in the separate SolMath repository at commit `dabc471`; that extraction does
not select the Aspis PCS.

## Two-point MLE batching diagnostic

Append-only tag 25 compares the three unselected two-point binding candidates
against an explicitly insecure one-point cost baseline on one identical
relation fixture. Every row absorbs the same two ten-coordinate points and the
same 102 canonical values before gamma, checks four degree-six relation rounds,
folds verifier weights, and executes the terminal dot. Only fresh-kappa adds an
extra transcript squeeze; independent lanes alone duplicate the relation
messages. Five local-validator repetitions are identical in each row, use the
default heap, and agree with the pinned host sink.

| isolated tag-25 mode | CU | delta vs insecure baseline | relation bytes | transcript hashes |
| --- | ---: | ---: | ---: | ---: |
| one-point baseline | 51,052 | 0 | 448 | 19 |
| fresh kappa, one lane | 68,380 | +17,328 | 448 | 21 |
| two independent lanes | 92,923 | +41,871 | 896 | 23 |
| disjoint gamma powers, one lane | 70,981 | +19,929 | 448 | 19 |

The paired cancellation, challenge-order, lane-omission, and gamma-shift teeth
demonstrate weakened acceptance and canonical rejection. These rows are a
same-build isolated relation-kernel comparison. They exclude the proof roots,
Merkle openings, circle encoding, query work, statement composition, hiding,
payment semantics, and pool transition; they are not additive to another
artifact and do not select a rule or update a product projection.

## Conformance gate before any M31 production integration

The following evidence is required before an M31 result can be promoted from
shape probe to PCS candidate:

| conformance item | status/value |
| --- | --- |
| actual 49-column `SpendTraceV4` circle FFT matches pinned Stwo basis/order | `HOST PASS: direct MLE message coefficients, official vectors at 5d10e6b4` |
| normalized first fold matches coefficient fold for tested fibers | `HOST PASS: p/Jp/Ap/JAp, alpha then alpha^2` |
| secure-circle OOD relation and two-sample transcript agree end to end | `CORE MATH PASS: non-panicking rational point, [...,pi(x),x,y] tensor, circle-to-line tail, two-sample fixture; complete production C1/C2 absorption pending` |
| later line-FRI coefficient/evaluation/query order matches pinned Stwo | `HOST PASS: 48 cases, 108 radix-4 rounds, explicit bitreverse bridge and raw 4^r scale; Merkle/transcript/SBF integration pending` |
| fixed-profile verifier domain/fold/query/final-tensor primitives match official/raw anchors | `HOST PASS: exhaustive 4096 circle points, 1360 line points, 1360 factor4 folds, 1024 query/final paths; explicit bounds/zero-denominator errors; authenticated integration/SBF pending` |
| fixed C1/C2 and later-leaf arithmetic query chain | `HOST PASS: all 1024 q paths canonically decode powers 0..50, match layers 1/2/3 at q>>2/4/6, and reach the natural final4 tensor; 7 same-input gamma-shift/query-map/alpha-reuse/final-order teeth reject canonically. Leaves are caller-supplied; Merkle composition, tag 24, KAT, and SBF remain open` |
| fixed candidate prefix, canonical fields, and pre-batching transcript order | `HOST PASS, STILL REJECTING: exact 2,456-byte zero-copy prefix, all 142 QM31 fields, labels 11..19, C1/C2 roots, external z/xor11(z), and all 102 values through gamma; 8 paired early/partial/root/C2 weakened schedules differ canonically; no KAT, batching rule, openings, or acceptance` |
| selected complete candidate transcript/relation | `HOST PASS: fresh kappa now builds encoding/roots, statement claims, OOD/sumcheck/folds, final/grinding/q36 in order and independently validates the relation; disjoint-gamma51 is comparison provenance only` |
| selected composed authenticated proof | `HOST PASS: exact 57,668-byte fresh-kappa proof SHA256 68a53608...50505ca joins transcript-derived challenges to layer-zero/later authentication and all query arithmetic; matching SBF PCS row is below` |
| selected full PCS on SBF | `PASS 5/5: tag 26 accepts at 1,112,605 CU under 1.4M/262,144; stale statement rejects; +287,395 vs platform cap, +77,395 vs project threshold. Fixture C2/payment/hiding/transition excluded` |
| fixed-rate Johnson query target | `FAIL: literal rho=1/4 q74/g32 reconciles to 1,873,746 CU; monolithic run exhausts at 1.4M` |
| low-rate Johnson query target | `PASS 5/5: literal rho=1/16 q36/g32 tag 28 accepts directly at 1,237,877 CU; +162,123 vs platform cap; 73,620-byte proof; query term 101.466 bits only` |

The selected row is already overlap-subtracted by literal in-place execution.
Its 501,989-CU RLC seam is included; adding it again to obtain 1,614,594 CU is
forbidden by the ledger rule.
| all 49 C1 + two C2 direct messages, exact leaves, and layer-zero roots match independent host references | `HOST PASS: every 49x4096 M31 and 2x4096 QM31 symbol, all 1024 leaves, both radix-4 roots; official Stwo roots c6a93117...ad4f / c764cdff...30b3; production proof/transcript/SBF pending` |
| representation bug classes demonstrate weakened acceptance and canonical rejection | `HOST PASS: 8 encoding/fold pairs, 8 fixed-prefix pairs, and 9 full-tail ordering pairs; authenticated composition, exceptional sampler failure paths, and the selected-two-point production family remain` |
| late gamma recombination commutes with separately encoded C1 columns | `HOST PASS through encoding, first fold, and OOD; C2/production wiring pending` |
| new version/basis discriminator and transcript KAT pinned with teeth | `FRAMING/PREFIX PASS: exact flag 0x08/word 0x0b, append-only tag 24, labels 11..19, and through-gamma ordering teeth. Tag 24 and production remain rejecting; candidate fixture 95ca0bc...15d588 remains non-production; no expected transcript digest was pinned and the downstream KAT remains pending` |
| circle-FRI/S-two soundness transport and finite-length ledger updated | `AUDITED OPEN: exact L'_10 subcode/Johnson code facts identified; grouped folds, two-phase batching, MLE binding, actual OOD denominator, BCS accounting, extension constants and finite-n remainder remain unproved` |
| in-place q36/g16 verifier, at least eight seeds | `PENDING` |
| selected final q36/g32 measurement | `PENDING OWNER SELECTION AND INTEGRATION` |

The host tests also pin why no AIR interpolation occurs: Aspis commits a
multilinear message table, so the 1,024 trace coordinates enter the
low-degree encoder directly, matching the existing substrate's message/MLE
contract. No one-transaction M31 total exists until the production rows close.
The diagnostic headroom in tag 23 is not product headroom.

The later-line result is an order/normalization constraint, not a CU result.
Stwo's line polynomial storage is bit-reversed; two raw folds at `alpha` and
`alpha^2` carry a factor of four relative to Aspis's normalized adjacent
radix-4 relation fold. The production path must either preserve that factor
explicitly or normalize it consistently in the proof and relation claims. It
may not silently mix the two conventions.

## Option evidence: one verification transaction

This option means one transaction contains the complete payment statement,
PCS, hiding checks, and atomic pool transition.

Evidence currently available:

- the current custom-CM31 exact-wide scaffold alone exceeds the absolute cap
  in all eight reconciled runs while still excluding payment work;
- the genuine-circle M31 candidate has structural and provisional kernel
  evidence, but no conforming integrated verifier or full-transaction total;
- the randomized `ConstraintId` registry, final `T8 = (J+2)/|F|`, 102-value
  framing, hiding, and pool transition remain unfinished.

Evidence still required for this option:

1. close every M31 conformance placeholder above;
2. freeze the final statement registry, two-point transcript schedule, hiding
   mechanism, and economic public inputs;
3. integrate those components into one production instruction rather than
   adding probes;
4. run at least eight production-envelope measurements plus the final g32
   profile;
5. demonstrate economic, transcript-order, proof-mutation, Merkle, OOD,
   malformed-field, hiding, nullifier, output, and failed-transition teeth;
6. report both the 1.19M project threshold and 1.4M execution-cap outcomes
   without silently changing either rule.

This packet neither selects nor rejects a future conforming M31
one-transaction implementation.

## Option evidence: secure transport split

Transaction splitting is a transport/product choice. It does not change the
cryptographic security regime or turn a conjectured bound into a proven one.
The current [split prototype](../crates/aspis-statement/src/split.rs) is an
in-memory state machine, not an on-chain receipt: verifier success, authority,
slot, hashes, and roots are caller-supplied values.

A minimum secure split experiment requires:

- a new versioned proof account, separate from mutable legacy `ASPU` accounts;
- a one-shot lifecycle `Uninitialized -> Uploading -> Sealed -> Closed/Aborted`;
- sequential, complete uploads with no overlap, holes, reset, or post-seal
  writes;
- an on-chain domain-separated hash of the exact proof account, length, program,
  and session;
- read-only sealed proof accounts during verification;
- canonical session/proof/receipt PDAs with owner, seeds, bump, protocol epoch,
  parameter digest, proof version, basis, q/g/s, and expiry from `Clock`;
- binding to the proof hash, statement digest, **one wide C1 root**, one C2
  root, later-roots/transcript digest, 102-value digest, gamma and both combined
  claims, queries/unique fibers, prior-phase digest, and every economic public
  input;
- state transitions written only after actual verifier success, never from a
  boolean;
- final receipt consumption and the canonical pool/nullifier/output CPI in one
  atomic instruction, including failed-CPI rollback and concurrent-finalization
  teeth.

The transaction count is intentionally written as **N**, not assumed to be
two, three, or four. Candidate phase cuts must be measured as real
receipt-writing instructions:

1. after transcript/statement verification and `QueriesReady`;
2. after layer-zero C1/C2 authentication;
3. after exact-wide combination and the layer-zero fold;
4. after the PCS tail, immediately before/with atomic pool consumption.

The owner packet should compare measured groupings of those cuts. Each phase
must include sealing/PDA/hash/sysvar/account-write costs and report its own
1.19M/1.4M result. Old one-transaction probes cannot be divided or added to
price the split.

Split-specific required teeth include proof mutation after seal, reset/length
attacks, missing or overlapping chunks, phase reordering, phase duplication,
receipt/proof/statement/pool mix-and-match, swapped evaluation points or lanes,
gamma-power errors, expiry, replay, close/abort races, concurrent finalization,
and failed CPI rollback.

This packet does not adopt split verification or choose N.

## Option evidence: proven-regime cryptographic retreat

The proven-regime path is a cryptographic parameter/security choice, not a
transaction-transport fallback. The pre-registered terminal retreat uses
Johnson-proven accounting; the current record describes approximately 67–68
proven bits after the pending re-pin, while 65.5 remains the only quotable
floor until its derivation section closes.

Selecting this path would require its own parameter set, proof bytes, KAT,
soundness ledger, CU measurements, and stated security claim. If it also needs
multiple transactions, receipt-bound transport is priced separately. A split
transaction does not make the current conjectured regime proven, and a
proven-regime parameter change does not by itself select one-transaction or
split transport.

No cryptographic retreat is selected here.

## Held protocol lever: q34/g36/s2

q34/g36/s2 remains held for one-knob discipline. Its recorded `0.3494`-bit
provisional gain and `44,479`-CU saving belong to the retired component model,
not the exact-wide CM31 verifier or an M31 circle PCS. It requires a deliberate
transcript/profile change, KAT re-pin, fresh soundness calculation, and
in-place repricing under the eventually selected PCS.

This packet does not substitute q34 for q36.

## Owner decision fields

The fields below are intentionally unfilled until the evidence placeholders
above close.

| decision field | owner entry |
| --- | --- |
| evidence freeze commit | `TBD` |
| final tag-23 winning RLC mode/CU | `measured: exact-49 prepared-limb canonical-byte dot4, 501,989 CU; owner acknowledgment TBD` |
| M31 conformance gate | `TBD: pass / fail / incomplete` |
| final `ConstraintId` count J and T8 | `TBD` |
| selected cryptographic regime | `TBD: rho=1/16 Johnson candidate; T1/per-fold-PoW/BCS derivation still open` |
| selected PCS/basis | `genuine-circle M31 engineering target; production approval waits on transport/SBF gates` |
| selected two-point MLE binding | `fresh kappa, one lane; ruled 2026-07-12; 51/|QM31| charged to T5'` |
| selected transport | `one transaction low-rate candidate; receipt-bound N=2 remains fallback` |
| selected q/g/s profile | `candidate: rho=1/16, q36/g32/s2; not production-selected until full soundness ledger closes` |
| applicable transaction count N | `TBD; do not assume` |
| treatment of 1.19M project threshold | `TBD: retain / explicitly amend with reason` |
| treatment of 1.4M execution cap | `fixed platform limit unless platform evidence changes` |
| required pre-implementation conditions | `TBD` |
| owner and decision date | `TBD` |

## Current packet outcome

**The engineering direction is now the one-transaction rate-1/16 M31 candidate
with fresh-kappa one-lane binding. The direct PCS fits at 1,237,877 CU, but this
is not production approval: rho=1/16 T1/per-fold-PoW/BCS, payment composition,
hiding, transition, and exact transport remain open. Receipt-bound N=2 remains
the measured fallback.**
