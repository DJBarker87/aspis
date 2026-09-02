# V7 first-cap-203 final-nonce cutoff CU measurement — 2026-09-02

## Result

**MEASUREMENT GREEN; RELEASE PROMOTION BLOCKED BY FINAL-NONCE FORMAL
BRIDGE.**

The large CU variation was not a verifier-code regression and it was not a
proof-generation failure. The verifier derives q16 query candidates in order
and accepts the first candidate whose paired binary frontier has at most 203
nodes. Every earlier candidate is reconstructed and rejected on chain. The
measured cost is approximately 3,983 CU per rejected candidate plus 451 CU per
frontier node. The frozen 1,201,757-CU transaction happened to have counter 0;
it was a valid low-cost sample, not the maximum cost of every valid proof.

This branch adds a default-off honest-prover audit policy that publishes only
an ordinary work-valid final nonce whose unchanged first-cap-203 counter is at
or below an explicit cutoff. It also rejects an unpublished nonce when any q16
candidate the verifier would evaluate needs more than the minimum two squeeze
blocks. That second condition removes the rare without-replacement collision
tail from the counter-based CU calibration.

The deployed verifier, Pool, Registry, TxV1 message format, proof bytes,
transcript labels/order, work predicate, relation, query count, frontier cap,
and CPI order are unchanged.

Base revision:
`44602d36d7b10f0a1d97f978fe632863c7ec7e0a`.

Measured implementation revision:
`0a2c37b14ff592ecb9884ac97063eff6e721c7b4`.

Branch:
`research/v7-first-cap203-scan-cu-fix-20260902`.

The exact final documentation/evidence HEAD is reported in the handoff rather
than embedded here, because a commit cannot contain its own hash.

## What changed

The feature `v7-final-nonce-cutoff-audit` is absent from default features and
does nothing unless both of these are supplied:

```text
ASPIS_V7_EXPERIMENTAL_MAX_COMPACT_COUNTER=<0..63>
ASPIS_V7_EXPERIMENTAL_FINAL_NONCE_CUTOFF_ACK=I_ACKNOWLEDGE_MEASUREMENT_ONLY_FINAL_NONCE_SELECTION
```

With the feature and acknowledgement enabled, the prover:

1. finds the minimum final-work nonce at or above the current search cursor;
2. verifies the unchanged 34-bit work predicate;
3. absorbs that nonce using the existing final-work transcript record;
4. derives the existing first-cap-203 q16 schedule;
5. requires the first accepted counter to be at or below the cutoff;
6. requires the first 16 query words to be distinct for every evaluated
   candidate, which is exactly the normal two-squeeze-block path; and
7. if either policy check fails, keeps the nonce unpublished and repeats from
   the next integer.

The returned proof is an ordinary Tag-73 proof. No counter or policy trailer
is added. The unchanged verifier independently checks the work nonce and
derives the same first acceptable q16 schedule. The live proof metadata records
the cutoff, selected counter, minimum-draw requirement, and number of valid
work nonces tested; none of those metadata fields are sent to the verifier.

The earlier authenticated-counter/trailer experiment was explicitly reverted
at `a28c536f752588b57040fa10843d0d58572e2509`. It is not present in the final
tree or measured binary path.

## Cutoff measurement

The current-binary worst-history-shape anchor is a true TxV1, genuine strict
Tag-73, SPL-withdrawal rollover with 255 populated pairs:

| Field | Value |
| --- | ---: |
| Counter | 0 |
| Frontier nodes | 202 |
| Serialized TxV1 bytes | 1,043 |
| Verifier CU | 1,084,738 |
| Total transaction CU | 1,218,972 |
| Pool SHA-256 | `9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d` |
| Verifier SHA-256 | `97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d` |

Two controlled same-verifier comparisons fit:

```text
candidate cost = 3983.010752688172 CU
frontier-node cost = 451.290322580643 CU
maximum fit error on the two comparisons = 1 CU
```

At the maximum 203-node frontier, the calibrated envelope is:

| Inclusive cutoff | Modeled ceiling CU | Fresh-candidate qualification | Expected final-grind multiplier |
| ---: | ---: | ---: | ---: |
| 20 | 1,299,084 | 86.61% | 1.155× |
| 25 | 1,318,999 | 91.70% | 1.090× |
| 27 | 1,326,965 | 93.15% | 1.074× |
| 28 | 1,330,948 | 93.77% | 1.066× |
| 32 | 1,346,880 | 95.76% | 1.044× |
| 33 | 1,350,863 | 96.14% | 1.040× |
| 45 | 1,398,659 | 98.78% | 1.012× |
| 46 | 1,402,642 | 98.89% | 1.011× |

Therefore the largest **calibrated** inclusive cutoffs are 20 below 1.30M,
27 below 1.33M, 32 below 1.35M, and 45 below Solana's 1.40M transaction
limit. Counter 25 is modeled at 1.319M, leaving about 11k CU to 1.33M and 31k
CU to 1.35M. Counter 20 retains the existing 1.30M harness gate, but only by
916 CU at the modeled maximum-frontier rollover point.

These figures are deliberately called a calibrated envelope rather than an
all-reachable theorem. The minimum-draw gate removes the identified q16
collision tail, but a source-level upper bound for every remaining
data-dependent verifier path has not been completed. Exact byte-identical
simulation must remain mandatory, and promotion must wait for that bound or a
documented decision to retain simulation as the runtime admission gate.

## Genuine live finalized measurement

A fresh disposable Agave 4.2.0 cluster activated
`txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` at slot 0. Its genesis hash
was `6f7GtJYeyxSY7aLJAADdEayQ1bYdU3TgbeyVNFC1QZ1H` and runtime feature set was
`565236538`. Only explicitly acknowledged audit identities and disposable
funds were used.

The lifecycle initialized a new eight-lane Pool, deposited a fresh note,
finalized a checkpoint, built the witness from those live accounts, generated
and uploaded a genuine proof, then simulated and submitted the byte-identical
withdrawal transaction.

| Case | Bytes | Simulated CU | Landed CU | Finalized slot |
| --- | ---: | ---: | ---: | ---: |
| Pool initialize | 784 | 131,942 | 131,942 | 151 |
| Deposit | 651 | 638,765 | 638,765 | 183 |
| Checkpoint | 581 | 703,267 | 703,267 | 215 |
| Withdrawal terminal | **1,543** | **1,196,956** | **1,196,956** | **445** |
| Fresh replay rejection | 1,543 | 30,169 | 30,169 | 477 |

The proof was 30,772 bytes, selected counter 9/frontier 202 under cutoff 20,
and took 83,671 ms to generate. The first valid work nonce qualified in this
sample. The focused deterministic selector test separately forces an initial
over-cutoff schedule and proves that the next work-valid nonce is tried.

The terminal signed-wire SHA-256 was
`f1a006bca5fd38658ed00b76c241dc8dffd34b4a91f784f6a5730ebda87fef78`;
the finalized signature was
`4fjNWMRrdbg1dLTYS4W6hSCkPh8v2W9HREAD8JPVDhCvWYHasi5yTA3uhMjWkqPYGyzzmevcbTR5dsvFeQ8B322W`.
The verifier consumed 1,125,340 CU. The vault moved from 1,000 to 750 and the
bound destination from 0 to 250. The fresh replay finalized as rejected with
all protected state unchanged except the payer fee.

The terminal transaction contains the ciphertext-carrier instruction and one
Pool terminal instruction. There is one terminal settlement transaction, not
a preparation-plus-settlement pair. Proof-account upload remains separate
account preparation and is not mislabeled as terminal settlement.

This is local disposable evidence. It is not public testnet, devnet, mainnet,
or production-identity evidence. `mainnetReady` is `false`.

## Security boundary

Nothing has been removed from verifier acceptance. Every published proof still
has all three canonical work witnesses, the exact ASQ8/ASF8/ASR8 binding, the
same proof bytes, and the same verifier replay. The change is solely which
otherwise valid final nonce an honest prover elects to publish.

That publication conditioning is why this remains an audit feature. The
generic first-acceptable-among-N q16 theorem makes the intended argument
plausible, but the real lazy-ROM/final-nonce bridge must cover both the counter
cutoff and the minimum-draw predicate. Until that closure exists, this branch
is not authorization to enable the policy by default or to deploy it.

## Focused validation and resources

Focused local checks passed:

```text
unpublished_range_miner_advances_between_valid_nonces: 1 passed
v7_final_nonce_selector_returns_ordinary_bounded_schedule: passed
v7_final_nonce_selector_retries_an_over_cutoff_first_nonce: passed
default aspis-prover cargo check: passed
feature-enabled prove-from-live-bundle cargo check: passed
```

The final NUC proof-tool build was optimized, offline, and locked: 9.43 s,
514,300 KiB maximum RSS, zero swap. The disposable lifecycle took 196.30 s,
820,628 KiB maximum RSS, zero swap. Both ran with `MemoryMax=12G` and
`MemorySwapMax=0`; neither approached the 12-GiB stop threshold. No SBF binary
was rebuilt.

Machine-readable evidence, exact replay commands, checksums, complete RPC
account images, transaction logs, and resource files are under
`results/v7-first-cap203-scan-cu-fix-20260902/`.

## Remaining blocker

The smallest remaining promotion blocker is precise:

1. close the lazy-ROM/final-nonce theorem for the exact publication predicate
   used here; and
2. either prove an all-reachable current-binary CU upper bound or retain exact
   byte-identical simulation as an explicit release/runtime admission rule.

No production deployment, public transaction, production identity selection,
release signing, verifier/Pool source edit, cryptographic-parameter edit, or
formal-file edit was performed.
