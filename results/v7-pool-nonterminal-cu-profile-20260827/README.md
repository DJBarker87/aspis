# V7 Pool nonterminal CU audit (2026-08-27)

## Result

One exact fixed-width packed-field optimization reduced the direct native
Tag-73 verifier from 1,395,868 CU to **1,255,491 CU** on the identical honest
30,192-byte proof.  The transaction accepted in simulation and execution with
byte-identical metadata and **144,509 CU of headroom**.

The complete 140,377-CU saving occurs inside the fused query-opening phase:

```text
fused query openings before: 383,343 CU
profiled query openings now: 242,966 CU
saving:                      140,377 CU
```

The optimized kernel decodes each exact 31-byte group of eight 31-bit limbs
with fixed-width little-endian loads.  The former sequential reader refilled
its bit buffer one byte at a time.  Proof bytes, limb order, canonical `P`
rejection, gamma powers, field products, typed SHA-256 leaves, Merkle roots,
transcript and all relation checks are unchanged.

## The original 987,895 nonterminal CU

The previous accepted diagnostic transaction consumed 1,395,868 CU, of which
407,973 CU was the Pool terminal.  Its remaining **987,895 CU** decomposes
exactly as follows:

| Region | CU |
| --- | ---: |
| Compute Budget instruction | 150 |
| entry through terminal start | 254,292 |
| relation setup through query coordinates | 173,450 |
| fused query authentication and gamma combination | 383,343 |
| post-authentication relation tail | 176,660 |
| **nonterminal total** | **987,895** |

The first region includes the request/envelope hashes (3,309), proof-body hash
(15,597), parse (296), runtime inactive schedule (3,983), transcript setup
(9,566), semantic sumcheck (193,735), point claims (27,039), entry (491) and
the terminal-start checkpoint (276).  The 173,450-CU relation prefix includes
the two diagnostic boundary checkpoints; its substantive phases remain the
172,912 CU in the prior ledger.

After this optimization the terminal remains 407,973 CU and the nonterminal
transaction cost is **847,518 CU**.

## Source-derived opening inventory

For each of 16 queries the verifier consumes 104 packed C1 limbs and 48 packed
C2 limbs.  The gamma dot therefore canonically decodes 2,432 limbs and retains
exactly:

- 6,656 C1 base-field products;
- 1,728 C2 helper base-field products;
- 2,624 M31 reductions across the C1 and C2 lazy accumulators.

The old decoder executed 9,424 byte-refill loop iterations across q16.  The
new decoder uses 2,432 fixed-width loads, one per output limb, grouped into
304 exact 31-byte chunks.  Equality tests compare the optimized gamma result
against the unpacked reference and cover every C1 limb position containing
the forbidden canonical boundary `P`.

Authentication itself cannot be removed or merged cryptographically.  The
preserved proof has 197 frontier nodes per tree.  A 16-leaf minimal subtree
therefore performs `197 + 16 - 1 = 212` parent hashes per tree, or 424 total.
Together with 32 typed private-leaf hashes, this fixes 456 SHA-256 calls and
600 compression blocks:

- C1 leaf input: 437 bytes, seven SHA-256 blocks, 16 leaves;
- C2 leaf input: 220 bytes, four SHA-256 blocks, 16 leaves;
- parent input: 53 bytes, one SHA-256 block, 424 parents.

The changed diagnostic splits the optimized 242,966-CU opening phase into:

| Opening subphase | CU |
| --- | ---: |
| fixed-width decode and exact gamma combination | 136,824 |
| 32 typed private-leaf hashes | 11,024 |
| paired-topology two-root Merkle walk | 94,845 |
| outer completion checkpoint | 273 |

The checkpoint cost is included in each preceding row.  The diagnostic twin
makes a second cheap pass over the 16 record descriptors solely to separate
gamma arithmetic from leaf hashing; production keeps the existing fused
one-pass wrapper.

## Exact post-authentication tail

The **176,660-CU** tail was byte-for-byte unchanged:

| Phase | CU |
| --- | ---: |
| circle-to-line query fold | 20,807 |
| install shifted q16 claim | 10,652 |
| round-one polynomial / weights / values | 3,135 / 25,859 / 36,453 |
| round-two polynomial / weights / values | 3,128 / 25,475 / 9,820 |
| round-three polynomial / weights / values | 3,128 / 19,999 / 3,165 |
| final relation dot | 13,994 |
| completion checkpoint and exit | 994 / 51 |

The three structured weight folds cost 71,333 CU; the three final-vector folds
cost 49,438 CU.  The value folds already use the exact lazy affine
three-product kernel and have essentially minimal product count.  The next
noncryptographic candidate is a composed three-round representation for the
structured weight accumulator, especially its 16-line M31 batch and deferred
binary mask.  The challenges can be collected before folding because weights
do not drive the transcript or intermediate running claim.  A direct kernel
must be proved identical to the current three sequential dual folds and must
preserve the round-one multilinear merge.

## Can nonterminal work save 180k without changing cryptography?

Not from Merkle traversal alone.  Its 600 SHA-256 blocks are fixed by the
current proof and roots.  The paired implementation already shares topology,
scratch allocation and index walking while keeping the two typed hashes
independent.

A credible unchanged-cryptography bundle now exists, but only 140,377 CU is
measured:

1. fixed-width packed gamma decoder: **140,377 CU measured**;
2. freeze the eight-entry inactive-mask schedule: up to 3,983 CU in the
   diagnostic ledger;
3. compose the three structured weight folds: target at least 35,640 CU from
   their measured 71,333-CU budget.

That reaches the requested 180k target without changing proof bytes, SHA-256,
Merkle topology or field equations.  Item 3 is plausible because the same 16
line tensors and deferred mask are traversed three times today, but it is not
yet a measured saving and should not be booked as headroom.  In-place Merkle
scratch and contiguous C2 leaf hashing are smaller follow-ups; neither can
honestly supply a six-figure saving because all 456 digest calls remain.

## Verification and provenance

- parent evidence commit: `f5f4ac2c8abcbb56902ae7d5131f265d589c9ec3`;
- proof: 30,192 bytes, SHA-256
  `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c`;
- SBF: 876,240 bytes, SHA-256
  `6b76c1368f61ffac9b2228222ec4a83bc1209ad088a101ff32103c8dc8b883f7`;
- focused SBF build: 16.31 seconds, 654,671,872-byte peak RSS, zero
  swap; no final stack-offset or frame-clobber diagnostic;
- focused host tests passed:
  `packed_26_plus_3_combination_matches_unpacked_reference` and
  `eight_aligned_decoder_matches_literal_packing_and_rejects_p`;
- simulation and execution both accepted at 1,255,491 CU with identical
  metadata;
- exactly one changed LiteSVM diagnostic transaction; no network, RPC,
  deploy, or submission.

The first instrumented link exposed a 5,440-byte inlined caller frame.  No
transaction used that artifact.  Explicit non-inlining boundaries isolated
the fixed arrays; the rebuilt artifact linked without an SBF stack warning and
was the sole binary executed.
