# Atomic state-only v3 copy/terminal registry

Date: 2026-07-13

Status: **the actual atomic trace, generated rank-74 routing reference,
shared-selector runtime helper, regenerated masking,
three-point terminal, complete prover, and read-only SBF verifier are
integrated. The atomic complete-view hiding-rank repin, mined PoW, and live
account mutation remain gates.** The implementation does not reuse the old
102-link terminal constants.

## Retired non-integrable draft

The earlier `m=143`, rank-120 draft with fingerprint
`0x1219d71ee84d1269` is retired. It balanced on Boolean traces, but routed an
output-path bit from a different row. Evaluating that virtual endpoint at an
off-domain sumcheck point requires a predecessor opening (and a composed
sibling transform), outside the frozen `(z,succ(z),xor12(z))` PCS view. That
fingerprint is not live anywhere in code or results.

## Correct local wiring

The corrected allocator places three independent nine-cell components per
level: input `(bit,current)`, output `(bit,current)`, and one shared
`(bit,sibling)`. It allocates only cells not used by retained non-path state,
and only rows whose retained endpoint arity leaves room for the exact new
two-producer/two-consumer LogUp shape.

For each input/output path and level the registry adds:

- one current link from the preceding final row (`block 3` or `48` at level
  zero, then the preceding path block);
- two same-tag selection terms implementing
  `{(b,current),(1-b,sibling)} = {(0,left),(1,right)}`;
- two per-level aliases `input_bit -> output_bit -> shared_sibling_bit`.

Both path blocks therefore use exactly the same witness sibling and bit. Every
tuple cell is on its endpoint row. The terminal compiler proves this by
enumerating all 366 endpoints; no routed limb exists. The complete statement
still uses exactly `z`, `succ(z)`, and `xor12(z)`.

The public roots remain block 23 for the current anchor and block 43 for the
output anchor, with independent public-binding teeth.

## Exact recount

| object | atomic v3 |
| --- | ---: |
| retained non-path links | 23 |
| current links | 40 |
| same-tag selection terms | 80 |
| bit-alias links | 40 |
| total copy terms `m` | 183 |
| unique tag groups | 143 |
| copy-active / inactive rows | 210 / 814 |
| active-row rectangles | 6 |
| maximum producers / consumers per row | 2 / 2 |
| tuple patterns | 15 |
| generated minimum tensor-routing rank | 74 |
| selected integrated routing rank | 103, sharing semantic selectors |
| unique left / right factors | 60 / 18 |
| shared outer-product pairs | 61 |
| routing destinations | 74 |
| factor entries | 798 |
| auxiliary cells used / capacity | 629 / 1,280 |
| auxiliary row high-water | 68 / 80 |
| base / packed base semantic lanes | 77 / 20 |
| randomized semantic lanes | 21 |
| Poseidon lanes | 4 |
| theta lanes / collision degree | 25 / 24 |
| zerocheck individual degree | 27 |
| terminal points | 3 |
| selected PCS-width candidate | 28 |

Live registry/configuration fingerprint:
`0xa5249dda67f75888`.

Live active-row fingerprint:
`0xfc90f89be110b6f5`.

The old Merkle semantic branch had 17 lanes (one bitness and sixteen ordered
child residuals). The same-tag two-item copy multiset now enforces those
relations, including Booleanity up to the ordinary tagged-tuple compression
collision event. Removing those 17 lanes changes 94 base lanes to 77, which
pack into 20 QM31 lanes. The copy lane gives 21 randomized semantic lanes;
four Poseidon lanes give 25 theta lanes and degree 24. The composed two-round
Poseidon branch still dominates at degree 27.

## Generated compiler and guards

`generate_atomic_state_only_terminal_constants.rs` derives, from the host
registry:

- all 183 link endpoints and 15 affine tuple patterns;
- the rank-74 high/low factorization and 61 shared outer products;
- the six active-row rectangles, exact 210-row list, and active fingerprint;
- the registry fingerprint compiled into the constants file.

The factorization uses row bits `5..0` for its 64-entry factor and bits `9..6`
for its 16-entry factor (`low-mask = 0x03c0`).  The derivation tool
`search_atomic_state_only_routing_partition.rs` exhaustively checks every
3-through-7-bit partition.  This repartition changes no row, link, tag,
tuple, challenge, or polynomial; it only changes the exact tensor basis.

`atomic_state_only_terminal.rs` consumes only registry-derived constants at
runtime. The generated rank-74 tensor remains the independent minimum-rank
reference. The integrated terminal selects the exact legacy rank-103 row
partition because its `(bits 9..4, bits 3..0)` tensor is identical to the
semantic selector tensor already required by the terminal; reusing it is
9,782 CU cheaper end-to-end than expanding a second, lower-rank tensor. Its
tests cover:

- generated-vs-host parity for every link, tag, endpoint row, slot, and
  pattern;
- compiled rank-74 routing versus the direct 183-link walk at 64 fresh random
  QM31 points;
- the shared semantic tensor versus the selected rank-103 partition at 64
  fresh random QM31 points;
- the compiled copy lane versus an independent direct evaluator at 64 fresh
  random QM31 points;
- all 16 opened C1 corruption teeth plus independent `h1`, `lambda`, and `chi`
  teeth;
- exact active/inactive membership for all 1,024 rows and random off-domain
  equality of the six-rectangle active selector;
- exact registry/config and active-row fingerprints.

The host suites are green: terminal 7/7, registry 7/7, trace 7/7.

Append-only SBF tag 42 measures the complete isolated copy lane at 187,959 CU
for the rank-103 partition and 166,581 CU for the exact rank-74 partition,
five identical runs each: an isolated saving of **21,378 CU**. The integrated
choice differs because tag 42 deliberately does not price the reusable
semantic selector tensor. The artifact is
`results/stage2/atomic_routing_partition_probe.json`.  This is not integrated
verifier CU.

### Why the 40 bit aliases remain

Within the current row-local tagged-tuple construction, each selected digest
needs eight digest cells plus one selector-bit cell on the same row.  A level
has three independently addressed components: input current, output current,
and the one shared sibling.  Even if two components share the bit cell, they
need `8 + 8 + 1 = 17` physical cells and therefore cannot share a 16-cell
row.  Three row-local bit copies need at least two equality edges to form one
connected alias class.  Over 20 levels, the current 40 bit-alias links are
therefore minimal unless the protocol adds a point transform or moves the
selection equations out of the copy argument.  Either change alters terminal
points or semantic lanes and must be measured as a separate construction.

## Hiding ruling

The relation still adds no committed C1 column, so the selected
`16 semantic + 10 mask-only + 2 C2` shape remains width 28. Active rows change
from 170 to 210, so the implementation derives a new 5,262-cell relation-free
mask inventory and removes every endpoint of the 183 atomic affine copy
terms. The actual prover uses that inventory and pins:

- relation-free mask fingerprint `0x0fdabd401816cc99`;
- copy-active-row fingerprint `0xfc90f89be110b6f5`;
- layout/factor fingerprint `0x9e4d2fcd4cf9fe01`.

Those pins prevent accidental reuse of the old layout. The exact atomic proof
has now been replayed through the rank gate. Baseline PCS rank is 712/780 M31
with valid-witness containment; adjoining the selected external switch closes
780/780, supplied by 64 later-query pivots and four relation pivots. The switch
has 70 QM31 variables, 52 public-observation rank, an 18-dimensional
conditioned kernel, q-randomness/q-coopening rank 16/16, and U rank 35/35.

This is still not a production HVZK claim. The rank artifact deliberately sets
`production_geometry_full_view_closes=false`: its raw 292-node frontier is a
retired one-value depth-17 diagnostic, whereas production packs four line
values per leaf at depth 15. The packed X/F commitment, translated W1 root,
fused literal `Enc(U)(q16)` evaluator, W0/W1 relation splice, and ROM/HVZK
simulator are not yet acceptance-integrated. See
`results/stage2/atomic_state_only_hiding_rank.json`.

## Actual proof and literal SBF acceptance

The host prover now constructs the exact atomic-v3 trace, masks it with the
atomic inventory, builds the exact 183-link copy helper and atomic degree-27
zerocheck, commits the complete profile-20 PCS, and produces a 56,044-byte
proof. The verifier derives the atomic statement digest internally and binds
pool key, pool revision, current anchor, nullifier, output commitment,
replacement root, asset, and fee.

Append-only tag 46 verifies that proof's own transcript-bound masked terminal,
relation, Merkle openings, and every q16 query. It accepts no writable account
and cannot mutate pool state. The literal validator-2.3.0 simulation is:

| bucket | CU |
| --- | ---: |
| setup and public decode | 1,549 |
| proof load | 484 |
| parse | 1,804 |
| transcript | 151,952 |
| atomic terminal | 384,716 |
| relation | 183,481 |
| Merkle openings | 185,774 |
| q16 arithmetic | 269,366 |
| verifier return | 266 |
| post-marker | 59 |
| **literal total** | **1,179,451** |

The sum is exact and leaves 220,549 CU under the 1.4M ceiling. No segmented
phase, overlap subtraction, or cross-artifact substitution appears in this
number. The fixture's SHA-256 is
`fdd1097f702b411b6bcd26d0e195322d7683ff93ec4cb70828b9459fe7cef007`.
All eight public-field mutations and eight proof corruptions reject on host;
a changed pool revision also rejects on SBF.

The terminal carries thirteen internal CU boundaries. They identified the
generic fifteen-pattern tuple evaluator as the largest atomic-only excess:
82,582 CU versus the baseline's 19,425 CU. Five shared eight-limb dot products
now reconstruct all fifteen patterns, routing products use exact lazy M31
reduction, and the selected rank-103 routing basis reuses the semantic selector
tensor. The final pattern/prepared/routing phases are 21,328 / 35,501 / 107,910
CU. The progression is 1,279,180 pre-rewrite, 1,217,906 after pattern sharing,
1,189,233 with rank-74 lazy routing, and **1,179,451** with shared selectors:
an exact overall saving of **99,729 CU**. Generated/reference identities,
the independent 183-link walk, and all sixteen C1 plus `h1`, `lambda`, and
`chi` teeth remain green. This changes neither proof bytes nor Fiat--Shamir.

The fixture deliberately uses an unmined nonce. Tag 46's diagnostic mode
absorbs that nonce and runs every downstream Fiat--Shamir operation while
bypassing only the PoW acceptance predicate. The production verifier rejects
the fixture. Therefore this is acceptance-complete read-only verifier evidence,
not a production mined transaction or an authorization to enable mutation.

## Measured account-transition closure

The same verifier core is now wrapped by the exact pool/nullifier kernel. A
program-owned zeroed marker measures **1,189,180 CU** and the canonical
zero-lamport System-owned `create_account` path measures **1,191,513 CU**.
Relative to tag 46, mutation costs 9,729 and 12,062 CU respectively. Account
validation, statement digest, proof verification, marker/CPI, recheck, write,
and post-marker buckets reconcile exactly in both artifacts.

Corrupt-proof rollback, duplicate rejection, exact post-state images, and a
two-signer same-pool/same-nullifier race are green; the concurrent path commits
exactly once. Default tag 47 remains fail-closed because the packed production
complete-view hiding proof is not closed. Its nondefault production candidate
has no diagnostic flag and rejects the unmined fixture at PoW before any CPI
or write. Tag 48's bypassing path exists only in a nondefault local-validator
measurement build.

See `docs/stage2-atomic-state-only-profile20-mutation.md` and
`results/stage2/atomic_state_only_profile20_mutation.json`.

Primary artifact:
`results/stage2/atomic_state_only_profile20_acceptance.json`.
