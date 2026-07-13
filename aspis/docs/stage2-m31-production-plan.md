# Stage 2 M31 circle-PCS production integration plan

Date: `2026-07-11`

Status: **teeth-first implementation specification; no production protocol,
parameter, transaction architecture, or gate ruling is selected here.**

This plan turns the passing host-only M31 circle conformance fixture into one
measurable, append-only diagnostic verifier. It deliberately stops before a
production instruction or final payment KAT is allocated. In particular:

- existing proof versions v3 and v4, instruction tags 0 through 23, and their
  KATs remain byte-for-byte frozen;
- instruction tag 20 remains the reserved, rejecting final-payment-v4 KAT;
- production `VerifyWithClaim` tag 6 must reject the circle diagnostic flag;
- the result may price a conforming PCS candidate, but cannot select a
  one-transaction or split architecture, waive the 1.19M project threshold,
  claim payment semantics, or close the soundness-transport gate.

Normative host anchors are:

- Stwo commit `5d10e6b4baa559766e7bbae133b918121211a9c5`;
- `crates/aspis-prover/tests/m31_circle_conformance.rs`;
- `crates/aspis-prover/tests/support/m31_circle_reference.rs`;
- `results/stage2/m31_circle_conformance.json`;
- `crates/aspis-prover/tests/m31_line_fri_conformance.rs` and
  `results/stage2/m31_line_fri_conformance.json`;
- the retained official-source corpus generator and reproduction command in
  `reference/stwo-line-fri/`;
- the retained full-circle candidate generator and pinned official roots in
  `reference/stwo-circle-candidate/`;
- `stage2-circle-soundness-transport.md`, whose code-level Johnson transport
  is positive but whose grouped-fold, OOD, MLE-binding, and BCS protocol
  obligations remain open;
- the direct Aspis MLE coordinate contract: coefficient/message index bits are
  big-endian, so the least-significant index bit is the last MLE coordinate.

The host fixture proves a representation identity. It does not prove
circle-FRI/S-two soundness, implement a proof parser, or authorize a payment.
Those distinctions remain binding throughout this plan.

### Implementation checkpoint

The append-only framing slice is implemented. Core parsing recognizes
`FLAG_M31_CIRCLE_C1_DIAGNOSTIC = 0x08` only as the exact required word `0x0b`,
declares the 784-byte layer-zero leaf, and reserves the basis discriminator.
Borsh tag 24 validates the exact q36/g16 header and ten canonical QM31 public
coordinates, then rejects deliberately. Production tag 6 rejects the same
flagged proof before transcript work; a feature-gated weakened verifier accepts
that proof only by misclassifying it as the legacy CM31 basis. Tags 0 through
24 are serialization-pinned, existing transcript KATs are unchanged, and the
weak feature is absent from the SBF dependency graph.

This framing slice alone does **not** complete implementation-order steps 2
and 3. The AIR-IFFT, endian, slot, fold, OOD, C2, root, frontier, and query
families now have independent host teeth below; composing them into one proof
path, exceptional sampler failures, and the selected-rule production vectors
remain open.
The fixed candidate prefix and its pre-batching transcript slice are now
implemented: a zero-copy exact parser exposes all offsets, canonical-checks
all 142 QM31 fields, and derives lambda, chi, and gamma only after the two
distinct roots, external points, and all 102 statement values. Eight paired
weakened schedules cover early gamma, partial value blocks, root labeling and
swapping, and C2 omission/order; each accepts its own vector while the
canonical schedule differs. This slice deliberately stops after gamma and
does not pin an expected digest. Independent openings and fold checks now
exist below, but the two-point rule, their composed proof path, transcript KAT,
SBF acceptance, and soundness transport remain open. The candidate-only evidence is
`results/stage2/m31_circle_prefix_candidate.json`.

A separate host-only continuation exercises the complete fixed transcript
tail for the two comparison shapes: fresh kappa and disjoint
gamma powers beginning at `gamma^51`. It continues the same transcript through
the layer-specific circle/line OOD samplers, both `(point,Y,mu)` triples,
layer-tagged sumchecks and alphas, natural final four, grinding, and 36 queries.
Nine paired weakened schedules cover later-root, OOD, sampler/label, alpha,
final, nonce, and query ordering. The comparison deliberately offers no
independent-lane fixed-prefix mode, pins no expected digest, verifies no
algebra or opening. Fresh kappa is now selected; disjoint gamma powers remain
rejected comparison provenance. Its evidence is
`results/stage2/m31_circle_transcript_tail_candidate.json`.
The matching host writer round-trips every root and all 142 QM31 fields through
that parser, with a pinned full-prefix digest. Its OOD and sumcheck values are
canonical fixtures only; this catches writer/parser drift without claiming the
relations or pinning a transcript KAT.
The fixed 102-value block is also generated at external `z` and derived
`xor11(z)` in point-major/column-major order. At both points, gamma-combining
the 51 individual evaluations equals evaluating the gamma-combined natural
message, including helper powers 49 and 50. This establishes the statement
block's linear wiring; the selected two-point rule is fresh kappa.

The host relation builder now accepts two explicit point scales without naming
or selecting their batching rule, adds two secure-circle OOD tensors in round
zero and two line tensors in each later round, constructs all four degree-six
sumcheck messages, folds natural coefficients and dual weights together, and
checks the terminal dot on final4. Independent fully materialized vectors
match every boundary, coefficient, alpha evaluation, and fold for two
nontrivial scale pairs. It receives the full message and explicit challenges,
so it is relation-conformance evidence—not a commitment verifier or transcript
integration.

The host encoder portion of step 5 is also implemented without a proof
acceptance path. All 49 direct M31 C1 messages and both coordinatewise QM31 C2
messages are differentially encoded over the full log-12 codeword; all 1,024
784-byte C1 leaves, 128-byte C2 leaves, and both candidate-tagged radix-4 roots
match independent test assembly. Eight representation classes now have paired
weakened acceptance and canonical rejection in
`results/stage2/m31_representation_teeth.json`. This does not yet build later
roots, openings, a transcript, or an SBF verifier inside the encoder artifact;
the later independent slices below consume its outputs.
The same full fixture now reproduces against official Stwo itself: C1 root
`c6a93117...ad4f`, C2 root `c764cdff...30b3`, with every codeword/leaf digest
and the generator stdout pinned by the retained example.

The verifier-side arithmetic portion of steps 4, 7, and 8 is host-tested in
`aspis-core::circle_fri`: fixed circle/line domain access, normalized first and
later folds, the later-`LinePoly`-only bit-reversal bridge, query mapping, and
final tensor evaluation. Exhaustive fixed-profile tests cover every public
domain point/fiber/query and return explicit errors for invalid shapes or zero
denominators. The host query checker now calls them, but no accepting SBF path
does.

The host commitment path now gamma-combines all 51 encoded codewords, applies
four normalized arity-4 folds, commits the intervening line layers under tags
`0x41..0x43`, and checks every one of the 16 terminal-domain evaluations
against the four natural tensor coefficients. Independent radix-4 root
assembly and a pinned aggregate digest cover all three later layers. This is
still a host-only consistency path: its explicit inputs are not themselves a
transcript or authenticated proof, it selects no two-point rule, and it
contributes no CU number.

The sequential host candidate builder now joins the previously separate
encoder, transcript-tail, OOD/sumcheck relation, fold-root, terminal, grinding,
and query slices in their actual causal order for both comparison
alternatives. It exact-parses and replays each 2,456-byte result and
independently validates the completed relation. Candidate hashes
`8df40160...152b8e` (fresh kappa) and `8b17d07d...327296` (disjoint
`gamma^51`) are pinned; flipping the external statement-digest bit produces
the separately pinned `2596c4cc...f7ee5f` stale fixture and changes gamma and
the post-query transcript state. This is host candidate evidence, not the
downstream production KAT. Fresh kappa is selected and now attaches to the
opening suffix in the 57,668-byte fixture. Append-only tag 26 accepts the exact
PCS path on SBF at 1,112,605 CU in 5/5 identical standard-envelope runs, with
stale-statement rejection. C2 remains fixture data, and this instruction cannot
authorize a payment or pool transition. The 287,395-CU platform headroom is not
yet product headroom; the path is 77,395 CU below the project threshold before
payment work.

This is the overlap-subtracted in-place PCS measurement. The isolated
501,989-CU tag-23 RLC row is contained inside 1,112,605 CU and must never be
added to it; 1,614,594 CU is a deliberate naive-sum anti-vector.

The Johnson rate/query fork is now measured. The fixed rho=1/4 q74/g32 proof
costs 1,873,746 CU after overlap subtraction and cannot fit one transaction.
The natural rho=1/16 q36/g32 redesign keeps four folds/final4 and accepts its
complete 73,620-byte PCS proof directly at **1,237,877 CU in 5/5 runs**. Its
segmented control is 1,237,884 CU (7 CU above direct), and it leaves 162,123 CU
against the platform cap. This is the active one-transaction engineering
candidate. It is not production-selected until the rho=1/16 T1/T2/per-fold-
PoW/BCS derivation, payment composition, hiding, and transition gates close.

The layer-zero opening verifier now parses and authenticates separately framed
C1 and C2 radix-4 minimal-subtree proofs against the official roots, with
canonical M31/QM31 decoding and externally derived sorted query indices.
Column/slot layout, tag swap, sibling order, and C1-frontier-reuse attacks all
have unchanged adversarial bytes accepted by explicit weakened test helpers
and rejected canonically. The composed host fixture described below now joins
this parser to the arithmetic query checker.

The three later 64-byte line layers now have their own exact sequential
opening parser and radix-4 verifier at depths 8/6/4 under tags
`0x41/0x42/0x43`. Query-derived indices are fixed to unique `q>>2`, `q>>4`,
and `q>>6`, and borrowed leaf/slot lookup exposes the intervening two-bit
chunks. Wrong tags, shifts, slot order, frontier reuse, truncation, and
trailing bytes all have same-vector weakened acceptance and canonical
rejection. The composed host fixture described below now joins these layers to
the arithmetic query checker.

The fixed per-query arithmetic checker now takes one exact 784-byte C1 leaf,
one 128-byte C2 leaf, and the three 64-byte later leaves supplied by the
opening layer. It canonical-decodes and gamma-combines powers 0..50, checks the
normalized circle fold against layer 1, the next two line folds against layers
2 and 3, and the last line fold against the natural final-four tensor at
`q>>6`. The full committed candidate passes all 1,024 query paths. Seven
same-input weakened vectors cover helper-power shift, the `q>>2/q>>4/q>>6`
chunks, circle and line alpha reuse, and final storage order; each rejects at
the canonical layer/terminal boundary with an explicit leaf offset or final
index. This is the host-only arithmetic artifact
`results/stage2/m31_circle_query_consistency.json`. It does not authenticate a
leaf or index, connect to tag 24, pin a transcript KAT, run on SBF, report CU,
or make a protocol or architecture ruling in isolation.

The composed host opening fixture now authenticates the layer-zero C1/C2 and
all three later-line sections before borrowing the exact leaves into the query
checker. Its 36 raw queries produce 34 layer-zero indices and exactly
21/18/15 later indices; the 48,124-byte suffix has SHA-256
`2775983d...0c780d`. Mutations distinguish layer-zero authentication,
later-layer authentication, and terminal arithmetic failures, while count,
trailing-byte, mixed-alpha, query-count, and range attacks reject at their
canonical boundaries. This closes host composition for explicit gamma/alpha
inputs. Attaching it to one selected sequential transcript tail, and then SBF,
remains open.

The append-only tag-25 diagnostic now supplies the previously missing neutral
cost comparison among the two-point rules on an identical relation fixture:
51,052 CU for the insecure one-point baseline, 68,380 for fresh kappa,
92,923 for two independent lanes, and 70,981 for disjoint gamma powers. Each
row has five identical standard-heap local-validator repetitions, host/SBF sink
parity, and pinned relation bytes/hash counts. Cancellation, ordering,
lane-omission, and shifted-power weakened validators provide teeth. The artifact is
`results/stage2/two_point_batching_probe.json`. It is isolated from tag 24 and
the production circle proof, cannot be added to a PCS total, and does not
ratify a rule, amend a soundness term, or authorize a transcript change.

## 1. Append-only diagnostic wire allocation

The first integration uses the existing v4/s=2 header shape with a new flag. A
new production version is not allocated.

| item | pinned diagnostic value |
| --- | --- |
| envelope name | `v4/s2-m31-circle-d0` |
| header version | `VERSION_V4_S2 = 4` |
| basis discriminator | ASCII `aspis:c1:m31-circle:v0` |
| new flag | `FLAG_M31_CIRCLE_C1_DIAGNOSTIC = 0x08` |
| required flag word | `0x0b = EVALUATION_CLAIM(0x01) \| SECOND_PHASE(0x02) \| M31_CIRCLE(0x08)` |
| forbidden combination | `FLAG_EXACT_WIDE_C1(0x04)` and `FLAG_M31_CIRCLE_C1_DIAGNOSTIC(0x08)` set together |
| fold payload | `RawFibers = 0` |
| Merkle mode | `Radix4MinimalSubtree = 2` |
| append-only Borsh instruction | tag **24**, `VerifyM31CircleV4Diagnostic` |
| first measurement profile | id 6, `capacity_lr10_q36_g16` |
| final-profile reservation | id 8, `capacity_lr10_q36_g32`; not selected or measured by the first run |

Tag 24 has the diagnostic arguments

```text
VerifyM31CircleV4Diagnostic {
    statement_digest: [u8; 32],
    claim_z: Vec<[u8; 16]>,
    statement_evaluations_digest: [u8; 32],
}
```

and consumes the same uploaded, program-owned proof account convention as the
current verifier. The second digest is

```text
SHA256("aspis:m31-circle:statement-evaluations:v0" ||
       z_bytes || xor11_z_bytes || evaluation_block_bytes)
```

so the diagnostic cannot accept a prover-chosen two-point claim vector that is
unbound to the instruction. `claim_z` must contain exactly ten canonical QM31
coordinates and is an external public input, matching the current PCS claim
API. It is not read from proof bytes. The digest is a diagnostic binding, not
final payment-statement semantics.

Header parsing may recognize `0x08` only after all existing header tests have a
frozen compatibility vector. Canonical tag 6 and reserved tag 20 reject any
proof carrying `0x08` before roots, field arithmetic, or Merkle work. Tag 24
requires exactly version 4, flags `0x0b`, raw fibers, radix-4 Merkle mode,
`log_rows=10`, `log_blowup=2`, four rounds, and a four-coefficient final
polynomial. No other instruction may enable the flag.

## 2. Normative message and statement-vector contract

### 2.1 C1 and C2 messages

C1 consists of exactly 49 M31 vectors of length 1,024. Column order is the
frozen statement order, with the multiplicity column last. For each column,
`c1[column][row]` is the multilinear message table in big-endian Boolean index
order. It is passed directly as the 1,024 circle tensor coefficients, then
zero-extended to 4,096 coefficients before the canonical circle FFT. An AIR
interpolation or circle IFFT before encoding is a different message and is
forbidden.

C2 consists of exactly two challenge-dependent QM31 message vectors, `h1` then
`h2`, each of length 1,024 in the same MLE coordinate order. They are encoded
over the same canonical circle domain using M31 twiddles and QM31 values. C2 is
not folded into C1 before either root is committed.

Two coefficient orders must remain distinct throughout the implementation:

```text
R_r = natural Aspis relation/MLE vector at round r
S_r = Stwo bit-reversed coefficient-storage vector used to encode round r
```

The ratified layer-zero embedding is byte-direct: `S_0` receives the original
message bytes `R_0` without AIR interpolation or a pre-encoding permutation.
That statement does not license later folded vectors to skip their storage
conversion. After every adjacent arity-4 relation fold, the next natural vector
`R_(r+1)` is converted explicitly as

```text
S_(r+1) = bitreverse(R_(r+1)).
```

This bridge changes storage order only. It never changes the big-endian MLE
variable order, the natural relation weights, or which four natural
coefficients are folded together. A single vector cannot be called both
"natural" and "bit-reversed" at a round boundary.

The two commitment phases are ordered:

```text
C1 message vectors -> one C1 root
                   -> squeeze lambda
                   -> squeeze chi
                   -> construct h1,h2
                   -> one combined C2 root
```

There is one wide C1 root, not one root per slot or column. There is one C2 root
containing both helpers, not two independently swappable helper roots.

### 2.2 Two statement points and 102 values

Tag 24 receives one canonical 10-coordinate QM31 public-input point
`z = [z0,...,z9]`. The proof does not choose it. The second point is derived,
never independently supplied:

```text
xor11(z) = [z0,...,z7, 1-z8, 1-z9]
```

because `z8` and `z9` correspond to the two low row-index bits under Aspis's
big-endian MLE convention.

The fixed evaluation block contains 102 canonical QM31 values in point-major,
column-major order:

```text
for point in [z, xor11(z)]:
    C1[0](point), ..., C1[48](point), C2[h1](point), C2[h2](point)
```

Each QM31 is 16-byte little-endian canonical limb encoding. No count, offset,
padding, alternate point order, or optional helper field appears inside this
fixed block. Both points and all 102 values are transcript-absorbed before
gamma.

After gamma is sampled, for point `p` the combined claim is

```text
V[p] = sum(c=0..48, gamma^c * lift(C1[c](p)))
     + gamma^49 * C2[h1](p)
     + gamma^50 * C2[h2](p).
```

The two point claims use the note-selected fresh exact-uniform `kappa`, sampled
after gamma, with scales `1` and `kappa`. The soundness ledger charges
`51/|QM31|` to T5'. The rejected alternatives and measurement provenance are
retained in `stage2-two-point-batching-options.md`. The next append-only SBF
path must implement exactly this order and selected rule.

## 3. Circle domains, leaves, roots, and openings

### 3.1 Codeword and slot order

The layer-zero domain is
`CanonicCoset::new(12).circle_domain()` from the pinned Stwo source. Codeword
symbols are in Stwo bit-reversed `CircleDomain` order. For fiber `f` and slot
`s`, the codeword index is exactly

```text
index(f,s) = 4*f + s,  f in 0..1024, s in 0..4.
```

If slot zero is `p=(x,y)`, the four consecutive points are

```text
slot 0: ( x,  y) = p
slot 1: ( x, -y) = Jp
slot 2: (-x, -y) = Ap
slot 3: (-x,  y) = JAp.
```

The internal Stwo FFT-twiddle comment describing
`(x,y),(-x,-y),(y,-x),(-y,x)` is the bit-reversed order of a CanonicCoset used
to derive twiddles. It is not the returned bit-reversed full `CircleDomain`
codeword order and must never be used as a leaf layout.

Every later committed layer is a bit-reversed Stwo line-domain codeword. Its
four-slot leaf is the encoding of `S_r = bitreverse(R_r)` and contains the four
consecutive symbols `4*f+s`; no legacy Aspis `f+s*fiber_count` transpose is
allowed.

### 3.2 Leaf bytes and tree identities

The diagnostic uses the existing SHA-256 radix-4 node compression, with new
append-only leaf layer tags so roots cannot be reinterpreted across bases:

```text
M31_CIRCLE_COMBINED_LAYER_TAG_BASE = 0x40  // tags 0x40..0x43
M31_CIRCLE_C2_LAYER_TAG            = 0xc0
```

Layer-zero C1 uses tag `0x40`; combined later layers use `0x41`, `0x42`, and
`0x43`; C2 uses `0xc0`. Leaf hashing remains
`SHA256(DOM_LEAF || layer_tag || leaf_bytes)`. Radix-4 parents retain ordered
child slots 0,1,2,3 and the existing `DOM_NODE4` prefix.

| commitment | leaf index/count | exact leaf bytes | size |
| --- | --- | --- | ---: |
| layer-0 C1, one root | `f`, 1,024 leaves | for `s=0..3`, then `c=0..48`: `M31(encoded_C1[c][4f+s])` | 784 |
| layer-0 C2, one root | `f`, 1,024 leaves | helper-major encoded symbols: `h1[4f+s]` for slots 0..3, then `h2[4f+s]`; each QM31 LE | 128 |
| combined line layer 1 | `f`, 256 leaves | four consecutive QM31 symbols, slots 0..3 | 64 |
| combined line layer 2 | `f`, 64 leaves | four consecutive QM31 symbols, slots 0..3 | 64 |
| combined line layer 3 | `f`, 16 leaves | four consecutive QM31 symbols, slots 0..3 | 64 |

Thus the binary depths supplied to the radix-4 multiproof verifier are
10, 8, 6, and 4. C2 also has binary depth 10. All are even and have exact
radix-4 depths 5, 4, 3, and 2.

For each layer the opening section is fixed:

```text
u16 unique_count
unique leaves in ascending leaf-index order
if layer 0: matching C2 leaves in the same ascending index order
u32 C1-or-combined frontier_node_count
frontier hashes in current radix-4 level/parent/child traversal order
if layer 0:
    u32 C2 frontier_node_count
    C2 frontier hashes in the same traversal order
```

There are no carried fold values in this diagnostic. Counts must exactly match
the verifier-recomputed unique indices; trailing, unused, duplicate, unsorted,
or out-of-range leaves and frontier nodes reject.

### 3.3 Query transition

Queries are derived only after final-polynomial absorption and grinding. Each
initial query is sampled exactly uniformly in `[0,1024)` and names a layer-zero
circle **fiber**, not one of the 4,096 individual symbols.

For an initial query `q`:

```text
layer 0: leaf f0 = q; opens symbols 4q..4q+3; fold output line index i1 = q
layer 1: leaf f1 = i1 >> 2; incoming slot s1 = i1 & 3; output i2 = f1
layer 2: leaf f2 = i2 >> 2; incoming slot s2 = i2 & 3; output i3 = f2
layer 3: leaf f3 = i3 >> 2; incoming slot s3 = i3 & 3; output i4 = f3
final:   evaluate the four-coefficient final tensor polynomial at line-domain index i4
```

Equivalently, later incoming slots are `q&3`, `(q>>2)&3`, and `(q>>4)&3`, and
the final index is `q>>6`. This transition is part of the wire contract. The
legacy strided-fiber map, a codeword-position query followed by `q>>2`, or a
path authenticated for a different leaf index must reject.

## 4. Transcript schedule and labels

The following absorb labels are appended after the currently allocated labels
1 through 10:

| id | name | absorbed bytes |
| ---: | --- | --- |
| 11 | `M31_CIRCLE_BASIS` | exact ASCII discriminator |
| 12 | `M31_CIRCLE_ROUND_ROOT` | `layer_u8 || root32` (C1 at layer 0; combined thereafter) |
| 13 | `M31_CIRCLE_C2_ROOT` | `root32` |
| 14 | `M31_CIRCLE_STATEMENT_POINTS` | `z_bytes || xor11_z_bytes` |
| 15 | `M31_CIRCLE_STATEMENT_EVALUATIONS` | fixed 102-value block |
| 16 | `M31_CIRCLE_OOD_VALUE` | `layer_u8 || sample_u8 || value16` |
| 17 | `M31_LINE_OOD_VALUE` | `layer_u8 || sample_u8 || value16` |
| 18 | `M31_CIRCLE_RELATION_SUMCHECK` | `layer_u8 || 7*QM31` |
| 19 | `M31_CIRCLE_FINAL_TENSOR_POLY` | four natural-order QM31 relation/tensor coefficients |

Existing labels `PROFILE`, `STATEMENT`, and `GRIND_NONCE` retain their current
IDs and encodings. Squeezes remain state-advancing exact-uniform challenge
calls; their semantic names below are pinned by schedule and by the new KAT.

The canonical transcript is:

```text
absorb PROFILE(header16)
absorb M31_CIRCLE_BASIS(discriminator)
absorb STATEMENT(statement_digest32)

absorb M31_CIRCLE_ROUND_ROOT(0 || c1_root)
squeeze lambda
squeeze chi
absorb M31_CIRCLE_C2_ROOT(c2_root)
absorb M31_CIRCLE_STATEMENT_POINTS(z || xor11(z))
absorb M31_CIRCLE_STATEMENT_EVALUATIONS(102 values)
squeeze gamma
squeeze the note-ratified two-point batching challenge
    (provisional candidate: kappa)

for layer in 0..4:
    if layer > 0:
        absorb M31_CIRCLE_ROUND_ROOT(layer || combined_root[layer])
    for sample in 0..2:
        sample beta[layer][sample] completely
        read and canonical-decode Y[layer][sample]
        absorb layer-specific OOD_VALUE(layer || sample || Y)
        squeeze mu[layer][sample]
        add mu * (evaluation weight, claimed value) to the relation
    absorb M31_CIRCLE_RELATION_SUMCHECK(layer || polynomial)
    check its boundary against the accumulated relation
    squeeze alpha[layer]
    evaluate the sumcheck at alpha and fold all relation weights

absorb M31_CIRCLE_FINAL_TENSOR_POLY(final4)
check the terminal relation on final4
check grinding nonce, then absorb GRIND_NONCE(nonce)
derive q query fibers
```

`gamma` is unavailable until both roots, both statement points, and all 102
values have been absorbed. The two-point batching squeeze is unavailable until
gamma has been derived and must follow the note-first ruling above. Each
`(beta,Y,mu)` triple completes before the next sample starts. `alpha[layer]` is
unavailable until both triples and the shared relation-sumcheck polynomial have
been absorbed.

The corresponding proof prefix is fixed-width and serialized as:

```text
header16
layer0_c1_root32
layer0_c2_root32
statement_evaluations[102]          // 1,632 bytes; z is external tag-24 input
layer0_ood_value[0]                 // 16 bytes
layer0_ood_value[1]                 // 16 bytes
layer0_relation_sumcheck[7]         // 112 bytes
for layer in 1..4:
    combined_root32
    ood_value[0]                    // 16 bytes
    ood_value[1]                    // 16 bytes
    relation_sumcheck[7]            // 112 bytes
natural_final_tensor_coefficients[4] // 64 bytes
grinding_nonce_u64_le
opening_sections                    // section 3.2, layers 0..3
```

There are no proof-carried `z` bytes, helper-claim fields outside the 102-value
block, optional counts inside the block, or roots after the final coefficients.
All length arithmetic is flag-aware, checked before slicing, and rejects
trailing bytes.

## 5. OOD sampling and tensor relation weights

### 5.1 Layer-zero rational secure-circle sampler

Layer zero uses a rational secure-circle point. Each bounded attempt draws an
exact-uniform QM31 parameter `t` using the existing per-limb rejection sampler.
The attempt rejects, advancing to fresh transcript output, if either:

- `t` lies in CM31 (`t.c1 == 0`), which in particular excludes every M31
  circle-domain point; or
- `d = 1 + t^2` is zero.

On acceptance:

```text
x = (1 - t^2) / d
y = 2t / d
beta = (x,y), with x^2 + y^2 = 1.
```

The outer retry limit is three, matching the current OOD completeness budget.
Exhaustion is proof rejection. The denominator-zero check is explicit even
though its roots lie in the rejected CM31 subfield; it must survive any future
sampler generalization and has its own adversarial vector.

Conditioned on acceptance, this is uniform on
`C(QM31) \ C(CM31)`, not on the larger set used by every upstream theorem.
That exact cardinality and an explicit RS-order degree convention must appear
in T2; the sampler implementation alone does not transport the current
STIR/WHIR list-collision formula.

For a length-`2^m` direct coefficient vector, the low-index-bit circle factors
are

```text
[y, x, pi(x), pi^2(x), ..., pi^(m-2)(x)],  pi(u)=2u^2-1.
```

Aspis's structured weight vectors are indexed in big-endian MLE coordinate
order. Therefore the stored factor vector is the reverse:

```text
[pi^(m-2)(x), ..., pi(x), x, y].
```

Writing `[y,x,pi,...]` directly as a big-endian point is an ordering bug.

### 5.2 Later line-layer sampler

Layers 1 through 3 commit line polynomials. Their OOD point is an exact-uniform
`u in QM31 \ CM31` from the existing `challenge_ood_qm31` sampler. They do not
reuse the x-coordinate marginal of a rational circle point: that marginal is
not uniform over QM31.

The low-index-bit line factors are `[u,pi(u),pi^2(u),...]`, stored by the
big-endian accumulator as the reverse vector. A circle component folded once
by the layer-zero `(alpha,alpha^2)` operation loses its `y,x` factors and is
thereafter exactly the corresponding line-tail component. Components added by
later line samples start directly in the line basis.

All structured relation components act on `R_r`, the natural adjacent-folded
vector. Encoding and Merkle commitments act on `S_r`. The explicit bit-reversal
bridge is therefore applied after relation folding and before the next Stwo
line encoding; it is not absorbed into an OOD factor permutation.

For both samples in a layer, the proof value is accumulated only after its
point is fully sampled and its canonical bytes are absorbed. No sampled point,
claim value, or mix challenge is reusable across layers or samples.

## 6. Normalized folds and final polynomial

### 6.1 First circle-to-line arity-4 fold

After gamma recombination, let the four layer-zero values be
`v0,v1,v2,v3` at `(x,y),(x,-y),(-x,-y),(-x,y)`. With `a=alpha[0]`:

```text
g_pos = (v0+v1)/2 + a   * (v0-v1)/( 2y)
g_neg = (v2+v3)/2 + a   * (v2-v3)/(-2y)
out   = (g_pos+g_neg)/2 + a^2 * (g_pos-g_neg)/(2x).
```

This is Stwo's raw circle fold followed by one line fold, divided by four. It
is coefficient folding by the low-bit factors `(a,a^2)` and weights
`[1,a,a^2,a^3]`. The second challenge is exactly the square of the first; it is
not a fresh squeeze and not another copy of `a`.

The unnormalized Stwo inverse-butterfly output for these two folds is exactly
four times the Aspis normalized result. The implementation must differential-
test `raw_stwo == 4 * normalized_aspis` before applying the round-boundary
bit-reversal bridge.

### 6.2 Later two-at-a-time line folds

For a line-domain point `u`, define the normalized inverse butterfly

```text
NIB(left,right,u,theta) = (left+right)/2
                        + theta * (left-right)/(2u).
```

For a four-symbol leaf at layer `r>0`, the verifier obtains the pair points
from the pinned Stwo `LineDomain::at(bit_reverse_index(...))` accessor:

```text
g0 = NIB(v0,v1, u0, alpha[r])
g1 = NIB(v2,v3, u1, alpha[r])
out = NIB(g0,g1, u2, alpha[r]^2)
```

where `u0` and `u1` are the two pair representatives at indices `4f` and
`4f+2`, and `u2` is the corresponding representative in the doubled line
domain. This definition, rather than a handwritten sign shortcut, is the
normative orientation. The output codeword index is `f`.

Each two-line-fold round has the same normalization rule: raw Stwo output is
four times the Aspis normalized value. The normalized natural output vector is
`R_(r+1)`; only then is it bit-reversed to `S_(r+1)` for the next codeword.
Every round requires a full-vector or digest differential covering both the
factor four and the storage permutation.

### 6.3 Final tensor polynomial

After four arity-4 rounds, four natural QM31 relation coefficients remain as
`R_4`. The diagnostic serializes `R_4` in natural coefficient order, 16-byte
canonical little-endian each, and absorbs those exact bytes under label 19.
The relation accumulator dots directly against this natural vector.

For query evaluation, the verifier makes a separate storage copy
`S_4 = bitreverse(R_4)` and passes that copy to the pinned Stwo line-polynomial
evaluation convention at final line-domain index `q>>6`. Natural relation
state is never mutated into storage order. Omitting the copy's bit reversal,
reversing `R_4` before the relation dot, or serializing `S_4` instead is a wire
bug. Ordinary monomial Horner evaluation or an unledgered tensor-to-monomial
conversion is also not wire-compatible unless independent evidence changes
this exact convention first. Such a change requires a new discriminator, KAT,
and explicit terminal relation conversion; it is not silently interchangeable
with this diagnostic.

## 7. Teeth-first adversarial matrix

Every ordering or representation class below needs both halves of a teeth
demonstration:

1. canonical code rejects the adversarial proof/vector; and
2. one deliberately weakened `cfg(test)` build accepts that same vector.

A rejection without weakened acceptance is only a malformed-proof test. A
weakened acceptance without canonical rejection is a live defect. All weakened
features must be absent from the SBF build and from its Cargo feature graph.

| class | deliberately weakened behavior | pinned adversarial vector and canonical result |
| --- | --- | --- |
| AIR-IFFT reinterpretation | interpolate each trace column as AIR-domain evaluations before circle encoding | nontrivial real `SpendTraceV4` proof built from the IFFT roots accepts weakened; canonical direct-message verifier rejects root/claim/KAT |
| MLE endian/basis reversal | pair the highest index bit with `y`, or reverse the direct coefficient vector | one-hot and nonsymmetric columns make the wrong root and OOD claim accept weakened; canonical rejects |
| folded storage bridge | encode natural `R_(r+1)` directly, bit-reverse twice, or bit-reverse relation weights instead of only Stwo storage | weakened line encoder accepts its paired roots; canonical per-round digest, next-layer slots, OOD relation, or terminal check rejects |
| circle slot order | use the internal twiddle-coset order or legacy strided slots instead of `p,Jp,Ap,JAp` | wrong-order leaf and fold accept weakened; canonical rejects Merkle/fold consistency |
| second fold challenge | use `alpha`, a fresh challenge, or the wrong power instead of `alpha^2` | crafted first-layer and later-line folds accept weakened; canonical rejects the next-layer slot/final check |
| fold normalization | accept raw Stwo output without dividing by four, or divide only one inverse-butterfly layer | weakened scaled proof accepts; canonical next-root/final relation rejects and the `raw == 4*normalized` KAT fails |
| OOD factor order | store `[y,x,pi,...]` as a big-endian factor vector, or retain `y` after the first fold | false OOD relation sumcheck accepts weakened; canonical boundary or terminal relation rejects |
| exceptional rational sampler | accept `1+t^2=0`, map inverse-zero to `(0,0)`, or reuse rejected transcript bytes | injected hash stream first emits an exceptional `t`, then a valid `t`; canonical retries and pins the later point, weakened accepts the invalid path. All-three-exceptional stream rejects canonically |
| gamma before claims | squeeze gamma before C2 root, before either statement point, after only 51 values, or before value 102 | matching weakened transcript accepts; canonical transcript/KAT rejects |
| C2 omission/power | omit h2, split helpers into swappable roots, use powers 48/49, or serialize C2 slot-major | weakened proof accepts; canonical root, 102-value digest, gamma combination, or fold rejects |
| root mix-and-match | swap C1/C2 roots, swap later roots, reuse a root from another proof, or change a root label | weakened unlabeled schedule accepts its paired vector; canonical transcript/Merkle check rejects |
| query mapping | authenticate legacy `f+sF`, use a codeword-position query, or shift before layer zero | weakened legacy mapper accepts; canonical consecutive-slot mapper rejects path/slot consistency |
| leaf/frontier framing | duplicate/unsort a unique index, append a frontier node, change child slot, or use a C1 leaf under the C2 tag | canonical rejects exact framing or root; a weakened count/index/tag check demonstrates each vector's intended tooth |
| two-point cancellation | omit the note-ratified batching rule and choose opposite claim errors at the two points | unbatched weakened verifier accepts; canonical ratified batching rejects except at its ledgered field-probability event |
| final basis | serialize storage-order final coefficients, skip the query-evaluation copy's bit reversal, or reverse the natural relation vector before its dot | weakened terminal evaluator accepts its paired proof; canonical final query/relation check rejects |
| noncanonical field bytes | encode M31 `P`, or any QM31 limb `P`, in C1/C2/claims/OOD/final bytes | host and SBF reject before arithmetic; canonical encodings continue to accept |

At minimum the random-property families vary fibers at boundaries and interior,
gamma/alpha and the ratified two-point batching challenge including 0 and 1,
nonzero random deltas, both OOD samples, all four layers, each C1 column, both
C2 helpers, both statement points, and each root/frontier section.

## 8. KAT and re-pin discipline

The existing candidate fixture digest
`95ca0bc440d1754d00be69de738122341381c50c395c2ae904f8ad845515d588`
remains a host representation anchor. It is not renamed as a production KAT.

Integration adds a distinct function and constant named
`transcript_kat_v4_s2_m31_circle_diagnostic` and
`TRANSCRIPT_KAT_V4_S2_M31_CIRCLE_DIAGNOSTIC_EXPECTED`. The vector covers:

- the 16-byte header, flag `0x08`, and basis discriminator;
- C1 and C2 roots in their distinct labels;
- lambda, chi, all 102 evaluation values, gamma, and the note-ratified
  two-point batching rule (provisional candidate: kappa);
- rational layer-zero sampler output and retry behavior;
- exact-uniform later line samples;
- both `(beta,Y,mu)` triples in every layer;
- every relation polynomial and alpha;
- natural final tensor coefficients, grinding, query fibers, later leaf/slot
  mapping, round-boundary bit reversals, raw-versus-normalized factor-four
  checks, the final query-evaluation storage copy, and the final indices.

Host SHA-256 and the Solana SHA-256 syscall must compute the same pin through
tag 24. The test first runs with an intentionally stale expected digest and
records the failure before the new expected value is committed.

`results/stage1/transcript_kat_repin_ledger.json` receives one append-only
entry in the same commit as the schedule. It records the old scaffold pin, the
new diagnostic pin, every added label/squeeze/absorption, the basis/leaf/query
change, proof version and flag, instruction tag 24, and the statement that tag
20 remains reserved and unchanged. Editing the v3 or v4 scaffold expected
constant to make this suite green is forbidden.

## 9. Implementation order

The dependency order is intentionally teeth-first.

1. **Freeze this specification.** Add no acceptance path yet.
2. **Land red adversarial fixtures and weakened test builds.** At least the
   AIR-IFFT, endian/basis, slot, alpha-squared, OOD-order, exceptional-sampler,
   gamma-before-values, C2-omission, and root/query-mix vectors must demonstrate
   weakened acceptance before their canonical fixes count as evidence.
3. **Add append-only parsing constants.** Introduce flag `0x08`, leaf tags, and
   Borsh tag 24. Preserve serialization KATs for all prior tags. Tags 6 and 20
   reject the new flag before expensive work.
4. **Implement sampler and relation weights.** Add the bounded rational circle
   sampler, generic reversed tensor factors, first-fold circle-to-line update,
   and direct exact-uniform later line components. Differential-test scalar,
   structured-weight, and folded terminal evaluations.
5. **Implement direct encoders and commitments.** Encode all 49 real C1 columns
   and two real C2 helpers, build one C1 and one C2 root, and pin full-codeword
   digests against the Stwo reference rather than only selected positions.
6. **Implement the two-point prefix.** Parse/derive the points, canonical-decode
   all 102 values, verify the instruction digest, derive gamma, and stop until
   the note-first two-point batching rule is ratified. The isolated tag-25
   comparison is decision evidence only and does not satisfy that ratification
   gate. Then implement exactly the selected challenge/rule. No zero filler or
   synthetic helper may appear in the integrated measurement path.
7. **Implement normalized folds and final tensor evaluation.** First circle
   fold, later Stwo line folds, natural-relation-to-bit-reversed-storage bridges,
   coefficient/weight folding, natural final serialization, the query-only
   final storage copy, and final checks land with their adversarial vectors.
8. **Implement exact openings and query transitions.** Use consecutive leaves,
   the fixed unique/frontier order, and `q -> q>>2` only after layer zero.
9. **Pin the new diagnostic transcript KAT.** Demonstrate the stale-pin failure,
   update the append-only ledger, and run host/SBF parity plus the complete
   weakened-build matrix.
10. **Run the in-place eight-seed measurement.** Only this integrated path may
    produce the candidate CU row.
11. **Re-derive circle-FRI/S-two transport and update the neutral owner packet.**
    A project-owner ruling happens only after that evidence; this plan does not
    supply or anticipate it.

No step may use a later CU result to waive an earlier missing tooth.

## 10. Priced implementation fork: public-domain denominator tables

The first circle domain and every later line domain are public and fixed for a
profile. A diagnostic implementation fork may replace runtime coordinate
derivation and batch inversion with a pinned read-only table keyed by
`(profile,layer,fiber,orientation)`.

The expected table scale is approximately 8--12KB: layer zero needs the
normalized `inv(2y)` and `inv(2x)` factors for 1,024 fibers, while the 256, 64,
and 16 later line fibers need their two normalized line inverse factors. This
is a size estimate, not a CU saving.

The table fork is admissible only with all of the following evidence:

- a checked-in deterministic generator tied to the pinned Stwo commit and
  exact profile/domain constants;
- canonical M31 encodings, a full-table SHA-256 digest, total byte count, and
  first/boundary/random-entry KATs on host and SBF;
- differential equality against runtime domain accessors and inversions for
  every entry, not a sampled subset;
- orientation teeth that swap `x/y`, negate the wrong slot, use layer `r+1`,
  reverse a table segment, or index by a legacy strided fiber;
- an SBF binary inspection proving the table is immutable program rodata and
  the weakened generator/table features are absent;
- deployed program binary-size delta, loader/deployment impact, and any account
  or instruction-cache impact reported explicitly;
- a literal same-proof SBF A/B across the registered eight seeds, with the
  runtime-derived/batch-inverted path and rodata-table path differing only in
  denominator acquisition.

Tag 23 measured a `+10,696`-CU coordinate-derivation increment and a
`+4,130`-CU batch-inversion increment in an isolated 36-fiber shape. Their
`14,826`-CU sum is not guaranteed headroom, is not subtracted from any PCS
total, and is not projected onto this different in-place path. The table fork
is selected only if its literal integrated SBF A/B wins without changing proof
bytes, roots, transcript, accepted language, heap envelope, or security
accounting.

## 11. Eight-seed in-place measurement contract

The first bookable measurement is the complete diagnostic circle-PCS verifier
at q36/g16, not a sum of tag-23 controls and older PCS totals.

For each of eight independently seeded statement/witness/transcript instances:

- generate a real 49-column `SpendTraceV4`, both nonzero C2 helpers, both
  statement points, all 102 values, four C1/combined round roots plus one C2
  root, two OOD samples per layer, the final tensor polynomial, grinding
  witness, and all required openings;
- upload the proof before the measured transaction, then invoke only tag 24
  with compute limit 1,400,000 and heap frame 262,144 bytes;
- require host and SBF acceptance of identical bytes;
- record seed, proof length, every root, transcript/KAT digest, statement-
  evaluations digest, sampled query fibers, unique leaves and frontier nodes
  per tree/layer, CU consumed, and peak/failed allocation if observable;
- report every raw CU observation plus min, max, mean, median, and spread;
- report signed margins separately against 1,190,000 and 1,400,000 CU;
- if the meter is exhausted, record only `>=1,400,001 CU` for that seed unless
  the identical work can be observed without changing its execution path;
- run the canonical corruption suite on at least one nondegenerate seed on
  both host and SBF: each root, C1 and C2 leaf, both helpers, both points, the
  first and last of the 102 values, each OOD sample, each relation polynomial,
  final coefficients, query mapping, frontier, basis flag, and noncanonical
  M31/QM31 limbs must reject;
- prove production tag 6 and reserved tag 20 reject the same flagged proof
  before reaching the diagnostic work;
- prove every deliberately weakened feature is absent from the SBF artifact.

The runtime-denominator implementation is the baseline. If the rodata table
fork is ready, it is measured as a paired A/B on the same eight proofs and
reported as a separate row. No isolated probe is added to or subtracted from
either integrated result.

The eight-seed q36/g16 result is a verifier-cost distribution, not the final
q36/g32 product number. A g32 measurement, payment constraint composition,
hiding, proof-account sealing, and pool transition are separate gates after a
project-owner selection. The registered conservative statistic remains the
only binding projection statistic until an in-place rule explicitly replaces
it.

## 12. Exit conditions and non-claims

This plan is implemented only when all of the following are true:

- prior tags, proof versions, and KATs remain frozen;
- the two-point batching rule has a note-first soundness entry and the
  diagnostic schedule/KAT implements that exact rule;
- every required weakened build accepts its adversarial vector and canonical
  host/SBF rejects it;
- the new candidate KAT has an explicit stale-pin demonstration and ledger
  entry;
- one layer-zero wide C1 root, one layer-zero C2 root, the three later combined
  roots, exact leaf order, exact query transition, s=2 OOD order, all 102
  values, gamma powers 0 through 50, all line folds, and the final tensor check
  execute in the measured instruction;
- eight independent standard-envelope measurements and corruption results are
  recorded without arithmetic composition of older probes.

Even then, the result proves only that the candidate diagnostic PCS path is
implemented and priced. It does not prove the revised finite-length
circle-FRI/S-two bound, the payment relation, LogUp totals, constraint-registry
soundness, masking/hiding, proof-account transport, atomic nullifier/output
state transition, or any architecture choice. Those truths must remain beside
the CU number wherever it is quoted.
