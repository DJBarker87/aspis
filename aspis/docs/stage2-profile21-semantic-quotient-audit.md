# Profile-21 semantic quotient audit

Date: 2026-07-13

> **INVALIDATED 2026-07-13:** the 712-to-716 quotient below was produced by
> an incoherent source vector: unbalanced C1 raw `e_r` was paired with a PCS
> tail cached as `e_r-e_d` on copy-inactive rows. The corrected physical map
> uses active `e_r`, inactive `e_r-e_d_c`, and skips each column's dependent.
> Its exact q16 replay is 712/712 with no semantic or legal-sumcheck pivots.
> See `stage2-profile21-physical-semantic-containment.md`. The historical
> rows, coefficients and conclusions below are retained only as a regression
> postmortem and must not be used as a hiding premise.

## Historical verdict (invalidated)

The four previously reported semantic sources

```text
(column,row) = (0,4), (1,0), (2,0), (3,0)
```

are streaming-echelon representatives, not four independently reachable
witness cells.

The three row-zero cells are killed exactly: atomic owner-key row zero is the
fixed initial state `[0^8, DOMAIN_OWNER_KEY, 8, 0^6]`.  This does **not** kill
the quotient.  Re-running the exact profile-21 rank calculation after removing
all sixteen row-zero cells leaves the same four-M31 (one-QM31) quotient.  Only
its representatives move to correlated owner-key trajectory cells.

The exact same-statement reachability question is not closed by the source
code.  Rows 1 onward are fixed polynomial functions of the private nullifier
key, but changing that trajectory while keeping the public nullifier and both
public Merkle roots fixed requires a collision somewhere in the Poseidon
hash/compression dependency graph.  Collision resistance would make the
witness computationally unique and kill every same-statement centre shift;
that is the explicitly rejected weaker privacy model.  There is no attached
unconditional theorem proving that the corresponding finite-field hash fiber
is a singleton or that it contains a pair whose image hits this quotient.

The root-zero control has also been widened beyond dense powers.  Adding one
multilinear `eq_row5` mask-only factor is RED; adding all four tower rotations
jointly is RED; and adding the complete fixed selector basis
`eq_row1..eq_row5` in all four tower rotations (twenty new M31 columns) is
still RED.  The last screen permits arbitrary schedule-dependent linear
combinations on the exact five-row owner-key support and permits cross-column
sumcheck cancellation, yet leaves `PCS=712` and the semantic quotient at
`716` on rows 276 through 279.  Thus the obstruction is not an artifact of
using powers of one dense linear form.  The twenty-column control would cost
320 bytes per opened layer-zero leaf and 6,080 value bytes on q16, so it is
both ineffective and economically irrelevant.

For unconditional algebraic witness-indistinguishability the safe ruling is
therefore to treat the complete one-QM31 quotient as live.  Its entropy lower
bound is one fresh QM31 value.  The controls below also show that this lower
bound cannot be implemented merely by appending another independently opened
root-zero mask column.

## Exact fixed-row exclusion replay

The current diagnostic excludes every `row == 0` semantic source before the
conservative witness augmentation.  The reproducible command is:

```text
NO_DNA=1 target/release/examples/profile21_good_schedule_probe witness-actual \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin
```

It returns:

```text
baseline selected PCS rank                 712 M31
rank with every non-row-zero semantic cell 716 M31
rank after every legal SC wire direction   716 M31
compatibility rank                           4 M31
compatibility pivot sources               [1,2,3,4]
semantic quotient sources                 [5,1025,2049,3073]
semantic quotient pivot rows              [276,277,278,279]
semantic minor fingerprint                0x07783670629fefd9
```

Source IDs are `1024 * column + row`, so the compatibility pivots are
`c0r1..c0r4`, and the four kernel representatives are
`c0r5,c1r1,c2r1,c3r1`.  Rows 276 through 279 are the four M31 coordinates of
one later-opening QM31 value.  The legal sumcheck augmentation introduces no
fifth direction.

The exact compatible representatives are the following source plus the
listed coefficients times `c0r1,c0r2,c0r3,c0r4`:

| representative | coefficients in M31 |
|---|---|
| `c0r5` | `350845536, 249757693, 1206727637, 1279178930` |
| `c1r1` | `1016364350, 411809830, 1907580655, 220234897` |
| `c2r1` | `1896196302, 418285848, 1665917791, 379859693` |
| `c3r1` | `2024538732, 54457632, 1743708851, 1698678299` |

Before the row-zero exclusion, the same calculation selected
`c0r4,c1r0,c2r0,c3r0` and the same PCS pivot rows.  The shift in representatives
is the decisive guard: the old list did not identify four literal leaking
cells.

## Atomic relation classification

### Row zero

The atomic schedule keeps block zero as the owner-key invocation.  The
terminal initial-state constraints bind all sixteen row-zero lanes to the
owner-key domain/length constant.  Consequently:

- `Delta(c1,r0) = Delta(c2,r0) = Delta(c3,r0) = 0` for every valid
  same-statement witness pair;
- indeed `Delta(c,r0) = 0` for every `c = 0..15`;
- these equalities remove those source vectors, not the quotient classes they
  happened to represent in the old elimination order.

### Owner-key trajectory

The row-zero leading transition absorbs the private nullifier key from the
row-12 payload and applies two pinned Poseidon rounds.  Every following active
row applies its pinned two-round transition.  Thus `c0r4` and the replacement
representatives are neither public constants nor independent cells: they are
coordinates of one deterministic, correlated Poseidon trajectory.

The retained copy registry links the owner-key final digest into the input
note invocation, and the same nullifier key is linked into the nullifier
invocation.  The public statement binds the resulting nullifier and the two
Merkle roots, but it does not publish the intermediate owner-key state.

Therefore the exact classification is:

| source class | exact status |
|---|---|
| row-zero owner-key cells | killed by public-layout constants |
| isolated `c0r4` unit vector | killed by Poseidon transition coupling |
| correlated owner-key trajectory differences | relation-valid when the private key changes, but same-statement reachability is a Poseidon hash-fiber question |
| four-dimensional conservative quotient | not killed by fixed-row, copy, raw-opening, or legal-sumcheck constraints |

### Rejected computational-uniqueness shortcut

If two valid witnesses for one statement differ, follow the two hash
dependency graphs until differing inputs reconverge to an equal public digest.
That produces a collision in an owner/note/nullifier/Merkle/output Poseidon
invocation.  Collision resistance therefore gives computational witness
uniqueness and would make the same-statement difference space zero.

This is useful as a diagnostic reduction, but it is not the selected privacy
claim.  An unconditional HVZK/WI simulator must translate every algebraically
possible valid centre, including hypothetical collision fibers.  The rank
closure must consequently cover the one-QM31 quotient without invoking
collision resistance.

## Root-zero mask controls

The following production-neutral exact-rank candidates were measured on the
same q16 schedule:

| candidate | masked SC rank | selected PCS rank | semantic augmented rank | result |
|---|---:|---:|---:|---|
| add ordinary M31 `L_0^23`, tower rotations 0,1,2,3 | 1080 | 712 | 716 | red |
| add ordinary M31 independent dense-family-17 `L^23`, rotation 0 | 1080 | 712 | 716 | red |
| add full-domain QM31 C2 tail, zero zerocheck coefficient | 1080 | 712 | not run in this mode | rank-neutral |

The shared-power controls all retain semantic PCS pivots 276..279.  The dense
control changes the sumcheck minor but not the selected PCS image or semantic
quotient.  The full-QM31 tail contributes 4,092 M31 source variables and a
3,824-dimensional raw-conditioned kernel, yet the selected PCS rank remains
712.

This is structural.  A separately authenticated root-zero column exposes its
own q-by-four layer-zero values and three terminal values.  After conditioning
those openings, its surviving same-code PCS image is already contained in the
existing full-domain mask image.  Adding column width or trying another tower
rotation does not supply the missing translation.

## Minimal closure obligation

Let `S` be the selected 712-dimensional post-sumcheck mask image and let `D`
be the conservative semantic plus legal-sumcheck image.  The exact replay
proves

```text
dim_M31((S + D) / S) = 4 = dim_M31(QM31).
```

Any unconditional repair needs at least four fresh M31 entropy dimensions
whose conditioned public image has nonzero determinant on pivot rows
276..279.  A proposed repair is accepted only if its exact joint-view replay
returns 716/716 for the conservative semantic target, with no compatibility
or outside-superset remainder.

The measured controls rule out an ordinary independently opened root-zero
column as that repair.  The remaining coherent directions are:

1. a reduced late mask/switch carrying exactly the one-QM31 quotient, with a
   new exact rank, binding and ROM-simulation proof; or
2. a larger code admitting a claim-preserving vanishing blinder, with the
   corresponding degree, fold, transport and MCA proof.

Neither construction is established by this audit.  In particular, the
one-QM31 entropy lower bound must not be reported as a one-column working
construction.

## Source anchors

- Atomic block schedule and trace construction:
  `crates/aspis-statement/src/atomic_state_only_trace.rs`.
- Fixed owner-key initial state and terminal constraints:
  `crates/aspis-statement/src/state_only_semantic.rs` and
  `crates/aspis-statement/src/atomic_state_only_terminal.rs`.
- Two-round transition polynomial:
  `crates/aspis-statement/src/state_only_poseidon.rs`.
- Retained copy and public ingress links:
  `crates/aspis-statement/src/trace_v4.rs` and
  `crates/aspis-statement/src/atomic_state_only_registry.rs`.
- Exact witness-source quotient and concrete projection hook:
  `crates/aspis-prover/src/state_only_hiding_rank.rs`.
- Ordinary-column controls:
  `crates/aspis-prover/src/state_only_hiding_rank/state_only_extra_mask_rank.rs`.
