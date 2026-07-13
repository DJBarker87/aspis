# Profile-21 no-switch source audit

Date: 2026-07-13

## Verdict

The 68-M31 baseline deficit is not an impossible copy-helper `H` space.  It
is already present in the gamma-combined message tail before any independent
`H`-padding directions are added.

The existing `baseline_valid_witness_containment=true` flag proves the
complete-view containment of active, zero-sum `H` differences.  It does not
insert semantic trace differences and therefore does not prove containment
for every honest same-statement witness difference.

Consequently the current evidence does not justify removing `X/F/U/tau`.
They can be removed without replacement only after proving the narrower
semantic-source containment theorem stated below.

## Exact q16 decomposition

The existing release rank replay was run on the exact atomic-v3 profile-20
fixture and transcript schedule:

```text
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile20_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-baseline-full-shared
```

It returned:

```text
pre-helper selected PCS rank                  444 M31
declared combined-message rank                512 M31
deficit before H                               68 M31

selected rank after inactive-H masks          712 M31
declared rank after inactive-H space           780 M31
deficit after inactive H                        68 M31

rank after all active zero-sum H differences   712 M31
```

Inactive `H` therefore contributes the same 268-M31 increment to both sides.
Every active zero-sum helper direction is already contained and contributes
no new pivot.  The missing quotient has dimension 68 over M31, or 17 over
QM31.  The existing switch diagnostic classifies it as 64 later-opening M31
coordinates plus four relation-polynomial M31 coordinates; it has no OOD or
final-coefficient pivot.

## Production source classification

Let `I` be the atomic-v3 copy-inactive rows and define

```text
V = { w in QM31^1024 : sum_(r in I) w[r] = 0 }.
```

The production sources are:

| Source | Witness-dependent centre? | Exact source space/invariant | Current containment status |
|---|---:|---|---|
| Semantic `C_0..C_15` | yes | Each committed M31 column is rebalanced so its sum on `I` is zero. A same-statement centre difference may alter non-maskable trace cells but still lies in the corresponding M31 slice of `V`. | **Not covered by `baseline_valid_witness_containment`.** |
| Mask-only `M_0..M_9` | no | Full-domain M31 randomness, rebalanced on `I`. | Part of the selected mask image. |
| Explicit `G` | no | Full-domain QM31 randomness, rebalanced on `I`. | Part of the selected mask image. |
| Unpadded copy helper `H_base` | yes | Copy-inactive rows are empty and hence zero. Each honest helper has total sum zero, so every honest difference is supported on active rows and has sum zero. | Universally contained by the active-helper augmentation tooth. |
| Helper padding `H_pad` | no | Arbitrary QM31 values on inactive rows with zero inactive sum. | Explicit selected mask source. |
| Merkle salts/roots | no witness centre in the field-rank model | Private independent salts; roots and unopened nodes belong to the ROM simulation rather than this affine field matrix. | Separate EPRO/ROM obligation. |

The production combined message is

```text
W = sum_(j=0)^15 gamma^j C_j
  + sum_(k=0)^9 gamma^(16+k) M_k
  + gamma^26 H
  + gamma^27 G.
```

All four source families obey the inactive-sum invariant, so `W` lies in
`V`.  The incremental PCS relation rejects any `W` outside `V`.

The rank gate first quotients the separately authenticated layer-zero and
terminal values, then the full 1080-M31 masked-sumcheck quotient.  Its
`declared_combined_rank=512` is the exact image of `V` in the remaining PCS
tail.  The selected no-switch masks span only 444 of those M31 directions.
The independent `H` source is added afterwards, which is why it cannot be the
cause of the 68-dimensional gap.

## What the current containment flag proves

The implementation constructs `augmented` by adding

```text
H image(e_row - e_active_dependent)
```

for every active row, in all four tower coordinates.  Equality of its rank
with the selected rank proves containment of the complete public image of
every active zero-sum helper difference.  The image includes `H` layer-zero
openings, all three terminal values, later openings, OOD values, relation
coefficients and final coefficients.

No semantic `C_j` witness-difference column is appended in this test.  The
boolean name is therefore broader than the theorem implemented by the code.

## Source-level counterexample to the helper explanation

Let `S` be the selected no-switch image after quotienting raw openings and the
masked sumcheck, and let `A: V -> View_tail` be the combined-message PCS map.
The measured dimensions give

```text
dim_M31(A(V) / (A(V) intersect S)) = 512 - 444 = 68.
```

Choose any `w in V` whose image has a nonzero class in this quotient.  Set the
abstract source difference to

```text
Delta C_0 = w,
Delta C_j = 0 for j>0,
Delta H = Delta M_k = Delta G = 0.
```

Because the coefficient of `C_0` is `gamma^0=1`, the combined-message shift
is exactly `w`.  This source respects the mandatory inactive-sum relation and
is not an `H` direction, yet it is not contained in the selected image.

This is a source-space/rank-model counterexample, not an exhibited pair of
valid payment witnesses.  It refutes the claim that the deficit is excluded
by the copy-helper invariant.  Ruling it out for the language requires a new
theorem about the coupled semantic trace differences of valid witnesses.

## Exact theorem needed for the no-switch route

For every accepted public statement `s`, every two valid witnesses `w,w'`,
and every accepted public schedule, let `Delta_sem(s,w,w')` be the complete
field-view difference contributed by:

1. the 16 rebalanced semantic C1 columns;
2. the change in the original zerocheck oracle and its ten-round transcript;
3. the induced unique copy helper before independent inactive padding; and
4. the gamma-combined PCS tail, including all later openings, OOD values,
   relation polynomials and final coefficients.

The missing theorem is

```text
Delta_sem(s,w,w') is in Image(M_selected(schedule)).
```

It must be proved for every same-statement valid witness pair, or under a
precisely bounded public-schedule `Good` predicate.  Showing only that the
combined word lies in `V`, or only that helper differences are zero-sum, is
insufficient because the 68-dimensional quotient lies inside `A(V)`.

## When X/F/U/tau may be deleted

If the semantic-source theorem above is proved, full ambient rank is stronger
than necessary.  In that case the 68 missing directions are unreachable by
an honest centre shift, and the external switch exists only to one-time-pad
irrelevant ambient directions.  Then the complete `X/F/U/tau` carry can be
removed rather than replaced:

- remove the X/F source lanes and their commitment/openings;
- remove `xi`, `U` and the derived `tau` transcript records;
- leave the original width-28 `C/M/H/G` relation and opening checks intact;
- retain the private-Merkle ROM simulation, EPRO ledger, canonical PoW,
  retry/fixed-release policy and the all-schedule source-containment proof.

Until that theorem exists, deleting the switch leaves a measured 17-QM31
semantic-message quotient unaccounted for and is not a privacy closure.

## Source anchors

- Mask-only/G/H-padding sampling and inactive balancing:
  `crates/aspis-prover/src/state_only_hiding.rs:340`.
- Semantic mask application and per-column inactive rebalance:
  `crates/aspis-prover/src/state_only_hiding.rs:443`.
- Width-28 gamma combination and relation construction:
  `crates/aspis-prover/src/state_only_proof.rs:308`.
- Mandatory combined inactive-sum check:
  `crates/aspis-prover/src/state_only_circle_relation.rs:62`.
- Exact ambient combined-message construction:
  `crates/aspis-prover/src/state_only_hiding_rank.rs:3104`.
- Active-helper-only containment tooth:
  `crates/aspis-prover/src/state_only_hiding_rank.rs:3143`.
