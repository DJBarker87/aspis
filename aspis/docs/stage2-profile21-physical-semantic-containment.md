# Profile-21 physical semantic containment correction

Date: 2026-07-13

Status: **GREEN on the frozen atomic-v3 q16 schedule; all-schedule proof still
open.**  The historical 712-to-716 semantic quotient was an artifact of
mixing two different source maps.  With the exact physical balancing map,
the existing selected mask image contains every tested semantic source and
every legal zero-initial-claim sumcheck direction at rank 712/712.  No X lane
is needed to repair that discarded quotient.

## Physical source map

`apply_mask_material_for_layout` overwrites one copy-inactive dependent row
`d_c` in each semantic column after adding its relation-free masks.  The
linearized physical centre map is therefore

```text
B_c(e_r) = e_r                 if r is copy-active,
B_c(e_r) = e_r - e_d_c         if r is copy-inactive and r != d_c,
B_c(e_d_c) = 0.
```

The owner-key pre-absorb row zero is fixed and is not a same-statement source.
Raw openings, terminal values and the complete PCS tail must all use `B_c`.
With the global cached row maps, an inactive source tail is exactly
`rows[r].pcs_tail-rows[d_c].pcs_tail`; an active source tail is
`rows[r].pcs_tail`.

The rank gate now keeps this physical source explicit.  Its caller-supplied
projection hook rejects a nonzero row-zero difference or nonzero
copy-inactive sum instead of silently canonicalizing an invalid input.  A
separately labelled unbalanced `e_r` control may be used only as a stronger
upper-oracle stress test; it never defines the physical containment verdict.

## Exact replay

```text
NO_DNA=1 target/release/examples/profile21_good_schedule_probe witness-actual \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin
```

Result:

```text
query count                                      16
masked-sumcheck rank                           1080 M31
selected PCS rank                               712 M31
declared PCS rank                               780 M31
physical semantic generators                 16352 M31
physical semantic augmented rank            712/712 M31
legal sumcheck generators                      1080 M31
legal sumcheck augmented rank                712/712 M31
compatibility rank                                4 M31
compatibility pivot sources                 [1,2,3,4]
semantic complement sources                        []
semantic complement pivots                         []
legal-sumcheck complement pivots                    []
elapsed                                      131614 ms
```

Frozen fingerprints from that replay are:

```text
post-sumcheck selected PCS minor       0xd9fee7f131428560
empty physical semantic minor          0xa8a5087704e77d8e
empty legal-sumcheck minor             0xf1cb19f589cc5dd5
physical sparse/dense projection       0xa1e218dad3c9dadc
```

The separately labelled, nonphysical unbalanced upper-oracle control is
internally coherent but RED at 712-to-716. It has 16,368 generators, pivots
`1084..1087`, minor fingerprint `0x10e1ad3101bf3619`, and sparse/dense
fingerprint `0xeacd5445471c7bf7`. This does not weaken the physical result:
inactive `e_r` alone is not emitted by the production balancing map. The
separate labels prevent that stronger ambient failure from being mistaken for
a same-statement leakage class again.

The full-native-X A/B was also run:

```text
NO_DNA=1 target/release/examples/profile21_good_schedule_probe nativefull-actual \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin
```

It retains rank 712 before X, after the complete 959-`QM31` conditioned X
kernel, and after the physical semantic/legal augmentation.  X contributes
no pivot.  Its observation rank is 65 over `QM31`; its exact run took 189850
ms.  This establishes that X is unnecessary for this fixed-schedule target,
not that X repaired it.

## Root cause and negative tooth

The old semantic loop used the raw image of `e_r` but, on copy-inactive rows,
paired it with a cached PCS image of `e_r-e_d`.  The concatenation had no
single underlying message.  Elimination nevertheless produced four M31
pivots at rows 276--279, later localized to the early-`p0.c4` boundary class.
Those rows were properties of the spliced matrix, not a physical leakage
class.

The old concrete projection built from `c0r5,c1r1,c2r1,c3r1` and the former
compatibility coefficients now fails `compatibility_kernel`.  That failure is
the required negative tooth: stale representatives cannot pass the corrected
physical projection API.

## Scope boundary

This result closes the specific fixed-q16 712-to-716 fork.  It does not prove
containment for every parser-valid query schedule, the private-Merkle/EPRO
hybrid, Fiat--Shamir programming, atomic mutation, or the final CU total.
Every rank artifact derived from the old semantic source loop—including
extra-factor, variable-permutation, affine-slice and compact repair screens—
must be treated as stale until replayed or shown not to depend on that loop.
