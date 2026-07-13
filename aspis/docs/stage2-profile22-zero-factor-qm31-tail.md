# Profile 22 zero-factor QM31 tail

Date: 2026-07-13

Status: **minimal frozen-schedule conditional rank bridge is green; universal
rank theorem is red on two explicit controls; production remains unchanged.**

## Exact candidate

Keep every production generator index unchanged and append one full-domain
QM31 lane `D`:

```text
C1 semantic/mask-only       generators 0..25
H                           generator 26
G                           generator 27
D, factor(D)=0              generator 28
```

For the root-neutral source restriction, after the nonzero `gamma` is fixed,
pair a D difference with

```text
delta_G = -gamma * delta_D.
```

Then pointwise

```text
gamma^27 delta_G + gamma^28 delta_D = 0.
```

The direct D mask factor is zero, so its effective compressed-sumcheck image
is exactly `-gamma F_G D`.  This is the valid zero-direct algebra suggested
by the old idealized-H diagnostic, but it does not alter H1 or suppress H1's
witness-dependent direct term.

This pairing is a post-challenge source-space argument, not a prover choice
of G after gamma.  In a real construction G and D are independently masked
and committed before gamma; the proof of view containment may combine their
source directions after conditioning on the public nonzero challenge.

## Correct conditional target

The compressed sumcheck wire has 1,084 M31 coordinates.  Fixing its initial
QM31 claim and its verifier-recomputed terminal QM31 value leaves

```text
dim ker(initial,T_z) = 1084 - 4 - 4 = 1076 M31.
```

The probe quotients every source by its exact separate raw block, verifies
that every surviving sumcheck image has terminal zero, then conditions the
initial claim once and ranks the remaining image.  D's separate q16 plus
three-terminal raw block has exact rank 268 M31.

An independent H1 padding translation guard uses exactly the inactive rows,
balanced against the global dependent row, over all four tower coordinates.
It also has rank `268/268`: 256 q limbs plus 12 terminal limbs.  This replaces
the old idealized-H diagnostic's over-wide 304-row allocation and proves that
the physical inactive H1 raw difference can be translated before applying
the D/G root cancellation.

## Exact three-schedule screen

| schedule | baseline | with D | target | D raw | terminal guard | minor fingerprint |
|---|---:|---:|---:|---:|---:|---:|
| frozen profile-22 fixture | 1,072 | **1,076** | 1,076 | 268 | true | `0xcc3e3f3feeac0dbb` |
| terminal-certificate `z=[1,1,1,1,1,1,0,1,i,u]` | 748 | 786 | 1,076 | 268 | true | `0x42e4e7e860fa7ad0` |
| documented affine-degenerate point | 900 | 912 | 1,076 | 268 | true | `0xfe338a9a49ff661d` |

Every run checks 17,324 post-raw M31 sources against the exact compressed
terminal functional.  Thus D is the minimum frozen-schedule bridge, but the
two controls refute any claim that this one lane makes the root-neutral map
surjective for every parser-valid z.  Those red schedules may still be
handled by a separately proved retry/selection liveness argument; they
cannot be erased from the theorem.

The integration-valid one-M31-before-H/G control also reaches 1,076 on the
frozen schedule, but shifts H/G and reaches only 750 from a 748 baseline on
the terminal-certificate point.  The QM31 tail is strictly cleaner: it keeps
the production indices frozen and supplies all four tower coordinates
without a gamma-basis condition.

## Wire and cost shape

One D lane changes the hypothetical wire by:

```text
C2 leaf width                       128 -> 192 bytes
q16 four-slot QM31 values                  1,024 bytes
three terminal QM31 values                    48 bytes
serialized proof increment                  1,072 bytes
fixture-size projection           56,686 -> 57,758 bytes
outer generator width                  28 -> 29
```

No integrated verifier measurement exists yet.  Prior measurements give two
planning screens only:

```text
optimistic:  60,968/3 + 1,027/2 + 1,832 + 5,000 ~= 27,668 CU
conservative: 60,968 + 1,027 + 1,832 + 5,000       = 68,827 CU
```

Here 60,968 CU is the entire measured fused three-QM31-lane q16 helper,
1,027 CU is a measured 128-byte shared-C2 widening, 1,832 CU is the entire
current parser, and 5,000 CU is handling reserve.  Neither formula is an
integrated measurement of D.  Both are below the exact 230,286-CU
System-create headroom, which makes integration worth measuring.

## Soundness and degree bookkeeping

`factor(D)=0` does not increase the degree-26 mask-factor ceiling.  The
nonzero scalar `-gamma` does not change the D image rank, so the local
root-neutral rank statement does not require choosing a gamma basis or
clearing a negative gamma power.  Adding D does add one separately
authenticated 268-M31 raw block and raises the generator width to 29.

The old `41040` raw-plus-sumcheck degree ledger does not transfer silently.
A promoted profile needs a new fixed joint minor, raw/query degree count,
layout/factor fingerprint, MCA numerator, and full soundness union.  The
frozen nonzero minor above proves only one schedule.

## Reproduction

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile22_zero_factor_qm31_tail \
  zero_factor_tail_pairing_is_pointwise_root_neutral

NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile22_zero_factor_qm31_tail \
  zero_factor_qm31_tail_closes_only_the_frozen_control \
  -- --ignored --nocapture

NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_zero_factor_root_neutral
```

## Promotion obligations

The next nondefault revision must, atomically:

1. sample D from fresh private mask entropy and include it in the pre-gamma
   C2 commitment;
2. serialize/authenticate D at q16 and all three statement points;
3. include generator 28 in gamma recombination and every fold/opening path;
4. keep `factor(D)=0`, so D never enters H's mask-oracle evaluation;
5. bind a new layout/profile fingerprint and fail closed across old/new tags;
6. rerun transcript, differential, corruption, privacy, and CU measurements;
7. prove a liveness theorem or retain a bounded fail-closed schedule gate.

Until those steps are complete, this file describes a host-only bridge, not
an accepted production proof.
