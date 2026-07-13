# Profile-21 compact terminal-claim rank

## Verdict

The physically implementable shared-tail compression is soundly batchable,
but it does **not** repair the current hiding deficit. On the exact current
log10, domain-log19, q16 geometry, two separator values both give

```text
shared unused raw                         1204 / 1204 M31
masked zerocheck                         1080 / 1080 M31
selected PCS image                         444
after every active-H difference            444
after conservative semantic differences    448
after legal sumcheck directions             448
```

The four new semantic pivots are `8..11`: one QM31 direction. Reducing the
public opening surface from 84 to 61 QM31 values therefore leaves the same
invariant initial-claim/round-zero obstruction. No mask source, affine lift,
or production wire was added by this probe.

## Exact construction

Split the 28 committed columns into semantic columns `S=0..15` and columns
whose successor/xor values the terminal never reads, `U=16..27`. Before the
batching challenges, publish all three values for each `S` column and only
the `z` value for each `U` column. After sampling `gamma` and `kappa`, publish

```text
A = kappa U_gamma(succ(z)) + kappa^2 U_gamma(xor12(z)),
U_gamma = sum_{j=16}^{27} gamma^j f_j.
```

Only after absorbing `A`, sample a fresh separator `tau`. The one PCS word
and its point weights are

```text
F* = tau^2 S_gamma + U_gamma,
weights = [tau, kappa, kappa^2].
```

The verifier's initial relation target is therefore exactly

```text
tau^3 S_z
+ tau^2 (kappa S_s + kappa^2 S_x)
+ tau U_z
+ A.
```

At each PCS query, columns `0..15` use coefficients
`tau^2 gamma^j`; columns `16..27` use `gamma^j`. This remains one ordinary
combined codeword. Conditional on nonzero `tau`, scaling the first sixteen
input codewords by `tau^2` preserves the code and leaves the polynomial
generator MCA invocation unchanged.

The new challenge must not be called `tau` in production code: profile 21
already serializes a different switch-seam value under the `SWITCH_TAU`
label after round zero. A production design should use a distinct name and
domain-separated transcript label such as `claim_separator`.

## Required Fiat--Shamir order

1. Bind the profile, statement, hiding precommit and both layer-zero roots.
2. Complete the masked zerocheck and derive `z`.
3. Absorb the three points.
4. Absorb the 48 semantic claims and the 12 `U(z)` claims.
5. Check and absorb the existing pre-gamma work nonce.
6. Sample `gamma`, then `kappa`.
7. Absorb the single canonical QM31 `A` under a new label.
8. Sample the fresh exact-uniform QM31 claim separator.
9. Start the ordinary OOD/relation/fold continuation for `F*`.

Sampling the separator before `A`, or omitting it, is unsound: the prover can
choose the aggregate after seeing `gamma,kappa` to cancel false terminal-used
claims. The new prover-message/challenge boundary also raises the current BCS
round factor from 33 to 34 and shifts every later transcript state.

## Collision accounting

Write aggregate claim errors as `e_Sz`, `e_Stail`, `e_Uz`, and `e_A`. Once
`A` has been absorbed, the relation collision polynomial is

```text
E(tau) = tau^3 e_Sz + tau^2 e_Stail + tau e_Uz + e_A.
```

It has at most three separator roots unless all four coefficients vanish.
Before that challenge, the relevant nonzero polynomials have degrees at most
15 for semantic `z`, 17 for semantic successor/xor batching in
`(gamma,kappa)`, and 27 for unused-column `z`. Thus

```text
pre-separator coefficient collision <= 27 / |QM31|,
separator collision                 <=  3 / |QM31|,
local claim binding                 <= 30 / |QM31|.
```

`tau=0` removes the semantic word from the proximity test, so the proximity
reduction separately charges `1/|QM31|`. A conservative ledger row is hence
`31/|QM31|`, replacing the present `29/|QM31|`. Holding every other selected
ledger term fixed gives `107.2883272621` union bits and
`102.2008644208` bits after factor 34. These are sensitivity numbers, not an
integrated claim.

## Consumer audit

The compiled atomic terminal constructs full three-point openings only for
the sixteen semantic columns. It indexes mask-only columns, `H`, and `G` only
at point zero (`z`). The logical switch `U` is not one of the 28 statement
columns: it is disclosed and injected after round zero, then bound by its
separate seam and authenticated q16 equations. Hence the proposed deletion
does not remove a value consumed by a constraint.

## Reproduction

```text
NO_DNA=1 cargo build --release -q -p aspis-prover \
  --example profile21_compact_claim_rank

NO_DNA=1 target/release/examples/profile21_compact_claim_rank \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin 1+u

NO_DNA=1 target/release/examples/profile21_compact_claim_rank \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin 2
```

The compact artifact is
`results/stage2/profile21_compact_claim_rank.json`. The exact shared-A rank
map is
`crates/aspis-prover/src/state_only_hiding_rank/state_only_claim_aggregation_rank.rs`.

## Bound root-zero X/F follow-up (2026-07-13)

Status: **exactly RED** on the log10/domain-log19/q16 compact baseline.

The follow-up removes the old selective-carry caveat. It commits complete
root-zero X/F source words, reveals `U=F+epsilon X`, authenticates all four C2
symbols for both words at every query, and conditions on the exact compact
relation target `tX=L_tau(X)`. X is a third PCS group at
`epsilon gamma^28`; F remains source-only. The X carry contains the complete
unbalanced p0, later-query, OOD, relation-polynomial and final-coefficient
tail under weights `[tau,kappa,kappa^2]`.

Two square source bases were measured:

```text
                              d18 / m2       d19 / m3
variables QM31                   36              38
raw four-symbol opening rank     16              16
rank(U, raw X/F)                 34              35
rank(U, raw X/F, tX)             35              36
conditioned kernel QM31           1               2
compact PCS before              444             444
compact PCS after               444             444
new PCS pivots                    0               0
semantic target                 448             448
```

The folded q-scalar maps have the same ranks and are contained in the raw
four-symbol views; the decisive quotient nevertheless uses the raw views.
Every natural X tail was compared against an independent full-codeword
reference. The reference carries the nonzero copy-inactive target explicitly;
it does not reuse the production zero-inactive constructor. Sparse/dense
parity passed for all 18 and all 19 basis rows respectively.

Thus even d18's unique conditioned QM31 source direction lies entirely in the
rank-444 compact baseline. It does not span any of the four missing semantic
M31 pivots `[5,4,6,7]`. The d19 fallback leaves two conditioned directions,
and both are likewise baseline-contained. Full-X root-zero switching with
these low-degree bases is rejected as a repair for the compact semantic gap.

The exact artifact, commands, fixture hash, basis/minor fingerprints and all
rank fields are in
`results/stage2/profile20_compact_bound_root0_switch_rank.json`.
