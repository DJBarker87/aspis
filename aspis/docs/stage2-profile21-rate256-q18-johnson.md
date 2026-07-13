# Profile-21 log-11/q18 Johnson ledger

Date: 2026-07-13

Status: **numerically above 100 bits, but not quotable.** The calculation is
conditional on the exact affine-slice candidate passing its q18 complete-view
rank gate and then landing in the production wire with transcript and mutation
tests. Neither condition may be inferred from this ledger.

## Exact code and theorem scope

The proposed message has 2,048 QM31 coefficients in the direct circle FFT
space `L'_11` and is evaluated on the canonical 524,288-symbol domain
`G'_19`. S-two's basis result gives

```text
L'_11(QM31) subset L_11(QM31),
rho = 2048 / 524288 = 1/256.
```

The full `L_11` code is Hamming-isometric to the corresponding generalized
Reed--Solomon code; restricting to `L'_11` can only shrink lists. The precise
published scope used here is S-two Corollary 1 for the direct subspace,
Theorem 19 for powers-generator correlated agreement/batching, and Lemma 4
for each degree-three arity-four fold. This note does not invoke the refuted
capacity conjecture.

The symbol `m=10` below is S-two's Johnson multiplicity parameter. It is not
the FFT-space subscript 11. Keeping `m=10` gives

```text
alpha = (1 + 1/(2m))*sqrt(rho) = 0.065625,
A = floor(alpha * 131072) = 8601 query fibers,
ell = (m + 1/2)/sqrt(rho) = 168.
```

## Pinned geometry and work

The circle word remains log 19. A query opens one four-symbol fiber, so there
are 131,072 query fibers. The candidate uses q18, with the existing 38-bit
pre-gamma batch work and 38-bit final/query work. The four fold work values
remain `[39,35,31,27]`.

The four output line-code dimensions are, exactly,

```text
512, 128, 32, 8
```

on output domains `131072,32768,8192,2048`. The resulting principal rows are:

| term | proven bits |
|---|---:|
| Theorem-19 batching after g38 | 109.8684871865 |
| exact q18 without-replacement miss after g38 | 108.7588004419 |
| union of four Lemma-4 folds | 112.2344087095 |
| two-sample OOD/list union | 211.0995877009 |

Unioning those rows with the frozen atomic-v3 local terms gives
`107.9367213225` bits before the BCS factor. The sensitivity is:

| BCS factor | system bits |
|---:|---:|
| 31 | 102.9825250121 |
| 33 | 102.8923272031 |
| 40 | 102.6147932276 |

This ledger assumes the affine construction replaces the older X/F/U source
switch. Retaining that switch requires its MCA/query/delta rows to be added
back and the union recomputed.

## Reproduction and promotion gates

The checked arithmetic is in
`crates/aspis-prover/examples/profile21_rate256_q18_johnson_ledger.rs` and the
machine-readable output is
`results/stage2/profile21_rate256_q18_johnson.json`.

```text
cargo run --release -q -p aspis-prover --example profile21_rate256_q18_johnson_ledger
```

Promotion requires all of the following:

1. exact complete-view affine containment on the literal q18 schedule;
2. a new production profile/header and byte-exact transcript KAT binding q18;
3. production prover/verifier parity, adversarial teeth and atomic mutation;
4. a regenerated integrated CU measurement.

Until then `complete_system_claim_quotable` remains false.
