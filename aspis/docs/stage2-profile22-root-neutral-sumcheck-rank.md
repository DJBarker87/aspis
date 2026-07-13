# Profile 22 root-neutral sumcheck rank

Date: 2026-07-13

Status: exact reduced-map rank probe implemented.  Neither the selected
factor schedule nor the `G=L_0^23` complete-shared-power candidate reaches
the 1080-M31 legal-wire target in the tested schedules.

## Exact reduction

Let `O_s` be the common K-linear root-opening map and let G have gamma
exponent 27.  For any nonzero gamma, pair a C1 mask table `U_j` at generator
index `j` with

```text
G_j = -gamma^(j-27) U_j.
```

The gamma-combined root message is then identically zero.  If `O_s(U_j)=0`,
K-linearity also gives `O_s(G_j)=0`.  The complete later PCS continuation is
therefore zero without evaluating a PCS minor.

The executable probe performs the following exact M31 eliminations:

1. quotient each C1 lane by its separate 64-symbol plus three-terminal raw
   block (76 M31 coordinates at q16);
2. eliminate G pointwise by the formula above;
3. condition the one shared initial QM31 claim exactly once; and
4. rank the remaining 270 QM31 / 1080 M31 legal sumcheck coordinates.

Semantic lanes use their literal atomic-v3 relation-free source bases.  The
reported H1 diagnostic uses the literal inactive-balanced H1 source paired
with G, but assigns H1 zero direct unmasked-oracle image.  This diagnostic is
the actual H1 image when `theta=mu=0`: the checked terminal identity test
shows that those challenge values remove every H1 contribution to the
unmasked oracle.

## Exact results

| factor schedule | z schedule | mask-only | + semantic kernels | + zero-direct-image H1 | target |
|---|---:|---:|---:|---:|---:|
| selected production | frozen q16 | 976 | 1072 | 1076 | 1080 |
| selected production | affine-degenerate z | 844 | 900 | 912 | 1080 |
| complete shared powers, `G=L_0^23` | frozen q16 | 884 | 1058 | 1062 | 1080 |
| complete shared powers, `G=L_0^23` | affine-degenerate z | 772 | 870 | 882 | 1080 |

The affine-degenerate point is

```text
z = [-(32+i)/9, 1, 1, 1, 1, 1, 0, 1, i, u].
```

It satisfies `sum_(v=0)^8 (9-v) z_v = 0`, making the last-round `L_16`
affine form proportional to `L_0`.

These are full finite-field ranks, not sampled minors.  The
`G=L_0^23` candidate is red in both schedules and is not a root-neutral
repair.

## Guards

Build once:

```text
NO_DNA=1 cargo build --release -q -p aspis-prover \
  --example state_only_hiding_rank_gate
```

Then run the same command with each mode below:

```text
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  <mode>
```

```text
atomic-root-neutral-sumcheck
atomic-root-neutral-sumcheck-bad-affine
atomic-root-neutral-complete23
atomic-root-neutral-complete23-bad-affine
```

The H1 terminal tooth is:

```text
NO_DNA=1 cargo test -q -p aspis-statement \
  zero_theta_and_mu_remove_every_h1_sumcheck_contribution
```

The executable implementation is in
`crates/aspis-prover/src/state_only_hiding_rank.rs`; the CLI modes are in
`crates/aspis-prover/examples/state_only_hiding_rank_gate.rs`; the H1
identity tooth is in
`crates/aspis-statement/src/atomic_state_only_terminal.rs`.
