# Profile-21 log-12/q20 Johnson ledger

Date: 2026-07-13

Status: **numerically above 100 bits, but not quotable.** This ledger is the
soundness target for the two-variable masking fallback. It does not assert
that the fallback passes complete-view rank or that a q20 production wire
exists.

The primary candidate fixes the two slice coordinates to `c=2,d=3 in M31`.
Extension-field slice coordinates are out of scope unless a separate
duplicate-lift subcode check is added.

## Exact code and theorem scope

The proposed message space has 4,096 QM31 coefficients in the direct circle
FFT space `L'_12`, evaluated on the existing 524,288-symbol domain `G'_19`:

```text
L'_12(QM31) subset L_12(QM31),
rho = 4096 / 524288 = 1/128.
```

The ledger uses S-two Corollary 1 for the direct subspace, Theorem 19 for the
powers-generator batch, and Lemma 4 for each degree-three arity-four fold. It
uses only the Johnson regime and does not invoke a capacity conjecture.

With S-two multiplicity parameter `m=10`, which is unrelated to the message
log 12,

```text
alpha = (1 + 1/(2m))*sqrt(1/128) = 0.092807765030734,
A = floor(alpha * 131072) = 12164 query fibers.
```

The candidate uses q20, 38 bits of pre-gamma batch work, and 38 bits of
query/final work. The four folded output dimensions are exactly
`[1024, 256, 64, 16]` on domains `[131072, 32768, 8192, 2048]`.

| term | proven bits |
|---|---:|
| Theorem-19 batching after g38 | 111.3684864911 |
| exact q20 without-replacement miss after g38 | 106.6138533153 |
| union of four Lemma-4 folds | 113.1210883033 |
| two-sample OOD/list union | 209.0993716764 |

Unioning those rows with the frozen atomic-v3 local terms gives
`106.4808520136` bits before the BCS factor. The sensitivity is:

| BCS factor | system bits |
|---:|---:|
| 31 | 101.5266557033 |
| 33 | 101.4364578943 |
| 40 | 101.1589239188 |

The OOD calculation uses root caps `[4096, 1023, 255, 63]` and the existing
conservative list cap 240. The local union assumes that this construction
replaces the older X/F/U source switch; retaining that switch requires adding
its terms and recomputing the union.

## Base-field statement reduction

The rate calculation is over QM31, but the committed C1 word is received in
M31. This restriction is compatible with the ambient circle/GRS proof. Undo
the S-two monomial isometry before applying Frobenius: on the canonical circle
domain the rational parameters and the nonzero coordinate multipliers are in
M31, so permutation and unscaling preserve the fact that every received C1
symbol lies in M31.

Let `f` be an ambient decoded polynomial of degree at most 4,096. On its
common Johnson agreement set, `f(t)` is M31-valued. The set has approximately

```text
0.092807765 * 2^19 = 48658
```

positions, far more than the degree bound. Since every evaluation point `t`
is Frobenius-fixed, the coefficientwise Frobenius difference
`f^(M31)-f` vanishes on that set. It is a polynomial of degree at most 4,096,
so it is identically zero. Thus `f` is M31-defined. The inverse circle/GRS
basis map is also M31-linear, and restricting its two new tensor coordinates
at `c=2,d=3` yields an M31 logical coefficient vector.

Consequently an accepted extended C1 word projects to an ordinary M31
ten-variable witness word. Kernel components of the two slice maps do not
enlarge the projected statement: all semantic, copy and terminal constraints
must be evaluated on that same projection. This is the implementation
conformance obligation for the two-variable agent; using a non-M31 slice
would invalidate the reduction.

## Reproduction and promotion gates

The arithmetic and frozen output are:

- `crates/aspis-prover/examples/profile21_rate128_q20_johnson_ledger.rs`
- `results/stage2/profile21_rate128_q20_johnson.json`

The example has no crate dependencies and can be checked directly:

```text
rustc --edition=2021 \
  crates/aspis-prover/examples/profile21_rate128_q20_johnson_ledger.rs \
  -o /tmp/profile21_rate128_q20_johnson_ledger
/tmp/profile21_rate128_q20_johnson_ledger
```

Promotion requires exact q20 complete-view containment for the two-variable
construction, a distinct production profile/header with byte-exact transcript
KAT, production prover/verifier and adversarial parity, and an integrated CU
measurement. Until all gates pass, `complete_system_claim_quotable` remains
false.
