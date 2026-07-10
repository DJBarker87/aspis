# `solmath-zk` candidate crate

Date: `2026-07-10`

Recommendation: **yes, build `solmath-zk`, but extract only measured reusable
kernels.** Keep Aspis protocol choices (range argument, transcript schedule,
proof envelope) outside the math crate.

The current `~/solmath` worktree contains extensive unrelated in-progress
changes, so the kernels were prototyped and measured inside Aspis first. This
avoids silently mixing a new crate into unfinished SolMath work. Once the APIs
below stabilize, they can move into a standalone no_std, zero-default-
dependency crate.

## Proposed modules

### `field::m31`

- canonical M31 add/sub/mul and full-u64 Mersenne reduction;
- lazy four-product dot reduction;
- branch/shift division by two;
- multiply by powers of two;
- exact canonical parsing.

### `field::tower`

- CM31 and QM31 Karatsuba multiplication;
- specialized CM31/QM31 squaring;
- late-lift `QM31 * M31` and `QM31 * CM31`;
- conjugation and multiply-by-i linear maps;
- lazy `QM31 dot M31`, `QM31 dot CM31`, and `QM31 dot QM31` kernels;
- const-generic `[1, gamma, ..., gamma^(N-1)]` power tables;
- two-level lazy accumulation: four products per Mersenne reduction, then one
  final reduction per output limb;
- batch inversion with an injected base-field inverse backend.

### `circle`

- cached omega power table;
- arity-4 layer advance by table shift and fourth powers;
- unit-circle inverse/denominator triple:
  `inv(2s)`, `inv(2*iota*s)`, `inv(2s^2)` without inversion;
- final-domain evaluation cache.

### `poseidon2_m31`

- Plonky3-0.6.1-pinned width-16 constants and KAT;
- canonical reference permutation;
- lazy M31 linear layers and power-of-two diagonals;
- domain/length-separated rate-8 sponge.

### `sbf` (optional feature)

- stack-backed `sol_big_mod_exp` adapter for general M31 inversion;
- host fallback injected by the caller;
- no Solana dependency in the default field crate.

### `merkle` (optional)

- fixed-preimage packed SHA node helper;
- binary and radix-4 minimal-subtree traversal with caller-supplied hash
  backend and scratch buffers.

## Measured inclusion decisions

| candidate | decision | evidence |
| --- | --- | --- |
| M31 syscall inverse | include optional SBF adapter | ~72% per-call saving |
| specialized QM31 square | include | ~19% per-call saving |
| lazy Poseidon2 linear layer | include | 66,830 CU saved over 49 permutations |
| cached circle powers | include | part of 229,861-CU binary PCS saving |
| conjugate fold denominators | include | 100,189 CU saved in same-build PCS comparison |
| lazy raw-M31 RLC dot | include | 159,932 CU saved at q36/k80 |
| fixed `QM31` power table | include | heap-backed 220,386 -> stack-backed 202,031 CU |
| radix-4 minimal subtree | include optional Merkle module | 35,704 CU saved in literal g32 PCS; corruption-tested |
| packed-pair/four RLC | exclude from chosen SBF path | algebraically sound but slower |
| whole-dot u128 accumulator | exclude | much slower on SBF |
| per-query Horner RLC | exclude | over 1.09M CU at q36/k80 |

## API discipline

- Every optimized function ships beside a simple reference implementation or
  differential test.
- SBF numbers are instruction-level deltas on a pinned validator version, not
  host benchmarks.
- Protocol security labels do not live in this crate. The crate supplies
  arithmetic; callers own transcript order, domain separation, challenge
  fields, and soundness accounting.
- Optimizations that change roots or proof bytes require caller-side KAT and
  corruption workflows. The math crate must never silently re-pin them.
