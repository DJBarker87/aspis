# `solmath-zk` candidate crate

Date: `2026-07-11`

Status: **the first `solmath-zk` extraction exists at SolMath commit
`682b5d4`; exact-wide CM31 and M31-circle arithmetic are frozen separately at
SolMath commit `dabc471` while the product gate remains open.** The crate contains only reusable arithmetic
kernels. Aspis protocol choices (PCS basis, range argument, transcript
schedule, proof envelope) remain outside the math crate.

The current `~/solmath` worktree contains extensive unrelated in-progress
changes, so the kernels were prototyped and measured inside Aspis first. The
extraction is a standalone nested workspace at `crate/solmath-zk`, avoiding
changes to SolMath's dirty root `Cargo.toml` and `Cargo.lock`. It is `no_std`,
has zero runtime dependencies, passes 12 unit/differential tests, and passes
`clippy -D warnings`.

## Module boundary

### `field::m31`

- canonical M31 add/sub/mul and full-u64 Mersenne reduction;
- lazy four-product dot reduction;
- branch/shift division by two;
- multiply by powers of two;
- exact canonical parsing.
- checked and explicitly prevalidated M31 batch inversion with an injected
  single-inverse backend.

### `field::tower`

- CM31 and QM31 Karatsuba multiplication;
- specialized CM31/QM31 squaring;
- late-lift `QM31 * M31` and `QM31 * CM31`;
- conjugation and multiply-by-i linear maps;
- lazy `QM31 dot M31`, `QM31 dot CM31`, and `QM31 dot QM31` kernels;
- const-generic `[1, gamma, ..., gamma^(N-1)]` power tables;
- two-level lazy accumulation: four products per Mersenne reduction, then one
  final reduction per output limb;
- prepared const-generic four-slot `QM31 x CM31` dots, including geometric
  preparation returning `gamma^N` and canonical slot-major byte parsing;
- batch inversion with an injected base-field inverse backend.

### `field::circle` (protocol-neutral fold extracted)

- normalized four-point circle-to-line plus line fold over QM31 values;
- caller-supplied, prevalidated `inv(2x)` and `inv(2y)`;
- differential coefficient-evaluation and wrong-slot-order tests.

### circle-domain machinery (still Aspis-local)

- cached omega power table;
- arity-4 layer advance by table shift and fourth powers;
- unit-circle inverse/denominator triple:
  `inv(2s)`, `inv(2*iota*s)`, `inv(2s^2)` without inversion;
- final-domain evaluation cache.

### `poseidon2_m31` (not extracted yet)

- Plonky3-0.6.1-pinned width-16 constants and KAT;
- canonical reference permutation;
- lazy M31 linear layers and power-of-two diagonals;
- domain/length-separated rate-8 sponge.

### `sbf` (future optional feature)

- stack-backed `sol_big_mod_exp` adapter for general M31 inversion;
- host fallback injected by the caller;
- no Solana dependency in the default field crate.

### `merkle`

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
| once-prepared exact 49-CM31 four-slot RLC | include API; protocol decision separate | unprepared q36 exhausts 1.4M; prepared structured diagnostic accepts at 1,125,266 CU |
| canonical-byte exact CM31 dot | include API | 1,066,396 CU, saving 58,870 CU / 5.23% versus prepared structured decoding |
| exact-49 prepared-limb four-row `QM31 x M31` dot | include fixed-shape API; protocol decision separate | tag23 winner 501,989 CU, 54,607 CU / 9.8109% below same-build structured decode and 50,416 CU below one-slot streaming |
| typed sixteen-accumulator `QM31 x M31` dot4 | exclude from chosen SBF path | 734,395 CU, substantially slower from register pressure |
| exact-49 two-row/eight-accumulator byte dot | exclude from chosen SBF path | 504,004 CU at q36, 2,017 CU slower than the 501,987-CU one-row prepared-limb kernel |
| normalized M31-circle first fold and prevalidated batch inverse | include arithmetic APIs; protocol decision separate | tag23 fold control 107,996 CU, including 4,130 CU for one prevalidated 72-denominator syscall-backed batch inverse |

The exact-wide and circle rows are isolated arithmetic diagnostics, not an integrated
payment-proof total. In particular, the CM31 exact diagnostic overlaps the
scalar C1/C2 path in the PCS scaffold, and the M31 candidate requires the
circle-polynomial encoding/fold/OOD changes in
`stage2-column-basis-audit.md`.

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
