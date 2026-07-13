# Radix-8 minimal-subtree candidate

Status: isolated core candidate; not part of a proof header, root, transcript,
program instruction, or production profile.

## Exact commitment semantics

An eight-child parent is

```text
SHA256(0x13 || child[0] || ... || child[7]).
```

The domain byte is distinct from Aspis binary (`0x11`) and radix-4 (`0x12`)
parents. A radix-8 root is therefore a new commitment and cannot reinterpret
an existing proof. The minimal-subtree frontier is consumed level-by-level,
then ascending parent index and child slot. Every entry must be sorted,
unique, and in range; the verifier rejects missing, extra, or partial hashes.

The pure radix-8 API requires the binary tree depth to be divisible by three.
It directly covers the profile-15 depth-12 C1/C2 trees and depth-6 later tree,
but not the depth-10 and depth-8 later trees. Those would require an explicitly
specified hybrid-arity tree rather than padding or silently truncating levels.

## q36/depth12 geometry

Let `N = 4096` leaves and sample `q = 36` distinct indices uniformly without
replacement. For arity `b`, level `l`, and group size `s = b^l`, the exact
expected number of occupied parents is

```text
P_l = (N/s) * (1 - choose(N-s, q) / choose(N, q)),   P_0 = q.
```

The expected number of frontier hashes consumed at that level is

```text
F_l = b * P_l - P_(l-1).
```

Applying those formulas gives:

| geometry | radix-4 | radix-8 | radix-8 delta |
| --- | ---: | ---: | ---: |
| occupied parent hash calls | 116.554 | 71.661 | -44.893 (-38.5%) |
| frontier hashes | 314.662 | 466.630 | +151.968 (+48.3%) |
| frontier bytes | 10,069 | 14,932 | +4,863 |
| parent preimage bytes | 15,035 | 18,417 | +3,382 |
| SHA-256 compression blocks | 349.662 | 358.307 | +8.645 (+2.5%) |

The compression-block row counts three blocks for a 129-byte radix-4 parent
and five for a 257-byte radix-8 parent, including SHA-256 padding. Thus
radix-8's possible SBF saving comes only from fewer syscall/base/traversal
charges; it does slightly more compression work and substantially increases
the frontier.

The fixed collision-free q36 fixture in
`crates/aspis-core/tests/radix8_merkle.rs` gives an exact same-indices A/B:

| fixed fixture | radix-4 | radix-8 |
| --- | ---: | ---: |
| parent hashes | 112 | 72 |
| frontier hashes | 301 | 469 |
| frontier bytes | 9,632 | 15,008 |
| parent preimage bytes | 14,448 | 18,504 |
| SHA-256 compression blocks | 336 | 360 |

## Correctness guard

The isolated tests use:

- an independent direct-SHA parent implementation;
- an independent full-tree builder and prover-side frontier emitter;
- a map-based reference verifier that does not call the production helper;
- fresh deterministic query sets at depths 3, 6, 9, and 12;
- wrong-root, frontier mutation, leaf mutation, truncation, extension,
  partial-hash, noncanonical-order, duplicate-index, out-of-range, and invalid-
  depth rejection vectors.

No CU claim follows from host geometry. The next admissible step is an
append-only SBF instruction comparing radix-4 and radix-8 on the exact same
q36/depth12 indices. Production integration would additionally require new
roots, proof framing, transcript binding, prover support, and corruption KATs.
