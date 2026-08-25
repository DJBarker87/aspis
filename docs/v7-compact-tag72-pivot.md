# Aspis V7 compact Tag-72 successor

Date: 2026-08-25  
Baseline: `a6fa6d817e3cf343c8639684e4ab2ce289c40355`  
Status: **selected host profile; SBF and recurrence gates still open**

## Decision

The downloaded split-tensor construction remains useful algebraically, and
its exact 26+3 restriction identity is proved in Rust and Lean.  It is not the
V7 production wire.  The literal three-tree construction measured 36,040
bytes with direct source rows (36,648 bytes with the padded zeta layout).  A
research-only half-domain source still measured 35,016 bytes and loses roughly
eight q16 proximity bits.  All three violate the frozen wire gate before an
SBF implementation is justified.

V7 therefore keeps the frozen V6 width-29/two-tree arithmetic and changes only
the authenticated wire:

- two 216-bit truncated-SHA-256 Merkle trees;
- 16 queries and the same sole arity-four circle-to-line fold;
- a maximum 203-node frontier per tree;
- one verifier-enforced first-success query stream with 64 bounded counters;
- work bits `35 / 31 / 34` for batch/fold/final;
- the full 256-bit private salt for every opened logical leaf; and
- one omitted D value per queried fibre, reconstructed before C2 leaf hashing
  from the exact fold equation.

This is a successor to Tag 72, not a mutation of the frozen V6 release.

## Exact wire census

The fixed V6 field section remains 9,936 bytes.  A V7 query carries:

| Component | Bytes |
|---|---:|
| 26 C1 columns at four M31 fibre positions | 403 |
| H and G at four QM31 positions, plus three of four D values | 171 |
| unchanged shared private salt | 32 |
| **Per query** | **606** |

The maximum proof body is therefore

```text
  9,936  fixed packed fields
     54  two 27-byte roots
     24  three u64 work nonces
  9,696  sixteen 606-byte query records
 10,962  two cap-203 frontiers at 27 bytes per node
-------
 30,672 bytes
```

This is 48 bytes below 30 KiB and 2,664 bytes below the frozen 33,336-byte V6
honest proof.

## Why the omitted value is not an omitted check

Let `L_alpha(v0,v1,v2,v3)` be the maintained V6 fold and let `c_j` be its four
linear coefficients.  Their sum is one, so at least one coefficient is
nonzero.  The verifier deterministically chooses the first nonzero slot `j`.
Because gamma is sampled from nonzero QM31, `c_j * gamma^28` is invertible.
After decoding all disclosed C1/H/G/D values and evaluating final256 at the
query, it reconstructs

```text
D_j = (expected - L_alpha(partial)) / (c_j * gamma^28).
```

It then serializes all twelve logical C2 values, including `D_j`, and hashes
that complete leaf against the pre-gamma C2 root.  Thus the same committed
value and the same fold equality are checked; only its redundant wire encoding
is removed.  `V7CompactOneFold.lean` proves the generic field reconstruction
identity and specializes it to the deployed QM31 tower.  Focused Rust tests
exercise the maintained fold implementation over randomized field values.

The verifier hot path prepares the 29 gamma powers and the three alpha
multipliers once for all sixteen queries.  It evaluates the fold coefficients
from the direct cubic expansion, checked against the maintained butterfly
implementation, and batch-inverts all sixteen nonzero reconstruction
denominators with one QM31 inversion.  This is an arithmetic scheduling
optimization only: the reconstructed value and the full committed leaf are
unchanged.

## Query availability and work

The exact candidate numerator for cap 203 is

```text
2168847668270364480248463894820533103335517458992692508721007794996625408
```

out of

```text
23758572837246225120935263320500846372979925468707821836403823401582444544.
```

One candidate is therefore favourable with probability above 9%.  Under the
named independent-candidate random-oracle interface, 64 candidates fail with
probability below 1/400.  Even charging a conservative `400/399` retry factor,
expected honest work is below 1.5 times V6.  The verifier accepts only the
first favourable counter, so counters do not create a proof-chosen union
factor.

The pinned numerator gives an exact conditioned q16-plus-final-work term of
about `2^-107.0065`.  With exact published initial/fold caps, one selector
stream and the inherited local terms, Lean proves that the BCS core uses less
than half of the `2^-100` budget.  The favourable numerator is still marked as
a candidate boundary until the generated binary-frontier recurrence replay is
complete.

## Remaining release gates

The selected profile is not yet a devnet or release result.  It still requires:

1. generated cap-203 frontier recurrence provenance on the NUC;
2. a 216-bit Merkle implementation and explicit truncated-SHA-256 binding
   interface (generic classical collision strength: 108 bits);
3. the compact parser/prover and reconstruction-before-hash source bridge;
4. a focused SBF CU measurement below 1.3M (hard stop at 1.35M);
5. complete hiding composition retaining the 256-bit paired salts;
6. adversarial position coverage and reproducible SBF build; and
7. one atomic devnet lifecycle with exact simulation/landing agreement.

No mainnet deployment is authorized by this document.
