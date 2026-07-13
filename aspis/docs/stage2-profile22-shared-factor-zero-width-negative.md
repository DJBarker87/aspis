# Profile-22 shared-factor zero-width repairs: negative evidence

Date: 2026-07-13

Status: exact host-only frozen-schedule probes complete; production unchanged.

## Outcome

Two zero-width factor edits preserve the existing 16 semantic M31, 10
mask-only M31, and one QM31 G source lanes.  Neither closes the exact
Profile-22 hiding image.

1. Moving semantic lane 13 from shared degree 26 to missing degree 23 makes
   the 26 M31 lanes cover degrees 0 through 25 exactly and leaves production
   G to supply degree 26.  Ordinary raw-quotiented sumcheck rank is full, but
   the literal direct-sum target remains four dimensions outside the mask
   image and D=0 rank remains eight short.
2. Keeping every factor unchanged and enriching the same existing G factor
   to `1 + L_16^26 + L_0^d` gives exactly the same D=0 rank for every
   `d=0..26`.  No exponent qualified for the gated literal-containment run.

No commitment leaf, source count, proof byte, gamma position, generator
width, transcript, verifier predicate, or production factor fingerprint was
changed.

## Frozen object

- proof: `results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin`
- statement digest:
  `52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9`
- query count: 16
- factor mode: full shared `L_0` M31 factors; production-shaped
  `G=1+L_16^26`

## Shared degree-cover result

The frozen semantic exponents are

```text
0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25.
```

The host schedule changes only entry 13 from 26 to 23.  Together with the
ten frozen odd mask-only exponents, the M31 factors then cover degrees
`0..=25` exactly.  G's degree-26 leading coefficient is nonzero in every
round, independently of affine offsets.

Exact frozen ranks:

| object | rank | target/result |
|---|---:|---:|
| raw opening minor | 2244 | full |
| ordinary raw-quotiented sumcheck | 1080 | 1080 |
| joint PCS | 712 | 780 |
| literal mask direct-sum view | 4036 | baseline |
| physical augmented direct-sum | 4040 | not contained |
| legal augmented direct-sum | 4040 | not contained |
| root-neutral mask-only image | 976 | - |
| root-neutral legal image | 1072 | 1080, not complete |
| idealized-H1 root-neutral image | 1076 | 1080 |

The complete-view replay took 81,104 ms and the root-neutral replay 16,053
ms while both ran concurrently.  These timings describe the host rank
diagnostic, not verifier CU.

The frozen necessary conditions are red, so consecutive, same-coset,
affine-degenerate, and terminal-certificate schedules were not run.

## Same-lane G shared-power scan

The second host schedule keeps all production-shaped factors and changes
only

```text
G(z) = 1 + L_16(z)^26
```

to

```text
G_d(z) = 1 + L_16(z)^26 + L_0(z)^d,
```

on the same existing QM31 G source.  The coefficient was fixed to one and
the bounded scan covered every `d=0..26`; no coefficient or subset search
was performed.

Every one of the 27 exact replays returned

```text
root-neutral legal rank = 1072 / 1080
mask-only rank          = 976
complete                = false
```

The predeclared first case `d=23` took 16,113 ms alone.  The complete scan
used four parallel host eliminations, so individual reported times
26,338--39,525 ms are CPU-contended and must not be read as performance
measurements.

The invariant rank is consistent with the added shared term being absorbed
by the existing shared-factor source image.  The scan is finite exact
evidence; it is not promoted here to an all-source algebraic theorem.

Because no exponent reached 1080, no literal direct-sum containment replay
was run for this family.

## CU implications

Neither candidate is eligible for integration or an end-to-end CU claim.

The degree-cover edit retains the shared power table.  A specialized
evaluator could stop the `L_0` chain at degree 25 rather than 26, potentially
saving one QM31 multiplication per factor-evaluation point; production G
still requires the separate `L_16^26` chain.  This is marginal and was not
SBF-measured because the candidate is algebraically red.

For the same-lane G enrichment, every `L_0^d` is already present while the
shared table is built through degree 26.  The incremental verifier work is
therefore one QM31 addition at each G-factor evaluation, with no extra leaf,
opening, generator, or generic multiplication.  Again, it cannot be adopted
because D=0 remains `1072/1080`.

## Reproduction

Build the host gate:

```bash
NO_DNA=1 cargo build --release -q -p aspis-prover \
  --example state_only_hiding_rank_gate
```

Frozen degree-cover gates:

```bash
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-shared-degree-cover

NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-root-neutral-shared-degree-cover
```

For a same-lane G exponent `d`:

```bash
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-root-neutral-g-add-l0-23
```
