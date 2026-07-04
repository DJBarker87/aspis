# ML-DSA Solana STARK Stage B SHAKE Gate

Date of run: `2026-04-20`

Primary artifact:

- `results/mldsa-solana-stark/shake-expanda-prototype.json`

Reproduction command:

```bash
experiments/mldsa-solana-stark/run-shake-expanda-prototype.sh
```

Fixed input:

- `rho = 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f`

Method:

- exact `FIPS 204 Algorithm 32 ExpandA`
- exact `Algorithm 30 RejNTTPoly`
- exact `Algorithm 14 CoeffFromThreeBytes`
- direct transcript measurement only
- no STARK proof generation
- projected rows = one row per `Keccak-f[1600]` round

## Measured Results

### ML-DSA-44

- total polynomials: `16`
- accepted coefficients: `4096`
- total attempts: `4097`
- total rejections: `1`
- total squeezed bytes: `12291`
- total `SHAKE128` permutations: `80`
- projected round rows: `1920`

Candidate AIR-size proxies:

- lane floor:
  - width `25`
  - rows `1920`
  - cells `48000`
- lane candidate v0:
  - width `32`
  - rows `1920`
  - cells `61440`
- bit floor:
  - width `1600`
  - rows `1920`
  - cells `3072000`

### ML-DSA-65

- total polynomials: `30`
- accepted coefficients: `7680`
- total attempts: `7687`
- total rejections: `7`
- total squeezed bytes: `23061`
- total `SHAKE128` permutations: `150`
- projected round rows: `3600`

Candidate AIR-size proxies:

- lane floor:
  - width `25`
  - rows `3600`
  - cells `90000`
- lane candidate v0:
  - width `32`
  - rows `3600`
  - cells `115200`
- bit floor:
  - width `1600`
  - rows `3600`
  - cells `5760000`

## Interpretation

- `ExpandA` by itself is **not** an immediate project-killer at the permutation-count level.
- The reason is simple:
  - each sampled polynomial needs only about `768` output bytes
  - with `SHAKE128` rate `168`, each polynomial lands at `5` permutations for this fixed-input run
- The rejection overhead is negligible in this experiment:
  - `1` rejection total for `ML-DSA-44`
  - `7` rejections total for `ML-DSA-65`

## What This Does Not Prove

- It does not prove that a full `ML-DSA.Verify_internal` AIR is small enough.
- It does not include:
  - `mu` hashing
  - challenge derivation by `SampleInBall`
  - `UseHint`
  - `w1Encode`
  - `NTT`
  - `NTT^-1`
  - norm checks
  - malformed-input checks
- It also does not include the actual constraint cost of a chosen Keccak/SHAKE AIR. The `bit floor`
  shows how expensive this becomes if the state is decomposed naively.

## Gate Decision

`AMBER-GO`

Reason:

- The SHAKE-only `ExpandA` transcript does not falsify feasibility on its own.
- It is cheap enough to justify continuing to the full direct evaluator for `ML-DSA-44 Verify_internal`.
- `ML-DSA-65` remains out of scope for implementation unless `44` keeps clearing gates.

## Immediate Next Work

1. Keep the SHAKE-first discipline and add the `mu` / `ctilde'` hash path next.
2. Build the no-proof direct evaluator for exact `ML-DSA-44 Verify_internal`.
3. Add the valid / invalid vector harness before any full proof generation.
4. Revisit the feasibility gate once the full hash + arithmetic + hint path is measured together.
