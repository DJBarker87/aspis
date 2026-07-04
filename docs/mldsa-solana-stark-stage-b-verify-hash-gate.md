# ML-DSA Solana STARK Stage B Verify Hash Gate

Date of run: `2026-04-20`

Primary artifact:

- `results/mldsa-solana-stark/verify-hash-path-prototype.json`

Reproduction command:

```bash
experiments/mldsa-solana-stark/run-verify-hash-path-prototype.sh
```

Fixed inputs:

- `rho = 000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f`
- `message = "ml-dsa verify hash path"`

Method:

- exact `pkDecode` / `sigDecode` byte-layout handling for `ML-DSA-44`
- exact `tr = H(pk, 64)` via `SHAKE256`
- exact `mu = H(tr || M', 64)` via `SHAKE256`
- exact `c = SampleInBall(ctilde)` transcript measurement
- exact `ctilde' = H(mu || w1Encode(w1'), lambda/4)` via `SHAKE256`
- exact malformed-signature checks for:
  - nonzero leftover hint bytes
  - non-monotone hint indices
  - wrong signature length
  - wrong `w1'` witness causing `ctilde'` mismatch
- direct transcript measurement only
- no STARK proof generation
- arithmetic reconstruction is intentionally omitted and `w1'` is supplied as an external witness
- projected rows = one row per `Keccak-f[1600]` round

## Measured Results

### Fixture Surface

- parameter set: `ML-DSA-44`
- public key length: `1312` bytes
- signature length: `2420` bytes
- hint ones in fixture: `9`
- max `w1'` coefficient: `43`
- max `|z|`: `128`

### Hash / Challenge Path

- `tr = H(pk, 64)`:
  - input bytes: `1312`
  - total permutations: `10`
  - projected round rows: `240`
- `mu = H(tr || M', 64)`:
  - input bytes: `87`
  - total permutations: `1`
  - projected round rows: `24`
- `ctilde' = H(mu || w1Encode(w1'), 32)`:
  - input bytes: `832`
  - total permutations: `7`
  - projected round rows: `168`
- `SampleInBall(ctilde)`:
  - seed bytes: `32`
  - sign bytes: `8`
  - position bytes consumed: `40`
  - rejected attempts: `1`
  - hamming weight: `39`
  - projected round rows: `24`

Total projected round rows for this Stage B hash-path slice:

- `456`

Combined with the earlier `ExpandA` measurement for `ML-DSA-44`:

- `ExpandA` rows: `1920`
- hash-path rows excluding `ExpandA`: `456`
- combined SHAKE-driven rows so far: `2376`

Candidate AIR-size proxies for the combined SHAKE-driven slice:

- lane floor:
  - width `25`
  - rows `2376`
  - cells `59400`
- lane candidate v0:
  - width `32`
  - rows `2376`
  - cells `76032`
- bit floor:
  - width `1600`
  - rows `2376`
  - cells `3801600`

### Verdict Checks

- `z` bound check: `true`
- `ctilde == ctilde'`: `true`
- overall hash-path verdict: `true`

Negative checks:

- malformed leftover hint bytes rejected: `true`
- malformed non-monotone hint indices rejected: `true`
- wrong signature length rejected: `true`
- wrong `w1'` witness mismatch detected: `true`

## Interpretation

- This is a useful de-risking result, but only a partial one.
- The remaining SHAKE-heavy path outside `ExpandA` adds `456` projected round rows, which is materially
  smaller than the `1920` rows already measured for `ExpandA`.
- That means the current feasibility bottleneck is still more likely to come from:
  - the chosen Keccak/SHAKE AIR encoding
  - `NTT` / `NTT^-1`
  - matrix-vector arithmetic over `Rq`
  - `UseHint` / reconstruction logic
  - trace width expansion from coefficient, limb, or bit decomposition

## What This Does Not Prove

- It does not prove that full `ML-DSA-44 Verify_internal` fits into a tractable Winterfell AIR.
- It does not prove that proof size will fit a Solana upload path.
- It does not prove that the on-chain verifier will stay under `1.4M` CU.
- It does not include:
  - `ExpandA` constraints themselves, only the prior transcript count
  - matrix multiplication by `A_hat`
  - `NTT` / `NTT^-1`
  - modular reductions
  - decomposition / high-bit extraction used to rebuild `w1'`
  - `UseHint`
  - final arithmetic relation linking `pk`, `z`, `c`, `t1`, and `h`

## Gate Decision

`AMBER-GO`

Reason:

- the SHAKE-only and hash-path transcript measurements together do **not** falsify feasibility
  for `ML-DSA-44`
- they are still only the easy half of the verification logic
- the next gate needs to measure the arithmetic and hint-reconstruction slice without proof generation

## Immediate Next Work

1. Build the no-proof evaluator for the arithmetic path of `ML-DSA-44 Verify_internal`.
2. Measure concrete trace-width / trace-length candidates for:
   - `NTT`
   - inverse `NTT`
   - matrix-vector multiply
   - `UseHint` / `w1'` reconstruction
3. Stop the full prover effort immediately if those measurements extrapolate to obviously
   unworkable proof sizes or verifier costs.
