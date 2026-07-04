# ML-DSA Solana STARK Spec Map

This is the Stage A handoff document for implementing `ML-DSA-44` verification in AIR.

## Scope Decision

- Prove `FIPS 204 Algorithm 8 ML-DSA.Verify_internal`
- Do not start with `Algorithm 7 ML-DSA.Verify`
- Reason: `Verify_internal` is the deterministic verification core, which is what the STARK needs to encode

## Frozen Parameter Set

- First target: `ML-DSA-44`
- Frozen values from `FIPS 204`:
  - `(k, l) = (4, 4)`
  - `q = 8380417`
  - `d = 13`
  - `tau = 39`
  - `lambda = 128`
  - `gamma1 = 2^17`
  - `gamma2 = (q - 1) / 88`
  - `eta = 2`
  - `beta = 78`
  - `omega = 80`
  - public key bytes: `1312`
  - signature bytes: `2420`

## Direct Call Graph From Verify_internal

`Algorithm 8 ML-DSA.Verify_internal(pk, M', sigma)`

1. `pkDecode(pk)` -> `Algorithm 23`
2. `sigDecode(sigma)` -> `Algorithm 27`
3. reject if `h = bottom`
4. `ExpandA(rho)` -> `Algorithm 32`
5. `tr <- H(pk, 64)` where `H = SHAKE256`
6. `mu <- H(BytesToBits(tr) || M', 64)`
7. `c <- SampleInBall(ctilde)` -> `Algorithm 29`
8. `wApprox' <- NTT^-1(Ahat o NTT(z) - NTT(c) o NTT(t1 * 2^d))`
9. `w1' <- UseHint(h, wApprox')` -> `Algorithm 40`, applied coefficientwise
10. `ctilde' <- H(mu || w1Encode(w1'), lambda / 4)` -> `Algorithm 28`
11. accept iff:
    - `||z||_inf < gamma1 - beta`
    - `ctilde == ctilde'`

## Required Auxiliary Algorithms

- `HintBitUnpack` -> `Algorithm 21`
- `w1Encode` -> `Algorithm 28`
- `RejNTTPoly` -> `Algorithm 30`
- `Decompose` -> `Algorithm 36`
- `HighBits` -> `Algorithm 37`
- `UseHint` -> `Algorithm 40`
- `NTT` -> `Algorithm 41`
- `NTT^-1` -> `Algorithm 42`

## AIR Module Boundaries

- `decode`
  - `pkDecode`
  - `sigDecode`
  - `HintBitUnpack`
- `hash`
  - `SHAKE256` for `tr`, `mu`, `ctilde'`
  - `SHAKE256` transcript for `SampleInBall`
  - `SHAKE128` transcript for `ExpandA`
- `challenge`
  - `SampleInBall`
- `poly`
  - scalar mod-`q` arithmetic
  - multiplication by `2^d`
- `ntt`
  - `NTT`
  - `NTT^-1`
- `hint`
  - `Decompose`
  - `UseHint`
  - `w1Encode`
- `verdict`
  - infinity norm check on `z`
  - `ctilde` equality

## Immediate Engineering Choices That Still Need A Written Decision

- Public-input binding:
  - Option A: exact `(pk, M', sigma)` bytes as public inputs
  - Option B: a commitment to those bytes, with the commitment exposed publicly
  - This must be frozen before Solana integration starts
- Keccak / SHAKE representation:
  - single monolithic AIR
  - or staged AIR with explicit transcript tables
- Matrix handling:
  - fully materialized `Ahat`
  - or streamed / tiled generation inside the trace

## Things That Must Not Be Hand-Waved

- malformed hint encoding rejection from `sigDecode`
- exact `SampleInBall` behavior, including rejection sampling loop
- exact wraparound behavior in `Decompose` / `UseHint`
- exact `NTT` schedule and constants
- exact byte-domain behavior of `H` and `G`

## First Code Tasks Implied By This Map

1. Build a no-proof reference harness for `Algorithm 8`
2. Differential-test `pkDecode`, `sigDecode`, `SampleInBall`, `UseHint`, and `w1Encode`
3. Instrument direct trace dimensions for:
   - decode only
   - decode + hash
   - full verify path
4. Refuse to generate STARK proofs until the full direct-evaluation path matches the pinned verifier
