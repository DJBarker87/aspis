# ML-DSA Solana STARK Claim Boundary

## Project

- Title: `Post-quantum ML-DSA signature verification on Solana via STARK`
- Baseline engineering reference: vendored `third_party/solana-pqzk-fullchain`
- Proof system: `Winterfell 0.12`
- Primary target: `ML-DSA-44`
- Secondary target: `ML-DSA-65` only if `ML-DSA-44` clears the measured gates with real slack

## In Scope

- A research AIR for `FIPS 204` `ML-DSA.Verify_internal` on `ML-DSA-44`
- A `Winterfell 0.12` prover and host verifier for that AIR
- A Solana verifier path that accepts those STARK proofs
- A measurement study with raw artifacts:
  - `n = 100` successful devnet runs
  - mean / median / max CU
  - proof bytes
  - signature bytes
  - CU per proof byte
  - exact transaction signatures
- A bounded comparison against the vendored Yano `SLH-DSA + STARK` baseline

## Explicitly Out Of Scope

- New cryptography
- New protocols
- Production readiness claims
- Application-layer protocols, bridges, vaults, privacy systems
- `ML-DSA-87`
- Any claim of superiority to Yano
- Any claim of novelty, first, or state of the art without a dedicated literature check

## Strongest Defensible Positive Claim

For one pinned code revision, one pinned proof configuration, and one pinned Solana runtime setup, this
repo implements an `ML-DSA-44` verification AIR aligned to `FIPS 204`, generates and locally verifies
`Winterfell 0.12` proofs for that computation, and accepts those proofs on Solana within the documented
`1.4M` CU per-transaction cap, with raw `n = 100` devnet measurements published.

## Strongest Defensible Negative Claim

After implementing and vector-checking a spec-faithful `ML-DSA-44` verification AIR, the resulting proof
bytes, upload/account pressure, or on-chain verifier cost still exceed the stated Solana constraints.
Within this pinned stack, `ML-DSA-44`-via-STARK-on-Solana is therefore not feasible.

## Verified Facts Frozen For Stage A

- `FIPS 204` Table 1 / Table 2 define:
  - `ML-DSA-44`: `(k, l) = (4, 4)`, public key `1312` bytes, signature `2420` bytes
  - `ML-DSA-65`: `(k, l) = (6, 5)`, public key `1952` bytes, signature `3309` bytes
- `FIPS 204` verification is `Algorithm 8 ML-DSA.Verify_internal`
- `FIPS 204` uses `H = SHAKE256` and `G = SHAKE128`
- Solana docs currently state:
  - transaction size limit `1232` bytes
  - per-transaction compute cap `1,400,000` CU
- Vendored Yano snapshot uses:
  - `winterfell = 0.12.0`
  - published devnet benchmark summary at `examples/benchmarks/statistics.txt`

## Assumptions That Still Need Measurement

- Whether a spec-faithful `ML-DSA-44` AIR yields proof bytes small enough for a practical Yano-style
  upload path and on-chain verification cost
- Whether SHAKE-heavy arithmetization dominates trace growth before NTT arithmetic does
- Whether Solana verification stays below the `1.4M` CU cap after replacing Yano's minimal affine AIR
  with `ML-DSA-44`
- Whether `ML-DSA-65` is remotely plausible under the same bound

## Immediate Gates

1. Stage A: freeze the spec map and baseline numbers
2. Stage B: build a direct AIR evaluator with no STARK proof generation and inspect real trace metrics
3. Stage C: generate one host proof for a pinned `ML-DSA-44` case and measure proof bytes
4. Do not open `ML-DSA-65` before `ML-DSA-44` clears Stage C with real headroom
