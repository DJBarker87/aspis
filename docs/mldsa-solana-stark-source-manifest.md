# ML-DSA Solana STARK Source Manifest

Primary sources only. This list is the allowed input set for Stage A and the start of Stage B.

## Frozen Sources

- `FIPS 204`
  - URL: `https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.204.pdf`
  - Use:
    - parameter sets
    - exact `ML-DSA.Verify_internal` semantics
    - exact encoding / decoding rules
    - exact `SampleInBall`, `ExpandA`, `UseHint`, `NTT`, `NTT^-1` behavior
  - Current status: verified and in use

- `NIST ACVP ML-DSA`
  - URL: `https://pages.nist.gov/ACVP/draft-celi-acvp-ml-dsa.html`
  - Use:
    - vector schema
    - `sigVer` input / output structure
    - harness planning
  - Current status: verified for schema planning; concrete vector ingestion still pending

- `Winterfell`
  - Repo: `https://github.com/facebook/winterfell`
  - Local version in this workspace:
    - `winterfell 0.12.0`
    - `winter-air 0.12.3`
    - `winter-verifier 0.12.3`
  - Use:
    - prover / verifier APIs
    - proof option constraints
    - serialization format expectations
  - Current status: verified from lockfile and vendored Yano baseline usage

- `Solana Compute Budget`
  - URL: `https://solana.com/docs/core/fees/compute-budget`
  - Use:
    - current `1,400,000` CU cap reference
  - Current status: verified

- `Solana Transaction Structure`
  - URL: `https://solana.com/docs/core/transactions/transaction-structure`
  - Use:
    - current `1232`-byte transaction size reference
  - Current status: verified

- Vendored Yano baseline
  - Local path: `third_party/solana-pqzk-fullchain`
  - Use:
    - Solana-side upload path
    - on-chain verifier split
    - heap / CU tuning pattern
    - raw benchmark methodology
  - Current status: verified locally; upstream commit identity still not frozen

## Explicitly Secondary

- Reference implementation mirrors such as `pq-code-package/mldsa-native`
  - Use only for cross-checking implementation behavior after the FIPS-based harness exists
  - Do not let these override FIPS 204

## Not Yet Verified

- Any literature claim about “first”, “novel”, or “state of the art”
- Any direct equivalence between the current public Yano repo and a specific paper or ePrint version
- Any claim that ACVP sample JSON alone is sufficient coverage for malformed-input handling

## Next Source Actions

1. Materialize a pinned local corpus for `ACVP ML-DSA sigVer`
2. Pin the exact upstream identity of the vendored Yano snapshot or state that the comparison is against a
   vendored workspace copy
3. Add a repo-local `spec-map` from `FIPS 204 Algorithm 8` to implementation modules before AIR code starts
