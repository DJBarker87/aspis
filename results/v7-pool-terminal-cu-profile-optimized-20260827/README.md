# V7 native Pool terminal prefactor CU profile (2026-08-27)

## Result

The terminal prefactorization makes the complete direct native Tag-73
cryptographic verifier accept the preserved honest 30,192-byte Pool proof in
one strict 1.4M-CU LiteSVM transaction:

```text
transaction CU: 1,395,868 / 1,400,000
headroom:                        4,132 CU
outcome:                         accepted
simulation metadata == execution metadata
```

The Pool semantic terminal fell from **821,667 CU to 407,973 CU**, an exact
saving of **413,694 CU (50.35%)**.  No cryptographic operation, transcript
challenge, semantic constraint, copy link, masking term, or proof byte was
removed.  The changed evaluator is the algebraic terminal factorization in
upstream commit `c233fc4d404c4d7705671090f65a53fe225338c5`.

This closes the direct single-leaf verifier feasibility question.  It does
**not** yet prove the final Pool transaction fits: the measured proof is the
30,192-byte predecessor, not the planned 34,658-byte proof-carried
pair-afterstate profile, and this transaction invokes only the verifier rather
than the atomic Pool state mutation.  The 4,132-CU diagnostic margin is too
small to absorb either unmeasured change by assumption.

## Exact before/after comparison

All values include the small checkpoint logging cost and are from the same
proof, request, LiteSVM harness, toolchain and 1.4M limit.

| Phase | Baseline CU | Prefactored CU | Change |
| --- | ---: | ---: | ---: |
| request/body/parse/schedule through terminal start | 254,292 | 254,292 | 0 |
| **Pool semantic terminal** | **821,667** | **407,973** | **-413,694** |
| relation setup through query coordinates | 172,912 | 172,912 | 0 |
| V7 two-tree authentication | not completed | 383,343 | now measured |
| query fold | not reached | 20,807 | now measured |
| query batch and remaining relation tail | not reached | 155,853 | now measured |
| verifier exit after final checkpoint | not reached | 51 | now measured |
| complete transaction | exhausted at 1,399,850 | **1,395,868 accepted** | complete |

The unchanged 172,912-CU relation prefix is measured from `relation-start`
through `query-coordinates`, matching the baseline ledger.  Authentication
through program exit consumes 560,003 CU.  The full machine-readable sequence
is in `phase-ledger.json`; the literal runtime logs are in
`evidence-profile.json`.

## Remaining one-transaction gates

1. Measure the exact 34,658-byte proof-carried pair-afterstate proof through
   this same prefactored verifier.  It adds 64 C2 SHA-256 message blocks across
   q16 and therefore cannot inherit the 30,192-byte result without a run.
2. Measure the production-inactive-checkpoint-free verifier called from the
   actual atomic Pool instruction, including account validation, current-root
   concurrency checks, two occupied-tagged leaf appends, history update,
   nullifier creation and account close/refund.
3. Establish a safe production margin.  The present diagnostic succeeds, but
   4,132 CU is evidence of feasibility rather than a release buffer.
4. Complete the Rust identity and Lean/Aeneas equality bridge for the
   prefactored evaluator before treating it as a verified replacement.

## Provenance

- diagnostic base commit:
  `6fc5fe7c1eb722acf20c19566a94ffbb8adfbe28`;
- prefactor source commit:
  `c233fc4d404c4d7705671090f65a53fe225338c5`;
- local cherry-pick commit:
  `725877da2f722a869c6564503d0257cfeac79467`;
- optimized SBF: 875,416 bytes, SHA-256
  `46f792b331d9fdf6e570e1e62c8118c6aac756990f95500d35cc303fac3b4969`;
- baseline SBF: 825,528 bytes, SHA-256
  `ffa7f7cb3de881c07561ad6d25b704659cb3645f2abe0c343bc61d3133bc14c9`;
- unchanged proof: 30,192 bytes, SHA-256
  `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c`;
- optimized focused SBF build: 17.00 seconds, 656,048,128-byte peak
  RSS, zero swap;
- build environment: `NO_DNA=1 CARGO_BUILD_JOBS=2`,
  `solana-cargo-build-sbf 2.3.0`, platform-tools `v1.48`, SBF
  `rustc 1.84.1`;
- local execution only: no RPC, deploy, network signing or submission.

The diagnostic feature remains mutually exclusive with all production
entrypoints.  The generic evidence harness records either acceptance or
rejection so a successful optimization does not erase its exact metadata.
