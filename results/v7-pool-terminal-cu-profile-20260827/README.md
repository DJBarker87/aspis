# V7 native Pool terminal CU profile (2026-08-27)

## Result

The current native Pool private-transfer verifier does not fit by itself in a
1.4M-CU transaction.  With the preserved honest 30,192-byte proof, the
diagnostic verifier consumed all 1,399,850 CU available after the Compute
Budget instruction and failed inside the two-tree V7 query authentication.

The decisive result is earlier: the Pool semantic terminal alone consumed
**821,667 CU**, or 58.7% of the complete transaction limit.  By the time query
authentication began, **1,249,409 CU** had already been consumed and only
150,441 CU remained.  The verifier did not reach query folding, query-batch
composition, the remaining three relation folds, or the final relation check.

This is the current 30,192-byte single-leaf Pool relation baseline, not the
corrected 35,216-byte proof-carried pair-afterstate profile. The latter has 64
additional C2 leaf SHA-256 message blocks across q16, so this result is a lower
complexity predecessor, not evidence that the staged pair profile fits.

## Exact phase ledger

The checkpoints below report literal remaining-CU values from the one local
LiteSVM transaction.  Deltas include the small preceding diagnostic logging
overhead, so they are exact diagnostic-binary costs rather than an assertion
that production logging is free.

| Checkpoint | Delta CU | Remaining CU |
| --- | ---: | ---: |
| program entry | 491 | 1,399,359 |
| request decoding and request/envelope hashes | 3,309 | 1,396,050 |
| full 30,192-byte proof-body SHA-256 | 15,597 | 1,380,453 |
| deferred-canonical wire parse | 296 | 1,380,157 |
| runtime inactive-mask schedule deduplication | 3,983 | 1,376,174 |
| transcript setup and hiding precommit | 9,566 | 1,366,608 |
| ten-round degree-27 semantic sumcheck | 193,735 | 1,172,873 |
| three point-claim rows | 27,039 | 1,145,834 |
| terminal-start checkpoint | 276 | 1,145,558 |
| **Pool semantic terminal** | **821,667** | **323,891** |
| relation-start checkpoint | 283 | 323,608 |
| relation weight preparation | 39,865 | 283,743 |
| two secure circle samples | 12,931 | 270,812 |
| compact relation-field decode | 7,079 | 263,733 |
| relation round zero plus fold-work check | 11,708 | 252,025 |
| final256 decode and transcript absorb | 79,883 | 172,142 |
| final-work check and q16 schedule | 13,786 | 158,356 |
| query-fold-start checkpoint | 255 | 158,101 |
| query coordinate preparation | 7,660 | 150,441 |
| V7 two-tree authentication | **>150,441** | exhausted |

The machine-readable form is in `phase-ledger.json`; the complete raw runtime
log is in `evidence-profile.json`.

## Deletion and optimization ledger

Nothing in this measurement supports deleting a cryptographic check.  The
safe targets are algebraic prefactorization and proven removal of duplicated
transport work:

| Work | Exact current cost | Treatment |
| --- | ---: | --- |
| Request/envelope validation | 3,309 CU | Keep. It binds the selected program, profile, release, statement and historical anchor. |
| Full proof-body digest | 15,597 CU | Removable only under the separately specified finalized-proof identity/length plus immediate-return source theorem. Removing one pass saves exactly this diagnostic cost. |
| Inactive-mask schedule deduplication | 3,983 CU | Replace with generated, compile-time row-group and mask constants proved equal to the registry. |
| Semantic sumcheck and point claims | 220,774 CU | Essential. Keep all rounds and claims; optimize only field/transcript implementation if terminal work is insufficient. |
| Pool semantic terminal | 821,667 CU | Primary blocker. Prefactorize selectors, fixed-zero/initial residuals and copy routing against the unchanged compiled polynomial. |
| Relation prefix through coordinates | 172,912 CU | Essential and already bounded. Do not attack before the terminal because the terminal is nearly five times larger. |
| Query authentication | >150,441 CU before failure | Essential. The staged pair proof makes this somewhat larger; profile it only after the terminal reaches its gate. |

The current private-transfer terminal spelling has an exact static inventory
of 109 semantic `Selectors::row` calls, 512 initial-state residual terms, 546
absorption-zero terms, 13 copy patterns with 68 nonzero limbs, and 78 copy
links expanded into 156 endpoint evaluations over 128 unique rows.  The
initial and absorption scans repeatedly multiply the same opened limbs by row
selectors; the copy loop separately reconstructs row selectors and weighted
patterns for every endpoint.  These are algebraic compilation opportunities:

1. generate per-lane selector linear forms for the initial and absorption
   constraints, including the public constants, so the verifier evaluates the
   same 1,058 terms through grouped linear forms rather than one row/lane term
   at a time;
2. generate a factorized copy-routing basis/matrix over the 128 unique rows
   and 13 pattern values, analogous to the already frozen atomic-terminal
   routing factorization; and
3. freeze the eight-value inactive-mask grouping instead of rebuilding it at
   runtime.

Each replacement must have a Rust identity test and a Lean/Aeneas equality
bridge to the existing compiled reference.  Poseidon, semantic constraints,
copy links, masking, degree and transcript challenges stay unchanged.

## Minimum prefactorization gate

The frozen V6 integrated profile measured its atomic semantic terminal at
299,489 CU.  Therefore the concrete first gate for this Pool terminal is:

```text
821,667 CU -> <=299,489 CU
required saving: >=522,178 CU
```

That exact target would reduce consumption before V7 query authentication from
1,249,409 to 727,231 CU, leaving 672,619 CU for authentication and the relation
tail.  As a cross-profile planning check, the frozen V6 integrated evidence
measured 589,078 CU from query authentication through its relation tail.  This
comparison makes the target technically plausible, but it is not a proof that
the V7 staged pair verifier or the final byte-only Pool suffix fits.  Those are
separate measurements after the prefactorized evaluator is proven equal.

## Reproduction and provenance

- source revision: `603c1c86dc4df46d3179eefaddeaac90c35129d5`;
- diagnostic SBF: 825,528 bytes, SHA-256
  `ffa7f7cb3de881c07561ad6d25b704659cb3645f2abe0c343bc61d3133bc14c9`;
- proof: 30,192 bytes, SHA-256
  `656f25689041ae7f90c9461f4dbe3336478e01e1970ff00c24d1e7d90ed2e72c`;
- build: `NO_DNA=1 CARGO_BUILD_JOBS=2 cargo-build-sbf --manifest-path
  programs/aspis-verifier/Cargo.toml --no-default-features --features
  v7-pool-cu-profile --sbf-out-dir
  results/v7-pool-terminal-cu-profile-20260827/artifacts`;
- toolchain: `solana-cargo-build-sbf 2.3.0`, platform-tools `v1.48`, SBF
  `rustc 1.84.1`;
- focused SBF build: 76.97 seconds, 659,488,768-byte peak RSS, zero swap;
- local execution only; no RPC, deploy, signing for a network, or submission.

The diagnostic feature is mutually exclusive with every production and CU
probe entrypoint.  Production verification still calls the original no-trace
wrapper, and the diagnostic function does not change any transcript byte or
cryptographic operation.
