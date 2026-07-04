# Circle spike gate

## AMBER

### Evidence

- Host roundtrip scenarios: `3` divergences: `0`
- Solana compilation status: `failed`
- Projected CU: `7267870` feasible=`false`

### Blockers

- error: failed to get `p3-air` as a dependency of package `circle-p3-core v0.1.0 (/Users/dominic/ZK/crates/circle-p3-core)`
- feature `edition2024` is required
- The package requires the Cargo feature called `edition2024`, but that feature is not stabilized in this version of Cargo (1.84.0 (12fe57a9d 2025-04-07)).
- Proof bytes exceed the 1232-byte transaction limit and require staged upload.
- predicted CU exceeds the transaction compute budget
- query-controlled soundness lower bound 28.0 bits is below the 100.0-bit target

### Recommendation

Keep the host result, then evaluate the listed Solana blockers before committing to a full port.
