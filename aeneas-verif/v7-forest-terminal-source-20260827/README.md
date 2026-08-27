# V7 eight-lane forest terminal Rust-to-Lean source bridge

This focused bundle pins and translates the production-inactive ASF8/ASR8
terminal at source revision
`2ff50df4b1dc58eb33ccb2f34c93e838cb72522c`.  It does not activate a proof
profile, verifier dispatch, Pool CPI, account mutation, or network path.

The literal translated entry points are:

- `decode_pool_v1_pair_forest_terminal_statement_v1`;
- `decode_pool_v1_pair_forest_terminal_result_v1`;
- `host::verify_pool_v1_pair_forest_terminal_inactive_v1`.

The checked bridge proves:

- the ASF8 statement is exactly 1,880 bytes and the ASR8 result is exactly
  792 bytes, with every top-level offset pinned;
- successful statement/result decoding implies the production validator at
  the end of the corresponding decoder returned `Ok(())`;
- successful host verification implies the matching transfer/withdrawal
  residual evaluator returned a residual object, the literal Rust count check
  passed, `all_zero` returned true, result-against-statement validation
  succeeded, and the returned ASR8 value has the canonical statement fields.

The last implication is an operational source theorem.  It does not prove
Poseidon, residual, account-codec, PDA, compiler, or cryptographic semantics;
those boundaries are listed in `SOURCE-BOUNDARY.md`.

## Replay

`replay-extraction.sh` checks the pinned source revision, re-extracts with
Charon 0.1.223, checks the normalized LLBC digest, runs the patched Aeneas
d860 translator, and compares the generated transparent files.  Set
`CHARON_BIN` and `AENEAS_BIN` to the pinned executables.

`replay-lean.sh` compiles the generated modules and all three focused proof
files against a pinned Aeneas Lean backend.  Set `AENEAS_LEAN_BACKEND`.

`replay.sh` runs both stages.  The frozen NUC replay used a systemd user
cgroup with `MemoryHigh=22G`, `MemoryMax=28G`, and `MemorySwapMax=0`.

`FunsExternal.lean` is the generated interface template with one transparent
standard-library fill: `Result::map_err` is implemented by its exact two-case
Rust semantics.  The remaining declarations are intentionally explicit
interfaces, not silently completed cryptographic proofs.
