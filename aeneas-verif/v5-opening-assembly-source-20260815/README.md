# V5 opening-result assembly proof

This bundle checks the final, non-cryptographic assembly step in
`verify_v5_private_openings_from_proof`.

The released function first runs the opening verifier five times. It stores the
five returned views in an array, keeps the four derived index arrays, and then
builds `VerifiedV5PrivateOpenings`. The pinned Aeneas version cannot translate
the whole function because its `HashFn` argument has a higher-ranked lifetime.
The replay therefore applies a temporary source refactor which moves only the
existing final struct expression into `assemble_v5_private_openings`. The
repository Rust is never edited, and the replay checks the patch and source
hashes before extraction.

`assemble_v5_private_openings_exact` proves for every successful extracted
execution that:

- array entries 0 and 1 become `c1` and `c2`;
- entries 2, 3, and 4 become the three later openings, in that order;
- the complete `CircleLineQueryIndices` value is preserved;
- `bytes_consumed` is exactly `proof_bytes_len - remainder.len()` under Rust's
  release-mode `usize` semantics; and
- the returned remainder is the same slice supplied to the assembly step.

The theorem is universal; it is not a test of one proof.

## What this does not prove

This bundle does not prove that the five-iteration production loop stores each
opening returned by the corresponding verifier call. It also does not prove the
opening verifier itself, the correctness of the four derived index arrays, or
the four later FRI loops. Those are separate obligations. In particular, a
direct Aeneas translation of the whole driver still stops at the unsupported
higher-ranked `HashFn` lifetime.

The temporary refactor is deliberately limited to an exact extraction of the
unchanged final expression. Equality between that refactor and the production
source remains reviewable from the checked patch; it is not presented as a Lean
theorem about the Rust compiler.

## Replay

Use the pinned Charon and Aeneas checkouts and the patched Lean 4.32 Aeneas
library:

```sh
LEAN432_BIN=/path/to/lean-4.32.0/bin/lean \
AENEAS_LEAN_LIB=/path/to/aeneas-lean-library \
ASPIS_CHARON_REPO=/path/to/charon-cb50ff16 \
ASPIS_AENEAS_REPO=/path/to/aeneas-b59d5188 \
./aeneas-verif/v5-opening-assembly-source-20260815/replay-lean432.sh
```

The replay regenerates the Lean files, compares them byte-for-byte with the
checked snapshot, compiles the proof, checks its printed axioms, and confirms
that the production Rust files have the expected hashes.
