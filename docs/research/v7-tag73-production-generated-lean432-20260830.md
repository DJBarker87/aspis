# V7 Tag-73 production Rust to Lean 4.32 milestone

The literal production root
`verify_v7_compact_transcript_and_relation_prepared_with_hiding_context` now
completes Charon/Aeneas translation and compiles as one Lean 4.32 generated
module.

## Frozen inputs

- generic LLBC SHA-256:
  `8acbe11cd3800b27e325bf3ef089a58e02f27fce84e08c55b928807d518ebd18`
- patched Aeneas tree:
  `8819b20bdc1713f7acd15e770caf0b955d3d677c`
- incremental translator SHA-256:
  `017fc5685a79d4aa3aa19f9529d57fdf167c1387c9b1fee63a254994f5ff9d5a`
- Lean version: 4.32.0
- authenticated Lake manifest SHA-256:
  `5d15524cf34ff705bebbd037e80baec63683d5d5a3a37a539a62f17405a2fc62`

The incremental translator is evidence for the patch, not the final isolated
release build.

## Results

| Gate | Result | Wall | Peak RSS | Swap |
| --- | --- | ---: | ---: | ---: |
| Production Rust to Lean generation | PASS | 6:38.396 | 2,691,724 KiB | 0 |
| Scoped Aeneas Lean-4.32 runtime | PASS | 4:22.465 | 6.2 GiB cgroup | 0 |
| Complete staged generated module | PASS | 30.266 s | 3,282,612 KiB | 0 |

The staged source SHA-256 values are:

```text
d7df5e1346da8f3e56cd96292b7f1ac05775f190d48c3823d184454e019abaf3  Funs.lean
86ca701db9c212d3e5651db24e9297e604b66314c8a939e17ee5d37e811a5c12  FunsExternal.lean
80cd40191de85197c50f7e7f4254ece11f6aa3571bd47aaccb9a51b73a773f67  MutableIteratorCompat.lean
8a74caf511821a0e8e1cd80e9e877bb6ec46f65cbfec5aad279f62dd30b48e94  Types.lean
93baa33fc37f2944b280d44f07c7408549162ef7b4c0a01fb7f603d6c425c935  TypesExternal.lean
```

All module compilation logs are error-free. The helper reports one benign
duplicated-namespace naming warning. No generated declaration reports `sorry`.

A subsequent root `#print axioms` audit found eight generated
`_native.decide` certificates, all originating in Debug/expect-only `Str`
literals. The staging gate now replaces exactly those eight messages with the
same kernel-proved empty `Str` used by earlier accepted-source bridges. This
does not alter typed success or failure; it removes panic text from the Lean
model. The staged hashes above predate this final string normalization and will
be superseded by the next frozen replay manifest.

## Security scope

Production Rust, the proof format, transcript order, field arithmetic,
Merkle profile, work schedule, query count and semantic relation are unchanged.
The staging layer is shape-checked and fails if the generated occurrences
change.

This is not yet the final end-to-end source theorem. `FunsExternal` remains the
generated template. The next gate is to install exact executable models for
the reached ownership/container operations, preserve the explicit SHA/runtime
boundary, and prove literal production success implies the existing fixed-field
projection and restored K1.3 source input.
