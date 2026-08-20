# Production transcript extraction

This bundle extracts four methods from the unchanged production
`aspis-core` transcript implementation:

- `absorb`;
- `squeeze_block`;
- `challenge_queries_without_replacement`;
- `grinding_ok`.

Charon reads the Rust and Aeneas produces the checked-in Lean definitions.
The extraction harness only delegates to those methods and returns the updated
transcript explicitly. It does not copy their implementations.

The Lean proofs establish:

- the exact byte-slice boundaries passed to the hash function by `absorb`,
  `squeeze_block`, and `grinding_ok`;
- the exact transcript state changes made by `absorb` and `squeeze_block`;
- equality between all four extraction wrappers and their generated production
  methods;
- equality between the generated hash inputs and the maintained transcript
  model for the operations above.
- exact little-endian decoding and 17-bit masking of all eight words in each
  squeezed block;
- exact duplicate rejection, insertion order, 18-query stop, and 64-draw
  limit for the generated inner loop;
- exact control of the generated outer loop, including the extra block that is
  squeezed when completion is first noticed at a block boundary;
- for every successful fixed call with `(count = 18, bound = 2^17,
  max_draws = 64)`, equality between the returned positions and
  `AspisV5TranscriptConnection.derive18Queries` over the blocks actually
  squeezed; and
- an exact trace from the input transcript to the returned transcript, with
  one generated `squeeze_block` state change for each consumed block.

These are universal proofs about the generated definitions, not checks of one
released proof or one test vector. They add no cryptographic assumption and do
not change the production Rust.

## Patched Aeneas

The extraction uses Aeneas commit
`000c7b6a4ab001ddceb16a82dd7fd37c3abfe24d`, based on upstream commit
`b59d5188c082f704a418c7cb4e52ad69328002d1`. The ordered patches needed to
reconstruct that checkout are in `aeneas-patches/`.

The added support is deliberately limited. Calls through function pointers are
accepted only when mutable references are absent. The loop matcher may ignore
an immutable shared-loan wrapper only when neither side can contain mutable
write-back state. The Rust verifier and deployed program are unchanged.

## Replay

Apply the patches to the stated Aeneas base, build its OCaml executable and
Lean library, then set the paths required by `replay-lean432.sh`. The script:

1. checks the exact Rust and harness files;
2. extracts the four methods with pinned Charon;
3. translates them with the patched Aeneas;
4. compares the normalized result byte-for-byte with `generated/`;
5. compiles the generated Lean, the two loop inductions, and the fixed-call
   result theorem with Lean 4.32; and
6. rejects proof shortcuts and unexpected axioms.

The checked proof uses only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` foundations.
