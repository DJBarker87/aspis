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

The bridge proof currently establishes:

- the exact byte-slice boundaries passed to the hash function by `absorb`,
  `squeeze_block`, and `grinding_ok`;
- the exact transcript state changes made by `absorb` and `squeeze_block`;
- equality between all four extraction wrappers and their generated production
  methods;
- equality between the generated hash inputs and the maintained transcript
  model for the operations above.

The complete without-replacement loop is now translated rather than assumed.
The remaining proof work is to show, by induction over its two generated loops,
that its successful fixed release call returns exactly the first 18 distinct
17-bit words described by `AspisV5TranscriptConnection.derive18Queries` and
advances the transcript by exactly the blocks it consumed.

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
5. compiles the generated Lean and bridge proof with Lean 4.32; and
6. rejects proof shortcuts and unexpected axioms.

The checked proof uses only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` foundations.
