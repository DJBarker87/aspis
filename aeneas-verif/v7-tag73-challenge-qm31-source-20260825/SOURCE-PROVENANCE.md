# Frozen source provenance

- deployed repository commit:
  `1589706d38a5e8ca705fbf7aaed2c82cf8595510`
- `crates/aspis-core` git tree:
  `4a869518c17b226068499b7c7880e05212315cd6`
- `crates/aspis-core/src/transcript.rs` SHA-256:
  `302edc38e3d158b6a16eda4cdb39fb5847c2996772e9d30c3c99b4cccf4d308e`
- `crates/aspis-core/src/field.rs` SHA-256:
  `e118899472e3049db688573570296f06696be659524bbf6a62ace537f0316312`
- `crates/aspis-core/src/circle.rs` SHA-256:
  `8f6f0f32c8dd93e3ee459df0c1d0ef710b01996d3bc929dbeffb3f7d14a0227c`
- `crates/aspis-core/src/lib.rs` SHA-256:
  `61180526f742be0b9c52db22165e7308f43f824222f46131da5ce7f996b09954`
- `crates/aspis-core/Cargo.toml` SHA-256:
  `8ad8e5fe47f897d327acc323003fc00adf40b7a0101c24d344bbea64838d3f92`
- path-normalized canonical LLBC SHA-256:
  `0c9f44a7a426b7efd1404e8776795958d89f203eca2915994d013a756b27d857`
- normalized generated `Types.lean` SHA-256:
  `2beae4347eb134ccfa73f56b471d278bbdfbcb2b56d14a10c6ac8976240d8e8c`
- normalized generated `Funs.lean` SHA-256:
  `2406554baf66146eb9d0434fdd65fbf78dad177e63f538e660f449e9c4c4b884`

The current worktree copies of these deployed files have the same hashes.
The extraction harness delegates to `Transcript::challenge_qm31`; it does not
copy or modify the sampler implementation.

The LLBC canonicalizer clears output-only destination fields and normalizes
only the absolute prefix above the separately hash-checked
`crates/aspis-core/...` files.  It also treats
`/translated/options/mir` as invocation metadata under one explicit
whitelist: the bundled extraction must contain JSON `null` and the replay
must contain the string `"Built"`.  The replay records both values, replaces
only the replayed value with `null`, and requires the rest of the canonical
structured LLBC tree to be byte-equal before checking the pinned digest.
Every other MIR-option value is rejected.  Relative file names, Rust sysroot
paths, source contents, declarations, spans, and generated bodies remain
unchanged.

## Exact deployed source schedule

The extracted method performs the following operations, in this order:

1. initialize `[M31::ZERO; 4]`;
2. call `squeeze_block` once and set `word_index = 0`;
3. visit the four mutable limb coordinates in array order;
4. for each limb, try the exact Rust range
   `0..CHALLENGE_RETRY_LIMIT`, where the deployed limit is eight;
5. whenever `word_index == 8`, call `squeeze_block` once and reset the index
   to zero before reading another word;
6. read `block[4 * word_index .. 4 * word_index + 4]`, decode little endian,
   increment the index, mask with `P = 2^31 - 1`, and accept iff the masked
   word differs from `P`;
7. return `ChallengeSampleExhausted` immediately if a limb has no accepted
   candidate in its eight attempts; otherwise assemble the four limbs as
   `(c0.a,c0.b,c1.a,c1.b)`.

Thus one successful call consumes between four and thirty-two words.  Since
each block holds eight words and the first block is squeezed before the loop,
the deployed ordinary sampler consumes between one and four blocks.

`squeeze_block` constructs one 33-byte buffer.  It hashes `state || 1` for
the output block, changes only byte 32 to `2`, hashes `state || 2` for the
successor state, and stores that second digest in the returned transcript.
The source certificate proves both exact hash inputs; it does not attach a
cryptographic assumption to the hash callback.
