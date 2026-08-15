# V5 deployed-Rust extraction replay

This directory records the small Aeneas patch stack used while checking the
Rust verifier deployed from Aspis commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`.

The patches fix translator limitations; they do not change the Aspis Rust or
the deployed Solana program. Applying them to the pinned Aeneas base must
produce tree `743286e4d49cbd53a7ae9dae393a166a64886728`.

## Rebuild the translator

```sh
git clone https://github.com/AeneasVerif/aeneas.git aeneas-v5-replay
cd aeneas-v5-replay
git checkout b59d5188c082f704a418c7cb4e52ad69328002d1
git am /path/to/aspis/aeneas-verif/v5-deployed-rust-replay-20260815/aeneas-patches/*.patch
test "$(git rev-parse HEAD^{tree})" = 743286e4d49cbd53a7ae9dae393a166a64886728
cd src
opam exec -- dune build main.exe
./_build/default/main.exe -version
```

The last command must report `aeneas 35b05b92`. Charon is pinned at
`cb50ff16b9f1066b8a97dc06da704de2da2fa41c` (`0.1.223`) with Rust nightly
`2026-06-01`.

Run `./verify.sh` to check this bundle. If the recorded focused LLBC file is
available locally, run `./verify.sh /path/to/patched/aeneas /path/to/tail.llbc`
to rebuild Aeneas, translate it with `-checks`, and compare `Tail.lean` with the
recorded hash.

## What this closed

The sixth patch recovers the lifetime relation carried by a compiler-generated
closure which borrows both the transcript and parsed proof data. With all six
patches, Aeneas translates and borrow-checks the selected-candidate wrapper
`derive_v5_selected_good_queries_from_transcript`. The generated Lean output
reproduces byte-for-byte, and the exact 22-line function body and
`ParsedProbeData` definition match the deployed source.

This result is deliberately narrow. The focused extraction keeps
`derive_v5_complete_queries_for_selector_from_transcript`,
`checked_v5_selected_good_candidate`, `candidate_is_good`, `Transcript`, and
`Transcript::clone` opaque. It therefore proves that Aeneas can translate the
outer closures and their borrowing structure; it does **not** by itself prove
the transcript-producing helper or the complete verifier.

The separate `v5-transcript-tail-source-20260815` proof checks the lower
`derive_v5_complete_queries_for_selector_from_transcript` data flow after a
reviewed four-step loop expansion. A future composition theorem must connect
that lower proof to this generated outer wrapper and supply the remaining
opaque selector, goodness-test, transcript, field-decoding, and hash meanings.

## Remaining Rust-to-Lean boundaries

- The full unchanged private-opening artifact reaches a function-pointer type
  with locally quantified lifetimes, which this Aeneas version cannot lower.
  The narrow route is a reviewed extraction-only fixed-SHA-256 adapter plus an
  explicit equality proof, not a claim that generic function pointers work.
- The full unchanged row/claim-preparation artifact still reaches an
  unsupported nested mutable-borrow join.
- The selected-candidate wrapper and lower transcript-tail proof are not yet
  joined into one generated theorem, and several helper meanings remain
  explicit premises as described above.
- Charon, Aeneas, Lean, Rust/LLVM, the Solana toolchain, and runtime remain part
  of the ordinary trusted toolchain boundary.

No probability or cryptographic-security claim is created by these translator
patches.
