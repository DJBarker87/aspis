# V5 deployed Merkle source extraction

This directory records a successful Charon/Aeneas extraction of the complete
V5 private-opening call graph from the source commit used for the mainnet
program. It does not modify the program source and it does not rebuild the SBF
binary.

The source identity is commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`. The four extracted source files
have these SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `crates/aspis-core/src/merkle.rs` | `76aa94ce9db033715c04e42effe4fe67807b7a2409dcae6595332be8f1cf9747` |
| `crates/aspis-core/src/state_only_private_openings.rs` | `178968bf12967eead324f07e8e0047c5e018874998540e103afad2dcea33cfdb` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| `programs/aspis-verifier/src/v5_private_openings.rs` | `916c14930d419bc0cd794a3d1e01c4e45fea9f4dbbc1f44f89f71caf3ff63c49` |

`source-adapter.patch` and `immediate-return-adapter.patch` are
extraction-only rewrites. They fix the hash backend to one opaque call, rewrite
unsupported iterator and loop shapes, and unroll the fixed five-section
driver. The second patch replaces the first patch's provisional failure flag
with recursive helpers designed to stop before hashing an incomplete
radix-four group. The handwritten semantics proof establishes first-error
hash-prefix and successful-buffer equality between the corresponding loop and
recursive models. It does not by itself establish either remaining code
bridge. Scratch contents after a rejected call are outside the modeled
observation because the production caller returns the error without reading
them.

The patched Rust type-checks. Charon then reaches
`verify_v5_private_openings` and Aeneas emits complete definitions for the
parser, topology constructor, leaf hashing, radix-four and binary-cap
authentication, the five helper calls, returned remainder, and trailing-byte
check. Aeneas emitted no partial bodies for those local functions.

The generated `FunsExternal_Template.lean` is also part of the record. It
lists 13 definitions that this extraction does not translate: standard
`Option`, `Result`, and `Vec` operations; the query-index helper and its public
constants; and `fixed_hashv`. The generated file is therefore not a standalone
proof until those definitions are implemented and proved against their source
semantics. The extraction replay checks generation; it does not claim to close
those external definitions.

The only opaque cryptographic operation is `merkle.fixed_hashv`. Any later
proof must take as an explicit premise that it equals Solana `hashv` (SHA-256)
over the concatenation of the exact ordered slices. This package makes no
collision, preimage, or random-oracle claim.

## Unchanged verifier-loop snapshot

`generated/V5MerkleUnchangedSource/` records the newer Aeneas output for the
production radix authentication function with its original three nested loops.
The byte-exact raw output and its LLBC hash are retained beside a Lean 4.32
compilable view.  The compilable view changes only Lean import and elaboration
details; it does not replace the Rust loop with the recursive extraction
helpers.

`V5MerkleUntouchedRadixInversion.lean` proves what every successful call to
that translated function must have done: the three public input checks passed,
and the original nested loop returned `some true` with exactly the output
vectors returned by the function.  The statement compares only data the
verifier reads, so arbitrary unused entries in fixed-size offset arrays are
irrelevant.

This is not yet the full source-to-mathematics proof for the loop.  The next
theorem must show that the successful generated loop execution produces the
same ordered child reads, hash inputs, cursor movement, and final root check as
the maintained Merkle model.  The topology constructor, shape validator, and
outer five-section driver were still partial in this raw translation and are
listed as explicit external declarations in its compilable view.

## What this does not prove

This is a complete extraction artifact, not the final source-equality proof.
`AspisFormal/V5MerkleSourceAdapter.lean` proves the generic control-flow
lemma: the loop-shaped and recursive scans have the same result and ordered
hash-call prefix, and successful runs have the same scratch vectors and
frontier position. It explicitly names, but does not assume or discharge, the
two remaining code connections: original deployed LLBC to the loop model, and
generated Aeneas helpers to the recursive model. The generated definitions
must then be connected to:

- `VerifyStateOnlyPrivateOpeningWithTopologySourceEquality`;
- `VerifyV5DriverCompositionSourceEquality`.

Until those proofs exist, the repository must not say that the deployed Rust
Merkle verifier has been proved equal to the mathematical model. Concrete Rust
tests support the rewrites, but tests do not replace that universal proof.

The generated proof package now establishes the exact leaf and binary-cap
SHA-256 inputs and inverts a successful top-level driver call into all five
opening results, their remainders, four query arrays, scratch states, byte
count, and the final empty-remainder check. Its one executable axiom is
`fixed_hashv`. The remaining generated-code proof is the nonterminal
radix-four recursion: each slot read, group hash, frontier read, and cursor
advance must still be connected to the maintained section trace. The original
deployed nested loop must separately be connected to the loop model, and
`fixed_hashv` must be connected to Solana SHA-256. These are open obligations,
not conclusions of the extraction replay.

## Tool versions

- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas base: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Aeneas extraction extensions: `b4e0c769`, `156a8d23`, `7c8dc061`,
  `d5cb4d05`, `b49f69d8`, `35b05b92`

Run `replay-extraction.sh` with `CHARON_BIN` and `AENEAS_BIN` pointing to
those builds, and `CHARON_REPO` and `AENEAS_REPO` pointing to their source
trees. The script checks the exact source identities, checks and applies the
adapter, type-checks it, and requires a complete Aeneas extraction.

The extraction-affecting compiler changes from the local Aeneas commits are
reproduced by `aeneas-extraction-extensions.patch` (SHA-256
`6be4942915a0468bb05f0de385d2c308e23deb8f2dbb91866a030bc5f55f38f5`).
The commits also contain tests, which are not needed to build the extractor
and are not copied into this patch. These local Aeneas changes are ordinary
tooling code, not formally verified transformations; review them or include
them in the extraction trust boundary.

Apply the patch to Aeneas base `b59d5188`, then build `src/main.exe` with the
recorded reconstruction version. Build Charon at `cb50ff16` with
`cargo build --release` from its `charon/` directory. For example:

```sh
git -C /path/to/aeneas checkout b59d5188
git -C /path/to/aeneas apply \
  /path/to/Aspis/aeneas-verif/v5-merkle-deployed-source-20260815/aeneas-extraction-extensions.patch
(cd /path/to/aeneas/src && \
  AENEAS_VERSION=aspis-v5-merkle-6be49429 dune build)

git -C /path/to/charon checkout cb50ff16
(cd /path/to/charon/charon && cargo build --release)

CHARON_REPO=/path/to/charon \
CHARON_BIN=/path/to/charon/charon/target/release/charon \
AENEAS_REPO=/path/to/aeneas \
AENEAS_BIN=/path/to/aeneas/src/_build/default/main.exe \
  ./aeneas-verif/v5-merkle-deployed-source-20260815/replay-extraction.sh
```
