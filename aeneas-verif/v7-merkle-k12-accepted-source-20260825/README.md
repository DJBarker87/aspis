# V7 Tag-73 two-tree Merkle accepted-source bridge

This bundle is the self-contained Charon/Aeneas evidence package connecting
the V7 production Rust parser, Tag-73 Merkle hashing, two-tree verifier, and
`verify_and_gamma_combine_v7_openings` caller to the already-frozen Lean
`accepted_two_tree_openings` predicate at the requested revision. It does not
change production Rust, the deployed SBF, the cryptography, or any Pool
theorem.

The strongest source-facing theorem is
`translated_caller_success_implies_accepted_two_tree_openings` in
`proof/V7MerkleK12CallerBridge.lean`. A literal successful result from the
translated production caller implies the existing frozen predicate, with the
opening proof constructed from translated caller and verifier control flow.
Its only semantic premise is `HashCallbackEqualsSha256`, the allowed SHA-256
primitive interface; it has no Rust-agrees-with-Lean or accepted-conclusion
premise.

The bridge proves all of the following source facts:

- C1 leaf input is exactly `0x10 || 0x71 || value[403] || salt[32]`;
- C2 leaf input is exactly `0x10 || 0xf1 || value[186] || salt[32]`;
- node input is exactly `0x11 || left[26] || right[26]`;
- `truncate_sha256_v7` returns exactly the first 26 bytes of the same
  successful 32-byte SHA result;
- the translated parser has the frozen exact lengths, offsets, little-endian
  fields, tags, shared-salt layout, and rejects malformed or trailing input;
- the caller supplies exactly 16 paired openings at the same public positions,
  distinct C1/C2 leaf tags, and the one disclosed salt from each query record;
- the verifier runs depth exactly 18, uses the position bit for left/right
  orientation in both trees, consumes paired frontiers, and compares the final
  nodes with the production transcript roots; and
- parse, query, arithmetic, hash, path, length, duplicate-position, or root
  failure cannot produce caller success.

The supporting theorem
`verify_two_subtrees_success_yields_exact_traversal` yields explicit witnesses
and equations for:

- clearing and seeding the working level from the supplied entries;
- executing the complete `0 .. depth` translated outer loop;
- consuming exactly `Slice.len c1Nodes` paired frontier bytes;
- returning `pending = none`;
- producing a singleton final level; and
- reading the exact final entry `(0, c1Root, c2Root)`.

The theorem does not assume those conclusions through an invariant or record
premise. Its supporting loop theorems prove that neither translated loop can
manufacture an accepting `some true` early return, and its array theorem proves
that translated byte-array equality returning `true` implies actual equality.

The transparent caller extraction includes the query accessor, both leaf-hash
calls, the two-tree verifier call, gamma combination, and field helpers.
`V7MerkleCallerNamespaceBridge` proves that its duplicate Merkle definitions
equal the four-root definitions and gives an exact fieldwise equivalence from
the independently translated parser wire to the caller wire.

## Pinned production source

The exact requested source is commit
`01f5f4f722cfdf6bc29c157fc3db6ff5ab5e413a`, tree
`f634f5d7d8ff6606f1a9db40771111e49f5f7e53`. Charon is run with these four
transparent roots:

```text
crate::v7_merkle208::truncate_sha256_v7
crate::v7_merkle208::private_leaf_hash_v7
crate::v7_merkle208::node_hash_v7
crate::v7_merkle208::verify_two_minimal_subtrees_v7_bytes
```

No extraction wrapper or production-source overlay is used. The direct Rust
source `crates/aspis-core/src/v7_merkle208.rs` has SHA-256
`fde745f90fb5870dd604e95333557aba04447cc36b4cff017d5eecd82ab966b5` at
that commit. `DEPLOYED-SOURCE.sha256` pins the other direct build/source inputs.

The archived raw LLBC was first produced from the byte-identical predecessor
revision `1589706d38a5e8ca705fbf7aaed2c82cf8595510`. This is not accepted merely
as a source-text argument: `replay-extraction.sh` re-extracts from a disposable
`git archive` of the requested revision. The fresh and archived normalized
LLBC files are byte-identical with SHA-256
`f43c3b6596bb4a527d46d9c4163e6ce21eef3db0ef6a55ecb6261b7fa5368d91`.
Aeneas regeneration is also byte-identical after the single pinned
failure-diagnostic normalization. `EXTRACTION-RESULT.txt` records commands and
resource evidence.

## Frozen translation artifacts

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `extraction/V7MerkleK12.llbc` | 1,009,262 | `e484caca945e26296abafe34da2423bb2a26cb3be7592a2815541092d420e3cc` |
| normalized LLBC | — | `f43c3b6596bb4a527d46d9c4163e6ce21eef3db0ef6a55ecb6261b7fa5368d91` |
| `extraction/translation.json` | 14,086 | `389f0a4c2b3cfd32a5c75e7fa6bddcd8c073f31313462a9c86ba5dcc74592040` |
| `generated/V7MerkleK12/Funs.lean` | 23,496 | `f3728e5098898f90010d3091413305517cd72b8fb19c5951f2c2ee80980da81b` |
| `generated/V7MerkleK12/FunsExternal.lean` | 3,110 | `6ccf96a51761986f88cb834d130fb8fe7f2cfd8181809453c6b8939296744953` |
| `generated/V7MerkleK12/Types.lean` | 810 | `bbf00fc3958d37c1629bf18dcfe0ced39a59210cd8c56130790b51f04c0d0fad` |
| `generated/V7MerkleK12/TypesExternal.lean` | 435 | `76e2751abe0e41777e7cae8da1b3c4ecea97d0cc9d796ed55b40beaf74489016` |
| `proof/V7MerkleK12SourceBridge.lean` | 60,239 | `20507816ca0554e3211659afeb6c7ac46fe400cc599c8c3ebef1b1d3fed51a78` |
| `proof/V7MerkleK12LayoutBridge.lean` | 48,630 | `af14a41bf9b16bbaa15f8314cc6be96b91df9213ec9ace279e2ac56e573d519d` |
| `proof/V7MerkleK12AcceptedBridge.lean` | 32,585 | `f2b4b610133f57d4ad660eb82f2c6751376d14bad9390bbe2f09eb73a5e4720c` |
| `proof/V7MerkleK12TraversalBridge.lean` | 17,518 | `c46bc5cae11d1ca804276ec81c90b3356d930e052cc189a5fd389b1a0484d3e8` |
| `proof/V7MerkleK12InnerTraceBridge.lean` | 81,606 | `4aaa3c8d3951c6782a8769340c0eeb7221e567eb0e2fb1197ece486196c1a07b` |
| `proof/V7MerkleK12OuterTraceBridge.lean` | 24,873 | `f34de56330b235cee12b58437d2c3af505d58330d2f39ac9a7205d5d92257ae1` |
| `proof/V7MerkleK12CallerBridge.lean` | 132,589 | `5f80ecf03873c011274de3c2011b962e87e03d709f3b14e88689050d7be0ebe2` |
| `caller/extraction/V7MerkleCaller.llbc` | 3,625,432 | `88f4208020474047b8bbe8e7028bbff0a0460b6548c58d40c17db0649ef65e07` |
| caller normalized LLBC | — | `8d964e12a81635c597c65074f92e27608aa886e8095fd42c71ba94b01e9d5513` |
| `caller/extraction/translation.json` | 74,171 | `4cb416e1daa5819b3e5c4406f55c32cd5be6e828b382fe50029a0b2fc71fe4af` |
| `caller/generated/V7MerkleCaller/Funs.lean` | 88,305 | `06aa67e665caea1d206f01adbac5f014a4b3581ded7ddcd9f13de9f06273e999` |
| `caller/proof/V7MerkleCallerNamespaceBridge.lean` | 14,744 | `26ed6b3b4b459aef9ab45f6ba522cf7ce8bc52158470d8e5b219cbc3c654b2c6` |

The raw LLBC hash pins the archived byte stream. The normalized LLBC hash sets
only Charon's destination path fields to `null` and sorts the three serialized
name maps, matching the repository's existing independent-extraction
normalization convention.

`extraction/aeneas-failure-diagnostic-normalization.patch` is the executable
record of the sole generated-function normalization described in
`SOURCE-BOUNDARY.md`.

The `*_Template.lean` files are Aeneas's archived external templates.
`TypesExternal.lean` and `FunsExternal.lean` are the executable interpretations
used by the proof for the five focused Rust-library interfaces. Their exact
status is described in `SOURCE-BOUNDARY.md`.

## Pinned tools

| Tool | Identity |
| --- | --- |
| Charon | 0.1.223, commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, Darwin arm64 binary SHA-256 `776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375` |
| Aeneas | commit `d860ac47ed548d3da6d799afc013779ce470516c`, the three pinned patches under `toolchain/`, Darwin arm64 binary SHA-256 `c824ad52b6fecc69abd41ed3206781132f6c84850de2ee6bb5bbb0ed5ad29926` |
| Caller Aeneas | same commit and patches, Linux x86-64 static binary SHA-256 `87f65bd36e0dad06d322f833fcb4cb6c3e7d84acf149b31d0c4e61656d23ea4a` |
| Lean | 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783` |

## Focused extraction replay

The extraction equality gate is:

```sh
CHARON_BIN=/path/to/pinned/charon \
AENEAS_BIN=/path/to/patched/pinned/aeneas \
bash aeneas-verif/v7-merkle-k12-accepted-source-20260825/replay-extraction.sh
```

Under the current memory policy this command must be run on `nuc.local` only
after `MemAvailable` is at least 24 GiB, inside the established 22/28 GiB
cgroup (`MemoryHigh=22G`, `MemoryMax=28G`, `MemorySwapMax=0`). It forces one
Cargo job and sequential Aeneas translation.

## Focused Lean replay

From the repository root, point the script at the pinned Aeneas Lean backend:

```sh
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
bash aeneas-verif/v7-merkle-k12-accepted-source-20260825/replay.sh
```

The replay validates the requested production source object and all frozen
bundle hashes, rejects Lean placeholders, and copies only the packaged
generated sources and proofs, the source-pinned transparent deferred-parser
translation and bridge, plus the three source-pinned frozen grammar modules
into a disposable directory under the supplied backend. In dependency order
it compiles the standalone Merkle translation, deferred parser and parser
bridge, frozen grammar/extractor/parser-roundtrip modules, layout and hash
bridges, exact verifier inner/outer traversal bridges, result-aware caller
translation and namespace bridge, and finally
`V7MerkleK12CallerBridge.lean`. It forces `LEAN_NUM_THREADS=1` and performs no
broad repository build or test.

The focused caller re-extraction and combined namespace replay are:

```sh
CHARON_BIN=/path/to/pinned/linux/charon \
AENEAS_BIN=/path/to/result-aware/linux/aeneas \
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
bash aeneas-verif/v7-merkle-k12-accepted-source-20260825/replay-caller-extraction.sh

AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
bash aeneas-verif/v7-merkle-k12-accepted-source-20260825/replay-caller-namespace-bridge.sh
```

The final namespace replay passed in unit
`aspis-v7-caller-namespace-12`, invocation
`f0abe441f3674d20b8f1edd446abfaa6`: exit 0, 23.69 s wall,
2,612,928 KiB maximum RSS, and zero swaps.

Before compiling the deferred parser, the replay applies the frozen
`toolchain/v7-deferred-parser-combined-external.patch`. That patch makes the
parser external module import the already-compiled Merkle external module and
removes only its byte-identical duplicate `core.slice.Slice.last` definition;
the parser's other four source-pinned executable external bodies are unchanged.
The caller replay additionally applies the deterministic combined parser and
caller compatibility overlays after verifying the raw generated files.

The strongest literal frozen-predicate theorem is
`translated_caller_success_implies_accepted_two_tree_openings`; its premise is
success of the translated production
`verify_and_gamma_combine_v7_openings`, and its conclusion is the existing
`accepted_two_tree_openings (frozenTruncate sha256)` predicate.

`REPLAY-RESULT.txt` records the successful serialized NUC replay of the
integrated parser-through-caller theorem chain. The exact command, memory gate,
resource record, and complete 118-entry `#print axioms` output are frozen under
`evidence/full-replay-candidate-04/`.

## Axiom inventory

The proof sources print the axiom dependencies of the hash-input, layout, loop,
equality, accepted-traversal, caller-control-flow, and final frozen-predicate
theorems. The integrated replay emitted 118 results. Every dependency is a
subset of:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, native-decide axiom, SHA axiom, random-oracle axiom, or
source-equivalence axiom in the proof sources. SHA behavior is supplied only
through the explicit `HashCallbackEqualsSha256` interface. The complete,
unabridged output is in `evidence/full-replay-candidate-04/axioms.txt`; the
strongest caller theorem reports exactly the three dependencies shown above.

This is a focused parser/caller/Merkle source bridge, not the complete K1.2
probability reduction. `SOURCE-CALL-GRAPH.md` records the transparent graph and
`SOURCE-BOUNDARY.md` distinguishes the theorem's sole semantic SHA interface
from compiler provenance and the deliberately excluded outer-runtime and K1.2
mathematical work.
