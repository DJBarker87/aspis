# V7 accepted-source bridge

This bundle closes the Charon/Aeneas result-flow bridge for the deployed V7
tag-73 verifier without changing production Rust or rebuilding the SBF.

1. `production-root/extraction/V7ProductionRoot.llbc` is Charon's extraction
   from the **byte-identical deployed Rust source** at commit
   `1589706d38a5e8ca705fbf7aaed2c82cf8595510` (tree
   `d43572d059a48a871933be4ab7067e7ded2fab28`).
2. The pinned Aeneas revision plus
   `toolchain/aeneas-d860ac47-static-return-loan.patch` translates that exact
   LLBC directly. No extraction-only Rust wrapper is involved in
   `production-root/generated-exact/V7ProductionRoot`.
3. `production-root/proof/V7ProductionRootSourceBridge.lean` kernel-checks
   exact success, parser fail-closure and transcript fail-closure for the
   deployed root across its generated typed interfaces.
4. The separately generated `V7DeferredParser` bridge still proves its free
   wrapper/inherent-method equality by `rfl` and proves the cap-203 rejection
   path.

`SOURCE-BOUNDARY.md` records the translator defect, its narrow correction and
the remaining ordinary Aeneas/opaque-function trust boundary. The former
`V7-SOURCE-OVERLAY-EQUIVALENCE` boundary is not used by the direct-root proof.
The earlier overlay extraction and failure logs remain archived only as
diagnostic history.

## Pinned deployed inputs

| Item | Size | SHA-256 |
| --- | ---: | --- |
| `programs/aspis-verifier/src/v7_verifier.rs` | source | `95eae0a76c7bd2115d700b3ec4cf8f5900d63a7ebd231d9a55115e72ac7dcacc` |
| `programs/aspis-verifier/src/v7_transaction.rs` | source | `d3c381ad8ded497a720831b19277d332b2860e81187f0de29650ec1280dea470` |
| `programs/aspis-verifier/src/v6_verifier.rs` | source | `07983a50378aafa470355b6b5599974da2e55a096116b2f3ab1a180cec951062` |
| `crates/aspis-core/src/v7_onefold.rs` | source | `2104684c2a18a02031b6355a89bfdcbc20f3f2a3fd4dc966c54f79de966cf21f` |
| `crates/aspis-core/src/v6_transcript.rs` | source | `8422e8fa817fae3a7db01976725fcfd3642ea837f4e87366829f63309c6f28d3` |
| `crates/aspis-core/src/v6_onefold.rs` | source | `61406f4631a01a0bb2c59847867acf878546808e79ca7b5671f2e6df6bbdbc76` |
| `crates/aspis-statement/src/atomic_state_only_terminal.rs` | source | `824bf54355a141400c8092ebc7b3cd024f592a2049288335b69237adcca391f9` |
| `Cargo.lock` | source | `354a35fbc0b3fb26e5529db67188e4bdb687e234000ddcdaeabda818ebab013b` |
| deployed `aspis_verifier_v7.so` | 1,152,504 bytes | `0d3c21f3ba9b291149aa82d9632417669bbe9a6490a46f718522666b47a670f4` |
| frozen `v7-proof.bin` | 30,504 bytes | `e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb` |
| frozen `v7-statement.json` | 937 bytes | `7dd15bd17b8f052d540d0187caf4f1d616f4220e66a14be78b56f9c736a5a375` |

`DEPLOYED-SOURCE.sha256` pins the source files from the archived deployed
commit. `GENERATED-PROOF.sha256` pins every generated Lean and handwritten
bridge proof byte. `MANIFEST.sha256` pins the complete bundle plus the frozen
deployed artifacts above.

## Pinned tools

| Tool | Identity |
| --- | --- |
| Charon | 0.1.223, source commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, Darwin arm64 binary SHA-256 `776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375` |
| Aeneas | commit `d860ac47ed548d3da6d799afc013779ce470516c` plus the three pinned patches under `toolchain/`, Darwin arm64 binary SHA-256 `c824ad52b6fecc69abd41ed3206781132f6c84850de2ee6bb5bbb0ed5ad29926` |

The V6 result-aware function-pointer and borrow-join patch remains unchanged.
The new static-return patch models an opaque immutable `&'static T` result with
the same persistent dummy-loan mechanism already used for immutable globals,
erases static only in the runtime context after selecting that case, and fixes
an existing comparison against the unerased rather than erased destination
type. The exact generated root needs the same syntax-only Lean pretty-printer
precedence correction as V6, recorded in
`production-root/aeneas-lean-printer-precedence.patch`.

## Replay

From the repository root:

```sh
CHARON_BIN=/path/to/pinned/charon \
AENEAS_BIN=/path/to/patched/aeneas \
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
bash aeneas-verif/v7-onefold-accepted-source-20260825/replay.sh
```

Replay extracts from a disposable `git archive` of the deployed commit, never
from the dirty working tree. It re-extracts the exact production LLBC,
translates the byte-identical root directly, regenerates Lean byte-for-byte,
compiles the direct-root and parser source-bridge proofs, and rejects
`sorry`/`admit` in all checked bundle Lean. `LEAN_NUM_THREADS=1`, Aeneas
`-sequential`, and `CARGO_BUILD_JOBS=1` are forced to prevent a local memory
spike.

`EXACT-ROOT-REPLAY-RESULT.txt` records the final serialized replay. The older
`REPLAY-RESULT.txt` records the superseded diagnostic overlay replay.

The bridge does not formalize SHA-256, Solana runtime semantics, SBF
compilation, or the correctness of the Charon/Aeneas translators themselves.
The generated opaque parser, schedule, transcript, field, terminal and Solana
functions remain explicit typed interfaces, not hidden theorems.
