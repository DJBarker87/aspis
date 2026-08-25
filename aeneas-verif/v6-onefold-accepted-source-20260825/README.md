# V6 accepted-source bridge

This bundle pins the V6 production verifier's accepted Rust result flow to a
kernel-checked Lean model.  It contains two Charon/Aeneas extractions:

- `V6AcceptedKernel`: the exact production root
  `verify_v6_read_only_with_statement_digest_and_schedule`;
- `V6DeferredParser`: the structural parser called by that root.

The accepted-kernel theorems prove that parser or transcript rejection stays
fail-closed and that success returns the transcript result verbatim.  The
parser theorems expose the translated layout parser and its frontier-cap
rejections.  Arithmetic, transcript grammar, Merkle/frontier semantics,
query batching, relation folds, terminal obligations and hiding factorization
are proved in the focused `AspisFormal/V6*.lean` modules rather than being
silently attributed to this wrapper proof.

## Pinned tools

| Tool | Identity |
| --- | --- |
| Charon | 0.1.223; binary SHA-256 `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c` |
| Aeneas (Darwin arm64) | commit `d860ac47ed548d3da6d799afc013779ce470516c` plus `toolchain/aeneas-d860ac47-v6-result-flow.patch`; binary SHA-256 `83a221f4c4cd2041e5ba942c945f9b0f2732031c6938b71cb3cc17a9de1d42ce` |
| Aeneas (Linux x86-64 static) | the same commit and result-flow patch, plus the OCaml 5.2 build-only `toolchain/aeneas-d860ac47-ocaml52-exhaustive-match.patch`; binary SHA-256 `c8dbc1f076bcbacf3493be46f7be669051c60b206ca00a6f0abf6df07b7ce50b` |

The Aeneas patch adds result-aware function-pointer translation and the
immutable frozen-borrow join handling required by the accepted closure graph.
The Linux-only OCaml 5.2 patch removes one catch-all arm that the compiler
proves unreachable and rejects under warning-as-error; it does not alter a
reachable translation case.  The hermetic Linux build reports its embedded
version as `unknown` because its Nix source omits `.git`.  Replay therefore
checks that exact value only for the pinned Linux binary, normalizes only that
field to the archived `d860ac47-dirty`, and compares every other translation
metadata byte.
The generated Lean then needs one syntax-only pretty-printer correction,
recorded in `generated/aeneas-lean-printer-precedence.patch`: parentheses are
added around a function type before its product with `V6OneFoldWire`.  The
unpatched type is parsed with the wrong precedence; the corrected type is the
closure type recorded in the LLBC.

## Replay

From the repository root, set the three tool paths and run:

```sh
CHARON_BIN=/path/to/charon \
AENEAS_BIN=/path/to/aeneas \
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
bash aeneas-verif/v6-onefold-accepted-source-20260825/replay.sh
```

The replay:

1. verifies every pinned source and bundle hash;
2. re-extracts both LLBC graphs with the options embedded in the archived
   extracts;
3. compares canonicalized LLBC hashes (Charon records output paths and emits
   three name-only hash maps in process-random order; the replay nulls only
   those paths and sorts only those metadata maps, while retaining every
   executable IR node; the raw bytes are also archived separately);
4. regenerates Aeneas Lean, applies the one recorded printer correction and
   compares the generated files byte-for-byte (with only the checked embedded
   Aeneas-version field normalized between the two pinned platform builds);
5. compiles both source-bridge proofs against the pinned Aeneas Lean backend;
6. rejects `sorry` or `admit` in every checked Lean source.

The replay does not claim a formal theorem about SHA-256, Solana's runtime or
the opaque interfaces listed by `#print axioms`.  Those boundaries remain
explicit and are covered by cryptographic assumptions, focused proofs,
differential tests, reproducible SBF bytes and runtime evidence.
