# V7 K1.2 translated-source boundary report

## Exact source and generated control flow

`extraction/V7MerkleK12.llbc` is Charon's archived extraction of the four named
roots. There is no extraction-only Rust wrapper and no production overlay.
`replay-extraction.sh` re-extracts from requested production commit
`01f5f4f722cfdf6bc29c157fc3db6ff5ab5e413a`, tree
`f634f5d7d8ff6606f1a9db40771111e49f5f7e53`, and establishes byte equality
after destination/name-map normalization. It then establishes byte equality of
the Aeneas output after the pinned failure-diagnostic-only normalization.

`generated/V7MerkleK12/Funs.lean` contains transparent definitions for the
deployed truncate, typed private-leaf hash, typed node hash, two-tree verifier,
both translated loops, and their loop bodies. The source bridge reasons about
those definitions directly.

The accepted-path theorem proves exact translated result flow. In particular,
it excludes `some true` from the inner body, inner loop, outer body, and outer
loop; then it inverts all successful public checks and the final two root
comparisons. The final root equality is derived from translated
`PartialEqArray.eq = .ok true`, not assumed.

The integrated endpoint is
`translated_caller_success_implies_accepted_two_tree_openings` in
`proof/V7MerkleK12CallerBridge.lean`. Its source premise is literal success of
the translated production `verify_and_gamma_combine_v7_openings`. From that
control flow it constructs the opening proof required by the already-frozen
Lean `accepted_two_tree_openings` predicate. The theorem does not take an
accepted-opening witness, caller-agreement fact, traversal invariant, source
equivalence, or desired implication as a premise.

## Failure-only diagnostic normalization

Aeneas initially emitted a formatting `toStr` term for the Rust
`expect("fixed 26-byte SHA-256 prefix")` diagnostic. The archived
`Funs.lean` replaces only that diagnostic argument with the empty `Str` at the
translated `core.result.Result.expect` call.

This changes only the error payload of that fixed-size conversion's failure
branch. It does not change the success value, hash input, branch decision,
loop state, root comparison, or accepted-path result. The source theorem makes
no claim that the normalized diagnostic text is byte-identical to Rust's panic
message. This is the bundle's sole generated-function normalization. Its exact
replay patch is
`extraction/aeneas-failure-diagnostic-normalization.patch`.

## Executable Rust-library interfaces

Aeneas leaves these five library calls opaque in its generated external
template:

- `core::iter::traits::iterator::Iterator::any`;
- `core::slice::iter::Windows::next`;
- `core::slice::Slice::last`;
- `core::slice::Slice::windows`; and
- `alloc::vec::Vec::clear`.

`TypesExternal.lean` and `FunsExternal.lean` provide executable Lean
interpretations for those interfaces. They are definitions rather than axioms,
which is why the final axiom print contains only Lean foundation axioms.

The caller translation has additional generated external templates. Every
template entry used by the integrated replay is either reused at an identical
signature from the standalone Merkle/parser executable externals or supplied
by an executable Lean definition in
`caller/generated/V7MerkleCaller/{TypesExternal,FunsExternal}.lean`. The
deterministic compatibility overlays resolve duplicate generated namespaces
and failure-message-only artifacts; they add no axioms or acceptance
assumptions.

These definitions mean the kernel theorem has no opaque standard-library
semantic premise. The evidence package still records Charon/Aeneas and the
external-definition review as part of the source-tool trust base; it does not
claim that Charon or Aeneas is a kernel-verified compiler. That provenance
qualification is distinct from the theorem's sole explicit semantic interface,
SHA-256.

## Production caller and parser coverage

The original four-root extraction does not contain
`V7CompactOneFoldWire::parse_deferred_canonicality`,
`V7CompactOneFoldWire::query`, or
`verify_and_gamma_combine_v7_openings`. Consequently its translated theorem
does not by itself prove caller facts. The bundled exact-revision caller
extension at `caller/extraction/V7MerkleCaller.llbc` now contains `query`, the
caller, both Merkle paths, gamma combination, and field helpers. Its generated
hash callback is result-valued, so hash failure remains in translated control
flow.

There is an independently translated parser in
`aeneas-verif/v7-onefold-accepted-source-20260825/parser/`; it uses an
extraction-only free wrapper with a kernel-checked `rfl` equality to the
production inherent method. The layout bridge imports that transparent parser
bridge and proves its successful exact offsets, tags, little-endian fields and
raw Merkle slices, as well as wrong/trailing-length rejection.
`caller/proof/V7MerkleCallerNamespaceBridge.lean` proves the duplicate Merkle
definitions equal across generated namespaces and transports every parser wire
field to the caller wire type with definitional two-sided inverses. Its query
result is obtained only by invoking the translated production query body.

`proof/V7MerkleK12CallerBridge.lean` then inverts the complete translated
caller: exactly 16 paired queries, equal public positions in both trees,
position bounds and duplicate rejection, distinct C1/C2 tags, one shared salt
per pair, depth 18, paired frontier traversal with bit-directed orientation,
and final comparison with `wire.c1_root` and `wire.c2_root`. The parser theorem
separately shows that malformed or trailing raw bytes cannot produce its
successful wire; the caller theorem shows that any query, checked-arithmetic,
hashing, sorting, duplicate, path, length, frontier, or root failure cannot
produce caller success. `SOURCE-CALL-GRAPH.md` records the exact transparent
graph.

## Sole semantic theorem boundary and excluded work

The sole semantic premise of
`translated_caller_success_implies_accepted_two_tree_openings` is
`HashCallbackEqualsSha256 sha256 hash`. It states the allowed SHA primitive
interface for successful calls. The proved formats are exact:

- C1: `0x10 || 0x71 || value[403] || salt[32]`;
- C2: `0x10 || 0xf1 || value[186] || salt[32]`;
- node: `0x11 || left[26] || right[26]`; and
- truncation: precisely bytes `0..26` of the same 32-byte SHA result.

No collision, binding, probability, or random-oracle claim is used to reach
the frozen accepted-opening predicate.

This bundle deliberately does not prove:

- SHA-256 correctness, collision resistance, preimage resistance, or its
  random-oracle interpretation;
- the numerical probability of accepted extraction failure;
- the 208-bit truncation collision accounting;
- the separate pure K1.2 complete `2^18 + 2^18` query-graph extractor or its
  causal provenance theorem;
- the complete production verifier/SBF call chain to that caller;
- SBF compilation, Solana syscalls, account state transition, or runtime
  semantics; or
- the external circle-code decoding theorem.

The SHA callback remains an explicit parameter. The hash-input theorems prove
the exact typed preimages and 26-byte truncation behavior for translated
successful calls; they do not instantiate SHA-256 as a Lean random oracle.

Consequently, this package closes the translated Rust parser/caller/Merkle
bridge to the existing Lean accepted-opening predicate. It deliberately does
not close K1.2's raw `accepted ∧ extractionFailure` probability event or the
end-to-end Tag-73 soundness theorem.
