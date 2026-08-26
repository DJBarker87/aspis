# Exact production call graph and extraction coverage

## Requested revision

The requested production revision is
`01f5f4f722cfdf6bc29c157fc3db6ff5ab5e413a`, tree
`f634f5d7d8ff6606f1a9db40771111e49f5f7e53`.

The source bodies in `state_only_private_merkle.rs`, `v7_merkle208.rs`, and
`v7_onefold.rs` are byte-identical to the earlier bundle source revision
`1589706d38a5e8ca705fbf7aaed2c82cf8595510`. The exact-base replay does not
rely on that text comparison alone: Charon was rerun on a disposable archive
of the requested revision, and its normalized LLBC is byte-identical to the
archived LLBC. Aeneas regeneration is also byte-identical after the one pinned
failure-diagnostic normalization.

## Four-root extracted graph

The current bundle has these four Charon starting roots:

```text
v7_merkle208::truncate_sha256_v7
v7_merkle208::private_leaf_hash_v7
  -> state_only_private_merkle::private_leaf_hash
  -> v7_merkle208::truncate_sha256_v7
v7_merkle208::node_hash_v7
  -> v7_merkle208::truncate_sha256_v7
v7_merkle208::verify_two_minimal_subtrees_v7_bytes
  -> v7_merkle208::node_hash_v7
```

The requested-revision source spans recorded by Aeneas are:

| Transparent item | Exact source span |
| --- | --- |
| `state_only_private_merkle::private_leaf_hash` | `state_only_private_merkle.rs:28-35` |
| `v7_merkle208::truncate_sha256_v7` | `v7_merkle208.rs:24-28` |
| `v7_merkle208::private_leaf_hash_v7` | `v7_merkle208.rs:31-38` |
| `v7_merkle208::node_hash_v7` | `v7_merkle208.rs:41-47` |
| `v7_merkle208::verify_two_minimal_subtrees_v7_bytes` | `v7_merkle208.rs:51-128` |
| verifier outer loop/body | `v7_merkle208.rs:77-128` |
| verifier inner loop/body | `v7_merkle208.rs:80-128` |

The generated names and spans are frozen in
`extraction/translation.json`; the table is a human-readable call-graph index,
not a replacement for that metadata.

The verifier translation also contains its two reconstructed loops and the
closure used by the sorted-entry check. Aeneas-generated standard-library
external slots are supplied by the executable, non-axiom definitions listed in
`SOURCE-BOUNDARY.md`; the SHA callback is the graph's sole explicit semantic
parameter.

## Transparent production caller extension

The production composition lives in `v7_onefold.rs`:

```text
V7CompactOneFoldWire::parse_deferred_canonicality
  -> exact-length calculation and fixed byte slicing

V7CompactOneFoldWire::query
  -> C1 bytes, C2 bytes, and one shared 32-byte salt from a query record

verify_and_gamma_combine_v7_openings
  -> sort exactly V6_QUERY_COUNT = 16 public (position, ordinal) pairs
  -> reject out-of-range or duplicate positions
  -> V7CompactOneFoldWire::query
  -> private_leaf_hash_v7(hash, V7_C1_TREE_TAG = 0x71,
       record.c1_packed, record.salt)
  -> private_leaf_hash_v7(hash, V7_C2_TREE_TAG = 0xf1,
       record.c2_packed, record.salt)
  -> verify_two_minimal_subtrees_v7_bytes(
       hash, (wire.c1_root, wire.c2_root), depth = 18, entries,
       (wire.c1_frontier, wire.c2_frontier), ...)
  -> false maps to V6WireError::MerkleMismatch
```

The translated hash-input correspondence fixes the production byte grammar:

```text
C1 leaf = 0x10 || 0x71 || value[403] || salt[32]
C2 leaf = 0x10 || 0xf1 || value[186] || salt[32]
node    = 0x11 || left[26] || right[26]
```

`truncate_sha256_v7` takes precisely the first 26 bytes of the same successful
32-byte SHA result passed back by the callback. No second hash result or
handwritten digest model is substituted.

The exact source spans are parser `v7_onefold.rs:130-164`, query accessor
`v7_onefold.rs:166-179`, and caller `v7_onefold.rs:183-225`. The constants used
by that caller are `V6_QUERY_COUNT = 16` (`v6_onefold.rs:25`),
`V7_C1_TREE_TAG = 0x71` and `V7_C2_TREE_TAG = 0xf1`
(`v7_merkle208.rs:16-17`), and the literal verifier argument `18`
(`v7_onefold.rs:216`).

Those facts are covered by the separate exact-revision caller LLBC at
`caller/extraction/V7MerkleCaller.llbc`. Its normalized SHA-256 is
`8d964e12a81635c597c65074f92e27608aa886e8095fd42c71ba94b01e9d5513`.
The extraction keeps `verify_and_gamma_combine_v7_openings`, `query`, the four
Merkle functions, gamma combination, and field helpers transparent. The final
Aeneas translation uses the same result-valued hash callback as the four-root
translation.

## Transparent parser evidence

`aeneas-verif/v7-onefold-accepted-source-20260825/parser/` contains a
transparent translation of
`V7CompactOneFoldWire::parse_deferred_canonicality`. Charon selected it through
an extraction-only free wrapper because the pinned toolchain could not select
the inherent method as a standalone root. The generated free wrapper and
inherent method are definitionally equal (`rfl`) in
`extracted_entry_is_exact_deferred_parser`. The production parser body is
byte-identical at the requested revision.

That parser evidence is imported by `V7MerkleK12LayoutBridge.lean`, which
derives exact total lengths, offsets, tags, little-endian fields, roots,
frontiers, query section, shared-salt slices, and wrong/trailing-length
rejection behavior. The caller extraction independently includes
`V7CompactOneFoldWire::query` and the construction of both leaf hashes and the
two-tree verifier call.

The exact production-root translation under
`v7-onefold-accepted-source-20260825/production-root/` deliberately leaves
`verify_and_gamma_combine_v7_openings` opaque. It therefore cannot be used as
proof of the depth, count, tags, shared-salt use, roots/frontiers, or fail-closed
composition required here. An axiom/interface for that opaque function would
be conclusion-shaped for this task and is not an acceptable substitute.

## Cross-extraction composition

The required transparent roots are now present:

```text
crate::v7_onefold::parse_v7_compact_onefold_wire_deferred
crate::v7_onefold::verify_and_gamma_combine_v7_openings
```

The first name is the reviewed extraction-only wrapper, with definitional
equality to the inherent parser. The second is an unmodified production
function. `caller/proof/V7MerkleCallerNamespaceBridge.lean` proves, from the
generated definitions, equality of the duplicate truncate/leaf/node/verifier
computations (including both loop levels), and a two-sided fieldwise
equivalence between the deferred-parser and caller wire structures. Its query
wrapper invokes the translated production `query` body. No source-agreement
premise is introduced.

## Integrated success-to-accepted chain

The kernel-checked dependency chain is:

```text
translated deferred parser success
  -> exact frozen byte layout and parser correspondence
  -> fieldwise parser-wire/caller-wire equivalence
translated verify_and_gamma_combine_v7_openings success
  -> exact caller loop and duplicate-window traces
  -> 16 paired query/leaf seeds at identical public positions
  -> C1 tag 0x71 and C2 tag 0xf1 with each record's one shared salt
  -> standalone translated two-tree verifier success at depth 18
  -> exact inner and outer traversal traces
  -> position-bit left/right orientation for both trees
  -> paired frontier consumption and final transcript-root comparisons
  -> existing Lean accepted_two_tree_openings predicate
```

The final theorem is
`AspisV7MerkleK12CallerBridge.translated_caller_success_implies_accepted_two_tree_openings`.
Its source premise is literally:

```text
V7MerkleCallerGenerated.v7_onefold.verify_and_gamma_combine_v7_openings
  hash wire queries powers = .ok (.Ok output)
```

and its conclusion uses the existing frozen roots and
`accepted_two_tree_openings (frozenTruncate sha256)`. The produced opening
proof, 16-query schedule, position injectivity, traversal, and root equations
are constructed from translated control flow. The only semantic premise is
`HashCallbackEqualsSha256 sha256 hash`; there is no conclusion-shaped caller
agreement or acceptance premise.
