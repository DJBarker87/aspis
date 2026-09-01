# V7 Tag-73 fixed-field accepted-source bridge

This bundle verifies the canonical 641-QM31 fixed-field path used by the
production Tag-73 verifier.  Its source revision is the exact head of
`origin/v7/split-tensor` recorded in `source/REVISION`.  Production Rust is
not modified by this bundle.

`source/SOURCE-CLOSURE.sha256` lists the files directly used by the bridge.
The broader `source/PRODUCTION-RUST-CLOSURE.txt` additionally pins all 115
Rust and Cargo inputs below the three translated project crates.  Replay
recomputes the sorted per-file manifest and rejects any aggregate other than
the recorded SHA-256 value before Charon starts.
`source/REQUIRED-TRANSLATED-ITEMS.txt` is checked against the generated Lean
source after Aeneas, so omission of the accepted caller, parser, fixed reader,
streaming reader, typed section consumers, or little-endian writers is a hard
replay failure.
The Lean-4.32 staging gate replaces every generated external template with a
tracked executable model. The complete translated production root now has an
exact `#print axioms` set of only `propext`, `Classical.choice`, and
`Quot.sound`; there is no project/runtime axiom or native-decision certificate
in that closure.

The accepted production route is:

```text
dispatch tag 73
  -> process_v7_atomic_instruction
  -> verify_v7_read_only_with_statement_digest
  -> V7CompactOneFoldWire::parse_deferred_canonicality
  -> verify_v7_compact_transcript_and_relation_prepared
  -> verify_v7_compact_transcript_and_relation_prepared_with_hiding_context
  -> V6FixedFieldReader::new
  -> 641 ordered V6FixedFieldReader::next_qm31 calls
  -> V6FixedFieldReader::finish
```

The fixed reader order is exactly:

```text
0       initial claim
1..270  10 semantic rounds x 27 sent coefficients
271..357  3 point rows x 29 columns
358     inactive claim
359..360  2 OOD values
361..384  4 relation rounds x 6 sent coefficients
385..640  256 final coefficients
```

The production body stores these values as 2,564 consecutive 31-bit limbs in
9,936 bytes.  Each successful reader step extracts limbs in
`(c0.a,c0.b,c1.a,c1.b)` order, rejects a limb at or above `2^31-1`, and the
transcript writes every accepted value as four little-endian `u32` words.

`PackedFixedMessagesMatch` is the primitive tape/input relation used by the
Lean bridge.  It equates each tape field with the four little-endian words
obtained from the parser's fixed-section bits; it does not state canonicality,
decoder success, or the desired existential.  The pure layer also defines
`tapeWithPackedFixedFields`, which constructs that representation directly
while preserving every non-fixed message, derived challenge, search witness,
frontier count, and circle return.  Thus the source capstone can target the
canonical projected tape without taking the relation as a premise.  Literal
translated reader success first establishes `PackedFixedSectionCanonical`;
the pure theorem then builds `decodedPackedFields` and discharges the
already-frozen `FixedFieldDecodeExact` predicate.

Production does not retain one aggregate `FixedFieldView`: it keeps the
semantic running state, the 3-by-29 point-claim array, the 4-by-6 relation
array, and the 256-value final vector at their respective control-flow sites.
The source trace proves those site projections in the frozen global order;
`StoredFixedFieldViewExact` packages exactly those projections and its
extensional theorem identifies them with `decodedFixedFieldView`.

`replay.sh` is intentionally memory-gated.  Charon, Aeneas, and generated
Lean compilation may run only on the dedicated Linux build host, only when `MemAvailable` is at
least 24 GiB, and under the user-authorized parallel-lane envelope
`MemoryHigh=18G`, `MemoryMax=20G`, and `MemorySwapMax=0`.  Focused static
checks remain safe locally.

Status is recorded in `REPLAY-RESULT.md`. Translation and executable-root
closure are green.  The generated semantic-verifier root now also constructs
the exact `CurrentSourceFixedFieldProjection` consumed by K1.3 directly from
literal success: all 641 reader calls, all 2,564 strict limb comparisons,
canonical padding and successful `finish` are internal consequences rather
than premises.

The remaining outer-source work is narrower and explicit: invert the current
`verify_v7_read_only_with_statement_digest` caller, connect its opaque parser
call to the separately translated exact current parser, identify the returned
fixed slice with this generated root's wire, and transport that projection to
each done restoration node's literal `rawMessages`.  The generated namespaces
must be joined by proved value/layout maps or replaced by one current combined
translation; namespace identity must not be assumed.
