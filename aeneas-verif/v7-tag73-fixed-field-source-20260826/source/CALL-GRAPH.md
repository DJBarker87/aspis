# Accepted production call graph

The numeric Tag-73 branch in
`programs/aspis-verifier/src/dispatch.rs` invokes
`v7_transaction::process_v7_atomic_instruction`.  After the exact instruction
length/tag parser and proof-account lifecycle checks, the accepted closure
calls `v7_verifier::verify_v7_read_only_with_statement_digest`.

That verifier calls
`V7CompactOneFoldWire::parse_deferred_canonicality`.  The parser requires an
exact proof-body length, caps the common frontier count at 203, slices exactly
9,936 fixed-field bytes at offset zero, rejects the four unused high bits in
the last packed byte, and leaves no trailing alternative layout.

The resulting V7 body offsets are exact:

| section | start | length | end |
|---|---:|---:|---:|
| fixed 2,564-limb section | 0 | 9,936 | 9,936 |
| C1 root | 9,936 | 26 | 9,962 |
| C2 root | 9,962 | 26 | 9,988 |
| three work nonces | 9,988 | 24 | 10,012 |
| 16 query records | 10,012 | 9,936 | 19,948 |
| C1 frontier | 19,948 | `26 * frontier_nodes` | variable |
| C2 frontier | variable | `26 * frontier_nodes` | exact body end |

Each query record is `403 + 186 + 32 = 621` bytes.  Thus the only accepted
body length is `19,948 + 52 * frontier_nodes`; at cap 203 it is 30,504 bytes.
The parser first checks equality with that length, then uses total `split_at`
operations whose lengths sum to it.  Consequently the returned C2 frontier
ends at the input end: no trailing byte or alternate fixed-field section can
be accepted.

The verifier then calls
`verify_v7_compact_transcript_and_relation_prepared`, which delegates to
`verify_v7_compact_transcript_and_relation_prepared_with_hiding_context`.
That production function creates `V6FixedFieldReader` on the parser's
`fixed_fields_packed` slice.  Its successful control flow consumes:

- `verify_compact_semantic_sumcheck`: 1 + 10 x 27 = 271;
- `decode_and_absorb_point_claims`: 3 x 29 = 87;
- `finish_onefold_relation`: 1 inactive + 2 OOD = 3;
- `decode_compact_relation_fields`: 4 x 6 = 24;
- `decode_and_absorb_final256`: 256;
- `V6FixedFieldReader::finish`: remaining count must be zero.

The total is 641.  Every `?` edge converts a `V6WireError` into
`V6TranscriptError::Wire`, then into `V7VerifyError::Transcript`, so no
canonicality, length, read, or finish failure has an alternate success path.

`PackedM31Reader::qm31` invokes the same streaming `next` four times in
`(c0.a,c0.b,c1.a,c1.b)` order.  `next` accumulates input bytes at the current
low-bit buffer position, returns `buffer & 0x7fff_ffff`, then shifts the
buffer by 31.  `V6FixedFieldReader::next_qm31` rejects each of those four
words unless it is strictly below `P = 0x7fff_ffff`.  `QM31::write_le_bytes`
then writes `c0` followed by `c1`, with each `CM31` writing `a` followed by
`b` and each `M31` using `u32::to_le_bytes`.

The ASVQ Pool Tag-73 handler reaches the same read-only verifier.  Pool-native
private-transfer and withdrawal helpers use the hiding-context variant
directly and therefore share the identical fixed-field reader path.
