# Generated-source proof decomposition

The final source theorem is intentionally decomposed into facts whose inputs
are literal generated equations.  None is a parser-correctness or decoder
conclusion premise.

1. `production_success_exposes_fixed_reader_trace` unfolds
   `v7_verifier.verify_v7_read_only_with_statement_digest` and the transparent
   transcript closure.  A successful result supplies the successful parser
   result, initialized fixed reader, and one ordered trace containing exactly
   641 generated `V6FixedFieldReader.next_qm31` calls followed by the literal
   successful `finish` call.
2. `parser_success_fixed_section_exact` unfolds the generated deployed parser
   and proves the returned fixed slice is exactly input bytes `0..9936`, its
   last high nibble is zero, the input length is
   `19948 + 52 * frontier_nodes`, and all returned sections end at the input
   end.
3. `fixed_reader_trace_matches_packed_limbs` proves the generated streaming
   state invariant.  At ordinal `field * 4 + limb`, `PackedM31Reader.next`
   returns `packedLimbNat packed field limb`; the four generated comparisons
   therefore establish `PackedFixedSectionCanonical packed`.
4. The semantic, point, inactive/OOD, relation, and final-vector trace
   projections establish the frozen global index order
   `1 + 270 + 87 + 1 + 2 + 24 + 256`.  At production storage sites their
   aggregate projections form `StoredFixedFieldViewExact`.
5. The pure theorem `tapeWithPackedFixedFields_constructs_exact_decode`
   constructs the exact source projection and requested decoder witness with
   no tape/input premise.  Where a pre-existing tape is already known to carry
   the source bytes, `packedFixedMessagesMatch_constructs_exact_decode_and_view`
   additionally supplies the stored-view equality.

## Streaming packed-reader invariant

The source reader is proved against the closed byte formula in
`V7Tag73FixedFieldLayoutModel`, not against a second decoder assumption.  At
the start of packed limb ordinal `k`, the generated state invariant is:

- `byte_index = (31 * k + 7) / 8`;
- `buffered_bits = byte_index * 8 - 31 * k`, hence it is in `0..7`;
- `buffer` is the still-unconsumed high suffix of the bytes already loaded;
- the next low 31 bits equal `packedLimbNat` at field `k / 4`, limb `k % 4`.

The invariant has a useful exact eight-limb cycle.  Starting with zero buffer
at limb `8 * block`, the eight generated `next` calls have buffered-bit states
`0,1,2,3,4,5,6,7`, consume exactly 31 bytes, and return to zero buffer at limb
`8 * (block + 1)`.  Thus 320 full blocks account for the first 2,560 limbs and
9,920 bytes.  The final four calls consume bytes 9,920 through 9,935; their
last four unused bits are precisely the high nibble rejected by the generated
parser.  This decomposition keeps the source proof finite while proving the
general ordinal formula rather than enumerating 2,564 unrelated cases.

For each group of four calls, the generated `qm31` constructor order is
literally `(c0.a,c0.b,c1.a,c1.b)`.  Successful generated `next_qm31` then
supplies the four strict comparisons against `P`, and its returned reader has
`remaining + 1` equal to the input reader's remaining count.  Mapping the
641-call control-flow trace through this invariant establishes
`PackedFixedSectionCanonical` without a canonical-decoder premise.

The capstone has the literal generated caller success equation as its first
logical premise.  Its canonical projected-tape form has no additional
tape/input premise.  A companion theorem for an independently supplied tape
uses only `PackedFixedMessagesMatch`, the primitive proof-bytes/tape-byte
identity; that relation contains no canonicality, decoder success, view
equality, or acceptance implication.
