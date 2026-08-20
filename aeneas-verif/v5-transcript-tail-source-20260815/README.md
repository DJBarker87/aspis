# V5 transcript-tail source proof

This bundle checks the production function
`derive_v5_complete_queries_for_selector_from_transcript` at the point where
the verifier reads the final polynomial, adds the last transcript inputs, and
asks the transcript for 18 query positions.

Charon extracts the unchanged production function. The pinned Aeneas version
then stops on the four-iteration Rust loop because it does not support `?`
returns inside loops. For translation only, the recorded patch replaces that
fixed loop with the same four decoder calls written out at indices 0, 1, 2,
and 3. The production Rust file is not changed.

The generated Lean and `generated_tail_success_returns_exact_decodes_and_queries`
prove that every successful translated execution:

- calls the final-value decoder at indices 0, 1, 2, and 3 in that order;
- accepts only selector values below 3;
- requests exactly 18 query positions, with bound `2^17` and draw limit 64;
- returns exactly the 18 values supplied by the transcript query sampler; and
- places the four decoder results into the returned polynomial in source order.

The external Lean definitions are deliberately observational. A decoded field
value is represented by its decoder index, and a transcript carries a supplied
query vector. The transcript observer now also records the final-polynomial
absorb, final work helper, selector absorb, and query-sampler call. The checked
theorem proves their exact labels, payloads, nonce, query count, `2^17` bound,
and draw limit on every successful generated execution. This proves call order
and data flow. It does not assume or prove field decoding, SHA-256,
Fiat-Shamir security, or the probability distribution of the supplied queries.

`V5TranscriptTailFinalJoin.lean` converts that observation trace to the
maintained transcript model. Once the parsed final-polynomial bytes, final
nonce, and selector are identified with the maintained input, a successful
generated tail has exactly `sourceTail`: final polynomial absorb, final work
check and absorb, selector absorb, then the query squeeze. No additional
transcript-order assumption remains in this tail segment.

## Source boundary

The only source rewrite in this bundle is the fixed four-step loop expansion.
Its equivalence to the original four-iteration Rust loop is directly visible in
the patch, but is not itself a theorem about Rust compilation.

The higher wrapper `derive_v5_selected_good_queries_from_transcript` is now
translated and joined to this theorem in
`../v5-transcript-selected-wrapper-source-20260820/`. That proof shows that the
same selector and returned query array flow through the wrapper's range and
candidate checks. The candidate's GoodA/GoodB meaning and the concrete
transcript/hash primitives remain separate proof and cryptographic boundaries.

The proof is probability-neutral. Its printed axioms are only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.
