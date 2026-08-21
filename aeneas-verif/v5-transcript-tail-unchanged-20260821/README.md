# Unchanged V5 transcript-tail proof

This bundle proves the production function
`derive_v5_complete_queries_for_selector_from_transcript` without rewriting
its four-iteration Rust loop. The production source still uses
`final_polynomial.iter_mut().enumerate()` and `?` inside the loop.

The checked Lean theorem follows the mutable iterator's forward state and its
write-back functions. On every successful generated execution it proves that:

- the decoder is called at indices 0, 1, 2, and 3 in that order;
- those four values are written back to the returned polynomial in that order;
- the selector is below 3;
- the query call asks for 18 positions with bound `2^17` and draw limit 64;
- the returned queries are exactly the transcript sampler's 18 values; and
- the final-polynomial, final-work, selector, and query calls have the exact
  labels, payloads, nonce, and order used by the maintained transcript model.

The proof is deliberately about data flow and call order. Its field values are
observed by decoder index, and its transcript is an observation state. Field
decoding, hash security, Fiat-Shamir security, and query-distribution claims
are separate proofs or explicit cryptographic assumptions.

## Aeneas iterator boundary

The patched Aeneas translator accepts the unchanged Rust loop and produces the
raw files in `generated/raw/`. The raw function translation exposes a separate
Aeneas Lean-library limitation: the generic `Iterator` interface returns a
pair, while mutable iteration also needs a write-back function.

The compiling copy therefore makes exactly three checked substitutions:

1. a type-correct view used to construct the generic iterator trait;
2. a specialised `Enumerate<IterMut>::next` that preserves the write-back; and
3. a specialised mutable `enumerate` constructor.

Their definitions are in `FunsExternal.lean`. `check-normalization.py` starts
from the pinned raw output, applies only those three substitutions plus the
standard Lean-4.32 import expansion, and requires a byte-for-byte match with
the checked generated files. This compatibility model is an explicit Aeneas
Lean-backend boundary; it is not described as a theorem about the translator.

## Pinned extraction

- Aspis source commit: `80b8793f0da0fcfc294b70954f32ee08525552e7`
- production source SHA-256:
  `6f40c88c7a6b9f1ce657dd07eaa3e323c4bd3578839d874ba0a16c0117ce8224`
- Aeneas base commit: `d860ac47ed548d3da6d799afc013779ce470516c`
- extracted LLBC SHA-256:
  `e1c27cadd32871b8dd24271ea902505450969461a800f889084eb4517452ad10`
- raw generated `Funs.lean` SHA-256:
  `03744bf055fa8c4bd4477c8ca55687c9ca7e5c1ad7fe652c191a58080a414390`
- raw generated `Types.lean` SHA-256:
  `ceb7d12bd8c2c7f23a28e3f37106ab69ad6558a7973098aa2ab6aed2d711951f`

The three narrow Aeneas join fixes used for extraction and their regression
test are recorded in `extraction/aeneas-mutable-iterator.patch`.

## Check

Run the exact normalization check:

```sh
python3 check-normalization.py .
```

Then compile `V5TranscriptTailUnchangedProof.lean` and
`V5TranscriptTailUnchangedFinalJoin.lean` with the pinned Lean 4.32 and Aeneas
library paths. The printed axioms for the public theorems are only
`propext`, `Classical.choice`, and `Quot.sound`.
