# V5 prepared point claims

This package checks the arithmetic used to turn the 76 uploaded evaluation
values into the four point claims consumed by the V5 verifier.

The replay extracts the production Rust with pinned Charon and Aeneas
versions. Lean proves, for every valid input rather than only the released
fixture, that:

- the production QM31 decoder agrees with the maintained little-endian model
  for each of the 76 sixteen-byte fields;
- the generated gamma-power helper returns `1, gamma, ..., gamma^18`;
- the generated dot-product helper is exact for every production block;
- the production QM31 addition used between blocks is exact;
- the fixed `4 + 4 + 4 + 4 + 3` calls include every column exactly once; and
- one shared gamma table produces the maintained nineteen-term claim for each
  of the four point-major rows.

The unmodified archived `prepare_v5_pcs_claims` still cannot be translated in
full. The project-specific Aeneas extension now lowers its nested `?` return,
then the exact archived LLBC reaches a separate Aeneas limitation: joining the
nested mutable iterators used by the nineteen-column and four-point loops.

`deployed-nested-loop-lowering.patch` is an extraction-only spelling that
decodes the same 76 fields in one loop and rebuilds row `point` from
`19 * point + column`. Lean proves for every possible decoder result that the
archived nested loop and the flat loop perform exactly the same operations in
the same order. They therefore produce the same first error and index, or the
same ordered list of 76 successful values. The existing layout theorem maps
entry `19 * point + column` to the exact uploaded bytes, and the extracted
arithmetic theorem proves the five-block expression used for each row.

The archived source and LLBC were kept unchanged. The patch and
`deployed-lowering-manifest.txt` record the archived commit, source blob, both
LLBC hashes, the transformed source blob, the generated Lean hash, and the
pinned Charon/Aeneas commits. This is a checked semantic argument for the
specific source transformation around a stated translator limitation, not a
claim that Aeneas accepted the unmodified nested mutable-iterator loop and not
a general proof of Rust source transformations.

Run `replay-lean432.sh` with the pinned tool paths described in the script.
The replay checks source hashes, regenerates the Lean translations, compares
them byte-for-byte with the checked snapshots, and rebuilds every proof,
including the deployed-loop lowering theorem.
