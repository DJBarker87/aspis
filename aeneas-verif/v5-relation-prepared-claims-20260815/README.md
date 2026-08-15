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

The direct translation of `prepare_v5_pcs_claims` is still blocked because
the pinned Aeneas version does not support its early return inside nested
loops. The remaining source connection is therefore narrow and explicit:
on a successful call, its outer loop must place the 76 already-proved decoded
values into four nineteen-entry arrays in `19 * point + column` order and call
the proved five-block expression for each row. Tests are not used as a
substitute for that universal equality.

Run `replay-lean432.sh` with the pinned tool paths described in the script.
The replay checks source hashes, regenerates the Lean translations, compares
them byte-for-byte with the checked snapshots, and rebuilds every proof.
