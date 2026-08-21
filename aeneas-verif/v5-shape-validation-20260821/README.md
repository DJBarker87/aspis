# V5 shape-validation return-value proof

The production FRI consumer validates a fixed `CirclePcsShape` before it
derives the coordinate tables.  The Lean consumer extraction originally left
that method opaque.  The coordinate proof therefore needed this small code
fact as an input:

> If `CirclePcsShape::validate(input)` succeeds with `output`, then
> `output == input`.

The Kani harness proves that statement for every possible value of every
field in `CirclePcsShape`.  It calls the unchanged production
`CirclePcsShape::validate` through a behavior-free wrapper.  The successful
run checked 312 properties with no failures; 13 paths were unreachable.

This discharges `ValidationSuccessPreservesShape` as a Rust code-verification
obligation.  It is not a cryptographic assumption.  The Lean theorem remains
explicitly parameterized by that proposition because Kani does not emit a
Lean proof term.

The check is pinned to:

- `cargo-kani 0.67.0`;
- production `crates/aspis-core/src/circle_pcs_shape.rs` blob
  `27fea89d4095718a0df5d22532d6cd4d24a5a6b3`.

Run:

```sh
./aeneas-verif/v5-shape-validation-20260821/verify.sh
```
