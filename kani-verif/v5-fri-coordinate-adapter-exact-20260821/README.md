# Released V5 coordinate adapter proof status

This bundle contains a completed proof for the selected circle-point stage and
the extraction-friendly Rust reference used by the Charon/Aeneas proofs.

The subject is the unchanged production function
`derive_query_fold_inverses_for_circle` in
`crates/aspis-core/src/circle_fri.rs`.

The complete production-to-adapter equality is not yet proved. The remaining
work starts after the selected points: the three parent layers, denominator
array, batch inversion input and output, and returned layer arrays.

## Exact scope

The equality harness quantifies over every array of 18 layer-zero query
indices satisfying:

- every index is below `2^17`;
- the indices are strictly increasing, hence unique;
- the three later index sets are produced by the unchanged production
  `derive_circle_line_query_indices_for_count` helper, so they are the exact
  sorted/deduplicated `q >> 2`, `q >> 4`, and `q >> 6` sets;
- the domain log size is `19`;
- the inverse backend is `M31::inv`.

Those are the released verifier's accepted-path inputs. The certificate does
not claim equality for other domains, arbitrary caller-supplied parent sets,
or malformed inputs. That distinction is intentional: the extraction adapter
validates some rejected inputs in a different order, so its error value is not
identical to production for every possible bad input.

## What is proved

For every released input array, the unchanged production point generator and
the extraction adapter:

- accept the same domain-19, 18-query input shape;
- return exactly 18 points;
- return the same point at each of the 18 positions.

The replay is split into one arbitrary-fiber calculation, one acceptance and
length check, and 18 position checks. Every check produced Kani's literal
`VERIFICATION:- SUCCESSFUL` result. The replay script rejects an exit code of
zero unless that exact marker is present.

## What remains

The Lean files under `aeneas-verif/v5-fri-coordinate-source-20260820/proof/`
prove the extraction adapter's point, denominator, inverse, and output loops.
What is still missing is the corresponding source equality from the unchanged
production Rust after the selected-point call. In plain terms, the project
still needs to show that production and the adapter build the same three
parent layers, the same denominator vector, the same checked inverse vector,
and the same returned arrays.

A direct layer-one Kani attempt was stopped without a verdict. CBMC remained
in equation generation because deriving the released parent-index vectors in
the same harness repeatedly expanded allocation and deduplication paths. It
never reached the layer comparison or the solver. This is not a failed proof;
it is no proof result. The next proof must receive the already-established
parent-index stage as an input to the source-local observation wrapper rather
than recomputing it inside each layer harness.

`src/lib.rs` is a direct extraction-friendly spelling of the recorded adapter:
it fixes domain 19 and `M31::inv`, uses explicit later-layer slices, and
replaces the unsupported iterator and closure forms with `while` loops. It is
not linked into the Solana verifier.

Together with the Charon/Aeneas translation and its Lean proofs, the current
connection is:

```text
unchanged production Rust selected points
        -- universal Kani equality -->
adapter selected points
        -- remaining source equality is open -->
complete extraction-friendly Rust output
        -- Charon/Aeneas -->
Lean model and mathematical proofs
```

The completed point proof relies on Rust-to-MIR compilation, Kani/CBMC
translation, and Bitwuzla. These are toolchain assumptions, not cryptographic
probability terms.

## Pinned subject and tools

- repository parent commit: `4be6be155e966c3bebb1507b55797bdc455c3082`
- production `circle_fri.rs` Git blob: `d9382a35ec7a660b696171e7609f443995a009bf`
- production `circle_fri.rs` SHA-256: `7df47ac39aeda39b15c536927310cd7612a23984907b7eb05d32613f8e156f9b`
- production `circle_line_merkle.rs` Git blob: `088917245f072b44e1b6bb0fa02d707ba5062274`
- production `circle_line_merkle.rs` SHA-256: `8c3fe1a4a60d037e7c6bd251ac451fd314991528f3831f7f892c5fb376da821a`
- production `field.rs` Git blob: `a28ff94de05265102ca819849805a7f73c675800`
- production `field.rs` SHA-256: `dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`
- coordinate-table generator `build.rs` Git blob: `62e5f3ff65bcb35bc61db8636648ab3addfeee47`
- coordinate-table generator `build.rs` SHA-256: `ed57b3d0beb1dc8de4ed55945faae5a7be7d97b6d4ee686b24b01744e7ce54b5`
- Kani: `cargo-kani 0.67.0`
- CBMC bundled with Kani: `6.8.0`
- Bitwuzla: `0.9.1`

Run `./verify.sh` from this directory.
