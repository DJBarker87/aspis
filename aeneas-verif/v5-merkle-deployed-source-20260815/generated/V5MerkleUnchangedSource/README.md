# Generated unchanged-loop source

This directory preserves the Aeneas output in which the production
`verify_radix4_binary_cap_with_matched_topology` implementation is translated
with its original three nested mutable loops.  In particular, this output does
not replace those loops with the extraction-only `fixed_hash_radix_*` helpers
used by the earlier proof snapshot.

The input LLBC SHA-256 was
`8f0c4c27a0770c581a67202a68624e302f3d3e1be12de29f72a7f84a4190d5cd`.
It was translated with Aeneas commit
`245bc09e6fe0091d4637863b5973d0ff25cac3b7`.  The generated Rust-source
locations still point to the extraction workspace; the repository source
identity remains `06788d44d30ea8cbd391899dddaf6f0acc6e4a3f` as recorded in
the parent README.

The byte-exact translator output is retained as `TypesRaw.lean.txt` and
`FunsRaw.lean.txt`; their hashes are recorded in `source.json`.  `Types.lean`
and `Funs.lean` are the compilable view.  Its import paths were changed, an
explicit low-32-bit cast was added for Rust's `usize` shift count, and one
`Option` match was written as `Option.elim` to give Lean the same missing type
information.  Unused `Iterator` default fields that are absent from the pinned
Lean runtime were removed.  None of those changes alters the verifier loop's
branches or returned values.

The raw translation left the topology constructor, the shape validator, and
the outer five-section driver as partial bodies.  The compilable view moves
those three declarations to the explicit external boundary instead of hiding
them in proof terms.  They are not used by the unchanged radix inversion
theorem.  Separate work is required before any theorem may depend on them.

`FunsExternal.lean` also supplies direct Lean definitions for the three `Vec`
operations used by the accepted verifier path: `as_slice`, `clear`, and
`is_empty`.  Other untranslated functions remain explicitly declared at the
generated boundary.  The cryptographic hash callback remains opaque.

`V5MerkleUntouchedRadixInversion.lean` proves the exact top-level shape of
every accepted execution of the unchanged verifier: its input guards passed
and the translated nested loop returned `some true` with the same output
vectors.  It deliberately observes only values the verifier reads and does
not require equality of unused fixed-array entries.
