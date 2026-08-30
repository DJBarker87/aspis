# V7 Tag-73 current production caller source bridge

This bundle isolates and closes the Charon/Aeneas translation boundary for
`verify_v7_read_only_with_statement_digest` at source revision
`bcd03b12293f2737dfa1da1436092a0a24a6ae24`. It does not modify production
Rust or any K1 mathematical theorem.

The unmodified complete translation exposed two context-sensitive Aeneas
failures. The exact production helpers translate independently, so the
accepted construction keeps only those helpers opaque in the combined LLBC,
translates each helper literally in its own LLBC, and reconnects the three
generated namespaces with structural, kernel-checked field/array/slice maps:

```text
current production caller
  ├─ exact translated gamma helper
  └─ exact translated qm31_dot3 helper
```

The two helper boundaries are source-extraction boundaries, not cryptographic
assumptions. Their replacement definitions execute the separately translated
production functions. The only semantic primitive boundary is whatever is
reported by the final root's `#print axioms` audit.

The complete result is now green: all 139 staged targets, the composed
production caller, the exact helper-split endpoints, the final axioms audit,
and the forbidden-construct scan pass. `REPLAY-RESULT.md` freezes the exact
hashes, resource records, and remaining source-tool boundary.

## Translator failures isolated

- `authenticate_and_fold_queries` lost the already translated gamma symbolic
  value at a later abstraction (`Could not find var for symbolic value:
  20017`).
- With gamma independently translated, the complete caller reached a distinct
  `qm31_dot3` loop join where two contexts retained the same symbolic ID with
  unequal region/type payloads.

Both helpers translate successfully on their own. No Rust arithmetic,
transcript, Merkle, work, proof grammar, or accepted result is changed.

The resulting complete graph then exposed two ordinary Rust-lowering shapes
which the pinned Aeneas does not support: a compiler-generated
`Box<MaybeUninit<[u8; 4]>>` used to construct the fixed vector
`[0, 1, 2, 3]`, and four `FnMut` closures which capture mutable accumulator
state. `current-caller-aeneas-source-normalization.patch` is applied only to a
task-owned copy of the pinned source. It replaces those shapes with explicit
`Vec::push` and ordinary `&mut` helper calls while preserving operation order,
field arithmetic, returned values, and transcript bytes. Production Rust is
unchanged. The exact input, patch, and output digests are frozen under
`source/`, and focused release tests check the grouped-fold reference, Tag-73
terminal dot product, and hard-pinned fingerprint values before extraction.

This normalization is a transparent source-extraction shim in the ordinary
Charon/Aeneas/compiler trust base. It is not a cryptographic premise and does
not make any verifier value trusted.

The normalized complete caller exposed one further Aeneas-only failure. Its
optional loop-output reordering pass asserted that every `break` payload had
the inferred output arity, although the pass already has a semantics-preserving
no-reorder path. `aeneas-d860ac47-loop-break-arity-preflight.patch` scans the
breaks before reordering and takes that existing path when their arities do not
match. The generic production function and the exact concrete halves translate
without this composition, confirming that the gate is a translator
normalization boundary rather than a verifier relation change.

## Generated-table resource fix

The first staged Lean attempt exposed a separate elaboration pathology: one
generated 256-entry circle-table declaration reached 22.87 GB without
finishing. It was stopped at the mandatory review point and was not rerun with
a larger cap.

`chunk-aeneas-circle-tables.pl` mechanically validates and hashes all five
generated tables, emits exact 16-entry chunks, and reconstructs the production
arrays with typed `append16`/`append32`/`append64`/`append128`/`append256`
joins. The first exact consumer then compiled in 1.68 seconds; the complete
focused table/consumer run peaked at 2,515,948 KiB with zero swap.

Raw Aeneas templates remain frozen. The chunker is a replayed staging step and
records both source-token and expanded-pair SHA-256 digests.

The same policy is applied to the generated 15-entry atomic copy-pattern
registry. `chunk-aeneas-atomic-patterns.py` validates every original record
token, records source and expanded hashes, emits one typed record per module,
and reconstructs the exact production array. This removes the second dense
elaboration graph without changing any record field or caller value.

The final stage also applies guarded Lean-parser/standard-library
compatibility fixes whose exact occurrence counts are frozen: the generated
closure-product parentheses, 80 post-shadow qualifications of
`Aeneas.Std.lift`, two no-op `FnMut` result pairs, and executable models for
the three scalar intrinsics and three iterator operations first required by
the accepted caller. Each rewrite is checked before and after application.

## Trust boundary

The ordinary Charon, Aeneas, compiler, and Lean kernel provenance remains in
the toolchain trust base. Generated `*_Template.lean` files are archival and
must never be imported. Final accepted modules use executable external models
and are scanned for `sorry`, `admit`, `sorryAx`, `native_decide`, and
project-specific axioms.

See `REPLAY-RESULT.md` and
`docs/research/v7-tag73-current-caller-aeneas-unblock-20260830.md` for the
exact result and resource evidence.
