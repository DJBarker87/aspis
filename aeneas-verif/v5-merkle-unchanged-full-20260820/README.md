# Unchanged V5 Merkle extraction: concrete external semantics

This bundle records the Aeneas translation of the unchanged V5 Merkle parser,
topology constructor, authentication loops, and five-section driver.  The
generated `Types.lean` and `Funs.lean` files are retained byte-for-byte.  Only
the generated external templates were filled in by hand.

## Generated snapshot

| File | SHA-256 |
|---|---|
| `generated/V5MerkleUnchangedFull/Types.lean` | `1179f5c160138711a16285e8fdcc0b4b93aeb7ac98135157b8839c31c6170437` |
| `generated/V5MerkleUnchangedFull/Funs.lean` | `7f89a145aef6103bdb7238f94ac72b56e5cbcfd21ad4a1634bae2b94a17d4c38` |
| `generated/V5MerkleUnchangedFull/TypesExternalRaw.lean.txt` | `bba20f3dd60edb17b0722f48b89185216e8be4dcf5b0c6181af21f8127ddf3e9` |
| `generated/V5MerkleUnchangedFull/FunsExternalRaw.lean.txt` | `ba0d9ca8b931467748335d921e0478066e42a0eab5b1cb95b8e209f6ab5cfee1` |
| `translation.json` | `4a56aaaf8071b598bab4b49289849e3a9da5d663a5104c36b541572d5788e557` |

The raw external files are evidence of what Aeneas left opaque.  The
compilable `TypesExternal.lean` and `FunsExternal.lean` replace those holes
with ordinary Lean definitions for:

- `Iterator::find` and `Iterator::any`, including predicate-state threading;
- `Option::ok_or`, shared `copied`, equality, `Try::branch`, and the impossible
  `Option<Infallible>` residual;
- `Result::map_err`;
- slice `windows`, window iteration, and `last`;
- vector `as_slice`, `clear`, and `is_empty`;
- the three public Merkle tag constants; and
- query-index derivation, via the earlier Aeneas translation of the unchanged
  Rust helper and a field-for-field namespace adapter.

`proof/V5MerkleExternalSemantics.lean` checks the defining cases and audits
the axioms of the topology constructor, shape validator, and public driver.

## Result

The proof now follows one successful generated
`verify_v5_private_openings` execution all the way to the maintained Merkle
model:

1. `V5MerkleQueryReuseProof.lean` proves the extracted query helper returns
   the exact sorted layer-zero list and the three exact divide-by-4, 16, and
   64 lists.
2. `V5MerkleUnchangedQueryModelBridge.lean` identifies those lists with the
   five maintained tree-index sets.
3. `V5MerkleUnchangedFiveSectionComposition.lean` applies the exact helper
   theorem to each of the five generated calls, builds one `ExactV5Run`, and
   identifies all five returned opening values with that run.
4. `V5MerkleUnchangedPublicAcceptanceBridge.lean` starts at the generated
   public verifier's success result and produces the maintained run, the
   exact returned openings, index arrays, consumed-byte count, and an
   authenticated five-tree forest.

The final theorems are
`generated_public_acceptance_yields_exact_v5` and
`generated_public_acceptance_yields_exact_v5_with_output`, with
`generated_public_acceptance_yields_forest` as the direct forest result. They do not use
`VerifyStateOnlyPrivateOpeningWithTopologySourceEquality` or
`VerifyV5DriverCompositionSourceEquality`.

## Exact remaining boundary

There are **no `axiom` declarations in the implemented external files**.
The reused `RuntimeScheduleMerkleReuse.lean` query-index translation also has
no `axiom` declarations, and the Rust source file is unchanged from commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`.

This does not remove the normal translation-tool trust boundary.  It also does
not prove a cryptographic hash implementation: the generated Merkle functions
receive their hash callback as an explicit argument.  A production theorem
must still state which callback is used and connect it to Solana SHA-256.  The
Aeneas `loop` operator models possible divergence with Lean's
`partial_fixpoint`; it is a definition, not a new axiom.

The final theorem takes two ordinary input facts from the transcript layer:
the maintained query set has 18 entries, and sorting the generated query
slice gives that set. The proof derives nonemptiness and the 17-bit range
from those facts. Its only executable-behavior premise is
`HashCallbackEqualsSha256`, which says that the callback result equals SHA-256
of the concatenated byte slices. SHA-256 collision resistance, the
translation tools, the compiler, and the Solana runtime remain external to
this deterministic source proof.

## Replay

Set `AENEAS_LEAN_PATH` to the pinned Aeneas Lean backend's build path, then run:

```sh
AENEAS_LEAN_PATH="$(cd /path/to/aeneas/backends/lean && lake env printenv LEAN_PATH)" \
  ./aeneas-verif/v5-merkle-unchanged-full-20260820/replay-lean432.sh
```

The replay requires Lean 4.32.0, checks the recorded hashes, compiles every
module into a fresh temporary directory, rejects proof shortcuts, and requires
zero external axioms in the compilable bundle.
