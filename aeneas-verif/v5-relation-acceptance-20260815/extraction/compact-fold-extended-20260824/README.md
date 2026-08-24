# Corrected compact-fold extraction

This directory records the 24 August 2026 Charon/Aeneas extraction of the
production `CompactBTerminalWeights::fold` method.

The previous checked snapshot translated the loop body but assembled the
mutable-array write-back around an empty iterator. That was a proof-artifact
bug, not a Rust bug. The Aeneas patch here retains the exact loop value consumed
by the backward iterator function. The regenerated loop therefore returns the
reconstructed iterator itself, and the outer function passes that iterator to
the array write-back function.

`generated/V5CompactFoldExtendedFull.raw.lean` is the direct Aeneas output.
`generated-normalization.patch` performs only three backend/library
normalizations:

1. use the pinned Lean 4.32 Aeneas imports;
2. render the three shift counts as unsigned values expected by that library;
3. replace the external declaration for mutable-array `into_iter` with the
   existing exact `Array.to_slice`/`Array.from_slice` model.

The normalized generated file contains no `axiom` or `sorry` and compiles with
Lean 4.32. The manifest records every source, tool, patch, generated file, and
compiled-object hash. The 1.7 MB LLBC is archived on the project NUC rather
than duplicated in Git.

The extraction-only Rust wrapper merely makes the private inherent method a
Charon root. The host-only Solana patch removes `cdylib` while retaining
`rlib`; neither patch changes the deployed verifier source or its semantics.
