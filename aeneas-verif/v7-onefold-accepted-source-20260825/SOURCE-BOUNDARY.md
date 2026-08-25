# V7 source boundary report

## What is byte-identical deployed source

The deployed source is commit
`1589706d38a5e8ca705fbf7aaed2c82cf8595510`, tree
`d43572d059a48a871933be4ab7067e7ded2fab28`. The frozen SBF has SHA-256
`0d3c21f3ba9b291149aa82d9632417669bbe9a6490a46f718522666b47a670f4`.
No production source file and no SBF byte was changed for this bundle.

Charon successfully extracts the unmodified root
`crate::v7_verifier::verify_v7_read_only_with_statement_digest`. The archived
`production-root/extraction/V7ProductionRoot.llbc` is that exact extraction;
its normalized LLBC SHA-256 is
`46e15b05151445109ce5bb3dced20242c9aac0000f086a6282e2e01d77c88763`.

## Original exact-root translator failure

The deployed root obtains two frozen `&'static` schedules inside the call to
`verify_v7_compact_transcript_and_relation_prepared`:

- line 120: `atomic_state_only_copy_inactive_row_groups_v3()`;
- line 121: `atomic_state_only_copy_inactive_group_masks_v3()`.

With the earlier V6-patched Aeneas, the unmodified root failed first at exactly
`programs/aspis-verifier/src/v7_verifier.rs:120:8-120:55`, with
`Error Unreachable`. With `-print-error-emitters`, the actual emitter is
`interp/InterpBorrowsCore.ml:629`: dereferencing the returned shared borrow
cannot find its loan. The original `interp/Interp.ml:619` location in the raw
log is only the outer warning handler.

The static region is intentionally absent from Aeneas's return-region
hierarchy, so expansion of an opaque `&'static T` result created `SB bid`
without installing `SL bid value`. After restoring that loan, execution also
exposed an independent typo in `InterpPaths.access_place`: it computed both
erased types but compared `updated_ty` against the unerased `v.ty`.

The diagnostic-only second root remains archived because it independently
reproduced the same issue for the group-mask accessor at
`v7_verifier.rs:160:8-160:56`. Neither diagnostic source nor the old overlay is
part of the deployed SBF or final direct-root proof.

## Narrow Aeneas correction

`toolchain/aeneas-d860ac47-static-return-loan.patch` makes two changes:

1. For an opaque immutable `&'static T` result, retain the fresh symbolic inner
   value in a non-ending dummy shared loan. This is the same storage model the
   pinned translator already uses for immutable global references. It restores
   the loan/borrow invariant without selecting or copying a concrete value.
2. Compare the erased updated type with the already-computed erased existing
   type in `InterpPaths.access_place`.

Static is preserved on the declaration long enough to select the persistent
loan case, then erased only in the concrete runtime context. Mutable static
references are not added or generalized by this patch.

The patched Aeneas binary has SHA-256
`c824ad52b6fecc69abd41ed3206781132f6c84850de2ee6bb5bbb0ed5ad29926`.
It translates all 11 transparent functions in the exact production LLBC with
no partial definition or extraction wrapper.

## Eliminated overlay boundary

`production-root/generated-exact/V7ProductionRoot/Funs.lean` contains the
direct generated definition
`v7_verifier.verify_v7_read_only_with_statement_digest`. Its source span is
the deployed `v7_verifier.rs:98:0-131:1`, and it calls the two frozen schedule
accessors itself.

`production-root/proof/V7ProductionRootSourceBridge.lean` proves directly:

- parser rejection is fail-closed as `V7VerifyError::Query`;
- transcript rejection is fail-closed as `V7VerifyError::Transcript` after the
  two infallible-source schedule interfaces return;
- successful interfaces return the exact transcript and its exact
  `folded_query_sum` projection.

Therefore `V7-SOURCE-OVERLAY-EQUIVALENCE` is eliminated from the final proof
chain. The old `V7AcceptedKernel` overlay files remain only as historical
diagnostics and are not imported by the direct-root theorem.

## Remaining explicit boundaries

Charon and Aeneas remain pinned trusted translation tools rather than
kernel-proved compilers. Functions deliberately opaque at the extraction
boundary remain named Aeneas axioms: the parser, schedule accessors,
transcript/relation verifier, field operations, terminal calculation and
Solana public-key conversion. Their arithmetic, transcript grammar,
terminal algebra, Merkle/frontier semantics and cryptographic assumptions
remain in the existing focused formal modules and release evidence. SHA-256,
SBF compilation and Solana runtime correspondence likewise remain explicit
boundaries.

The separate parser wrapper bridge still proves definitional equality to the
translated deployed inherent parser by `rfl`, cap-203 rejection, and exact
success propagation.
