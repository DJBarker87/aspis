# V5 atomic-terminal source extraction

This package records a successful Charon/Aeneas extraction of the unchanged
production function `verify_v5_atomic_terminal_from_bytes` from
`programs/aspis-verifier/src/v5_atomic_terminal.rs`.

Unlike the earlier checkpoint in this directory, the complete extraction keeps
`decode_points` in the translated program.  The only deliberately opaque
cryptographic computation in the Charon command is
`atomic_state_only_selected_unmasked_terminal_value_compiled_v3`; its evaluator
layers are recorded separately by the earlier generated modules in this
directory.

The translation completed with `-abort-on-error`.  The generated definition is
`V5AtomicTerminalCompleteSourceGenerated.v5_atomic_terminal.verify_v5_atomic_terminal_from_bytes`
in `generated/V5AtomicTerminalCompleteSource/Funs.lean`.

`extraction/manifest.sha256` binds the LLBC, the generated Lean files, the
translator patch, and the exact tool binaries.  The patch is the full delta from
the pinned Aeneas base revision named in `extraction/toolchain.txt`; it includes
the nested-return and mutable-reborrow handling needed by this source path.

Run `./replay-complete-source.sh` from this directory to repeat extraction and
translation.  The script uses temporary output directories and compares the
result with the checked-in files.  The comparison ignores only trailing blank
lines in Aeneas's external-template output; the checked-in template has the
repository-standard single final newline.

This checkpoint closes the parser/decoder translation problem inside the
terminal verifier.  It does not by itself connect the separate outer
`verify_mode9_atomic_terminal_with_prefix` wrapper to the accepted-entry model,
and it does not turn the evaluator or field/hash primitives into proved Lean
implementations.  Those are explicit next-layer obligations.

## Direct production outer-wrapper extraction

`generated/V5AtomicTerminalPrefixWrapperComplete` is the stronger follow-up
snapshot.  Charon starts directly from the private production function
`aspis_verifier::v5_cu_probe::verify_mode9_atomic_terminal_with_prefix` in the
real verifier crate.  Its call graph keeps both context decoding and
`verify_v5_atomic_terminal_from_bytes` transparent.  Consequently the generated
Lean definition contains the outer wrapper, both decoders, and the complete
terminal checks in one namespace.  Only the compiled semantic evaluator is
deliberately opaque at extraction time.

The direct verifier-crate extraction uses Charon's distributed Rust sysroot
(`--sysroot default`).  This avoids attempting to link Solana's dependency
`cdylib` against Charon's MIR sysroot while still extracting built MIR for the
unchanged production crate.  Run `./replay-prefix-wrapper-complete.sh` to repeat
this snapshot.
