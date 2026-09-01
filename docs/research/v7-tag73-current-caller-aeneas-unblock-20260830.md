# V7 current Tag-73 caller Aeneas unblock

## Scope

This milestone targets only the production Rust-to-Lean source closure for
`verify_v7_read_only_with_statement_digest` at
`bcd03b12293f2737dfa1da1436092a0a24a6ae24`. No K1 cryptographic theorem,
production Rust source, verifier relation, or Pool state transition is edited.

## Exact reduction

The original combined translation failed inside
`authenticate_and_fold_queries`: the gamma value had been translated and
embedded in the returned `QM31`, but a later abstraction no longer registered
the symbolic value. The smallest exact production composition reproducing it
has LLBC SHA-256
`c96d97fd31b79860b28b0a102a1630c2107a80abea0dff7abcd978b03bc7b032`.

The exact production gamma helper translates independently (LLBC SHA-256
`35e86058a6be07116332a96b222b091ecb58a7b3ab720c231acd9c56ac2f8d42`).
After making only that helper opaque, the complete caller advanced to a
second, independent Aeneas context-join failure in `qm31_dot3`. The exact
production `qm31_dot3` helper also translates independently (LLBC SHA-256
`79b3364db61b3c1f4752332a5e9259d779a22b9e3d5f5e131cfc13df8d27c378`).

The final combined extraction therefore keeps exactly those two helpers
opaque and reconnects their literal translations with structural maps. This
is narrower than a translator semantic patch and does not alter verifier
behavior.

That combined graph exposed one further translator family after the two
algebraic helpers were split. The smallest concrete failure is
`fold_grouped_rows_twice`: Rust lowers its fixed `vec![0, 1, 2, 3]` return to
`Box<MaybeUninit<[u8; 4]>>`, and the pinned Aeneas attempts to expand that
opaque standard-library type while preparing the assignment. A no-abort
diagnostic traversal identified exactly one additional family: four `FnMut`
closures which capture mutable fingerprint/dot-product accumulators.

The accepted extraction therefore applies a frozen source-equivalent patch to
a task-owned source copy. It replaces only those compiler-hostile spellings:

- the fixed vector is built by four ordered `Vec::push` calls;
- the three FNV-1a fingerprint closures call one explicit `&mut u64` helper;
- the line-dot closure calls one explicit helper with the same mutable arrays,
  reduction cadence, and operation order.

The production files are not edited. The patch changes only
`state_only_hiding.rs` and `sumcheck.rs`; exact input, patch, and normalized
output hashes are frozen in the bundle. Four optimized focused tests retain
the grouped-fold reference equality, Tag-73 composed terminal equality, and
the two hard-pinned fingerprint gates.

The normalized complete caller then exposed a fourth, independent translator
failure in Aeneas's optional loop-output reordering pass. A concrete
`finish_onefold_relation` composition contains a `break` payload whose arity
does not match the inferred loop-output permutation; the pass asserted equal
lengths before it could take its existing no-reorder path. The generic
production function, its exact body, and both halves translate independently,
so this is a composition-sensitive compiler transformation rather than a Rust
semantic failure.

The accepted Aeneas patch performs an exact preflight over all loop breaks. It
applies the optional permutation only when every break payload has the inferred
output arity; otherwise it uses the existing no-reorder path. This changes no
Rust value, proof relation, transcript byte, or cryptographic assumption. The
patched tree and reproducible static binary are pinned below.

Inlining the current statement terminal exposed one additional source-shape
boundary: the production caller obtains the frozen inactive row-group and mask
tables through functions returning static references. The complete composition
reached those references as bottom values in the pinned Aeneas loan model even
though the two constants themselves are finite arrays.

The accepted extraction-only normalization adds owned accessors for the same
two constants and changes only the task-owned caller copy to bind those arrays
locally before borrowing them for the existing verifier call. The original
reference accessors remain unchanged. The owned arrays contain exactly the
same 64 `u8` row-group entries and seven `u16` masks; no verifier input,
comparison, transcript operation, or result changes. An optimized verifier
compile/test and independent Charon/Aeneas translations of both accessors pass
before the complete caller is retried.

The complete current caller now translates with the statement terminal inline
and exactly two opaque functions: the independently translated
`gamma_combine_v6_c1_slot_major` and `qm31_dot3` helpers. Its LLBC SHA-256 is
`b4d931347481d70935e1aa6445173f68a38e678cc3b67eba6a467ca502c1be69`.
The generated caller `Funs.lean` SHA-256 is
`470d8c68c224b26f54db77276af71cbd89b196cdc65dd47d088105b61c8e4c9a`.

The first Lean elaboration of the newly inlined terminal then identified three
missing executable standard-library models, rather than a source or theorem
error: owned-array `next_back`, shared-slice `next_back`, and mapped-iterator
`next`. The external models retain exact front/back bounds, thread the mapped
closure state, and shrink the retained slice on reverse iteration. The first
affected generated chunk compiles after those models are added.

Subsequent focused compilation exposed only generated-Lean compatibility
shapes, not verifier mathematics: three scalar intrinsics, three iterator
operations, two no-op `FnMut` return pairs, 80 monadic `lift` calls after a
Rust helper shadows that name, and a missing pair of parentheses in the type
of the final captured `(hash, wire)` closure. Every correction is guarded by
the exact frozen generated shape and count.

The 15-entry atomic copy-pattern registry was also factored token-for-token
into independently compiled records and one typed array join. Together with
the earlier circle-table factoring, this makes the complete caller graph fit
comfortably under the per-target resource rule without changing any constant
or consumer.

## Focused evidence

| Target | Wall | Peak RSS | Swap | Exit |
|---|---:|---:|---:|---:|
| Gamma-opaque authenticate/fold Charon | 13.50 s | 523,260 KiB | 0 | 0 |
| Gamma-opaque authenticate/fold Aeneas | 26.48 s | 415,292 KiB | 0 | 0 |
| Literal `qm31_dot3` Charon | 5.77 s | 679,744 KiB | 0 | 0 |
| Literal `qm31_dot3` Aeneas | 1:49.23 | 390,056 KiB | 0 | 0 |
| Chunked low8 table plus first consumer | 31.15 s | 2,515,948 KiB | 0 | 0 |
| Owned-accessor optimized verifier compile/test | 1:48.23 | 462,448 KiB | 0 | 0 |
| Complete current caller Charon | 14.97 s | 512,272 KiB | 0 | 0 |
| Complete current caller Aeneas | 11:45.20 | 2,694,524 KiB | 0 | 0 |
| Retyped table chain plus first affected caller chunk | 1:24.32 | 2,505,616 KiB | 0 | 0 |
| Exact final staging pass | 0.96 s | 28,420 KiB | 0 | 0 |
| Complete 139-target Lean graph | 201.12 s summed | 3,179,956 KiB worst target | 0 | all 0 |
| Final production-root audit | 1.11 s | 2,514,584 KiB | 0 | 0 |

The rejected unchunked generated-table run was stopped after roughly twelve
minutes with no completed target at 22,866,784,256 bytes cgroup memory and
zero swap. The changed staging generator—not a larger cap—produced the green
replacement above.

## Toolchain

- Charon `0.1.223`, commit
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, binary SHA-256
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.
- Rust nightly `2026-06-01`, rustc `1.98.0-nightly
  (14210df0e 2026-05-31)`, LLVM `22.1.6`.
- Aeneas base `d860ac47ed548d3da6d799afc013779ce470516c`, patched Git tree
  `031a61b263bffddabfd04e3476fb53a3754fdb64`.
- Reproducible Aeneas binary version
  `d860ac47-tag73-looparity-r1`, SHA-256
  `7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a`.
- Pinned dependency image
  `sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7`.

## Final status

The complete Rust-to-Aeneas translation, all 139 staged Lean targets, the
composed production caller, and the final production-root audit are green.
The strongest caller reports exactly `propext`, `Classical.choice`, and
`Quot.sound`; every audited theorem is a subset of that set. There is no
`sorry`, `admit`, `sorryAx`, `native_decide`, or project-defined axiom in any
accepted compiled source.

The strongest generated root is
`V7Tag73CurrentHelpersOpaque.v7_verifier.verify_v7_read_only_with_statement_digest`
in `proof/V7Tag73CurrentHelpersOpaque/FunsChunk45.lean`. Its exact audit is in
`proof/CurrentCallerAudit.lean`, and the complete output is frozen under
`evidence/nuc/current-caller-lean-owned-r19/`.

The remaining explicit boundary is ordinary source provenance: the hash
callback/SHA-256 primitive behavior, Charon/Aeneas/compiler correctness, the
guarded source-equivalent extraction shims and executable standard-library
models, and the Lean kernel. The two combined-LLBC opaque helpers are not
assumptions: each is independently translated and reconnected by the
kernel-checked `gamma_combine_v6_c1_slot_major_split_exact` and
`qm31_dot3_split_exact` endpoints.
