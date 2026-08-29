# Aeneas loop-break lifetime-cleanup fix

## Diagnostic

The pinned LLBC function `aspis_core::transcript::Transcript::challenge_qm31`
(function 72) reconstructs the retry loop at Rust lines 371-388 as LLBC Loop
13516.  Its `Range<u32>` iterator is local 18.  Each iteration creates
`_21 = &mut iter^18` at statement 13316, makes the two-phase reborrow `_20` at
13317, and calls `Iterator::next` at 13331.

Both current-loop breaks precede the lifetime cleanup for that call:

- iterator exhaustion breaks at 13334;
- an accepted limb breaks at 13503;
- only after the structured Loop, statements 13517, 13518, 13520, and 13521
  end `_21`, `_19`, `iter^18`, and its source range.

At break synthesis, the projected execution context therefore retained a live
function-call handback abstraction `abs@45`, with mutable-borrow/loan links 39
and 40 between `iter^18` and `_21`.  The joined break source had already
flattened the equivalent relationship to link 23 and contained no `abs@45`.
Because this is mutable state, `match_ctx_with_target` correctly rejected the
structurally different contexts instead of erasing the extra abstraction.

## Patch boundary and soundness

`aeneas-d860ac47-loop-break-lifetime-cleanup.patch` changes only the existing
`lower_nested_loop_returns` prepass.  That prepass already moves the immediate
post-loop `StorageDead`/`Nop` prefix before every current-loop `Break 0` when a
nested loop contains a return.  The patch applies the same transformation to a
nested loop without a return: it extracts the immediate cleanup, uses the
existing `loop_normal_exit_cleanup` guard, passes that cleanup to the existing
break rewriter, and removes the now-relocated suffix after the Loop.

The transformation preserves Rust control flow.  A break still performs the
same lifetime cleanup before reaching the following statement; a continue does
not receive exit cleanup; reference write-back is executed through Aeneas's
ordinary abstraction-ending machinery.  The patch does not alter production
Rust, LLBC values, mutable join rules, or context-match permissiveness.

The diagnostic used unchanged LLBC SHA-256
`d05f26ee7b8bbd4f16c3bccd50348b129d1c25dd51a950730141a9e418d479e3`.
The unrelated dirty mutable-iterator worktree at
`/Users/dominic/ZK-aeneas-v5-outer` was inspected read-only and no change from
it is included here.
